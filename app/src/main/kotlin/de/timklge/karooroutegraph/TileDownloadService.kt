/*
 * Copyright 2026 timklge
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package de.timklge.karooroutegraph

import android.content.Context
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Canvas
import android.net.ConnectivityManager
import android.net.NetworkCapabilities
import com.mapbox.geojson.LineString
import com.mapbox.turf.TurfConstants
import com.mapbox.turf.TurfMeasurement
import de.timklge.karooroutegraph.datatypes.minimap.getRequiredTiles
import kotlin.math.cos
import kotlin.math.pow
import android.util.Log
import de.timklge.karooroutegraph.datatypes.minimap.MinimapViewModelProvider
import io.hammerhead.karooext.models.HttpResponseState
import io.hammerhead.karooext.models.OnHttpResponse
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.delay
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.channels.trySendBlocking
import kotlinx.coroutines.flow.callbackFlow
import kotlinx.coroutines.flow.single
import kotlinx.coroutines.launch
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.IOException
import java.time.Duration
import java.time.Instant

const val SWISSTOPO_MAX_ZOOM = 18
private val PREFETCH_ZOOM_ORDER = listOf(14, 15, 13, 16, 12, 11, 10)
private const val PREFETCH_VIEW_WIDTH_PX = 480
private const val PREFETCH_VIEW_HEIGHT_PX = 720
private const val MAX_DISK_BYTES = 2L * 1024 * 1024 * 1024 // 2 GB

class TileDownloadService(
    private val karooSystemServiceProvider: KarooSystemServiceProvider,
    private val minimapViewModelProvider: MinimapViewModelProvider,
    context: Context,
) {
    data class CachedTile(val lastAccessed: Instant, val bitmap: Bitmap)

    // filesDir instead of cacheDir: Android may clear cacheDir, but pre-downloaded route tiles must stay
    private val cacheDir = File(context.filesDir, "swisstopo-tiles")
    private val appContext = context.applicationContext
    private var prefetchJob: Job? = null
    private val inMemoryCache = mutableMapOf<Tile, CachedTile>()
    private val mutex = Mutex()
    private val maxCacheSize = 24 // 512 px tiles are ~1 MB each in memory
    private val pendingTiles: MutableSet<Tile> = java.util.concurrent.ConcurrentHashMap.newKeySet()
    private val downloadWorkers = 3
    private val maxCacheAge = Duration.ofMinutes(30)

    private val downloadQueue: Channel<Tile> = Channel(Channel.UNLIMITED)

    init {
        if (!cacheDir.exists()) {
            cacheDir.mkdirs()
        }
        CoroutineScope(Dispatchers.IO).launch { pruneDiskCache() }
        startDownloadJob()
    }

    private var downloadJob: Job? = null

    fun startDownloadJob() {
        downloadJob = CoroutineScope(Dispatchers.IO).launch {
          repeat(downloadWorkers) { launch {
            for (tile in downloadQueue) {
                try {
                    val downloadedTile = getTileIfAvailableInstantly(tile)
                    if (downloadedTile != null) {
                        Log.d(KarooRouteGraphExtension.TAG, "Tile $tile already in cache")
                        continue
                    }
                    val fetchedBitmap = fetchTileFromNetwork(tile)

                    // Save to caches (file and memory)
                    mutex.withLock {
                        val tileFile = getTileFile(tile)
                        saveTileToFile(fetchedBitmap, tileFile)
                        gcCache() // Clean up memory cache before adding new item
                        inMemoryCache[tile] = CachedTile(Instant.now(), fetchedBitmap)
                        Log.d(KarooRouteGraphExtension.TAG, "Fetched tile ${tile}, saved to file and added to memory cache")
                    }

                    minimapViewModelProvider.update {
                        it.copy(lastTileDownloadedAt = Instant.now())
                    }
                } catch (e: Exception) {
                    Log.e(KarooRouteGraphExtension.TAG, "Error downloading tile $tile", e)
                } finally {
                    pendingTiles.remove(tile) // allows a re-queue (retry) on the next redraw if it failed
                }
            }
          } }
        }
    }

    private fun getTileFile(tile: Tile): File {
        return File(cacheDir, "swisstopo2x-${tile.z}-${tile.x}-${tile.y}.jpg")
    }

    /**
     * Download every minimap tile along [route] for the zoom steps from 5 km down to 50 m
     * (Z10..Z16) into persistent storage, but only while the Karoo is on Wi-Fi (Karoo routes
     * extension HTTP over Wi-Fi when connected, otherwise via Bluetooth to the phone, which is slow).
     */
    fun prefetchRoute(route: LineString?) {
        prefetchJob?.cancel()
        setPrefetchStatus(null)
        if (route == null) return

        prefetchJob = CoroutineScope(Dispatchers.IO).launch {
            try {
                val tiles = computeRouteTiles(route)
                var done = tiles.count { getTileFile(it).exists() }
                Log.i(KarooRouteGraphExtension.TAG, "Route prefetch: ${tiles.size} tiles, $done already stored")

                for (tile in tiles) {
                    if (getTileFile(tile).exists()) continue
                    while (!isOnWifi()) {
                        setPrefetchStatus("Offline ${percent(done, tiles.size)}% - needs Wi-Fi")
                        delay(30_000)
                    }
                    setPrefetchStatus("Offline ${percent(done, tiles.size)}%")
                    try {
                        val bitmap = fetchTileFromNetwork(tile)
                        mutex.withLock { saveTileToFile(bitmap, getTileFile(tile)) }
                        bitmap.recycle()
                    } catch (e: kotlinx.coroutines.CancellationException) {
                        throw e
                    } catch (e: Exception) {
                        Log.w(KarooRouteGraphExtension.TAG, "Route prefetch: tile $tile failed", e)
                    }
                    done++
                    delay(100) // stay well within swisstopo fair use (max 600 requests/min)
                }
                setPrefetchStatus(if (done >= tiles.size) "Offline ready" else "Offline ${percent(done, tiles.size)}%")
            } catch (e: kotlinx.coroutines.CancellationException) {
                throw e
            } catch (e: Exception) {
                Log.e(KarooRouteGraphExtension.TAG, "Route prefetch failed", e)
                setPrefetchStatus(null)
            }
        }
    }

    private fun percent(done: Int, total: Int) = if (total == 0) 100 else (done * 100 / total)

    private fun setPrefetchStatus(status: String?) {
        minimapViewModelProvider.update { if (it.prefetchStatus == status) it else it.copy(prefetchStatus = status) }
    }

    /** All tiles the minimap could need along the route, most used zoom steps first. */
    private fun computeRouteTiles(route: LineString): List<Tile> {
        val routeLengthM = TurfMeasurement.length(route, TurfConstants.UNIT_METERS)
        val lat = route.coordinates().firstOrNull()?.latitude() ?: 46.8
        val result = LinkedHashSet<Tile>()
        for (zoom in PREFETCH_ZOOM_ORDER) {
            // Sample the route every quarter tile and add the tiles a screen-sized view around that point needs
            val tileSizeM = 40_075_016.0 * cos(Math.toRadians(lat)) / 2.0.pow(zoom)
            val stepM = tileSizeM / 4
            var d = 0.0
            while (d <= routeLengthM) {
                val point = TurfMeasurement.along(route, d, TurfConstants.UNIT_METERS)
                result.addAll(getRequiredTiles(zoom.toFloat(), PREFETCH_VIEW_WIDTH_PX, PREFETCH_VIEW_HEIGHT_PX, point))
                d += stepM
            }
        }
        return result.toList()
    }

    private fun isOnWifi(): Boolean {
        return try {
            val cm = appContext.getSystemService(ConnectivityManager::class.java) ?: return false
            val caps = cm.getNetworkCapabilities(cm.activeNetwork) ?: return false
            caps.hasTransport(NetworkCapabilities.TRANSPORT_WIFI) || caps.hasTransport(NetworkCapabilities.TRANSPORT_ETHERNET)
        } catch (e: Exception) {
            Log.w(KarooRouteGraphExtension.TAG, "Could not determine network state, assuming Wi-Fi", e)
            true
        }
    }

    /** Keep stored tiles under MAX_DISK_BYTES by deleting the least recently written ones. */
    private fun pruneDiskCache() {
        val files = cacheDir.listFiles()?.filter { it.isFile } ?: return
        var total = files.sumOf { it.length() }
        if (total <= MAX_DISK_BYTES) return
        for (file in files.sortedBy { it.lastModified() }) {
            if (total <= MAX_DISK_BYTES * 3 / 4) break
            total -= file.length()
            file.delete()
        }
    }

    suspend fun getTileIfAvailableInstantly(tile: Tile): Bitmap? {
        mutex.withLock {
            val cachedTile = inMemoryCache[tile]
            if (cachedTile != null) {
                // Update last accessed time in memory cache
                inMemoryCache[tile] = cachedTile.copy(lastAccessed = Instant.now())
                return cachedTile.bitmap
            }
        }

        // Check file system cache (outside memory cache lock initially for read)
        val tileFile = getTileFile(tile)
        if (tileFile.exists()) {
            try {
                val bitmap = loadTileFromFile(tileFile)
                if (bitmap != null) {
                    // Add to memory cache (needs lock)
                    mutex.withLock {
                        // Double check if another thread added it while we were reading the file
                        if (!inMemoryCache.containsKey(tile)) {
                            gcCache() // Make space if needed before adding
                            inMemoryCache[tile] = CachedTile(Instant.now(), bitmap)
                            Log.d(KarooRouteGraphExtension.TAG, "Loaded tile $tile from file cache into memory")
                        } else {
                            // Already in memory, update access time
                            inMemoryCache[tile] = inMemoryCache[tile]!!.copy(lastAccessed = Instant.now())
                        }
                        // Return the bitmap from the (potentially updated) memory cache entry
                        return inMemoryCache[tile]?.bitmap
                    }
                } else {
                    // File exists but couldn't be decoded, delete it
                    Log.w(KarooRouteGraphExtension.TAG, "Could not decode tile file ${tileFile.path}, deleting.")
                    tileFile.delete()
                }
            } catch (e: IOException) {
                Log.e(KarooRouteGraphExtension.TAG, "Error reading tile file ${tileFile.path}", e)
                // Optionally delete corrupted file: tileFile.delete()
            }
        }

        return null // Not found in memory or file cache
    }

    fun queueTileDownload(tile: Tile) {
        // If not available instantly, add to download queue
        if (pendingTiles.add(tile)) downloadQueue.trySendBlocking(tile)
    }

    /**
     * Upstream drew 256 px tiles at 700 px (~2.7x upscaling); swisstopo picks its map product by zoom,
     * so that looked far too coarse. Each tile is built from its four children one zoom level deeper,
     * stitched into a 512 px bitmap and drawn 1:1 (TARGET_TILE_SIZE = 512).
     */
    private suspend fun fetchTileFromNetwork(tile: Tile): Bitmap {
        if (tile.z >= SWISSTOPO_MAX_ZOOM) return fetchWithRetry(tile.z, tile.x, tile.y)

        val childZ = tile.z + 1
        val offsets = listOf(0 to 0, 1 to 0, 0 to 1, 1 to 1)
        val children = coroutineScope {
            offsets.map { (dx, dy) -> async { fetchWithRetry(childZ, tile.x * 2 + dx, tile.y * 2 + dy) } }.awaitAll()
        }
        val stitched = Bitmap.createBitmap(512, 512, Bitmap.Config.ARGB_8888)
        val canvas = Canvas(stitched)
        offsets.zip(children).forEach { (offset, child) ->
            val (dx, dy) = offset
            canvas.drawBitmap(child, null, android.graphics.Rect(dx * 256, dy * 256, dx * 256 + 256, dy * 256 + 256), null)
            child.recycle()
        }
        return stitched
    }

    private suspend fun fetchWithRetry(z: Int, x: Int, y: Int, attempts: Int = 3): Bitmap {
        var lastError: Throwable? = null
        repeat(attempts) { attempt ->
            try {
                return fetchSwisstopoTile(z, x, y)
            } catch (e: Throwable) {
                if (e is kotlinx.coroutines.CancellationException) throw e
                lastError = e
                Log.w(KarooRouteGraphExtension.TAG, "Tile $z/$x/$y attempt ${attempt + 1} failed", e)
                delay(500L * (attempt + 1))
            }
        }
        throw lastError ?: IllegalStateException("Tile $z/$x/$y failed")
    }

    private suspend fun fetchSwisstopoTile(z: Int, x: Int, y: Int): Bitmap {
        return callbackFlow {
            // swisstopo national map (Landeskarte), Web Mercator / XYZ tiling
            val url = "https://wmts.geo.admin.ch/1.0.0/ch.swisstopo.pixelkarte-farbe/default/current/3857/${z}/${x}/${y}.jpeg"

            Log.d(KarooRouteGraphExtension.TAG, "Http tile request to ${url}...")

            val listenerId = karooSystemServiceProvider.karooSystemService.addConsumer(
                OnHttpResponse.MakeHttpRequest(
                    "GET",
                    url,
                    waitForConnection = false,
                    headers = mapOf("User-Agent" to KarooRouteGraphExtension.TAG),
                ),
            ) { event: OnHttpResponse ->
                if (event.state is HttpResponseState.Complete) {
                    val completeEvent = (event.state as HttpResponseState.Complete)

                    try {
                        val inputStream =
                            java.io.ByteArrayInputStream(completeEvent.body ?: ByteArray(0))

                        if (completeEvent.error != null) {
                            Log.e(
                                KarooRouteGraphExtension.TAG,
                                "Http response event; error ${completeEvent.error}"
                            )
                            error(completeEvent.error ?: "Unknown error")
                        }

                        val result = BitmapFactory.decodeStream(inputStream)
                            ?: error("Could not decode tile $url (HTTP ${completeEvent.statusCode})")

                        trySendBlocking(result)
                    } catch (e: Throwable) {
                        Log.e(KarooRouteGraphExtension.TAG, "Failed to process response", e)
                    }

                    close()
                }
            }
            awaitClose {
                karooSystemServiceProvider.karooSystemService.removeConsumer(listenerId)
            }
        }.single()
    }

    private fun saveTileToFile(bitmap: Bitmap, file: File) {
        try {
            FileOutputStream(file).use { out ->
                bitmap.compress(Bitmap.CompressFormat.JPEG, 90, out)
            }
            Log.v(KarooRouteGraphExtension.TAG, "Saved tile to ${file.path}")
        } catch (e: IOException) {
            Log.e(KarooRouteGraphExtension.TAG, "Error saving tile to ${file.path}", e)
            // Attempt to delete partially written file
            file.delete()
        }
    }

    private fun loadTileFromFile(file: File): Bitmap? {
        return try {
            FileInputStream(file).use { fis ->
                BitmapFactory.decodeStream(fis)
            }.also {
                if (it != null) Log.v(KarooRouteGraphExtension.TAG, "Loaded tile from ${file.path}")
                else Log.w(KarooRouteGraphExtension.TAG, "Failed to decode bitmap from ${file.path}")
            }
        } catch (e: IOException) {
            Log.e(KarooRouteGraphExtension.TAG, "Error loading tile from ${file.path}", e)
            null
        }
    }


    private fun gcCache() {
        // Assumes this function is called within a mutex lock
        val now = Instant.now()
        val expiryTime = now.minus(maxCacheAge)

        // Remove entries older than maxCacheAge
        val iterator = inMemoryCache.iterator()
        while (iterator.hasNext()) {
            val entry = iterator.next()
            if (entry.value.lastAccessed.isBefore(expiryTime)) {
                iterator.remove()
                Log.d(KarooRouteGraphExtension.TAG, "GC Cache: Removed expired tile ${entry.key}")
            }
        }

        // If cache still exceeds max size, remove the oldest entries
        if (inMemoryCache.size > maxCacheSize) {
            // Sort entries by lastAccessed time (oldest first)
            val sortedEntries = inMemoryCache.entries.sortedBy { it.value.lastAccessed }
            val entriesToRemove = inMemoryCache.size - maxCacheSize

            // Remove the oldest entries
            for (i in 0 until entriesToRemove) {
                val entryToRemove = sortedEntries[i]
                inMemoryCache.remove(entryToRemove.key)
                Log.d(KarooRouteGraphExtension.TAG, "GC Cache: Removed oldest tile ${entryToRemove.key} due to size limit")
            }
        }
    }

}
