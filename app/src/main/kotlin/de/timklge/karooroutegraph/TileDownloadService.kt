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

class TileDownloadService(
    private val karooSystemServiceProvider: KarooSystemServiceProvider,
    private val minimapViewModelProvider: MinimapViewModelProvider,
    context: Context,
) {
    data class CachedTile(val lastAccessed: Instant, val bitmap: Bitmap)

    private val cacheDir = File(context.cacheDir, "tiles")
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
     * The minimap draws every tile at TARGET_TILE_SIZE (700 px), i.e. a 256 px tile is upscaled ~2.7x.
     * swisstopo chooses its map product by zoom level, so upscaled tiles look far too coarse
     * (overview map at street scale). Instead, build each tile from its four children one zoom
     * level deeper, stitched into a 512 px bitmap: finer map product and only ~1.4x upscaling.
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
