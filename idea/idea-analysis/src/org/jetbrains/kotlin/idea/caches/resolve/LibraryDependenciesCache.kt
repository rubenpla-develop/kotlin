/*
 * Copyright 2010-2015 JetBrains s.r.o.
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

package org.jetbrains.kotlin.idea.caches.resolve

import com.intellij.openapi.module.Module
import com.intellij.openapi.module.ModuleManager
import com.intellij.openapi.project.Project
import com.intellij.openapi.projectRoots.Sdk
import com.intellij.openapi.roots.*
import com.intellij.openapi.roots.libraries.Library
import com.intellij.openapi.util.Condition
import com.intellij.psi.util.CachedValueProvider
import com.intellij.psi.util.CachedValuesManager
import com.intellij.util.containers.MultiMap
import org.jetbrains.kotlin.idea.project.TargetPlatformDetector
import org.jetbrains.kotlin.resolve.TargetPlatform
import org.jetbrains.kotlin.utils.addIfNotNull
import java.util.*

class LibraryDependenciesCache(private val project: Project) {

    //NOTE: used LibraryRuntimeClasspathScope as reference
    fun getLibrariesAndSdksUsedWith(library: Library): Pair<List<Library>, List<Sdk>> {
        val processedModules = HashSet<Module>()
        val condition = Condition<OrderEntry> { orderEntry ->
            if (orderEntry is ModuleOrderEntry) {
                val module = orderEntry.module
                module != null && module !in processedModules
            }
            else {
                true
            }
        }

        val libraries = LinkedHashSet<Library>()
        val sdks = LinkedHashSet<Sdk>()

        val platform = TargetPlatformDetector.getPlatform(library)

        for (module in getLibraryUsageIndex().modulesLibraryIsUsedIn[library]) {
            if (!processedModules.add(module)) continue

            ModuleRootManager.getInstance(module).orderEntries().recursively().satisfying(condition).process(object : RootPolicy<Unit>() {
                override fun visitModuleSourceOrderEntry(moduleSourceOrderEntry: ModuleSourceOrderEntry, value: Unit) {
                    processedModules.add(moduleSourceOrderEntry.ownerModule)
                }

                override fun visitLibraryOrderEntry(libraryOrderEntry: LibraryOrderEntry, value: Unit) {
                    val otherLibrary = libraryOrderEntry.library
                    if (otherLibrary != null && compatiblePlatforms(platform, TargetPlatformDetector.getPlatform(otherLibrary))) {
                        libraries.add(otherLibrary)
                    }
                }

                override fun visitJdkOrderEntry(jdkOrderEntry: JdkOrderEntry, value: Unit) {
                    sdks.addIfNotNull(jdkOrderEntry.jdk)
                }
            }, Unit)
        }

        return Pair(libraries.toList(), sdks.toList())
    }

    /**
     * @return true if it's OK to add a dependency from a library with platform [from] to a library with platform [to]
     */
    private fun compatiblePlatforms(from: TargetPlatform, to: TargetPlatform): Boolean {
        return from == to || to == TargetPlatform.Default
    }

    private fun getLibraryUsageIndex(): LibraryUsageIndex {
        return CachedValuesManager.getManager(project).getCachedValue(project) {
            CachedValueProvider.Result(LibraryUsageIndex(), ProjectRootModificationTracker.getInstance(project))
        }!!
    }

    private inner class LibraryUsageIndex {
        val modulesLibraryIsUsedIn: MultiMap<Library, Module> = MultiMap.createSet()

        init {
            for (module in ModuleManager.getInstance(project).modules) {
                for (entry in ModuleRootManager.getInstance(module).orderEntries) {
                    if (entry is LibraryOrderEntry) {
                        val library = entry.library
                        if (library != null) {
                            modulesLibraryIsUsedIn.putValue(library, module)
                        }
                    }
                }
            }
        }
    }
}
