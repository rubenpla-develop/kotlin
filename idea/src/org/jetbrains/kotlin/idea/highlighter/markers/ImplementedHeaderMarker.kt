/*
 * Copyright 2010-2016 JetBrains s.r.o.
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

package org.jetbrains.kotlin.idea.highlighter.markers

import com.intellij.codeInsight.daemon.impl.PsiElementListNavigator
import com.intellij.ide.util.DefaultPsiElementCellRenderer
import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.idea.caches.resolve.findModuleDescriptor
import org.jetbrains.kotlin.idea.core.toDescriptor
import org.jetbrains.kotlin.psi.KtDeclaration
import org.jetbrains.kotlin.resolve.DescriptorToSourceUtils
import org.jetbrains.kotlin.resolve.MultiTargetPlatform
import org.jetbrains.kotlin.resolve.checkers.HeaderImplDeclarationChecker
import org.jetbrains.kotlin.resolve.getMultiTargetPlatform
import java.awt.event.MouseEvent

fun ModuleDescriptor.hasImplementationsOf(descriptor: MemberDescriptor) =
        implementationsOf(descriptor).isNotEmpty()

private fun ModuleDescriptor.implementationsOf(descriptor: MemberDescriptor): List<DeclarationDescriptor> =
        with (HeaderImplDeclarationChecker(this)) {
            descriptor.findCompatibleDescriptors().filter { it.isImpl }
        }

fun getPlatformImplementationTooltip(declaration: KtDeclaration): String? {
    val descriptor = declaration.toDescriptor() as? MemberDescriptor ?: return null
    val commonModuleDescriptor = declaration.containingKtFile.findModuleDescriptor()

    val platformModulesWithImplementation = commonModuleDescriptor.allImplementingModules.filter {
        it.hasImplementationsOf(descriptor)
    }
    if (platformModulesWithImplementation.isEmpty()) return null

    return platformModulesWithImplementation.joinToString(prefix = "Has implementations in ") {
        (it.getMultiTargetPlatform() as MultiTargetPlatform.Specific).platform
    }
}

fun navigateToPlatformImplementation(e: MouseEvent?, declaration: KtDeclaration) {
    val implementations = declaration.headerImplementations()
    if (implementations.isEmpty()) return

    val renderer = DefaultPsiElementCellRenderer()
    PsiElementListNavigator.openTargets(e,
                                        implementations.toTypedArray(),
                                        "Choose implementation of ${declaration.name}",
                                        "Implementations of ${declaration.name}",
                                        renderer)
}

internal fun KtDeclaration.headerImplementations(): Set<KtDeclaration> {
    val descriptor = toDescriptor() as? MemberDescriptor ?: return emptySet()
    val commonModuleDescriptor = containingKtFile.findModuleDescriptor()
    return commonModuleDescriptor.allImplementingModules.flatMap {
        it.implementationsOf(descriptor)
    }.mapNotNullTo(LinkedHashSet()) { DescriptorToSourceUtils.descriptorToDeclaration(it) as? KtDeclaration }
}