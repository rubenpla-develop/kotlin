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

package org.jetbrains.kotlin.cli.common.arguments;

import org.jetbrains.annotations.NotNull;

import static org.jetbrains.kotlin.cli.common.arguments.K2JsArgumentConstants.CALL;
import static org.jetbrains.kotlin.cli.common.arguments.K2JsArgumentConstants.NO_CALL;

public class K2JSCompilerArguments extends CommonCompilerArguments {
    public static final long serialVersionUID = 0L;

    @GradleOption(DefaultValues.StringNullDefault.class)
    @Argument(value = "-output", valueDescription = "<path>", description = "Output file path")
    public String outputFile;

    @GradleOption(DefaultValues.BooleanTrueDefault.class)
    @Argument(value = "-no-stdlib", description = "Don't use bundled Kotlin stdlib")
    public boolean noStdlib;

    @Argument(
            value = "-libraries",
            valueDescription = "<path>",
            description = "Paths to Kotlin libraries with .meta.js and .kjsm files, separated by system file separator")
    public String libraries;

    @GradleOption(DefaultValues.BooleanFalseDefault.class)
    @Argument(value = "-source-map", description = "Generate source map")
    public boolean sourceMap;

    @GradleOption(DefaultValues.BooleanTrueDefault.class)
    @Argument(value = "-meta-info", description = "Generate .meta.js and .kjsm files with metadata. Use to create a library")
    public boolean metaInfo;

    @GradleOption(DefaultValues.JsEcmaVersions.class)
    @Argument(value = "-target", valueDescription = "{ v5 }", description = "Generate JS files for specific ECMA version")
    public String target;

    @GradleOption(DefaultValues.JsModuleKinds.class)
    @Argument(
            value = "-module-kind",
            valueDescription = "{ plain, amd, commonjs, umd }",
            description = "Kind of a module generated by compiler"
    )
    public String moduleKind;

    @GradleOption(DefaultValues.JsMain.class)
    @Argument(value = "-main", valueDescription = "{" + CALL + "," + NO_CALL + "}", description = "Whether a main function should be called")
    public String main;

    @Argument(
            value = "-output-prefix",
            valueDescription = "<path>",
            description = "Path to file which will be added to the beginning of output file"
    )
    public String outputPrefix;

    @Argument(
            value = "-output-postfix",
            valueDescription = "<path>",
            description = "Path to file which will be added to the end of output file"
    )
    public String outputPostfix;

    // Advanced options

    @GradleOption(DefaultValues.BooleanFalseDefault.class)
    @Argument(value = "-Xtypedarrays", description = "Translate primitive arrays to JS typed arrays")
    public boolean typedArrays;

    @GradleOption(DefaultValues.BooleanFalseDefault.class)
    @Argument(value = "XfriendModulesDisabled", description = "Translate primitive arrays to JS typed arrays")
    public boolean friendModulesDisabled;

    @Argument(
            value = "XfriendModules",
            valueDescription = "<path>",
            description = "Paths to friend modules"
    )
    public String friendModules;

    @NotNull
    public static K2JSCompilerArguments createDefaultInstance() {
        K2JSCompilerArguments arguments = new K2JSCompilerArguments();
        arguments.moduleKind = K2JsArgumentConstants.MODULE_PLAIN;
        return arguments;
    }

    @Override
    @NotNull
    public String executableScriptFileName() {
        return "kotlinc-js";
    }
}
