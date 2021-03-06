package org.jetbrains.kotlin.konan.library.impl

import org.jetbrains.kotlin.konan.file.File
import org.jetbrains.kotlin.konan.library.*
import org.jetbrains.kotlin.konan.properties.Properties
import org.jetbrains.kotlin.konan.properties.loadProperties
import org.jetbrains.kotlin.konan.properties.propertyList
import org.jetbrains.kotlin.konan.target.KonanTarget
import org.jetbrains.kotlin.konan.util.defaultTargetSubstitutions
import org.jetbrains.kotlin.konan.util.substitute


class KonanLibraryImpl(
        override val libraryFile: File,
        internal val target: KonanTarget?,
        override val isDefault: Boolean,
        private val metadataReader: MetadataReader
) : KonanLibrary {

    // For the zipped libraries inPlace gives files from zip file system
    // whereas realFiles extracts them to /tmp.
    // For unzipped libraries inPlace and realFiles are the same
    // providing files in the library directory.

    private val layout = createKonanLibraryLayout(libraryFile, target)

    override val libraryName: String by lazy { layout.inPlace { it.libraryName } }

    override val manifestProperties: Properties by lazy {
        val properties = layout.inPlace { it.manifestFile.loadProperties() }
        if (target != null) substitute(properties, defaultTargetSubstitutions(target))
        properties
    }

    override val versions: KonanLibraryVersioning
        get() = manifestProperties.readKonanLibraryVersioning()

    override val linkerOpts: List<String>
        get() = manifestProperties.propertyList(KLIB_PROPERTY_LINKED_OPTS)

    override val bitcodePaths: List<String>
        get() = layout.realFiles { (it.kotlinDir.listFilesOrEmpty + it.nativeDir.listFilesOrEmpty).map { it.absolutePath } }

    override val includedPaths: List<String>
        get() = layout.realFiles { it.includedDir.listFilesOrEmpty.map { it.absolutePath } }

    override val targetList by lazy { layout.inPlace { it.targetsDir.listFiles.map { it.name } } }

    override val dataFlowGraph by lazy { layout.inPlace { it.dataFlowGraphFile.let { if (it.exists) it.readBytes() else null } } }

    override val moduleHeaderData: ByteArray by lazy { layout.inPlace { metadataReader.loadSerializedModule(it) } }

    override fun packageMetadata(packageFqName: String, partName: String) =
            layout.inPlace { metadataReader.loadSerializedPackageFragment(it, packageFqName, partName) }

    override fun packageMetadataParts(fqName: String): Set<String> =
            layout.inPlace { inPlaceLayout ->
                val fileList =
                        inPlaceLayout.packageFragmentsDir(fqName)
                                .listFiles
                                .mapNotNull {
                                    it.name
                                            .substringBeforeLast(KLIB_METADATA_FILE_EXTENSION_WITH_DOT, missingDelimiterValue = "")
                                            .takeIf { it.isNotEmpty() }
                                }

                fileList.toSortedSet().also {
                    require(it.size == fileList.size) { "Duplicated names: ${fileList.groupingBy { it }.eachCount().filter { (_, count) -> count > 1 }}" }
                }
            }

    override fun toString() = "$libraryName[default=$isDefault]"
}