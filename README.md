# Preserves

Nim implementation of the [Preserves data language](https://preserves.dev/).

If you don't know why you need Preserves, see the [Syndicate library](https://git.syndicate-lang.org/ehmry/syndicate-nim).

## Library

To parse or produce Preserves one should write a [schema](https://preserves.dev/preserves-schema.html) and generate a Nim module using the [preserves_schema_nim](./src/preserves/preserves_schema_nim.nim) utility. This module will contain Nim types corresponding to schema definitions. The `toPreserve` and`fromPreserve` routines will convert Nim types to and from Preserves. The `decodePreserves`, `parsePreserves`, `encode`, and `$` routines will convert `Preserve` objects to and from binary and textual encoding.

To debug the `toPreserves` and `fromPreserves` routines compile with `-d:tracePreserves`.

## Utilities
* preserves-schema-nim
* preserves-encode
* preserves-decode
* preserves-from-json
* preserves-to-json
* preserves-from-xml
* preserves-to-xml

### Installation
`preserves_encode` is a multi-call binary that implements `preserves-encode`, `preserves-decode`, `preserves-from-json`, and `preserves-to-json`, so the appropriate symlinks should be created during packaging.
