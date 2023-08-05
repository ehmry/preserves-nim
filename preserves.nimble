# Package

version = "20230805"
author        = "Emery Hemingway"
description   = "data model and serialization format"
license       = "Unlicense"
srcDir        = "src"

bin           = @["preserves/preserves_schema_nim", "preserves/private/preserves_encode", "preserves/schemac"]


# Dependencies

requires "nim >= 1.4.8", "compiler >= 1.4.8", "npeg"
