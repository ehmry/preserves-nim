# Package

version = "20231220"
author        = "Emery Hemingway"
description   = "data model and serialization format"
license       = "Unlicense"
srcDir        = "src"

bin           = @["preserves/preserves_schema_nim", "preserves/private/preserves_encode", "preserves/schemac"]


# Dependencies

requires "nim >= 2.0.0", "compiler >= 1.4.8", "https://github.com/zevv/npeg.git >= 1.2.1"
