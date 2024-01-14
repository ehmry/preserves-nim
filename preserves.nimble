# Package

version = "20240114"
author        = "Emery Hemingway"
description   = "data model and serialization format"
license       = "Unlicense"
srcDir        = "src"

bin           = @["preserves/preserves_schema_nim", "preserves/private/preserves_encode", "preserves/schemac"]


# Dependencies

requires "nim >= 2.0.0", "compiler >= 2.0.0", "https://github.com/zevv/npeg.git >= 1.2.1", "https://github.com/ehmry/nim-bigints.git >= 20231006"
