# auto-update-version

version = "20240523"
author        = "Emery Hemingway"
description   = "data model and serialization format"
license       = "Unlicense"
srcDir        = "src"

bin           = @["preserves/preserves_schemac", "preserves/preserves_schema_nim", "preserves/private/preserves_encode"]

# Dependencies

requires "nim >= 2.0.0", "compiler >= 2.0.0", "https://github.com/zevv/npeg.git >= 1.2.1", "https://github.com/ehmry/nim-bigints.git >= 20231006"
