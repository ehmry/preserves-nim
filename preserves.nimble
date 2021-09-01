# Package

version       = "0.3.0"
author        = "Emery Hemingway"
description   = "data model and serialization format"
license       = "Unlicense"
srcDir        = "src"

bin           = @["preserves/private/preserves_schema_nim"]


# Dependencies

requires "nim >= 1.4.8", "compiler >= 1.4.8", "bigints", "npeg"
