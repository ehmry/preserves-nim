# SPDX-License-Identifier: MIT

import
  ../preserves, ./private / macros

proc `%`*(v: bool | SomeFloat | SomeInteger | string | seq[byte] | Symbol): Value {.
    inline.} =
  v.toPreserves
