# SPDX-License-Identifier: MIT

import
  ../preserves, ./private / macros

proc `%`*(n: SomeInteger): Value {.inline.} =
  n.toPreserves
