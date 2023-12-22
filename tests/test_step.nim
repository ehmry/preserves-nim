# SPDX-License-Identifier: MIT

import
  std / [options, sequtils, unittest]

import
  preserves

suite "step":
  var data = parsePreserves """      <foo "bar" [ 0.0 {a: #f, "b": #t } ] >
    """
  var o = some data
  for i in [1.toPreserve, 1.toPreserve, "b".toPreserve]:
    test $i:
      o = step(get o, i)
      check o.isSome