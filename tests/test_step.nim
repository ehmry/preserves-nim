# SPDX-License-Identifier: MIT

import
  std / [options, sequtils], pkg / balls, preserves

suite "step":
  var data = parsePreserves """      <foo "bar" [ 0.0 {a: #f, "b": #t } ] >
    """
  var o = some data
  for i in [1.toPreserves, 1.toPreserves, "b".toPreserves]:
    o = step(get o, i)
    check o.isSome