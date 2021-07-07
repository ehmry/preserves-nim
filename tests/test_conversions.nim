# SPDX-License-Identifier: MIT

import
  streams, strutils, unittest

import
  bigints, preserves, preserves / records

suite "conversions":
  test "dictionary":
    type
      Bar = object
      
    type
      Foobar = tuple[a, b: int, c: Bar]
    let
      c: Foobar = (a: 1, b: 2, c: Bar(s: "ku"))
      b = toPreserve(c)
      a = preserveTo(b, Foobar)
    check(a == c)
    check(b.kind == pkDictionary)
  test "records":
    type
      Bar {.record: "bar".} = object
      
    type
      Foobar {.record: "foo".} = tuple[a, b: int, c: Bar]
    let
      tup: Foobar = (a: 1, b: 2, c: Bar(s: "ku"))
      prs = toPreserve(tup)
    check(prs.kind == pkRecord)
    check(preserveTo(prs, Foobar) == tup)
    check(classOf(tup) == classOf(prs))