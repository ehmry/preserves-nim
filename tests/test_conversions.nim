# SPDX-License-Identifier: MIT

import
  streams, strutils, unittest

import
  bigints, preserves, preserves / records

suite "conversions":
  test "dictionary":
    type
      Bar = tuple[s: string]
    type
      Foobar = object
      
    let
      c = Foobar(a: 1, b: 2, c: (s: "ku"))
      b = toPreserve(c)
      a = preserveTo(b, Foobar)
    check(a == c)
    check(b.kind == pkDictionary)
    expect Defect:
      checkpoint $classOf(c)
  test "records":
    type
      Bar {.record: "bar".} = tuple[s: string]
    type
      Foobar {.record: "foo".} = object
      
    let
      c = Foobar(a: 1, b: 2, c: (s: "ku"))
      b = toPreserve(c)
      a = preserveTo(b, Foobar)
    check(a == c)
    check(b.kind == pkRecord)
    check(classOf(c) == RecordClass(label: symbol"foo", arity: 3))