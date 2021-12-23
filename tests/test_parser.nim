# SPDX-License-Identifier: MIT

import
  std / [strutils, unittest]

import
  preserves, preserves / parse

const
  examples = [("""<capture <discard>>""", "��\acapture��\adiscard��"),
    ("""[1 2 3 4]""", "������"), ("""[-2 -1 0 1]""", "������"),
    (""""hello"""", "�\x05hello"), ("""" \"hello\" """", "�\t \"hello\" "),
    ("""["a" b #"c" [] #{} #t #f]""", "��\x01a�\x01b�\x01c�������"),
    ("""-257""", "���"), ("""-1""", "�"), ("""0""", "�"), ("""1""", "�"),
    ("""255""", "�\x00�"), ("""1.0f""", "�?�\x00\x00"),
    ("""1.0""", "�?�\x00\x00\x00\x00\x00\x00"),
    ("""-1.202e300""", "��<��Y�\x04&"), (
      """#=#x"B4B30763617074757265B4B307646973636172648484"""",
      "��\acapture��\adiscard��"), ("""#f""", "�")]
suite "parse":
  for (txt, bin) in examples:
    test txt:
      checkpoint(txt)
      let test = parsePreserves(txt, int)
      checkpoint($test)
      block:
        let
          a = test
          b = decodePreserves(bin, int)
        check(a == b)
      block:
        let
          a = encode test
          b = bin
        check(cast[string](a).toHex == b.toHex)