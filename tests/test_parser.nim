# SPDX-License-Identifier: MIT

import
  std / [strutils, unittest]

import
  preserves, preserves / parse

const
  examples = [("""<capture <discard>>""", "´³\acapture´³\adiscard„„"),
    ("""[1 2 3 4]""", "µ‘’“”„"), ("""[-2 -1 0 1]""", "µŸ‘„"),
    (""""hello"""", "±\x05hello"), ("""" \"hello\" """", "±\t \"hello\" "),
    ("""["a" b #"c" [] #{} #t #f]""", "µ±\x01a³\x01b²\x01cµ„¶„€„"),
    ("""-257""", "¡şÿ"), ("""-1""", "Ÿ"), ("""0""", ""), ("""1""", "‘"),
    ("""255""", "¡\x00ÿ"), ("""1.0f""", "‚?€\x00\x00"),
    ("""1.0""", "ƒ?ğ\x00\x00\x00\x00\x00\x00"),
    ("""-1.202e300""", "ƒş<··Y¿\x04&"), (
      """#=#x"B4B30763617074757265B4B307646973636172648484"""",
      "´³\acapture´³\adiscard„„"), ("""#f""", "€")]
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