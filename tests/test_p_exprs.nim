# SPDX-License-Identifier: MIT

import
  pkg / balls, preserves, preserves / expressions

template testExpr(name, code, cntrl: string) {.dirty.} =
  test name:
    checkpoint code
    let
      pr = parsePreserves cntrl
      exprs = parseExpressions code
    checkpoint $(exprs.toPreserves)
    check exprs.len == 1
    let px = exprs[0]
    check px == pr

suite "expression":
  testExpr "date", """      <date 1821 (lookup-month "February") 3>
    """, """      <r date 1821 <g lookup-month "February"> 3>
    """
  testExpr "r", "<>", "<r>"
  testExpr "begin", """(begin (println! (+ 1 2)) (+ 3 4))""",
           """<g begin <g println! <g + 1 2>> <g + 3 4>>"""
  testExpr "g", """()""", """<g>"""
  testExpr "groups", """[() () ()]""", """[<g>, <g>, <g>]"""
  testExpr "loop", """      {
        setUp();
        # Now enter the loop
        loop: {
            greet("World");
        }
        tearDown();
      }
    """, """      <b
      setUp <g> <p |;|>
      # Now enter the loop
      loop <p |:|> <b
          greet <g "World"> <p |;|>
      >
      tearDown <g> <p |;|>
    >
  """
  testExpr "+", """      [1 + 2.0, print "Hello", predicate: #t, foo, #:remote, bar]
    """, """      [1 + 2.0 <p |,|> print "Hello" <p |,|> predicate <p |:|> #t <p |,|>
   foo <p |,|> #:remote <p |,|> bar]
   """
  testExpr "set", """#{1 2 3}""", """<s 1 2 3>"""
  testExpr "group-set", """#{(read) (read) (read)}""",
           """<s <g read> <g read> <g read>>"""
  testExpr "block", """      {
        optional name: string,
        address: Address,
      }
    """, """      <b
        optional name <p |:|> string <p |,|>
        address <p |:|> Address <p |,|>
      >
    """