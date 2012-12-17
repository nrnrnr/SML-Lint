structure ReportErr : REPORT = struct
  fun eprint s = TextIO.output (TextIO.stdErr, s)

  type t = SourceMap.sourcemap
  type name = Symbol.symbol
  type pos  = SourceMap.charpos
  type region = pos * pos
  fun mk m = m
  fun pushDef (_, m) = m
  fun popDef m = m

  fun brackets (around, (pos, _), m) =
    let val {fileName, line, column} = SourceMap.filepos m pos
        val () = app eprint [fileName, ", line ", Int.toString line,
                             ", column ", Int.toString column, ": ",
                             "redundant parentheses ", around, "\n"]
    in  m
    end        

  fun report _ = ()
end

