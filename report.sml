structure ReportErr : REPORT = struct
  fun eprint s = TextIO.output (TextIO.stdErr, s)

  type t = SourceMap.sourcemap
  type name = Symbol.symbol
  type pos  = SourceMap.charpos
  fun mk m = m
  fun pushDef (_, m) = m
  fun popDef m = m

  fun brackets (msg, pos, m) =
    let val {fileName, line, column} = SourceMap.filepos m pos
        val () = app eprint [fileName, ", line ", Int.toString line, ": ", msg, "\n"]
    in  m
    end        

  fun report _ = ()
end

