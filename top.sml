structure LintErr = LintFn(structure Report = ReportErr)

structure Lint = struct
  fun lint (source : Source.inputSource) dec =
    let val rpt = ReportErr.mk (#sourceMap source)
        val rpt = LintErr.elabDec(dec, LintErr.initEnv, SourceMap.nullRegion, rpt)
    in  rpt
    end


  fun parse filename =
    let val fd = TextIO.openIn filename
        val dev = PrettyPrintNew.defaultDevice
        val source = Source.newSource (filename, fd, false, dev)
    in  case MLParser.parse source ()
          of MLParser.PARSE dec => SOME (lint source dec)
           | _ => NONE
    end
end
