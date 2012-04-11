structure Lint = struct
  fun parse filename =
    let val fd = TextIO.openIn filename
        val dev = PrettyPrintNew.defaultDevice
        val source = Source.newSource (filename, fd, false, dev)
    in  MLParser.parse source ()
    end
end