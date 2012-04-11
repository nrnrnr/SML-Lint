
signature REPORT = sig
  type t
  type name
  type pos
  val mk      : SourceMap.sourcemap -> t
  val pushDef : name * t -> t
  val popDef  : t -> t
  val brackets : string * pos * t -> t
  val report : t * TextIO.outstream -> unit
end

