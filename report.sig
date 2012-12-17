
signature REPORT = sig
  type t
  type name
  type pos
  type region = pos * pos (* starting and ending position *)
  val mk      : SourceMap.sourcemap -> t
  val pushDef : name * t -> t
  val popDef  : t -> t
  val brackets : string * region * t -> t
  val report : t * TextIO.outstream -> unit
end

