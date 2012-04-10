(* Copyright 1989 by AT&T Bell Laboratories *)

signature PPUTIL =
sig

  datatype break_style = CONSISTENT | INCONSISTENT

  val openStyleBox : break_style -> PrettyPrint.stream -> PrettyPrint.indent -> unit

  val ppSequence : PrettyPrint.stream ->
		   {sep: PrettyPrint.stream->unit, 
		    pr: PrettyPrint.stream->'a->unit,
		    style: break_style}
		   -> 'a list -> unit
  val ppClosedSequence : PrettyPrint.stream
			 -> {front:PrettyPrint.stream->unit, 
                             sep:PrettyPrint.stream->unit,
			     back:PrettyPrint.stream->unit,
                             pr:PrettyPrint.stream->'a->unit,
			     style:break_style}
			 -> 'a list -> unit
  val ppSym : PrettyPrint.stream -> Symbol.symbol -> unit
  val mlstr : string -> string
  val pp_mlstr : PrettyPrint.stream -> string -> unit
  val pp_intinf : PrettyPrint.stream -> IntInf.int -> unit
  val ppvseq : PrettyPrint.stream
               -> int -> string -> (PrettyPrint.stream -> 'a -> unit)
               -> 'a list -> unit
  val ppvlist : PrettyPrint.stream
               -> string * string * (PrettyPrint.stream -> 'a -> unit) * 'a list
               -> unit
  val ppvlist' : PrettyPrint.stream
               -> string * string * (PrettyPrint.stream -> string -> 'a -> unit)
                    * 'a list
               -> unit
  val ppIntPath : PrettyPrint.stream -> int list -> unit
  val ppSymPath : PrettyPrint.stream -> SymPath.path -> unit
  val ppInvPath : PrettyPrint.stream -> InvPath.path -> unit
  val nl_indent : PrettyPrint.stream -> int -> unit

  (* needed in PPTypes, PPModules *)
  val findPath : InvPath.path * ('a -> bool) * (SymPath.path -> 'a)
                 -> (Symbol.symbol list * bool)

  val ppTuple: PrettyPrint.stream
	       -> (PrettyPrint.stream -> 'a -> unit) -> 'a list -> unit

  val ppi: PrettyPrint.stream -> int -> unit
  val ppcomma : PrettyPrint.stream -> unit
  val ppcomma_nl : PrettyPrint.stream -> unit
  val nl_app : PrettyPrint.stream -> (PrettyPrint.stream -> 'a -> unit)
               -> 'a list -> unit 
  val br_app : PrettyPrint.stream -> (PrettyPrint.stream -> 'a -> unit)
               -> 'a list -> unit 
  val en_pp : PrettyPrint.stream -> 
              {break      : {nsp: int, offset: int} -> unit, 
	       newline    : unit -> unit,
	       openHVBox  : int -> unit,
	       openHOVBox : int -> unit,
	       closeBox   : unit -> unit, 
	       pps        : string -> unit}
  val ppArray : PrettyPrint.stream -> 
                (PrettyPrint.stream -> 'a -> unit) * 'a array
	        -> unit

end (* signature PPUTIL *)
