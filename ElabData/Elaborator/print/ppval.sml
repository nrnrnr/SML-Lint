(* Copyright 1996 by AT&T Bell Laboratories *)
(* Copyright 2003 by The SML/NJ Fellowship *)
(* ppval.sml *)

(* modified to use SML/NJ Lib PP. [dbm, 7/30/03]) *)

signature PPVAL = 
sig
  val ppAccess: PrettyPrintNew.stream -> Access.access -> unit
  val ppRep: PrettyPrintNew.stream -> Access.conrep -> unit
  val ppDcon: PrettyPrintNew.stream -> VarCon.datacon -> unit
  val ppVar: PrettyPrintNew.stream -> VarCon.var -> unit
  val ppDebugDcon : PrettyPrintNew.stream
		    -> StaticEnv.staticEnv -> VarCon.datacon -> unit
  val ppDebugVar: (PrimOpId.primId -> string) ->
		  PrettyPrintNew.stream 
		  -> StaticEnv.staticEnv -> VarCon.var -> unit
end (* signature PPVAL *)

structure PPVal : PPVAL =
struct

local
  structure PP = PrettyPrintNew
  structure PU = PPUtilNew
  structure TU = TypesUtil
  structure LU = Lookup 
  structure A = Access
  open PrettyPrintNew PPUtilNew VarCon Types

in 

val internals = ElabControl.internals

fun C f x y = f y x

val pps = PP.string
val ppType = PPType.ppType
val ppTycon = PPType.ppTycon
val ppTyfun = PPType.ppTyfun

fun ppAccess ppstrm a = pps ppstrm (" ["^(A.prAcc a)^"]")

fun ppInfo ii2string ppstrm a = pps ppstrm (" ["^(ii2string a)^"]")

fun ppRep ppstrm rep = PP.string ppstrm (A.prRep rep)

fun ppCsig ppstrm csig = PP.string ppstrm (A.prCsig csig)

fun ppDcon ppstrm =
    let fun ppD(DATACON{name, rep=A.EXN acc, ...}) =
	       (ppSym ppstrm name;
		if !internals then ppAccess ppstrm acc else ())
	  | ppD(DATACON{name,...}) = ppSym ppstrm name
     in ppD
    end

fun ppDebugDcon ppstrm env (DATACON{name,rep,const,typ,sign,lazyp}) =
    let val {openHVBox, openHOVBox,closeBox,pps,break,...} = en_pp ppstrm
	val ppSym = ppSym ppstrm
     in openHVBox 3;
        pps "DATACON";
	break{nsp=0,offset=0};
	pps "{name = "; ppSym name; ppcomma_nl ppstrm;
	pps "const = "; pps (Bool.toString const); ppcomma_nl ppstrm;
	pps "typ = "; ppType env ppstrm typ; ppcomma_nl ppstrm;
	pps "lazyp = "; pps (Bool.toString lazyp); ppcomma_nl ppstrm;
	pps "conrep ="; ppRep ppstrm rep; ppcomma_nl ppstrm;
        pps "sign = ["; ppCsig ppstrm sign; pps "]}";
        closeBox()
    end

fun ppDatacon (env:StaticEnv.staticEnv,DATACON{name,typ,...}) ppstrm =
    let val {openHVBox, openHOVBox,closeBox,pps,...} = en_pp ppstrm
     in openHOVBox 0;
	ppSym ppstrm name; pps " : "; ppType env ppstrm typ;
	closeBox()
    end

fun ppConBinding ppstrm =
    let val {openHVBox, openHOVBox,closeBox,pps,...} = en_pp ppstrm
	fun ppCon (DATACON{name, typ, rep=A.EXN _, ...}, env) =
		(openHVBox 0;
		 pps "exception "; ppSym ppstrm name; 
                 if BasicTypes.isArrowType typ then
                   (pps " of "; 
   		    ppType env ppstrm (BasicTypes.domain typ))
                 else ();
		 closeBox())
	  | ppCon (con,env) = 
	      let exception Hidden
		  val visibleDconTyc =
		      let val tyc = TU.dconTyc con
		       in 
			  (TypesUtil.equalTycon
			      (LU.lookTyc
			         (env,SymPath.SPATH
				       [InvPath.last(TypesUtil.tycPath tyc)],
				  fn _ => raise Hidden),
			       tyc)
			     handle Hidden => false)
		      end
	       in if !internals orelse not visibleDconTyc 
	          then (openHVBox 0;
			pps "con ";
			ppDatacon(env,con) ppstrm;
		        closeBox())
	          else ()
	      end
     in ppCon
    end

fun ppVar ppstrm (VALvar {access,path,...}) =
      (pps ppstrm (SymPath.toString path);
       if !internals then ppAccess ppstrm access else ())
  | ppVar ppstrm (OVLDvar {name,...}) = ppSym ppstrm (name)
  | ppVar ppstrm (ERRORvar) = PP.string ppstrm "<errorvar>"

fun ppDebugVar ii2string ppstrm env  = 
    let val {openHVBox, openHOVBox,closeBox,pps,...} = en_pp ppstrm
	val ppAccess = ppAccess ppstrm
        val ppInfo = ppInfo ii2string ppstrm
	fun ppDV(VALvar {access,path, btvs, typ,prim}) = 
	     (openHVBox 0;
	      pps "VALvar";
	      openHVBox 3;
	      pps "({access="; ppAccess access; ppcomma_nl ppstrm;
              pps "prim="; ppInfo prim; ppcomma_nl ppstrm;
	      pps "path="; pps (SymPath.toString path); ppcomma_nl ppstrm;
	      pps "typ=ref "; ppType env ppstrm (!typ); 
	      pps "})";
	      closeBox(); closeBox())
	  | ppDV (OVLDvar {name,options,scheme}) = 
	     (openHVBox 0;
	      pps "OVLDvar";
	      openHVBox 3;
	      pps "({name="; ppSym ppstrm (name); ppcomma_nl ppstrm;
	      pps "options=["; 
	      (ppvseq ppstrm 0 ","
	       (fn ppstrm => fn {indicator,variant} =>
		  (pps "{indicator=";ppType env ppstrm  indicator; 
		   ppcomma_nl ppstrm;
		   pps " variant =";
		   ppDebugVar ii2string ppstrm env variant; pps "}"))
	       (!options));
	      pps "]"; ppcomma_nl ppstrm;
	      pps "scheme="; ppTyfun env ppstrm scheme; pps "})";
	      closeBox();
	      closeBox())
	  | ppDV (ERRORvar) = pps "<ERRORvar>"
     in ppDV
    end

fun ppVariable ppstrm  =
    let val {openHVBox, openHOVBox,closeBox,pps,...} = en_pp ppstrm
	fun ppV(env:StaticEnv.staticEnv,VALvar{btvs,path,access,typ,prim}) = 
	      (openHVBox 0;
	       pps(SymPath.toString path);
	       if !internals then ppAccess ppstrm access else ();
	       pps " : "; ppType env ppstrm (!typ);
	       closeBox())
	  | ppV (env,OVLDvar {name,options=ref optl,scheme=TYFUN{body,...}}) =
	      (openHVBox 0;
	       ppSym ppstrm (name); pps " : "; ppType env ppstrm body; 
	       pps " as ";
	       ppSequence ppstrm
		 {sep=C PP.break {nsp=1,offset=0},
		  pr=(fn ppstrm => fn{variant,...} => ppV(env,variant)),
		  style=CONSISTENT}
		 optl;
	       closeBox())
	  | ppV(_,ERRORvar) = pps "<ERRORvar>"
     in ppV
    end

end (* local *)
end (* structure PPVal *)
