(* Copyright 1996 by AT&T Bell Laboratories *)
(* elabcore.sml *)

signature ELABCORE =
sig

  val elabABSTYPEdec :
        {abstycs: Ast.db list,withtycs: Ast.tb list,body: Ast.dec} 
        * StaticEnv.staticEnv * ElabUtil.context * (Types.tycon -> bool)
        * InvPath.path * SourceMap.region * ElabUtil.compInfo
        -> Absyn.dec * StaticEnv.staticEnv (* * Modules.entityEnv ??? *)

  val elabDec : 
        Ast.dec * StaticEnv.staticEnv * (Types.tycon -> bool)
        * InvPath.path * SourceMap.region * ElabUtil.compInfo
        -> Absyn.dec * StaticEnv.staticEnv

  val debugging : bool ref

end (* signature ELABCORE *)


structure ElabCore: ELABCORE =
struct

local structure EM = ErrorMsg
      structure SP = SymPath
      structure IP = InvPath
      structure SE = StaticEnv
      structure LU = Lookup
      structure V = VarCon
      structure B  = Bindings
      structure M  = Modules
      structure MU = ModuleUtil
      structure T  = Types
      structure TU = TypesUtil
      structure BT = BasicTypes
      structure EE = EntityEnv
      structure EU = ElabUtil
      structure ED = ElabDebug
      structure TS = TyvarSet
      structure ET = ElabType
      structure S = Symbol
      (* structure II = InlInfo *)
      structure A = Access

      structure Tbl = SymbolHashTable

      open Absyn Ast BasicTypes Access ElabUtil Types VarCon
   (*
      open BasicTypes Symbol Absyn Ast PrintUtil AstUtil BasicTypes TyvarSet
           Types EqTypes TypesUtil Access ElabUtil
    *)
in

fun cMARKpat (p, r) = if !ElabControl.markabsyn then MARKpat (p, r) else p
fun cMARKexp (e, r) = if !ElabControl.markabsyn then MARKexp (e, r) else e
fun cMARKdec (d, r) = if !ElabControl.markabsyn then MARKdec (d, r) else d

val say = Control_Print.say
val debugging = ElabControl.ecdebugging
fun debugmsg (msg: string) = if !debugging then (say msg; say "\n") else ()
fun bug msg = ErrorMsg.impossible("ElabCore: "^msg)

val debugPrint = (fn x => ED.debugPrint debugging x)

fun showDec(msg,dec,env) =
(*    ED.withInternals(fn () => *)
      debugPrint(msg,
		 (fn pps => fn dec =>
		   PPAbsyn.ppDec (env,NONE) pps (dec, 100)),
		 dec)(* ) *)

infix -->

(* tyvarset management *)
type tyvUpdate = TS.tyvarset -> unit
val --- = TS.diffPure
val union = TS.union
val diff = TS.diff
fun no_updt (_ : TS.tyvarset) = ()
fun noTyvars (dec,env) = (dec,env,TS.empty,no_updt)
infix ++ -- ---

fun stripExpAbs (MARKexp(e,_)) = stripExpAbs e
  | stripExpAbs (CONSTRAINTexp(e,_)) = stripExpAbs e
  | stripExpAbs e = e

fun stripExpAst(MarkExp(e,r'),r) = stripExpAst(e,r')
  | stripExpAst(ConstraintExp{expr=e,...},r) = stripExpAst(e,r)
  | stripExpAst(SeqExp[e],r) = stripExpAst(e,r)
  | stripExpAst(FlatAppExp[{item,region,...}],r) = stripExpAst(item,region)
  | stripExpAst x = x

val internalSym = SpecialSymbols.internalVarId

val dummyFNexp =
    FNexp([RULE(WILDpat,RAISEexp(CONexp(V.bogusEXN,[]),UNDEFty))],UNDEFty)
(** Updated CONexp ty option type -GK *)

(* LAZY *)
(* clauseKind: used for communicating information about lazy fun decls
   between preprocessing phase (makevar) and main part of elabFUNdec *)
datatype clauseKind = STRICT | LZouter | LZinner

(*
(* capture the  ":=" and "!" VALvars from PrimEnv.primEnv 
 *  These VALvars are used in lrvbMakeY.
 *  Perhaps PrimEnv should just export these VALvars. *)
val dummyComplainer = (fn _ => fn _ => fn _ => ())
val assignVar = 
    case LU.lookVal(PrimEnv.primEnv,SP.SPATH[S.strSymbol "InLine",S.varSymbol ":="],
		    dummyComplainer)
      of V.VAL v => v
       | _ => bug "lazy 1"
val bangVar = 
    case LU.lookVal(PrimEnv.primEnv,SP.SPATH[S.strSymbol "InLine",S.varSymbol "!"],
		    dummyComplainer)
      of V.VAL v => v
       | _ => bug "lazy 2"
val assignExp = VARexp(ref assignVar,NONE)
val bangExp = VARexp(ref bangVar,NONE)
*)

local
    fun mkCoreExp name env = VARexp (ref (CoreAccess.getVar env [name]), [])
in
    val mkAssignExp = mkCoreExp "assign"
    val mkBangExp = mkCoreExp "deref"
end

(**** ABSTRACT TYPE DECLARATIONS ****)
fun elabABSTYPEdec({abstycs,withtycs,body},env,context,isFree,
                   rpath,region,compInfo) =
  let val (datatycs,withtycs,_,env1) =
        ET.elabDATATYPEdec({datatycs=abstycs,withtycs=withtycs}, env,
                           [], EE.empty, isFree, rpath, region, compInfo)

      val (body,env2) = 
        elabDec(body,SE.atop(env1,env),isFree,rpath,region,compInfo)

      (* datatycs will be changed to abstycs during type checking
	 by changing the eqprop field *)
      fun bind (x, e) = SE.bind(TU.tycName x, B.TYCbind x, e)
      val envt = foldl bind (foldl bind SE.empty datatycs) withtycs 

   in (ABSTYPEdec{abstycs=datatycs,withtycs=withtycs,body=body},
       SE.atop(env2,envt))
  end (* function elabABSTYPEdec *)


(**** ELABORATE GENERAL (core) DECLARATIONS ****)
and elabDec (dec, env, isFree, rpath, region,
             compInfo as {mkLvar=mkv,error,errorMatch,...}) =

let
    val _ = debugmsg ">>ElabCore.elabDec"

    val completeMatch = EU.completeMatch(env,"Match")
    val _ = debugmsg "--ElabCore.elabDec << completeBind Match"
    val completeBind = EU.completeMatch(env,"Bind")
    val _ = debugmsg "--ElabCore.elabDec << completeBind Bind"

    fun newVALvar s = V.mkVALvar(s, A.namedAcc(s, mkv))


    (* LAZY: utilities for lazy sml translation *)
  
    (* will one forcingFun do, or should new ones be generated with
     * different bound variables for each use? (DBM) *)

    fun forceExp e = 
	let val v = newVALvar(S.varSymbol "x")
	 in APPexp(FNexp(completeMatch[RULE(APPpat(BT.dollarDcon,[],VARpat v),
				     VARexp(ref v,[]))],
			 UNDEFty),
		   e)
	     (* DBM: second arg of APPpat and VARexp = nil and 
	      * of FNexp = UNDEFty ok? *)
	end

    fun delayExp e = 
	APPexp(CONexp(BT.dollarDcon,[]), e)

    (* lrvbMakeY n: build declaration of n-ary Y combinator for lazy val rec *)
    fun lrvbMakeY n =
	let fun upto 0 = []
	      | upto n = n::(upto (n-1))
	    val base = rev(upto n)  (* [1,2,...,n] *)
	    fun repeat f = map f base

	    fun hold e = delayExp(forceExp e)

	    (* capture Match exn from coreEnv as a random exn for use internally
	       in the Y combinator definition *)
	    val exn = CoreAccess.getExn env ["Match"]

	    (* val exn = V.bogusEXN (* see if this will work? *) *)

	    (* Y variable and local variables ri and fi and d *)
	    val yvar (* as VALvar{path,typ,access,prim} *) =
		newVALvar(S.varSymbol("Y$"^(Int.toString n)))
	    fun mkVarSym s i = newVALvar(S.varSymbol(s^(Int.toString i)))
	    val rvars = repeat(mkVarSym "r$")
	    val fvars = repeat(mkVarSym "f$")
	    val dvar  = newVALvar(S.varSymbol "d$")

	    (* "ref($(raise Match))" *)
	    fun rdrExp _ = APPexp(CONexp(BT.refDcon,[]),
				  delayExp(RAISEexp(CONexp(exn,[]),UNDEFty)))
	    val rpat  = TUPLEpat (map VARpat rvars)
	    val rexp  = TUPLEexp (repeat rdrExp)
	    val rdec  = VALdec([VB{pat=rpat, exp=rexp, boundtvs=[], tyvars=ref[]}])

	    (* "$(force(!ri))" *)
	    fun dfbr rv = hold(APPexp(mkBangExp env,VARexp(ref rv,[])))
	    val ddec  = VALdec[VB{pat=VARpat dvar, exp=TUPLEexp(map dfbr rvars),
				  boundtvs=[],tyvars=ref[]}]

	    fun dexp () = VARexp(ref dvar,[])
	    fun setrExp (rv,fv) =
		APPexp(mkAssignExp env,
		       TUPLEexp([VARexp(ref rv,[]),
				 hold(APPexp(VARexp(ref fv,[]),dexp()))]))
	    val updates = ListPair.map setrExp (rvars,fvars)

	    val yexp = FNexp(completeMatch
			       [RULE(TUPLEpat(map VARpat fvars),
				     LETexp(SEQdec[rdec,ddec],
					    SEQexp(updates@[dexp()])))],
			     UNDEFty)

	 in (yvar,VALdec[VB{pat=VARpat yvar, exp=yexp, boundtvs=[], tyvars=ref[]}])
	end (* fun lrvbMakeY *)


    (**** EXCEPTION DECLARATIONS ****)

    fun elabEb (region:region) (env:SE.staticEnv) (eb:Ast.eb) =
	case eb
	  of EbGen{exn=id,etype=NONE} =>
	       let val exn =
		     DATACON{name=id, const=true, typ=exnTy, lazyp=false,
			     rep=EXN(LVAR(mkv(SOME id))), sign=CNIL}
		in ([EBgen{exn=exn, etype=NONE, 
                           ident=STRINGexp(S.name id)}], 
		    SE.bind(id, B.CONbind exn, SE.empty),TS.empty)
	       end
	   | EbGen{exn=id,etype=SOME typ} =>
	       let val (ty,vt) = ET.elabType(typ,env,error,region)
		   val exn = 
                     DATACON{name=id, const=false, typ=(ty --> exnTy), lazyp=false,
			     rep=EXN(LVAR(mkv(SOME id))), sign=CNIL}
		in ([EBgen{exn=exn,etype=SOME ty,
			   ident=STRINGexp(S.name id)}],
		    SE.bind(id,B.CONbind exn, SE.empty),vt) 
	       end
	   | EbDef{exn=id,edef=qid} =>
	       let val edef as DATACON{const,typ,sign,...} =
		     LU.lookExn(env,SP.SPATH qid,error region)
                   val nrep = EXN(LVAR(mkv(SOME id)))
	           val exn = DATACON{name=id, const=const, typ=typ, lazyp=false,
                                     sign=sign, rep=nrep}
		in ([EBdef{exn=exn,edef=edef}],
		    SE.bind(id,B.CONbind exn,SE.empty),TS.empty)
	       end
	   | MarkEb(eb,region) => elabEb region env eb

    fun elabEXCEPTIONdec(excbinds:Ast.eb list, env: SE.staticEnv, region) =
	let val (ebs,env,vt) = 
	      foldl
		(fn (exc1,(ebs1,env1,vt1)) =>
		   let val (eb2,env2,vt2) = elabEb region env exc1
		    in (eb2@ebs1, SE.atop(env2,env1),
                        union(vt1,vt2,error region))
		   end)
		 ([],SE.empty,TS.empty) excbinds
	    fun getname(EBgen{exn=DATACON{name,...},...}) = name
	      | getname(EBdef{exn=DATACON{name,...},...}) = name
	 in EU.checkUniq (error region, "duplicate exception declaration",
		       map getname ebs);
	    (EXCEPTIONdec(rev ebs),env,vt,no_updt)
	end


    (**** PATTERNS ****)

    fun apply_pat (c as MarkPat(_,(l1,r1)),p as MarkPat(_,(l2,r2))) = 
	  MarkPat(AppPat{constr=c, argument=p},(Int.min(l1,l2),Int.max(r1,r2)))
      | apply_pat (c ,p) = AppPat{constr=c, argument=p}

    fun tuple_pat (a as MarkPat(_,(l,_)),b as MarkPat(_,(_,r))) =
	  MarkPat(TuplePat[a,b],(l,r))
      | tuple_pat (a,b) = TuplePat[a,b]

    val patParse = Precedence.parse{apply=apply_pat, pair=tuple_pat}

    exception FreeOrVars
    fun elabPat(pat:Ast.pat, env:SE.staticEnv, region:region) 
		 : Absyn.pat * TS.tyvarset =
      case pat
      of WildPat => (WILDpat, TS.empty)
       | VarPat path => 
	   (clean_pat (error region) 
              (pat_id(SP.SPATH path, env, error region, compInfo)),
	    TS.empty)
       | IntPat s => (INTpat(s,TU.mkLITERALty(T.INT,region)),TS.empty)
       | WordPat s => (WORDpat(s,TU.mkLITERALty(T.WORD,region)),TS.empty)
       | StringPat s => (STRINGpat s,TS.empty)
       | CharPat s => (CHARpat s,TS.empty)
       | RecordPat {def,flexibility} =>
	    let val (lps,tyv) = elabPLabel region env def
	    in (makeRECORDpat (lps,flexibility,error region),tyv) end
       | ListPat nil =>
	      (NILpat, TS.empty)
       | ListPat (a::rest) =>
	    let val (p, tyv) = elabPat(TuplePat[a,ListPat rest], env, region)
	     in (CONSpat p, tyv)
	    end
       | TuplePat pats =>
	    let val (ps,tyv) = elabPatList(pats, env, region)
	     in (TUPLEpat ps,tyv)
	    end
       | VectorPat pats =>
	    let val (ps,tyv) = elabPatList(pats, env, region)
	    in (VECTORpat(ps,UNDEFty),tyv) end
       | OrPat pats =>
         (* Check that the sub-patterns of an or-pattern have exactly the same
          * free variables, and rewrite the sub-pattersn so that all instances
          * of a given free variable have the same type ref and the same 
          * access.
          *)
	   let val (ps, tyv) = elabPatList(pats, env, region)
	       fun freeOrVars (pat::pats) =
		   let val tbl : (access * ty ref * int) Tbl.hash_table =
			   Tbl.mkTable (16, FreeOrVars)
		       fun ins kv = Tbl.insert tbl kv
		       fun look k = Tbl.lookup tbl k
		       fun errorMsg x = 
			     error region EM.COMPLAIN
			       ("variable " ^ S.name x ^
			        " does not occur in all branches of or-pattern")
			       EM.nullErrorBody
		       fun insFn (id, access, tyref) =
			   (ins(id, (access, tyref, 1)); (access,tyref))
		       fun bumpFn (id, access0, tyref0) =
			   (let val (access, tyref, n) = look id
			     in ins (id, (access, tyref, n+1)); (access,tyref)
			    end
			    handle FreeOrVars => 
				    (errorMsg id; (access0,tyref0)))
		       fun checkFn (id, access0, tyref0) = 
                           (let val (access, tyref, _) = look id 
                             in (access, tyref) 
                            end
			    handle FreeOrVars => 
				   (errorMsg id; (access0, tyref0)))
		       fun doPat(insFn: (S.symbol*access*ty ref)
                                          ->access*ty ref) =
			   let fun doPat' (VARpat(VALvar{access, prim, path, 
                                                         btvs, typ})) =
				     let val (access,typ) = 
					 insFn(SymPath.first path,access,typ)
				      in VARpat(VALvar{access=access, 
                                                       path=path,prim=prim,
						       btvs = btvs,
						       typ=typ})
				     end
				 | doPat' (RECORDpat{fields, flex, typ}) =
				     RECORDpat
				       {fields = 
                                            map (fn (l, p) => (l, doPat' p))
						     fields,
					flex = flex, typ = typ}
				 | doPat' (APPpat(dc, ty, pat)) =
				     APPpat(dc, ty, doPat' pat)
				 | doPat' (CONSTRAINTpat(pat, ty)) =
				     CONSTRAINTpat(doPat' pat, ty)
				 | doPat' (LAYEREDpat(p1, p2)) =
				     LAYEREDpat(doPat' p1, doPat' p2)
				 | doPat' (ORpat(p1, p2)) =
				     ORpat(doPat' p1, doPat checkFn p2)
				 | doPat' (VECTORpat(pats, ty)) =
				     VECTORpat(map doPat' pats, ty)
				 | doPat' (MARKpat(pat, region)) =
				     doPat' pat  (*?? *)
				 | doPat' pat = pat
			      in doPat'
			     end
		     (* check that each variable occurs in each sub-pattern *)
		       fun checkComplete m (id, (_, _, n:int)) =
			   if (n = m) then () else (errorMsg id)
		       val pats = (doPat insFn pat) :: 
                                     (map (doPat bumpFn) pats)
		    in Tbl.appi (checkComplete (length pats)) tbl;
		       pats
		   end (* freeOrVars *)
		 | freeOrVars _ = bug "freeOrVars"
	       val (pat, pats) =
		   case freeOrVars ps of
		       (h::t) => (h, t)
		     | _ => bug "elabPat:no free or vars"
	       fun foldOr (p, []) = p
		 | foldOr (p, p'::r) = ORpat(p, foldOr(p', r))
	    in (foldOr(pat, pats), tyv)
	   end
       | AppPat {constr, argument} =>
	   let fun getVar (MarkPat(p,region),region') = getVar(p,region)
		 | getVar (VarPat path, region') = 
		      let val dcb = pat_id (SP.SPATH path, env, 
                                            error region', compInfo)
			  val (p,tv) = elabPat(argument, env, region)
		      in (makeAPPpat (error region) (dcb,p),tv) end
		 | getVar (_, region') = 
		   (error region' EM.COMPLAIN 
			 "non-constructor applied to argument in pattern"
			 EM.nullErrorBody;
		    (WILDpat,TS.empty))
	    in getVar(constr,region)
	   end
       | ConstraintPat {pattern=pat,constraint=ty} =>
	   let val (p1,tv1) = elabPat(pat, env, region)
	       val (t2,tv2) = ET.elabType(ty,env,error,region)
	    in (CONSTRAINTpat(p1,t2), union(tv1,tv2,error region))
	   end
       | LayeredPat {varPat,expPat} =>
	   let val (p1,tv1) = elabPat(varPat, env, region)
	       val (p2,tv2) = elabPat(expPat, env, region)
	    in (makeLAYEREDpat(p1,p2,error region),union(tv1,tv2,error region))
	   end
       | MarkPat (pat,region) =>
	   let val (p,tv) = elabPat(pat, env, region)
	    in (cMARKpat(p,region),tv)
	   end
       | FlatAppPat pats => elabPat(patParse(pats,env,error), env, region) 

    and elabPLabel (region:region) (env:SE.staticEnv) labs =
	foldl
	  (fn ((lb1,p1),(lps1,lvt1)) => 
	      let val (p2,lvt2) = elabPat(p1, env, region)
	      in ((lb1,p2) :: lps1, union(lvt2,lvt1,error region)) end)
	  ([],TS.empty) labs

    and elabPatList(ps, env:SE.staticEnv, region:region) =
	foldr
	  (fn (p1,(lps1,lvt1)) => 
	      let val (p2,lvt2) = elabPat(p1, env, region)
	      in (p2 :: lps1, union(lvt2,lvt1,error region)) end)
	  ([],TS.empty) ps


    (**** EXPRESSIONS ****)

    val expParse = Precedence.parse
		     {apply=fn(f,a) => AppExp{function=f,argument=a},
		      pair=fn (a,b) => TupleExp[a,b]}

    fun elabExp(exp: Ast.exp, env: SE.staticEnv, region: region) 
		: (Absyn.exp * TS.tyvarset * tyvUpdate) =
	(case exp
	  of VarExp path =>
	       ((case LU.lookVal(env,SP.SPATH path,error region)
		  of V.VAL v => VARexp(ref v,[])  
		   | V.CON(d as DATACON{lazyp,const,...}) =>
		      if lazyp then  (* LAZY *)
		        if const then delayExp(CONexp(d,[]))
			else let val var = newVALvar(S.varSymbol "x")
			      in FNexp(completeMatch
				        [RULE(VARpat(var),
					      delayExp(
					        APPexp(CONexp(d,[]),
						       VARexp(ref(var),[]))))],
				       UNDEFty (* DBM: ? *))
			     end
		      else CONexp(d, [])), 
		TS.empty, no_updt)
	   | IntExp s => 
               (INTexp(s,TU.mkLITERALty(T.INT,region)),TS.empty,no_updt)
           | WordExp s => 
               (WORDexp(s,TU.mkLITERALty(T.WORD,region)),TS.empty,no_updt)
	   | RealExp r => (REALexp r,TS.empty,no_updt)
	   | StringExp s => (STRINGexp s,TS.empty,no_updt)
	   | CharExp s => (CHARexp s,TS.empty,no_updt)
	   | RecordExp cells => 
	       let val (les,tyv,updt) = elabELabel(cells,env,region)
		in (makeRECORDexp (les,error region),tyv,updt)
	       end
	   | SeqExp exps =>
	       (case exps
		  of [e] => elabExp(e,env,region)
		   | [] => bug "elabExp(SeqExp[])"
		   | _ =>
		     let val (es,tyv,updt) = elabExpList(exps,env,region)
		      in (SEQexp es,tyv,updt)
		     end)
	   | ListExp nil => (NILexp, TS.empty, no_updt)
	   | ListExp (a::rest) =>
	       let val (e,tyv,updt) = 
                     elabExp(TupleExp[a,ListExp rest],env,region)
		in (APPexp(CONSexp,e), tyv, updt)
	       end
	   | TupleExp exps =>
	       let val (es,tyv,updt) = elabExpList(exps,env,region)
		in (TUPLEexp es,tyv,updt)
	       end
	   | VectorExp exps =>
	       let val (es,tyv,updt) = elabExpList(exps,env,region)
		in (VECTORexp(es,UNDEFty),tyv,updt)
	       end
	   | AppExp {function,argument} =>
	       let val (e1,tv1,updt1) = elabExp(function,env,region)
		   and (e2,tv2,updt2) = elabExp(argument,env,region)
		   fun updt tv = (updt1 tv;updt2 tv)
		in (APPexp (e1,e2),union(tv1,tv2,error region),updt)
	       end
	   | ConstraintExp {expr=exp,constraint=ty} =>
	       let val (e1,tv1,updt) = elabExp(exp,env,region)
		   val (t2,tv2) = ET.elabType(ty,env,error,region)
		in (CONSTRAINTexp(e1,t2), union(tv1,tv2,error region),updt)
	       end
	   | HandleExp {expr,rules} =>
	       let val (e1,tv1,updt1) = elabExp(expr,env,region)
		   val (rls2,tv2,updt2) = elabMatch(rules,env,region)
		   fun updt tv = (updt1 tv;updt2 tv)
		in (makeHANDLEexp (e1, rls2, compInfo), 
                    union(tv1,tv2,error region), updt)
	       end
	   | RaiseExp exp =>
	       let val (e,tyv,updt) = elabExp(exp,env,region)
		in (RAISEexp(e,UNDEFty),tyv,updt)
	       end
	   | LetExp {dec,expr} => 
	       let val (d1,e1,tv1,updt1) =
			  elabDec'(dec,env,IP.IPATH[],region)
		   val (e2,tv2,updt2) = elabExp(expr,SE.atop(e1,env),region)
		   fun updt tv = (updt1 tv;updt2 tv)
		in (LETexp(d1,e2), union(tv1,tv2,error region),updt)
	       end
	   | CaseExp {expr,rules} =>
	       let val (e1,tv1,updt1) = elabExp(expr,env,region)
		   val (rls2,tv2,updt2) = elabMatch(rules,env,region)
		   fun updt tv = (updt1 tv;updt2 tv)
		in (CASEexp (e1,completeMatch rls2, true),
		    union(tv1,tv2,error region),updt)
	       end
	   | IfExp {test,thenCase,elseCase} =>
	       let val (e1,tv1,updt1) = elabExp(test,env,region)
		   and (e2,tv2,updt2) = elabExp(thenCase,env,region)
		   and (e3,tv3,updt3) = elabExp(elseCase,env,region)
		   fun updt tv = (updt1 tv;updt2 tv;updt3 tv)
		in (Absyn.IFexp { test = e1, thenCase = e2, elseCase = e3 },
		    union(tv1,union(tv2,tv3,error region),error region),
		    updt)
	       end
	   | AndalsoExp (exp1,exp2) =>
	       let val (e1,tv1,updt1) = elabExp(exp1,env,region)
		   and (e2,tv2,updt2) = elabExp(exp2,env,region)
		   fun updt tv = (updt1 tv;updt2 tv)
		in (ANDALSOexp(e1, e2), union(tv1,tv2,error region),updt)
	       end
	   | OrelseExp (exp1,exp2) =>
	       let val (e1,tv1,updt1) = elabExp(exp1,env,region)
		   and (e2,tv2,updt2) = elabExp(exp2,env,region)
		   fun updt tv = (updt1 tv;updt2 tv)
		in (ORELSEexp(e1, e2), union(tv1,tv2,error region),updt)
	       end
	   | WhileExp {test,expr} =>
	       let val (e1,tv1,updt1) = elabExp(test,env,region)
		   and (e2,tv2,updt2) = elabExp(expr,env,region)
		   fun updt tv = (updt1 tv;updt2 tv)
		in (Absyn.WHILEexp { test = e1, expr = e2 },
                    union(tv1,tv2,error region), updt)
	       end
	   | FnExp rules => 
	       let val (rls,tyv,updt) = elabMatch(rules,env,region)
		in (FNexp (completeMatch rls,UNDEFty),tyv,updt)
	       end
	   | MarkExp (exp,region) => 
	       let val (e,tyv,updt) = elabExp(exp,env,region)
		in (cMARKexp(e,region), tyv, updt)
	       end
	   | SelectorExp s => 
	       (let val v = newVALvar s
		 in FNexp(completeMatch
			  [RULE(RECORDpat{fields=[(s,VARpat v)], flex=true,
					  typ= ref UNDEFty},
				cMARKexp(VARexp(ref v,[]),region))],UNDEFty)
		end,
		TS.empty, no_updt)
	   | FlatAppExp items => elabExp(expParse(items,env,error),env,region))


    and elabELabel(labs,env,region) =
	let val (les1,lvt1,updt1) =
	      foldr 
		(fn ((lb2,e2),(les2,lvt2,updts2)) => 
		    let val (e3,lvt3,updt3) = elabExp(e2,env,region)
		     in ((lb2,e3) :: les2, union(lvt3,lvt2,error region),
			 updt3 :: updts2)
		    end)
		([],TS.empty,[]) labs
	    fun updt tv : unit = app (fn f => f tv) updt1
	 in (les1, lvt1, updt)
	end

    and elabExpList(es,env,region) =
	let val (les1,lvt1,updt1) =
	      foldr 
		(fn (e2,(es2,lvt2,updts2)) => 
		    let val (e3,lvt3,updt3) = elabExp(e2,env,region)
		     in (e3 :: es2, union(lvt3,lvt2,error region), 
                         updt3 :: updts2)
		    end)
		([],TS.empty,[]) es
	    fun updt tv: unit = app (fn f => f tv) updt1
	 in (les1, lvt1, updt)
	end

    and elabMatch(rs,env,region) =
	let val (rs,lvt,updt1) =
	      foldr 
		(fn (r1,(rs1,lvt1,updt1)) => 
		    let val (r2,lvt2,updt2) = elabRule(r1,env,region)
		     in (r2 :: rs1, union(lvt2,lvt1,error region), 
                         updt2::updt1) 
                    end)
		([],TS.empty,[]) rs
	    fun updt tv: unit = app (fn f => f tv) updt1
	 in (rs, lvt, updt)
	end

    and elabRule(Rule{pat,exp},env,region)  =
	let val region' = case pat of MarkPat (p,reg) => reg | _ => region
	    val (p,tv1) = elabPat(pat, env, region)
	    val env' = SE.atop(bindVARp ([p],error region'), env)
	    val (e,tv2,updt) = elabExp(exp,env',region)
	 in (RULE(p,e),union(tv1,tv2,error region),updt)
	end


    (**** SIMPLE DECLARATIONS ****)

    and elabDec'(dec,env,rpath,region)
		: (Absyn.dec * SE.staticEnv * TS.tyvarset * tyvUpdate) =
	(case dec 
	  of TypeDec tbs => 
	      let val (dec', env') =
		  ET.elabTYPEdec(tbs,env,(* EU.TOP,??? *) rpath,region,compInfo)
	       in noTyvars(dec', env')
	      end
	   | DatatypeDec(x) => 
	      let val (dtycs, wtycs, _, env') =
		      ET.elabDATATYPEdec(x,env,[],EE.empty,isFree,
                                         rpath,region,compInfo)
	       in noTyvars(DATATYPEdec{datatycs=dtycs,withtycs=wtycs}, env')
	      end
	   | DataReplDec(name,path) => 
	     (* LAZY: not allowing "datatype lazy t = datatype t'" *)
	     (* BUG: what to do if rhs is lazy "datatype"? (DBM) *)
	      (case LU.lookTyc(env, SP.SPATH path, error region)
		 of (dtyc as T.GENtyc{kind=T.DATATYPE _,...}) =>
		    let val dcons = TU.extractDcons dtyc
			val envDcons =
			    foldl (fn (d as T.DATACON{name,...},e)=>
				      SE.bind(name,B.CONbind d, e))
				  SE.empty 
				  dcons
                        (* types of new datacon bindings same as the old *)
			val env = SE.bind(name,B.TYCbind dtyc,envDcons)
		     in noTyvars(DATATYPEdec{datatycs=[dtyc], 
					     withtycs=[]},
				 env)
		    end
		  | _ => (* error if not a datatype (bug 1578.1) *)
		    ((error region EM.COMPLAIN
			    "rhs of datatype replication not a datatype"
			    EM.nullErrorBody);
		     noTyvars(SEQdec[], SE.empty)))
	   | AbstypeDec x => 
	      let val (dec', env') =
  		    elabABSTYPEdec(x,env,EU.TOP,isFree,
                                   rpath,region,compInfo)
	       in noTyvars(dec', env')
	      end
	   | ExceptionDec ebs => elabEXCEPTIONdec(ebs,env,region)
	   | ValDec(vbs,explicitTvs) =>
	       elabVALdec(vbs,explicitTvs,env,rpath,region)
	   | FunDec(fbs,explicitTvs) =>
	       elabFUNdec(fbs,explicitTvs,env,rpath,region)
	   | ValrecDec(rvbs,explicitTvs) =>
	       elabVALRECdec(rvbs,explicitTvs,env,rpath,region)
	   | SeqDec ds => elabSEQdec(ds,env,rpath,region)
	   | LocalDec ld => elabLOCALdec(ld,env,rpath,region)
	   | OpenDec ds => elabOPENdec(ds,env,region)
	   | FixDec (ds as {fixity,ops}) => 
	       let val env = 
		 foldr (fn (id,env) => SE.bind(id,B.FIXbind fixity,env))
			SE.empty ops
		in (FIXdec ds,env,TS.empty,no_updt)
	       end
	   | OvldDec dec  => elabOVERLOADdec(dec,env,rpath,region)
	   | MarkDec(dec,region') =>
	       let val (d,env,tv,updt)= elabDec'(dec,env,rpath,region')
		in (cMARKdec(d,region'), env,tv,updt)
	       end
	   | StrDec _ => bug "strdec"
	   | AbsDec _ => bug "absdec"
	   | FctDec _ => bug "fctdec"
	   | SigDec _ => bug "sigdec"
	   | FsigDec _ => bug "fsigdec")
              

    (**** OVERLOADING ****)

    and elabOVERLOADdec((id,typ,exps),env,rpath,region) =
	let val (body,tyvars) = ET.elabType(typ,env,error,region)
	    val tvs = TS.elements tyvars
	    val scheme = (TU.bindTyvars tvs; TU.compressTy body;
			  TYFUN{arity=length tvs, body=body})
	    fun option (MARKexp(e,_)) = option e
	      | option (VARexp(ref (v as VALvar{typ,...}),_)) =
		  {indicator = TU.matchScheme(scheme,!typ), variant = v}
	      | option _ = bug "makeOVERLOADdec.option"
	    val exps = map (fn exp => elabExp(exp,env,region)) exps
	    val exps1 = map #1 exps
	    and exps3 = map #3 exps
	    fun updt tv: unit = app (fn f => f tv) exps3
	    val ovldvar = OVLDvar{name=id,scheme=scheme,
				  options=ref(map option exps1)}
	 in (OVLDdec ovldvar, SE.bind(id,B.VALbind ovldvar,SE.empty),
             TS.empty, updt)
	end

    (**** LOCAL ****)

    and elabLOCALdec((ldecs1,ldecs2),env,rpath:IP.path,region) =
	let val (ld1,env1,tv1,updt1) = elabDec'(ldecs1,env,IP.IPATH[],region)
	    val (ld2,env2,tv2,updt2) =
		  elabDec'(ldecs2,SE.atop(env1,env),rpath,region)
	    fun updt tv = (updt1 tv;updt2 tv)
	 in (LOCALdec(ld1,ld2), env2,union(tv1,tv2,error region),updt)
	end

    (**** OPEN ****)

    and elabOPENdec(spaths, env, region) = 
        let val err = error region
	    val strs = map (fn s => let val sp = SP.SPATH s
                                     in (sp, LU.lookStr(env, sp, err))
                                    end) spaths
	    
            fun loop([], env) = (OPENdec strs, env, TS.empty, no_updt)
              | loop((_, s)::r, env) = loop(r, MU.openStructure(env, s))

         in loop(strs, SE.empty)
        end 

    (****  VALUE DECLARATIONS ****)
    (* elabVB : Ast.vb * tyvar list * staticEnv * region
                ->  ... *)
    and elabVB (MarkVb(vb,region),etvs,env,_) =
          (* pass through MarkVb, updating region parameter *)
          let val (d, tvs, u) = elabVB(vb,etvs,env,region)
              val d' = cMARKdec (d, region)
           in (d', tvs, u)
          end
      | elabVB (Vb{pat,exp,lazyp},etvs,env,region) =
	  let val (pat,pv) = elabPat(pat, env, region)
	      val (exp,ev,updtExp) = elabExp(exp,env,region)
	      val exp = if lazyp  (* LAZY *)
		        then delayExp(forceExp exp)
			else exp

              (* tracking user (or "explicit") type variables *)
	      val tvref = ref []
	      fun updt tv: unit =
		let fun a++b = union(a,b,error region)
                    fun a--b = diff(a,b,error region)
		    val localtyvars = (ev++pv++etvs) -- (tv---etvs)
			 (* etvs should be the second argument to union
			  * to avoid having the explicit type variables
			  * instantiated by the union operation. *)
		    val downtyvars = localtyvars ++ (tv---etvs)
		 in tvref := TS.elements localtyvars; updtExp downtyvars
	        end

              (* The following code propagates a PRIMOP access
               * through a simple aliasing value binding.
               * WARNING [ZHONG] This is an old hack and should be
               * replaced. 
	       * [DBM] This won't apply if lazyp=true.
               *)
              fun stripMarksVar (MARKpat(p as VARpat _, reg)) = p
                | stripMarksVar (MARKpat(p,reg)) = stripMarksVar p
                | stripMarksVar (CONSTRAINTpat (p, ty)) =
                    CONSTRAINTpat(stripMarksVar p, ty)
                | stripMarksVar p = p

	      val pat = 
		case stripExpAbs exp
		 of VARexp(ref(VALvar{prim,...}),_) =>
                      (case prim
                         of PrimOpId.Prim _ => 
		            (case stripMarksVar pat
			      of CONSTRAINTpat(VARpat(VALvar{path,typ,btvs,
                                                             access,...}), ty) =>
			         CONSTRAINTpat(
                                   VARpat(
                                     VALvar{path=path, typ=typ, access=access,
                                            btvs = btvs, prim=prim}),
                                   ty)
			       | VARpat(VALvar{path, typ, btvs, access, ...}) =>
			         VARpat(VALvar{path=path, typ=typ,
				 	       btvs = btvs, access=access,
                                               prim=prim})
			       | _ => pat)
                          | PrimOpId.NonPrim => pat)
		  | _ => pat

	   in (VALdec([VB{exp=exp, tyvars=tvref, pat=pat, boundtvs=[]}]), [pat], updt) 
(* old version
             case pat
               of (VARpat _ | CONSTRAINTpat(VARpat _,_)) => (* variable pattern *)
                   (VALdec([VB{exp=exp, tyvars=tvref, pat=pat, boundtvs=[]}]),
                    [pat], updt) 
                | _ => (* Nonvariable pattern binding will be "normalized"
                        * into a more complex declaration using only
                        * simple variable valbinds. See DEVNOTE/valbind.txt. *)
		   let val (newpat,oldvars,newvars) = aconvertPat(pat, compInfo)
		         (* this is the only call of aconvertPat *)
                       val newVarExps = map (fn v => VARexp(ref v,[])) newvars 
		       val r = RULE(newpat, TUPLEexp(newVarExps))
                       val newexp = CASEexp(exp, completeBind[r], false)

                    in case oldvars
                        of [] => 
                             let val nvb = VB{exp=newexp, tyvars=tvref,
                                              pat=WILDpat, boundtvs=[]}
                              in (VALdec [nvb], [], updt)
                             end
                         | _ => 
                             let val newVar = newVALvar internalSym
                                 val newVarPat = VARpat(newVar)
                                 val newVarExp = VARexp(ref newVar, [])

                                 val newVarDec = 
                                     VALdec([VB{exp=newexp, tyvars=tvref, 
                                                pat=newVarPat, boundtvs=[]}])

                                 fun buildDec([], _, d) =  
                                     LOCALdec(newVarDec, SEQdec(rev d))
                                   | buildDec(vp::r, i, d) = 
                                     let val nvb = VB{exp=TPSELexp(newVarExp,i),
                                                      pat=vp, boundtvs=[],
                                                      tyvars=ref[]}

                                      in buildDec(r, i+1, VALdec([nvb])::d)
                                     end

                              in (buildDec(oldvars, 1, []), oldvars, updt)
                             end
                   end
*)
	  end

    and elabVALdec(vb,etvs,env,rpath,region) =
       let val etvs = ET.elabTyvList(etvs,error,region)
	   val (ds,pats,updt1) = 
	      foldr 
		(fn (vdec,(ds1,pats1,updt1)) => 
		   let val etvs = TS.mkTyvarset(map T.copyTyvar etvs)
		       val (d2,pats2,updt2) = elabVB(vdec,etvs,env,region)
		    in (d2::ds1,pats2@pats1,updt2::updt1) 
                   end)
		([],[],[]) vb
	    fun updt tv : unit = app (fn f => f tv) updt1
	in (SEQdec ds, bindVARp (pats,error region), TS.empty, updt)
       end

    and elabRVB(MarkRvb(rvb,region),env,_) =
	let val ({ match, ty, name }, tvs, u) = elabRVB(rvb,env,region)
	    val match' = cMARKexp (match, region)
	in
	    ({ match = match', ty = ty, name = name }, tvs, u)
	end
      | elabRVB(Rvb{var,fixity,exp,resultty,lazyp},env,region) =
         (case stripExpAst(exp,region)
	    of (FnExp _,region')=>
	        let val (e,ev,updt) = elabExp(exp,env,region')
		    val (t,tv) = 
			case resultty 
			  of SOME t1 => 
			       let val (t2,tv2) = ET.elabType(t1,env,error,region)
				in (SOME t2,tv2)
			       end
			   | NONE => (NONE,TS.empty)
		 in case fixity 
		      of NONE => ()
		       | SOME(f,region) => 
			 (case LU.lookFix(env,f) 
			   of Fixity.NONfix => ()
			    | _ =>
			      error region EM.COMPLAIN
			        ("infix symbol \""^ S.name f ^
				 "\" used where a nonfix identifier was expected")
				EM.nullErrorBody);
		    ({match = e , ty = t, name=var},
		     union(ev,tv,error region),updt)
		end
	     | _ =>
		(error region EM.COMPLAIN
		  "fn expression required on rhs of val rec"
		  EM.nullErrorBody;
		 ({match = dummyFNexp, ty = NONE, name = var},TS.empty,no_updt)))

    and elabVALRECstrict(rvbs,etvs,env,region) = 
	let val env' = ref(SE.empty: SE.staticEnv)
	    fun makevar region (p as Rvb{var,...}) =
		  let val v = newVALvar var
                      val nv = newVALvar var (* DBM: what is this for? *)
		   in (* checkBoundConstructor(env,var,error region); -- fix bug 1357 *)
		      env' := SE.bind(var,B.VALbind v,!env');
		      (v, p)
		  end
	      | makevar _ (p as MarkRvb(rvb,region)) = 
		  let val (v,_) = makevar region rvb in (v,p) end

	    val rvbs' = map (makevar region) rvbs
	    val env'' = SE.atop(!env', env)
	    val (rvbs,tyvars,updts)=
		foldl (fn((v,rvb1),(rvbs1,tvs1,updt1)) =>
			   let val (rvb2,tv2,updt2) =
				   elabRVB(rvb1,env'',region)
			    in ((v,rvb2)::rvbs1, 
				union(tv2,tvs1,error region),
				updt2::updt1)
			   end) 
			([],TS.empty,[]) rvbs' 
	    val tvref = ref []
	    fun updt tvs : unit =  
		let fun a++b = union(a,b,error region)
		    fun a--b = diff(a,b,error region)
		    val localtyvars = (tyvars ++ etvs) -- (tvs --- etvs)
		    val downtyvars = localtyvars ++ (tvs --- etvs)
		 in tvref := TS.elements localtyvars;
		    app (fn f => f downtyvars) updts
		end
	    val _ = EU.checkUniq(error region,
                        "duplicate function name in val rec dec",
  		        (map (fn (v,{name,...}) => name) rvbs))

            val (ndec, nenv) = 
  	        wrapRECdec((map (fn (v,{ty,match,name}) =>
				    RVB{var=v,resultty=ty,tyvars=tvref, exp=match,
					boundtvs=[]})
			        rvbs),
			   compInfo)
         in (ndec, nenv, TS.empty, updt)
	end (* fun elabVALRECstrict *)

    (* LAZY: "val rec lazy ..." *)
    and elabVALREClazy (rvbs,etvs,env,region) = 
	let fun split [] = ([],[])
	      | split ((Rvb {var,exp,resultty,lazyp,...})::xs) =
		 let val (a,b) = split xs in ((var,resultty)::a,(exp,lazyp)::b) end
	      | split ((MarkRvb (x,_))::xs) = split (x::xs) (* loosing regions *)

	    val (yvar,declY) = lrvbMakeY (length rvbs)

	    val (lhss,exps) = split rvbs
	    val argpat = TuplePat(map (fn (sym,NONE) => VarPat[sym]
					| (sym,SOME ty) =>
					    ConstraintPat{pattern=VarPat[sym],
							  constraint=ty})
				      lhss)

	    fun elabFn((exp,lazyp),(fexps,tvs,updts)) =
		let val (p,tv1) = elabPat(argpat, env, region)
		    val env' = SE.atop(bindVARp ([p],error region), env)
		    val (e,tv2,updt) = elabExp(exp,env',region)
		in (FNexp(completeMatch[RULE(p,if lazyp then e else delayExp e)],
			  UNDEFty)::fexps,
		    union(union(tv1,tv2,error region),tvs,error region),
		    updt::updts)
		end

	    val (fns,tyvars,updts) = foldr elabFn ([],TS.empty,[]) exps

	    val lhsSyms = map #1 lhss  (* left hand side symbols *)
	    val lhsVars = map newVALvar lhsSyms

	    (* copied from original elabVALRECdec *)
	    val tvref = ref []
	    fun updt tvs : unit =  
		let fun a++b = union(a,b,error region)
		    fun a--b = diff(a,b,error region)
		    val localtyvars = (tyvars ++ etvs) -- (tvs --- etvs)
		    val downtyvars = localtyvars ++ (tvs --- etvs)
		 in tvref := TS.elements localtyvars;
		    app (fn f => f downtyvars) updts
		end

	    val declAppY =
		VALdec[VB{pat=TUPLEpat(map VARpat lhsVars),
			  exp=APPexp(VARexp(ref yvar,[]),TUPLEexp fns),
			  tyvars=tvref,boundtvs=[]}]

	    fun forceStrict ((sym,var1,lazyp),(vbs,vars)) =
		  let val var2 = newVALvar sym
		      val vb = if lazyp
			       then VB{pat=VARpat var2, 
				       exp=VARexp (ref var1,[]),boundtvs=[],
				       tyvars=ref[]}
			       else VB{pat=APPpat(BT.dollarDcon,[],(VARpat var2)), 
				       exp=VARexp (ref var1,[]),boundtvs=[],
				       tyvars=ref[]}
		  in  (vb::vbs,var2::vars)
		  end

	    fun zip3(x::xs,y::ys,z::zs) = (x,y,z)::zip3(xs,ys,zs)
	      | zip3(nil,_,_) = nil
	      | zip3 _ = bug "zip3"

	    val (vbs,vars) =
		foldr forceStrict ([],[]) (zip3(lhsSyms,lhsVars,map #2 exps))

	    val env' = foldl (fn ((s,v),env) => SE.bind(s,B.VALbind v,env)) SE.empty
			     (ListPair.zip(lhsSyms,vars))

	    val absyn = LOCALdec(SEQdec[declY,declAppY],VALdec vbs)
	 in showDec("elabVALREClazy: ",absyn,env');
	    (absyn,env',TS.empty(*?*),updt)
	end (* fun elabVALREClazy *)

    and elabVALRECdec(rvbs: rvb list,etvs,env,rpath:IP.path,region) = 
	let val etvs = TS.mkTyvarset(ET.elabTyvList(etvs,error,region))
	    fun isLazy(Rvb{lazyp,...}) = lazyp
	      | isLazy(MarkRvb(rvb,_)) = isLazy rvb
         in if List.exists isLazy rvbs
	    then elabVALREClazy(rvbs,etvs,env,region)
	    else elabVALRECstrict(rvbs,etvs,env,region) 
	end

    and elabFUNdec(fb,etvs,env,rpath,region) =
	let val etvs = TS.mkTyvarset(ET.elabTyvList(etvs,error,region))
            (* makevar: parse the function header to determine the function name *)
	    fun makevar _ (MarkFb(fb,fbregion),ctx) = makevar fbregion (fb,ctx)
	      | makevar fbregion (Fb(clauses,lazyp),(lcl,env')) =
		 let fun getfix(SOME f) = LU.lookFix(env,f)
		       | getfix NONE = Fixity.NONfix

		     fun ensureInfix{item,fixity,region} =
			 (case getfix fixity
			   of Fixity.NONfix =>
			        error region EM.COMPLAIN
			          "infix operator required, or delete parentheses" 
			          EM.nullErrorBody
			    | _ => ();
			  item)

		     fun ensureNonfix{item,fixity,region} =
			 (case (getfix fixity, fixity)
			   of (Fixity.NONfix,_) => ()
			    | (_,SOME sym) =>
			       error region EM.COMPLAIN
				 ("infix operator \"" ^ S.name sym ^
				  "\" used without \"op\" in fun dec")
				 EM.nullErrorBody
			    | _ => bug "ensureNonfix";
			  item)

		     fun getname(MarkPat(p,region),_) = getname(p,region)
		       | getname(VarPat[v], _) = v
		       | getname(_, region) = 
                           (error region EM.COMPLAIN
			      "illegal function symbol in clause"
			      EM.nullErrorBody;
			    bogusID)

   	             fun parse'({item=FlatAppPat[a,b as {region,...},c],...}
                                ::rest) = 
			   (getname(ensureInfix b, region),
			    tuple_pat(ensureNonfix a, ensureNonfix c)
			     :: map ensureNonfix rest)
		       | parse' [{item,region,...}] = 
			   (error region EM.COMPLAIN
			      "can't find function arguments in clause"
			      EM.nullErrorBody;
			    (getname(item,region), [WildPat]))
		       | parse' ((a as {region,...}) :: rest) =
			   (getname(ensureNonfix a, region), 
			    map ensureNonfix rest)
		       | parse' [] = bug "parse':[]"

		     fun parse({item=MarkPat(p,_),region,fixity}::rest) = 
			   parse({item=p,region=region,fixity=fixity}::rest)
		       | parse (pats as [a as {region=ra,...},
					 b as {item,fixity,region},c]) =
			   (case getfix fixity
			      of Fixity.NONfix => parse' pats
			       | _ => (getname(item,region),
				  [tuple_pat(ensureNonfix a, ensureNonfix c)]))
		       | parse pats = parse' pats

		     fun parseClause(Clause{pats,resultty,exp}) =
			 let val (funsym,argpats) = parse pats
			  in {kind=STRICT,funsym=funsym,argpats=argpats,
			      resultty=resultty,exp=exp}
			 end

		     val (clauses, var) = 
                         case map parseClause clauses of
			     [] => bug "elabcore:no clauses"
			   | (l as ({funsym=var,...}::_)) => (l,var)

		     val _ = if List.exists (fn {funsym,...} => 
					not(S.eq(var,funsym))) clauses
			     then  error fbregion EM.COMPLAIN 
				     "clauses don't all have same function name"
				     EM.nullErrorBody
			     else ()

(* DBM: fix bug 1357
		     val _ = checkBoundConstructor(env,var,error fbregion)
*)
		     val v = newVALvar var

		     val argcount = 
			 case clauses
			   of ({argpats,...})::rest => 
				let val len = length argpats
				 in if List.exists
					(fn {argpats,...} => 
					      len <> length argpats) rest
				    then error fbregion EM.COMPLAIN 
				   "clauses don't all have same number of patterns"
					  EM.nullErrorBody
				    else ();
				    len
				end
			    | [] => bug "elabFUNdec: no clauses"
		  in if lazyp (* LAZY *)
		     then let fun newArgs(args,0) = args
				| newArgs(args,n) = 
				  newArgs([S.varSymbol("$"^Int.toString n)]::args,
					  n-1)
			      fun curryApp (f,[]) = f
				| curryApp (f,x::xs) =
				  curryApp(AppExp{function=f, argument=x},xs)
			      val lazyvar = S.varSymbol(S.name var ^ "_")
			      val lv = newVALvar lazyvar
			      fun mkLazy(new,resty,[]) = (rev new,resty)
			        | mkLazy(new,resty,
					 {kind,funsym,argpats,resultty,exp}::rest) =
				  mkLazy({kind=LZinner,funsym=lazyvar,argpats=argpats,
					  resultty=NONE, (* moved to outer clause *)
					  exp=exp}
				         ::new,
				         case resty
					   of NONE => resultty
					    | _ => resty,
					 rest)
                              (* BUG: this captures the first resultty encountered,
			         if any, and discards the rest, not checking
				 consistency of redundant resultty constraints *)
			      val (innerclauses,resultty) =
				  mkLazy ([],NONE,clauses)
                              val outerargs = newArgs([],argcount)
			      val outerclause = 
				  {kind=LZouter, funsym=var, resultty=resultty,
				   argpats=map VarPat outerargs,
				   exp=curryApp(VarExp[lazyvar],
						     map VarExp outerargs)}
			   in ((lv,innerclauses,fbregion)::(v,[outerclause],fbregion)
			       ::lcl,
			       SE.bind(var,B.VALbind v,
					SE.bind(lazyvar,B.VALbind lv, env')))
			  end
		     else ((v,clauses,fbregion)::lcl,SE.bind(var,B.VALbind v,env'))
		 end (* makevar *)
	    val (fundecs,env') = foldl (makevar region) ([],SE.empty) fb
	    val env'' = SE.atop(env',env)
	    fun elabClause(region,({kind,argpats,resultty,exp,funsym})) =
		let val (pats,tv1) = elabPatList(argpats, env, region)
                    val nenv = SE.atop(bindVARp(pats,error region), env'')
		    val (exp,tv2,updt) = elabExp(exp, nenv,region)
		    (* LAZY: wrap delay or force around rhs as appropriate*)
		    val exp = 
			case kind
			  of STRICT => exp
			   | LZouter => delayExp exp
			   | LZinner => forceExp exp
		    val (ty,tv3) =
		      case resultty
		       of NONE => (NONE,TS.empty)
			| SOME t => 
			    let val (t4,tv4) = ET.elabType(t,env,error,region)
			     in (SOME t4,tv4)
			    end
		 in ({pats=pats,resultty=ty,exp=exp},
		     union(tv1,union(tv2,tv3,error region),error region),updt)
		end
	    fun elabFundec ((var,clauses,region),(fs,tvs,updt)) = 
		let val (cs1,tvs1,updt1) =
		      foldl (fn (c2,(cs2,tvs2,updt2)) =>
			     let val (c3,tvs3,updt3) = elabClause(region,c2)
			      in (c3::cs2,union(tvs3,tvs2,error region),
				  updt3::updt2)
			     end) 
			  ([],TS.empty,[]) clauses
		 in ((var,rev cs1,region)::fs, union(tvs1,tvs,error region),
                     updt1 @ updt)
		end
	    val (fbs1,ftyvars,updts) = foldl elabFundec ([],TS.empty,[]) fundecs
	    val tvref = ref [] (* common tvref cell for all bindings! *)
	    fun updt tvs : unit =  
		let fun a++b = union(a,b,error region)
		    fun a--b = diff(a,b,error region)
		    val localtyvars = (ftyvars ++ etvs) -- (tvs --- etvs)
		    val downtyvars = localtyvars ++ (tvs --- etvs)
		 in tvref := TS.elements localtyvars;
		    app (fn f => f downtyvars) updts
		end
	    fun makefb (v as VALvar{path=SymPath.SPATH[_],...},cs,r) =
		  ({var=v,clauses=cs, tyvars=tvref,region=r})
	      | makefb _ = bug "makeFUNdec.makefb"
	 in EU.checkUniq(error region, "duplicate function names in fun dec",
		      (map (fn (VALvar{path=SymPath.SPATH[x],...},_,_) => x
			     | _ => bug "makeFUNdec:checkuniq")
			   fbs1));
	    (let val (ndec, nenv) = 
                   FUNdec(completeMatch,map makefb fbs1,compInfo)
              in showDec("elabFUNdec: ",ndec,nenv);
		 (ndec, nenv, TS.empty, updt)
             end)
	end

    and elabSEQdec(ds,env,rpath:IP.path,region) =
	let val (ds1,env1,tv1,updt1) = 
	      foldl 
	       (fn (decl2,(ds2,env2,tvs2,updt2)) =>
		  let val (d3,env3,tvs3,updt3) =
			   elabDec'(decl2,SE.atop(env2,env),rpath,region)
		   in (d3::ds2, SE.atop(env3,env2), 
                       union(tvs3,tvs2,error region), updt3::updt2)
		  end)
	       ([],SE.empty,TS.empty,[]) ds 
	    fun updt tv : unit = app (fn f => f tv) updt1
	 in (SEQdec(rev ds1),env1,tv1,updt)
	end

    val _ = debugmsg ("EC.elabDec calling elabDec' - foo")
    val (dec',env',tyvars,tyvUpdate) = elabDec'(dec,env,rpath,region)

 in tyvUpdate tyvars;
    (dec',env')

end (* function elabDec *)

end (* top-level local *)
end (* structure ElabCore *)
