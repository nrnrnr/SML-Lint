    structure Precedence = struct
        fun parse _ _ = raise Match
    end
                       
functor LintFn (structure Report : REPORT where type name = Symbol.symbol
                                            and type pos  = SourceMap.charpos
               ) =
struct
 
local structure EM = ErrorMsg
      open Absyn Ast 
      structure S = Symbol
      val bogusID = S.varSymbol "bogus ID"
      fun badsource () = badsource ()
      fun error x = ErrorMsg.error (badsource ()) x
      fun fst (x, y) = x
      fun snd (x, y) = y
in

(*
infix  7 * / mod div
infix  6 + - ^
infixr 5 :: @
infix  4 = <> > >= < <=
infix  3 := o
infix  0 before
*)

local
    val left = [ (7, ["*", "/", "mod", "div"])
               , (6, ["+", "-", "^"])
               , (4, ["=", "<>", ">", ">=", "<", "<="])
               , (3, [":=", "o"])
               , (0, ["before"])
               ]
    val right = [ (5, ["::", "@"]) ]

    val sym = Symbol.varSymbol

    fun addfix assoc ((prec, oprs), env) =
          foldl (fn (opr, env) => (sym opr, assoc prec) :: env) env oprs

in
    val initEnv = []
    val initEnv = foldl (addfix Fixity.infixleft)  initEnv left
    val initEnv = foldl (addfix Fixity.infixright) initEnv right
end



val say = Control_Print.say
val debugging = ref false
fun debugmsg (msg: string) = if !debugging then (say msg; say "\n") else ()
fun bug msg = ErrorMsg.impossible("LintFn: "^msg)

type fixenv = (S.symbol * Fixity.fixity) list

fun lookFix ([], _) = Fixity.NONfix
  | lookFix ((x,f)::xs, y) =
       case S.compare(x, y)
         of EQUAL => f
          | _     => lookFix (xs, y)

val _ = case Fixity.fixityToString (lookFix (initEnv, Symbol.varSymbol "@"))
          of "infixr 5 " => ()
           | s => (app print ["Bad fixity ", s, " for operator @\n"] ; bug "fixity")

val debugPrint = (fn x => if !debugging then print x else ())

infix -->

fun stripExpAst(MarkExp(e,r'),r) = stripExpAst(e,r')
  | stripExpAst(ConstraintExp{expr=e,...},r) = stripExpAst(e,r)
  | stripExpAst(SeqExp[e],r) = stripExpAst(e,r)
  | stripExpAst(FlatAppExp[{item,region,...}],r) = stripExpAst(item,region)
  | stripExpAst x = x

fun ensureInfix getfix {item,fixity,region} =
   (case getfix fixity
     of Fixity.NONfix =>
          error region EM.COMPLAIN
            "infix operator required, or delete parentheses" 
            EM.nullErrorBody
      | _ => ();
    item)

fun ensureNonfix getfix {item,fixity,region} =
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
           (error region EM.COMPLAIN "illegal function symbol in clause"
            EM.nullErrorBody;
            bogusID)



(* LAZY *)
(* clauseKind: used for communicating information about lazy fun decls
   between preprocessing phase (makevar) and main part of elabFUNdec *)
datatype clauseKind = STRICT | LZouter | LZinner

exception Unimp of string

fun unimp what = raise Unimp what

(**** ABSTRACT TYPE DECLARATIONS ****)
fun elabABSTYPEdec({abstycs,withtycs,body},env,rpt,
                   rpath,region,compInfo) =
  let val (datatycs,withtycs,_,env1) =
        unimp "ET.elabDATATYPEdec" ({datatycs=abstycs,withtycs=withtycs}, env,
                           [], rpath, region, compInfo)

      val (body,env2) = 
        unimp "elabDec"(body,env,rpath,region,compInfo)

      (* datatycs will be changed to abstycs during type checking
     by changing the eqprop field *)
   in rpt
  end (* function elabABSTYPEdec *)


(**** ELABORATE GENERAL (core) DECLARATIONS ****)
and elabDec (dec, env, region, rpt) =
    (**** COULD PASS ERROR HERE ****)

let
    val _ = debugmsg ">>ElabCore.elabDec"

    (**** TYPES ****)

    datatype tycontext
        = Exn
        | Constructor
        
    fun elabTy region tcontext ty rpt = rpt


    (**** EXCEPTION DECLARATIONS ****)

    fun elabEb (region:region) (eb:Ast.eb) rpt =
    case eb
      of EbGen{exn=id,etype=NONE} => rpt
       | EbGen{exn=id,etype=SOME typ} => elabTy region Exn typ rpt
       | EbDef{exn=id,edef=qid} => rpt
       | MarkEb(eb,region) => elabEb region eb rpt

    (**** PATTERNS ****)

    fun apply_pat (c as MarkPat(_,(l1,r1)),p as MarkPat(_,(l2,r2))) = 
      MarkPat(AppPat{constr=c, argument=p},(Int.min(l1,l2),Int.max(r1,r2)))
      | apply_pat (c ,p) = AppPat{constr=c, argument=p}

    fun tuple_pat (a as MarkPat(_,(l,_)),b as MarkPat(_,(_,r))) =
      MarkPat(TuplePat[a,b],(l,r))
      | tuple_pat (a,b) = TuplePat[a,b]

(*
    val patParse = Precedence.parse{apply=apply_pat, pair=tuple_pat}
*)

    datatype pcontext = PClause

    fun elabPat (p, env, region, pcontext, rpt) = rpt

(*
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

*)
    and elabPatList(ps, env, region:region, context, rpt) =
    foldr (fn (p1,rpt) => elabPat(p1, env, region, context, rpt)) rpt ps

    (**** EXPRESSIONS ****)


    val expParse = Precedence.parse
             {apply=fn(f,a) => AppExp{function=f,argument=a},
              pair=fn (a,b) => TupleExp[a,b]}

    datatype context
        = Infix_child
        | Function
        | Argument
        | Condition
        | IfBranch
        | Constraint
        | Rhs
        | Element of comma_syntax
        | Raise
        | Handle
        | Bracketed
    and comma_syntax = Record | Tuple | List | Vector

    fun checkBracket region context rpt =
      case context
        of Rhs => Report.brackets("parens on RHS of function", fst region, rpt)
         | _ => rpt

    type env = fixenv

    fun atom region Bracketed rpt what =
          let val (pos, _) = region
          in  Report.brackets ("redundant parentheses around " ^ what, pos, rpt)
          end
      | atom _ _ rpt _ = rpt

    fun elabExp(exp: Ast.exp, env: env, context: context, region: region, rpt : Report.t) 
        : Report.t =
      let val atom = atom region context rpt
      in
    (case exp
      of BracketExp e =>
           let val rpt = checkBracket region context rpt
               val _ = debugmsg "brackets"
           in  rpt  (* sequence/infix not yet implemented *)
           end
       | VarExp [sym] => atom "name"
       | VarExp _ => atom "qualified name"
       | IntExp s => atom "integer literal"
       | WordExp s => atom "word literal"
       | RealExp r => atom "floating-point literal"
       | StringExp s => atom "string literal"
       | CharExp s => atom "character literal"
       | RecordExp cells =>
          foldl (fn ((_, e), rpt) => elabExp(e, env, Element Record, region, rpt))
                (atom "record literal") cells
       | SeqExp exps =>
           (case exps
              of [e] => elabExp (e,env,context,region,rpt)
               | [] => bug "elabExp(SeqExp[])"
               | _ => elabExpList(exps,env,context,region,rpt))
       | ListExp exps =>
          foldl (fn (e, rpt) => elabExp(e, env, Element List, region, rpt))
                (atom "list literal") exps
       | TupleExp exps =>
          foldl (fn (e, rpt) => elabExp(e, env, Element Tuple, region, rpt))
                (atom "tuple") exps
       | VectorExp exps =>
          foldl (fn (e, rpt) => elabExp(e, env, Element Vector, region, rpt))
                (atom "vector literal") exps
       | AppExp {function,argument} =>
           let val rpt = elabExp(function, env, Function, region, rpt)
               val rpt = elabExp(argument, env, Argument, region, rpt)
           in  rpt
           end
       | ConstraintExp {expr=exp,constraint=ty} =>
           elabExp(exp, env, Constraint, region, rpt)
       | _ => rpt
)end
(*
       | HandleExp {expr,rules} =>
           let val rpt = elabExp(expr, env, Handle, region, rpt)
           in  elabMatch(rules,env,region,rpt)
           end
       | RaiseExp exp => elabExp(exp, env, Raise, region, rpt)
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

*)
(*
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

*)
    (**** SIMPLE DECLARATIONS ****)

    and elabDb region (_, rpt) = (say "skipped db"; rpt) (* BOGUS *)
    and elabTb region (_, rpt) = (say "skipped tb"; rpt) (* BOGUS *)


    and elabDec'(dec,env,region,rpt) : fixenv * Report.t =
      let fun here rpt = (env, rpt)
      in
    (case dec 
      of TypeDec tbs => here (foldl (elabTb region) rpt tbs)
       | DatatypeDec x =>
           let val rpt = foldl (elabDb region) rpt (#datatycs x)
               val rpt = foldl (elabTb region) (rpt) (#withtycs x)
           in  here rpt
           end
       | DataReplDec(name,path) => here rpt
       | AbstypeDec x =>
           let val rpt = foldl (elabDb region) rpt (#abstycs x)
               val rpt = foldl (elabTb region) rpt (#withtycs x)
           in  elabDec' (#body x, env, region, rpt)
           end
(*
       | ExceptionDec ebs => elabEXCEPTIONdec(ebs,env,region)
       | ValDec(vbs,explicitTvs) =>
           elabVALdec(vbs,explicitTvs,env,region,rpt)
*)
       | FunDec(fbs,explicitTvs) =>
           here (elabFUNdec(fbs,explicitTvs,env,region,rpt))
(*
       | ValrecDec(rvbs,explicitTvs) =>
           elabVALRECdec(rvbs,explicitTvs,env,rpath,region)
*)
       | SeqDec ds =>
           foldl (fn (dec, (env, rpt)) => elabDec'(dec, env, region, rpt)) (env, rpt) ds
(*
       | LocalDec ld => elabLOCALdec(ld,env,rpath,region)
       | OpenDec ds => elabOPENdec(ds,env,region)
       | FixDec (ds as {fixity,ops}) => 
           let val env = 
         foldr (fn (id,env) => SE.bind(id,B.FIXbind fixity,env))
            SE.empty ops
        in (FIXdec ds,env,TS.empty,no_updt)
           end
       | OvldDec dec  => elabOVERLOADdec(dec,env,rpath,region)
*)
       | MarkDec(dec,region') => elabDec'(dec, env, region', rpt)
       | StrDec strbs => here (elabStrbs(strbs, env, region, rpt))
       | AbsDec _ => bug "absdec"
       | FctDec _ => bug "fctdec"
       | SigDec _ => bug "sigdec"
(*
       | FsigDec _ => bug "fsigdec")
*)
       | _ => (say "Skipped declaration\n"; here rpt))
      end              

  and elabStrbs (strbs, env, region, rpt) =
        foldl (fn (strb, rpt) => elabStrb (strb, env, region, rpt)) rpt strbs
  and elabStrb (strb, env, region, rpt) =
      (case strb
         of MarkStrb (strb, region) => elabStrb (strb, env, region, rpt)
          | Strb {name, def, constraint} => elabStrexp (def, env, region, rpt))
  and elabStrexp (def, env, region, rpt) =
      (case def
         of VarStr _ => rpt
          | BaseStr dec => snd (elabDec' (dec, env, region, rpt))
          | ConstrainedStr (def, constraint) =>
             elabStrexp (def, env, region, rpt)  (* XXX constraint not checked *)
          | AppStr (_, args) =>
             foldl (fn ((def, _), rpt) => elabStrexp(def, env, region, rpt)) rpt args
          | AppStrI (path, args) => elabStrexp(AppStr (path, args), env, region, rpt)
          | LetStr (dec, def) =>
             let val (env, rpt) = elabDec' (dec, env, region, rpt)
             in  elabStrexp (def, env, region, rpt)
             end
          | MarkStr (def, region) => elabStrexp (def, env, region, rpt))

             


    (**** OVERLOADING ****)

(*
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
*)
    (**** LOCAL ****)

(*
    and elabLOCALdec((ldecs1,ldecs2),env,rpath:IP.path,region) =
    let val (ld1,env1,tv1,updt1) = elabDec'(ldecs1,env,IP.IPATH[],region)
        val (ld2,env2,tv2,updt2) =
          elabDec'(ldecs2,SE.atop(env1,env),rpath,region)
        fun updt tv = (updt1 tv;updt2 tv)
     in (LOCALdec(ld1,ld2), env2,union(tv1,tv2,error region),updt)
    end
*)

    (**** OPEN ****)

(*
    and elabOPENdec(spaths, env, region) = 
        let val err = error region
        val strs = map (fn s => let val sp = SP.SPATH s
                                     in (sp, LU.lookStr(env, sp, err))
                                    end) spaths
        
            fun loop([], env) = (OPENdec strs, env, TS.empty, no_updt)
              | loop((_, s)::r, env) = loop(r, MU.openStructure(env, s))

         in loop(strs, SE.empty)
        end 
*)

    (****  VALUE DECLARATIONS ****)
    (* elabVB : Ast.vb * tyvar list * staticEnv * region
                ->  ... *)
(*
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
*)

(*
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
*)

(*
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
             (case lookFix(env,f) 
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
*)
    and elabFUNdec(fb,etvs,env,region,rpt) =
    let     (* makevar: parse the function header to determine the function name *)
        fun makevar _ (MarkFb(fb,fbregion)) = makevar fbregion fb
          | makevar fbregion (Fb(clauses,lazyp)) =
              let fun getfix(SOME f) = lookFix(env,f)
                    | getfix NONE = Fixity.NONfix

                  val ensureInfix  = ensureInfix  getfix
                  val ensureNonfix = ensureNonfix getfix

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
                      case map parseClause clauses
                        of [] => bug "elabcore:no clauses"
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
                  val v = var
                  val _ = app say ["Linting function named ", S.symbolToString v, "\n"]

               in   (v,clauses,fbregion)
              end (* makevar *)
        val fundecs = map (makevar region) fb
        fun elabClause(region,({kind,argpats,resultty,exp,funsym}), rpt) =
        let val rpt = elabPatList(argpats, env, region, PClause, rpt)
            val rpt = elabExp(exp, env, Rhs, region, rpt)
            val _ = debugmsg "linting clause"
         in rpt
        end
        fun elabFundec ((var,clauses,region),rpt) = 
          foldl (fn (c2,rpt) => elabClause(region,c2,rpt)) rpt clauses
        val rpt = foldl elabFundec rpt fundecs
     in rpt
    end

(*
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
*)
    and elabExpList x = unimp "elabExpList" x

 in elabDec' (dec, env, region, rpt)

end (* function elabDec *)

end (* top-level local *)

end
