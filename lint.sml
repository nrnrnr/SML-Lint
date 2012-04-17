functor LintFn (structure Report : REPORT where type name = Symbol.symbol
                                            and type pos  = SourceMap.charpos
               ) =
struct
 
local structure EM = ErrorMsg
      open Absyn Ast 
      structure S = Symbol
      val bogusID = S.varSymbol "bogus ID"
      fun fst (x, y) = x
      fun snd (x, y) = y

      fun fixmap f {item=x, fixity=fix, region=r} = {item = f x, fixity=fix, region=r}



in

(*
infix  7 * / mod div
infix  6 + - ^
infixr 5 :: @
infix  4 = <> > >= < <=
infix  3 := o
infix  0 before
*)

infix 3 >>

fun f >> g = g o f

fun uncurry f (x, y) = f x y
fun curry   f x y    = f (x, y)

val say = Control_Print.say
val debugging = ref false
fun debugmsg (msg: string) = if !debugging then (say msg; say "\n") else ()
fun bug msg = ErrorMsg.impossible("LintFn: "^msg)

type fixenv = (S.symbol * Fixity.fixity) list

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

    type env = (Symbol.symbol * Fixity.fixity) list
                       

    fun lookup (env, sym) =
      case List.find (fn (s, f) => Symbol.eq (sym, s)) env
        of SOME (_, f) => f
         | NONE => Fixity.NONfix

in
    val initEnv = [] : env
    val initEnv = foldl (addfix Fixity.infixleft)  initEnv left
    val initEnv = foldl (addfix Fixity.infixright) initEnv right


    structure Precedence = PrecedenceFn(type env = env
                                        val lookup = lookup)
    val lookFix = lookup

end

(*
fun lookFix ([], _) = Fixity.NONfix
  | lookFix ((x,f)::xs, y) =
       case S.compare(x, y)
         of EQUAL => f
          | _     => lookFix (xs, y)
*)

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

fun ensureInfix error getfix {item,fixity,region} =
   (case getfix fixity
     of Fixity.NONfix =>
          error region EM.COMPLAIN
            "infix operator required, or delete parentheses" 
            EM.nullErrorBody
      | _ => ();
    item)

fun ensureNonfix error getfix {item,fixity,region} =
      (case (getfix fixity, fixity)
        of (Fixity.NONfix,_) => ()
         | (_,SOME sym) =>
            error region EM.COMPLAIN
          ("infix operator \"" ^ S.name sym ^
           "\" used without \"op\" in fun dec")
          EM.nullErrorBody
         | _ => bug "ensureNonfix";
       item)

fun getname error (MarkPat(p,region),_) = getname error (p,region)
  | getname error (VarPat[v], _) = v
  | getname error (_, region) = 
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
and elabDec ({source}, dec, env, region, rpt) =
let
    fun error x = ErrorMsg.error source x

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

    datatype comma_syntax = Record | Tuple | List | Vector
      (* things that have elements separated by commas *)

    datatype common_context
      = InfixChild
      | Function
      | Argument
      | Element of comma_syntax
      | Bracketed

      | HighLevel (* infix expression in an exp-specific context *)


    datatype pcontext
      = PClause
      | PVal
      | P of common_context

    datatype econtext
      = Condition
      | IfCase
      | WhileCondition
      | WhileBody
      | Constraint
      | Rhs
      | Raise
      | Handle
      | LetBody
      | E of common_context

    fun unE (E context) = context
      | unE _ = HighLevel

    datatype 'a infixed
      = ATOM  of 'a
      | INFIX of 'a infixed * 'a infixed * 'a infixed
      | APPLY of 'a infixed * 'a infixed

    fun elabInfix elabOpr atom wrap (thing, env, context, region) =
      let fun elab thing context =
                elabInfix elabOpr atom wrap (thing, env, context, region)
      in  case thing
            of ATOM a => atom (a, env, wrap context, region) 
             | APPLY (f, arg) => elab f Function >> elab arg Argument
             | INFIX (left, opr, right) =>
                 elab left InfixChild >> elabOpr opr >> elab right InfixChild
      end



    fun atom region Bracketed rpt what =
          let val (pos, _) = region
          in  Report.brackets ("redundant parentheses around " ^ what, pos, rpt)
          end
      | atom _ _ rpt _ = rpt

    fun eatom r (E c) rpt what = atom r c rpt what
      | eatom _ _ rpt _ = rpt

    fun patom r (P c) rpt what = atom r c rpt what
      | patom _ _ rpt _ = rpt


    fun elabPat (p:Ast.pat, env, context : pcontext, region:region) rpt =
      let val atom = patom region context rpt
          fun elab ctx pat rpt = elabPat (pat, env, ctx, region) rpt
          val elem = P o Element
      in
      case p
        of WildPat => atom "wildcard '_'"
         | VarPat [_] => atom "name"
         | VarPat _ => atom "qualified name"
         | IntPat s => atom "integer literal"
         | WordPat s => atom "word literal"
         | StringPat s => atom "string literal"
         | CharPat s => atom "character literal"
         | RecordPat {def,flexibility} =>
             foldl (uncurry (elab (elem Record) o snd)) (atom "record pattern") def
         | ListPat pats =>
             foldl (uncurry (elab (elem List))) (atom "list pattern") pats
         | TuplePat pats =>
             foldl (uncurry (elab (elem Tuple))) (atom "tuple pattern") pats
         | VectorPat pats =>
             foldl (uncurry (elab (elem Vector))) (atom "vector pattern") pats
         | OrPat pats =>
             foldl (uncurry (elab context)) rpt pats
(*
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
*)
       | MarkPat (pat,region) =>
             elabPat (pat, env, context, region) rpt
(*
       | FlatAppPat pats => elabPat(patParse(pats,env,error), env, region) 
*)
             | _ => (debugmsg "skipped pattern"; rpt)
      end

(*
    and elabPLabel (region:region) (env:SE.staticEnv) labs =
    foldl
      (fn ((lb1,p1),(lps1,lvt1)) => 
          let val (p2,lvt2) = elabPat(p1, env, region)
          in ((lb1,p2) :: lps1, union(lvt2,lvt1,error region)) end)
      ([],TS.empty) labs

*)
    and elabPatList(ps, env, context, region:region) rpt =
      foldr (fn (p1,rpt) => elabPat (p1, env, context, region) rpt) rpt ps

    (**** EXPRESSIONS ****)



    val expParse = Precedence.parse {apply=APPLY, infixapp=INFIX}

    fun checkBracket region context rpt =
      case context
        of Rhs => Report.brackets("parens on RHS of function", fst region, rpt)
         | _ => (debugmsg "brackets not checked" ; rpt)

    type env = fixenv

    fun atom region Bracketed rpt what =
          let val (pos, _) = region
          in  Report.brackets ("redundant parentheses around " ^ what, pos, rpt)
          end
      | atom _ _ rpt _ = rpt

    fun elabExp(exp: Ast.exp, env: env, context: econtext, region: region) (rpt : Report.t) 
        : Report.t =
      let val atom = eatom region context rpt
          fun elab (ctx:econtext) exp rpt = elabExp (exp, env, ctx, region) rpt
          val elem = E o Element
      in
    (case exp
      of BracketExp e =>
           let val rpt = checkBracket region context rpt
               val _ = debugmsg "brackets"
           in  elab (E Bracketed) e rpt
           end
       | VarExp [sym] => atom "name"
       | VarExp _ => atom "qualified name"
       | IntExp s => atom "integer literal"
       | WordExp s => atom "word literal"
       | RealExp r => atom "floating-point literal"
       | StringExp s => atom "string literal"
       | CharExp s => atom "character literal"
       | RecordExp cells =>
          foldl (uncurry (elab (elem Record) o snd))
                (atom "record literal") cells
       | SeqExp exps =>
           (case exps
              of [e] => elabExp (e,env,context,region) rpt
               | [] => bug "elabExp(SeqExp[])"
               | _ => elabExpList(exps,env,context,region,rpt))
       | ListExp exps =>
          foldl (uncurry (elab (elem List))) (atom "list literal") exps
       | TupleExp exps =>
          foldl (uncurry (elab (elem Tuple))) (atom "tuple literal") exps
       | VectorExp exps =>
          foldl (uncurry (elab (elem Vector))) (atom "vector literal") exps
       | AppExp {function,argument} =>
           elab (E Argument) argument (elab (E Function) function rpt)
       | ConstraintExp {expr=exp,constraint=ty} => elab Constraint exp rpt
(*
       | HandleExp {expr,rules} =>
           let val rpt = elabExp(expr, env, Handle, region) rpt
           in  elabMatch(rules,env,region,rpt)
           end
*)
       | RaiseExp exp => elab Raise exp rpt
       | LetExp {dec,expr} => 
           let val (env, rpt) = elabDec'(dec, env, region, rpt)
           in  elabExp (expr, env, LetBody, region) rpt
           end
(*
       | CaseExp {expr,rules} =>
           let val (e1,tv1,updt1) = elabExp(expr,env,region)
           val (rls2,tv2,updt2) = elabMatch(rules,env,region)
           fun updt tv = (updt1 tv;updt2 tv)
        in (CASEexp (e1,completeMatch rls2, true),
            union(tv1,tv2,error region),updt)
           end
*)
       | IfExp {test,thenCase,elseCase} =>
           (elab Condition test >> elab IfCase thenCase >> elab IfCase elseCase) rpt
       | AndalsoExp (exp1,exp2) =>
           (elab (E InfixChild) exp1 >> elab (E InfixChild) exp2) rpt
       | OrelseExp (exp1,exp2) =>
           (elab (E InfixChild) exp1 >> elab (E InfixChild) exp2) rpt
       | WhileExp {test,expr} =>
           (elab WhileCondition test >> elab WhileBody expr) rpt
(*
       | FnExp rules => 
           let val (rls,tyv,updt) = elabMatch(rules,env,region)
        in (FNexp (completeMatch rls,UNDEFty),tyv,updt)
           end
*)
       | MarkExp (exp,region) => elabExp (exp, env, context, region) rpt
(*
       | SelectorExp s => 
           (let val v = newVALvar s
         in FNexp(completeMatch
              [RULE(RECORDpat{fields=[(s,VARpat v)], flex=true,
                      typ= ref UNDEFty},
                cMARKexp(VARexp(ref v,[]),region))],UNDEFty)
        end,
        TS.empty, no_updt)
*)
       | FlatAppExp items =>
           elabInfix elabOpr elabExp E
           (expParse(map (fixmap ATOM) items,env,error),env,unE context,region) rpt
       | _ => (debugmsg "skipped expression"; rpt)
)end

    and elabInfix' (exp, env, context, region) =
      let fun elab exp context = elabInfix' (exp, env, context, region)
      in  case exp
            of ATOM e => elabExp (e, env, context, region) 
             | APPLY (f, arg) => elab f (E Function) >> elab arg (E Argument)
             | INFIX (left, opr, right) =>
                 elab left (E InfixChild) >> elabOpr opr >> elab right (E InfixChild)
      end

    and elabOpr (ATOM e) =
          let fun elab e =
                case e
                  of MarkExp (e, _) => elab e
                   | VarExp _ => (fn rpt => rpt)
                   | _ => bug "lint: syntactic form of infix operator"
          in  elab e
          end
      | elabOpr _ = bug "lint: syntactic form of infix operator"

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
      let fun lift rpt = (env, rpt)
      in
    (case dec 
      of TypeDec tbs => lift (foldl (elabTb region) rpt tbs)
       | DatatypeDec x =>
           let val rpt = foldl (elabDb region) rpt (#datatycs x)
               val rpt = foldl (elabTb region) (rpt) (#withtycs x)
           in  lift rpt
           end
       | DataReplDec(name,path) => lift rpt
       | AbstypeDec x =>
           let val rpt = foldl (elabDb region) rpt (#abstycs x)
               val rpt = foldl (elabTb region) rpt (#withtycs x)
           in  elabDec' (#body x, env, region, rpt)
           end
(*
       | ExceptionDec ebs => elabEXCEPTIONdec(ebs,env,region)
*)
       | ValDec(vbs,_) => lift (foldl (elabVb (region, env)) rpt vbs)
       | FunDec(fbs,explicitTvs) =>
           lift (elabFUNdec(fbs,explicitTvs,env,region,rpt))
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
       | StrDec strbs => lift (elabStrbs(strbs, env, region, rpt))
       | AbsDec _ => bug "absdec"
       | FctDec _ => bug "fctdec"
       | SigDec _ => bug "sigdec"
(*
       | FsigDec _ => bug "fsigdec")
*)
       | _ => (say "Skipped declaration\n"; lift rpt))
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

    and elabVb (region, env) (vb, rpt) =
      (case vb
         of MarkVb(vb, region) => elabVb (region, env) (vb, rpt)
         | Vb {pat, exp, ...} => (debugmsg "linting vb"; 
             (elabPat (pat, env, PVal, region) >> elabExp (exp, env, Rhs, region)) rpt)
           )

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

                  val ensureInfix  = ensureInfix  error getfix
                  val ensureNonfix = ensureNonfix error getfix
                  val getname = getname error

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
(debugmsg "linting clause";
           (elabPatList(argpats, env, PClause, region) >>
            elabExp(exp, env, Rhs, region)) rpt
)
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
