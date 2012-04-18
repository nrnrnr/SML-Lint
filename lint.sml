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


    (* a slightly more convenient form of foldl *)
    fun sequence f []      rpt = rpt
      | sequence f (x::xs) rpt = sequence f xs (f x rpt)

    val sequence : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b = sequence


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

fun id x = x

fun f >> g = g o f

fun elabOpt f NONE     rpt = rpt
  | elabOpt f (SOME x) rpt = f x rpt

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

    fun bindFix(id, fixity, env) = (id, fixity) :: env
end

  (* sanity check *)
val _ = case Fixity.fixityToString (lookFix (initEnv, Symbol.varSymbol "@"))
          of "infixr 5 " => ()
           | s => (app print ["Bad fixity ", s, " for operator @\n"] ; bug "fixity")

val debugPrint = (fn x => if !debugging then print x else ())

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
        | TConstraint
        
    fun elabTy region tcontext ty rpt = (debugmsg "skipped type"; rpt)


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

    datatype comma_syntax = Record | Tuple | List | Vector
      (* things that have elements separated by commas *)

    datatype common_context
      = InfixChild
      | Function
      | Argument
      | Element of comma_syntax
      | Bracketed of region (* retains location of brackets *)
      | Constrained (* under a type contraint  exp : ty *)
      | Handle (* either pat or exp in  handle pat => exp | ... *)
      | CaseMatch (* either pat or exp in  case e of pat => exp | ... *)
      | FnMatch (* either pat or exp in  fn pat => exp | ... *)

      | HighLevel (* infix expression in an exp-specific context *)


    datatype pcontext
      = PClause
      | PVal
      | POr   (* SML/NJ or-patterns *)
      | P of common_context

    datatype econtext
      = Condition
      | IfCase
      | WhileCondition
      | WhileBody
      | Rhs
      | Raise
      | LetBody
      | Scrutinee   (* exp in case exp of ... *)
      | Sequent     (* exp in (exp1 ; exp2 ; ... ; expn) *)
      | E of common_context

    fun unE (E context) = context
      | unE _ = HighLevel

    fun unP (P context) = context
      | unP _ = HighLevel

    datatype 'a infixed
      = ATOM  of 'a
      | INFIX of 'a infixed * 'a infixed * 'a infixed
      | APPLY of 'a infixed * 'a infixed

    fun parse items = Precedence.parse {apply=APPLY, infixapp=INFIX} items

    fun elabOpr varOnly (ATOM a) = varOnly a
      | elabOpr _ _ = bug "lint: syntactic form of infix operator"

    fun expVarOnly (VarExp _) = (fn rpt => rpt)
      | expVarOnly (MarkExp (e, _)) = expVarOnly e
      | expVarOnly _ =  bug "lint: syntactic form of infix operator"

    fun patVarOnly (VarPat _) = (fn rpt => rpt)
      | patVarOnly (MarkPat (p, _)) = patVarOnly p
      | patVarOnly _ =  bug "lint: syntactic form of infix operator in pattern"

    fun elabInfix varOnly wrap atom (thing, env, context, region) =
      let fun elab thing context =
                elabInfix varOnly wrap atom (thing, env, context, region)
      in  case thing
            of ATOM a => atom (a, env, wrap context, region) 
             | APPLY (f, arg) => elab f Function >> elab arg Argument
             | INFIX (left, opr, right) =>
                 elab left InfixChild >> elabOpr varOnly opr >> elab right InfixChild
      end

    fun atom (Bracketed region) rpt what =
          let val (pos, _) = region
          in  Report.brackets ("redundant parentheses around " ^ what, pos, rpt)
          end
      | atom _ rpt _ = rpt

    fun eatom (E c) rpt what = atom c rpt what
      | eatom _ rpt _ = rpt

    fun patom (P c) rpt what = atom c rpt what
      | patom _ rpt _ = rpt


    fun elabPat (p:Ast.pat, env, context : pcontext, region:region) rpt =
      let val atom = patom context rpt
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
             sequence (elab (elem List)) pats (atom "list pattern")
         | TuplePat pats =>
             sequence (elab (elem Tuple)) pats (atom "tuple pattern")
         | VectorPat pats =>
             sequence (elab (elem Vector)) pats (atom "vector pattern")
         | OrPat pats =>
             sequence (elab POr) pats rpt
         | AppPat {constr, argument} =>
             (elab (P Function) constr >> elab (P Argument) argument) rpt
         | ConstraintPat {pattern=pat,constraint=ty} =>
             (elab (P Constrained) pat >> elabTy region TConstraint ty) rpt
         | LayeredPat {varPat,expPat} =>
             (elab (P InfixChild) varPat >> elab (P InfixChild) expPat) rpt
         | MarkPat (pat,region) =>
             elabPat (pat, env, context, region) rpt
         | FlatAppPat pats =>
             elabInfix patVarOnly P elabPat
             (parse(map (fixmap ATOM) pats,env,error), env, unP context, region) rpt
      end

    and elabPatList(ps, env, context, region:region) rpt =
      sequence (fn p => elabPat (p, env, context, region)) ps rpt

    (**** EXPRESSIONS ****)



    fun checkBracket region context rpt =
      case context
        of Rhs => Report.brackets("parens on RHS of function", fst region, rpt)
         | _ => (debugmsg "brackets not checked" ; rpt)

    type env = fixenv

    fun elabExp(exp: Ast.exp, env: env, context: econtext, region: region) (rpt : Report.t) 
        : Report.t =
      let val atom = eatom context rpt
          fun elab (ctx:econtext) exp rpt = elabExp (exp, env, ctx, region) rpt
          val elem = E o Element
      in
    (case exp
      of BracketExp e =>
           let val rpt = checkBracket region context rpt
               val _ = debugmsg "brackets"
           in  elab (E (Bracketed region)) e rpt
           end
       | VarExp [sym] => atom "name"
       | VarExp _ => atom "qualified name"
       | IntExp s => atom "integer literal"
       | WordExp s => atom "word literal"
       | RealExp r => atom "floating-point literal"
       | StringExp s => atom "string literal"
       | CharExp s => atom "character literal"
       | RecordExp cells =>
           sequence (elab (elem Record) o snd) cells (atom "record literal")
       | SeqExp [e] => elab context e rpt
       | SeqExp exps => sequence (elab Sequent) exps rpt
       | ListExp exps =>
           sequence (elab (elem List)) exps (atom "list literal")
       | TupleExp exps =>
           sequence (elab (elem Tuple)) exps (atom "tuple literal")
       | VectorExp exps =>
           sequence (elab (elem Vector)) exps (atom "vector literal")
       | AppExp {function,argument} =>
           elab (E Argument) argument (elab (E Function) function rpt)
       | ConstraintExp {expr=exp,constraint=ty} =>
           (elab (E Constrained) exp >> elabTy region TConstraint ty) rpt
       | HandleExp {expr,rules} =>
           (elab (E Handle) expr >> elabMatch (rules, env, Handle, region)) rpt
       | RaiseExp exp => elab Raise exp rpt
       | LetExp {dec,expr} => 
           let val (env, rpt) = elabDec'(dec, env, region, rpt)
           in  elabExp (expr, env, LetBody, region) rpt
           end
       | CaseExp {expr,rules} =>
           (elab Scrutinee expr >> elabMatch (rules, env, CaseMatch, region)) rpt
       | IfExp {test,thenCase,elseCase} =>
           (elab Condition test >> elab IfCase thenCase >> elab IfCase elseCase) rpt
       | AndalsoExp (exp1,exp2) =>
           (elab (E InfixChild) exp1 >> elab (E InfixChild) exp2) rpt
       | OrelseExp (exp1,exp2) =>
           (elab (E InfixChild) exp1 >> elab (E InfixChild) exp2) rpt
       | WhileExp {test,expr} =>
           (elab WhileCondition test >> elab WhileBody expr) rpt
       | FnExp rules => elabMatch (rules, env, FnMatch, region) rpt
       | MarkExp (exp,region) => elabExp (exp, env, context, region) rpt
       | SelectorExp s => atom "record selector"
       | FlatAppExp items =>
           elabInfix expVarOnly E elabExp
           (parse(map (fixmap ATOM) items,env,error),env,unE context,region) rpt
)end

    and elabMatch (rs,env,context,region) =
      sequence (fn (Rule {pat, exp}) => 
                  elabPat (pat, env, P context, region) >>
                  elabExp (exp, env, E context, region)) rs
       (* XXX TODO: singleton matches special; others may recommend parens
          at least in some contexts *)

    (**** SIMPLE DECLARATIONS ****)

    and elabDb region (_, rpt) = (say "skipped db"; rpt) (* BOGUS *)
    and elabTb region (_, rpt) = (say "skipped tb"; rpt) (* BOGUS *)

    and elabDec'(dec,env,region,rpt) : fixenv * Report.t =
        (* N.B. current code *extends* an existing environment,
           but it may make more sense to *return* one and combine,
           so as to deal with 'local' declarations *)

      let fun lift rpt = (env, rpt)
          fun elab dev (env, rpt) = elabDec'(dev, env, region, rpt)
      in
    (case dec 
      of TypeDec tbs => lift (foldl (elabTb region) rpt tbs)
       | DatatypeDec x =>
           let val rpt = foldl (elabDb region) rpt (#datatycs x)
               val rpt = foldl (elabTb region) rpt (#withtycs x)
           in  lift rpt
           end
       | DataReplDec(name,path) => lift rpt
       | AbstypeDec x =>
           let val rpt = foldl (elabDb region) rpt (#abstycs x)
               val rpt = foldl (elabTb region) rpt (#withtycs x)
           in  elabDec' (#body x, env, region, rpt)
           end
       | ExceptionDec ebs => (lift o sequence (elabEb region) ebs) rpt
       | ValDec(vbs,_) => lift (foldl (elabVb (region, env)) rpt vbs)
       | FunDec(fbs,explicitTvs) =>
           lift (elabFUNdec(fbs,explicitTvs,env,region,rpt))
       | ValrecDec(rvbs,explicitTvs) =>
           lift (sequence (elabRvb (region, env)) rvbs rpt)
       | SeqDec ds =>
           foldl (fn (dec, (env, rpt)) => elabDec'(dec, env, region, rpt)) (env, rpt) ds
       | LocalDec (dec, body) =>
             let val (env1, rpt) = elab dec  (env,  rpt)
                 val (env2, rpt) = elab body (env1, rpt)
             in  (fixityExtend body env, rpt)
             end

       | OpenDec ds => lift rpt
       | FixDec (ds as {fixity,ops}) =>
           (foldl (fn (id, env) => bindFix(id, fixity, env)) env ops, rpt)
       | OvldDec dec  => lift rpt  (* SML/NJ internal; not linted *)
       | MarkDec(dec,region') => elabDec'(dec, env, region', rpt)
       | StrDec strbs => lift (elabStrbs(strbs, env, region, rpt))
       | AbsDec _ => bug "absdec"
       | FctDec fctbs => lift (sequence (elabFctb (env, region)) fctbs rpt)
       | SigDec _ => bug "sigdec"
       | FsigDec _ => bug "fsigdec")
      end              

  and fixityExtend body env = (debugmsg "skipped fixity declarations in 'local'"; env)

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

    and elabFctb (env, region) fctb =
        (case fctb
           of MarkFctb (fctb, region) => elabFctb (env, region) fctb
            | Fctb {name, def} => elabFctexp (env, region) def)

    and elabFctexp (env, region) def =
        (case def
           of VarFct(spath,constraintExpOp) =>
               (debugmsg "skipped functor variable"; id)
            | LetFct(decl,fct) =>
               (debugmsg "skipped let functor (have no idea what this is)"; id)

            | AppFct(spath,larg,constraint) =>
               (debugmsg "skipped application functor; call me later"; id)

            | BaseFct{params,body,constraint} =>
               ( debugmsg "skipped functor parameters"
               ; debugmsg "skipped functor constraint"
               ; (fn rpt => elabStrexp (body, env, region, rpt))
               )

            | MarkFct(fctexp',region') => elabFctexp (env, region') fctexp')

             


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

    (****  VALUE DECLARATIONS ****)

    and elabVb (region, env) (vb, rpt) =
      (case vb
         of MarkVb(vb, region) => elabVb (region, env) (vb, rpt)
          | Vb {pat, exp, ...} => 
             (elabPat (pat, env, PVal, region) >> elabExp (exp, env, Rhs, region)) rpt)

    and elabRvb (region, env) rvb rpt =
      (case rvb
         of MarkRvb(rvb, region) => elabRvb (region, env) rvb rpt
          | Rvb {resultty, exp, ...} =>
             ( debugmsg "linting rvb"
             ; elabOpt (elabTy region TConstraint) resultty >>
               elabExp (exp, env, Rhs, region)) rpt)

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
                   in {kind=(), funsym=funsym,argpats=argpats,
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
           (sequence (fn p => elabPat (p, env, PClause, region)) argpats >>
            elabExp(exp, env, Rhs, region)) rpt

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
*)

 in elabDec' (dec, env, region, rpt)

end (* function elabDec *)

end (* top-level local *)

end
