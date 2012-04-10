(* absyn.sml
 *
 * (C) 2001 Lucent Technologies, Bell Labs
 *)
structure Absyn : ABSYN =
struct

local
  structure S = Symbol
  structure F = Fixity
  structure SP = SymPath
  structure B = Bindings
  open VarCon Modules Types
in

type region = Ast.region  (* = int * int *)

datatype numberedLabel = LABEL of {name: S.symbol, number: int}

datatype exp
  = VARexp of var ref * tyvar list
    (* the 2nd arg is a type univar list used to capture the instantiation
       parameters for this occurence of var when its type is polymorphic.
       FLINT will use these to provide explicit type parameters for
       var if var is bound to a primop. These will then be used to specialize
       the primop. *)
  | CONexp of datacon * tyvar list (* ditto *)
  | INTexp of IntInf.int * ty
  | WORDexp of IntInf.int * ty
  | REALexp of string
  | STRINGexp of string
  | CHARexp of string
  | RECORDexp of (numberedLabel * exp) list
  | SELECTexp of numberedLabel * exp           (* record selections *)
  | VECTORexp of exp list * ty        
  | PACKexp of exp * ty * tycon list           (* abstraction packing *)
  | APPexp of exp * exp
  | HANDLEexp of exp * fnrules
  | RAISEexp of exp * ty              
  | CASEexp of exp * rule list * bool     (* true: match; false: bind *)
  | IFexp of { test: exp, thenCase: exp, elseCase: exp }
  | ANDALSOexp of exp * exp
  | ORELSEexp of exp * exp
  | WHILEexp of { test: exp, expr: exp }
  | FNexp of fnrules
  | LETexp of dec * exp
  | SEQexp of exp list
  | CONSTRAINTexp of exp * ty         
  | MARKexp of exp * region

and rule = RULE of pat * exp

and pat 
  = WILDpat
  | VARpat of var
  | INTpat of IntInf.int * ty
  | WORDpat of IntInf.int * ty
  | REALpat of string
  | STRINGpat of string
  | CHARpat of string
  | CONpat of datacon * tyvar list (* See comment for VARexp *)
  | RECORDpat of {fields: (label * pat) list, flex: bool, typ: ty ref}
  | APPpat of datacon * tyvar list * pat
  | CONSTRAINTpat of pat * ty
  | LAYEREDpat of pat * pat
  | ORpat of pat * pat
  | VECTORpat of pat list * ty
  | MARKpat of pat * region       
  | NOpat

and dec	
  = VALdec of vb list        (* always a single element list (FLINT normalization) *)
  | VALRECdec of rvb list
  | TYPEdec of tycon list
  | DATATYPEdec of {datatycs: tycon list, withtycs: tycon list}
  | ABSTYPEdec of {abstycs: tycon list, withtycs: tycon list, body: dec}
  | EXCEPTIONdec of eb list
  | STRdec of strb list
  | ABSdec of strb list      (* should be merged with STRdec in the future *)
  | FCTdec of fctb list
  | SIGdec of Signature list
  | FSIGdec of fctSig list
  | OPENdec of (SP.path * Structure) list
  | LOCALdec of dec * dec
  | SEQdec of dec list
  | OVLDdec of var
  | FIXdec of {fixity: F.fixity, ops: S.symbol list} 
  | MARKdec of dec * region

(*
 * The "argtycs" field in APPstr is used to record the list of instantiated
 * hotycs passed to functor during the functor application.
 *)
and strexp 
  = VARstr of Structure 
  | STRstr of B.binding list
  | APPstr of {oper: Functor, arg: Structure, argtycs: tycpath list}
  | LETstr of dec * strexp
  | MARKstr of strexp * region

(*
 * For typing purpose, a functor is viewed as a high-order type constructor 
 * (hotyc) that takes a list of hotycs returns another list of hotycs. The
 * "argtycs" field in FCTfct records the list of formal hotyc paramaters.
 *)
and fctexp 
  = VARfct of Functor
  | FCTfct of {param: Structure, argtycs: tycpath list, def: strexp}
  | LETfct of dec * fctexp
  | MARKfct of fctexp * region

(*
 * Each value binding vb only binds one variable identifier. That is, 
 * pat is always a simple VARpat (with type constraints) or it simply
 * does not contain any variable patterns; boundtvs gives the list of
 * type variables that are being generalized at this binding. 
 *)
and vb = VB of {pat: pat, exp: exp, boundtvs: tyvar list,
                tyvars: tyvar list ref}

(*
 * Like value binding vb, boundtvs gives a list of type variables 
 * being generalized at this binding. However, the mutually recursive
 * list of RVBs could share type variables, that is, the boundtvs sets
 * used in these RVBs could contain overlapping set of type variables.
 *)
and rvb = RVB of {var: var, exp: exp, boundtvs: tyvar list,
                  resultty: ty option, tyvars: tyvar list ref}

and eb = EBgen of {exn: datacon, etype: ty option, ident: exp}
       | EBdef of {exn: datacon, edef: datacon}

and strb = STRB of {name: S.symbol, str: Structure, def: strexp} 
and fctb = FCTB of {name: S.symbol, fct: Functor, def: fctexp}

withtype fnrules = rule list * Types.ty

end (* local *)
end
