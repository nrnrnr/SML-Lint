(* COPYRIGHT (c) 1996 Bell Laboratories *)
(* elabtop.sml *)

signature ELABTOP =
sig
  val elabTop: Ast.dec * StaticEnv.staticEnv * ElabUtil.compInfo
               -> Absyn.dec * StaticEnv.staticEnv

  val debugging : bool ref

end (* signature ELABTOP *)


(* functorized to factor out dependencies on FLINT... *)
functor ElabTopFn (structure ElabMod : ELABMOD) : ELABTOP =
struct

local structure PP = PrettyPrintNew
      structure PU = PPUtilNew
      structure S = Symbol
      structure SP = SymPath
      structure IP = InvPath
      structure DA = Access
      structure A = Absyn
      structure T = Types
      structure V = VarCon
      structure M = Modules
      structure MU = ModuleUtil
      structure B = Bindings
      structure SE = StaticEnv
      structure L = Lookup
      structure EU = ElabUtil
      structure EE = EntityEnv
      structure EP = EntPath
      structure EPC = EntPathContext
      open Ast
in 

(* debugging *)
val say = Control_Print.say
val debugging = ref false
fun debugmsg (msg: string) =
  if !debugging then (say msg; say "\n") else ()
val debugPrint = (fn x => ElabDebug.debugPrint debugging x)

(* localStrName: used in makeOpenDec to build redeclaration of components *)
val localStrName = S.strSymbol "<a funny structure>"

fun bug msg = ErrorMsg.impossible("ElabTop: "^msg)

(* 
 * makeOpenDecls is a hack; it is written to make sure that the backend
 * will generate the right dynamic code for all structure components.
 * Once the static environment and the dynamic environment are merged,
 * these code should become obsolete. (ZHONG)
 *)
fun makeOpenDecls (str, spath) =
  let fun build (name, dl) = 
        (case S.nameSpace name
          of S.VALspace =>
              let val v = MU.getValPath(str, SP.SPATH[name],
					SP.SPATH(spath@[name]))
               in case v
                   of V.VAL(V.VALvar _) => 
                        ValDec([Vb{pat=VarPat[name],
				   exp=VarExp([localStrName,name]),
				   lazyp=false}],
			       nil)
			 :: dl
		      (* here is the source of bug 788.  If name is bound
                         to a constructor in the top level environment,
			 then this will not have the desired affect of
			 rebinding name, but will probably result in a
			 type error. Possible fix would be to narrow down
			 the static environment. *)

                    | V.CON(T.DATACON{rep=DA.EXN _, ...}) => 
                        ExceptionDec [EbDef{exn=name,
					    edef=([localStrName,name])}] :: dl

                    | _ => dl
              end
           | S.STRspace =>
              StrDec [Strb{name=name,
                           def=VarStr([localStrName,name]),
                           constraint=NoSig}] :: dl
           | S.FCTspace =>
              FctDec [Fctb{name=name,
                           def=VarFct([localStrName,name],NoSig)}] :: dl

           | _ => dl)

      val nds = foldr build [] (MU.getStrSymbols str)

   in LocalDec(StrDec[Strb{name=localStrName, def=VarStr(spath),
                           constraint=NoSig}],
               SeqDec nds)
  end 

(*
 * The main purpose of having a separate layer of elabTop above elabDecl
 * is to deal with the top-level OPEN declarations; once statenv and dynenv
 * are merged, there should be no special treatment for OPEN declarations,
 * and elabTop probably can be dramatically simplied. (ZHONG)
 *)
fun elabTop(dec, env, compInfo as {error,...}: EU.compInfo) =
let 

val _ = debugmsg ">>elabTop";

fun elab(SeqDec decs, env0, top, region) =
      let fun h(dec, (abdecls, env)) = 
            let val (abdecl, env') = elab(dec, SE.atop(env,env0), top, region) 
             in (abdecl::abdecls, SE.atop(env', env))
            end
       
          val (abdecls,env') = foldl h ([], SE.empty) decs

       in (A.SEQdec(rev abdecls),env')
      end

  | elab(LocalDec(decl_in, decl_out), env0, top, region) =
      let val top_in = EU.hasModules decl_in orelse EU.hasModules decl_out
          val (adec_in, env1) = elab(decl_in, env0, top_in, region)
          val (adec_out, env2) = 
            elab(decl_out, SE.atop(env1, env0), top, region)
       in (A.LOCALdec(adec_in, adec_out), env2)
      end

  | elab(MarkDec(dec,region'), env, top, region) = 
	       let val (d,env)= elab(dec,env,top,region')
		in (if !ElabControl.markabsyn then A.MARKdec(d,region')
		    else d, env)
	       end

  | elab(OpenDec paths, env, top, region) = 
      let val _ = debugPrint("top level open: ",
                    (fn pps => fn paths =>
                       PU.ppSequence pps
                         {sep=(fn pps => PP.string pps ","),
                          pr=PU.ppSymPath, style=PU.INCONSISTENT}
                       (List.map SymPath.SPATH paths)), paths)

          val err = error region

          (* look up the structure variables *)
          val strs = map (fn p => L.lookStr(env,SP.SPATH p,err)) paths

          (* open their environments to add datatypes, etc. *)
          fun h(M.ERRORstr, env) = env
            | h(str, env) = MU.openStructure(env, str)
          val openEnv = foldl h SE.empty strs

          fun g((M.ERRORstr,spath), decs) = decs
            | g((str,spath), decs) = 
              let val ndec = makeOpenDecls(str, spath)
               in ndec::decs
              end
                 

          val newDecs = foldr g [] (ListPair.zip(strs, paths))

          (* hack to fix bugs 788, 847.
           * narrow the static environment used to elaborate newDecs
	   * to one only binding the initial symbols of the paths.
	   * Doesn't hurt if more than one path has same head symbol. *)

          val minEnv = foldl (fn (p,e) => 
			       let val h = (case p 
                                    of x::_ => x
                                     | []  => bug "unexpected case OpenDec")
				   fun err' _ _ _ = ()
				     (* to suppress duplicate error messages *)
				   val str = L.lookStr(env,SP.SPATH [h],err') 
				in SE.bind(h,Bindings.STRbind str,e)
			       end)
	                     SE.empty
			     paths

          val {absyn=ds, statenv=env'} =
                ElabMod.elabDecl{ast=(SeqDec newDecs), statenv=minEnv,
                                 entEnv=EE.empty, context=EU.TOP,
                                 level=top, tdepth=DebIndex.top,
                                 epContext=EPC.initContext, 
                                 path=IP.IPATH[], region=region,
                                 compInfo=compInfo}

          val nenv = SE.consolidate(SE.atop(env',openEnv))

	  val strs' = ListPair.zip(map SP.SPATH paths,strs)

       in (A.SEQdec [A.OPENdec strs', ds], nenv)
      end

  | elab(dec, env, top, region) =
      let val _ = debugmsg "--elabTop.elab[dec]: calling ElabMod.elabDecl"
          val {absyn=d, statenv=env'} = 
            ElabMod.elabDecl{ast=dec, statenv=env, entEnv=EE.empty,
                             context=EU.TOP, level=top, tdepth=DebIndex.top,
                             epContext=EPC.initContext, path=IP.IPATH[],
                             region=region,compInfo=compInfo}
       in (d, env')
      end

 in elab(dec,env,true,SourceMap.nullRegion) before debugmsg "<<elabTop"
end

end (* local *) 
end (* functor ElabTopFn *)
