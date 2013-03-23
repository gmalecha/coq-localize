(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

module Localize = struct

  let get_decl (e : Environ.env) (v : Names.constant)
      : Declarations.constant_body option =
    try
      let b = Environ.lookup_constant v e in
      if Declarations.is_opaque b then None
      else Some b
    with
      | Not_found -> None

  let get_body (cb : Declarations.constant_body) : Term.constr =
    match Declarations.body_of_constant cb with
      | Some x -> Declarations.force x
      | None -> failwith "couldn't get body"

  let get_type (e : Environ.env) (c : Names.constant) : Term.types =
    Typeops.type_of_constant_type e (Environ.constant_type e c)
    
  let gather (e : Environ.env) (d : Term.constr) (ls : Names.constant list) 
      (skip : Names.constant list)
      : Names.constant list =
    let rec gather (d : Term.constr) (ls : Names.constant list) 
      : Names.constant list =
      match Term.kind_of_term d with
	| Term.Rel _
	| Term.Meta _
	| Term.Sort _ 
	| Term.Evar _ -> ls
	| Term.Var i -> ls
	| Term.Cast (c,_,_) -> gather c ls
	| Term.Prod (n,t,b) -> (* forall *)
	  gather b (gather t ls)
	| Term.Lambda (n,_,body) -> (* fun *)
	  gather body ls
	| Term.LetIn (_,body,_,c) ->
	  gather c (gather body ls)
	| Term.App (f,args) ->
	  Array.fold_left (fun a x -> gather x a) (gather f ls) args
	| Term.Const c ->
	  if List.exists (fun x -> x = c) ls 
	  or List.exists (fun x -> x = c) skip 
	  then
	    ls
	  else
	    begin
	      match get_decl e c with
		| None -> ls
		| Some cb ->
		  c :: gather (get_body cb) ls
	    end
	| Term.Ind i -> ls
	| Term.Construct _ -> ls
	| Term.Case (_,c,r,arms) ->
	  Array.fold_left (fun a x -> gather x a) (gather r (gather c ls)) arms
	| Term.Fix (_,(_,_,ca)) ->
	  Array.fold_left (fun a x -> gather x a) ls ca
	| Term.CoFix (i,(_,_,ca)) ->
	  Array.fold_left (fun a x -> gather x a) ls ca
    in
    gather d ls

  let replace (resolve : Names.constant -> int -> Term.constr) (d : Term.constr) 
      : Term.constr =
    let rec replace (off : int) (d : Term.constr) : Term.constr =
      match Term.kind_of_term d with
	| Term.Rel _ -> d
	| Term.Meta _ -> d
	| Term.Sort _ -> d
	| Term.Evar _ -> d
	| Term.Var i -> d
	| Term.Cast (c,a,b) -> 
	  Term.mkCast (replace off c, a, b)
	| Term.Prod (n,a,b) ->
	  Term.mkProd (n, replace off a, replace (1 + off) b)
	| Term.Lambda (n,t,body) -> (* fun *)
	  Term.mkLambda (n, t, replace (1+off) body)
	| Term.LetIn (a, body, b, c) ->
	  Term.mkLetIn (a, replace off body, b, replace (1+off) c)
	| Term.App (f,args) ->
	  Term.mkApp (replace off f, Array.map (replace off) args)
	| Term.Const c ->
	  resolve c off
	| Term.Ind _ -> d
	| Term.Construct _ -> d
	| Term.Case (a,c,b,arms) ->
	  let binders = a.Term.ci_cstr_ndecls in
	  Term.mkCase (a,
		       replace off c,
		       replace off b,
		       Array.mapi (fun i c -> 
			 let patterns = Array.get binders i in
			 replace (patterns + off) c) arms)
	| Term.Fix (a,(b,c,ca)) ->
	  let n = Array.length c in
	  Term.mkFix (a,(b, 
			 Array.map (replace (n + off)) c,
			 Array.map (replace (n + off)) ca))
	| Term.CoFix (a,(b,c,ca)) -> 
	  let n = Array.length c in
	  Term.mkCoFix (a,(b, 
			 Array.map (replace (n + off)) c,
			 Array.map (replace (n + off)) ca))
    in
    replace 1 d

  let inline (env : Environ.env) (d : Term.constr) (ls : Names.constant list) : Term.constr =
    let rec inline (resolve : Names.constant -> int -> Term.constr) 
	           (rem : Names.constant list) 
		   (d : Term.constr) : Term.constr =
      match rem with
	| [] -> 
	  replace resolve d
	| r :: rem ->
	  match get_decl env r with
	    | Some cbody ->
	      let rest = 
		inline (fun v acc -> if v = r then Term.mkRel acc 
	                             else resolve v (1 + acc))
	               rem
	               d
	      in
	      Term.mkLetIn (Names.Anonymous, replace resolve (get_body cbody), get_type env r, rest)
	    | None -> failwith "couldn't get decl"
    in
    inline (fun x _ -> Term.mkConst x) ls d

  let localize (env : Environ.env) (d : Term.constr) (skip : Names.constant list) 
      : Term.constr =
    let x = gather env d [] skip in
    inline env d (List.rev x)

  let tactic (t : Term.constr) (bl : Libnames.global_reference list) 
      (k : Term.constr -> Tacmach.tactic) : Tacmach.tactic =
    fun gl ->
      let env = Tacmach.pf_env gl in
      let black = List.map Libnames.destConstRef bl in
      let r = localize env t black in
      k r gl

end  

let _=Mltop.add_known_module "Localize_plugin"

open Tacexpr
open Tacinterp

TACTIC EXTEND localize
  | ["localize" constr(n)] -> 
    [ Localize.tactic n [] (Tactics.exact_check) ]
  | ["localize" constr(n) "as" ident(name) ] -> 
    [ Localize.tactic n [] (Tactics.pose_proof (Names.Name name)) ]
  | ["localize" constr(n) "blacklist" "[" reference_list(bl) "]" ] -> 
    [ Localize.tactic n bl (Tactics.exact_check) ]
  | ["localize" constr(n) "blacklist" "[" reference_list(bl) "]" "as" ident(name) ] -> 
    [ Localize.tactic n bl (Tactics.pose_proof (Names.Name name)) ]
END;;

