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
	| Term.Var i -> failwith "Var"
	| Term.Cast (c,_,_) -> gather c ls
	| Term.Prod (_,_,_) -> (* forall? *)
	  failwith "Prod"
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
	| Term.Case (_,c,_,arms) ->
	  Array.fold_left (fun a x -> gather x a) (gather c ls) arms
	| Term.Fix (_,(_,_,ca)) ->
	  Array.fold_left (fun a x -> gather x a) ls ca
	| Term.CoFix _ ->
	  failwith "CoFix"
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
	| Term.Prod (_,_,_) -> (* forall? *)
	  failwith "Prod"
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
	  Term.mkCase (a, replace off c, replace off b, 
		       Array.map (replace off) arms) (** TODO : this is wrong *)
	| Term.Fix (a,(b,c,ca)) ->
	  Term.mkFix (a,(b,c, Array.map (replace off) ca))
	| Term.CoFix _ -> d
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

end  

let _=Mltop.add_known_module "Localize_plugin"

(**
let pp_print () =
  let buf = Buffer.create 4 in 
  let fmt = Format.formatter_of_buffer buf in 
  let _ = (Format.fprintf fmt "%a\n%!" Section.print ()) in 
  (Buffer.contents buf)
**)

open Tacexpr
open Tacinterp

TACTIC EXTEND localize
  | ["localize" constr(n)] -> 
    [
      fun gl ->
	let env = Tacmach.pf_env gl in
	let r = Localize.localize env n [] in 
	Tactics.exact_check r gl ]
  | ["localize" constr(n) "blacklist" "[" reference_list(bl) "]" ] -> 
    [
      fun gl ->
	let env = Tacmach.pf_env gl in
	let r = Localize.localize env n (List.map Libnames.destConstRef bl) in 
	Tactics.exact_check r gl ]
END;;

