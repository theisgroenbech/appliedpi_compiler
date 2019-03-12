
module Int = struct
  type t = int
  let compare = Pervasives.compare
end

module ISet = Set.Make(Int);;
module IMap = Map.Make(Int);;

let var_index = ref 0

type flag_t =
  | Univ
  | Exist

type pol_t = Pos | Neg

type env_t = (string * flag_t) list

(* Terms are either variables, represented as deBrujin indexes or
   functions *)
type term_t =
  | Var of int
  | Skolem of int * term_t list
  | Fun of string * term_t list

type quant_term_t =
  | QVar of int
  | QFun of string * quant_term_t list

type var_term_t =
  | VVar of string
  | VFun of string * var_term_t list

(* Skolemised formulae *)
type form_t =
  | Pred of string * term_t list
  | Tensor of form_t * form_t
  | Lolli of form_t * form_t
  | Pling of (string * flag_t) list * form_t (* (variable name, flag), formula *)

(* Quantified formulae *)
type quant_form_t =
  | QPred of string * quant_term_t list
  | QTensor of quant_form_t * quant_form_t
  | QLolli of quant_form_t * quant_form_t
  | QPling of quant_form_t
  | QExists of string * quant_form_t
  | QForall of string * quant_form_t

type var_form_t =
  | VPred of string * var_term_t list
  | VTensor of var_form_t * var_form_t
  | VLolli of var_form_t * var_form_t
  | VPling of var_form_t
  | VExists of string list * var_form_t
  | VForall of string list * var_form_t

and subst_t =
  | Ext of subst_t * term_t
  | Shift of int

exception Missing_var of string
let rec var_to_quant ctx = function
  | VPred(p, args) ->
     let find_in_stack v =
       let rec find i = function
         | [] -> raise (Missing_var v)
         | v'::vs -> if v = v' then i else find (i+1) vs in
       find 0 ctx in
     let rec var_to_quant = function
       | VVar(x) -> QVar(find_in_stack x)
       | VFun(f, args) -> QFun(f, List.map var_to_quant args) in
     QPred(p, List.map var_to_quant args)
  | VTensor(f1, f2) -> QTensor(var_to_quant ctx f1, var_to_quant ctx f2)
  | VLolli(f1, f2) -> QLolli(var_to_quant ctx f1, var_to_quant ctx f2)
  | VPling(f) -> QPling(var_to_quant ctx f)
  | VExists([], f) -> var_to_quant ctx f
  | VExists(n::ns, f) -> QExists(n, var_to_quant (n::ctx) (VExists(ns, f)))
  | VForall([], f) -> var_to_quant ctx f
  | VForall(n::ns, f) -> QForall(n, var_to_quant (n::ctx) (VExists(ns, f)))

let id = Shift 0

(* If G2 |- s2: G1 and G1 |- s1: G0 and flags2 describes G2 respectively, then G2 |- compose s1 \circ s2: G0 *)
let rec composeSub s1 s2 =
  if s2 = id then s1 else
    (match s1 with
      Shift n -> proj s2 n
    | Ext(s, t) -> Ext(composeSub s s2, applySub s2 t))

(* If G |- ns : G1, G2 and G2 has n elements, then G |- proj ns n : G1 *)
and proj ns n =
  if n = 0 then ns
  else (match ns with
    Shift m -> Shift (n+m)
  | Ext (ns', _) -> proj ns' (n-1))

(* If G |- s : G',  G' |- t : T and flags describe the variables in G, then G |- applySub s t : T[s] *)
and applySub s t =
  if s = id then t
  else
  match t with
  | Var(n) ->
     (match proj s n with
      | Ext(_, t) -> t
      | Shift m -> Var(m))
  | Skolem(i, ms) ->
     let i' = match proj s i with
	 Ext(_, Var n) -> n
       | Shift m -> m
       | x -> Printf.printf "Applying substitution to existential variable %d\n" i;
	     failwith "not" in
     let ms' = List.map (applySub s) ms in
     Skolem(i', ms')
  | Fun(name, args) -> Fun(name, List.map (applySub  s) args)

(* If G | - s: G', flags describes the variables in G and vartype is type of the new variable, the then G, x:T |- extSubst s: G', x:T[s] *)
let extSubst s =
  if s = id then s
  else
    Ext(composeSub s (Shift 1), Var 0)

let rec extSubstIter n s =
  if n = 0 then s
  else extSubst (extSubstIter (n-1) s)

let renameVar name =
  var_index := 1 + !var_index;
  let index = !var_index in
  let name_regexp = Str.regexp "\\(.*\\)\\(_[0-9]+\\)$" in
  if Str.string_match name_regexp name 0 then
    Printf.sprintf "%s_%d" (Str.matched_group 1 name) index
  else
    Printf.sprintf "%s_%d" name index

let renameCtxt ctxt =
  List.map (fun (name, flag) -> (renameVar name, flag)) ctxt

(* If G |- s : G',  G' |- f fmla and flags describe the variables in G, then G |- applySubForm s f : fmla *)
let rec applySubForm s f =
  if s = id then f else
    match f with
    | Pred(name, args) -> Pred(name, List.map (applySub s) args)
    | Lolli(l, r) -> Lolli(applySubForm s l, applySubForm s r)
    | Tensor(l, r) -> Tensor (applySubForm s l, applySubForm s r)
    | Pling(ctxt, f) -> Pling(ctxt, applySubForm (extSubstIter (List.length ctxt) s) f)


(* If \Psi vdash t and \Phi \vdash mu: \Psi, then \Phi vdash skolem_term mu flags t *)
let rec skolemTerm mu t =
  match t with
    QVar(n) -> applySub mu (Var n)
  | QFun(name,ts) -> Fun(name, List.map (skolemTerm mu) ts)

(* allAlls flags i returns the list of all indices of universal variables in flags, starting with i *)
let rec allAlls ctxt i =
  match ctxt with
    [] -> []
  | (_, Univ)::ctxt' -> (Var i)::allAlls ctxt' (i+1)
  | (_, Exist)::ctxt' -> allAlls ctxt' (i+1)

(* If Psi \vdash K, \Phi \vdash \mu: \Psi, ctxt and flags desribe Phi and skolemForm mu ctxt flags K = ctxt',flags',L), then ctxt' and flags' describe \Phi', SK(\Psi; K; mu)  =  L and \Phi, \Phi' \vdash L. *)
let rec skolemForm mu ctxt = function
  | QPred(name,args)  -> ([],  Pred(name, List.map (skolemTerm mu) args))
  | QTensor(l, r) ->
     let (ctxt_l, l') = skolemForm mu ctxt l in
     let (ctxt_r, r') = skolemForm mu ctxt r in
     let nl = List.length ctxt_l in
     let nr = List.length ctxt_r in
     let lift_r = extSubstIter nr (Shift nl) in
     let lift_l = Shift(nr) in
     (ctxt_r @ ctxt_l, Tensor(applySubForm lift_l l', applySubForm lift_r r'))
  | QLolli(l, r) ->
     let ([], l') = skolemForm mu ctxt l in
     let (ctxt', r') = skolemForm mu ctxt r in
       (ctxt', Lolli(applySubForm (Shift (List.length ctxt')) l', r'))
  | QForall(name, f) ->
     let (ctxt', f) = skolemForm (Ext(composeSub mu (Shift 1), Var 0)) ((name, Univ)::ctxt) f in
     (ctxt'@[name, Univ], f)
  | QExists(name, f) ->
     let (ctxt', f) = skolemForm (Ext(composeSub mu (Shift 1), Skolem(0, (allAlls ctxt 1)))) ((name, Exist)::ctxt) f in
     (ctxt'@[name, Exist], f)
  | QPling f ->
     let (ctxt', f') = skolemForm mu ctxt f in
     ([], Pling(ctxt', f'))

let skolemForm = skolemForm id []

exception Unify

(* If ls is list of length > n, strengthenCtxtFlags ls is a list with the n-th element removed (the first element is 0)*)
let rec strengthenCtxtFlags ls n =
  match ls with
    l::ls' ->
      if n = 0 then ls'
      else l::(strengthenCtxtFlags ls' (n-1))

(* If G, x:T, G' is a context such that flags desribes G, x:T, G', G' has length n, and G, x:T, G' |- t:T, then G, G' |- strengthenTerm t n: T if the variable n does not occur in t. If this is the case, the exception Occurs is raised. *)
let rec strengthenTerm t n =
  match t with
    Var m ->
      if m = n then raise Unify
      else if m > n then Var(m-1)
      else t
  | Skolem(m, ts) ->
     if m = n then raise Unify
     else if m > n then Skolem(m-1, List.map (fun t -> strengthenTerm t n) ts)
     else Skolem(m, List.map (fun t -> strengthenTerm t n) ts)
  | Fun(name,ts) -> Fun(name, List.map (fun t -> strengthenTerm t n) ts)

(* if G, G', G1 |-  s: G'', G' has length n and flags describes at least the elements of G' and G1 has length base, then G, G', G1 |- extendSubst flags s n: G'', G' *)
let extendSubst s n base =
  let rec eSubst s n =
    if n = 0 then s
    else
      let t = Var (n-1+base) in
      eSubst (Ext(s, t)) (n-1) in
  eSubst s n

(* If G, x:T, G', G' has length n, flags describes at least the variables in G', vartype is the type of x, then G, G' |- termToSubst t n: G, x:T, G' if the variable n does not occur in t. If this is not the case, the the exception Occurs is raised. *)
let termToSubst t n =
  extendSubst (Ext(Shift n, (strengthenTerm t n))) n 0

(* If unify(flags, t1, t2) = (flags', s) and G |- t1:T, G |- t2:T and flags describes the variables in G, then G' |- s: G,  t1[s] = t2[s] and flags' describe the variables in G' and the variable names in G' do not change *)
let rec unify ctxt x y =
  match x, y with
  | Var i, Var j when i=j -> ctxt, id
  | Var i, t -> strengthenCtxtFlags ctxt i, (termToSubst t i)
  | (Skolem _ as sk1), (Skolem _ as sk2) when sk1 = sk2 -> ctxt, id
  | Fun(name1, fargs1), Fun(name2, fargs2) ->
     if name1 = name2 && (List.length fargs1 = List.length fargs2) then unifyArgs ctxt fargs1 fargs2
     else raise Unify
  | _, Var _ -> unify ctxt  y x
  | _, _ -> raise Unify

(* If unifyArgs(flags, args1, args2) = (flags', s) and G |- args1:T, G |- args2:T and flags describes the variables in G, then G' |- s: G,  args1[s] = args2[s] and flags' describe the variables in G' *)
and unifyArgs ctxt args1 args2 = match args1, args2 with
  | [], [] -> ctxt, id
  | x::args1', y::args2' ->
     let ctxt', mu =  unify ctxt x y in
     let ctxt', mu' = unifyArgs ctxt' (List.map (applySub mu) args1') (List.map (applySub mu) args2') in
     (ctxt', (composeSub mu mu'))
  | _, _ -> raise Unify

exception Match

let rec matchTerm ctxt x y =
  match x,y with
  | Var i, Var j when i = j -> ctxt, id
  | Var i, t -> strengthenCtxtFlags ctxt i, (termToSubst t i)
  | (Skolem _ as sk1), (Skolem _ as sk2) when sk1 = sk2 -> ctxt, id
  | Fun(name1, fargs1), Fun(name2, fargs2) ->
     if name1 = name2 && (List.length fargs1 = List.length fargs2) then matchArgs ctxt fargs1 fargs2
     else raise Match
  | _, _ -> raise Match

and matchArgs ctxt args1 args2 = match args1, args2 with
  | [], [] -> ctxt, id
  | x::args1', y::args2' ->
     let ctxt', mu =  matchTerm ctxt x y in
     let ctxt', mu' = matchArgs ctxt' (List.map (applySub mu) args1') (List.map (applySub mu) args2') in
     (ctxt', (composeSub mu mu'))
  | _, _ -> raise Unify

let rec in_s =
  let ps = [Pling([], Pred("k", [Var 0]))] in
  let rec renames_t = function
    | Var _, Var _ -> true
    | Fun(f1, args1), Fun(f2, args2) ->
       f1 = f2 &&
         List.length args1 = List.length args2 &&
           List.for_all renames_t (List.combine args1 args2)
    | _, _ -> false in
  let renames = function
    | Pred(name1, args1), Pred(name2, args2)
      | Pling([], Pred(name1, args1)), Pling([], Pred(name2, args2))->
       name1 = name2 &&
         List.length args1 = List.length args2  &&
           List.for_all renames_t (List.combine args1 args2)
    | Pred _, _ -> false
    | _, Pred _ -> false
    | Pling([], Pred _), _ -> false
    | _, Pling([], Pred _) -> false
    | _ -> failwith "we should check only predicates here" in
  let rec check = function
    | p::ps -> fun x -> renames (p,x) || check ps x
    | [] -> fun x -> false in
  check ps
