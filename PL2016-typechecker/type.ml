type exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

type program = exp

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

(* type equation 확장 *)
let extend_typ_eqn : (typ * typ) -> (typ * typ) list -> (typ * typ) list
= fun (a, b) l -> (a, b) :: l

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ " ^ ")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x (* x랑 묶인 typ을 반환한다. *)
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst (* x랑 묶인 typ을 반환한다. *)

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty -> match e with
| CONST n -> [(ty, TyInt)]
| VAR x -> [(ty, tenv x)]
| ADD (e1, e2) -> [(ty, TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
| SUB (e1, e2) -> [(ty, TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
| MUL (e1, e2) -> [(ty, TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
| DIV (e1, e2) -> [(ty, TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
| ISZERO n -> [(ty, TyBool)] @ (gen_equations tenv n TyInt)
| IF (e1, e2, e3) -> (gen_equations tenv e1 TyBool) @ (gen_equations tenv e2 ty) @ (gen_equations tenv e3 ty)
| LET (x, e1, e2) -> let a = fresh_tyvar() in
                     let newenv = TEnv.extend (x, a) tenv in
                     (gen_equations tenv e1 a) @ (gen_equations newenv e2 ty)
| LETREC (f, x, e1, e2) -> let a1 = fresh_tyvar() in
                           let a2 = fresh_tyvar() in
                           let newenv1 = TEnv.extend (x, a1) tenv in
                           let newenv2 = TEnv.extend (f, TyFun (a1, a2)) tenv in
                           (gen_equations newenv1 e1 a2) @ (gen_equations newenv2 e2 ty)
| PROC (x, body) -> let a1 = fresh_tyvar() in
                    let a2 = fresh_tyvar() in
                    let newenv = TEnv.extend (x, a1) tenv in
                    [(ty, TyFun (a1, a2))] @ (gen_equations newenv body a2)
| CALL (e1, e2) -> let a = fresh_tyvar() in
                   (gen_equations tenv e1 (TyFun (a, ty))) @ (gen_equations tenv e2 a)
| _ -> raise TypeError

let rec occurs : var -> typ -> bool
=fun x t -> match t with
| TyInt -> false
| TyBool -> false
| TyVar y -> if x = y then true else false
| TyFun (a, b) -> (occurs x a) || (occurs x b)


let rec unify : (typ * typ) -> Subst.t -> Subst.t
=fun teqn subs -> match teqn with
| (TyInt, TyInt) -> subs
| (TyBool, TyBool) -> subs
| (TyVar a, t) -> (match t with
                   (* check if it is meaningless *)
                   | TyVar b -> if a = b then subs else (Subst.extend a t subs)
                   | TyFun (x, y) -> if (occurs a x) || (occurs a y) then raise TypeError else (Subst.extend a t subs)
                   | _ -> Subst.extend a t subs
                  )
| (t, TyVar a) -> unify (TyVar a, t) subs
| (TyFun (a1, a2), TyFun (b1, b2)) -> let newsubs = unify (a1, b1) subs in
                                      let a3 = Subst.apply a2 newsubs in
                                      let b3 = Subst.apply b2 newsubs in
                                      unify (a3, b3) newsubs
| _ -> raise TypeError;;

(* unifyall *)
let solve : typ_eqn -> Subst.t
=fun eqns -> []


let typeof : exp -> typ (* Do not modify this function *)
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns;
          print_endline "" in
  let subst = solve eqns in
  let ty = Subst.apply new_tv subst in
   print_endline "= Substitution = ";
    Subst.print subst;
    print_endline "";
    print_endline ("Type: " ^ string_of_type ty);
    print_endline "";
    ty

let eqn = gen_equations TEnv.empty (LETREC ("f","x", ADD(VAR "x", CONST 2), CALL (VAR "f", CONST 2))) (TyVar "t");;

