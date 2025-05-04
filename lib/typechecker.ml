(* typechecker.ml *)
(* Author: Dang Truong, Tran Ong *)

open Exp
open Type

let counter = ref 0

(*
 * subst_ty : (int * ty) list -> ty -> ty
 * REQUIRES: [subst] is a valid substitution map.
 * ENSURES: [subst_ty subst t] applies the substitution [subst] to type [t] and 
 *          returns a new type with all type variables in [t] replaced according
 *          to [subst].
 *)
let rec subst_ty subst t =
  match t with
  | Var id -> (
      (* Find most recent mapping for id, if any *)
      match List.assoc_opt id subst with
      | Some t' -> subst_ty subst t' (* recursively resolve substitution *)
      | None -> Var id)
  | List t' -> List (subst_ty subst t')
  | Pair (t1, t2) -> Pair (subst_ty subst t1, subst_ty subst t2)
  | Fun (t1, t2) -> Fun (subst_ty subst t1, subst_ty subst t2)
  | Int | Bool | Unit -> t (* Base types remain unchanged *)

(*
 * subst_constraints : (int * ty) list -> (ty * ty) list -> (ty * ty) list
 * REQUIRES: [subst] is a valid substitution map.
 * ENSURES: [subst_constraints subst cs] applies the substitution [subst] to all
 *          types in the constraints [cs] and returns a new list of constraints
 *          with substitution applied to both sides.
 *)
let subst_constraints subst cs =
  List.map (fun (t1, t2) -> (subst_ty subst t1, subst_ty subst t2)) cs

(*
 * occurs_check : int -> ty -> bool
 * REQUIRES: [id] is a valid type variable identifier.
 * ENSURES: [occurs_check id t] returns true if type variable with [id] appears
 *          within type [t] and false otherwise.
 *)
let rec occurs_check id t =
  match t with
  | Var v -> v = id
  | List t1 -> occurs_check id t1
  | Pair (t1, t2) -> occurs_check id t1 || occurs_check id t2
  | Fun (t1, t2) -> occurs_check id t1 || occurs_check id t2
  | Int | Bool | Unit -> false (* Base types never contain variables *)

(*
 * unify : (ty * ty) list -> (int * ty) list option
 * REQUIRES: [constraints] is a list of type equality constraints.
 * ENSURES: [unify constraints] attempts to find a substitution that makes all
 *          pairs of types in [constraints] equal. Returns Some substitution if
 *          unification succeeds, or None if unification fails. The substitution
 *          maps type variables to their unified types.
 *)
let rec unify constraints =
  match constraints with
  | [] -> Some [] (* No constraints means empty substitution *)
  | (t1, t2) :: rest -> (
      if t1 = t2 then
        (* If types are already equal, just unify the rest *)
        unify rest
      else
        match (t1, t2) with
        (* If one side is a type variable, try to substitute it *)
        | Var id, t | t, Var id -> (
            if occurs_check id t then
              (* Occurs check prevents infinite types *)
              None
            else
              let binding = [ (id, t) ] in
              let new_constraints = subst_constraints binding rest in
              match unify new_constraints with
              | None -> None
              | Some subst -> Some ((id, t) :: subst))
        | Fun (a1, b1), Fun (a2, b2) | Pair (a1, b1), Pair (a2, b2) ->
            (* Break down complex types into their components *)
            unify ((a1, a2) :: (b1, b2) :: rest)
        | List t1, List t2 ->
            (* Lists must contain same element type *)
            unify ((t1, t2) :: rest)
        | _ ->
            (* Type constructors mismatch - unification fails *)
            None)

(*
 * fresh_tyvar : unit -> ty
 * REQUIRES: None.
 * ENSURES: [fresh_tyvar ()] generates a fresh type variable with a unique
 *          identifier and returns it as a ty.
 *)
let fresh_tyvar () =
  let id = !counter in
  counter := id + 1;
  Var id

(*
 * lookup_tyenv : (string * ty) list -> string -> ty option
 * REQUIRES: [env] is a valid typing environment.
 * ENSURES: [lookup_tyenv env x] returns Some t if variable [x] is bound to
 *          type t in environment [env], or None if [x] is not bound.
 *)
let lookup_tyenv env x = List.assoc_opt x env

(*
 * infer_expr : (string * ty) list -> ast -> ty * (ty * ty) list
 * REQUIRES: [env] is a valid typing environment.
 * ENSURES: [infer_expr env e] returns a pair (t, cs) where t is the inferred
 *          type of expression [e] in environment [env] and cs is a list of
 *          type constraints that must be satisfied for [e] to have type [t].
 *)
let rec infer_expr env e =
  match e with
  | Base b -> (
      match b with
      (* Base types: constants have fixed types with no constraints *)
      | Int _ -> (Int, [])
      | Bool _ -> (Bool, [])
      | Unit -> (Unit, [])
      | Nil ->
          (* Empty list: polymorphic type 'a list with fresh type variable *)
          let elem_type = fresh_tyvar () in
          (List elem_type, [])
      | Var x -> (
          (* Variable: look up type in environment or fail if unbound *)
          match lookup_tyenv env x with
          | Some t -> (t, [])
          | None -> failwith ("Unbound variable: " ^ x)))
  | UnOp (op, e1) -> (
      (* Unary operators: infer type of subexpression and add constraints *)
      (* let t1, c1 = infer_expr env e1 in *)
      match op with
      | Not ->
          (* Not operator: input must be Bool, output is Bool *)
          let t1, c1 = infer_expr env e1 in
          (Bool, (t1, Bool) :: c1)
      | Neg ->
          (* Negation: input must be Int, output is Int *)
          let t1, c1 = infer_expr env e1 in
          (Int, (t1, Int) :: c1)
      | Fun x ->
          (* Lambda: fun x -> e1 has type param_type -> body_type, param_type
             is fresh *)
          let param_type = fresh_tyvar () in
          let env' = (x, param_type) :: env in
          (* Infer type of body in extended environment to account for x *)
          let body_type, body_constraints = infer_expr env' e1 in
          (Fun (param_type, body_type), body_constraints)
      | RecFun (f, x) ->
          (* Recursive function: f x = e1 has type fun_type = param_type ->
             return_type *)
          let param_type = fresh_tyvar () in
          let return_type = fresh_tyvar () in
          let fun_type = Fun (param_type, return_type) in
          let env' = (x, param_type) :: (f, fun_type) :: env in
          (* Infer type of body in extended environment to handle
             recursion *)
          let body_type, body_constraints = infer_expr env' e1 in
          (fun_type, (return_type, body_type) :: body_constraints))
  | BinOp (op, e1, e2) -> (
      (* Binary operators: infer types of both subexpressions *)
      match op with
      | Add | Sub | Mul | Div ->
          (* Arithmetic: both inputs must be Int, output is Int *)
          let t1, c1 = infer_expr env e1 in
          let t2, c2 = infer_expr env e2 in
          (Int, (t1, Int) :: (t2, Int) :: (c1 @ c2))
      | Eq | Neq | Geq | Leq | Gt | Lt ->
          (* Comparisons: inputs must unify, output is Bool *)
          let t1, c1 = infer_expr env e1 in
          let t2, c2 = infer_expr env e2 in
          (Bool, (t1, t2) :: (c1 @ c2))
      | And | Or ->
          (* Logical: both inputs must be Bool, output is Bool *)
          let t1, c1 = infer_expr env e1 in
          let t2, c2 = infer_expr env e2 in
          (Bool, (t1, Bool) :: (t2, Bool) :: (c1 @ c2))
      | App ->
          (* Function application: t1 must be t2 -> result_type, output is
             result_type *)
          let t1, c1 = infer_expr env e1 in
          let t2, c2 = infer_expr env e2 in
          let result_type = fresh_tyvar () in
          (result_type, (t1, Fun (t2, result_type)) :: (c1 @ c2))
      | Cons ->
          (* Cons: t2 must be t1 list, output is t1 list *)
          let t1, c1 = infer_expr env e1 in
          let t2, c2 = infer_expr env e2 in
          (List t1, (t2, List t1) :: (c1 @ c2))
      | Pair ->
          (* Pair: output is t1 * t2 *)
          let t1, c1 = infer_expr env e1 in
          let t2, c2 = infer_expr env e2 in
          (Pair (t1, t2), c1 @ c2)
      | MatchP (x, y) ->
          (* Pair matching: t1 must be a pair, bind x to first element type
             and y to second element type in e2 *)
          let t1, c1 = infer_expr env e1 in
          let first_elem_type = fresh_tyvar () in
          let second_elem_type = fresh_tyvar () in
          let env' = (x, first_elem_type) :: (y, second_elem_type) :: env in
          (* Infer type of body in extended environment to use x and y *)
          let body_type, body_constraints = infer_expr env' e2 in
          ( body_type,
            (t1, Pair (first_elem_type, second_elem_type))
            :: (c1 @ body_constraints) )
      | Let x ->
          (* Let binding: bind x to t1 in e2 *)
          let t1, c1 = infer_expr env e1 in
          let env' = (x, t1) :: env in
          (* Infer type of body in extended environment to account for x *)
          let body_type, body_constraints = infer_expr env' e2 in
          (body_type, c1 @ body_constraints)
      | LetRec (f, x) ->
          (* Recursive let: f x = e1 has type fun_type = param_type ->
             return_type *)
          let param_type = fresh_tyvar () in
          let return_type = fresh_tyvar () in
          let fun_type = Fun (param_type, return_type) in
          let env1 = (x, param_type) :: (f, fun_type) :: env in
          (* Infer type of function body in extended environment *)
          let body_type, body_constraints = infer_expr env1 e1 in
          let env2 = (f, fun_type) :: env in
          (* Infer type of outer body in extended environment to use f *)
          let outer_type, outer_constraints = infer_expr env2 e2 in
          ( outer_type,
            (body_type, return_type) :: (body_constraints @ outer_constraints)
          ))
  | TrinOp (op, e1, e2, e3) -> (
      (* Ternary operators: infer types of all subexpressions *)
      match op with
      | MatchL (x, xs) ->
          (* List matching: t1 must be a list, bind x to element type and xs
             to list of same element type in e3 *)
          let t1, c1 = infer_expr env e1 in
          let t2, c2 = infer_expr env e2 in
          let elem_type = fresh_tyvar () in
          let env' = (x, elem_type) :: (xs, List elem_type) :: env in
          (* Infer type of cons branch in extended environment to use x and
             xs *)
          let cons_type, cons_constraints = infer_expr env' e3 in
          (* Both branches must have the same type, and t1 must be a list *)
          ( t2,
            (t1, List elem_type) :: (t2, cons_type)
            :: (c1 @ c2 @ cons_constraints) )
      | Cond ->
          (* Conditional: t1 must be Bool, t2 and t3 must unify *)
          let t1, c1 = infer_expr env e1 in
          let t2, c2 = infer_expr env e2 in
          let t3, c3 = infer_expr env e3 in
          (t2, (t1, Bool) :: (t2, t3) :: (c1 @ c2 @ c3)))

(*
 * infer : ast -> ty option
 * REQUIRES: [e] is a valid AST expression.
 * ENSURES: [infer e] performs type inference on [e] and returns Some t if [e]
 *          is well-typed with inferred type t, or None if [e] has a type error.
 *)
let infer e =
  (* Reset type variable counter for fresh inference *)
  counter := 0;
  let typ, constraints = infer_expr [] e in
  match unify constraints with
  | None -> None (* Type constraints cannot be satisfied *)
  | Some subst -> Some (subst_ty subst typ)
