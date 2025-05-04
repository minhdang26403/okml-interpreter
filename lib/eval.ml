(* eval.ml *)
(* Author: Dang Truong, Tran Ong *)

open AstUtils
open Exp

(*
 * step_binOp : binOp -> ast -> ast -> ast
 * REQUIRES: two operands [v1] and [v2] are values
 * ENSURES: [step_binOp op v1 v2] |-*-> v1 op v2
 *)
let step_binOp op v1 v2 =
  match (op, v1, v2) with
  | Add, Base (Int a), Base (Int b) -> Base (Int (a + b))
  | Sub, Base (Int a), Base (Int b) -> Base (Int (a - b))
  | Mul, Base (Int a), Base (Int b) -> Base (Int (a * b))
  | Div, Base (Int a), Base (Int b) -> Base (Int (a / b))
  | Eq, v1, v2 -> Base (Bool (eq_ast v1 v2))
  | Neq, v1, v2 -> Base (Bool (not (eq_ast v1 v2)))
  | Geq, v1, v2 -> Base (Bool (not (lt_ast v1 v2)))
  | Leq, v1, v2 -> Base (Bool (not (gt_ast v1 v2)))
  | Gt, v1, v2 -> Base (Bool (gt_ast v1 v2))
  | Lt, v1, v2 -> Base (Bool (lt_ast v1 v2))
  | App, UnOp (Fun x, body), v -> subst body v x
  | App, UnOp (RecFun (f, x), body), v ->
      let body1 = subst body v x in
      let rec_fun_val = UnOp (RecFun (f, x), body) in
      let body2 = subst body1 rec_fun_val f in
      body2
  (* just an identity operation for cons and pair values *)
  | Cons, v1, v2 -> BinOp (Cons, v1, v2)
  | Pair, v1, v2 -> BinOp (Pair, v1, v2)
  | _ -> assert false

(*
 * step_internal: ast -> ast
 * REQUIRES: [e] is a valid, non-value AST expression.
 * ENSURES: Returns the AST resulting from performing a single evaluation step on [e].
 *          Behavior is undefined (or may raise an exception) if [e] is already a value.
 *)
let rec step_internal e =
  match e with
  | Base (Var _ | Int _ | Bool _ | Unit | Nil)
  | UnOp (Fun _, _)
  | UnOp (RecFun (_, _), _) ->
      assert false
  | UnOp (op, e) ->
      if is_value e then
        match (op, e) with
        | Not, Base (Bool b) -> Base (Bool (not b))
        | Neg, Base (Int x) -> Base (Int (-x))
        | _ -> assert false
      else UnOp (op, step_internal e)
  | BinOp (And, e1, e2) ->
      if is_value e1 then
        match e1 with
        | Base (Bool false) -> Base (Bool false)
        | Base (Bool true) ->
            if is_value e2 then e2 else BinOp (And, e1, step_internal e2)
        | _ -> assert false
      else BinOp (And, step_internal e1, e2)
  | BinOp (Or, e1, e2) ->
      if is_value e1 then
        match e1 with
        | Base (Bool true) -> Base (Bool true)
        | Base (Bool false) ->
            if is_value e2 then e2 else BinOp (Or, e1, step_internal e2)
        | _ -> assert false
      else BinOp (Or, step_internal e1, e2)
  | BinOp (MatchP (x, y), e1, e2) ->
      if is_value e1 then
        match e1 with
        | BinOp (Pair, v1, v2) ->
            let e2' = subst e2 v1 x in
            subst e2' v2 y
        | _ -> assert false
      else BinOp (MatchP (x, y), step_internal e1, e2)
  | BinOp (Let x, e1, e2) ->
      if is_value e1 then subst e2 e1 x
      else BinOp (Let x, step_internal e1, e2)
  | BinOp (LetRec (f, x), e1, e2) ->
      (* e1 is the function body, so it is already a value. Hence, we don't
         need to step it *)
      let fun_val = UnOp (RecFun (f, x), e1) in
      subst e2 fun_val f
  | BinOp (op, e1, e2) ->
      if is_value e1 && is_value e2 then step_binOp op e1 e2
      else if is_value e2 then BinOp (op, step_internal e1, e2)
      else BinOp (op, e1, step_internal e2)
  | TrinOp (MatchL (x, xs), e1, e2, e3) ->
      if is_value e1 then
        match e1 with
        | Base Nil -> e2
        | BinOp (Cons, hd, tl) ->
            let e3' = subst e3 hd x in
            subst e3' tl xs
        | _ -> assert false
      else TrinOp (MatchL (x, xs), step_internal e1, e2, e3)
  | TrinOp (Cond, e1, e2, e3) ->
      if is_value e1 then
        match e1 with
        | Base (Bool true) -> e2
        | Base (Bool false) -> e3
        | _ -> assert false
      else TrinOp (Cond, step_internal e1, e2, e3)

(*
 * step: ast -> ast option
 * REQUIRES: [e] is a valid AST expression.
 * ENSURES: Returns [Some e'] if [e] can take a single evaluation step to [e']; 
 *          returns [None] if [e] is already a value and cannot be reduced further.
 *)
let step (e : ast) : ast option =
  if is_value e then None else Some (step_internal e)

(*
 * eval: ast -> ast
 * REQUIRES: [e] is a valid AST expression.
 * ENSURES: Fully evaluates [e] to a value (in normal form), returning the resulting AST.
 *          Raises an exception if evaluation encounters an error (e.g., type mismatch, division by zero).
 *)
let rec eval (e : ast) : ast =
  match step e with None -> e | Some e' -> eval e'
