(* eval.ml *)
(* Author: Dang Truong *)

open AstUtils
open Exp

let step_binOp (op : binOp) (v1 : ast) (v2 : ast) : ast =
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
      let body2 = subst body1 (UnOp (RecFun (f, x), body)) f in
      body2
  | _ -> assert false

let rec step_internal (e : ast) : ast =
  match e with
  | Base (Var _)
  | Base (Int _)
  | Base (Bool _)
  | Base Unit
  | Base Nil
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
  | BinOp (Cons, e1, e2) ->
      if is_value e1 && is_value e2 then assert false
      else if is_value e2 then BinOp (Cons, step_internal e1, e2)
      else BinOp (Cons, e1, step_internal e2)
  | BinOp (Pair, e1, e2) ->
      if is_value e1 && is_value e2 then assert false
      else if is_value e2 then BinOp (Pair, step_internal e1, e2)
      else BinOp (Pair, e1, step_internal e2)
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

let step (e : ast) : ast option =
  if is_value e then None else Some (step_internal e)

let rec eval (e : ast) : ast =
  match step e with None -> e | Some e' -> eval e'
