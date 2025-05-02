(* opt.ml *)
(* Author: Dang Truong *)

open AstUtils
open Exp

let rec constProp (e : ast) : ast =
  match e with
  | Base _ -> e (* Constants and variables are unchanged *)
  | UnOp (op, e1) -> (
      let e1' = constProp e1 in
      match (op, e1') with
      | Not, Base (Bool b) -> Base (Bool (not b))
      | Neg, Base (Int n) -> Base (Int (-n))
      | _ -> UnOp (op, e1'))
  | BinOp (And, e1, e2) -> (
      let e1' = constProp e1 in
      match e1' with
      | Base (Bool false) -> Base (Bool false)
      | Base (Bool true) -> constProp e2
      | _ -> BinOp (And, e1', constProp e2))
  | BinOp (Or, e1, e2) -> (
      let e1' = constProp e1 in
      match e1' with
      | Base (Bool false) -> constProp e2
      | Base (Bool true) -> Base (Bool true)
      | _ -> BinOp (Or, e1', constProp e2))
  | BinOp (op, e1, e2) -> (
      let e1' = constProp e1 in
      let e2' = constProp e2 in
      match (op, e1', e2') with
      | Add, Base (Int a), Base (Int b) -> Base (Int (a + b))
      | Sub, Base (Int a), Base (Int b) -> Base (Int (a - b))
      | Mul, Base (Int a), Base (Int b) -> Base (Int (a * b))
      | Div, _, Base (Int 0) -> BinOp (Div, e1', e2')
      | Div, Base (Int a), Base (Int b) -> Base (Int (a / b))
      | (Eq | Neq | Geq | Leq | Gt | Lt), UnOp (Fun _, _), _
      | (Eq | Neq | Geq | Leq | Gt | Lt), UnOp (RecFun _, _), _ ->
          (* avoid comparing functions *)
          BinOp (op, e1', e2')
      | Eq, v1, v2 when is_value v1 && is_value v2 ->
          Base (Bool (eq_ast v1 v2))
      | Neq, v1, v2 when is_value v1 && is_value v2 ->
          Base (Bool (not (eq_ast v1 v2)))
      | Geq, v1, v2 when is_value v1 && is_value v2 ->
          Base (Bool (not (lt_ast v1 v2)))
      | Leq, v1, v2 when is_value v1 && is_value v2 ->
          Base (Bool (not (gt_ast v1 v2)))
      | Gt, v1, v2 when is_value v1 && is_value v2 ->
          Base (Bool (gt_ast v1 v2))
      | Lt, v1, v2 when is_value v1 && is_value v2 ->
          Base (Bool (lt_ast v1 v2))
      | App, UnOp (Fun x, body), arg when is_value arg ->
          constProp (subst body arg x)
      | MatchP (x, y), BinOp (Pair, v1, v2), e2 ->
          let body = subst (subst e2 v1 x) v2 y in
          constProp body
      | Let x, v, body when is_value v -> constProp (subst body v x)
      | LetRec (f, x), e1, e2 ->
          let fun_val = UnOp (RecFun (f, x), constProp e1) in
          constProp (subst e2 fun_val f)
      | _ ->
          (* fallback: propagate inside *)
          BinOp (op, e1', e2'))
  | TrinOp (op, e1, e2, e3) -> (
      let e1' = constProp e1 in
      match (op, e1') with
      | MatchL (_, _), Base Nil -> constProp e2
      | MatchL (x, xs), BinOp (Cons, hd, tl) when is_value hd && is_value tl
        ->
          let body = subst (subst e3 hd x) tl xs in
          constProp body
      | Cond, Base (Bool true) -> constProp e2
      | Cond, Base (Bool false) -> constProp e3
      | _ -> TrinOp (op, e1', constProp e2, constProp e3))
