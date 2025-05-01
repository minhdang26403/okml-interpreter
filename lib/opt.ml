(* opt.ml *)
(* Author: Dang Truong *)

open Exp

let rec is_value (e : ast) : bool =
  match e with
  | Base (Int _) | Base (Bool _) | Base Unit | Base Nil -> true
  | UnOp (Fun _, _) | UnOp (RecFun _, _) -> true
  | BinOp (Cons, e1, e2) | BinOp (Pair, e1, e2) -> is_value e1 && is_value e2
  | _ -> false

let rec eq_ast (e1 : ast) (e2 : ast) : bool =
  match (e1, e2) with
  | Base (Int a1), Base (Int a2) -> a1 = a2
  | Base (Bool b1), Base (Bool b2) -> b1 = b2
  | Base Unit, Base Unit -> true
  | Base Nil, Base Nil -> true
  | BinOp (Cons, h1, t1), BinOp (Cons, h2, t2) ->
      eq_ast h1 h2 && eq_ast t1 t2
  | BinOp (Pair, a1, b1), BinOp (Pair, a2, b2) ->
      eq_ast a1 a2 && eq_ast b1 b2
  | UnOp (Fun _, _), _ | UnOp (RecFun (_, _), _), _ ->
      raise (Invalid_argument "compare: functional value")
  | _ -> assert false

let rec gt_ast (e1 : ast) (e2 : ast) : bool =
  match (e1, e2) with
  | Base (Int a1), Base (Int a2) -> a1 > a2
  | Base (Bool b1), Base (Bool b2) -> b1 > b2
  | Base Unit, Base Unit -> false
  | Base Nil, Base Nil -> false
  | BinOp (Cons, h1, t1), BinOp (Cons, h2, t2) ->
      if gt_ast h1 h2 then true
      else if eq_ast h1 h2 then gt_ast t1 t2
      else false
  | BinOp (Pair, a1, b1), BinOp (Pair, a2, b2) ->
      if gt_ast a1 a2 then true
      else if eq_ast a1 a2 then gt_ast b1 b2
      else false
  | UnOp (Fun _, _), _ | UnOp (RecFun (_, _), _), _ ->
      raise (Invalid_argument "compare: functional value")
  | _ -> assert false

let rec lt_ast (e1 : ast) (e2 : ast) : bool =
  match (e1, e2) with
  | Base (Int a1), Base (Int a2) -> a1 < a2
  | Base (Bool b1), Base (Bool b2) -> b1 < b2
  | Base Unit, Base Unit -> false
  | Base Nil, Base Nil -> false
  | BinOp (Cons, h1, t1), BinOp (Cons, h2, t2) ->
      if lt_ast h1 h2 then true
      else if eq_ast h1 h2 then lt_ast t1 t2
      else false
  | BinOp (Pair, a1, b1), BinOp (Pair, a2, b2) ->
      if lt_ast a1 a2 then true
      else if eq_ast a1 a2 then lt_ast b1 b2
      else false
  | UnOp (Fun _, _), _ | UnOp (RecFun (_, _), _), _ ->
      raise (Invalid_argument "compare: functional value")
  | _ -> assert false

let rec subst (e : ast) (v : ast) (x : string) : ast =
  match e with
  | Base (Var y) -> if x = y then v else e
  | Base _ -> e
  | UnOp (Fun y, body) -> if x = y then e else UnOp (Fun y, subst body v x)
  | UnOp (RecFun (f, y), body) ->
      if x = f || x = y then e else UnOp (RecFun (f, y), subst body v x)
  | UnOp (op, e1) -> UnOp (op, subst e1 v x)
  | BinOp (Let y, e1, e2) ->
      let e1' = subst e1 v x in
      let e2' = if x = y then e2 else subst e2 v x in
      BinOp (Let y, e1', e2')
  | BinOp (LetRec (f, y), e1, e2) ->
      let e1' = if x = f || x = y then e1 else subst e1 v x in
      let e2' = if x = f then e2 else subst e2 v x in
      BinOp (LetRec (f, y), e1', e2')
  | BinOp (MatchP (a, b), e1, e2) ->
      let e1' = subst e1 v x in
      let e2' = if x = a || x = b then e2 else subst e2 v x in
      BinOp (MatchP (a, b), e1', e2')
  | BinOp (op, e1, e2) -> BinOp (op, subst e1 v x, subst e2 v x)
  | TrinOp (MatchL (hd, tl), e1, e2, e3) ->
      let e1' = subst e1 v x in
      let e2' = subst e2 v x in
      let e3' = if x = hd || x = tl then e3 else subst e3 v x in
      TrinOp (MatchL (hd, tl), e1', e2', e3')
  | TrinOp (Cond, e1, e2, e3) ->
      TrinOp (Cond, subst e1 v x, subst e2 v x, subst e3 v x)

let rec constProp (e : ast) : ast =
  match e with
  | Base _ -> e (* Constants and variables are unchanged *)
  | UnOp (op, e1) -> (
      let e1' = constProp e1 in
      match (op, e1') with
      | Not, Base (Bool b) -> Base (Bool (not b))
      | Neg, Base (Int n) -> Base (Int (-n))
      | _ ->
          (* keep original if not a constant *)
          UnOp (op, e1'))
  | BinOp (op, e1, e2) -> (
      let e1' = constProp e1 in
      let e2' = constProp e2 in
      match (op, e1', e2') with
      | Add, Base (Int a), Base (Int b) -> Base (Int (a + b))
      | Sub, Base (Int a), Base (Int b) -> Base (Int (a - b))
      | Mul, Base (Int a), Base (Int b) -> Base (Int (a * b))
      | Div, Base _, Base (Int 0) -> BinOp (Div, e1', e2')
      | Div, Base (Int a), Base (Int b) -> Base (Int (a / b))
      | (Eq | Neq | Gt | Lt | Geq | Leq), UnOp (Fun _, _), _
      | (Eq | Neq | Gt | Lt | Geq | Leq), UnOp (RecFun _, _), _ ->
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
      | And, Base (Bool false), _ -> Base (Bool false)
      | And, Base (Bool true), e -> e
      | Or, Base (Bool true), _ -> Base (Bool true)
      | Or, Base (Bool false), e -> e
      | Let x, v, body when is_value v -> constProp (subst body v x)
      | Pair, a, b when is_value a && is_value b ->
          (* it's already a value *)
          BinOp (Pair, a, b)
      | Cons, a, b when is_value a && is_value b -> BinOp (Cons, a, b)
      | App, UnOp (Fun x, body), v when is_value v ->
          constProp (subst body v x)
      | _, _, _ ->
          (* fallback: propagate inside *)
          BinOp (op, e1', e2'))
  | TrinOp (Cond, e1, e2, e3) -> (
      let e1' = constProp e1 in
      match e1' with
      | Base (Bool true) -> constProp e2
      | Base (Bool false) -> constProp e3
      | _ -> TrinOp (Cond, e1', constProp e2, constProp e3))
  | TrinOp (MatchL (x, xs), e1, e2, e3) -> (
      let e1' = constProp e1 in
      match e1' with
      | Base Nil -> constProp e2
      | BinOp (Cons, hd, tl) when is_value hd && is_value tl ->
          let body = subst (subst e3 hd x) tl xs in
          constProp body
      | _ -> TrinOp (MatchL (x, xs), e1', constProp e2, constProp e3))
