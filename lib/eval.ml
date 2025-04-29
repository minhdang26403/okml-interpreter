(* eval.ml *)
(* Author: Dang Truong *)

open Exp

(*
 * subst : ast -> ast -> string -> ast
 * REQUIRES: [v] is a value
 * ENSURES: [subst e v x] replaces all free occurrences of variable [x] in
 * expression [e] with value [v]. This function avoids variable capture by
 * respecting scoping (e.g., skip substitution when [x] is shadowed)
 *)
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
  | App, UnOp (Fun x, e), v | App, UnOp (RecFun (_, x), e), v -> subst e v x
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
      if is_value e1 then subst e2 e1 x
      else BinOp (LetRec (f, x), step_internal e1, e2)
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
