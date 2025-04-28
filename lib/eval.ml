(* eval.ml *)
(* Author: Dang Truong *)

open Exp

let rec is_value (e : ast) : bool =
  match e with
  (* literals *)
  | Base (Int _) -> true
  | Base (Bool _) -> true
  | Base Unit -> true
  | Base Nil -> true
  (* functions are values *)
  | UnOp (Fun _, _) -> true
  | UnOp (RecFun _, _) -> true
  (* structured compound values *)
  | BinOp (Pair, e1, e2) -> is_value e1 && is_value e2
  | BinOp (Cons, e1, e2) -> is_value e1 && is_value e2
  | _ -> false

let is_fun e =
  match e with
  | UnOp (Fun _, _) -> true
  | UnOp (RecFun (_, _), _) -> true
  | _ -> false

let rec eq_ast e1 e2 =
  match (e1, e2) with
  | Base (Int a1), Base (Int a2) -> a1 = a2
  | Base (Bool b1), Base (Bool b2) -> b1 = b2
  | Base Unit, Base Unit -> true
  | Base Nil, Base Nil -> true
  | BinOp (Pair, a1, b1), BinOp (Pair, a2, b2) ->
      eq_ast a1 a2 && eq_ast b1 b2
  | BinOp (Cons, h1, t1), BinOp (Cons, h2, t2) ->
      eq_ast h1 h2 && eq_ast t1 t2
  | _ -> failwith "eq_ast: cannot compare these values"

let rec gt_ast e1 e2 =
  match (e1, e2) with
  | Base (Int a1), Base (Int a2) -> a1 > a2
  | Base (Bool b1), Base (Bool b2) -> b1 > b2
  | Base Unit, Base Unit -> false
  | Base Nil, Base Nil -> false
  | BinOp (Pair, a1, b1), BinOp (Pair, a2, b2) ->
      if gt_ast a1 a2 then true
      else if eq_ast a1 a2 then gt_ast b1 b2
      else false
  | BinOp (Cons, h1, t1), BinOp (Cons, h2, t2) ->
      if gt_ast h1 h2 then true
      else if eq_ast h1 h2 then gt_ast t1 t2
      else false
  | _ -> failwith "gt_ast: cannot compare these values"

let rec lt_ast e1 e2 =
  match (e1, e2) with
  | Base (Int a1), Base (Int a2) -> a1 < a2
  | Base (Bool b1), Base (Bool b2) -> b1 < b2
  | Base Unit, Base Unit -> false
  | Base Nil, Base Nil -> false
  | BinOp (Pair, a1, b1), BinOp (Pair, a2, b2) ->
      if lt_ast a1 a2 then true
      else if eq_ast a1 a2 then lt_ast b1 b2
      else false
  | BinOp (Cons, h1, t1), BinOp (Cons, h2, t2) ->
      if lt_ast h1 h2 then true
      else if eq_ast h1 h2 then lt_ast t1 t2
      else false
  | _ -> failwith "lt_ast: cannot compare these values"

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

let step_binOp op e1 e2 =
  match (op, e1, e2) with
  (* arithmetic operations *)
  | Add, Base (Int a), Base (Int b) -> Base (Int (a + b))
  | Sub, Base (Int a), Base (Int b) -> Base (Int (a - b))
  | Mul, Base (Int a), Base (Int b) -> Base (Int (a * b))
  | Div, Base (Int _), Base (Int 0) -> raise Division_by_zero
  | Div, Base (Int a), Base (Int b) -> Base (Int (a / b))
  (* comparisons *)
  | Eq, e1, e2
  | Neq, e1, e2
  | Geq, e1, e2
  | Leq, e1, e2
  | Gt, e1, e2
  | Lt, e1, e2 -> (
      if is_fun e1 || is_fun e2 then
        (* TODO: we may not need to check both since the typechecker
         * should ensure both operands to be of the same type *)
        raise (Invalid_argument "compare: functional value")
      else
        match op with
        | Eq -> Base (Bool (eq_ast e1 e2))
        | Neq -> Base (Bool (not (eq_ast e1 e2)))
        | Geq -> Base (Bool (not (lt_ast e1 e2)))
        | Leq -> Base (Bool (not (gt_ast e1 e2)))
        | Gt -> Base (Bool (gt_ast e1 e2))
        | Lt -> Base (Bool (lt_ast e1 e2))
        | _ -> failwith "Unreachable")
  (* function application *)
  | App, UnOp (Fun x, e), v -> subst e v x
  | App, UnOp (RecFun (_, x), e), v -> subst e v x
  (* should be unreachable *)
  | _ -> failwith "Operator and operand type mismatch"

let fst (e : ast) : ast =
  match e with BinOp (Pair, v, _) -> v | _ -> failwith "Not a pair"

let snd (e : ast) : ast =
  match e with BinOp (Pair, _, v) -> v | _ -> failwith "Not a pair"

let rec step_helper (e : ast) : ast =
  match e with
  (* cannot step primitive expressions and functions *)
  | Base (Var _)
  | Base (Int _)
  | Base (Bool _)
  | Base Unit
  | Base Nil
  | UnOp (Fun _, _)
  | UnOp (RecFun (_, _), _) ->
      failwith "Unreachable"
  | UnOp (op, e) -> step_unary op e
  | BinOp (And, e1, e2) -> step_and e1 e2
  | BinOp (Or, e1, e2) -> step_or e1 e2
  | BinOp (Cons, e1, e2) -> step_list_cons e1 e2
  | BinOp (Pair, e1, e2) -> step_pair e1 e2
  (* pair matching *)
  | BinOp (MatchP (x, y), e1, e2) ->
      if is_value e1 then
        let e2' = subst e2 (fst e1) x in
        subst e2' (snd e1) y
      else BinOp (MatchP (x, y), step_helper e1, e2)
  (* let binding *)
  | BinOp (Let x, e1, e2) ->
      if is_value e1 then subst e2 e1 x else BinOp (Let x, step_helper e1, e2)
  (* recursive let binding *)
  | BinOp (LetRec (f, x), e1, e2) ->
      if is_value e1 then subst e2 e1 x
      else BinOp (LetRec (f, x), step_helper e1, e2)
  (* arithmetic operations and comparisons *)
  | BinOp (op, e1, e2) ->
      (* always evaluate left-to-right *)
      if is_value e1 && is_value e2 then step_binOp op e1 e2
      else if is_value e1 then BinOp (op, e1, step_helper e2)
      else BinOp (op, step_helper e1, e2)
  | TrinOp (Cond, e1, e2, e3) -> step_conditional_branching e1 e2 e3
  | TrinOp (op, e1, e2, e3) -> step_list_matching op e1 e2 e3

and step_unary (op : unOp) (e : ast) : ast =
  if is_value e then
    match (op, e) with
    | Not, Base (Bool b) -> Base (Bool (not b))
    | Neg, Base (Int x) -> Base (Int (-x))
    | _ -> failwith "Unreachable"
  else UnOp (op, step_helper e)

and step_and (e1 : ast) (e2 : ast) : ast =
  match e1 with
  | Base (Bool false) -> Base (Bool false)
  | Base (Bool true) -> BinOp (And, e1, step_helper e2)
  | _ -> failwith "Unreachable"

and step_or (e1 : ast) (e2 : ast) : ast =
  match e1 with
  | Base (Bool true) -> Base (Bool true)
  | Base (Bool false) -> BinOp (Or, e1, step_helper e2)
  | _ -> failwith "Unreachable"

and step_list_cons (e1 : ast) (e2 : ast) : ast =
  if is_value e1 && is_value e2 then failwith "Already a value"
  else if is_value e2 then BinOp (Cons, step_helper e1, e2)
  else BinOp (Cons, e1, step_helper e2)

and step_pair (e1 : ast) (e2 : ast) : ast =
  if is_value e1 && is_value e2 then failwith "Already a value"
  else if is_value e2 then BinOp (Pair, step_helper e1, e2)
  else BinOp (Pair, e1, step_helper e2)

and step_list_matching (op : trinOp) (e1 : ast) (e2 : ast) (e3 : ast) : ast =
  if is_value e1 then
    match (op, e1) with
    | _, Base Nil -> e2
    | MatchL (x, xs), BinOp (Cons, hd, tl) ->
        let e3' = subst e3 hd x in
        subst e3' tl xs
    | _ -> failwith "Unreachable"
  else TrinOp (op, step_helper e1, e2, e3)

and step_conditional_branching (e1 : ast) (e2 : ast) (e3 : ast) : ast =
  match e1 with
  | Base (Bool true) -> e2
  | Base (Bool false) -> e3
  | _ -> TrinOp (Cond, step_helper e1, e2, e3)

let rec step (e : ast) : ast option =
  if is_value e then None else Some (step_helper e)

let rec eval (e : ast) : ast =
  match step e with None -> e | Some e' -> eval e'
