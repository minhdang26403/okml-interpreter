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

let step_unOp op e =
  match (op, e) with
  | Not, Bool b -> Bool (not b)
  | Neg, Int x -> Int (-x)
  | _ -> failwith "Not implemented"

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
  | BinOp (Pair, a1, b1), BinOp (Pair, a2, b2) -> eq_ast a1 a2 && eq_ast b1 b2
  | BinOp (Cons, h1, t1), BinOp (Cons, h2, t2) -> eq_ast h1 h2 && eq_ast t1 t2
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

let step_binOp op e1 e2 =
  match (op, e1, e2) with
  (* arithmetic operations *)
  | Add, Base (Int a), Base (Int b) -> Int (a + b)
  | Sub, Base (Int a), Base (Int b) -> Int (a - b)
  | Mul, Base (Int a), Base (Int b) -> Int (a * b)
  | Div, Base (Int _), Base (Int 0) -> raise Division_by_zero
  | Div, Base (Int a), Base (Int b) -> Int (a / b)
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
        | Eq -> Bool (eq_ast e1 e2)
        | Neq -> Bool (not (eq_ast e1 e2))
        | Geq -> Bool (not (lt_ast e1 e2))
        | Leq -> Bool (not (gt_ast e1 e2))
        | Gt -> Bool (gt_ast e1 e2)
        | Lt -> Bool (lt_ast e1 e2)
        | _ -> failwith "Unreachable")
  | _ -> failwith "Operator and operand type mismatch"

let rec step (e : ast) : ast option =
  match e with
  | Base (Var _) | Base (Int _) | Base (Bool _) | Base Unit | Base Nil -> None
  (* logical negation *)
  | UnOp (Not, e) -> (
      match step e with
      (* e is already a value *)
      | None -> (
          match e with
          | Base (Bool b) -> Some (Base (Bool (not b)))
          | _ -> failwith "Operator and operand type mismatch")
      (* e is not a value yet *)
      | Some e' -> Some (UnOp (Not, e')))
  (* numerical negation *)
  | UnOp (Neg, e) -> (
      match step e with
      (* e is already a value *)
      | None -> (
          match e with
          | Base (Int x) -> Some (Base (Int (-x)))
          | _ -> failwith "Operator and operand type mismatch")
      (* e is not a value yet *)
      | Some e' -> Some (UnOp (Neg, e')))
  (* functions are values *)
  | UnOp (Fun _, _) | UnOp (RecFun (_, _), _) -> None
  (* logical operators are short-circuited *)
  | BinOp (And, e1, e2) -> (
      match step e1 with
      | Some e1' -> Some (BinOp (And, e1', e2))
      | None -> (
          match step e2 with
          | Some e2' -> Some (BinOp (And, e1, e2'))
          | None -> Some (Base (step_binOp And e1 e2))))
  | BinOp (Or, e1, e2) -> (
      match step e1 with
      | Some e1' -> Some (BinOp (Or, e1', e2))
      | None -> (
          match step e2 with
          | Some e2' -> Some (BinOp (Or, e1, e2'))
          | None -> Some (Base (step_binOp Or e1 e2))))
  (* other binary operations are evaluated right-to-left *)
  | BinOp (op, e1, e2) ->
      if not (is_value e2) then
        match step e2 with
        | Some e2' -> Some (BinOp (op, e1, e2'))
        | None -> None
      else if not (is_value e1) then
        match step e1 with
        | Some e1' -> Some (BinOp (op, e1', e2))
        | None -> None
      else Some (Base (step_binOp op e1 e2))
  | _ -> failwith "Not implemented"

let rec eval (e : ast) : ast =
  match step e with None -> e | Some e' -> eval e'
