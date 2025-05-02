open Exp

let rec is_value (e : ast) : bool =
  match e with
  | Base (Int _ | Bool _ | Unit | Nil) -> true
  | UnOp (Fun _, _) | UnOp (RecFun _, _) -> true
  | BinOp (Cons, e1, e2) | BinOp (Pair, e1, e2) -> is_value e1 && is_value e2
  | _ -> false

(*
 * eq_ast : ast -> ast -> bool
 * REQUIRES: e1 and e2 are values
 * ENSURES: true if [e1 = e2], false otherwise
 *)
let rec eq_ast (e1 : ast) (e2 : ast) : bool =
  match (e1, e2) with
  | Base v1, Base v2 -> v1 = v2
  | BinOp (Cons, h1, t1), BinOp (Cons, h2, t2) ->
      eq_ast h1 h2 && eq_ast t1 t2
  | BinOp (Pair, a1, b1), BinOp (Pair, a2, b2) ->
      eq_ast a1 a2 && eq_ast b1 b2
  | UnOp (Fun _, _), _ | UnOp (RecFun (_, _), _), _ ->
      raise (Invalid_argument "compare: functional value")
  | _ -> assert false

(*
 * gt_ast : ast -> ast -> bool
 * REQUIRES: e1 and e2 are values
 * ENSURES: true if [e1 > e2], false otherwise
 *)
let rec gt_ast (e1 : ast) (e2 : ast) : bool =
  match (e1, e2) with
  | Base v1, Base v2 -> v1 > v2
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

(*
 * lt_ast : ast -> ast -> bool
 * REQUIRES: e1 and e2 are values
 * ENSURES: true if [e1 < e2], false otherwise
 *)
let rec lt_ast (e1 : ast) (e2 : ast) : bool =
  match (e1, e2) with
  | Base v1, Base v2 -> v1 < v2
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
  | BinOp (MatchP (a, b), e1, e2) ->
      let e1' = subst e1 v x in
      let e2' = if x = a || x = b then e2 else subst e2 v x in
      BinOp (MatchP (a, b), e1', e2')
  | BinOp (Let y, e1, e2) ->
      let e1' = subst e1 v x in
      let e2' = if x = y then e2 else subst e2 v x in
      BinOp (Let y, e1', e2')
  | BinOp (LetRec (f, y), e1, e2) ->
      let e1' = if x = f || x = y then e1 else subst e1 v x in
      let e2' = if x = f then e2 else subst e2 v x in
      BinOp (LetRec (f, y), e1', e2')
  | BinOp (op, e1, e2) -> BinOp (op, subst e1 v x, subst e2 v x)
  | TrinOp (MatchL (hd, tl), e1, e2, e3) ->
      let e1' = subst e1 v x in
      let e2' = subst e2 v x in
      let e3' = if x = hd || x = tl then e3 else subst e3 v x in
      TrinOp (MatchL (hd, tl), e1', e2', e3')
  | TrinOp (Cond, e1, e2, e3) ->
      TrinOp (Cond, subst e1 v x, subst e2 v x, subst e3 v x)
