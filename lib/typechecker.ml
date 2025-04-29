open Exp  
open Type  

(* 
 * val unify : (Type.ty * Type.ty) list -> (int * Type.ty) list option 
 *)

 let rec occur x ty = 
  match ty with 
  | Var y -> x = y
  | Fun(t1, t2) -> occur x t1 || occur x t2
  | Pair(t1, t2) -> occur x t1 || occur x t2
  | List t -> occur x t 
  | _ -> false

(* for i.e: x = 1, rt = Int, ty = Var '1 *)
(* rt: replaced type, usually primitive types already defined in OCaml *)
let rec substitute x rt ty = 
  match ty with 
  | Var y -> If x = y then rt else Var y 
  | Fun(t1, t2) -> Fun(substitute x rt t1, substitute x rt t2)
  | Pair(t1,t2) -> Pair(substitute x rt t1, substitute x rt t2)
  | List t -> List (substitute x rt t)
  | _ -> ty 

let mapSubstitution x rt lst = 
  List.map (fun(a,b) -> (substitute x rt a, substitute x rt b)) lst

(* Ref: https://cs3110.github.io/textbook/chapters/interp/inference.html*)

(* For i.e: 
 * Input: lst = [ (Var 1, Int); (Var 2, Var 1); (Fun(Var 2, Bool), Fun(Int, Var 3)) ]
 * Output: Some ([ (1, Int); (2, Int); (3, Bool) ])
 *)
let rec unify(lst : (ty * ty) list) : (int * ty) list option = 
  match lst with 
  | [] -> Some []
  | (t1,t2) :: xs -> 
    if t1 = t2 then unify(xs) else 
      match (t1,t2) with 
      | (Var x, t) | (t, Var x) -> 
        if occur x t then None 
        else 
          let ys = mapSubstitution x t xs in 
          (match unify ys with 
          | None -> None 
          | Some subst -> Some((x,t) :: subst))
      | (Fun(a1, b1), Fun(a2,b2)) | (Pair(a1, b1), Pair(a2, b2)) -> unify((a1,a2) :: (b1,b2) :: xs)
      | (List t1, List t2) -> unify((t1, t2) :: xs)
      | _ -> None

let counter = ref 0

let fresh () =
  let v = !counter in
  let () = counter := v + 1 in
  Var v

type tyenv = (string * ty) list

let rec lookup (env : tyenv) (x : string) : ty option =
  match env with
  | [] -> None
  | (y, t) :: rest -> if x = y then Some t else lookup rest x

(* Ref: https://cs3110.github.io/textbook/chapters/interp/inference.html *)
let rec infer_exp (env : tyenv) (e : ast) : (ty * (ty * ty) list) =
  match e with
  | Base b ->
      (match b with
       | Int _ -> (Int, [])
       | Bool _ -> (Bool, [])
       | Unit -> (Unit, [])
       | Nil -> 
           let t = fresh () in
           (List t, [])
       | Var x ->
           (match lookup env x with
            | Some t -> (t, [])
            | None -> failwith ("unbound variable: " ^ x)))

  | UnOp (u, e1) ->
      let (t1, c1) = infer_exp env e1 in
      (match u with
       | Not -> (Bool, (t1, Bool) :: c1)
       | Neg -> (Int, (t1, Int) :: c1)
       | Fun x ->
           let tx = fresh () in
           let (t_body, c_body) = infer_exp ((x, tx) :: env) e1 in
           (Fun (tx, t_body), c1 @ c_body)
       | RecFun (f, x) ->
           let tx = fresh () in
           let ty = fresh () in
           let tf = Fun (tx, ty) in
           let env' = (f, tf) :: (x, tx) :: env in
           let (t_body, c_body) = infer_exp env' e1 in
           (tf, (ty, t_body) :: (c1 @ c_body)))

  | BinOp (b, e1, e2) ->
      let (t1, c1) = infer_exp env e1 in
      let (t2, c2) = infer_exp env e2 in
      (match b with
       | Add | Sub | Mul | Div -> (Int, (t1, Int) :: (t2, Int) :: (c1 @ c2))
       | Eq | Neq | Geq | Leq | Gt | Lt -> (Bool, (t1, Int) :: (t2, Int) :: (c1 @ c2))
       | And | Or -> (Bool, (t1, Bool) :: (t2, Bool) :: (c1 @ c2))
       | App ->
           let t_ret = fresh () in
           (t_ret, (t1, Fun (t2, t_ret)) :: (c1 @ c2))
       | Cons ->
           (List t1, (t2, List t1) :: (c1 @ c2))
       | Pair ->
           (Pair (t1, t2), c1 @ c2)
       | MatchP (x, y) ->
           let t_left = fresh () in
           let t_right = fresh () in
           let env' = (x, t_left) :: (y, t_right) :: env in
           let (t_body, c_body) = infer_exp env' e2 in
           (t_body, (t1, Pair (t_left, t_right)) :: (c1 @ c2 @ c_body))
       | Let x ->
           let env' = (x, t1) :: env in
           infer_exp env' e2
       | LetRec (f, x) ->
           let tx = fresh () in
           let ty = fresh () in
           let tf = Fun (tx, ty) in
           let env' = (f, tf) :: (x, tx) :: env in
           let (t_body, c_body) = infer_exp env' e2 in
           (t_body, (t1, tf) :: (c1 @ c2 @ c_body)))

  | TrinOp (t, e1, e2, e3) ->
      let (t1, c1) = infer_exp env e1 in
      let (t2, c2) = infer_exp env e2 in
      let (t3, c3) = infer_exp env e3 in
      (match t with
       | MatchL (x, xs) ->
           let elem_ty = fresh () in
           let env' = (x, elem_ty) :: (xs, List elem_ty) :: env in
           let (t_cons, c_cons) = infer_exp env' e3 in
           (t2, (t1, List elem_ty) :: (t2, t_cons) :: (c1 @ c2 @ c3 @ c_cons))
       | Cond ->
           (t2, (t1, Bool) :: (t2, t3) :: (c1 @ c2 @ c3)))

let infer (e : ast) : (ty * (int * ty) list) option =
  let (t, constraints) = infer_exp [] e in
  match unify constraints with
  | Some subst -> Some (t, subst)
  | None -> None



