(* The definitions of Call by Push Value terms *)
open Base
open Core

type addr = int [@@deriving show, sexp]
type env = (string, addr, String.comparator_witness) Map.t

(* Core Language *)
type 'a val_tm = 
  (* Value *)
  | Nil
  | Var of string
  | Num of int
  | Bool of bool
  | Atom of string
  | Thunk of 'a comp_tm
  | Cons of ('a val_tm) * ('a val_tm)
  | PrimOp of ('a val_tm) * ('a val_tm)
and 'a comp_tm =
  (* Computation *)
  | Set of 'a val_tm * 'a comp_tm     (* mutation *)
  | DeRef of 'a val_tm
  | GetRef of 'a val_tm
  | Fun of string * 'a comp_tm
  | RecFun of string * 'a comp_tm
  | App of 'a comp_tm * 'a val_tm
  | Return of 'a val_tm 
  | Force of 'a val_tm
  | Match of 'a val_tm * string list * ('a comp_tm) list
  | To of string * 'a comp_tm * 'a comp_tm
  [@@deriving show, sexp]

type 'a term =
  | Val of 'a val_tm
  | Comp of 'a comp_tm
  [@@deriving show, sexp]

type 'a value =
  | VNil
  | VNum of int
  | VBool of bool
  | VCons of 'a value * 'a value
  | VClos of env * string * 'a comp_tm
  | VRecClos of env * string * 'a comp_tm
  | VAtom of string
  | VThunk of 'a comp_tm
  | VReturn of 'a value

let rec show_value v =
  let open Printf in
  let display_comp_tm = show_comp_tm (fun _ _ -> ()) in 
  match v with
  | VNil -> "nil"
  | VNum i -> string_of_int i
  | VBool true -> "#t"
  | VBool false -> "#f"
  | VCons (v1, v2) -> sprintf "(%s . %s)" (show_value v1) (show_value v2)
  | VClos (_, x, c) -> sprintf "(\\%s. %s)" x (display_comp_tm c)
  | VRecClos (_, x, c) -> sprintf "(\\%s. %s)" x (display_comp_tm c)
  | VAtom x -> sprintf "\"%s\"" x
  | VThunk c -> sprintf "{%s}" (display_comp_tm c)
  | VReturn v -> sprintf "(ret %s)" (show_value v)

type 'a store = (addr, 'a value) Hashtbl.t

let alloca tbl data =
  let key = Hashtbl.length tbl in
  Hashtbl.set tbl ~key ~data;
  key

type 'a konts = ('a kont) list
and 'a kont =
  | KSet of addr
  | KFun of 'a value
  | KRecFun of 'a value
  | KTo of string * 'a comp_tm
 
let rec eval_val context env store konts =
  let open Result.Let_syntax in
  match context with
  | Nil -> return VNil
  | Var x ->
     let%bind addr = Map.find env x |> Result.of_option ~error:"cannot find env" in
     Hashtbl.find store addr |> Result.of_option ~error:"cannot find store"
  | Num i -> return @@ VNum i
  | Bool b -> return @@ VBool b
  | Atom l -> return @@ VAtom l
  | Thunk c -> return @@ VThunk c
  | Cons (hd, tl) ->
     (* We don't need a continuation as it simply maps value representation *)
     let%bind hd' = eval_val hd env store konts in
     let%bind tl' = eval_val tl env store konts in
     return @@ VCons (hd', tl')
  | PrimOp ((PrimOp ((Atom "+"), v1)), v2) ->
     let get_num = function
       | VNum i -> Ok i
       | v -> Error (Printf.sprintf "not a number: %s" @@ show_value v)
     in
     let%bind i1 = eval_val v1 env store konts >>= get_num in
     let%bind i2 = eval_val v2 env store konts >>= get_num in 
     return @@ VNum (i1 + i2)
  | _ -> Error "invalid match"

let list_err = Result.of_option ~error:"list outof index" 
let stack_oob = Result.of_option ~error:"stack out of bound"
let undef_var = Result.of_option ~error:"undefined variable name"

let eval_kont value env store konts =
  match value, konts with
  | _, KSet addr::ks -> Hashtbl.set store ~key:addr ~data:value;
                 Ok (Return Nil, env, store, ks)
  | VClos (env', x, c), KFun v::ks ->
     let addr = alloca store v in
     let env'' = Map.set env' ~key:x ~data:addr in
     Ok (c, env'', store, ks)
  | VRecClos (env', x, c), KFun v::ks ->
     let addr = alloca store v in
     let env'' = Map.set env' ~key:x ~data:addr in
     Ok (c, env'', store, ks)
  | VReturn v, KTo (x, c)::ks ->
     let addr = alloca store v in
     let env' = Map.set env ~key:x ~data:addr in
     Ok (c, env', store, ks)
  | _, _ ->
     Error (Printf.sprintf "cannot apply continuation[%d]: %s"
              (List.length konts) (show_value value))

let eval_comp context env store konts =
  let open Result.Let_syntax in
  match context with
  | Set (v, c) ->
     (match eval_val v env store konts with
      | Ok (VNum i) -> Ok (c, env, store, KSet i :: konts)
      | _ -> Error "incorrect dereference value")
  | DeRef v ->
     (match eval_val v env store konts with
      | Ok (VNum i) ->
         let%bind v' = Hashtbl.find store i |> stack_oob in
         eval_kont v' env store konts
      | _ -> Error "incorrect dereference value")
  | GetRef v ->
     (match v with
      | (Var x) ->
         let%bind i = Map.find env x |> undef_var in
         eval_kont (VNum i) env store konts
      | _ -> Error "not a variable object")
  | Fun (x, c) ->
     let closure = VClos (env, x, c) in
     eval_kont closure env store konts
  | RecFun (x, c) ->
     let closure = VRecClos (env, x, c) in
     eval_kont closure env store konts
  | App (c, v) ->
     let%bind v' = eval_val v env store konts in
     Ok (c, env, store, KFun v' :: konts)
  | Return v ->
     let%bind v' = eval_val v env store konts in
     eval_kont (VReturn v') env store konts
  | Force v -> 
     (match eval_val v env store konts with
      | Ok (VThunk c) -> return (c, env, store, konts)  
      | _ -> Error "expect thunks")
  | Match (v, xlist, clist) ->
     let%bind v' = eval_val v env store konts  in 
     (match v' with
      | VBool true ->
         let%bind c = List.nth clist 0 |> list_err in
         Ok (c, env, store, konts)
      | VBool false ->
         let%bind c = List.nth clist 1 |> list_err in
         Ok (c, env, store, konts)
      | VNil ->
         let%bind c = List.nth clist 0 |> list_err in
         Ok (c, env, store, konts)
      | VCons (v1, v2) ->
         let%bind c = List.nth clist 1 |> list_err in
         let%bind x1 = List.nth xlist 0 |> list_err in
         let%bind x2 = List.nth xlist 1 |> list_err in
         let addr1 = alloca store v1 in
         let addr2 = alloca store v2 in
         let env' = Map.set env ~key:x1 ~data:addr1
                    |> Map.set ~key:x2 ~data:addr2 in
         Ok (c, env', store, konts)
      | _ -> Error "incorrect value")
  | To (x, c1, c2) -> 
     Ok (c1, env, store, KTo (x, c2) :: konts)

let eval_cbpv c =
  let e = Map.empty (module String) in
  let s = Hashtbl.create (module Int) in
  let k = [] in
  match c with
  | Val v -> eval_val v e s k
  | Comp c ->
     let rec eval_cbpv_help c e s k =
       match eval_comp c e s k with
       | Ok (Return v, c', e', []) -> eval_val v c' e' []
       | Ok (c, e, s, k) -> eval_cbpv_help c e s k
       | Error e -> Error e
     in
     eval_cbpv_help c e s k

let%test_unit "example1" =
  let letk x value comp = App (Fun (x, comp), value) in
  let funk x comp = Fun (x, comp) in
  let opk v1 v2 = PrimOp (v1, v2) in
  let comp = letk "x" (Num 3)
               (letk "y" (Thunk
                            (funk "z" (Return
                                         (opk (opk (Atom "+") (Var "x"))
                                            (Var "z")))))
                  (To ("w", letk "v" (Num 7) (App ((Force (Var "y"), (Var "v")))),
                       (Return (opk (opk (Atom "+") (Num 5)) (Var "w")))))) in
  match eval_cbpv (Comp comp) with
  | Ok v -> Printf.printf "%s" @@ show_value v
  | Error e -> Printf.printf "%s" @@ e
