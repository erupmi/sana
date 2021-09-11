(* The definitions of Call by Push Value terms *)
open Base
open Result

type addr = int [@@deriving show, sexp]
type env = (string, addr, String.comparator_witness) Map.t

(* Core Language *)
type 'a val_tm = 
  (* Value *)
  | Nil
  | Var of string
  | Int of int
  | Bool of bool
  | Atom of string
  | Thunk of 'a comp_tm
  | Cons of ('a val_tm) * ('a val_tm)
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
  | Op of string
  [@@deriving show, sexp]

type 'a term =
  | Val of 'a val_tm
  | Comp of 'a comp_tm
  [@@deriving show, sexp]

type 'a value =
  | VNil
  | VInt of int
  | VBool of bool
  | VCons of 'a value * 'a value
  | VClos of env * string * 'a comp_tm
  | VRecClos of env * string * 'a comp_tm
  | VAtom of string
  | VThunk of 'a comp_tm
  | VReturn of 'a value

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
  let open Option.Let_syntax in
  match context with
  | Nil -> return VNil
  | Var x ->
     let%bind addr = Map.find env x in
     Hashtbl.find store addr
  | Int i -> return @@ VInt i
  | Bool b -> return @@ VBool b
  | Atom l -> return @@ VAtom l
  | Thunk c -> return @@ VThunk c
  | Cons (hd, tl) ->
     (* We don't need a continuation as it simply maps value representation *)
     let%bind hd' = eval_val hd env store konts in
     let%bind tl' = eval_val tl env store konts in
     return @@ VCons (hd', tl')

let eval_kont _value _env _store _konts = assert false (* TODO *)

let eval_comp context env store konts =
  let eval_err = Result.of_option ~error:"cannot evaluate" in
  let list_err = Result.of_option ~error:"list outof index" in
  let stack_oob = Result.of_option ~error:"stack out of bound" in
  let undef_var = Result.of_option ~error:"undefined variable name" in
  let open Result.Let_syntax in
  match context with
  | Set (v, c) ->
     (match eval_val v env store konts with
      | Some (VInt i) -> Ok (c, env, store, KSet i :: konts)
      | _ -> Error "incorrect dereference value")
  | DeRef v ->
     (match eval_val v env store konts with
      | Some (VInt i) ->
         let%bind v' = Hashtbl.find store i |> stack_oob in
         eval_kont v' env store konts
      | _ -> Error "incorrect dereference value")
  | GetRef v ->
     (match v with
      | (Var x) ->
         let%bind i = Map.find env x |> undef_var in
         eval_kont (VInt i) env store konts
      | _ -> Error "not a variable object")
  | Fun (x, c) ->
     let closure = VClos (env, x, c) in
     eval_kont closure env store konts
  | RecFun (x, c) ->
     let closure = VRecClos (env, x, c) in
     eval_kont closure env store konts
  | App (c, v) ->
     let%bind v' = eval_val v env store konts |> eval_err in
     Ok (c, env, store, KFun v' :: konts)
  | Return v -> eval_kont (eval_val v) env store konts
  | Force v -> 
     (match eval_val v env store konts with
      | Some (VThunk c) -> return (c, env, store, konts)  
      | _ -> Error "expect thunks")
  | Match (v, xlist, clist) ->
     let%bind v' = eval_val v env store konts |> eval_err in 
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
  | _ ->
     let context_msg = show_comp_tm (fun _ _  -> ()) context in
     Error (String.concat ~sep:" " ["incoreect"; context_msg])
