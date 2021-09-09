(* The definitions of Call by Push Value terms *)
open Base

type 'a cbpv_variant = (string, 'a cbpv_tm, String.comparator_witness) Map.t

(* Core Language *)
and 'a val_tm = 'a cbpv_tm
and 'a comp_tm = 'a cbpv_tm
and 'a cbpv_tm =
  (* Value *)
  | Var of string
  | Int of int
  | Bool of bool
  | Lit of string
  | Thunk of 'a comp_tm
  | InL of 'a val_tm
  | InR of 'a val_tm
  | Variant of 'a cbpv_variant
  (* Computation *)
  | Fun of string * 'a comp_tm
  | RecFun of string * 'a comp_tm
  | App of 'a comp_tm * 'a val_tm
  | Return of 'a val_tm 
  | Op of string
  | Force of 'a val_tm
  | Match of 'a val_tm * string * ('a comp_tm) list
  | To of string * 'a comp_tm * 'a comp_tm

type 'a cbpv_env = (string, 'a value, String.comparator_witness) Map.t
and 'a value =
  | VInt of int
  | VBool of bool
  | VClos of 'a cbpv_env * string * 'a cbpv_tm
  | VRecClos of 'a cbpv_env * string * 'a cbpv_tm
  | VLit of string
  | VThunk of 'a cbpv_env * 'a cbpv_tm
  | VReturn of 'a value
 
let rec eval env = function
  | Var x -> Map.find_exn env x
  | Int i -> VInt i
  | Bool b -> VBool b
  | Lit l -> VLit l
  | Thunk e -> VThunk (env, e)
  | InL _ -> assert false
  | InR _ -> assert false
  | Variant _ -> assert false
  | Fun (x, f) -> VClos (env, x, f) 
  | RecFun (x, f) -> VRecClos (env, x, f)
  | App (Op _, _) -> assert false
  | App (e1, e2) -> begin
      let v2 = eval env e2 in
      match eval env e1 with
      | VClos (env', x, f) -> eval (Map.set env' ~key:x ~data:v2) f
      |  _ -> assert false 
    end
  | Return e -> VReturn e
  | Force e -> begin
      match eval env e with
      | VThunk (env', e) -> eval env' e
      | _ -> assert false
    end
  | Match (m, x, l) -> begin
      let v = eval env m in
      let env' = Map.set env ~key:x ~data:v in
      match v with
      | VBool true -> List.nth_exn l 0 |> eval env'
      | VBool false -> List.nth_exn l 0 |> eval env'
      | _ -> assert false
    end
  | To (x, e1, e2) -> begin 
     match eval env e1 with 
     | VReturn v1 -> eval (Map.set env ~key:x ~data:v1) e2
     | _ -> assert false
    end
  | _ -> assert false
