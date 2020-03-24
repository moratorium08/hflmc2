open Eldarica.Dag
open Hflmc2_syntax

module M = Map.Make(String)

let gen_map nodes = 
  List.fold_left (fun m x -> 
    match M.find_opt x.head m with
    | Some(l) -> M.add x.head (x::l) m
    | None -> M.add x.head [x] m
  ) nodes

type value = 
  | VBool of bool
  | VInt of int
  | VFun of Rtype.t Id.t * Rhflz.t * env
and env = value IdMap.t

exception Infeasible

let rid_of_arithid id = 
  Id.({name=id.name; id=id.id; ty=Rtype.RInt(RId(id))})
let eval formula dic = 
  (* evaluator *)
  let rec e_arith env a = 
    match a with
  | Arith.Int x -> x
  | Arith.Var x -> begin match IdMap.find env (rid_of_arithid x) with 
    | Some(VInt(x)) -> x
    | _ -> failwith "evaluation error"
  end
  | Arith.Op (op, x::xs) -> 
    let i = e_arith env x in
    let is = List.map (e_arith env) xs in
    let f = Arith.op_func op in
    List.fold_left f i is
  | _ -> failwith "evaluation error"
  in
  let open Rhflz in
  let rec f env fml = match fml with
    | Bool x -> VBool(x)
    | Var x -> begin match IdMap.find env x with 
      | Some(x) -> x
      | None -> failwith "evaluation error"
      end
    | Or(p, q, _, _) -> 
      begin
      match f env p , f env q with
        | VBool(false), VBool(false) -> VBool(false)
        | _ -> raise Infeasible
      end
    | Abs(id, e) -> VFun(id, e, env)
    | App(e1, e2, _) -> 
      let v1 = f env e1 in
      begin
      match v1 with
      | VFun(id, e, env) -> 
        let v2 = f env e2 in
        f (IdMap.add env id v2) e
      | _ -> failwith "runtime error(Disprove.eval)"
      end
    | And(p, q, _, _) -> failwith "uo"
    | Forall(x, y, _) -> failwith "uo"
    | Arith(a) -> VInt(e_arith env a)
    | Pred(a, l) -> failwith "uo"
  in failwith "hoge"