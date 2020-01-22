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
and env = value M.t

exception Infeasible

let eval formula dic = 
  (* evaluator *)
  let open Rhflz in
  let rec f fml env = match fml with
    | Bool x -> VBool(x)
    | Var x -> M.find x.name env
    | Or(p, q) -> 
      begin
      match f p env, f q env with
        | VBool(false), VBool(false) -> VBool(false)
        | _ -> raise Infeasible
      end
    | Abs(id, e) -> VFun(id, e, env)
    | App(e1, e2) -> 
      let v1 = f e1 env in
      begin
      match v1 with
      | VFun(id, e, env) -> 
        let v2 = f e2 env in
        f e (M.add id.name v2 env)
      | _ -> failwith "runtime error(Disprove.eval)"
      end
    | And(p, q) -> failwith "uo"
    | Forall(x, y) -> failwith "uo"
  in failwith "hoge"