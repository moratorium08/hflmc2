open Eldarica.Dag
open Hflmc2_syntax

type r = [`Invalid | `Unknown]

type value = 
  | VBool of Fpl.t
  | VFun of Rtype.t Id.t * Rhflz.t * env
and env = value IdMap.t

exception Infeasible

let rid_of_arithid id = 
  Id.({name=id.name; id=id.id; ty=Rtype.RInt(RId(id))})

let disprove unsat_proof hes env top = 
  (* no recursive hes *)
  let hes = Expand.expand unsat_proof hes in
  let fml = (Rhflz.lookup_rule top hes).body in
  Rhflz.print_formula fml;
  (*let eval formula dic = 
    (* evaluator *)
    let open Rhflz in
    let rec f env fml = match fml with
      | Bool x -> VBool(Fpl.Bool(x))
      | Var x -> begin match IdMap.find env x with 
        | Some(x) -> x
        | None -> failwith "evaluation error"
        end
      | Or(p, q, _, _) -> 
        begin
        match f env p, f env q with
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
in*)
  failwith "not implemented"