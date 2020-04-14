open Eldarica.Dag
open Hflmc2_syntax

type r = [`Invalid | `Unknown]

type value = 
  | VBool of Fpl.t
  | VInt of Arith.t
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
  let eval fml = 
    (* evaluator *)
    let open Rhflz in
    let rec f env fml = match fml with
      | Bool x -> VBool(Fpl.Bool(x))
      | Or(p, q, _, _) -> VBool(Fpl.Or(f_bool env p, f_bool env q))
      | And(p, q, _, _) -> VBool(Fpl.And(f_bool env p, f_bool env q))
      | Pred(a, l) -> VBool(Fpl.Pred(a, l))
      | Forall(id, e, _) -> 
        begin
        match id.ty with
        | Rtype.RInt(RId(x)) -> 
          VBool(Fpl.Forall ({id with ty = `Int},
            f_bool (IdMap.add env id @@ VInt(Arith.Var(x))) e))
        | Rtype.RInt(RArith(x)) -> 
          VBool(Fpl.Forall ({id with ty = `Int},
            f_bool (IdMap.add env id @@ VInt(x)) e))
        | Rtype.RArrow(_) -> 
          let g = Rhflz.bottom_hflz id.ty in
          begin
          match g with
          | Abs(id, e) -> f (IdMap.add env id @@ VFun(id, e, env)) e
          | _ -> failwith "evaluation error(bottom)"
          end
        | Rtype.RBool(x) -> f (IdMap.add env id @@ VBool(Fpl.Bool(false))) e
        end
      | Var x -> begin match IdMap.find env x with 
        | Some(x) -> x
        | None -> 
        Printf.printf "\nCurrent Environments\n";
        IdMap.iter_keys ~f:(fun key -> 
          Printf.printf "%s\n" @@ Id.to_string key
        ) env;
        Printf.printf "but not found %s\n" @@ Id.to_string x;
         failwith "evaluation error(var not found)"
        end
      | Arith(a) -> VInt(a)
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
    and f_bool env fml = match f env fml with
      | VBool(x) -> x
      | _ -> failwith "runetime error(Disprove f_bool in eval)"
    in 
    f IdMap.empty fml
  in
  let v = eval fml in
  let b = begin
  match v with
  | VBool(v) -> v
  | _ -> failwith "evaluation error"
  end in
  Printf.printf "\n\n";
  Fpl.print b;
  failwith "not_implemented"