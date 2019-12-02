open Hflmc2_util
open Hflmc2_syntax
open Type
module Options = Hflmc2_options.Abstraction
module FpatInterface = FpatInterface

let log_src = Logs.Src.create ~doc:"Predicate Abstraction" "Abstraction"
module Log = (val Logs.src_log log_src)

type env = abstraction_ty IdMap.t

module FormulaMap = Map.Make'(Formula)
type preds_map = (abstracted_ty Id.t) FormulaMap.t

type gamma =
  { env   : env
  ; preds : preds_map
  ; guard : Formula.t (* for optimization only. always [true] for now *)
  }

let pp_env : env Print.t =
  fun ppf env ->
    let compare_id (x,_) (y,_) = Int.compare x.Id.id y.Id.id in
    let item ppf (f,aty) =
      Print.pf ppf "@[<h>%a : %a@]" Print.id f Print.abstraction_ty aty
    in
    Print.pf ppf "@[<v>%a@]"
      (Print.list item)
      (List.sort ~compare:compare_id @@ IdMap.to_alist env)

let merge_types tys =
  let append_preds ps qs =
    List.remove_duplicates ~equal:FpatInterface.(<=>) @@ (ps@qs)
  in Type.merges append_preds tys

let merge_env : env -> env -> env =
  fun env1 env2 ->
    IdMap.merge env1 env2
      ~f:begin fun ~key:_ -> function
      | `Left l -> Some l
      | `Right r -> Some r
      | `Both (l, r) -> Some (merge_types [l;r])
      end

module Int_base = Int_base
let abstract = Int_base.abstract
