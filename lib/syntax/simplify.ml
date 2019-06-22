open Hflmc2_util

let rec is_true : Hfl.t -> bool =
  fun phi -> match phi with
  | Bool b -> b
  | And(phis, _) -> List.for_all ~f:is_true phis
  | Or (phis, _) -> List.exists  ~f:is_true phis
  | _ -> false
let rec is_false : Hfl.t -> bool =
  fun phi -> match phi with
  | Bool b -> not b
  | And(phis, _) -> List.exists  ~f:is_false phis
  | Or (phis, _) -> List.for_all ~f:is_false phis
  | _ -> false

let rec hfl : ?force:bool -> Hfl.t -> Hfl.t =
  fun ?(force=false) phi ->
    match Subst.Hfl.reduce phi with
    | And(phis, k) when k = `Inserted || force ->
        let phis = List.map ~f:hfl phis in
        let phis = List.filter ~f:Fn.(not <<< is_true) phis in
        begin if List.exists ~f:is_false phis then
          Bool false
        else match phis with
          | []    -> Bool true
          | [phi] -> phi
          | _     -> And(phis, k)
        end
    | Or(phis, k) when k = `Inserted || force ->
        let phis = List.map ~f:hfl phis in
        let phis = List.filter ~f:Fn.(not <<< is_false) phis in
        begin if List.exists ~f:is_true phis then
          Bool true
        else match phis with
          | []    -> Bool false
          | [phi] -> phi
          | _     -> Or(phis, k)
        end
    | And(phis, k) -> And(List.map ~f:hfl phis, k) (* preserve the structure *)
    | Or (phis, k) -> Or (List.map ~f:hfl phis, k) (* preserve the structure *)
    | Exists(l,phi)  -> Exists(l, hfl ~force phi)
    | Forall(l,phi)  -> Forall(l, hfl ~force phi)
    | Abs(x,phi)     -> Abs(x, hfl ~force phi)
    | App(phi1,phi2) -> App(hfl ~force phi1, hfl ~force phi2)
    | phi -> phi

