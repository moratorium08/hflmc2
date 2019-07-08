open Hflmc2_util

let rec hfl : ?force:bool -> Hfl.t -> Hfl.t =
  let rec is_true : Hfl.t -> bool =
    fun phi -> match phi with
    | Bool b -> b
    | And(phis, _) -> List.for_all ~f:is_true phis
    | Or (phis, _) -> List.exists  ~f:is_true phis
    | _ -> false
  in
  let rec is_false : Hfl.t -> bool =
    fun phi -> match phi with
    | Bool b -> not b
    | And(phis, _) -> List.exists  ~f:is_false phis
    | Or (phis, _) -> List.for_all ~f:is_false phis
    | _ -> false
  in
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

let rec formula : 'bvar 'avar. ('bvar, 'avar) Formula.gen_t -> ('bvar, 'avar) Formula.gen_t =
  let rec is_true =
    fun phi -> match phi with
    | Formula.Bool b -> b
    | Formula.And phis -> List.for_all ~f:is_true phis
    | Formula.Or  phis -> List.exists  ~f:is_true phis
    | _ -> false
  in
  let rec is_false =
    fun phi -> match phi with
    | Formula.Bool b -> not b
    | Formula.And phis -> List.exists  ~f:is_false phis
    | Formula.Or  phis -> List.for_all ~f:is_false phis
    | _ -> false
  in
  function
  | Formula.And phis ->
      let phis = List.map ~f:formula phis in
      let phis = List.filter ~f:Fn.(not <<< is_true) phis in
      begin if List.exists ~f:is_false phis then
        Bool false
      else match phis with
        | []    -> Bool true
        | [phi] -> phi
        | _     -> And phis
      end
  | Formula.Or phis ->
      let phis = List.map ~f:formula phis in
      let phis = List.filter ~f:Fn.(not <<< is_false) phis in
      begin if List.exists ~f:is_true phis then
        Bool true
      else match phis with
        | []    -> Bool false
        | [phi] -> phi
        | _     -> Or phis
      end
  | phi -> phi

