
(* TODO 雑 *)
let rec hfl : Hfl.t -> Hfl.t =
  fun phi -> match Subst.Hfl.reduce phi with
    | And(phi1, phi2) -> begin match hfl phi1, hfl phi2 with
        | Bool true, phi2 -> phi2
        | Bool false, _ -> Bool false
        | phi1, Bool true -> phi1
        | _, Bool false -> Bool false
        | phi1, phi2 -> And(phi1, phi2)
        end
    | Or(phi1, phi2) -> begin match hfl phi1, hfl phi2 with
        | Bool false, phi2 -> phi2
        | Bool true, _ -> Bool true
        | phi1, Bool false -> phi1
        | _, Bool true -> Bool true
        | phi1, phi2 -> Or(phi1, phi2)
        end
    | Exists(l,phi) -> Exists(l, hfl phi)
    | Forall(l,phi) -> Forall(l, hfl phi)
    | Fix(x,phi,z) -> Fix(x, hfl phi, z)
    | Abs(x,phi) -> Abs(x, hfl phi)
    | App(phi1,phi2) -> App(phi1, hfl phi2)
    | phi -> phi

