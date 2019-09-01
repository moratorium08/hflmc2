open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type

type t =
  | Var      of [ `I of TraceVar.t | `T of simple_ty Id.t ]
  | Bool     of bool
  | Or       of t list
  | And      of t list
  | Exists   of string * t
  | Forall   of string * t
  | Abs      of simple_argty Id.t * t
  | App      of t * t
  | Arith    of HornClause.arith
  | Pred     of Formula.pred *  HornClause.arith list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let pp_hum : t Print.t =
  let module P = Print in
  let rec hflz_ : P.Prec.t -> t Print.t =
    fun prec ppf phi -> match phi with
      | Bool true  -> Fmt.string ppf "true"
      | Bool false -> Fmt.string ppf "false"
      | Var (`I x)      -> TraceVar.pp_hum ppf x
      | Var (`T x)      -> Print.id ppf x
      | Or phis  ->
          let sep ppf () = Fmt.pf ppf "@ || " in
          P.show_paren (prec > P.Prec.or_) ppf "@[<hv 0>%a@]"
            (P.list ~sep (hflz_ P.Prec.or_)) phis
      | And phis  ->
          let sep ppf () = Fmt.pf ppf "@ && " in
          P.show_paren (prec > P.Prec.or_) ppf "@[<hv 0>%a@]"
            (P.list ~sep (hflz_ P.Prec.and_)) phis
      | Exists (l, psi) ->
          P.show_paren (prec > P.Prec.app) ppf "@[<1><%s>%a@]"
            l
            (hflz_ P.Prec.(succ app)) psi
      | Forall (l, psi) ->
          P.show_paren (prec > P.Prec.app) ppf "@[<1>[%s]%a@]"
            l
            (hflz_ P.Prec.(succ app)) psi
      | App (psi1, psi2) ->
          P.show_paren (prec > P.Prec.app) ppf "@[<1>%a@ %a@]"
            (hflz_ P.Prec.app) psi1
            (hflz_ P.Prec.(succ app)) psi2
      | Abs (x, psi) ->
          P.show_paren (prec > P.Prec.abs) ppf "@[<1>λ%a.@,%a@]"
            Print.id x
            (hflz_ P.Prec.abs) psi
      | Arith a ->
          HornClause.pp_hum_arith_ prec ppf a
      | Pred (pred, as') ->
          P.show_paren (prec > P.Prec.eq) ppf "%a"
            HornClause.pp_hum_formula (Formula.Pred(pred, as'))
  in hflz_ P.Prec.zero

let mk_bool b = Bool b

let mk_var x =
  match TraceVar.type_of x with
  | TyInt -> Arith (Var (`I x))
  | _     -> Var (`I x)

let mk_ands = function
  | [] -> Bool true
  | [x] -> x
  | xs -> And xs

let mk_ors = function
  | [] -> Bool false
  | [x] -> x
  | xs -> Or xs

let mk_pred pred a1 a2 = Pred(pred, [a1;a2])

let mk_forall l t = Forall(l,t)
let mk_exists l t = Exists(l,t)

let mk_arith a = Arith a

let mk_app t1 t2 = App(t1,t2)
let mk_apps t ts = List.fold_left ts ~init:t ~f:mk_app

let rec decompose_app = function
  | App(phi1, phi2) ->
      let (a, args) = decompose_app phi1 in
      a, args @ [phi2]
  | phi -> phi, []

module Make = struct
  type env = TraceVar.t IdMap.t
  let rec arith : env -> Arith.t -> HornClause.arith_var Arith.gen_t =
    fun subst a -> match a with
      | Var v ->
          begin match IdMap.lookup subst v with
          | v           -> Var (`I v)
          | exception _ -> Var (`E (Id.remove_ty v))
          (* | exception Not_found -> *)
          (*     print_endline @@ Print.strf "%s" (Id.to_string v); *)
          (*     assert false *)
          end
      | Int n -> Int n
      | Op (op, as') -> Op (op, List.map as' ~f:(arith subst))

  let rec hflz : simple_ty Hflz.hes -> env -> simple_ty Hflz.t -> t =
    fun hes subst phi -> match phi with
      | Var v ->
          begin match List.find hes ~f:(fun r -> Id.eq r.var v) with
          | Some _ -> (* NT *)
              Var (`I (TraceVar.mk_nt v))
          | None -> (* NT じゃない*)
              begin match IdMap.lookup subst v with
              | tv -> assert (TraceVar.type_of tv <> TyInt); Var (`I tv)
              | exception _ -> Var (`T v)
              end
          end
      | Bool b           -> Bool b
      | Or phis          -> Or (List.map phis ~f:(hflz hes subst))
      | And phis         -> And (List.map phis ~f:(hflz hes subst))
      | Exists (l, phi)  -> Exists (l, hflz hes subst phi)
      | Forall (l, phi)  -> Forall (l, hflz hes subst phi)
      | Arith a          -> Arith (arith subst a)
      | Pred (op, as')   -> Pred (op, List.map as' ~f:(arith subst))
      | App (phi1, phi2) -> App (hflz hes subst phi1, hflz hes subst phi2)
      | Abs (x, phi)     -> Abs (x, hflz hes subst phi)
end

let rec beta_head_arith
          : simple_argty Id.t
         -> t
         -> HornClause.arith
         -> HornClause.arith =
  fun x e a -> match a with
    | Var (`E v) ->
        begin match Id.eq x v, e with
        | true, (Arith a') -> a'
        | true,  _ -> assert false
        | false, _ -> a
        end
    | Var (`I v)   -> Var (`I v)
    | Int n        -> Int n
    | Op (op, as') -> Op (op, List.map as' ~f:(beta_head_arith x e))

let rec beta_head : simple_argty Id.t -> t -> t -> t =
  fun x e phi -> match phi with
    | Var (`T x') when Id.eq x x' -> e
    | Var _            -> phi
    | Bool _           -> phi
    | Or phis          -> Or (List.map phis ~f:(beta_head x e))
    | And phis         -> And (List.map phis ~f:(beta_head x e))
    | Exists (l, phi)  -> Exists (l, beta_head x e phi)
    | Forall (l, phi)  -> Forall (l, beta_head x e phi)
    | Arith a          -> Arith (beta_head_arith x e a)
    | Pred (op, as')   -> Pred (op, List.map as' ~f:(beta_head_arith x e))
    | App (phi1, phi2) -> App (beta_head x e phi1, beta_head x e phi2)
    | Abs (x', phi)    ->
        if (Id.eq x x')
        then Abs (x', phi)
        else Abs (x', beta_head x e phi)

let rec subst_arith : t TraceVar.Map.t -> HornClause.arith -> HornClause.arith =
  fun env a -> match a with
    (* | Var v -> *)
    | Var (`I v) ->
        begin match TraceVar.Map.find env v with
        | Some (Arith a') -> a'
        | Some _ -> assert false
        | None -> a
        end
    | Var (`E v)   -> Var (`E v)
    | Int n        -> Int n
    | Op (op, as') -> Op (op, List.map as' ~f:(subst_arith env))
let rec subst : t TraceVar.Map.t -> t -> t =
  fun env t -> match t with
    | Var (`I v) ->
        begin match TraceVar.Map.find env v with
        | Some t -> t
        | None   -> t
        end
    | Var (`T v)       -> Var (`T v)
    | Bool b           -> Bool b
    | Or phis          -> Or (List.map phis ~f:(subst env))
    | And phis         -> And (List.map phis ~f:(subst env))
    | Exists (l, phi)  -> Exists (l, subst env phi)
    | Forall (l, phi)  -> Forall (l, subst env phi)
    | Arith a          -> Arith (subst_arith env a)
    | Pred (op, as')   -> Pred (op, List.map as' ~f:(subst_arith env))
    | App (phi1, phi2) -> App (subst env phi1, subst env phi2)
    | Abs (v, phi)     -> Abs (v, subst env phi)
