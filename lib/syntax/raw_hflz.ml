open Hflmc2_util
type raw_hflz =
  | Bool   of bool
  | Var    of string
  | Or     of raw_hflz list
  | And    of raw_hflz list
  | Exists of string * raw_hflz
  | Forall of string * raw_hflz
  | Abs    of string * raw_hflz
  | App    of raw_hflz * raw_hflz
  (* constructers only for hflz *)
  | Int    of int
  | Op     of Arith.op * raw_hflz list
  | Pred   of Formula.pred * raw_hflz list
  [@@deriving eq,ord,show,iter,map,fold,sexp]
type hes_rule =
  { var  : string
  ; args : string list
  ; fix  : Fixpoint.t
  ; body : raw_hflz
  }
  [@@deriving eq,ord,show,iter,map,fold,sexp]
type hes = hes_rule list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_int n     = Int(n)
let mk_bool b    = Bool b
let mk_var x     = Var x
let mk_op op as' = Op(op,as')

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

let mk_app t1 t2 = App(t1,t2)
let mk_apps t ts = List.fold_left ts ~init:t ~f:mk_app

let mk_abs x t = Abs(x, t)
let mk_abss xs t = List.fold_right xs ~init:t ~f:mk_abs

let rec decompose_app = function
  | App(phi1, phi2) ->
      let (a, args) = decompose_app phi1 in
      a, args @ [phi2]
  | phi -> phi, []
let rec decompose_abs = function
  | Abs(x, phi) ->
      let (args, body) = decompose_abs phi in
      x::args, body
  | phi -> [], phi

module Typing = struct
  open Type
  exception Error of string
  let error s = raise (Error s)

  type tyvar = (* simple_ty + simple_argty + type variable *)
    | TvRef of int * tyvar option ref
    | TvInt
    | TvBool
    | TvArrow of tyvar * tyvar
    [@@deriving show { with_path = false }]
  type id = int
  let new_id    : unit -> id    = Id.gen_id
  let new_tyvar : unit -> tyvar =
    let counter = new Fn.counter in
    fun () -> TvRef (counter#tick, ref None)

  let rec pp_hum_tyvar : tyvar Print.t =
    fun ppf tv -> match tv with
      | TvInt -> Fmt.string ppf "int"
      | TvBool -> Fmt.string ppf "o"
      | TvRef(id,{contents=None }) ->
          Fmt.pf ppf "tv%d" id
      | TvRef(id,{contents=Some tv}) ->
          Fmt.pf ppf "tv%d@%a" id pp_hum_tyvar tv
      | TvArrow(tv1,tv2) ->
          Fmt.pf ppf "(%a -> %a)"
            pp_hum_tyvar tv1
            pp_hum_tyvar tv2

  let rec occur : tyvar option ref -> tyvar -> bool =
    fun r tv -> match tv with
      | TvInt | TvBool -> false
      | TvArrow(tv1, tv2) -> occur r tv1 || occur r tv2
      | TvRef(_, ({contents=None} as r')) -> r == r'
      | TvRef(_, ({contents=Some tv} as r')) -> r == r' || occur r tv
  let occur_check r tv =
    if occur r tv then begin
      (* Print.pr "r=%a; tv=%a" pp_hum_tyvar (TvRef (-1, r)) pp_hum_tyvar tv; *)
      Fn.fatal "Recursive type is unsupported"
    end

  let rec write : tyvar option ref -> tyvar -> unit =
    fun r tv -> match tv with
      | TvInt | TvBool | TvArrow _ -> r := Some tv
      | TvRef (_, r') ->
          begin match !r' with
          | None -> r := Some tv
          | Some tv' -> write r tv'; write r tv'
          end


  let rec unify : tyvar -> tyvar -> unit =
    fun tv1 tv2 ->
      (* Print.pr "UNIFY %a -- %a@." *)
      (*   pp_hum_tyvar tv1 *)
      (*   pp_hum_tyvar tv2; *)
      match tv1, tv2 with
      | TvInt, TvInt -> ()
      | TvBool, TvBool -> ()
      | TvArrow(tv11,tv12),  TvArrow(tv21,tv22) ->
          unify tv11 tv21; unify tv12 tv22
      | TvRef (_,r1), TvRef (_,r2) when r1 = r2 ->
          (* Print.pr "EQUAL %a == %a@." *)
          (*   pp_hum_tyvar tv1 *)
          (*   pp_hum_tyvar tv2; *)
          if !r1 = None && !r2 = None then begin
            occur_check r1 tv2;
            (* Print.pr "APPLY  %a := %a@." *)
            (*   pp_hum_tyvar tv1 *)
            (*   pp_hum_tyvar tv2; *)
            write r1 tv2
          end;
      | TvRef (_, ({contents = None} as r1)), _ ->
          occur_check r1 tv2;
          (* Print.pr "APPLY %a := %a@." *)
          (*   pp_hum_tyvar tv1 *)
          (*   pp_hum_tyvar tv2; *)
          write r1 tv2
      | _, TvRef (_, ({contents = None} as r2)) ->
          occur_check r2 tv1;
          (* Print.pr "APPLY %a := %a@." *)
          (*   pp_hum_tyvar tv2 *)
          (*   pp_hum_tyvar tv1; *)
          write r2 tv1;
      | TvRef (_, ({contents = Some tv1'} as r1)), _ ->
          occur_check r1 tv2;
          (* Print.pr "APPLY %a := %a@." *)
          (*   pp_hum_tyvar tv1 *)
          (*   pp_hum_tyvar tv2; *)
          write r1 tv2;
          unify tv1' tv2
      | _, TvRef (_, ({contents = Some tv2'} as r2)) ->
          occur_check r2 tv1;
          (* Print.pr "APPLY %a := %a@." *)
          (*   pp_hum_tyvar tv2 *)
          (*   pp_hum_tyvar tv1; *)
          write r2 tv1;
          unify tv1 tv2'
      | _, _ ->
          Fn.fatal @@ Fmt.strf "ill-typed"

  type id_env = int StrMap.t   (* name to id *)
  let pp_id_env : id_env Print.t =
    fun ppf env ->
      let open Print in
      list_comma (pair string int) ppf (StrMap.to_alist env)
  type ty_env = tyvar IntMap.t (* id to tyvar *)

  class add_annot = object (self)
    val mutable global_ints : id_env = StrMap.empty
    val mutable ty_env : ty_env = IntMap.empty

    method get_ty_env : ty_env = ty_env

    method add_ty_env : 'a. 'a Id.t -> tyvar -> unit =
      fun x tv ->
        (* Print.pr "TyENV %s : %a@." (Id.to_string x) pp_hum_tyvar tv; *)
        match IntMap.find ty_env x.id with
        | None -> ty_env <- IntMap.add_exn ty_env ~key:x.id ~data:tv
        | Some tv' -> unify tv tv'

    method arith : id_env -> raw_hflz -> Arith.t =
      fun id_env a -> match a with
        | Int n -> Int n
        | Var name ->
            let x =
              match
                StrMap.find id_env name,
                StrMap.find global_ints name
              with
              | None, None ->
                  let id = Id.gen_id() in
                  global_ints <- StrMap.add_exn global_ints ~key:name ~data:id;
                  Id.{ name; id; ty=`Int }
              | Some id, _ | _, Some id  -> (* the order of match matters! *)
                  Id.{ name; id; ty=`Int }
            in
            self#add_ty_env x TvInt; Arith.mk_var x
        | Op (op, as') -> Op (op, List.map ~f:(self#arith id_env) as')
        | _ -> failwith "annot.arith"

    method term : id_env -> raw_hflz -> tyvar * unit Hflz.t =
      fun id_env psi ->
        (* Print.pr "term %a |- %a@." *)
        (*   pp_id_env id_env *)
        (*   pp_raw_hflz psi; *)
        match psi with
        | Bool b -> TvBool, Bool b
        | Var name ->
            let id,ty =
              match
                StrMap.find id_env name,
                StrMap.find global_ints name
              with
              | Some id, _ ->
                  let ty = new_tyvar() in
                  id, ty
              | _, Some id ->
                  let ty = TvInt in
                  id, ty
              | _, _ ->

                  let id = new_id() in
                  let ty = TvInt in
                  global_ints <- StrMap.add_exn global_ints ~key:name ~data:id;
                  id, ty
            in
            let x = Id.{ name; id; ty=() } in
            self#add_ty_env x ty;
            ty, Hflz.mk_var x
        | Or psis ->
            let tvs, psis = List.unzip @@ List.map psis ~f:(self#term id_env) in
            List.iter tvs ~f:(fun tv -> unify tv TvBool);
            TvBool, Or psis
        | And psis ->
            let tvs, psis = List.unzip @@ List.map psis ~f:(self#term id_env) in
            List.iter tvs ~f:(fun tv -> unify tv TvBool);
            TvBool, And psis
        | Exists (l, psi) ->
            let tv, psi = self#term id_env psi in
            unify tv TvBool;
            TvBool, Exists (l, psi)
        | Forall (l, psi) ->
            let tv, psi = self#term id_env psi in
            unify tv TvBool;
            TvBool, Forall (l, psi)
        | Pred (pred,as') ->
            TvBool, Pred(pred, List.map ~f:(self#arith id_env) as')
        | Int _ | Op _ ->
            TvInt, Arith (self#arith id_env psi)
        | Abs(name, psi) ->
            let id = new_id() in
            let tv = new_tyvar() in
            let x = Id.{ name; id; ty = () } in
            let id_env = StrMap.replace id_env ~key:name ~data:id in
            let ret, psi = self#term id_env psi in
            self#add_ty_env x tv;
            TvArrow(tv, ret), Abs(lift_arg x, psi)
        | App (psi1, psi2) ->
            let tv_fun, psi1 = self#term id_env psi1 in
            let tv_arg, psi2 = self#term id_env psi2 in
            let tv_ret = new_tyvar() in
            (* Print.pr "tv_ret %a@." pp_hum_tyvar tv_ret; *)
            unify (TvArrow(tv_arg, tv_ret)) tv_fun;
            tv_ret, App (psi1, psi2)

    method hes_rule : id_env -> hes_rule -> unit Hflz.hes_rule =
      fun id_env rule ->
        (* Print.pr "hes_rule.vars %a@." Print.string rule.var; *)
        let id   = StrMap.find_exn id_env rule.var in
        let tv_F = new_tyvar() in
        let _F   = Id.{ name=rule.var; id=id; ty=() } in
        self#add_ty_env _F tv_F;

        (* Print.pr "hes_rule.vars %a@." Print.(list_comma string) rule.args; *)
        let var_env =
          List.map rule.args ~f:begin fun name ->
            let id  = new_id() in
            let tv  = new_tyvar() in
            let var = Id.{ name; id; ty = TySigma() } in
            self#add_ty_env var tv;
            (var, id, tv)
          end
        in
        let vars, _, tv_vars = List.unzip3 var_env in
        let id_env =
          List.fold_left var_env ~init:id_env ~f:begin fun env (var,id,tv) ->
            StrMap.replace env ~key:var.name ~data:id
          end
        in
        (* Print.pr "ID_ENV: %a@." pp_id_env id_env; *)
        let tv_body, body = self#term id_env rule.body in
        unify tv_body TvBool;
        (* Print.pr "LAST@."; *)
        unify tv_F @@
          List.fold_left (List.rev tv_vars)
            ~init:tv_body ~f:(fun ret arg -> TvArrow (arg, ret));
        (* Print.pr "@."; *)
        { var  = _F
        ; body = Hflz.mk_abss vars body
        ; fix  = rule.fix }

    method hes : hes -> unit Hflz.hes =
      fun hes ->
        let id_env =
          List.fold_left hes ~init:StrMap.empty ~f:begin fun id_env rule ->
            try
              StrMap.add_exn id_env ~key:rule.var ~data:(new_id())
            with _ ->
              error @@ Fmt.strf "%s is defined twice" rule.var
          end
        in
        let annotated = List.map hes ~f:(self#hes_rule id_env) in
        annotated
  end

  exception IntType

  class deref ty_env = object (self)
    val ty_env : ty_env = ty_env

    method arg_ty : string -> tyvar -> simple_ty arg = fun info -> function
      | TvInt  -> TyInt
      | TvBool -> TySigma (TyBool())
      | TvRef (_, {contents=None}) as tv ->
          (* Print.pr "DEFAULT %s : %a@." info pp_hum_tyvar tv; *)
          TySigma (TyBool())
          (* assert false *)
      | TvRef (_, {contents=Some tv}) -> self#arg_ty info tv
      | TvArrow (tv1, tv2) ->
          let x = Id.gen ~name:"t" (self#arg_ty (info^".arg") tv1) in
          TySigma (TyArrow (x, self#ty (info^".ret") tv2))
    method ty : string -> tyvar -> simple_ty =
      fun info tv -> match self#arg_ty info tv with
      | TyInt -> raise IntType
      | TySigma ty -> ty

    method id : unit Id.t -> simple_ty Id.t =
      fun x -> match IntMap.find ty_env x.id with
        | None -> failwith @@ Fmt.strf "%s" (Id.to_string x)
        | Some ty -> { x with ty = self#ty (Id.to_string x) ty }
    method arg_id : unit arg Id.t -> simple_ty arg Id.t =
      fun x -> match IntMap.find ty_env x.id with
        | None -> failwith @@ Fmt.strf "%s" (Id.to_string x)
        | Some tv -> { x with ty = self#arg_ty (Id.to_string x) tv }

    method term : unit Hflz.t -> simple_ty Hflz.t = function
      | Var x ->
          begin match self#id x with
          | x -> Var x
          | exception IntType -> Arith (Arith.mk_var x)
          end
      | Bool b           -> Bool b
      | Or  psis         -> Or  (List.map ~f:self#term psis)
      | And psis         -> And (List.map ~f:self#term psis)
      | Exists (l, psi)  -> Exists (l, self#term psi)
      | Forall (l, psi)  -> Forall (l, self#term psi)
      | App (psi1, psi2) -> App (self#term psi1, self#term psi2)
      | Abs (x, psi)     -> Abs (self#arg_id x, self#term psi)
      | Arith a          -> Arith a
      | Pred (pred,as')  -> Pred(pred, as')

    method hes_rule : unit Hflz.hes_rule -> simple_ty Hflz.hes_rule =
      fun rule ->
        let var  = self#id rule.var in
        let body = self#term rule.body in
        { var; body; fix = rule.fix }

    method hes : unit Hflz.hes -> simple_ty Hflz.hes =
      fun hes -> List.map hes ~f:self#hes_rule
  end

  let to_typed rhes =
    let add_annot = new add_annot in
    let annotated = add_annot#hes rhes in
    let deref     = new deref add_annot#get_ty_env in
    deref#hes annotated
end

open Type

let rename_simple_ty_rule
      : simple_ty Hflz.hes_rule
     -> simple_ty Hflz.hes_rule =
  fun rule ->
    let sty        = rule.var.ty in
    let vars, _    = Hflz.decompose_abs rule.body in
    let ty_vars, _ = decompose_arrow sty in
    let ty_vars' =
      List.map2_exn vars ty_vars ~f:begin fun var ty_var ->
        { ty_var with name = var.name }
      end
    in
    let sty' = mk_arrows ty_vars' (TyBool()) in
    { rule with var = { rule.var with ty = sty' } }

let rec rename_abstraction_ty
      : ?env:[`Int] Id.t IdMap.t
     -> simple_ty
     -> abstraction_ty
     -> abstraction_ty =
  fun ?(env=IdMap.empty) orig aty -> match orig, aty with
    | TyBool(), TyBool fs ->
        TyBool(List.map ~f:(Trans.Subst.Id'.formula env) fs)
    | TyArrow({ty=TyInt;_} as x , ret_sty),
      TyArrow({ty=TyInt;_} as x', ret_aty) ->
        let env = IdMap.replace env x' {x with ty=`Int} in
        TyArrow({x with ty=TyInt}, rename_abstraction_ty ~env ret_sty ret_aty)
    | TyArrow({ty=TySigma arg_sty;_} as x , ret_sty),
      TyArrow({ty=TySigma arg_aty;_} as x', ret_aty) ->
        let ty = TySigma(rename_abstraction_ty ~env arg_sty arg_aty) in
        TyArrow({x with ty}, rename_abstraction_ty ~env ret_sty ret_aty)
    | _ ->
        invalid_arg "Raw_hflz.rename_abstraction_ty: Simple type mismatch"

let rename_ty_body : simple_ty Hflz.hes -> simple_ty Hflz.hes =
  fun hes ->
    let rec term : simple_ty IdMap.t -> simple_ty Hflz.t -> simple_ty Hflz.t =
      fun env psi -> match psi with
        | Bool b -> Bool b
        | Var x -> Var { x with ty = IdMap.lookup env x }
        | Or  psis -> Or  (List.map psis ~f:(term env))
        | And psis -> And (List.map psis ~f:(term env))
        | Exists (l, psi) -> Exists (l, term env psi)
        | Forall (l, psi) -> Forall (l, term env psi)
        | Abs ({ty=TySigma ty;_} as x, psi) ->
            Abs(x, term (IdMap.add env x ty) psi)
        | Abs ({ty=TyInt;_} as x, psi) -> Abs(x, term env psi)
        | App (psi1, psi2) -> App (term env psi1, term env psi2)
        | Arith a -> Arith a
        | Pred (pred, as') -> Pred (pred, as')
    in
    let rule : simple_ty IdMap.t
            -> simple_ty Hflz.hes_rule
            -> simple_ty Hflz.hes_rule =
      fun env rule ->
        { rule with body = term env rule.body }
    in
    let env =
      IdMap.of_list @@
        List.map hes ~f:begin fun rule ->
          rule.var, rule.var.ty
        end
    in
    List.map hes ~f:(rule env)

let to_typed (raw_hes, env) =
  let typed_hes =
    raw_hes
    |> Typing.to_typed
    |> List.map ~f:rename_simple_ty_rule
  in
  let () = (* check env *)
    let unknown_nt =
      List.find env ~f:begin fun (f,_) ->
        List.for_all typed_hes ~f:(fun r -> r.var.name <> f)
      end
    in
    match unknown_nt with
    | None -> ()
    | Some (f,_) -> Fn.fatal @@ "ENV: There is no NT named " ^ f
  in
  let gamma = IdMap.of_list @@
    List.map typed_hes ~f:begin fun rule ->
      let v = rule.var in
      let aty =
        match List.Assoc.find ~equal:String.equal env v.name with
        | Some aty -> rename_abstraction_ty v.ty aty
        | None -> map_ty (fun () -> []) v.ty
      in rule.var, aty
    end
  in
  rename_ty_body typed_hes, gamma

