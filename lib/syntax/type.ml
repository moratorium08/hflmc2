open Hflmc2_util

type 'ty arg
  = TyInt
  | TySigma of 'ty
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type 'annot ty
  = TyBool of 'annot
  | TyArrow of 'annot ty arg Id.t * 'annot ty
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type simple_ty = unit ty
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type abstraction_ty = Formula.t list ty
  [@@deriving eq,ord,show,iter,map,fold,sexp]



type abstracted_ty =
  | ATyBool
  | ATyArrow of abstracted_argty * abstracted_ty
and abstracted_argty = abstracted_ty
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let rec abstract : abstraction_ty -> abstracted_ty = function
  | TyBool preds ->
      (* bool -> ... -> bool -> o *)
      Fn.apply_n_times ~n:(List.length preds) (fun ret -> ATyArrow(ATyBool, ret)) ATyBool
  | TyArrow({ Id.ty = TyInt; _ }, ret) ->
      abstract ret
  | TyArrow({ Id.ty = TySigma arg; _}, ret) ->
      ATyArrow(abstract arg, abstract ret)


