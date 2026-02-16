Require Export Coq.Strings.String.
Require Export Coq.Lists.List.
Require Export Coq.Init.Nat.
Require Export Coq.Bool.Bool.
Import ListNotations.

(* --- Abstract base types ------------------------------------------------ *)

(* TODO: add more base types if needed *)
Inductive BaseT : Type :=
| BString : BaseT
| BBool : BaseT
| BNat : BaseT
| BUnit : BaseT
.

Definition base_to_set (τb : BaseT) : Set :=
  match τb with
  | BString => string
  | BBool => bool
  | BNat => nat
  | BUnit => unit
  end.

(* --- Syntax: types and expressions (!! internal language only !!) ------------------ *)

Inductive i_ty : Type :=
| TBase     : BaseT -> i_ty                        (* τ_b *)
| TSet      : string -> BaseT -> i_expr -> i_ty    (* {x : τb | e} e must be boolean containing x *)
| TArr      : i_ty -> i_ty -> i_ty
| TArrDep   : string -> i_ty -> i_ty -> i_ty        (* Πx : τ1. τ2 (x can occur in τ2 - dependent)*)
| TProd     : i_ty -> i_ty -> i_ty                 (* τ1 × τ2 *)
| TRef      : i_ty -> i_ty                         (* τ ref *)

with i_expr : Type :=
(* have to store the values somewhere
   TODO: add more if more base types are added *)
| EString : string -> i_expr
| EBool : bool -> i_expr
| ENat : nat -> i_expr
| EUnit : unit -> i_expr

| EConst : string -> i_expr
| EVar    : string -> i_expr
| EFix    : string -> string -> i_ty -> i_ty -> i_expr -> i_expr (* fix f (x : τ1) : τ2 . e *)
| EApp    : i_expr -> i_expr -> i_expr
| EPlus   : i_expr -> i_expr -> i_expr
| EPair   : i_expr -> i_expr -> i_expr
| EFst    : i_expr -> i_expr
| ESnd    : i_expr -> i_expr
| EIf     : i_expr -> i_expr -> i_expr -> i_expr
| ENot    : i_expr -> i_expr
| EAnd    : i_expr -> i_expr -> i_expr
| EOr     : i_expr -> i_expr -> i_expr
| EImp    : i_expr -> i_expr -> i_expr
| EEq     : i_expr -> i_expr -> i_expr
| ENewRef : i_ty -> i_expr -> i_expr
| EGet    : i_expr -> i_expr               (* !e *)
| ESet    : i_expr -> i_expr -> i_expr       (* e := e *)
| EFail   : i_expr
.

Scheme i_expr_ind_mut := Induction for i_expr Sort Prop
with i_ty_ind_mut := Induction for i_ty Sort Prop.

Definition make_expr (t : BaseT) : base_to_set t -> i_expr :=
  match t with
  | BString => EString
  | BNat    => ENat
  | BBool   => EBool
  | BUnit   => EUnit
  end.

(* --- Context and context lookup ------------------------------------------------ *)

(* Γ (\Gamma) - the context for variables *)
Definition var_context := list (string * i_ty).

Fixpoint var_ctx_lookup (Γ : var_context) (x : string) : option i_ty :=
  match Γ with
  | [] => None
  | (y, t) :: ys => if String.eqb x y then Some t else var_ctx_lookup ys x
  end.
Notation "Γ[ x ] c" := (var_ctx_lookup c x) (at level 1).

(* Γ (\Gamma) - the context for variable values *)
Definition varval_context := list (string * i_expr).

Fixpoint varval_ctx_lookup (Γ : varval_context) (x : string) : option i_expr :=
  match Γ with
  | [] => None
  | (y, e) :: ys => if String.eqb x y then Some e else varval_ctx_lookup ys x
  end.
Notation "Γv[ x ] c" := (varval_ctx_lookup c x) (at level 1).


(* Φ (\F) - the context for constants *)
Definition const_context := list (string * i_ty).

Fixpoint const_ctx_lookup (F : const_context) (x : string) : option i_ty :=
  match F with
  | [] => None
  | (y, t) :: ys => if String.eqb x y then Some t else const_ctx_lookup ys x
  end.
Notation "Φ[ x ] c" := (const_ctx_lookup c x) (at level 10).

(* ι (\i) - the context for function implementations *)
Definition fun_imp_list := list (string * i_expr).

Fixpoint fun_imp_lookup (f : fun_imp_list) (x : string) : option i_expr :=
  match f with
  | [] => None
  | (y, e) :: ys => if String.eqb x y then Some e else fun_imp_lookup ys x
  end.
Notation "ι[ x ] c" := (fun_imp_lookup c x) (at level 10).

(* --- Syntax: types and expressions (surface language) ------------------ *)

Inductive ty : Type :=
| TyBase     : BaseT -> ty
| TySet      : string -> BaseT -> expr -> ty
| TyArr      : ty -> ty -> ty
| TyArrDep   : string -> ty -> ty -> ty
| TyProd     : ty -> ty -> ty
| TyRef      : ty -> ty
| TyDeRef    : ty -> ty

with expr : Type :=
(* have to store the values somewhere
   TODO: add more if more base types are added *)
| ExString : string -> expr
| ExBool : bool -> expr
| ExNat : nat -> expr
| ExUnit : unit -> expr

| ExConst : string -> expr
| ExVar    : string -> expr
| ExFix    : string -> string -> ty -> ty -> expr -> expr
| ExApp    : expr -> expr -> expr
| ExPlus   : expr -> expr -> expr
| ExPair   : expr -> expr -> expr
| ExFst    : expr -> expr
| ExSnd    : expr -> expr
| ExIf     : expr -> expr -> expr -> expr
| ExNot    : expr -> expr
| ExAnd    : expr -> expr -> expr
| ExOr     : expr -> expr -> expr
| ExImp    : expr -> expr -> expr
| ExEq     : expr -> expr -> expr
| ExNewRef : ty -> expr -> expr
| ExGet    : expr -> expr               (* !e *)
| ExSet    : expr -> expr -> expr       (* e := e *)
| ExDeRef  : expr -> expr
| ExGetDep : expr -> expr              (* !d e *)
| ExSetDep : expr -> expr -> expr      (* e1 :=d e2 *)

| EAssert : expr -> ty -> expr
| ESimple : expr -> expr
| EDep    : expr -> expr
.

Scheme expr_ind_mut := Induction for expr Sort Prop
with ty_ind_mut := Induction for ty Sort Prop.

(* Γ (\Gamma) - the context for variables *)
Definition var_context_surf := list (string * ty).

Fixpoint var_ctx_lookup_surf (Γ : var_context_surf) (x : string) : option ty :=
  match Γ with
  | [] => None
  | (y, t) :: ys => if String.eqb x y then Some t else var_ctx_lookup_surf ys x
  end.
Notation "Γs[ x ] c" := (var_ctx_lookup_surf c x) (at level 1).

(* Γ (\Gamma) - the context for variable values *)
Definition varval_context_surf := list (string * expr).

Fixpoint varval_ctx_lookup_surf (Γ : varval_context_surf) (x : string) : option expr :=
  match Γ with
  | [] => None
  | (y, e) :: ys => if String.eqb x y then Some e else varval_ctx_lookup_surf ys x
  end.
Notation "Γvs[ x ] c" := (varval_ctx_lookup_surf c x) (at level 1).


(* Φ (\F) - the context for constants *)
Definition const_context_surf := list (string * ty).

Fixpoint const_ctx_lookup_surf (F : const_context_surf) (x : string) : option ty :=
  match F with
  | [] => None
  | (y, t) :: ys => if String.eqb x y then Some t else const_ctx_lookup_surf ys x
  end.
Notation "Φs[ x ] c" := (const_ctx_lookup_surf c x) (at level 10).

(* ι (\i) - the context for function implementations *)
Definition fun_imp_list_surf := list (string * expr).

Fixpoint fun_imp_lookup_surf (f : fun_imp_list_surf) (x : string) : option expr :=
  match f with
  | [] => None
  | (y, e) :: ys => if String.eqb x y then Some e else fun_imp_lookup_surf ys x
  end.
(* Notation "ιs[ x ] c" := (fun_imp_lookup_surf c x) (at level 10).
 *)