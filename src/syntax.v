Require Export Coq.Strings.String.
Require Export Coq.Init.Nat.
Require Export Coq.Bool.Bool.
From stdpp Require Export base.
From stdpp Require Export strings.
From stdpp Require Export gmap.

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

Notation "Γ ,, x ↦ v" :=
  (<[x := v]> Γ)
  (at level 20, right associativity).

(* ? (\Γ) - the context for variables *)
Definition var_context := gmap string (i_ty * i_expr).

(* ? (\F) - the context for constants *)
Definition const_context := gmap string (i_ty * i_expr).

(* ? - the runtime store for locations *)
Definition store_context := gmap string (i_ty * i_expr).

Definition ctx : Type := ((var_context * const_context) * store_context).
Notation "Γ ▷vars"   := (fst (fst Γ)) (at level 10).
Notation "Γ ▷consts" := (snd (fst Γ)) (at level 10).
Notation "Γ ▷store"  := (snd Γ) (at level 10).

Definition empty_ctx : ctx := ((∅, ∅), ∅).

Definition var_ctx_lookup (Γ : ctx) (x : string) : option (i_ty * i_expr) := (Γ ▷vars) !! x.
Notation "c !!₁ x" := (var_ctx_lookup c x) (at level 50).

Definition const_ctx_lookup (Γ : ctx) (x : string) : option (i_ty * i_expr) := (Γ ▷consts) !! x.
Notation "c !!₂ x" := (const_ctx_lookup c x) (at level 50).

Definition store_ctx_lookup (Γ : ctx) (x : string) : option (i_ty * i_expr) := (Γ ▷store) !! x.
Notation "c !!₃ x" := (store_ctx_lookup c x) (at level 50).

Definition ctx_add_var (Γ : ctx) (x : string) (τ : i_ty) (exp : i_expr) : ctx :=
  ((<[ x := (τ, exp) ]> (Γ ▷vars), Γ ▷consts), Γ ▷store).
Notation "g ,,v x ↦ v" :=
  (ctx_add_var g x (fst v) (snd v))
  (at level 30).

Definition ctx_add_const (Γ : ctx) (f : string) (τ : i_ty) (e : i_expr) : ctx :=
  ((Γ ▷vars, <[ f := (τ, e) ]> (Γ ▷consts)), Γ ▷store).
Notation "g ,,c f ↦ v" :=
  (ctx_add_const g f (fst v) (snd v))
  (at level 30).

Definition ctx_add_store (Γ : ctx) (l : string) (τ : i_ty) (exp : i_expr) : ctx :=
  ((Γ ▷vars, Γ ▷consts), <[ l := (τ, exp) ]> (Γ ▷store)).
Notation "g ,,s l ↦ v" :=
  (ctx_add_store g l (fst v) (snd v))
  (at level 30).

Definition add_ctx (Γ₁ Γ₂ : ctx) : ctx :=
  (((Γ₂ ▷vars) ∪ (Γ₁ ▷vars), (Γ₂ ▷consts) ∪ (Γ₁ ▷consts)), (Γ₂ ▷store) ∪ (Γ₁ ▷store)).
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

(* Γ (\Γ) - the context for variables *)
Definition var_context_surf := gmap string (ty * expr).

(* Φ (\F) - the context for constants *)
Definition const_context_surf := gmap string (ty * expr).

Definition ctx_surf : Type := (var_context_surf * const_context_surf).
Notation "Γ ▷surfvars"   := (fst Γ) (at level 40).
Notation "Γ ▷surfconsts" := (snd Γ) (at level 40).

Definition empty_ctx_surf : ctx_surf := (∅, ∅).

Definition var_ctx_lookup_surf (Γ : ctx_surf) (x : string) : option (ty * expr) := (Γ ▷surfvars) !! x.
Notation "c !!₁ₛ x" := (var_ctx_lookup_surf c x) (at level 1).

Definition const_ctx_lookup_surf (Γ : ctx_surf) (x : string) : option (ty * expr) := (Γ ▷surfconsts) !! x.
Notation "c !!₂ₛ x" := (const_ctx_lookup_surf c x) (at level 10).

Definition ctx_add_var_surf (Γ : ctx_surf) (x : string) (τ : ty) (exp : expr) : ctx_surf :=
  (<[ x := (τ, exp) ]> (Γ ▷surfvars), Γ ▷surfconsts).
Notation "g ,,sv x ↦ v" :=
  (ctx_add_var_surf g x (fst v) (snd v))
  (at level 30).

Definition ctx_add_const_surf (Γ : ctx_surf) (f : string) (τ : ty) (e : expr) : ctx_surf :=
  (Γ ▷surfvars, <[ f := (τ, e) ]> (Γ ▷surfconsts)).
Notation "g ,,sc f ↦ v" :=
  (ctx_add_const_surf g f (fst v) (snd v))
  (at level 30).
