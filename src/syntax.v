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

(* --- Context and context lookup ------------------------------------------------ *)

(* Γ (\Gamma) - the context for variables *)
Definition var_context := list (string * i_ty).

Fixpoint var_ctx_lookup (Γ : var_context) (x : string) : option i_ty :=
  match Γ with
  | [] => None
  | (y, t) :: ys => if String.eqb x y then Some t else var_ctx_lookup ys x
  end.
Notation "Γ[ x ] c" := (var_ctx_lookup c x) (at level 1).

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

(* TODO: add surface level reference types *)
Inductive ty : Type :=
| TInter : i_ty -> ty

with expr : Type :=
| EInter : i_expr -> expr
| ESimple : expr -> expr
| EDep : expr -> expr
| EAssert : expr -> ty -> expr
.

Scheme expr_ind_mut := Induction for expr Sort Prop
with ty_ind_mut := Induction for ty Sort Prop.
