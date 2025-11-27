Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* --- Abstract base types and constants ---------------------------------- *)

(* Base type set. TODO: add more base types *)
Inductive BaseT : Type :=
| BString : string -> BaseT
| BBool : bool -> BaseT
| BNat : nat -> BaseT
.

(* --- Syntax: types and expressions (internal language) ------------------ *)

Inductive ty : Type :=
| TBase : BaseT -> ty                      (* τ_b *)
| TSet  : string -> BaseT -> expr -> ty    (* {x : τb | e} e must be boolean containing x *)
| TArr : string -> ty -> ty -> ty          (* Πx : τ1. τ2 (x can occur in τ2 - dependent)*)
| TProd : ty -> ty -> ty                   (* τ1 × τ2 *)
(* | TRef  : ty -> ty.                        (* τ ref *) *)

with expr : Type :=
| EConst : string -> expr
| EVar   : string -> expr
| EFix   : string -> string -> ty -> ty -> expr -> expr (* fix f (x : τ1) : τ2 . e -- storing the names too *)
| EApp   : expr -> expr -> expr
| EPair  : expr -> expr -> expr
| EFst   : expr -> expr
| ESnd   : expr -> expr
| EIf    : expr -> expr -> expr -> expr

| ESimple : expr -> expr
| EDep : expr -> expr
| EAssert : expr -> ty -> expr
(* | ENewRef : ty -> expr -> expr
| EGet   : expr -> expr               (* !e *)
| ESet   : expr -> expr -> expr       (* e := e *)
| EFail  : expr *)
.

Scheme expr_ind_mut := Induction for expr Sort Prop
with ty_ind_mut := Induction for ty Sort Prop.



(* --- Context and context lookup ------------------------------------------------ *)

(* Γ - the context for variables *)
Definition context := list (string * ty).

Fixpoint context_lookup (Γ : context) (x : string) : option ty :=
  match Γ with
  | [] => None
  | (y, t) :: ys => if String.eqb x y then Some t else context_lookup ys x
  end.

(* F - the context for constants *)
Definition const_context := list (string * ty).

Fixpoint const_ctx_lookup (F : const_context) (x : string) : option ty :=
  match F with
  | [] => None
  | (y, t) :: ys => if String.eqb x y then Some t else const_ctx_lookup ys x
  end.

(* --- Pure term validation ------------------------------------------------------ *)

(* TODO checking for pure terms *)