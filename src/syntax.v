Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* --- Abstract base types ------------------------------------------------ *)

(* TODO: add more base types if needed *)
Inductive BaseT : Type :=
| BString : BaseT
| BBool : BaseT
| BNat : BaseT
.

(* --- Syntax: types and expressions (!! internal language only !!) ------------------ *)

(* TODO: add reference types *)
Inductive i_ty : Type :=
| TBase : BaseT -> i_ty                        (* τ_b *)
| TSet  : string -> BaseT -> i_expr -> i_ty    (* {x : τb | e} e must be boolean containing x *)
| TArr : string -> i_ty -> i_ty -> i_ty        (* Πx : τ1. τ2 (x can occur in τ2 - dependent)*)
| TProd : i_ty -> i_ty -> i_ty                 (* τ1 × τ2 *)

with i_expr : Type :=
| EConst : string -> i_expr
| EVar   : string -> i_expr
| EFix   : string -> string -> i_ty -> i_ty -> i_expr -> i_expr (* fix f (x : τ1) : τ2 . e *)
| EApp   : i_expr -> i_expr -> i_expr
| EPair  : i_expr -> i_expr -> i_expr
| EFst   : i_expr -> i_expr
| ESnd   : i_expr -> i_expr
| EIf    : i_expr -> i_expr -> i_expr -> i_expr

| EFail : i_expr
.

Scheme i_expr_ind_mut := Induction for i_expr Sort Prop
with i_ty_ind_mut := Induction for i_ty Sort Prop.

(* --- Context and context lookup ------------------------------------------------ *)

(* Γ - the context for variables *)
Definition var_context := list (string * i_ty).

Fixpoint var_context_lookup (Γ : var_context) (x : string) : option i_ty :=
  match Γ with
  | [] => None
  | (y, t) :: ys => if String.eqb x y then Some t else var_context_lookup ys x
  end.

(* F - the context for constants *)
Definition const_context := list (string * i_ty).

Fixpoint const_ctx_lookup (F : const_context) (x : string) : option i_ty :=
  match F with
  | [] => None
  | (y, t) :: ys => if String.eqb x y then Some t else const_ctx_lookup ys x
  end.

(* --- Pure term validation ------------------------------------------------------ *)

(*
Pure terms are:
- variables whose essential type is a base type
- constants with simple type (τb1 → τb2 → ... → τbn)
- application of pure terms to pure terms
 *)

Fixpoint is_simple_type (type : i_ty) : bool :=
  match type with
  | TBase _ => true
  | TArr fname t1 t2 => is_simple_type t1 && is_simple_type t2
  | TProd t1 t2 => is_simple_type t1 && is_simple_type t2
  | _ => false
  end.

Definition essential_type_is_base_type (type : i_ty) : bool :=
  match type with
  | TBase _ => true
  | TSet _ _ _ => true
  | _ => false
  end.

Fixpoint is_pure_term (term : i_expr) (var_con : var_context) (const_con : const_context) : bool :=
  match term with
  | EConst con_name => match (const_ctx_lookup const_con con_name) with
    | Some type => is_simple_type type
    | _ => false
    end
  | EVar var_name => match (var_context_lookup var_con var_name) with
    | Some type => essential_type_is_base_type type
    | _ => false
    end
  | EApp exp1 exp2 => is_pure_term exp1 var_con const_con && is_pure_term exp2 var_con const_con
  | _ => false
  end.

(* Some testing just in case *)
Compute is_pure_term (EApp (EConst "f") (EVar "a")) [] [].
Compute is_pure_term (EApp (EConst "f") (EVar "a")) [("a"%string , TSet "x" BBool (EConst "b"))] [].
Compute is_pure_term (EApp (EConst "f") (EVar "a")) [("a"%string , TSet "x" BBool (EConst "b"))] [("f"%string , TArr "f" (TBase BBool) (TBase BBool))].


(* --- Syntax: types and expressions (surface language) ------------------ *)

(* TODO: add reference types *)
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
