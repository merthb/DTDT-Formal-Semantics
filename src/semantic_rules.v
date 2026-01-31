Require Import DTDT.syntax.
Import ListNotations.
From stdpp Require Export base.
From stdpp Require Export strings.
From stdpp Require Import stringmap.


(* --- Selfification rule ------------------------------------------------------ *)

Fixpoint exp_vars (term : i_expr) : list string :=
  match term with
  | EConst var => [var]
  | EVar var => [var]
  | EFix v1 v2 ty1 ty2 exp => v1 :: v2 :: ty_vars ty1 ++ ty_vars ty2 ++ exp_vars exp
  | EApp exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EPlus exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EPair exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EFst exp => exp_vars exp
  | ESnd exp => exp_vars exp
  | EIf exp1 exp2 exp3 => exp_vars exp1 ++ exp_vars exp2 ++ exp_vars exp3
  | ENot exp => exp_vars exp
  | EAnd exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EOr exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EImp exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EEq exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | ENewRef type exp => ty_vars type ++ exp_vars exp
  | EGet exp => exp_vars exp
  | ESet exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | _ => []
  end
with ty_vars (type : i_ty) : list string :=
  match type with
  | TBase _ => []
  | TSet var _ exp => var :: exp_vars exp
  | TArr ty1 ty2 => ty_vars ty1 ++ ty_vars ty2
  | TArrDep var ty1 ty2 => var :: ty_vars ty1 ++ ty_vars ty2
  | TProd ty1 ty2 => ty_vars ty1 ++ ty_vars ty2
  | TRef type => ty_vars type
  end.

Definition fresh_string_list (l : list string) : string :=
  fresh_string_of_set ("x"%string) (list_to_set l).

Fixpoint self (type : i_ty) (term : i_expr) : i_ty :=
  match type with
  | TBase ty => TSet (fresh_string_list (exp_vars term)) ty (EEq (EVar (fresh_string_list (exp_vars term))) term)
  | TSet var tb expr => TSet var tb (EAnd expr (EEq (EVar var) term))
  | TArr (TBase ty) ty2 => TArrDep (fresh_string_list (exp_vars term)) (TBase ty) (self ty2 (EApp term (EVar (fresh_string_list (exp_vars term)))))
  | x => x
  end.

Compute self (TBase BNat) (EVar ("x"%string)).
Compute self (TArr (TBase BNat) (TArr (TBase BNat) (TBase BNat))) (EVar ("+"%string)).


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
  | TArr t1 t2 => is_simple_type t1 && is_simple_type t2
  | TProd t1 t2 => is_simple_type t1 && is_simple_type t2
  | _ => false
  end.

Definition essential_type_is_base_type (type : i_ty) : bool :=
  match type with
  | TBase _ => true
  | TSet _ _ _ => true
  | _ => false
  end.
Notation "β[ t ]" := (essential_type_is_base_type t) (at level 10).


(* Fixpoint is_pure_term (term : i_expr) (var_con : var_context) (const_con : const_context) : bool :=
  match term with
  | EConst con_name => match (const_ctx_lookup const_con con_name) with
    | Some type => is_simple_type type
    | _ => false
    end
  | EVar var_name => match (var_ctx_lookup var_con var_name) with
    | Some type => essential_type_is_base_type type
    | _ => false
    end
  | EApp exp1 exp2 => is_pure_term exp1 var_con const_con && is_pure_term exp2 var_con const_con
  | _ => false
  end.

(* Some testing just in case *)
Compute is_pure_term (EApp (EConst "f") (EVar "a")) [] [].
Compute is_pure_term (EApp (EConst "f") (EVar "a")) [("a"%string , TSet "x" BBool (EBool false))] [].
Compute is_pure_term (EApp (EConst "f") (EVar "a")) [("a"%string , TSet "x" BBool (EConst "b"))] [("f"%string , TArr (TBase BBool) (TBase BBool))]. *)



(* Fancier way *)

Inductive has_type_pure
  ( Γ : var_context)
  (Φ : const_context)
  : i_expr -> i_ty -> Prop :=
  | PVar :
    forall x τb,
      Γ[ x ] Γ = Some τb ->
      β[ τb ] ->
      has_type_pure Γ Φ (EVar x) τb
  | PNat :
    forall n,
    has_type_pure Γ Φ (ENat n) (TBase BNat)
  | PBool :
    forall b,
    has_type_pure Γ Φ (EBool b) (TBase BBool)
  | PString :
    forall s,
    has_type_pure Γ Φ (EString s) (TBase BString)
  | PUnit :
    forall u,
    has_type_pure Γ Φ (EUnit u) (TBase BUnit)
  | PConst :
    forall c τ,
      Φ[ c ] Φ = Some τ ->
      is_simple_type τ ->
      has_type_pure Γ Φ (EConst c) τ
  | PApp :
    forall e₁ e₂ τ₁ τ₂,
      β[ τ₁ ] ->
      has_type_pure Γ Φ e₁ (TArr τ₁ τ₂) ->
      has_type_pure Γ Φ e₂ τ₁ ->
      has_type_pure Γ Φ (EApp e₁ e₂) τ₂.

Lemma pure_plus_app_nat :
  has_type_pure [( "n" , TBase BNat)] [( "+" , TArr (TBase BNat) (TArr (TBase BNat) (TBase BNat)))] (EApp (EConst "+"%string) (ENat 1)) (TArr (TBase BNat) (TBase BNat)).
  Proof.
  apply (PApp _ _ _ _ (TBase BNat) _).
  - simpl. reflexivity.
  - apply PConst.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - apply PNat.
  Qed.

Lemma pure_plus_app_var :
  has_type_pure [( "n" , TBase BNat)] [( "+" , TArr (TBase BNat) (TArr (TBase BNat) (TBase BNat)))] (EApp (EConst "+"%string) (EVar "n")) (TArr (TBase BNat) (TBase BNat)).
  Proof.
  apply (PApp _ _ _ _ (TBase BNat) _).
  - simpl. reflexivity.
  - apply PConst.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - apply PVar.
    + simpl. reflexivity.
    + simpl. reflexivity.
  Qed.

(* --- Well-formed type checking ------------------------------------------------------ *)

Inductive ty_valid
  (Γ : var_context)
  (Φ : const_context)
  : i_ty -> Prop :=
  | VBase :
    forall (τb : BaseT),
      ty_valid Γ Φ (TBase τb)
  | VSet :
    forall var (τb : BaseT) e,
      has_type_pure ((var , TBase τb) :: Γ) Φ e (TBase BBool) ->
      ty_valid Γ Φ (TSet var τb e)
  | VFun :
    forall τ₁ τ₂,
      ty_valid Γ Φ τ₁ ->
      ty_valid Γ Φ τ₂ ->
      ty_valid Γ Φ (TArr τ₁ τ₂)
  | VFunDep :
    forall var τ₁ τ₂,
      ty_valid Γ Φ τ₁ ->
      ty_valid ((var, τ₁) :: Γ) Φ τ₂ ->
      ty_valid Γ Φ (TArrDep var τ₁ τ₂)
  | VPair :
    forall τ₁ τ₂,
      ty_valid Γ Φ τ₁ ->
      ty_valid Γ Φ τ₂ ->
      ty_valid Γ Φ (TProd τ₁ τ₂)
  | VRef :
    forall τ₁,
      ty_valid Γ Φ τ₁ ->
      ty_valid Γ Φ (TRef τ₁).

(* --- Subtyping ---------------------------------------------------------------------- *)

Inductive subtype 
  (Γ : var_context)
  (Φ : const_context) :
  i_ty -> i_ty -> Prop :=
  | SBase :
    forall b,
      subtype Γ Φ (TBase b) (TBase b)
  | SSet :
    forall var τb e₁ e₂,
      ty_valid Γ Φ (TSet var τb e₁) ->
      ty_valid Γ Φ (TSet var τb e₂) ->
      has_type_pure ((var , TBase τb) :: Γ) Φ
        (EImp e₁ e₂) (TBase BBool) -> (* TODO: should be |= *)
      subtype Γ Φ (TSet var τb e₁) (TSet var τb e₂)
  | SSetBase :
    forall var τb e,
      ty_valid Γ Φ (TSet var τb e) ->
      subtype Γ Φ (TSet var τb e) (TBase τb)
  | SBaseSet :
    forall var τb e,
      ty_valid Γ Φ (TSet var τb e) ->
      has_type_pure ((var , TBase τb) :: Γ) Φ e (TBase BBool) -> (* TODO: should be |- *)
      subtype Γ Φ (TBase τb) (TSet var τb e)
  | SFun :
    forall τ₁ τ₁' τ₂ τ₂',
      subtype Γ Φ τ₁' τ₁ ->
      subtype Γ Φ τ₂ τ₂' ->
      subtype Γ Φ (TArr τ₁ τ₂) (TArr τ₁' τ₂')
  | SFunDep :
    forall var τ₁ τ₁' τ₂ τ₂',
      subtype Γ Φ τ₁' τ₁ ->
      subtype ((var , τ₁') :: Γ) Φ τ₂ τ₂' ->
      subtype Γ Φ (TArrDep var τ₁ τ₂) (TArrDep var τ₁' τ₂')
  | SPair :
    forall τ₁ τ₁' τ₂ τ₂',
      subtype Γ Φ τ₁ τ₁' ->
      subtype Γ Φ τ₂ τ₂' ->
      subtype Γ Φ (TProd τ₁ τ₂) (TProd τ₁' τ₂')
  | SRef :
    forall τ τ',
      subtype Γ Φ τ τ' ->
      subtype Γ Φ τ' τ ->
      subtype Γ Φ (TRef τ) (TRef τ').














