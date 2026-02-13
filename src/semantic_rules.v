Require Import DTDT.syntax.
Require Import DTDT.big_step_eval.
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
      has_type_pure Γ Φ (EApp e₁ e₂) τ₂
  | PNot :
    forall b,
      has_type_pure Γ Φ b (TBase BBool) ->
      has_type_pure Γ Φ (ENot b) (TBase BBool)
  | PImp :
    forall b₁ b₂,
      has_type_pure Γ Φ b₁ (TBase BBool) ->
      has_type_pure Γ Φ b₂ (TBase BBool) ->
      has_type_pure Γ Φ (EImp b₁ b₂) (TBase BBool)
  | PAnd :
    forall b₁ b₂,
      has_type_pure Γ Φ b₁ (TBase BBool) ->
      has_type_pure Γ Φ b₂ (TBase BBool) ->
      has_type_pure Γ Φ (EAnd b₁ b₂) (TBase BBool)
  | POr :
    forall b₁ b₂,
      has_type_pure Γ Φ b₁ (TBase BBool) ->
      has_type_pure Γ Φ b₂ (TBase BBool) ->
      has_type_pure Γ Φ (EOr b₁ b₂) (TBase BBool)
  | PPlus :
    forall n₁ n₂,
      has_type_pure Γ Φ n₁ (TBase BNat) ->
      has_type_pure Γ Φ n₂ (TBase BNat) ->
      has_type_pure Γ Φ (EPlus n₁ n₂) (TBase BNat).

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

(* Should this be on surface level? In paper there's a rule for dereferation too *)
Inductive subtype 
  (Γ : var_context)
  (Γv : varval_context)
  (Φ : const_context)
  (ι : fun_imp_list) :
  i_ty -> i_ty -> Prop :=
  | SBase :
    forall b,
      subtype Γ Γv Φ ι (TBase b) (TBase b)
  | SSet :
    forall var τb e₁ e₂,
      ty_valid Γ Φ (TSet var τb e₁) ->
      ty_valid Γ Φ (TSet var τb e₂) ->
      ∀ (c : (base_to_set τb)), eval ((var , TBase τb) :: Γ) ((var , make_expr τb c) :: Γv) Φ ι (EImp e₁ e₂) (EBool true) ->
      subtype Γ Γv Φ ι (TSet var τb e₁) (TSet var τb e₂)
  | SSetBase :
    forall var τb e,
      ty_valid Γ Φ (TSet var τb e) ->
      subtype Γ Γv Φ ι (TSet var τb e) (TBase τb)
  | SBaseSet :
    forall var τb e,
      ty_valid Γ Φ (TSet var τb e) ->
      ∀ (c : (base_to_set τb)), eval ((var , TBase τb) :: Γ) ((var , make_expr τb c) :: Γv) Φ ι e (EBool true) ->
      subtype Γ Γv Φ ι (TBase τb) (TSet var τb e)
  | SFun :
    forall τ₁ τ₁' τ₂ τ₂',
      subtype Γ Γv Φ ι τ₁' τ₁ ->
      subtype Γ Γv Φ ι τ₂ τ₂' ->
      subtype Γ Γv Φ ι (TArr τ₁ τ₂) (TArr τ₁' τ₂')
  | SFunDep :
    forall var τ₁ τ₁' τ₂ τ₂',
      subtype Γ Γv Φ ι τ₁' τ₁ ->
      subtype ((var , τ₁') :: Γ) Γv Φ ι τ₂ τ₂' ->
      subtype Γ Γv Φ ι (TArrDep var τ₁ τ₂) (TArrDep var τ₁' τ₂')
  | SPair :
    forall τ₁ τ₁' τ₂ τ₂',
      subtype Γ Γv Φ ι τ₁ τ₁' ->
      subtype Γ Γv Φ ι τ₂ τ₂' ->
      subtype Γ Γv Φ ι (TProd τ₁ τ₂) (TProd τ₁' τ₂')
  | SRef :
    forall τ τ',
      subtype Γ Γv Φ ι τ τ' ->
      subtype Γ Γv Φ ι τ' τ ->
      subtype Γ Γv Φ ι (TRef τ) (TRef τ').

Lemma set_sub_test : forall Γ Γv Φ ι, subtype Γ Γv Φ ι (TSet "x" BBool (ENot (EVar "x"))) (TSet "x" BBool (EBool true)).
Proof.
intros.
eapply SSet.
apply VSet.
apply PNot.
apply PVar.
simpl. reflexivity.
simpl. reflexivity.
apply VSet.
apply PBool.
simpl.
apply eval_imp with (e₁ := ENot (EVar "x")) (e₂ := EBool true) (b₁ := true) (b₂ := true).
apply eval_not with (b := false).
eapply eval_var.
simpl; reflexivity.
simpl; reflexivity.
apply eval_bool.
Qed.

(* two equivalent sets *)
Lemma set_sub_test_without_var_use : forall Γ Γv Φ ι, subtype Γ Γv Φ ι (TSet "x" BBool (ENot (EBool false))) (TSet "x" BBool (EBool true)).
Proof.
intros.
apply SSet with (c := true).
apply VSet.
apply PNot.
apply PBool.
apply VSet.
apply PBool.
simpl.
apply eval_imp with (e₁ := ENot (EBool false)) (e₂ := EBool true) (b₁ := true) (b₂ := true).
apply eval_not with (e := EBool false) (b := false).
apply eval_bool.
apply eval_bool.
Qed.

(* actual subsets *)
Lemma set_sub_test_without_var_use2 : forall Γ Γv Φ ι, subtype Γ Γv Φ ι (TSet "x" BBool (ENot (EBool true))) (TSet "x" BBool (EBool true)).
Proof.
intros.
apply SSet with (c := true).
apply VSet.
apply PNot.
apply PBool.
apply VSet.
apply PBool.
apply eval_imp with (e₁ := ENot (EBool true)) (e₂ := EBool true) (b₁ := false) (b₂ := true).
apply eval_not with (e := EBool true) (b := true).
apply eval_bool.
apply eval_bool.
Qed.

Lemma base_sub_set_test : forall Γ Γv Φ ι, subtype Γ Γv Φ ι (TBase BBool) (TSet "x" BBool (EOr (EBool true) (EVar "x"))).
Proof.
intros.
eapply SBaseSet.
apply VSet.
apply POr.
apply PBool.
apply PVar.
simpl; reflexivity.
simpl; reflexivity.
simpl.
apply eval_or with (b₁ := true) (b₂ := false).
apply eval_bool.
eapply eval_var.
simpl; reflexivity.
simpl; reflexivity.
Qed.

(* --- Type rules for the internal language ------------------------------------------- *)

Inductive has_type
  ( Γ : var_context)
  (Γv : varval_context)
  (Φ : const_context)
  (ι : fun_imp_list)
  : i_expr -> i_ty -> Prop :=
  | TConst :
    forall c τ,
      Φ[ c ] Φ = Some τ ->
      has_type Γ Γv Φ ι (EConst c) τ
  | TVar :
    forall v τ,
      Γ[ v ] Γ = Some τ ->
      has_type Γ Γv Φ ι (EVar v) τ
  | TFail :
    forall τ,
      ty_valid Γ Φ τ ->
      has_type Γ Γv Φ ι EFail τ
  | TFun :
    forall f x τ₁ τ₂ e,
      ty_valid Γ Φ (TArrDep x τ₁ τ₂) ->
      has_type Γ Γv ((f , (TArrDep x τ₁ τ₂)) :: Φ) ι e τ₂ ->
      has_type Γ Γv Φ ι (EFix f x τ₁ τ₂ e) (TArrDep x τ₁ τ₂)
  | TAppPure :
    forall e₁ e₂ x τ₁ τ₂,
      has_type Γ Γv Φ ι e₂ τ₁ ->
      (forall τ₃, has_type_pure Γ Φ e₂ τ₃) ->
      has_type Γ Γv Φ ι e₁ (TArrDep x τ₁ τ₂) ->
      has_type Γ Γv Φ ι (EApp e₁ e₂) (τ₂(* TODO [e₂/x]τ₂ kellene*))
  | TAppImPure :
    forall e₁ e₂ τ₁ τ₂,
      has_type Γ Γv Φ ι e₂ τ₁ ->
      has_type Γ Γv Φ ι e₁ (TArr τ₁ τ₂) ->
      has_type Γ Γv Φ ι (EApp e₁ e₂) τ₂
  | TPair :
    forall e₁ e₂ τ₁ τ₂,
      has_type Γ Γv Φ ι e₁ τ₁ ->
      has_type Γ Γv Φ ι e₂ τ₂ ->
      has_type Γ Γv Φ ι (EPair e₁ e₂) (TProd τ₁ τ₂)
  | TFst :
    forall e τ₁ τ₂,
      has_type Γ Γv Φ ι e (TProd τ₁ τ₂) ->
      has_type Γ Γv Φ ι (EFst e) τ₁
  | TSnd :
    forall e τ₁ τ₂,
      has_type Γ Γv Φ ι e (TProd τ₁ τ₂) ->
      has_type Γ Γv Φ ι (ESnd e) τ₂
  | TIf :
    forall e e₁ e₂ τ u,
      has_type_pure Γ Φ e (TBase BBool) ->
      has_type ((u , TBase BBool) :: Γ) ((u , e) :: Γv) Φ ι e₁ τ ->
      has_type ((u , TBase BBool) :: Γ) ((u , ENot e) :: Γv) Φ ι e₂ τ ->
      has_type Γ Γv Φ ι (EIf e e₁ e₂) τ
  | TSelf :
    forall e τ,
      has_type Γ Γv Φ ι e τ ->
      (forall τ₁, has_type_pure Γ Φ e τ₁) ->
      has_type Γ Γv Φ ι e (self τ e)
  | TSub :
    forall e τ τ',
      has_type Γ Γv Φ ι e τ' ->
      subtype Γ Γv Φ ι τ' τ ->
      has_type Γ Γv Φ ι e τ.


