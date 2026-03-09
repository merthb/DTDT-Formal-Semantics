Require Import DTDT.syntax.
Require Import DTDT.machine_inter.
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

(* Compute self (TBase BNat) (EVar ("x"%string)).
Compute self (TArr (TBase BNat) (TArr (TBase BNat) (TBase BNat))) (EVar ("+"%string)). *)


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
  ( Γ : ctx)
  : i_expr -> i_ty -> Prop :=
  | PVar :
    forall x τb e,
      Γ !!₁ x = Some (τb, e) ->
      β[ τb ] ->
      has_type_pure Γ (EVar x) τb
  | PNat :
    forall n,
      has_type_pure Γ (ENat n) (TBase BNat)
  | PBool :
    forall b,
      has_type_pure Γ (EBool b) (TBase BBool)
  | PString :
    forall s,
      has_type_pure Γ (EString s) (TBase BString)
  | PUnit :
    forall u,
      has_type_pure Γ (EUnit u) (TBase BUnit)
  | PConst :
    forall c τ e,
      Γ !!₂ c = Some (τ, e) ->
      is_simple_type τ ->
      has_type_pure Γ (EConst c) τ
  | PApp :
    forall e₁ e₂ τ₁ τ₂,
      β[ τ₁ ] ->
      has_type_pure Γ e₁ (TArr τ₁ τ₂) ->
      has_type_pure Γ e₂ τ₁ ->
      has_type_pure Γ (EApp e₁ e₂) τ₂
  | PNot :
    forall b,
      has_type_pure Γ b (TBase BBool) ->
      has_type_pure Γ (ENot b) (TBase BBool)
  | PImp :
    forall b₁ b₂,
      has_type_pure Γ b₁ (TBase BBool) ->
      has_type_pure Γ b₂ (TBase BBool) ->
      has_type_pure Γ (EImp b₁ b₂) (TBase BBool)
  | PAnd :
    forall b₁ b₂,
      has_type_pure Γ b₁ (TBase BBool) ->
      has_type_pure Γ b₂ (TBase BBool) ->
      has_type_pure Γ (EAnd b₁ b₂) (TBase BBool)
  | POr :
    forall b₁ b₂,
      has_type_pure Γ b₁ (TBase BBool) ->
      has_type_pure Γ b₂ (TBase BBool) ->
      has_type_pure Γ (EOr b₁ b₂) (TBase BBool)
  | PPlus :
    forall n₁ n₂,
      has_type_pure Γ n₁ (TBase BNat) ->
      has_type_pure Γ n₂ (TBase BNat) ->
      has_type_pure Γ (EPlus n₁ n₂) (TBase BNat).

Lemma const_lookup_add Γ f τ e :
  (Γ ,,c f ↦ (τ, e)) !!₂ f = Some (τ,e).
Proof.
  unfold const_ctx_lookup.
  unfold ctx_add_const. cbn.
  apply lookup_insert.
Qed.

Lemma var_lookup_add Γ x τ e :
  (Γ ,,v x ↦ (τ, e)) !!₁ x = Some (τ,e).
Proof.
  unfold var_ctx_lookup.
  unfold ctx_add_var. cbn.
  apply lookup_insert.
Qed.

Lemma pure_plus_app_nat :
  has_type_pure ((ctx_add_const empty_ctx "+" (TArr (TBase BNat) (TArr (TBase BNat) (TBase BNat))) (EFix "" "n" (TBase BNat) (TArr (TBase BNat) (TBase BNat)) (EFix "" "m" (TBase BNat) (TBase BNat) (EPlus (EVar "n") (EVar "m"))))) ,,v "n" ↦ (TBase BNat, ENat 1)) (EApp (EConst "+"%string) (ENat 1)) (TArr (TBase BNat) (TBase BNat)).
Proof.
  apply PApp with (τ₁ := TBase BNat).
  reflexivity.
  eapply PConst.
  apply const_lookup_add.
  reflexivity.
  apply PNat.
Qed.

Lemma pure_plus_app_var :
  has_type_pure ((ctx_add_const empty_ctx "+" (TArr (TBase BNat) (TArr (TBase BNat) (TBase BNat))) (EFix "" "n" (TBase BNat) (TArr (TBase BNat) (TBase BNat)) (EFix "" "m" (TBase BNat) (TBase BNat) (EPlus (EVar "n") (EVar "m"))))) ,,v "n" ↦ (TBase BNat, ENat 1)) (EApp (EConst "+"%string) (EVar "n")) (TArr (TBase BNat) (TBase BNat)).
Proof.
  apply PApp with (τ₁ := TBase BNat).
  reflexivity.
  eapply PConst.
  apply const_lookup_add.
  reflexivity.
  eapply PVar.
  apply var_lookup_add.
  reflexivity.
Qed.

(* --- Well-formed type checking ------------------------------------------------------ *)

Inductive ty_valid
  (Γ : ctx)
  : i_ty -> Prop :=
  | VBase :
    forall (τb : BaseT),
      ty_valid Γ (TBase τb)
  | VSet :
    forall var (τb : BaseT) e v,
      has_type_pure (ctx_add_var Γ var (TBase τb) v) e (TBase BBool) ->
      ty_valid Γ (TSet var τb e)
  | VFun :
    forall τ₁ τ₂,
      ty_valid Γ τ₁ ->
      ty_valid Γ τ₂ ->
      ty_valid Γ (TArr τ₁ τ₂)
  | VFunDep :
    forall var τ₁ τ₂ v,
      ty_valid Γ τ₁ ->
      ty_valid (ctx_add_var Γ var τ₁ v) τ₂ ->
      ty_valid Γ (TArrDep var τ₁ τ₂)
  | VPair :
    forall τ₁ τ₂,
      ty_valid Γ τ₁ ->
      ty_valid Γ τ₂ ->
      ty_valid Γ (TProd τ₁ τ₂)
  | VRef :
    forall τ₁,
      ty_valid Γ τ₁ ->
      ty_valid Γ (TRef τ₁).

(* --- Subtyping ---------------------------------------------------------------------- *)

Definition entails (Γ : ctx) (e : i_expr) : Prop :=
  eval (Γ, e) (Γ, (EBool true)).
Notation "Γ ⊨ e" := (entails Γ e) (at level 80).

(* Should this be on surface level? In paper there's a rule for dereferation too *)
Inductive subtype 
  (Γ : ctx) :
  i_ty -> i_ty -> Prop :=
  | SBase :
    forall b,
      subtype Γ (TBase b) (TBase b)
  | SSet :
    forall var τb e₁ e₂ (c : (base_to_set τb)),
      ty_valid Γ (TSet var τb e₁) ->
      ty_valid Γ (TSet var τb e₂) ->
      (ctx_add_var Γ var (TBase τb) (make_expr τb c)) ⊨ (EImp e₁ e₂) ->
      subtype Γ (TSet var τb e₁) (TSet var τb e₂)
  | SSetBase :
    forall var τb e,
      ty_valid Γ (TSet var τb e) ->
      subtype Γ (TSet var τb e) (TBase τb)
  | SBaseSet :
    forall var τb e (c : (base_to_set τb)),
      ty_valid Γ (TSet var τb e) ->
      (ctx_add_var Γ var (TBase τb) (make_expr τb c)) ⊨ e ->
      subtype Γ (TBase τb) (TSet var τb e)
  | SFun :
    forall τ₁ τ₁' τ₂ τ₂',
      subtype Γ τ₁' τ₁ ->
      subtype Γ τ₂ τ₂' ->
      subtype Γ (TArr τ₁ τ₂) (TArr τ₁' τ₂')
  | SFunDep :
    forall var τ₁ τ₁' τ₂ τ₂' v,
      subtype Γ τ₁' τ₁ ->
      subtype (ctx_add_var Γ var τ₁' v) τ₂ τ₂' ->
      subtype Γ (TArrDep var τ₁ τ₂) (TArrDep var τ₁' τ₂')
  | SPair :
    forall τ₁ τ₁' τ₂ τ₂',
      subtype Γ τ₁ τ₁' ->
      subtype Γ τ₂ τ₂' ->
      subtype Γ (TProd τ₁ τ₂) (TProd τ₁' τ₂')
  | SRef :
    forall τ τ',
      subtype Γ τ τ' ->
      subtype Γ τ' τ ->
      subtype Γ (TRef τ) (TRef τ').

Lemma set_sub_test : forall Γ, subtype Γ (TSet "x" BBool (ENot (EVar "x"))) (TSet "x" BBool (EBool true)).
Proof.
intro Γ.
eapply SSet with (c := true).
apply VSet with (v := EBool true).
apply PNot.
apply PVar with (e := EBool true).
unfold var_ctx_lookup.
apply var_lookup_add.
reflexivity.
apply VSet with (v := ENat 1).
apply PBool.
simpl.
econstructor.
apply StepCtx with (E := ECImpL ECHole (EBool true)).
apply StepCtx with (E := ECNot ECHole).
solve_var.
econstructor. simpl.
apply StepCtx with (E := ECImpL ECHole (EBool true)).
apply StepNot. simpl.
econstructor.
apply StepImp. rewrite implb_true_r.
apply steps_refl.
Qed.

(* two equivalent sets *)
Lemma set_sub_test_without_var_use : forall Γ, subtype Γ (TSet "x" BBool (ENot (EBool false))) (TSet "x" BBool (EBool true)).
Proof.
intros.
apply SSet with (c := true).
apply VSet with (v := ENat 0).
apply PNot.
apply PBool.
apply VSet with (v := ENat 0).
apply PBool.
simpl.
econstructor.
apply StepCtx with (E := ECImpL ECHole (EBool true)).
apply StepNot. simpl.
econstructor.
apply StepImp.
simpl. apply steps_refl.
Qed.

(* actual subsets *)
Lemma set_sub_test_without_var_use2 : forall Γ, subtype Γ (TSet "x" BBool (ENot (EBool true))) (TSet "x" BBool (EBool true)).
Proof.
intros.
apply SSet with (c := true).
apply VSet with (v := EBool false).
apply PNot.
apply PBool.
apply VSet with (v := EBool false).
apply PBool.
simpl.
econstructor.
apply StepCtx with (E := ECImpL ECHole (EBool true)).
apply StepNot. simpl.
econstructor.
apply StepImp.
simpl. apply steps_refl.
Qed.

Lemma base_sub_set_test : forall Γ, subtype Γ (TBase BBool) (TSet "x" BBool (EOr (EBool true) (EVar "x"))).
Proof.
intros.
eapply SBaseSet with (c := true).
apply VSet with (v := ENat 2).
apply POr.
apply PBool.
apply PVar with (e := ENat 2).
unfold var_ctx_lookup.
apply var_lookup_add.
reflexivity.
simpl.
econstructor.
apply StepCtx with (E := ECOrR (EBool true) ECHole).
solve_var.
econstructor. simpl.
apply StepOr. simpl.
apply steps_refl.
Qed.

(* --- Type rules for the internal language ------------------------------------------- *)

Inductive has_type
  ( Γ : ctx)
  : i_expr -> i_ty -> Prop :=
  | TString :
    forall s,
      has_type Γ (EString s) (TBase BString)
  | TNat :
    forall n,
      has_type Γ (ENat n) (TBase BNat)
  | TBool :
    forall b,
      has_type Γ (EBool b) (TBase BBool)
  | TUnit :
    forall u,
      has_type Γ (EUnit u) (TBase BUnit)
  | TConst :
    forall c τ e,
      Γ !!₂ c = Some (τ, e) ->
      has_type Γ (EConst c) τ
  | TVar :
    forall v τ e,
      Γ !!₁ v = Some (τ, e) ->
      has_type Γ (EVar v) τ
  | TFail :
    forall τ,
      ty_valid Γ τ ->
      has_type Γ EFail τ
  | TFun :
    forall f x τ₁ τ₂ e exp,
      ty_valid Γ (TArrDep x τ₁ τ₂) ->
      has_type (ctx_add_const Γ f (TArrDep x τ₁ τ₂) exp) e τ₂ ->
      has_type Γ (EFix f x τ₁ τ₂ e) (TArrDep x τ₁ τ₂)
  | TAppPure :
    forall e₁ e₂ x τ₁ τ₂,
      has_type Γ e₂ τ₁ ->
      (forall τ₃, has_type_pure Γ e₂ τ₃) ->
      has_type Γ e₁ (TArrDep x τ₁ τ₂) ->
      has_type Γ (expr_subst x e₂ e₁) τ₂ ->
      has_type Γ (EApp e₁ e₂) τ₂
  | TAppImPure :
    forall e₁ e₂ τ₁ τ₂,
      has_type Γ e₂ τ₁ ->
      has_type Γ e₁ (TArr τ₁ τ₂) ->
      has_type Γ (EApp e₁ e₂) τ₂
  | TPlus :
    forall e₁ e₂,
      has_type Γ e₁ (TBase BNat) ->
      has_type Γ e₂ (TBase BNat) ->
      has_type Γ (EPlus e₁ e₂) (TBase BNat)
  | TPair :
    forall e₁ e₂ τ₁ τ₂,
      has_type Γ e₁ τ₁ ->
      has_type Γ e₂ τ₂ ->
      has_type Γ (EPair e₁ e₂) (TProd τ₁ τ₂)
  | TFst :
    forall e τ₁ τ₂,
      has_type Γ e (TProd τ₁ τ₂) ->
      has_type Γ (EFst e) τ₁
  | TSnd :
    forall e τ₁ τ₂,
      has_type Γ e (TProd τ₁ τ₂) ->
      has_type Γ (ESnd e) τ₂
  | TIf :
    forall e e₁ e₂ τ u,
      has_type_pure Γ e (TBase BBool) ->
      has_type (ctx_add_var Γ u (TBase BBool) e) e₁ τ ->
      has_type (ctx_add_var Γ u (TBase BBool) (ENot e)) e₂ τ ->
      has_type Γ (EIf e e₁ e₂) τ
  | TSelf :
    forall e τ,
      has_type Γ e τ ->
      (forall τ₁, has_type_pure Γ e τ₁) ->
      has_type Γ e (self τ e)
  | TSub :
    forall e τ τ',
      has_type Γ e τ' ->
      subtype Γ τ' τ ->
      has_type Γ e τ.


