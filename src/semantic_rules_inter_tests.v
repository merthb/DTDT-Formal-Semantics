Require Import DTDT.syntax.
Require Import DTDT.machine_inter.
Require Import DTDT.entails_inter.
Require Import DTDT.semantic_rules_inter.

(* Example derivations for the internal judgments. *)

(* Local tactics and lookup lemmas used by the semantic examples. *)
Ltac solve_var :=
  eapply StepVar;
  unfold ctx_add_var, var_ctx_lookup;
  simpl;
  apply lookup_insert; simpl.

Lemma var_lookup_add (Γ : ctx) x (τ : i_ty) e :
  (Γ ,,v x ↦ (τ, e)) !!₁ x = Some (τ, e).
Proof.
  unfold var_ctx_lookup, ctx_add_var. cbn.
  apply lookup_insert.
Qed.

Lemma var_lookup_add_ne (Γ : ctx) y (τ : i_ty) ey x (τ₂ : i_ty) e :
  x <> y ->
  var_ctx_lookup Γ x = Some (τ₂, e) ->
  var_ctx_lookup (ctx_add_var Γ y τ ey) x = Some (τ₂, e).
Proof.
  intros Hneq Hlookup.
  destruct Γ as [[vars consts] store].
  unfold var_ctx_lookup, ctx_add_var in *. simpl in *.
  assert (Hyx : y <> x) by congruence.
  rewrite (lookup_insert_ne vars y x (τ, ey) Hyx).
  exact Hlookup.
Qed.

Definition pure_nat_ctx : ctx :=
  empty_ctx ,,v "n" ↦ (TBase BNat, ENat 2).

Definition ref_nat_ctx : ctx :=
  empty_ctx ,,s "l" ↦ (TBase BNat, ENat 2).

Definition ref_inspecting_fun : i_expr :=
  EFix "f" "r" (TRef (TBase BNat)) (TBase BNat)
    (EIf (EEq (ENat 0) (ENat 0))
         (EPlus (EGet (EVar "r")) (ENat 1))
         (ENat 0)).

(* Example pure typing derivation for a nested boolean/arithmetic formula. *)
Lemma pure_guarded_arithmetic_test :
  pure_nat_ctx ⊢pure
    EImp (EEq (EVar "n") (ENat 2))
         (EEq (EPlus (EVar "n") (ENat 1)) (ENat 3))
    : TBase BBool.
Proof.
  apply PImp.
  - eapply PEq.
    + apply PVar with (τb := TBase BNat) (e := ENat 2).
      * unfold pure_nat_ctx. apply var_lookup_add.
      * reflexivity.
    + apply PNat.
  - eapply PEq.
    + apply PPlus.
      * apply PVar with (τb := TBase BNat) (e := ENat 2).
        -- unfold pure_nat_ctx. apply var_lookup_add.
        -- reflexivity.
      * apply PNat.
    + apply PNat.
Qed.

(* Example semantic subtyping derivation driven by a nontrivial implication witness. *)
Lemma subtype_refinement_implication_test : forall Γ,
  subtype Γ
    (TSet "x" BNat (EEq (EVar "x") (ENat 3)))
    (TSet "x" BNat (EOr (EEq (EVar "x") (ENat 3))
                         (EEq (EVar "x") (ENat 4)))).
Proof.
  intro Γ.
  eapply SSet with (c := 3).
  - apply VSet with (v := ENat 3).
    eapply PEq.
    + apply PVar with (τb := TBase BNat) (e := ENat 3).
      * apply var_lookup_add.
      * reflexivity.
    + apply PNat.
  - apply VSet with (v := ENat 3).
    apply POr.
    + eapply PEq.
      * apply PVar with (τb := TBase BNat) (e := ENat 3).
        -- apply var_lookup_add.
        -- reflexivity.
      * apply PNat.
    + eapply PEq.
      * apply PVar with (τb := TBase BNat) (e := ENat 3).
        -- apply var_lookup_add.
        -- reflexivity.
      * apply PNat.
  - simpl.
    eapply steps_step.
    + eapply StepCtx with (E := ECImpL ECHole (EOr (EEq (EVar "x") (ENat 3)) (EEq (EVar "x") (ENat 4)))).
      eapply StepCtx with (E := ECEqL ECHole (ENat 3)).
      solve_var.
    + eapply steps_step.
      * eapply StepCtx with (E := ECImpL ECHole (EOr (EEq (EVar "x") (ENat 3)) (EEq (EVar "x") (ENat 4)))).
        apply StepEq.
        -- apply BVNat.
        -- apply BVNat.
        -- reflexivity.
      * eapply steps_step.
        -- eapply StepCtx with (E := ECImpR (EBool true) ECHole).
           eapply StepCtx with (E := ECOrL ECHole (EEq (EVar "x") (ENat 4))).
           eapply StepCtx with (E := ECEqL ECHole (ENat 3)).
           solve_var.
        -- eapply steps_step.
           ++ eapply StepCtx with (E := ECImpR (EBool true) ECHole).
              eapply StepCtx with (E := ECOrL ECHole (EEq (EVar "x") (ENat 4))).
              apply StepEq.
              ** apply BVNat.
              ** apply BVNat.
              ** reflexivity.
           ++ eapply steps_step.
              ** eapply StepCtx with (E := ECImpR (EBool true) ECHole).
                 eapply StepCtx with (E := ECOrR (EBool true) ECHole).
                 eapply StepCtx with (E := ECEqL ECHole (ENat 4)).
                 solve_var.
              ** eapply steps_step.
                 --- eapply StepCtx with (E := ECImpR (EBool true) ECHole).
                     eapply StepCtx with (E := ECOrR (EBool true) ECHole).
                     apply StepEq.
                     +++ apply BVNat.
                     +++ apply BVNat.
                     +++ reflexivity.
                 --- eapply steps_step.
                     +++ eapply StepCtx with (E := ECImpR (EBool true) ECHole).
                         apply StepOr.
                     +++ eapply steps_step.
                         *** apply StepImp.
                         *** apply steps_refl.
Qed.

(* Example typing derivation for a conditional that reads from the store. *)
Lemma has_type_reference_conditional_test :
  has_type ref_nat_ctx
    (EIf (EEq (ENat 0) (ENat 0))
         (EPlus (EGet (ELoc "l")) (ENat 1))
         (ENat 0))
    (TBase BNat).
Proof.
  unfold ref_nat_ctx.
  eapply TIf.
  - eapply PEq; apply PNat.
  - apply TPlus.
    + eapply TGet.
      apply TLoc with (v := ENat 2).
      unfold store_ctx_lookup, ctx_add_var, ctx_add_store. cbn.
      apply lookup_insert.
    + apply TNat.
  - apply TNat.
Qed.

(* Example typing derivation for a function that inspects a reference argument. *)
Lemma has_type_reference_inspecting_function_test :
  has_type empty_ctx ref_inspecting_fun
    (TArrDep "r" (TRef (TBase BNat)) (TBase BNat)).
Proof.
  unfold ref_inspecting_fun.
  eapply TFun.
  - simpl. tauto.
  - apply VFunDep.
    + apply VRef. apply VBase.
    + apply VBase.
  - eapply TIf.
    + eapply PEq; apply PNat.
    + apply TPlus.
      * eapply TGet.
        eapply TVar with (v := "r") (e := EVar "r").
        apply var_lookup_add.
      * apply TNat.
    + apply TNat.
Qed.
