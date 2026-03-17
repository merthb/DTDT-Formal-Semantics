Require Import DTDT.syntax.
Require Import DTDT.machine_inter.

(* Example evaluations for the machine semantics. *)

Definition machine_ref_ctx (Γ : ctx) : ctx :=
  Γ ,,s "l" ↦ (TBase BNat, ENat 2).

Definition machine_ref_update_fun : i_expr :=
  EFix "f" "r" (TRef (TBase BNat)) (TBase BUnit)
    (EIf (EEq (EGet (EVar "r")) (ENat 2))
         (ESet (EVar "r") (ENat 7))
         EFail).

(* Example evaluation of a conditional that reads a reference and updates the store. *)
Lemma eval_if_get_set_test : forall Γ,
  (machine_ref_ctx Γ,
   EIf (EEq (EGet (EVar "l")) (ENat 2))
       (ESet (EVar "l") (ENat 5))
       EFail) ↠*
  (((Γ ,,s "l" ↦ (TBase BNat, ENat 2)) ,,s "l" ↦ (TBase BNat, ENat 5)), EUnit tt).
Proof.
  intros Γ.
  unfold machine_ref_ctx.
  eapply steps_step.
  - eapply StepCtx with (E := ECIf ECHole (ESet (EVar "l") (ENat 5)) EFail).
    eapply StepCtx with (E := ECEqL ECHole (ENat 2)).
    eapply StepGet with (τ := TBase BNat) (v := ENat 2).
    unfold store_ctx_lookup, ctx_add_store. cbn.
    apply lookup_insert.
  - eapply steps_step.
    + eapply StepCtx with (E := ECIf ECHole (ESet (EVar "l") (ENat 5)) EFail).
      apply StepEq.
      * apply VNat.
      * apply VNat.
      * reflexivity.
    + eapply steps_step.
      * apply StepIfTrue.
      * eapply steps_step.
        -- eapply StepSet with (τ := TBase BNat) (e := ENat 2).
           ++ apply VNat.
           ++ unfold store_ctx_lookup, ctx_add_store. cbn.
              apply lookup_insert.
        -- apply steps_refl.
Qed.

(* Example evaluation of an application whose body performs a stateful reference update. *)
Lemma eval_app_with_store_effect_test : forall Γ,
  (machine_ref_ctx Γ,
   EApp machine_ref_update_fun (EVar "l")) ↠*
  (((Γ ,,s "l" ↦ (TBase BNat, ENat 2)) ,,s "l" ↦ (TBase BNat, ENat 7)), EUnit tt).
Proof.
  intros Γ.
  unfold machine_ref_ctx, machine_ref_update_fun.
  eapply steps_step.
  - apply StepFix.
    apply VLoc with (τ := TBase BNat) (v := ENat 2).
    unfold store_ctx_lookup, ctx_add_store. cbn.
    apply lookup_insert.
  - simpl.
    eapply steps_step.
    + eapply StepCtx with (E := ECIf ECHole (ESet (EVar "l") (ENat 7)) EFail).
      eapply StepCtx with (E := ECEqL ECHole (ENat 2)).
      eapply StepGet with (τ := TBase BNat) (v := ENat 2).
      unfold store_ctx_lookup, ctx_add_store. cbn.
      apply lookup_insert.
    + eapply steps_step.
      * eapply StepCtx with (E := ECIf ECHole (ESet (EVar "l") (ENat 7)) EFail).
        apply StepEq.
        -- apply VNat.
        -- apply VNat.
        -- reflexivity.
      * eapply steps_step.
        -- apply StepIfTrue.
        -- eapply steps_step.
           ++ eapply StepSet with (τ := TBase BNat) (e := ENat 2).
              ** apply VNat.
              ** unfold store_ctx_lookup, ctx_add_store. cbn.
                 apply lookup_insert.
           ++ apply steps_refl.
Qed.
