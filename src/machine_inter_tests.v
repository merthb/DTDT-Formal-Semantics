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
   EIf (EEq (EGet (ELoc "l")) (ENat 2))
       (ESet (ELoc "l") (ENat 5))
       EFail) ↠*
  (((Γ ,,s "l" ↦ (TBase BNat, ENat 2)) ,,s "l" ↦ (TBase BNat, ENat 5)), EUnit tt).
Proof.
  intros Γ.
  unfold machine_ref_ctx.
  eapply steps_step.
  - eapply StepCtx with (E := ECIf ECHole (ESet (ELoc "l") (ENat 5)) EFail).
    eapply StepCtx with (E := ECEqL ECHole (ENat 2)).
    eapply StepGet with (τ := TBase BNat) (v := ENat 2).
    unfold store_ctx_lookup, ctx_add_store. cbn.
    apply lookup_insert.
  - eapply steps_step.
    + eapply StepCtx with (E := ECIf ECHole (ESet (ELoc "l") (ENat 5)) EFail).
      apply StepEq.
      * apply BVNat.
      * apply BVNat.
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
  EApp machine_ref_update_fun (ELoc "l")) ↠*
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
    + eapply StepCtx with (E := ECIf ECHole (ESet (ELoc "l") (ENat 7)) EFail).
      eapply StepCtx with (E := ECEqL ECHole (ENat 2)).
      eapply StepGet with (τ := TBase BNat) (v := ENat 2).
      unfold store_ctx_lookup, ctx_add_store. cbn.
      apply lookup_insert.
    + eapply steps_step.
      * eapply StepCtx with (E := ECIf ECHole (ESet (ELoc "l") (ENat 7)) EFail).
        apply StepEq.
        -- apply BVNat.
        -- apply BVNat.
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

Definition rewards_ctx (Γ : ctx) : ctx :=
  (Γ ,,s "points" ↦ (TBase BNat, ENat 9))
    ,,s "member" ↦ (TBase BBool, EBool true).

Lemma rewards_points_lookup : forall Γ,
  rewards_ctx Γ !!₃ "points" = Some (TBase BNat, ENat 9).
Proof.
  intro Γ.
  unfold rewards_ctx, store_ctx_lookup, ctx_add_store.
  cbn.
  apply lookup_insert_Some.
  right.
  split.
  - intros Hmember_points.
    inversion Hmember_points.
  - apply lookup_insert.
Qed.

Lemma rewards_member_lookup : forall Γ,
  rewards_ctx Γ !!₃ "member" = Some (TBase BBool, EBool true).
Proof.
  intro Γ.
  unfold rewards_ctx, store_ctx_lookup, ctx_add_store. cbn.
  apply lookup_insert.
Qed.

Definition award_bonus_fun : i_expr :=
  EFix "award_bonus" "account"
    (TProd (TRef (TBase BNat)) (TRef (TBase BBool)))
    (TBase BUnit)
    (EIf (EGet (ESnd (EVar "account")))
         (EIf (EEq (EGet (EFst (EVar "account"))) (ENat 9))
              (ESet (EFst (EVar "account")) (ENat 10))
              EFail)
         EFail).

Definition award_bonus_program : i_expr :=
  EApp award_bonus_fun (EPair (ELoc "points") (ELoc "member")).

(* Example of a more realistic program: if a customer is a member and has
   exactly 9 points, award one bonus point by updating the points reference. *)
Lemma eval_award_bonus_program_test : forall Γ,
  (rewards_ctx Γ, award_bonus_program) ↠*
  ((((Γ ,,s "points" ↦ (TBase BNat, ENat 9))
      ,,s "member" ↦ (TBase BBool, EBool true))
      ,,s "points" ↦ (TBase BNat, ENat 10)), EUnit tt).
Proof.
  intros Γ.
  unfold rewards_ctx, award_bonus_program, award_bonus_fun.
  eapply steps_step.
  - apply StepFix.
    apply VPair.
    + apply VLoc with (τ := TBase BNat) (v := ENat 9).
      apply rewards_points_lookup.
    + apply VLoc with (τ := TBase BBool) (v := EBool true).
      apply rewards_member_lookup.
  - simpl.
    eapply steps_step.
    + eapply StepCtx with (E := ECIf (ECGet ECHole) _ EFail).
      apply StepSnd.
      * apply VLoc with (τ := TBase BNat) (v := ENat 9).
        apply rewards_points_lookup.
      * apply VLoc with (τ := TBase BBool) (v := EBool true).
        apply rewards_member_lookup.
    + eapply steps_step.
      * eapply StepCtx with (E := ECIf ECHole _ EFail).
        eapply StepGet with (τ := TBase BBool) (v := EBool true).
        apply rewards_member_lookup.
      * eapply steps_step.
        -- apply StepIfTrue.
        -- eapply steps_step.
           ++ eapply StepCtx with (E := ECIf (ECEqL (ECGet ECHole) (ENat 9)) (ESet (EFst (EPair (ELoc "points") (ELoc "member"))) (ENat 10)) EFail).
              apply StepFst.
              ** apply VLoc with (τ := TBase BNat) (v := ENat 9).
                 apply rewards_points_lookup.
              ** apply VLoc with (τ := TBase BBool) (v := EBool true).
                 apply rewards_member_lookup.
           ++ eapply steps_step.
              ** eapply StepCtx with (E := ECIf (ECEqL ECHole (ENat 9)) (ESet (EFst (EPair (ELoc "points") (ELoc "member"))) (ENat 10)) EFail).
                 eapply StepGet with (τ := TBase BNat) (v := ENat 9).
                 apply rewards_points_lookup.
              ** eapply steps_step.
                 --- eapply StepCtx with (E := ECIf ECHole (ESet (EFst (EPair (ELoc "points") (ELoc "member"))) (ENat 10)) EFail).
                     apply StepEq.
                     +++ apply BVNat.
                     +++ apply BVNat.
                     +++ reflexivity.
                 --- eapply steps_step.
                     +++ apply StepIfTrue.
                     +++ eapply steps_step.
                         { eapply StepCtx with (E := ECSetL ECHole (ENat 10)).
                           apply StepFst.
                           - apply VLoc with (τ := TBase BNat) (v := ENat 9).
                             apply rewards_points_lookup.
                           - apply VLoc with (τ := TBase BBool) (v := EBool true).
                             apply rewards_member_lookup. }
                         { eapply steps_step.
                           - eapply StepSet with (τ := TBase BNat) (e := ENat 9).
                             + apply VNat.
                             + apply rewards_points_lookup.
                           - apply steps_refl. }
Qed.
