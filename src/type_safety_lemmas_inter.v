Require Import DTDT.syntax.
Require Import DTDT.entails_inter.
Require Import DTDT.machine_inter.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.foundational_lemmas_inter.

(* ==================== PAPER LEMMA 9 ====================
   If ∅ ⊢pure e : τ and e → e'', then ∅ ⊢pure e'' : τ. *)
Lemma pure_step_ctx_preservation :
  forall G1 G2 e e' E t,
    step (G1, e) (G2, e') ->
    (forall t, has_type_pure empty_ctx e t -> has_type_pure empty_ctx e' t) ->
    has_type_pure empty_ctx (plug E e) t ->
    has_type_pure empty_ctx (plug E e') t.
Proof.
  intros G1 G2 e e' E t Hstep IH.
  revert t.
  induction E; intros t Hpure; simpl in *;
    try solve [inversion Hpure];
    try solve [exfalso; eapply has_type_pure_empty_ctx_app_absurd; exact Hpure].
  - exact (IH _ Hpure).
  - inversion Hpure; subst.
    apply PPlus.
    + match goal with
      | Hsub : has_type_pure empty_ctx (plug E e) (TBase BNat) |- _ => exact (IHE _ Hsub)
      end.
    + assumption.
  - inversion Hpure; subst.
    apply PPlus.
    + assumption.
    + match goal with
      | Hsub : has_type_pure empty_ctx (plug E e) (TBase BNat) |- _ => exact (IHE _ Hsub)
      end.
  - inversion Hpure; subst.
    apply PNot.
    match goal with
    | Hsub : has_type_pure empty_ctx (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
    end.
  - inversion Hpure; subst.
    apply PAnd.
    + match goal with
      | Hsub : has_type_pure empty_ctx (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
    + assumption.
  - inversion Hpure; subst.
    apply PAnd.
    + assumption.
    + match goal with
      | Hsub : has_type_pure empty_ctx (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
  - inversion Hpure; subst.
    apply POr.
    + match goal with
      | Hsub : has_type_pure empty_ctx (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
    + assumption.
  - inversion Hpure; subst.
    apply POr.
    + assumption.
    + match goal with
      | Hsub : has_type_pure empty_ctx (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
  - inversion Hpure; subst.
    apply PImp.
    + match goal with
      | Hsub : has_type_pure empty_ctx (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
    + assumption.
  - inversion Hpure; subst.
    apply PImp.
    + assumption.
    + match goal with
      | Hsub : has_type_pure empty_ctx (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
  - inversion Hpure; subst.
    match goal with
    | Hsub : has_type_pure empty_ctx (plug E e) (TBase ?tb) |- _ =>
        match goal with
        | Hother : has_type_pure empty_ctx ?er (TBase tb) |- _ =>
            eapply (PEq empty_ctx (plug E e') er tb);
            [ exact (IHE _ Hsub) | exact Hother ]
        end
    end.
  - inversion Hpure; subst.
    match goal with
    | Hsub : has_type_pure empty_ctx (plug E e) (TBase ?tb) |- _ =>
        match goal with
        | Hother : has_type_pure empty_ctx ?el (TBase tb) |- _ =>
            eapply (PEq empty_ctx el (plug E e') tb);
            [ exact Hother | exact (IHE _ Hsub) ]
        end
    end.
Qed.

Lemma pure_fail_ctx_absurd :
  forall E t,
    has_type_pure empty_ctx (plug E EFail) t ->
    False.
Proof.
  induction E; intros t Hpure; simpl in *;
    try solve [inversion Hpure];
    try solve [exfalso; eapply has_type_pure_empty_ctx_app_absurd; exact Hpure].
  all: inversion Hpure; subst;
    match goal with
    | IHE : forall t, has_type_pure empty_ctx (plug _ EFail) t -> False, Hsub : has_type_pure empty_ctx (plug _ EFail) _ |- _ => exact (IHE _ Hsub)
    end.
Qed.

Lemma preservation_pure_terms_sigma :
  forall sigma1 sigma2,
    step sigma1 sigma2 ->
    forall τ,
      empty_ctx ⊢pure (snd sigma1) : τ ->
      empty_ctx ⊢pure (snd sigma2) : τ.
Proof.
  intros sigma1 sigma2 Hstep.
  induction Hstep; intros t Hpure; simpl in *.
  - eapply pure_step_ctx_preservation; eauto.
  - exfalso. eapply has_type_pure_empty_ctx_app_absurd. exact Hpure.
  - inversion Hpure; subst.
    simpl in H. discriminate.
  - exfalso. eapply has_type_pure_empty_ctx_app_absurd. exact Hpure.
  - inversion Hpure.
  - inversion Hpure.
  - inversion Hpure.
  - inversion Hpure.
  - inversion Hpure.
  - inversion Hpure.
  - inversion Hpure.
  - exfalso. eapply pure_fail_ctx_absurd. exact Hpure.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PNat.
Qed.

Lemma preservation_pure_terms :
  forall Γ e e' τ,
    step (Γ, e) (Γ, e') ->
    empty_ctx ⊢pure e : τ ->
    empty_ctx ⊢pure e' : τ.
Proof.
  intros Γ e e' τ Hstep Hpure.
  exact (preservation_pure_terms_sigma (Γ, e) (Γ, e') Hstep τ Hpure).
Qed.

(* ==================== PAPER LEMMA 11 ====================
   If ∅ ⊢ v : bool and v is a value, then v = true or v = false. *)
Lemma subtype_bool_essential_inv :
  forall G t1 t2,
    subtype G t1 t2 ->
    essential_type t2 = TBase BBool ->
    essential_type t1 = TBase BBool.
Proof.
  intros G t1 t2 Hsub.
  induction Hsub; intro Hbool; simpl in *; try discriminate; inversion Hbool; reflexivity.
Qed.

Lemma canonical_forms_bool_essential :
  forall v ty,
    has_type empty_ctx v ty ->
    DTDT.machine_inter.value empty_ctx v ->
    essential_type ty = TBase BBool ->
    v = EBool true \/ v = EBool false.
Proof.
  intros v ty Hty Hv Hbool.
  remember empty_ctx as G eqn:HeqG.
  revert HeqG Hv Hbool.
  induction Hty; intros HeqG Hv Hbool; subst; simpl in Hbool;
    try discriminate;
    try solve [inversion Hv; subst; try discriminate].
  - destruct b; [left | right]; reflexivity.
  - destruct τ; simpl in Hbool; try discriminate.
    { destruct b; inversion Hbool; subst; exact (IHHty eq_refl Hv eq_refl). }
    { inversion Hbool; subst; exact (IHHty eq_refl Hv eq_refl). }
    { destruct τ1; simpl in Hbool; discriminate. }
  - apply (IHHty eq_refl Hv).
    eapply subtype_bool_essential_inv; eauto.
Qed.

Lemma canonical_forms_bool :
  forall v,
    has_type empty_ctx v (TBase BBool) ->
    DTDT.machine_inter.value empty_ctx v ->
    v = EBool true \/ v = EBool false.
Proof.
  intros v Hty Hv.
  eapply canonical_forms_bool_essential; eauto.
Qed.

(* Paper Lemma 11, pair canonical forms.
   If empty ? v : tau1 * tau2 and v is a value, then v = (v1, v2). *)
Lemma canonical_forms_pair :
  forall v tau1 tau2,
    has_type empty_ctx v (TProd tau1 tau2) ->
    DTDT.machine_inter.value empty_ctx v ->
    exists v1 v2, v = EPair v1 v2.
Proof.
  intros v tau1 tau2 Hty Hv.
  remember empty_ctx as G eqn:HeqG.
  remember (TProd tau1 tau2) as tp eqn:Heqtp.
  revert tau1 tau2 HeqG Heqtp Hv.
  induction Hty; intros tau1' tau2' HeqG Heqtp Hv; inversion Heqtp; subst;
    try solve [inversion Hv; subst; try discriminate].
  - eexists _, _.
    reflexivity.
  - exfalso.
    pose proof (has_type_pure_empty_ctx_base _ _ (H (TProd tau1' tau2'))) as Hbeta.
    simpl in Hbeta.
    contradiction.
  - inversion H; subst; try discriminate.
    exact (IHHty _ _ eq_refl eq_refl Hv).
Qed.

(* Paper Lemma 11, reference canonical forms.
   If empty ? v : tau ref and v is a value, then v is a location in the store. *)
Lemma canonical_forms_ref :
  forall v tau,
    has_type empty_ctx v (TRef tau) ->
    DTDT.machine_inter.value empty_ctx v ->
    exists l stored,
      v = EVar l /\ store_ctx_lookup empty_ctx l = Some (tau, stored).
Proof.
  intros v tau Hty Hv.
  remember empty_ctx as G eqn:HeqG.
  remember (TRef tau) as tr eqn:Heqtr.
  revert tau HeqG Heqtr Hv.
  induction Hty; intros tau' HeqG Heqtr Hv; inversion Heqtr; subst;
    try solve [inversion Hv; subst; try discriminate].
  - match goal with
    | Hself : self ?t ?e = TRef ?t' |- _ =>
        apply self_ref_inv in Hself;
        inversion Hself; subst
    end.
    eapply IHHty; eauto.
  - inversion H; subst; try discriminate.
    destruct (IHHty _ eq_refl eq_refl Hv) as [l [stored [Heq Hlookup]]].
    subst.
    unfold store_ctx_lookup, empty_ctx in Hlookup.
    simpl in Hlookup.
    discriminate.
Qed.

Lemma store_well_typed_empty :
  store_well_typed empty_ctx.
Proof.
  constructor.
  intros l t v Hlookup.
  unfold store_ctx_lookup, empty_ctx in Hlookup.
  simpl in Hlookup.
  inversion Hlookup.
Qed.


(* ==================== PAPER THEOREM 4 ====================
   Implementation-aligned preservation: stepping preserves typing together with
   the store well-typedness invariant needed by the reference fragment. *)
Theorem preservation :
  forall G e G' e' tau,
    store_well_typed G ->
    has_type G e tau ->
    step (G, e) (G', e') ->
    has_type G' e' tau /\ store_well_typed G'.
Admitted.

(* ==================== PAPER THEOREM 5 ====================
   If ∅ ⊢ e : τ, then e is a value, e = fail, or there exists e' with e → e'. *)
Theorem progress :
  forall e τ,
    has_type empty_ctx e τ ->
    DTDT.machine_inter.value empty_ctx e \/
    e = EFail \/
    exists G' e', step (empty_ctx, e) (G', e').
Admitted.

(* ==================== PAPER THEOREM 1 ====================
   Type safety: if ∅ ⊢ e : τ and (∅, e) ↠* (∅, e₀), then e₀ is a value,
   e₀ = fail, or there exists a further step from e₀. *)
Theorem paper_theorem_1_type_safety :
  forall e τ G₀ e₀,
    has_type empty_ctx e τ ->
    (empty_ctx, e) ↠* (G₀, e₀) ->
    DTDT.machine_inter.value G₀ e₀ \/
    e₀ = EFail \/
    exists G₁ e₁, step (G₀, e₀) (G₁, e₁).
Admitted.
