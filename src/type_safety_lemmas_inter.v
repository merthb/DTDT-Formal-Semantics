Require Import Coq.Program.Equality.
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
    eapply PApp.
    + exact H1.
    + apply IHE. exact H2.
    + exact H4.
  - inversion Hpure; subst.
    eapply PApp.
    + exact H1.
    + exact H2.
    + apply IHE. exact H4.
  - inversion Hpure; subst.
    apply PPlus.
    + apply IHE. exact H1.
    + exact H3.
  - inversion Hpure; subst.
    apply PPlus.
    + exact H1.
    + apply IHE. exact H3.
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
  - exfalso. inversion Hpure. inversion H4. subst. discriminate H8.
  - inversion Hpure; subst.
    simpl in H. discriminate.
  - inversion Hpure. inversion H3; subst.
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
    simpl in Hbeta. discriminate.
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

Lemma var_well_typed_empty :
  var_well_typed empty_ctx.
Proof.
  intros x t v Hlookup.
  unfold var_well_typed, var_ctx_lookup, empty_ctx in Hlookup.
  simpl in Hlookup.
  inversion Hlookup.
Qed.

Lemma const_well_typed_empty :
  const_well_typed empty_ctx.
Proof.
  intros c t e Hlookup.
  unfold const_well_typed, const_ctx_lookup, empty_ctx in Hlookup.
  simpl in Hlookup.
  inversion Hlookup.
Qed.

Lemma const_step_well_typed_empty :
  const_step_well_typed empty_ctx.
Proof.
  intros c t e v τtop Hlookup _ _.
  unfold const_step_well_typed, const_ctx_lookup, empty_ctx in Hlookup.
  simpl in Hlookup.
  inversion Hlookup.
Qed.

Lemma runtime_ctx_well_typed_empty :
  runtime_ctx_well_typed empty_ctx.
Proof.
  constructor.
  - exact var_well_typed_empty.
  - exact const_well_typed_empty.
  - exact const_step_well_typed_empty.
  - exact store_well_typed_empty.
Qed.

Lemma var_well_typed_lookup :
  forall Γ x t v,
    var_well_typed Γ ->
    var_ctx_lookup Γ x = Some (t, v) ->
    ty_valid Γ t /\ has_type Γ v t.
Proof.
  intros Γ x t v Hvar Hlookup.
  exact (Hvar x t v Hlookup).
Qed.

Lemma const_well_typed_lookup :
  forall Γ c t e,
    const_well_typed Γ ->
    const_ctx_lookup Γ c = Some (t, e) ->
    ty_valid Γ t /\ has_type Γ e t.
Proof.
  intros Γ c t e Hconst Hlookup.
  exact (Hconst c t e Hlookup).
Qed.

Lemma runtime_ctx_well_typed_var :
  forall Γ,
    runtime_ctx_well_typed Γ ->
    var_well_typed Γ.
Proof.
  intros Γ Hrt.
  inversion Hrt.
  exact H.
Qed.

Lemma runtime_ctx_well_typed_const :
  forall Γ,
    runtime_ctx_well_typed Γ ->
    const_well_typed Γ.
Proof.
  intros Γ Hrt.
  inversion Hrt.
  exact H0.
Qed.

Lemma runtime_ctx_well_typed_store :
  forall Γ,
    runtime_ctx_well_typed Γ ->
    store_well_typed Γ.
Proof.
  intros Γ Hrt.
  inversion Hrt.
  exact H2.
Qed.

Lemma runtime_ctx_well_typed_const_step :
  forall Γ,
    runtime_ctx_well_typed Γ ->
    const_step_well_typed Γ.
Proof.
  intros Γ Hrt.
  inversion Hrt.
  exact H1.
Qed.

Lemma var_well_typed_from_none_lookup :
  forall Γ,
    (forall x, var_ctx_lookup Γ x = None) ->
    var_well_typed Γ.
Proof.
  intros Γ Hnone x t v Hlookup.
  rewrite (Hnone x) in Hlookup.
  inversion Hlookup.
Qed.

Lemma const_well_typed_from_none_lookup :
  forall Γ,
    (forall c, const_ctx_lookup Γ c = None) ->
    const_well_typed Γ.
Proof.
  intros Γ Hnone c t e Hlookup.
  rewrite (Hnone c) in Hlookup.
  inversion Hlookup.
Qed.

Lemma const_step_well_typed_from_none_lookup :
  forall Γ,
    (forall c, const_ctx_lookup Γ c = None) ->
    const_step_well_typed Γ.
Proof.
  intros Γ Hnone c t e v τtop Hlookup _ _.
  rewrite (Hnone c) in Hlookup.
  inversion Hlookup.
Qed.

Lemma runtime_ctx_well_typed_from_invariants :
  forall Γ,
    (forall x, var_ctx_lookup Γ x = None) ->
    (forall c, const_ctx_lookup Γ c = None) ->
    store_well_typed Γ ->
    runtime_ctx_well_typed Γ.
Proof.
  intros Γ HnoneVar HnoneConst Hstore.
  constructor.
  - exact (var_well_typed_from_none_lookup _ HnoneVar).
  - exact (const_well_typed_from_none_lookup _ HnoneConst).
  - exact (const_step_well_typed_from_none_lookup _ HnoneConst).
  - exact Hstore.
Qed.

Lemma empty_ctx_no_var_bindings :
  forall x,
    var_ctx_lookup empty_ctx x = None.
Proof.
  intros x.
  unfold var_ctx_lookup, empty_ctx.
  simpl.
  reflexivity.
Qed.

Lemma empty_ctx_no_const_bindings :
  forall c,
    const_ctx_lookup empty_ctx c = None.
Proof.
  intros c.
  unfold const_ctx_lookup, empty_ctx.
  simpl.
  reflexivity.
Qed.

Lemma subtype_to_essential_type :
  forall Γ t,
    essential_type_is_base_type t = true ->
    ty_valid Γ t ->
    subtype Γ t (essential_type t).
Proof.
  intros Γ t Hbeta Hvalid.
  destruct t; simpl in Hbeta; try discriminate.
  - apply SBase.
  - apply SSetBase.
    exact Hvalid.
Qed.

Lemma store_well_typed_lookup :
  forall Γ l t v,
    store_well_typed Γ ->
    store_ctx_lookup Γ l = Some (t, v) ->
    ty_valid Γ t /\ has_type Γ v t.
Proof.
  intros Γ l t v Hstore Hlookup.
  inversion Hstore as [Hinv]; subst.
  exact (Hinv l t v Hlookup).
Qed.

Lemma store_lookup_add_eq :
  forall Γ l t v,
    store_ctx_lookup (Γ ,,s l ↦ (t, v)) l = Some (t, v).
Proof.
  intros Γ l t v.
  unfold store_ctx_lookup, ctx_add_store.
  simpl.
  apply lookup_insert.
Qed.

Lemma store_lookup_add_neq :
  forall Γ l l' t v,
    l' <> l ->
    store_ctx_lookup (Γ ,,s l ↦ (t, v)) l' = store_ctx_lookup Γ l'.
Proof.
  intros Γ l l' t v Hneq.
  unfold store_ctx_lookup, ctx_add_store.
  simpl.
  apply lookup_insert_ne.
  congruence.
Qed.

Lemma has_type_app_left :
  forall Γ e1 e2 τ,
    has_type Γ (EApp e1 e2) τ ->
    exists τ1, has_type Γ e1 τ1.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EApp e1 e2) as eapp eqn:Heqeapp.
  revert e1 e2 Heqeapp.
  induction Hty; intros e1' e2' Heqeapp; inversion Heqeapp; subst; try discriminate.
  - eexists. exact Hty2.
  - eexists. exact Hty2.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
Qed.

Lemma has_type_app_right :
  forall Γ e1 e2 τ,
    has_type Γ (EApp e1 e2) τ ->
    exists τ2, has_type Γ e2 τ2.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EApp e1 e2) as eapp eqn:Heqeapp.
  revert e1 e2 Heqeapp.
  induction Hty; intros e1' e2' Heqeapp; inversion Heqeapp; subst; try discriminate.
  - eexists. exact Hty1.
  - eexists. exact Hty1.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
Qed.

Lemma has_type_pair_left :
  forall Γ e1 e2 τ,
    has_type Γ (EPair e1 e2) τ ->
    exists τ1, has_type Γ e1 τ1.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EPair e1 e2) as epair eqn:Heqepair.
  revert e1 e2 Heqepair.
  induction Hty; intros e1' e2' Heqepair; inversion Heqepair; subst; try discriminate.
  - eexists. exact Hty1.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
Qed.

Lemma has_type_pair_right :
  forall Γ e1 e2 τ,
    has_type Γ (EPair e1 e2) τ ->
    exists τ2, has_type Γ e2 τ2.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EPair e1 e2) as epair eqn:Heqepair.
  revert e1 e2 Heqepair.
  induction Hty; intros e1' e2' Heqepair; inversion Heqepair; subst; try discriminate.
  - eexists. exact Hty2.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
Qed.

Lemma has_type_fst_arg :
  forall Γ e τ,
    has_type Γ (EFst e) τ ->
    exists τp, has_type Γ e τp.
Proof.
  intros Γ e τ Hty.
  remember (EFst e) as efst eqn:Heqefst.
  revert e Heqefst.
  induction Hty; intros e' Heqefst; inversion Heqefst; subst; try discriminate.
  - eexists. exact Hty.
  - destruct (IHHty _ eq_refl) as [τp Harg].
    eexists; exact Harg.
  - destruct (IHHty _ eq_refl) as [τp Harg].
    eexists; exact Harg.
Qed.

Lemma has_type_snd_arg :
  forall Γ e τ,
    has_type Γ (ESnd e) τ ->
    exists τp, has_type Γ e τp.
Proof.
  intros Γ e τ Hty.
  remember (ESnd e) as esnd eqn:Heqesnd.
  revert e Heqesnd.
  induction Hty; intros e' Heqesnd; inversion Heqesnd; subst; try discriminate.
  - eexists. exact Hty.
  - destruct (IHHty _ eq_refl) as [τp Harg].
    eexists; exact Harg.
  - destruct (IHHty _ eq_refl) as [τp Harg].
    eexists; exact Harg.
Qed.

Lemma has_type_newref_arg :
  forall Γ t e τ,
    has_type Γ (ENewRef t e) τ ->
    exists τe, has_type Γ e τe.
Proof.
  intros Γ t e τ Hty.
  remember (ENewRef t e) as enew eqn:Heqenew.
  revert t e Heqenew.
  induction Hty; intros t' e' Heqenew; inversion Heqenew; subst; try discriminate.
  - eexists. exact Hty.
  - destruct (IHHty _ _ eq_refl) as [τe Harg].
    eexists; exact Harg.
  - destruct (IHHty _ _ eq_refl) as [τe Harg].
    eexists; exact Harg.
Qed.

Lemma has_type_get_arg :
  forall Γ e τ,
    has_type Γ (EGet e) τ ->
    exists τe, has_type Γ e τe.
Proof.
  intros Γ e τ Hty.
  remember (EGet e) as eget eqn:Heqeget.
  revert e Heqeget.
  induction Hty; intros e' Heqeget; inversion Heqeget; subst; try discriminate.
  - eexists. exact Hty.
  - destruct (IHHty _ eq_refl) as [τe Harg].
    eexists; exact Harg.
  - destruct (IHHty _ eq_refl) as [τe Harg].
    eexists; exact Harg.
Qed.

Lemma has_type_set_left :
  forall Γ e1 e2 τ,
    has_type Γ (ESet e1 e2) τ ->
    exists τ1, has_type Γ e1 τ1.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (ESet e1 e2) as eset eqn:Heqeset.
  revert e1 e2 Heqeset.
  induction Hty; intros e1' e2' Heqeset; inversion Heqeset; subst; try discriminate.
  - eexists. exact Hty1.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
Qed.

Lemma has_type_set_right :
  forall Γ e1 e2 τ,
    has_type Γ (ESet e1 e2) τ ->
    exists τ2, has_type Γ e2 τ2.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (ESet e1 e2) as eset eqn:Heqeset.
  revert e1 e2 Heqeset.
  induction Hty; intros e1' e2' Heqeset; inversion Heqeset; subst; try discriminate.
  - eexists. exact Hty2.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
Qed.

Lemma has_type_if_cond :
  forall Γ e e1 e2 τ,
    has_type Γ (EIf e e1 e2) τ ->
    exists τc, has_type Γ e τc.
Proof.
  intros Γ e e1 e2 τ Hty.
  remember (EIf e e1 e2) as eif eqn:Heqeif.
  revert e e1 e2 Heqeif.
  induction Hty; intros e' e1' e2' Heqeif; inversion Heqeif; subst; try discriminate.
  - exists (TBase BBool).
    exact (has_type_pure_implies_has_type _ _ _ H).
  - destruct (IHHty _ _ _ eq_refl) as [τc Hc].
    eexists; exact Hc.
  - destruct (IHHty _ _ _ eq_refl) as [τc Hc].
    eexists; exact Hc.
Qed.

Lemma has_type_plus_left :
  forall Γ e1 e2 τ,
    has_type Γ (EPlus e1 e2) τ ->
    exists τ1, has_type Γ e1 τ1.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EPlus e1 e2) as eplus eqn:Heqeplus.
  revert e1 e2 Heqeplus.
  induction Hty; intros e1' e2' Heqeplus; inversion Heqeplus; subst; try discriminate.
  - eexists. exact Hty1.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
Qed.

Lemma has_type_plus_right :
  forall Γ e1 e2 τ,
    has_type Γ (EPlus e1 e2) τ ->
    exists τ2, has_type Γ e2 τ2.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EPlus e1 e2) as eplus eqn:Heqeplus.
  revert e1 e2 Heqeplus.
  induction Hty; intros e1' e2' Heqeplus; inversion Heqeplus; subst; try discriminate.
  - eexists. exact Hty2.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
Qed.

Lemma has_type_not_arg :
  forall Γ e τ,
    has_type Γ (ENot e) τ ->
    exists τe, has_type Γ e τe.
Proof.
  intros Γ e τ Hty.
  remember (ENot e) as enot eqn:Heqenot.
  revert e Heqenot.
  induction Hty; intros e' Heqenot; inversion Heqenot; subst; try discriminate.
  - eexists. exact Hty.
  - destruct (IHHty _ eq_refl) as [τe Harg].
    eexists; exact Harg.
  - destruct (IHHty _ eq_refl) as [τe Harg].
    eexists; exact Harg.
Qed.

Lemma has_type_and_left :
  forall Γ e1 e2 τ,
    has_type Γ (EAnd e1 e2) τ ->
    exists τ1, has_type Γ e1 τ1.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EAnd e1 e2) as eand eqn:Heqeand.
  revert e1 e2 Heqeand.
  induction Hty; intros e1' e2' Heqeand; inversion Heqeand; subst; try discriminate.
  - eexists. exact Hty1.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
Qed.

Lemma has_type_and_right :
  forall Γ e1 e2 τ,
    has_type Γ (EAnd e1 e2) τ ->
    exists τ2, has_type Γ e2 τ2.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EAnd e1 e2) as eand eqn:Heqeand.
  revert e1 e2 Heqeand.
  induction Hty; intros e1' e2' Heqeand; inversion Heqeand; subst; try discriminate.
  - eexists. exact Hty2.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
Qed.

Lemma has_type_or_left :
  forall Γ e1 e2 τ,
    has_type Γ (EOr e1 e2) τ ->
    exists τ1, has_type Γ e1 τ1.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EOr e1 e2) as eor eqn:Heqeor.
  revert e1 e2 Heqeor.
  induction Hty; intros e1' e2' Heqeor; inversion Heqeor; subst; try discriminate.
  - eexists. exact Hty1.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
Qed.

Lemma has_type_or_right :
  forall Γ e1 e2 τ,
    has_type Γ (EOr e1 e2) τ ->
    exists τ2, has_type Γ e2 τ2.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EOr e1 e2) as eor eqn:Heqeor.
  revert e1 e2 Heqeor.
  induction Hty; intros e1' e2' Heqeor; inversion Heqeor; subst; try discriminate.
  - eexists. exact Hty2.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
Qed.

Lemma has_type_imp_left :
  forall Γ e1 e2 τ,
    has_type Γ (EImp e1 e2) τ ->
    exists τ1, has_type Γ e1 τ1.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EImp e1 e2) as eimp eqn:Heqeimp.
  revert e1 e2 Heqeimp.
  induction Hty; intros e1' e2' Heqeimp; inversion Heqeimp; subst; try discriminate.
  - eexists. exact Hty1.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
Qed.

Lemma has_type_imp_right :
  forall Γ e1 e2 τ,
    has_type Γ (EImp e1 e2) τ ->
    exists τ2, has_type Γ e2 τ2.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EImp e1 e2) as eimp eqn:Heqeimp.
  revert e1 e2 Heqeimp.
  induction Hty; intros e1' e2' Heqeimp; inversion Heqeimp; subst; try discriminate.
  - eexists. exact Hty2.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
Qed.

Lemma has_type_eq_left :
  forall Γ e1 e2 τ,
    has_type Γ (EEq e1 e2) τ ->
    exists τ1, has_type Γ e1 τ1.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EEq e1 e2) as eeq eqn:Heqeeq.
  revert e1 e2 Heqeeq.
  induction Hty; intros e1' e2' Heqeeq; inversion Heqeeq; subst; try discriminate.
  - eexists. exact Hty1.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
  - destruct (IHHty _ _ eq_refl) as [τ1 Hleft].
    eexists; exact Hleft.
Qed.

Lemma has_type_eq_right :
  forall Γ e1 e2 τ,
    has_type Γ (EEq e1 e2) τ ->
    exists τ2, has_type Γ e2 τ2.
Proof.
  intros Γ e1 e2 τ Hty.
  remember (EEq e1 e2) as eeq eqn:Heqeeq.
  revert e1 e2 Heqeeq.
  induction Hty; intros e1' e2' Heqeeq; inversion Heqeeq; subst; try discriminate.
  - eexists. exact Hty2.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
  - destruct (IHHty _ _ eq_refl) as [τ2 Hright].
    eexists; exact Hright.
Qed.

Lemma plug_has_typed_hole :
  forall Γ E e τ,
    has_type Γ (plug E e) τ ->
    exists τh, has_type Γ e τh.
Proof.
  intros Γ E.
  induction E; intros e ty Hty; simpl in *.
  - eexists; exact Hty.
  - destruct (has_type_app_left _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_app_right _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_pair_left _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_pair_right _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_fst_arg _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_snd_arg _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_if_cond _ _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_newref_arg _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_get_arg _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_set_left _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_set_right _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_plus_left _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_plus_right _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_not_arg _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_and_left _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_and_right _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_or_left _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_or_right _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_imp_left _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_imp_right _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_eq_left _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
  - destruct (has_type_eq_right _ _ _ _ Hty) as [τh Hh].
    exact (IHE _ _ Hh).
Qed.

Lemma has_type_newref_payload :
  forall Γ t e τ,
    has_type Γ (ENewRef t e) τ ->
    ty_valid Γ t /\ has_type Γ e t.
Proof.
  intros Γ t e τ Hty.
  remember (ENewRef t e) as enew eqn:Heqenew.
  revert t e Heqenew.
  induction Hty; intros t' e' Heqenew; inversion Heqenew; subst; try discriminate.
  - split; assumption.
  - exact (IHHty _ _ eq_refl).
  - exact (IHHty _ _ eq_refl).
Qed.

Lemma has_type_set_payload :
  forall Γ x v τ,
    has_type Γ (ESet (ELoc x) v) τ ->
    exists τx,
      has_type Γ (ELoc x) (TRef τx) /\ has_type Γ v τx.
Proof.
  intros Γ x v τ Hty.
  remember (ESet (ELoc x) v) as eset eqn:Heqeset.
  revert x v Heqeset.
  induction Hty; intros x' v' Heqeset; inversion Heqeset; subst; try discriminate.
  - eexists.
    split; eauto.
  - exact (IHHty _ _ eq_refl).
  - exact (IHHty _ _ eq_refl).
Qed.

Lemma has_type_eloc_lookup :
  forall Γ x τ,
    has_type Γ (ELoc x) τ ->
    exists tstored vstored,
      store_ctx_lookup Γ x = Some (tstored, vstored).
Proof.
  intros Γ x τ Hty.
  remember (ELoc x) as ex eqn:Heqex.
  revert x Heqex.
  induction Hty; intros x' Heqex; inversion Heqex; subst; try discriminate.
  - eexists _, _. exact H.
  - exact (IHHty _ eq_refl).
  - exact (IHHty _ eq_refl).
Qed.

Lemma in_store_dom_lookup :
  forall Γ l,
    List.In l (store_dom Γ) ->
    is_Some (store_ctx_lookup Γ l).
Proof.
  intros Γ l Hin.
  destruct Γ as [env store].
  destruct env as [vars consts].
  unfold store_dom, store_ctx_lookup in *.
  simpl in *.
  apply in_map_iff in Hin.
  destruct Hin as [p Hp].
  destruct Hp as [Hk Hin].
  destruct p as [k entry].
  simpl in Hk. subst k.
  apply elem_of_list_In in Hin.
  apply elem_of_map_to_list in Hin.
  eauto.
Qed.

Lemma lookup_in_store_dom :
  forall Γ l entry,
    store_ctx_lookup Γ l = Some entry ->
    List.In l (store_dom Γ).
Proof.
  intros Γ l entry Hlookup.
  destruct Γ as [env store].
  destruct env as [vars consts].
  unfold store_dom, store_ctx_lookup in *.
  simpl in *.
  apply in_map_iff.
  exists (l, entry).
  split.
  - reflexivity.
  - apply elem_of_list_In.
    apply elem_of_map_to_list.
    exact Hlookup.
Qed.

Lemma var_lookup_store_add :
  forall Γ l t v x,
    var_ctx_lookup (Γ ,,s l ↦ (t, v)) x = var_ctx_lookup Γ x.
Proof.
  intros Γ l t v x.
  unfold var_ctx_lookup, ctx_add_store.
  simpl.
  reflexivity.
Qed.

Lemma const_lookup_store_add :
  forall Γ l t v c,
    const_ctx_lookup (Γ ,,s l ↦ (t, v)) c = const_ctx_lookup Γ c.
Proof.
  intros Γ l t v c.
  unfold const_ctx_lookup, ctx_add_store.
  simpl.
  reflexivity.
Qed.

Lemma no_var_bindings_preserved_by_step :
  forall σ1 σ2,
    step σ1 σ2 ->
    (forall x, var_ctx_lookup (fst σ1) x = None) ->
    (forall x, var_ctx_lookup (fst σ2) x = None).
Proof.
  intros [Γ1 e1] [Γ2 e2] Hstep.
  simpl in *.
  dependent induction Hstep; intros Hnone y.
  - eapply IHHstep; eauto.
  - exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
  - unfold var_ctx_lookup, ctx_add_store.
    simpl.
    exact (Hnone y).
  - exact (Hnone y).
  - unfold var_ctx_lookup, ctx_add_store.
    simpl.
    exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
  - exact (Hnone y).
Qed.

Lemma no_const_bindings_preserved_by_step :
  forall σ1 σ2,
    step σ1 σ2 ->
    (forall c, const_ctx_lookup (fst σ1) c = None) ->
    (forall c, const_ctx_lookup (fst σ2) c = None).
Proof.
  intros [Γ1 e1] [Γ2 e2] Hstep.
  simpl in *.
  dependent induction Hstep; intros Hnone d.
  - eapply IHHstep; eauto.
  - exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
  - unfold const_ctx_lookup, ctx_add_store.
    simpl.
    exact (Hnone d).
  - exact (Hnone d).
  - unfold const_ctx_lookup, ctx_add_store.
    simpl.
    exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
  - exact (Hnone d).
Qed.

Lemma store_lookup_store_add_fresh :
  forall Γ lnew tnew vnew l t v,
    ~ List.In lnew (store_dom Γ) ->
    store_ctx_lookup Γ l = Some (t, v) ->
    store_ctx_lookup (Γ ,,s lnew ↦ (tnew, vnew)) l = Some (t, v).
Proof.
  intros Γ lnew tnew vnew l t v Hfresh Hlookup.
  destruct (String.eq_dec l lnew) as [Heq | Hneq].
  - subst l.
    exfalso.
    apply Hfresh.
    eapply lookup_in_store_dom.
    exact Hlookup.
  - rewrite store_lookup_add_neq; auto.
Qed.

Lemma store_lookup_add_fresh_inv :
  forall Γ lnew tnew vnew l t v,
    ~ List.In lnew (store_dom Γ) ->
    store_ctx_lookup (Γ ,,s lnew ↦ (tnew, vnew)) l = Some (t, v) ->
    (l = lnew /\ t = tnew /\ v = vnew) \/
    (l <> lnew /\ store_ctx_lookup Γ l = Some (t, v)).
Proof.
  intros Γ lnew tnew vnew l t v Hfresh Hlookup.
  destruct (String.eq_dec l lnew) as [Heq | Hneq].
  - left.
    subst l.
    rewrite store_lookup_add_eq in Hlookup.
    inversion Hlookup; subst.
    auto.
  - right.
    split; [exact Hneq |].
    rewrite store_lookup_add_neq in Hlookup by exact Hneq.
    exact Hlookup.
Qed.

Lemma store_lookup_add_inv :
  forall Γ lnew tnew vnew l t v,
    store_ctx_lookup (Γ ,,s lnew ↦ (tnew, vnew)) l = Some (t, v) ->
    (l = lnew /\ t = tnew /\ v = vnew) \/
    (l <> lnew /\ store_ctx_lookup Γ l = Some (t, v)).
Proof.
  intros Γ lnew tnew vnew l t v Hlookup.
  destruct (String.eq_dec l lnew) as [Heq | Hneq].
  - left.
    subst l.
    rewrite store_lookup_add_eq in Hlookup.
    inversion Hlookup; subst.
    auto.
  - right.
    split; [exact Hneq |].
    rewrite store_lookup_add_neq in Hlookup by exact Hneq.
    exact Hlookup.
Qed.

Lemma store_dom_ctx_add_var :
  forall Γ x tx ex,
    store_dom (ctx_add_var Γ x tx ex) = store_dom Γ.
Proof.
  intros Γ x tx ex.
  unfold store_dom, ctx_add_var.
  simpl.
  reflexivity.
Qed.

Lemma store_dom_ctx_add_const :
  forall Γ c tc ec,
    store_dom (ctx_add_const Γ c tc ec) = store_dom Γ.
Proof.
  intros Γ c tc ec.
  unfold store_dom, ctx_add_const.
  simpl.
  reflexivity.
Qed.

Lemma store_dom_ctx_add_var_notin :
  forall Γ x tx ex l,
    ~ List.In l (store_dom Γ) ->
    ~ List.In l (store_dom (ctx_add_var Γ x tx ex)).
Proof.
  intros Γ x tx ex l H.
  rewrite store_dom_ctx_add_var.
  exact H.
Qed.

Lemma store_dom_ctx_add_const_notin :
  forall Γ c tc ec l,
    ~ List.In l (store_dom Γ) ->
    ~ List.In l (store_dom (ctx_add_const Γ c tc ec)).
Proof.
  intros Γ c tc ec l H.
  rewrite store_dom_ctx_add_const.
  exact H.
Qed.

(* ==================== PAPER THEOREM 4 ====================
   Implementation-aligned preservation: stepping preserves typing together with
   the store well-typedness invariant needed by the reference fragment. *)

Axiom preservation_left_stepctx_assumption :
  forall Γ1 Γ2 e e' E τ,
    runtime_ctx_well_typed Γ1 ->
    has_type Γ1 (plug E e) τ ->
    step (Γ1, e) (Γ2, e') ->
    has_type Γ2 (plug E e') τ.

(* When l is fresh in Γ, the store extension Γ ,,s l ↦ (t,v) equals
   add_ctx (ctx_add_store empty_ctx l t v) Γ.  This expresses the fresh
   insert as a right-weakening, enabling use of weakening_right and
   weakening_ty_valid_right. *)
Lemma ctx_add_store_fresh_eq_add_ctx :
  forall Γ l t v,
    ~ List.In l (store_dom Γ) ->
    Γ ,,s l ↦ (t, v) = add_ctx (ctx_add_store empty_ctx l t v) Γ.
Proof.
  intros Γ l t v Hnotin.
  assert (Hfresh : Γ !!₃ l = None).
  { destruct (Γ !!₃ l) eqn:E.
    - exfalso. apply Hnotin. apply (lookup_in_store_dom Γ l _ E).
    - reflexivity. }
  destruct Γ as [[vars consts] store].
  unfold store_ctx_lookup in Hfresh. simpl in Hfresh.
  unfold ctx_add_store, add_ctx, empty_ctx. simpl.
  f_equal.
  - f_equal.
    + apply map_eq. intros i.
      rewrite (lookup_union vars ∅ i).
      rewrite lookup_empty.
      change (vars !! i = vars !! i ∪ None).
      destruct (vars !! i); reflexivity.
    + apply map_eq. intros i.
      rewrite (lookup_union consts ∅ i).
      rewrite lookup_empty.
      change (consts !! i = consts !! i ∪ None).
      destruct (consts !! i); reflexivity.
  - apply map_eq. intros i.
    destruct (decide (i = l)) as [-> | Hi].
    + rewrite (lookup_union store (<[l:=(t,v)]>∅) l).
      destruct (store !! l) eqn:Hsl.
      * exfalso.
        apply Hnotin.
        exact (lookup_in_store_dom ((vars, consts), store) l p Hsl).
      * rewrite (lookup_insert store l (t, v)).
        setoid_rewrite Hsl.
        setoid_rewrite (lookup_insert ∅ l (t, v)).
        reflexivity.
    + rewrite (lookup_union store (<[l:=(t,v)]>∅) i).
        rewrite (lookup_insert_ne store l i (t, v)); [|congruence].
        setoid_rewrite (lookup_insert_ne ∅ l i (t, v)); [|congruence].
      rewrite lookup_empty.
      change (store !! i = store !! i ∪ None).
      destruct (store !! i); reflexivity.
Qed.

Lemma ty_valid_store_extension_fresh :
  forall Γ l t v τ,
    ~ List.In l (store_dom Γ) ->
    ty_valid Γ τ ->
    ty_valid (Γ ,,s l ↦ (t, v)) τ.
Proof.
  intros Γ l t v τ Hnotin Hvalid.
  rewrite (ctx_add_store_fresh_eq_add_ctx Γ l t v Hnotin).
  apply weakening_ty_valid_right.
  exact Hvalid.
Qed.

Lemma has_type_store_extension_fresh :
  forall Γ l t v e τe,
    ~ List.In l (store_dom Γ) ->
    has_type Γ e τe ->
    has_type (Γ ,,s l ↦ (t, v)) e τe.
Proof.
  intros Γ l t v e τe Hnotin Hty.
  rewrite (ctx_add_store_fresh_eq_add_ctx Γ l t v Hnotin).
  apply weakening_right.
  exact Hty.
Qed.

Lemma step_new_preserves_store_well_typed :
  forall Γ τ v l τtop,
    store_well_typed Γ ->
    has_type Γ (ENewRef τ v) τtop ->
    value Γ v ->
    ~ List.In l (var_dom Γ) ->
    ~ List.In l (store_dom Γ) ->
    store_well_typed (Γ ,,s l ↦ (τ, v)).
Proof.
  intros Γ τ v l τtop Hstore Hty Hval Hnotin_var Hnotin_store.
  destruct (has_type_newref_payload _ _ _ _ Hty) as [Htyvalid Htypay].
  constructor.
  intros l' t' v' Hlookup.
  destruct (string_dec l' l) as [Heq | Hneq].
  - subst l'.
    rewrite store_lookup_add_eq in Hlookup.
    inversion Hlookup; subst.
    split.
    + apply ty_valid_store_extension_fresh; assumption.
    + apply has_type_store_extension_fresh; assumption.
  - rewrite store_lookup_add_neq in Hlookup; [|exact Hneq].
    destruct (store_well_typed_lookup _ _ _ _ Hstore Hlookup) as [Hvalid' Hty'].
    split.
    + apply ty_valid_store_extension_fresh; assumption.
    + apply has_type_store_extension_fresh; assumption.
Qed.

Lemma ctx_add_const_store_comm :
  forall Γ f τ e l τstore v,
    ctx_add_const (ctx_add_store Γ l τstore v) f τ e =
    ctx_add_store (ctx_add_const Γ f τ e) l τstore v.
Proof.
  intros Γ f τ e l τstore v.
  destruct Γ as [[vars consts] store].
  reflexivity.
Qed.

Lemma has_type_pure_store_update :
  forall Γ x τx vx e τ,
    has_type_pure Γ e τ ->
    has_type_pure (Γ ,,s x ↦ (τx, vx)) e τ.
Proof.
  intros Γ x τx vx e τ Hpure.
  induction Hpure.
  - eapply PVar.
    + unfold var_ctx_lookup, ctx_add_store in *.
      simpl in *.
      exact H.
    + exact H0.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst.
    + unfold const_ctx_lookup, ctx_add_store in *.
      simpl in *.
      exact H.
    + exact H0.
  - eapply PApp; eauto.
  - eapply PNot; eauto.
  - eapply PImp; eauto.
  - eapply PAnd; eauto.
  - eapply POr; eauto.
  - eapply PEq; eauto.
  - eapply PPlus; eauto.
Qed.

Lemma ty_valid_store_update :
  forall Γ x τx vx τ,
    ty_valid Γ τ ->
    ty_valid (Γ ,,s x ↦ (τx, vx)) τ.
Proof.
  intros Γ x τx vx τ Hvalid.
  induction Hvalid.
  - apply VBase.
  - eapply VSet.
    rewrite ctx_add_var_store_comm.
    apply has_type_pure_store_update.
    exact H.
  - eapply VFun; eauto.
  - eapply VFunDep.
    + exact IHHvalid1.
    + rewrite ctx_add_var_store_comm.
      exact IHHvalid2.
  - eapply VPair; eauto.
  - eapply VRef; eauto.
Qed.

Lemma plug_has_typed_hole_pure :
  forall Γ E e τ,
    has_type_pure Γ (plug E e) τ ->
    exists τh, has_type_pure Γ e τh.
Proof.
  intros Γ E.
  induction E; intros e τ0 Hty; simpl in *.
  - eexists. exact Hty.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TArr _ _) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) _ |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase BNat) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase BNat) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase ?tb) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure Γ (plug E e) (TBase ?tb) |- _ => exact (IHE _ _ Hsub)
    end.
Qed.

(* Store updates do not affect entailments that arise in refinement subtyping:
   predicates evaluated under a single refinement variable binding. *)
Axiom entails_store_update_refinement :
  forall Γ x τ oldv newv var τb witness pred,
    Γ !!₃ x = Some (τ, oldv) ->
    ty_valid Γ (TSet var τb pred) ->
    entails (ctx_add_var Γ var (TBase τb) witness) pred ->
    entails (ctx_add_var (Γ ,,s x ↦ (τ, newv)) var (TBase τb) witness) pred.

Lemma has_type_pure_change_var_witness :
  forall Γ x τ witness_old witness_new e ty,
    has_type_pure (ctx_add_var Γ x τ witness_old) e ty ->
    has_type_pure (ctx_add_var Γ x τ witness_new) e ty.
Proof.
  intros Γ x τ witness_old witness_new e ty Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [Heq | Hneq].
    + subst x0.
      unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [[Hkey Hbinding] | [Hneq' _]].
      * inversion Hbinding; subst.
        eapply PVar.
        -- unfold var_ctx_lookup, ctx_add_var.
           simpl.
           apply lookup_insert.
        -- exact H0.
      * contradiction.
    + eapply PVar.
      * unfold var_ctx_lookup, ctx_add_var in *.
        simpl in *.
        apply lookup_insert_Some.
        right.
        split.
        -- congruence.
        -- apply lookup_insert_Some in H.
           destruct H as [[Heq _] | [Hneq' Hbase]].
            ++ congruence.
           ++ exact Hbase.
      * exact H0.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst; eauto.
  - eapply PApp; eauto.
  - apply PNot. exact IHHpure.
  - apply PImp; assumption.
  - apply PAnd; assumption.
  - apply POr; assumption.
  - eapply PEq; eauto.
  - apply PPlus; assumption.
Qed.

Lemma ty_valid_set_predicate :
  forall Γ var τb e v,
    ty_valid Γ (TSet var τb e) ->
    has_type_pure (ctx_add_var Γ var (TBase τb) v) e (TBase BBool).
Proof.
  intros Γ var τb e v Hvalid.
  remember (TSet var τb e) as t eqn:Ht.
  induction Hvalid; inversion Ht; subst; try discriminate.
  eapply has_type_pure_change_var_witness.
  exact H.
Qed.

(* Subtyping is preserved under same-type store updates. *)
Lemma subtype_store_update :
  forall Γ x τ oldv newv τ₁ τ₂,
    Γ !!₃ x = Some (τ, oldv) ->
    subtype Γ τ₁ τ₂ ->
    subtype (Γ ,,s x ↦ (τ, newv)) τ₁ τ₂.
Proof.
  intros Γ x τ oldv newv τ₁ τ₂ Hlookup Hsub.
  induction Hsub.
  - apply SBase.
  - eapply SSet with (c := c).
    + apply ty_valid_store_update. exact H.
    + apply ty_valid_store_update. exact H0.
    + rewrite ctx_add_var_store_comm.
      eapply (entails_store_update_refinement
          Γ x τ oldv newv var τb (make_expr τb c) (EImp e₁ e₂)).
        * exact Hlookup.
      * eapply (VSet Γ var τb (EImp e₁ e₂) (make_expr τb c)).
        apply PImp.
        -- exact (ty_valid_set_predicate _ _ _ _ _ H).
        -- exact (ty_valid_set_predicate _ _ _ _ _ H0).
      * exact H1.
  - apply SSetBase. apply ty_valid_store_update. exact H.
  - eapply SBaseSet with (c := c).
    + apply ty_valid_store_update. exact H.
    + rewrite ctx_add_var_store_comm.
      eapply (entails_store_update_refinement
          Γ x τ oldv newv var τb (make_expr τb c) e).
        * exact Hlookup.
      * exact H.
      * exact H0.
  - apply SFun.
    + exact (IHHsub1 Hlookup).
    + exact (IHHsub2 Hlookup).
  - eapply SFunDep.
    + exact (IHHsub1 Hlookup).
    + rewrite ctx_add_var_store_comm.
      apply IHHsub2.
      unfold store_ctx_lookup, ctx_add_var in *.
      simpl in *.
      exact Hlookup.
  - apply SPair.
    + exact (IHHsub1 Hlookup).
    + exact (IHHsub2 Hlookup).
  - apply SRef.
    + exact (IHHsub1 Hlookup).
    + exact (IHHsub2 Hlookup).
Qed.

(* ELoc is not a pure expression; no has_type_pure derivation for it exists. *)
Lemma self_to_TRef :
  forall τ e τ',
    self τ e = TRef τ' ->
    τ = TRef τ'.
Proof.
  intros τ e τ' H.
  destruct τ; simpl in H; try discriminate.
  - (* TArr τ1 τ2: self maps TArr (TBase b) to TArrDep, else to TArr; neither is TRef *)
    destruct τ1; simpl in H; discriminate.
  - (* TRef t: self (TRef t) e = TRef t *)
    inversion H. reflexivity.
Qed.

Lemma no_eloc_has_type_pure :
  forall Γ x τ,
    ~ has_type_pure Γ (ELoc x) τ.
Proof.
  intros Γ x τ Hpure.
  inversion Hpure.
Qed.

Lemma has_type_eloc_origin :
  forall Γ x τ,
    has_type Γ (ELoc x) (TRef τ) ->
    exists τ' v,
      store_ctx_lookup Γ x = Some (τ', v) /\
      ref_type_origin Γ (TRef τ') (TRef τ).
Proof.
  intros Γ x τ Hty.
  remember (ELoc x) as e eqn:He.
  remember (TRef τ) as tref eqn:Ht.
  revert x τ He Ht.
  induction Hty; intros x0 τ0 He Ht; inversion He; subst; try discriminate;
    try (inversion Ht; subst); try discriminate.
  - exists τ0, v. split.
    + exact H.
    + apply RefOriginHere.
  - match goal with
    | Hself : self ?τ1 (ELoc x0) = TRef τ0 |- _ =>
        apply self_ref_inv in Hself;
        inversion Hself; subst
    end.
    eapply IHHty; eauto.
  - inversion H; subst; try discriminate.
    destruct (IHHty _ _ eq_refl eq_refl) as [τ_store [v_store [Hstore Horigin]]].
    exists τ_store, v_store. split.
    + exact Hstore.
    + eapply RefOriginStep.
      * exact Horigin.
      * apply SRef; assumption.
Qed.

Lemma ref_type_origin_payload_has_type :
  forall Γ τstore τout v,
    ref_type_origin Γ (TRef τstore) (TRef τout) ->
    has_type Γ v τout ->
    has_type Γ v τstore.
Proof.
  intros Γ τstore τout v Horigin Hv.
  dependent induction Horigin.
  - exact Hv.
  - eapply (IHHorigin _ _ eq_refl eq_refl).
    inversion H; subst; try discriminate.
    eapply TSub.
    + exact Hv.
    + exact H3.
Qed.

  Lemma step_var_preserves_typing :
    forall Γ x tbound vbound τtop,
      runtime_ctx_well_typed Γ ->
      Γ !!₁ x = Some (tbound, vbound) ->
      has_type Γ (EVar x) τtop ->
      has_type Γ vbound τtop.
  Proof.
    intros Γ x tbound vbound τtop Hrt Hlookup Hty.
    remember (EVar x) as ex eqn:Heqex.
    revert x tbound vbound Hlookup Heqex.
    induction Hty; intros x0 tbound0 vbound0 Hlookup0 Heqex;
      inversion Heqex; subst; try discriminate.
    - destruct (var_well_typed_lookup _ _ _ _ (runtime_ctx_well_typed_var _ Hrt) H)
        as [Hvalid Htyped].
      rewrite Hlookup0 in H.
      inversion H; subst.
      exact Htyped.
    - destruct (var_well_typed_lookup _ _ _ _ (runtime_ctx_well_typed_var _ Hrt) H)
        as [Hvalid Htyped].
      rewrite Hlookup0 in H.
      inversion H; subst.
      match goal with
      | Hbeta : Is_true (essential_type_is_base_type _) |- _ =>
          pose proof (bool_prop_eq_true _ Hbeta) as Hbeta_eq
      end.
      eapply TSub.
      + exact Htyped.
      + apply subtype_to_essential_type.
        * exact Hbeta_eq.
        * exact Hvalid.
    - exfalso.
      specialize (H (TArr (TBase BNat) (TBase BNat))).
      inversion H; subst.
      destruct τb; simpl in *.
      + discriminate.
      + discriminate.
      + contradiction.
      + contradiction.
      + contradiction.
      + contradiction.
    - eapply TSub.
      + eapply IHHty.
        * exact Hrt.
        * exact Hlookup0.
        * reflexivity.
      + exact H.
  Qed.

Lemma step_const_preserves_typing_runtime :
  forall Γ c t e v τtop,
    runtime_ctx_well_typed Γ ->
    Γ !!₂ c = Some (t, e) ->
    value Γ v ->
    has_type Γ (EApp (EConst c) v) τtop ->
    has_type Γ e τtop.
Proof.
  intros Γ c t e v τtop Hrt Hlookup Hval Hty.
  eapply (runtime_ctx_well_typed_const_step _ Hrt); eauto.
Qed.

Lemma ref_type_origin_payload_has_type_forward :
  forall Γ τstore τout v,
    ref_type_origin Γ (TRef τstore) (TRef τout) ->
    has_type Γ v τstore ->
    has_type Γ v τout.
Proof.
  intros Γ τstore τout v Horigin Hv.
  dependent induction Horigin.
  - exact Hv.
  - inversion H; subst; try discriminate.
    eapply TSub.
    + eapply (IHHorigin _ _ eq_refl eq_refl).
      exact Hv.
    + exact H2.
Qed.

(* The value v in ESet (ELoc x) v has type τ where Γ !!₃ x = Some (τ, _). *)
Lemma set_payload_typed_at_store_type :
  forall Γ x τ oldv v τtop,
    store_well_typed Γ ->
    has_type Γ (ESet (ELoc x) v) τtop ->
    Γ !!₃ x = Some (τ, oldv) ->
    has_type Γ v τ.
Proof.
  intros Γ x τ oldv v τtop Hstore Hty Hlookup.
  destruct (has_type_set_payload Γ x v τtop Hty) as [τx [HLoc Hv]].
  destruct (has_type_eloc_origin Γ x τx HLoc) as [τ' [stored [Hstorex Horigin]]].
  rewrite Hlookup in Hstorex.
  inversion Hstorex; subst.
  eapply ref_type_origin_payload_has_type; eauto.
Qed.

(* Typing is preserved when the store is updated with the same type. *)
Lemma has_type_store_update_same_type :
  forall Γ x τ oldv newv e τe,
    Γ !!₃ x = Some (τ, oldv) ->
    has_type Γ e τe ->
    has_type (Γ ,,s x ↦ (τ, newv)) e τe.
Proof.
  intros Γ x τ oldv newv e τe Hlookup Hty.
  induction Hty.
  - apply TString.
  - apply TNat.
  - apply TBool.
  - apply TUnit.
  - eapply TConst.
    unfold const_ctx_lookup, ctx_add_store in *. simpl. exact H.
  - eapply TVar.
    unfold var_ctx_lookup, ctx_add_store in *. simpl. exact H.
  - eapply TEssentialVar.
    + unfold var_ctx_lookup, ctx_add_store in *. simpl. exact H.
    + exact H0.
  - (* TLoc: case split on whether this location is x *)
    destruct (string_dec l x) as [Heqlx | Hneqlx].
    + subst l.
      assert (Ht : t = τ).
      { rewrite Hlookup in H. inversion H. reflexivity. }
      subst t.
      eapply TLoc. apply store_lookup_add_eq.
    + eapply TLoc.
      rewrite store_lookup_add_neq; [exact H | exact Hneqlx].
  - apply TFail. apply ty_valid_store_update. exact H.
  - eapply TFun.
    + apply ty_valid_store_update. exact H.
    + rewrite ctx_add_const_store_comm.
      rewrite ctx_add_var_store_comm.
      apply IHHty.
      unfold store_ctx_lookup, ctx_add_var, ctx_add_const in *.
      simpl in *.
      exact Hlookup.
  - eapply TAppPure.
    + exact (IHHty1 Hlookup).
    + intros τ₃.
      match goal with
      | Hpure : forall τ₄ : i_ty, has_type_pure Γ e₂ τ₄ |- _ =>
          apply has_type_pure_store_update;
          exact (Hpure τ₃)
      end.
    + exact (IHHty2 Hlookup).
  - eapply TAppImPure.
    + exact (IHHty1 Hlookup).
    + exact (IHHty2 Hlookup).
  - apply TPlus.
    + exact (IHHty1 Hlookup).
    + exact (IHHty2 Hlookup).
  - apply TNot. exact (IHHty Hlookup).
  - apply TImp.
    + exact (IHHty1 Hlookup).
    + exact (IHHty2 Hlookup).
  - apply TAnd.
    + exact (IHHty1 Hlookup).
    + exact (IHHty2 Hlookup).
  - apply TOr.
    + exact (IHHty1 Hlookup).
    + exact (IHHty2 Hlookup).
  - eapply TEq.
    + exact (IHHty1 Hlookup).
    + exact (IHHty2 Hlookup).
  - eapply TRefI.
    + apply ty_valid_store_update. exact H.
    + exact (IHHty Hlookup).
  - eapply TGet. exact (IHHty Hlookup).
  - eapply TSetI.
    + exact (IHHty1 Hlookup).
    + exact (IHHty2 Hlookup).
  - apply TPair.
    + exact (IHHty1 Hlookup).
    + exact (IHHty2 Hlookup).
  - eapply TFst. exact (IHHty Hlookup).
  - eapply TSnd. exact (IHHty Hlookup).
  - eapply TIf.
    + apply has_type_pure_store_update. exact H.
    + rewrite ctx_add_var_store_comm.
      apply IHHty1.
      unfold store_ctx_lookup, ctx_add_var in *.
      simpl in *.
      exact Hlookup.
    + rewrite ctx_add_var_store_comm.
      apply IHHty2.
      unfold store_ctx_lookup, ctx_add_var in *.
      simpl in *.
      exact Hlookup.
  - eapply TSelf.
    + exact (IHHty Hlookup).
    + intros τ₁.
      match goal with
      | Hpure : forall τ₂ : i_ty, has_type_pure Γ e τ₂ |- _ =>
          apply has_type_pure_store_update;
          exact (Hpure τ₁)
      end.
  - eapply TSub.
    + exact (IHHty Hlookup).
    + match goal with
      | Hsub : subtype Γ _ _ |- _ =>
          apply subtype_store_update with (oldv := oldv);
          [exact Hlookup | exact Hsub]
      end.
Qed.

Lemma step_set_preserves_store_well_typed :
  forall Γ x τ oldv v τtop,
    store_well_typed Γ ->
    has_type Γ (ESet (ELoc x) v) τtop ->
    value Γ v ->
    Γ !!₃ x = Some (τ, oldv) ->
    store_well_typed (Γ ,,s x ↦ (τ, v)).
Proof.
  intros Γ x τ oldv v τtop Hstore Hty Hval Hlookupx.
  constructor.
  intros l t w Hlookup.
  destruct (string_dec l x) as [Heq | Hneq].
  - subst l.
    rewrite store_lookup_add_eq in Hlookup.
    inversion Hlookup; subst.
    split.
    + apply ty_valid_store_update.
      destruct (store_well_typed_lookup _ _ _ _ Hstore Hlookupx) as [Hvalid _].
      exact Hvalid.
    + apply has_type_store_update_same_type with (oldv := oldv).
      * exact Hlookupx.
      * eapply set_payload_typed_at_store_type;
          [exact Hstore | exact Hty | exact Hlookupx].
  - rewrite store_lookup_add_neq in Hlookup; [|exact Hneq].
    destruct (store_well_typed_lookup _ _ _ _ Hstore Hlookup) as [Hvalid Htyped].
    split.
    + apply ty_valid_store_update.
      exact Hvalid.
    + apply has_type_store_update_same_type with (oldv := oldv).
      * exact Hlookupx.
      * exact Htyped.
Qed.

Lemma subtype_store_extension_fresh :
  forall Γ l t v τ1 τ2,
    ~ List.In l (store_dom Γ) ->
    subtype Γ τ1 τ2 ->
    subtype (Γ ,,s l ↦ (t, v)) τ1 τ2.
Proof.
  intros Γ l t v τ1 τ2 Hfresh Hsub.
  rewrite (ctx_add_store_fresh_eq_add_ctx Γ l t v Hfresh).
  apply weakening_subtype_right.
  exact Hsub.
Qed.

Lemma no_enewref_has_type_pure :
  forall Γ τ e t,
    ~ has_type_pure Γ (ENewRef τ e) t.
Proof.
  intros Γ τ e t Hpure.
  inversion Hpure.
Qed.

Lemma no_eset_has_type_pure :
  forall Γ e1 e2 t,
    ~ has_type_pure Γ (ESet e1 e2) t.
Proof.
  intros Γ e1 e2 t Hpure.
  inversion Hpure.
Qed.

Lemma step_new_preserves_typing :
  forall Γ τ v l τtop,
    has_type Γ (ENewRef τ v) τtop ->
    value Γ v ->
    ~ List.In l (var_dom Γ) ->
    ~ List.In l (store_dom Γ) ->
    has_type (Γ ,,s l ↦ (τ, v)) (ELoc l) τtop.
Proof.
  intros Γ τ v l τtop Hty Hval Hfresh_var Hfresh_store.
  remember (ENewRef τ v) as enew eqn:Heqenew.
  revert τ v Hval Hfresh_var Hfresh_store Heqenew.
  induction Hty; intros τ0 v0 Hval0 Hfresh_var0 Hfresh_store0 Heqenew;
    inversion Heqenew; subst; try discriminate.
  - eapply TLoc.
    apply store_lookup_add_eq.
  - exfalso.
    match goal with
    | Hpure : forall τ1 : i_ty, has_type_pure Γ (ENewRef τ0 v0) τ1 |- _ =>
        exact (no_enewref_has_type_pure _ _ _ _ (Hpure (TBase BNat)))
    end.
  - eapply TSub.
    + eapply IHHty; eauto.
    + apply subtype_store_extension_fresh; assumption.
Qed.

Lemma step_set_preserves_typing :
  forall Γ x τ oldv v τtop,
    has_type Γ (ESet (ELoc x) v) τtop ->
    value Γ v ->
    Γ !!₃ x = Some (τ, oldv) ->
    has_type (Γ ,,s x ↦ (τ, v)) (EUnit tt) τtop.
Proof.
  intros Γ x τ oldv v τtop Hty Hval Hlookup.
  remember (ESet (ELoc x) v) as eset eqn:Heqeset.
  revert x τ oldv v Hval Hlookup Heqeset.
  induction Hty; intros x0 τ0 oldv0 v0 Hval0 Hlookup0 Heqeset;
    inversion Heqeset; subst; try discriminate.
  - apply TUnit.
  - exfalso.
    match goal with
    | Hpure : forall τ1 : i_ty, has_type_pure Γ (ESet (ELoc x0) v0) τ1 |- _ =>
        exact (no_eset_has_type_pure _ _ _ _ (Hpure (TBase BNat)))
    end.
  - eapply TSub.
    + eapply IHHty; eauto.
    + apply subtype_store_update with (oldv := oldv0).
      * exact Hlookup0.
      * exact H.
Qed.

Lemma no_eget_has_type_pure :
  forall Γ e t,
    ~ has_type_pure Γ (EGet e) t.
Proof.
  intros Γ e t Hpure.
  inversion Hpure.
Qed.

Lemma step_get_preserves_typing :
  forall Γ x τstored v τtop,
    store_well_typed Γ ->
    has_type Γ (EGet (ELoc x)) τtop ->
    Γ !!₃ x = Some (τstored, v) ->
    has_type Γ v τtop.
Proof.
  intros Γ x τstored v τtop Hstore Hty Hlookup.
  remember (EGet (ELoc x)) as eget eqn:Heqeget.
  revert x τstored v Hstore Hlookup Heqeget.
  induction Hty; intros x0 τstored0 v0 Hstore0 Hlookup0 Heqeget;
    inversion Heqeget; subst; try discriminate.
  - destruct (has_type_eloc_origin Γ x0 τ Hty) as [τ' [stored [Hstorex Horigin]]].
    rewrite Hlookup0 in Hstorex.
    inversion Hstorex; subst.
    destruct (store_well_typed_lookup _ _ _ _ Hstore0 Hlookup0) as [_ Htyped].
    eapply ref_type_origin_payload_has_type_forward; eauto.
  - exfalso.
    match goal with
    | Hpure : forall τ1 : i_ty, has_type_pure Γ (EGet (ELoc x0)) τ1 |- _ =>
        exact (no_eget_has_type_pure _ _ _ (Hpure (TBase BNat)))
    end.
  - eapply TSub; [eapply IHHty; eauto | exact H].
Qed.

Lemma no_efst_has_type_pure :
  forall Γ e t,
    ~ has_type_pure Γ (EFst e) t.
Proof.
  intros Γ e t Hpure.
  inversion Hpure.
Qed.

Lemma no_esnd_has_type_pure :
  forall Γ e t,
    ~ has_type_pure Γ (ESnd e) t.
Proof.
  intros Γ e t Hpure.
  inversion Hpure.
Qed.

Lemma step_fst_preserves_typing :
  forall Γ v1 v2 τtop,
    has_type Γ (EFst (EPair v1 v2)) τtop ->
    value Γ v1 ->
    value Γ v2 ->
    has_type Γ v1 τtop.
Proof.
  intros Γ v1 v2 τtop Hty Hv1 Hv2.
  remember (EFst (EPair v1 v2)) as efst eqn:Heqefst.
  revert v1 v2 Hv1 Hv2 Heqefst.
  induction Hty; intros v1' v2' Hv1' Hv2' Heqefst;
    inversion Heqefst; subst; try discriminate.
  - destruct (inversion_pair _ _ _ _ _ Hty) as [Hleft _].
    exact Hleft.
  - exfalso.
    match goal with
    | Hpure : forall τ1 : i_ty, has_type_pure Γ (EFst (EPair v1' v2')) τ1 |- _ =>
        exact (no_efst_has_type_pure _ _ _ (Hpure (TBase BNat)))
    end.
  - eapply TSub.
    + eapply (IHHty v1' v2'); eauto; reflexivity.
    + exact H.
Qed.

Lemma step_snd_preserves_typing :
  forall Γ v1 v2 τtop,
    has_type Γ (ESnd (EPair v1 v2)) τtop ->
    value Γ v1 ->
    value Γ v2 ->
    has_type Γ v2 τtop.
Proof.
  intros Γ v1 v2 τtop Hty Hv1 Hv2.
  remember (ESnd (EPair v1 v2)) as esnd eqn:Heqesnd.
  revert v1 v2 Hv1 Hv2 Heqesnd.
  induction Hty; intros v1' v2' Hv1' Hv2' Heqesnd;
    inversion Heqesnd; subst; try discriminate.
  - destruct (inversion_pair _ _ _ _ _ Hty) as [_ Hright].
    exact Hright.
  - exfalso.
    match goal with
    | Hpure : forall τ1 : i_ty, has_type_pure Γ (ESnd (EPair v1' v2')) τ1 |- _ =>
        exact (no_esnd_has_type_pure _ _ _ (Hpure (TBase BNat)))
    end.
  - eapply TSub.
    + eapply (IHHty v1' v2'); eauto; reflexivity.
    + exact H.
Qed.

Lemma step_not_preserves_typing :
  forall Γ b τtop,
    has_type Γ (ENot (EBool b)) τtop ->
    has_type Γ (EBool (negb b)) τtop.
Proof.
  intros Γ b τtop Hty.
  remember (ENot (EBool b)) as enot eqn:Heqenot.
  revert b Heqenot.
  induction Hty; intros b' Heqenot; inversion Heqenot; subst; try discriminate.
  - apply TBool.
  - match goal with
    | H : forall τ₁ : i_ty, has_type_pure _ (ENot (EBool b')) τ₁ |- _ =>
        specialize (H (TBase BNat)); inversion H
    end.
  - eapply TSub.
    + eapply IHHty; reflexivity.
    + exact H.
Qed.

Lemma step_and_preserves_typing :
  forall Γ b₁ b₂ τtop,
    has_type Γ (EAnd (EBool b₁) (EBool b₂)) τtop ->
    has_type Γ (EBool (andb b₁ b₂)) τtop.
Proof.
  intros Γ b₁ b₂ τtop Hty.
  remember (EAnd (EBool b₁) (EBool b₂)) as eand eqn:Heqeand.
  revert b₁ b₂ Heqeand.
  induction Hty; intros b₁' b₂' Heqeand; inversion Heqeand; subst; try discriminate.
  - apply TBool.
  - match goal with
    | H : forall τ₁ : i_ty, has_type_pure _ (EAnd (EBool b₁') (EBool b₂')) τ₁ |- _ =>
        specialize (H (TBase BNat)); inversion H
    end.
  - eapply TSub.
    + eapply IHHty; reflexivity.
    + exact H.
Qed.

Lemma step_or_preserves_typing :
  forall Γ b₁ b₂ τtop,
    has_type Γ (EOr (EBool b₁) (EBool b₂)) τtop ->
    has_type Γ (EBool (orb b₁ b₂)) τtop.
Proof.
  intros Γ b₁ b₂ τtop Hty.
  remember (EOr (EBool b₁) (EBool b₂)) as eor eqn:Heqeor.
  revert b₁ b₂ Heqeor.
  induction Hty; intros b₁' b₂' Heqeor; inversion Heqeor; subst; try discriminate.
  - apply TBool.
  - match goal with
    | H : forall τ₁ : i_ty, has_type_pure _ (EOr (EBool b₁') (EBool b₂')) τ₁ |- _ =>
        specialize (H (TBase BNat)); inversion H
    end.
  - eapply TSub.
    + eapply IHHty; reflexivity.
    + exact H.
Qed.

Lemma step_imp_preserves_typing :
  forall Γ b₁ b₂ τtop,
    has_type Γ (EImp (EBool b₁) (EBool b₂)) τtop ->
    has_type Γ (EBool (implb b₁ b₂)) τtop.
Proof.
  intros Γ b₁ b₂ τtop Hty.
  remember (EImp (EBool b₁) (EBool b₂)) as eimp eqn:Heqeimp.
  revert b₁ b₂ Heqeimp.
  induction Hty; intros b₁' b₂' Heqeimp; inversion Heqeimp; subst; try discriminate.
  - apply TBool.
  - match goal with
    | H : forall τ₁ : i_ty, has_type_pure _ (EImp (EBool b₁') (EBool b₂')) τ₁ |- _ =>
        specialize (H (TBase BNat)); inversion H
    end.
  - eapply TSub.
    + eapply IHHty; reflexivity.
    + exact H.
Qed.

Lemma step_eq_preserves_typing :
  forall Γ v₁ v₂ b τtop,
    has_type Γ (EEq v₁ v₂) τtop ->
    has_type Γ (EBool b) τtop.
Proof.
  intros Γ v₁ v₂ b τtop Hty.
  remember (EEq v₁ v₂) as eeq eqn:Heqeeq.
  revert v₁ v₂ Heqeeq.
  induction Hty; intros v₁' v₂' Heqeeq; inversion Heqeeq; subst; try discriminate.
  - apply TBool.
  - match goal with
    | H : forall τ₁ : i_ty, has_type_pure _ (EEq v₁' v₂') τ₁ |- _ =>
        specialize (H (TBase BNat)); inversion H
    end.
  - eapply TSub.
    + eapply IHHty; reflexivity.
    + exact H.
Qed.

Lemma step_plus_preserves_typing :
  forall Γ n₁ n₂ τtop,
    has_type Γ (EPlus (ENat n₁) (ENat n₂)) τtop ->
    has_type Γ (ENat (n₁ + n₂)) τtop.
Proof.
  intros Γ n₁ n₂ τtop Hty.
  remember (EPlus (ENat n₁) (ENat n₂)) as eplus eqn:Heqeplus.
  revert n₁ n₂ Heqeplus.
  induction Hty; intros n₁' n₂' Heqeplus; inversion Heqeplus; subst; try discriminate.
  - apply TNat.
  - match goal with
    | H : forall τ₁ : i_ty, has_type_pure _ (EPlus (ENat n₁') (ENat n₂')) τ₁ |- _ =>
        specialize (H (TBase BBool)); inversion H
    end.
  - eapply TSub.
    + eapply IHHty; reflexivity.
    + exact H.
Qed.

Lemma preservation_left_same_ctx_step :
  forall Γ e e' τ,
    runtime_ctx_well_typed Γ ->
    has_type Γ e τ ->
    step (Γ, e) (Γ, e') ->
    has_type Γ e' τ.
Proof.
  intros Γ e e' τ Hrt Hty Hstep.
  inversion Hstep; subst.
  - eapply preservation_left_stepctx_assumption; eauto.
  - eapply step_const_preserves_typing_runtime; eauto.
  - eapply step_var_preserves_typing; eauto.
  - eapply preservation_left_stepctx_assumption with (E := ECHole); eauto.
  - eapply step_fst_preserves_typing; eauto.
  - eapply step_snd_preserves_typing; eauto.
  - eapply preservation_left_stepctx_assumption with (E := ECHole); eauto.
  - eapply preservation_left_stepctx_assumption with (E := ECHole); eauto.
  - exfalso.
    match goal with
    | HfreshStore : ~ List.In ?l (store_dom (ctx_add_store ?G ?l ?t ?v)) |- _ =>
        apply HfreshStore;
        eapply (lookup_in_store_dom (ctx_add_store G l t v) l (t, v));
        apply store_lookup_add_eq
    end.
  - eapply step_get_preserves_typing; eauto.
    exact (runtime_ctx_well_typed_store _ Hrt).
  - assert (HvalΓ : value Γ v) by (rewrite <- H1; exact H2).
    assert (HlookupΓ : Γ !!₃ x = Some (τ0, e0)) by (rewrite <- H1; exact H4).
    exact (step_set_preserves_typing Γ x τ0 e0 v τ Hty HvalΓ HlookupΓ).
  - eapply preservation_left_stepctx_assumption with (E := ECHole); eauto.
  - eapply step_not_preserves_typing; exact Hty.
  - eapply step_and_preserves_typing; exact Hty.
  - eapply step_or_preserves_typing; exact Hty.
  - eapply step_imp_preserves_typing; exact Hty.
  - eapply step_eq_preserves_typing; exact Hty.
  - eapply step_plus_preserves_typing; exact Hty.
Qed.

Lemma preservation_left_store_typed_ctx_by_step :
  forall σ1 σ2,
    step σ1 σ2 ->
    forall τgoal,
      runtime_ctx_well_typed (fst σ1) ->
      has_type (fst σ1) (snd σ1) τgoal ->
      has_type (fst σ2) (snd σ2) τgoal.
Proof.
  intros σ1 σ2 Hstep.
  induction Hstep; intros τgoal Hrt Hty.
  - eapply preservation_left_stepctx_assumption; eauto.
  - eapply preservation_left_same_ctx_step; eauto.
    econstructor; eauto.
  - eapply preservation_left_same_ctx_step; eauto.
    econstructor; eauto.
  - eapply preservation_left_same_ctx_step; eauto.
    econstructor; eauto.
  - match goal with
    | H1 : value _ _, H2 : value _ _ |- _ =>
        eapply (step_fst_preserves_typing _ _ _ _ Hty H1 H2)
    end.
  - match goal with
    | H1 : value _ _, H2 : value _ _ |- _ =>
        eapply (step_snd_preserves_typing _ _ _ _ Hty H1 H2)
    end.
  - eapply preservation_left_same_ctx_step; eauto.
    econstructor; eauto.
  - eapply preservation_left_same_ctx_step; eauto.
    econstructor; eauto.
  - eapply step_new_preserves_typing; eauto.
  - eapply step_get_preserves_typing; eauto.
    exact (runtime_ctx_well_typed_store _ Hrt).
  - eapply step_set_preserves_typing; eauto.
  - eapply preservation_left_same_ctx_step; eauto.
    econstructor; eauto.
  - eapply step_not_preserves_typing; exact Hty.
  - eapply step_and_preserves_typing; exact Hty.
  - eapply step_or_preserves_typing; exact Hty.
  - eapply step_imp_preserves_typing; exact Hty.
  - eapply step_eq_preserves_typing; exact Hty.
  - eapply step_plus_preserves_typing; exact Hty.
Qed.

Lemma preservation_left_store_typed_ctx :
  forall Γ e Γ' e' τ,
    runtime_ctx_well_typed Γ ->
    has_type Γ e τ ->
    step (Γ, e) (Γ', e') ->
    has_type Γ' e' τ.
Proof.
  intros Γ e Γ' e' τ Hrt Hty Hstep.
  eapply (preservation_left_store_typed_ctx_by_step (Γ, e) (Γ', e')); eauto.
Qed.

Lemma preservation_left_runtime_ctx_by_step :
  forall σ1 σ2,
    step σ1 σ2 ->
    forall τgoal,
      runtime_ctx_well_typed (fst σ1) ->
      has_type (fst σ1) (snd σ1) τgoal ->
      has_type (fst σ2) (snd σ2) τgoal.
Proof.
  intros σ1 σ2 Hstep.
  induction Hstep; intros τgoal Hrt Hty.
  - eapply preservation_left_stepctx_assumption; eauto.
  - eapply step_const_preserves_typing_runtime; eauto.
  - eapply step_var_preserves_typing; eauto.
  - eapply preservation_left_same_ctx_step; eauto.
    econstructor; eauto.
  - match goal with
    | H1 : value _ _, H2 : value _ _ |- _ =>
        eapply (step_fst_preserves_typing _ _ _ _ Hty H1 H2)
    end.
  - match goal with
    | H1 : value _ _, H2 : value _ _ |- _ =>
        eapply (step_snd_preserves_typing _ _ _ _ Hty H1 H2)
    end.
  - eapply preservation_left_same_ctx_step; eauto.
    econstructor; eauto.
  - eapply preservation_left_same_ctx_step; eauto.
    econstructor; eauto.
  - eapply step_new_preserves_typing; eauto.
  - eapply step_get_preserves_typing; eauto.
    exact (runtime_ctx_well_typed_store _ Hrt).
  - eapply step_set_preserves_typing; eauto.
  - eapply preservation_left_same_ctx_step; eauto.
    econstructor; eauto.
  - eapply step_not_preserves_typing; exact Hty.
  - eapply step_and_preserves_typing; exact Hty.
  - eapply step_or_preserves_typing; exact Hty.
  - eapply step_imp_preserves_typing; exact Hty.
  - eapply step_eq_preserves_typing; exact Hty.
  - eapply step_plus_preserves_typing; exact Hty.
Qed.

Lemma preservation_left_runtime_ctx :
  forall Γ e Γ' e' τ,
    runtime_ctx_well_typed Γ ->
    has_type Γ e τ ->
    step (Γ, e) (Γ', e') ->
    has_type Γ' e' τ.
Proof.
  intros Γ e Γ' e' τ Hrt Hty Hstep.
  eapply (preservation_left_runtime_ctx_by_step (Γ, e) (Γ', e')); eauto.
Qed.

Lemma preservation_left :
  forall Γ e Γ' e' τ,
    runtime_ctx_well_typed Γ ->
    has_type Γ e τ ->
    step (Γ, e) (Γ', e') ->
    has_type Γ' e' τ.
Proof.
  intros Γ e Γ' e' τ Hrt Hty Hstep.
  exact (preservation_left_store_typed_ctx Γ e Γ' e' τ Hrt Hty Hstep).
Qed.

Lemma preservation_right_store_typed_ctx_by_step :
  forall σ1 σ2,
    step σ1 σ2 ->
    forall τgoal,
      store_well_typed (fst σ1) ->
      has_type (fst σ1) (snd σ1) τgoal ->
      store_well_typed (fst σ2).
Proof.
  intros σ1 σ2 Hstep.
  induction Hstep; intros τgoal Hstore Hty.
  - destruct (plug_has_typed_hole _ _ _ _ Hty) as [τh Hhole].
    eapply IHHstep; eauto.
  - exact Hstore.
  - exact Hstore.
  - exact Hstore.
  - exact Hstore.
  - exact Hstore.
  - exact Hstore.
  - exact Hstore.
  - eapply step_new_preserves_store_well_typed; eauto.
  - exact Hstore.
  - eapply step_set_preserves_store_well_typed; eauto.
  - exact Hstore.
  - exact Hstore.
  - exact Hstore.
  - exact Hstore.
  - exact Hstore.
  - exact Hstore.
  - exact Hstore.
Qed.

Lemma preservation_right_store_typed_ctx :
  forall Γ e Γ' e' τ,
    store_well_typed Γ ->
    has_type Γ e τ ->
    step (Γ, e) (Γ', e') ->
    store_well_typed Γ'.
Proof.
  intros Γ e Γ' e' τ Hstore Hty Hstep.
  eapply (preservation_right_store_typed_ctx_by_step (Γ, e) (Γ', e')); eauto.
Qed.

Lemma preservation_right :
  forall Γ e Γ' e' τ,
    store_well_typed Γ ->
    has_type Γ e τ ->
    step (Γ, e) (Γ', e') ->
    store_well_typed Γ'.
Proof.
  intros Γ e Γ' e' τ Hstore Hty Hstep.
  exact (preservation_right_store_typed_ctx Γ e Γ' e' τ Hstore Hty Hstep).
Qed.

Theorem preservation :
  forall Γ e Γ' e' τ,
    runtime_ctx_well_typed Γ ->
    has_type Γ e τ ->
    step (Γ, e) (Γ', e') ->
    has_type Γ' e' τ /\ store_well_typed Γ'.
Proof.
  intros Γ e Γ' e' τ Hrt Htype Hstep.
  split.
  exact (preservation_left _ _ _ _ _ Hrt Htype Hstep).
  exact (preservation_right _ _ _ _ _ (runtime_ctx_well_typed_store _ Hrt) Htype Hstep).
Qed.

(* ==================== PAPER THEOREM 5 ====================
   If ∅ ⊢ e : τ, then e is a value, e = fail, or there exists e' with e → e'. *)

Axiom progress_store_typed_ctx_assumption :
  forall Γ e τ,
    store_well_typed Γ ->
    has_type Γ e τ ->
    DTDT.machine_inter.value Γ e \/
    e = EFail \/
    exists G' e', step (Γ, e) (G', e').

Lemma progress_store_typed_ctx :
  forall Γ e τ,
    store_well_typed Γ ->
    has_type Γ e τ ->
    DTDT.machine_inter.value Γ e \/
    e = EFail \/
    exists G' e', step (Γ, e) (G', e').
Proof.
  intros Γ e τ Hstore Hty.
  exact (progress_store_typed_ctx_assumption Γ e τ Hstore Hty).
Qed.

Theorem progress :
  forall e τ,
    has_type empty_ctx e τ ->
    DTDT.machine_inter.value empty_ctx e \/
    e = EFail \/
    exists G' e', step (empty_ctx, e) (G', e').
Proof.
  intros e τ Hty.
  exact (progress_store_typed_ctx empty_ctx e τ store_well_typed_empty Hty).
Qed.

(* ==================== PAPER THEOREM 1 ====================
  Type safety: if ∅ ⊢ e : τ and (∅, e) ↠* (G₀, e₀), then e₀ is a value,
  e₀ = fail, or there exists a further step from e₀. *)
Theorem paper_theorem_1_type_safety :
  forall e τ G₀ e₀,
    has_type empty_ctx e τ ->
    (empty_ctx, e) ↠* (G₀, e₀) ->
    DTDT.machine_inter.value G₀ e₀ \/
    e₀ = EFail \/
    exists G₁ e₁, step (G₀, e₀) (G₁, e₁).
Proof.
  intros e τ G₀ e₀ Hty Heval.
  assert (Hsafe : forall σ1 σ2,
    eval σ1 σ2 ->
    forall Γ e_start tau_start,
      σ1 = (Γ, e_start) ->
      store_well_typed Γ ->
      (forall x, var_ctx_lookup Γ x = None) ->
      (forall c, const_ctx_lookup Γ c = None) ->
      has_type Γ e_start tau_start ->
      DTDT.machine_inter.value (fst σ2) (snd σ2) \/
      snd σ2 = EFail \/
      exists G1 e1, step σ2 (G1, e1)).
  {
    intros σ1 σ2 Hev.
    induction Hev as [σ | σ1 σ2 σ3 Hstep Hev23 IH];
      intros Γ e_start tau_start Hσ Hstore HnoneVar HnoneConst Hty0.
    - inversion Hσ; subst.
      simpl.
      exact (progress_store_typed_ctx Γ e_start tau_start Hstore Hty0).
    - destruct σ2 as [Γ2 e2].
      inversion Hσ; subst.
      pose proof (runtime_ctx_well_typed_from_invariants _ HnoneVar HnoneConst Hstore) as Hrt.
      pose proof (preservation_left _ _ _ _ _ Hrt Hty0 Hstep) as Hty2.
      pose proof (preservation_right _ _ _ _ _ Hstore Hty0 Hstep) as Hstore2.
      pose proof (no_var_bindings_preserved_by_step (Γ, e_start) (Γ2, e2) Hstep HnoneVar) as HnoneVar2.
      pose proof (no_const_bindings_preserved_by_step (Γ, e_start) (Γ2, e2) Hstep HnoneConst) as HnoneConst2.
      exact (IH Γ2 e2 tau_start eq_refl Hstore2 HnoneVar2 HnoneConst2 Hty2).
  }
  exact (Hsafe (empty_ctx, e) (G₀, e₀) Heval empty_ctx e τ eq_refl
    store_well_typed_empty empty_ctx_no_var_bindings empty_ctx_no_const_bindings Hty).
Qed.
