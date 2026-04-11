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
Lemma subtype_base_essential_inv :
  forall G t1 t2 b,
    subtype G t1 t2 ->
    essential_type t2 = TBase b ->
    essential_type t1 = TBase b.
Proof.
  intros G t1 t2 b Hsub Hbase.
  induction Hsub; simpl in *; try discriminate; inversion Hbase; reflexivity.
Qed.

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

Lemma self_to_TArr :
  forall tau e tau1 tau2,
    self tau e = TArr tau1 tau2 ->
    tau = TArr tau1 tau2.
Proof.
  intros tau e tau1 tau2 Hself.
  destruct tau as [b | var tb expr | tdom tcod | var tdom tcod | t1 t2 | t]; simpl in Hself; try discriminate.
  destruct tdom; simpl in Hself; try discriminate; inversion Hself; subst; reflexivity.
Qed.

Lemma self_to_TArrDep_cases :
  forall tau e x tau1 tau2,
    self tau e = TArrDep x tau1 tau2 ->
    tau = TArrDep x tau1 tau2 \/
    exists b tau2', tau = TArr (TBase b) tau2'.
Proof.
  intros tau e x tau1 tau2 Hself.
  destruct tau as [b | var tb expr | tdom tcod | var tdom tcod | t1 t2 | t]; simpl in Hself; try discriminate.
  destruct tdom; simpl in Hself; try discriminate.
  - right.
    eexists _, _. reflexivity.
  - left.
    inversion Hself; subst. reflexivity.
Qed.

Lemma self_to_TProd :
  forall tau e tau1 tau2,
    self tau e = TProd tau1 tau2 ->
    tau = TProd tau1 tau2.
Proof.
  intros tau e tau1 tau2 Hself.
  destruct tau as [b | var tb expr | tdom tcod | var tdom tcod | t1 t2 | t]; simpl in Hself; try discriminate.
  - destruct tdom; simpl in Hself; discriminate.
  - inversion Hself; subst. reflexivity.
Qed.

Lemma self_essential_base_inv :
  forall tau e b,
    essential_type (self tau e) = TBase b ->
    essential_type tau = TBase b.
Proof.
  intros tau e b Hself.
  destruct tau as [b0 | var tb expr | tdom tcod | var tdom tcod | t1 t2 | t]; simpl in Hself; try discriminate.
  - inversion Hself; subst. reflexivity.
  - inversion Hself; subst. reflexivity.
  - destruct tdom; simpl in Hself; discriminate.
Qed.

Lemma no_simple_arrow_value_nobindings :
  forall G v tau1 tau2,
    (forall x, var_ctx_lookup G x = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    has_type G v (TArr tau1 tau2) ->
    DTDT.machine_inter.value G v ->
    False.
Proof.
  intros G v tau1 tau2 HnoneVar HnoneConst Hty Hv.
  remember (TArr tau1 tau2) as targ eqn:Heqtarg.
  revert tau1 tau2 Heqtarg.
  induction Hty; intros tau1' tau2' Heqtarg; subst;
    try solve [inversion Heqtarg];
    try solve [inversion Hv; subst; try discriminate; discriminate].
  all: try match goal with
  | Hlookup : const_ctx_lookup _ _ = Some _ |- _ =>
      rewrite HnoneConst in Hlookup; discriminate
  end.
  all: try match goal with
  | Hlookup : var_ctx_lookup _ _ = Some _ |- _ =>
      rewrite HnoneVar in Hlookup; discriminate
  end.
  all: try match goal with
  | Hself : self ?tau ?e = TArr _ _ |- _ =>
      apply self_to_TArr in Hself;
      subst;
      eapply IHHty; eauto
  end.
  all: try match goal with
  | Hsub : subtype _ _ (TArr _ _) |- _ =>
      inversion Hsub; subst; try discriminate;
      eapply IHHty; eauto
  end.
Qed.

Lemma canonical_forms_fun_dep_nobindings :
  forall G v x tau1 tau2,
    (forall y, var_ctx_lookup G y = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    has_type G v (TArrDep x tau1 tau2) ->
    DTDT.machine_inter.value G v ->
    exists f y tau1' tau2' body,
      v = EFix f y tau1' tau2' body.
Proof.
  intros G v x tau1 tau2 HnoneVar HnoneConst Hty Hv.
  remember (TArrDep x tau1 tau2) as targ eqn:Heqtarg.
  revert x tau1 tau2 Heqtarg.
  induction Hty; intros x' tau1' tau2' Heqtarg; subst;
    try solve [inversion Heqtarg];
    try solve [inversion Hv; subst; try discriminate].
  all: try match goal with
  | Hlookup : const_ctx_lookup _ _ = Some _ |- _ =>
      rewrite HnoneConst in Hlookup; discriminate
  end.
  all: try match goal with
  | Hlookup : var_ctx_lookup _ _ = Some _ |- _ =>
      rewrite HnoneVar in Hlookup; discriminate
  end.
  all: try solve [do 5 eexists; reflexivity].
  all: try match goal with
  | Hself : self ?tau ?e = TArrDep _ _ _ |- _ =>
      destruct (self_to_TArrDep_cases _ _ _ _ _ Hself) as [Htau | [b [tau2'' Htau]]];
      [ subst; eapply IHHty; eauto
      | subst; exfalso; eapply no_simple_arrow_value_nobindings; eauto ]
  end.
  all: try match goal with
  | Hsub : subtype _ _ (TArrDep _ _ _) |- _ =>
      inversion Hsub; subst; try discriminate;
      eapply IHHty; eauto
  end.
Qed.

Lemma canonical_forms_base_essential_nobindings :
  forall G v ty b,
    (forall x, var_ctx_lookup G x = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    has_type G v ty ->
    DTDT.machine_inter.value G v ->
    essential_type ty = TBase b ->
    base_value v.
Proof.
  intros G v ty b HnoneVar HnoneConst Hty Hv Hbase.
  remember G as C eqn:HeqC.
  revert b HnoneVar HnoneConst HeqC Hv Hbase.
  induction Hty; intros b' HnoneVar HnoneConst HeqC Hv Hbase; subst; simpl in Hbase;
    try discriminate;
    try solve [inversion Hv; subst; constructor].
  all: try match goal with
  | Hlookup : const_ctx_lookup _ _ = Some _ |- _ =>
      rewrite HnoneConst in Hlookup; discriminate
  end.
  all: try match goal with
  | Hlookup : var_ctx_lookup _ _ = Some _ |- _ =>
      rewrite HnoneVar in Hlookup; discriminate
  end.
  all: try match goal with
  | Hself : essential_type (self ?tau ?e) = TBase ?b |- _ =>
      apply self_essential_base_inv in Hself;
      eapply IHHty; eauto
  end.
  all: try match goal with
  | Hsub : subtype _ _ _ |- _ =>
      eapply IHHty; eauto;
      eapply subtype_base_essential_inv; eauto
  end.
Qed.

Lemma nat_literal_base :
  forall G n ty b,
    has_type G (ENat n) ty ->
    essential_type ty = TBase b ->
    b = BNat.
Proof.
  intros G n ty b Hty.
  remember (ENat n) as e eqn:Heqe.
  revert b Heqe.
  induction Hty; intros b' Heqe Hbase; inversion Heqe; subst; simpl in Hbase; try discriminate.
  - inversion Hbase. reflexivity.
  - eapply IHHty.
    + reflexivity.
    + apply self_essential_base_inv in Hbase. exact Hbase.
  - eapply IHHty.
    + reflexivity.
    + eapply subtype_base_essential_inv; eauto.
Qed.

Lemma bool_literal_base :
  forall G b ty b',
    has_type G (EBool b) ty ->
    essential_type ty = TBase b' ->
    b' = BBool.
Proof.
  intros G b ty b' Hty.
  remember (EBool b) as e eqn:Heqe.
  revert b' Heqe.
  induction Hty; intros b'' Heqe Hbase; inversion Heqe; subst; simpl in Hbase; try discriminate.
  - inversion Hbase. reflexivity.
  - eapply IHHty.
    + reflexivity.
    + apply self_essential_base_inv in Hbase. exact Hbase.
  - eapply IHHty.
    + reflexivity.
    + eapply subtype_base_essential_inv; eauto.
Qed.

Lemma string_literal_base :
  forall G s ty b,
    has_type G (EString s) ty ->
    essential_type ty = TBase b ->
    b = BString.
Proof.
  intros G s ty b Hty.
  remember (EString s) as e eqn:Heqe.
  revert b Heqe.
  induction Hty; intros b' Heqe Hbase; inversion Heqe; subst; simpl in Hbase; try discriminate.
  - inversion Hbase. reflexivity.
  - eapply IHHty.
    + reflexivity.
    + apply self_essential_base_inv in Hbase. exact Hbase.
  - eapply IHHty.
    + reflexivity.
    + eapply subtype_base_essential_inv; eauto.
Qed.

Lemma unit_literal_base :
  forall G ty b,
    has_type G (EUnit tt) ty ->
    essential_type ty = TBase b ->
    b = BUnit.
Proof.
  intros G ty b Hty.
  remember (EUnit tt) as e eqn:Heqe.
  revert b Heqe.
  induction Hty; intros b' Heqe Hbase; inversion Heqe; subst; simpl in Hbase; try discriminate.
  - inversion Hbase. reflexivity.
  - eapply IHHty.
    + reflexivity.
    + apply self_essential_base_inv in Hbase. exact Hbase.
  - eapply IHHty.
    + reflexivity.
    + eapply subtype_base_essential_inv; eauto.
Qed.

Lemma canonical_forms_bool_essential_nobindings :
  forall G v ty,
    (forall x, var_ctx_lookup G x = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    has_type G v ty ->
    DTDT.machine_inter.value G v ->
    essential_type ty = TBase BBool ->
    v = EBool true \/ v = EBool false.
Proof.
  intros G v ty HnoneVar HnoneConst Hty Hv Hbool.
  pose proof (canonical_forms_base_essential_nobindings G v ty BBool HnoneVar HnoneConst Hty Hv Hbool) as Hbasev.
  destruct Hbasev as [n | b0 | | s0].
  - exfalso.
    pose proof (nat_literal_base G n ty BBool Hty Hbool) as Hnat.
    discriminate.
  - subst. destruct b0; [left | right]; reflexivity.
  - exfalso.
    pose proof (unit_literal_base G ty BBool Hty Hbool) as Hunit.
    discriminate.
  - exfalso.
    pose proof (string_literal_base G s0 ty BBool Hty Hbool) as Hstring.
    discriminate.
Qed.

Lemma canonical_forms_nat_essential_nobindings :
  forall G v ty,
    (forall x, var_ctx_lookup G x = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    has_type G v ty ->
    DTDT.machine_inter.value G v ->
    essential_type ty = TBase BNat ->
    exists n, v = ENat n.
Proof.
  intros G v ty HnoneVar HnoneConst Hty Hv Hnat.
  pose proof (canonical_forms_base_essential_nobindings G v ty BNat HnoneVar HnoneConst Hty Hv Hnat) as Hbasev.
  destruct Hbasev as [n | b0 | | s0].
  - subst. eexists. reflexivity.
  - exfalso.
    pose proof (bool_literal_base G b0 ty BNat Hty Hnat) as Hbool.
    discriminate.
  - exfalso.
    pose proof (unit_literal_base G ty BNat Hty Hnat) as Hunit.
    discriminate.
  - exfalso.
    pose proof (string_literal_base G s0 ty BNat Hty Hnat) as Hstring.
    discriminate.
Qed.

Lemma has_type_pure_nobindings_base :
  forall G e t,
    (forall x, var_ctx_lookup G x = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    has_type_pure G e t ->
    essential_type_is_base_type t = true.
Proof.
  intros G e t HnoneVar HnoneConst Hpure.
  induction Hpure.
  - rewrite HnoneVar in H. discriminate.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - rewrite HnoneConst in H. discriminate.
  - simpl in IHHpure1. discriminate.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma canonical_forms_pair_nobindings :
  forall G v tau1 tau2,
    (forall x, var_ctx_lookup G x = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    has_type G v (TProd tau1 tau2) ->
    DTDT.machine_inter.value G v ->
    exists v1 v2, v = EPair v1 v2.
Proof.
  intros G v tau1 tau2 HnoneVar HnoneConst Hty Hv.
  remember G as C eqn:HeqC.
  remember (TProd tau1 tau2) as tp eqn:Heqtp.
  revert tau1 tau2 HnoneVar HnoneConst HeqC Heqtp Hv.
  induction Hty; intros tau1' tau2' HnoneVar HnoneConst HeqC Heqtp Hv; inversion Heqtp; subst;
    try solve [inversion Hv; subst; try discriminate].
  all: try match goal with
  | Hlookup : const_ctx_lookup _ _ = Some _ |- _ =>
      rewrite HnoneConst in Hlookup; discriminate
  end.
  all: try match goal with
  | Hlookup : var_ctx_lookup _ _ = Some _ |- _ =>
      rewrite HnoneVar in Hlookup; discriminate
  end.
  - eexists _, _. reflexivity.
  - exfalso.
    pose proof (has_type_pure_nobindings_base _ _ _ HnoneVar HnoneConst (H (TProd tau1' tau2'))) as Hbeta.
    simpl in Hbeta. discriminate.
  - inversion H; subst; try discriminate.
    exact (IHHty _ _ HnoneVar HnoneConst eq_refl eq_refl Hv).
Qed.

Lemma canonical_forms_ref_nobindings :
  forall G v tau,
    (forall x, var_ctx_lookup G x = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    has_type G v (TRef tau) ->
    DTDT.machine_inter.value G v ->
    exists l stored_tau stored,
      v = ELoc l /\ store_ctx_lookup G l = Some (stored_tau, stored).
Proof.
  intros G v tau HnoneVar HnoneConst Hty Hv.
  remember G as C eqn:HeqC.
  remember (TRef tau) as tr eqn:Heqtr.
  revert tau HnoneVar HnoneConst HeqC Heqtr Hv.
  induction Hty; intros tau' HnoneVar HnoneConst HeqC Heqtr Hv; inversion Heqtr; subst;
    try solve [inversion Hv; subst; try discriminate].
  all: try match goal with
  | Hlookup : const_ctx_lookup _ _ = Some _ |- _ =>
      rewrite HnoneConst in Hlookup; discriminate
  end.
  all: try match goal with
  | Hlookup : var_ctx_lookup _ _ = Some _ |- _ =>
      rewrite HnoneVar in Hlookup; discriminate
  end.
  - eexists _, _, _. split; [reflexivity | exact H].
  - match goal with
    | Hself : self ?t ?e = TRef ?t' |- _ =>
        apply self_ref_inv in Hself;
        inversion Hself; subst
    end.
    eapply IHHty; eauto.
  - inversion H; subst; try discriminate.
    exact (IHHty _ HnoneVar HnoneConst eq_refl eq_refl Hv).
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

Lemma var_base_pure_well_typed_empty :
  var_base_pure_well_typed empty_ctx.
Proof.
  intros ?x t v Hlookup.
  unfold var_ctx_lookup, empty_ctx in Hlookup.
  simpl in Hlookup.
  inversion Hlookup.
Qed.

Lemma const_step_well_typed_empty :
  const_step_well_typed empty_ctx.
Proof.
  intros c t e v ?top Hlookup _ _.
  unfold const_step_well_typed, const_ctx_lookup, empty_ctx in Hlookup.
  simpl in Hlookup.
  inversion Hlookup.
Qed.

Lemma const_step_pure_well_typed_empty :
  const_step_pure_well_typed empty_ctx.
Proof.
  intros c t e v ? Hlookup _ _.
  unfold const_step_pure_well_typed, const_ctx_lookup, empty_ctx in Hlookup.
  simpl in Hlookup.
  inversion Hlookup.
Qed.

Lemma runtime_ctx_well_typed_empty :
  runtime_ctx_well_typed empty_ctx.
Proof.
  constructor.
  - exact var_well_typed_empty.
  - exact var_base_pure_well_typed_empty.
  - exact const_well_typed_empty.
  - exact const_step_well_typed_empty.
  - exact const_step_pure_well_typed_empty.
  - exact store_well_typed_empty.
Qed.

Lemma var_well_typed_lookup :
  forall G x t v,
    var_well_typed G ->
    var_ctx_lookup G x = Some (t, v) ->
    ty_valid G t /\ has_type G v t.
Proof.
  intros G x t v Hvar Hlookup.
  exact (Hvar x t v Hlookup).
Qed.

Lemma const_well_typed_lookup :
  forall G c t e,
    const_well_typed G ->
    const_ctx_lookup G c = Some (t, e) ->
    ty_valid G t /\ has_type G e t.
Proof.
  intros G c t e Hconst Hlookup.
  exact (Hconst c t e Hlookup).
Qed.

Lemma runtime_ctx_well_typed_var :
  forall G,
    runtime_ctx_well_typed G ->
    var_well_typed G.
Proof.
  intros G Hrt.
  inversion Hrt.
  exact H.
Qed.

Lemma runtime_ctx_well_typed_var_base_pure :
  forall G,
    runtime_ctx_well_typed G ->
    var_base_pure_well_typed G.
Proof.
  intros G Hrt.
  inversion Hrt.
  exact H0.
Qed.

Lemma runtime_ctx_well_typed_const :
  forall G,
    runtime_ctx_well_typed G ->
    const_well_typed G.
Proof.
  intros G Hrt.
  inversion Hrt.
  exact H1.
Qed.

Lemma runtime_ctx_well_typed_store :
  forall G,
    runtime_ctx_well_typed G ->
    store_well_typed G.
Proof.
  intros G Hrt.
  inversion Hrt.
  exact H4.
Qed.

Lemma runtime_ctx_well_typed_const_step :
  forall G,
    runtime_ctx_well_typed G ->
    const_step_well_typed G.
Proof.
  intros G Hrt.
  inversion Hrt.
  exact H2.
Qed.

Lemma runtime_ctx_well_typed_const_step_pure :
  forall G,
    runtime_ctx_well_typed G ->
    const_step_pure_well_typed G.
Proof.
  intros G Hrt.
  inversion Hrt.
  exact H3.
Qed.

Lemma var_well_typed_from_none_lookup :
  forall G,
    (forall x, var_ctx_lookup G x = None) ->
    var_well_typed G.
Proof.
  intros G Hnone x t v Hlookup.
  rewrite (Hnone x) in Hlookup.
  inversion Hlookup.
Qed.

Lemma var_base_pure_well_typed_from_none_lookup :
  forall G,
    (forall x, var_ctx_lookup G x = None) ->
    var_base_pure_well_typed G.
Proof.
  intros G Hnone x t v Hlookup.
  rewrite (Hnone x) in Hlookup.
  inversion Hlookup.
Qed.

Lemma const_well_typed_from_none_lookup :
  forall G,
    (forall c, const_ctx_lookup G c = None) ->
    const_well_typed G.
Proof.
  intros G Hnone c t e Hlookup.
  rewrite (Hnone c) in Hlookup.
  inversion Hlookup.
Qed.

Lemma const_step_well_typed_from_none_lookup :
  forall G,
    (forall c, const_ctx_lookup G c = None) ->
    const_step_well_typed G.
Proof.
  intros G Hnone c t e v ttop Hlookup _ _.
  rewrite (Hnone c) in Hlookup.
  inversion Hlookup.
Qed.

Lemma const_step_pure_well_typed_from_none_lookup :
  forall G,
    (forall c, const_ctx_lookup G c = None) ->
    const_step_pure_well_typed G.
Proof.
  intros G Hnone c t e v ty Hlookup _ _.
  rewrite (Hnone c) in Hlookup.
  inversion Hlookup.
Qed.

Lemma runtime_ctx_well_typed_from_invariants :
  forall G,
    (forall x, var_ctx_lookup G x = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    store_well_typed G ->
    runtime_ctx_well_typed G.
Proof.
  intros G HnoneVar HnoneConst Hstore.
  constructor.
  - exact (var_well_typed_from_none_lookup _ HnoneVar).
  - exact (var_base_pure_well_typed_from_none_lookup _ HnoneVar).
  - exact (const_well_typed_from_none_lookup _ HnoneConst).
  - exact (const_step_well_typed_from_none_lookup _ HnoneConst).
  - exact (const_step_pure_well_typed_from_none_lookup _ HnoneConst).
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

Lemma fresh_string_list_not_in :
  forall l,
    ~ List.In (fresh_string_list l) l.
Proof.
  intros l Hin.
  unfold fresh_string_list in *.
  pose proof (stringmap.fresh_string_of_set_fresh (list_to_set l) "x"%string) as Hfresh.
  apply Hfresh.
  apply elem_of_list_to_set.
  apply elem_of_list_In.
  exact Hin.
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



Fixpoint compose_eval_ctx (E1 E2 : eval_ctx) : eval_ctx :=
  match E1 with
  | ECHole => E2
  | ECAppL E e2 => ECAppL (compose_eval_ctx E E2) e2
  | ECAppR v1 E => ECAppR v1 (compose_eval_ctx E E2)
  | ECPairL E e2 => ECPairL (compose_eval_ctx E E2) e2
  | ECPairR v1 E => ECPairR v1 (compose_eval_ctx E E2)
  | ECFst E => ECFst (compose_eval_ctx E E2)
  | ECSnd E => ECSnd (compose_eval_ctx E E2)
  | ECIf E e2 e3 => ECIf (compose_eval_ctx E E2) e2 e3
  | ECNewRef t E => ECNewRef t (compose_eval_ctx E E2)
  | ECGet E => ECGet (compose_eval_ctx E E2)
  | ECSetL E e2 => ECSetL (compose_eval_ctx E E2) e2
  | ECSetR v1 E => ECSetR v1 (compose_eval_ctx E E2)
  | ECPlusL E e2 => ECPlusL (compose_eval_ctx E E2) e2
  | ECPlusR v1 E => ECPlusR v1 (compose_eval_ctx E E2)
  | ECNot E => ECNot (compose_eval_ctx E E2)
  | ECAndL E e2 => ECAndL (compose_eval_ctx E E2) e2
  | ECAndR v1 E => ECAndR v1 (compose_eval_ctx E E2)
  | ECOrL E e2 => ECOrL (compose_eval_ctx E E2) e2
  | ECOrR v1 E => ECOrR v1 (compose_eval_ctx E E2)
  | ECImpL E e2 => ECImpL (compose_eval_ctx E E2) e2
  | ECImpR v1 E => ECImpR v1 (compose_eval_ctx E E2)
  | ECEqL E e2 => ECEqL (compose_eval_ctx E E2) e2
  | ECEqR v1 E => ECEqR v1 (compose_eval_ctx E E2)
  end.

Lemma plug_compose_eval_ctx :
  forall E1 E2 e,
    plug E1 (plug E2 e) = plug (compose_eval_ctx E1 E2) e.
Proof.
  induction E1; intros E2 e; simpl; try rewrite IHE1; reflexivity.
Qed.



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

Lemma value_preserved_by_add_var_none :
  forall G x tx witness v,
    var_ctx_lookup G x = None ->
    value G v ->
    value (ctx_add_var G x tx witness) v.
Proof.
  intros G x tx witness v Hnone Hv.
  induction Hv.
  - apply DTDT.machine_inter.VNat.
  - apply DTDT.machine_inter.VBool.
  - apply DTDT.machine_inter.VUnit.
  - apply DTDT.machine_inter.VString.
  - eapply DTDT.machine_inter.VConst.
    unfold const_ctx_lookup, ctx_add_var in *.
    simpl in *.
    exact H.
  - apply DTDT.machine_inter.VFix.
  - apply DTDT.machine_inter.VPair; assumption.
  - eapply DTDT.machine_inter.VVar.
    unfold var_ctx_lookup, ctx_add_var in *.
    simpl in *.
    destruct (String.eq_dec x0 x) as [Heq | Hneq].
    + subst.
      rewrite H in Hnone.
      discriminate.
    + apply lookup_insert_Some.
      right.
      split; [congruence | exact H].
  - eapply DTDT.machine_inter.VLoc.
    unfold store_ctx_lookup, ctx_add_var in *.
    simpl in *.
    exact H.
Qed.

Lemma pure_fail_ctx_absurd_runtime_early :
  forall G E t,
    has_type_pure G (plug E EFail) t ->
    False.
Proof.
  induction E; intros t Hpure; simpl in *; inversion Hpure; subst; eauto.
Qed.

Lemma pure_step_preserved_by_add_var_none :
  forall G1 G2 e e' x tx witness t,
    step (G1, e) (G2, e') ->
    has_type_pure G1 e t ->
    var_ctx_lookup G1 x = None ->
    step (ctx_add_var G1 x tx witness, e) (ctx_add_var G2 x tx witness, e').
Proof.
  intros G1 G2 e e' x tx witness t Hstep.
  revert t.
  set (P := fun c1 c2 : ctx * i_expr =>
    match c1, c2 with
    | (G1', e1), (G2', e2) =>
        forall t',
          has_type_pure G1' e1 t' ->
          var_ctx_lookup G1' x = None ->
          step (ctx_add_var G1' x tx witness, e1)
               (ctx_add_var G2' x tx witness, e2)
    end).
  change (P (G1, e) (G2, e')).
  induction Hstep; unfold P in *; simpl in *; intros t' Hpure' Hnone.
  - apply StepCtx.
    match goal with
    | Hsub : has_type_pure ?G (plug E e0) _ |- _ =>
        destruct (plug_has_typed_hole_pure G E e0 t' Hsub) as [th Hhole]
    end.
    eapply IHHstep.
    + exact Hhole.
    + exact Hnone.
  - eapply StepConst.
    + unfold const_ctx_lookup, ctx_add_var in *. simpl. exact H.
    + eapply value_preserved_by_add_var_none; eauto.
  - inversion Hpure'; subst.
    destruct (String.eq_dec x0 x) as [Heq | Hneq].
    + subst. rewrite H in Hnone. discriminate.
    + eapply StepVar.
      unfold var_ctx_lookup, ctx_add_var in *. simpl.
      apply lookup_insert_Some.
      right.
      split; [congruence | exact H].
  - inversion Hpure'. inversion H3; subst.
  - inversion Hpure'.
  - inversion Hpure'.
  - inversion Hpure'.
  - inversion Hpure'.
  - inversion Hpure'.
  - inversion Hpure'.
  - inversion Hpure'.
  - exfalso. eapply pure_fail_ctx_absurd_runtime_early. exact Hpure'.
  - apply StepNot.
  - apply StepAnd.
  - apply StepOr.
  - apply StepImp.
  - eapply StepEq; eauto.
  - apply StepPlus.
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

Lemma pure_step_same_ctx :
  forall G1 G2 e e' t,
    step (G1, e) (G2, e') ->
    has_type_pure G1 e t ->
    G1 = G2.
Proof.
  intros G1 G2 e e' t Hstep.
  revert t.
  set (P := fun c1 c2 : ctx * i_expr =>
    match c1, c2 with
    | (G1', e1), (G2', e2) => forall t', has_type_pure G1' e1 t' -> G1' = G2'
    end).
  change (P (G1, e) (G2, e')).
  induction Hstep; unfold P in *; simpl in *; intros t' Hpure'.
  - destruct (plug_has_typed_hole_pure _ _ _ _ Hpure') as [th Hhole].
    exact (IHHstep _ Hhole).
  - reflexivity.
  - reflexivity.
  - inversion Hpure'. inversion H3; subst.
  - inversion Hpure'.
  - inversion Hpure'.
  - inversion Hpure'.
  - inversion Hpure'.
  - inversion Hpure'.
  - inversion Hpure'.
  - inversion Hpure'.
  - exfalso.
    eapply pure_fail_ctx_absurd_runtime_early.
    exact Hpure'.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma has_type_fix_body :
  forall G f x t1 t2 e t,
    has_type G (EFix f x t1 t2 e) t ->
    ~ List.In x (ty_vars t1) /\
    ty_valid G (TArrDep x t1 t2) /\
    has_type (ctx_add_var (ctx_add_const G f (TArrDep x t1 t2) (EFix f x t1 t2 e)) x t1 (EVar x)) e t2.
Proof.
  intros G f x t1 t2 e t Hty.
  remember (EFix f x t1 t2 e) as efix eqn:Heqefix.
  revert f x t1 t2 e Heqefix.
  induction Hty; intros f0 x0 t10 t20 e0 Heqefix; subst;
    try solve [inversion Heqefix].
  - inversion Heqefix; subst.
    repeat split; assumption.
  - exact (IHHty _ _ _ _ _ eq_refl).
  - exact (IHHty _ _ _ _ _ eq_refl).
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
Lemma step_var_preserves_pure_runtime :
  forall G x tbound vbound ty,
    runtime_ctx_well_typed G ->
    var_ctx_lookup G x = Some (tbound, vbound) ->
    has_type_pure G (EVar x) ty ->
    has_type_pure G vbound ty.
Proof.
  intros G x tbound vbound ty Hrt Hlookup Hpure.
  inversion Hpure as [x0 tb e0 Hvar Hbeta | | | | | | | | | | | | ]; subst.
  pose proof (bool_prop_eq_true _ Hbeta) as Hbeta_eq.
  pose proof ((runtime_ctx_well_typed_var_base_pure _ Hrt) x tb e0 Hvar Hbeta_eq) as Hpv.
  rewrite Hlookup in Hvar.
  inversion Hvar; subst.
  exact Hpv.
Qed.

Lemma step_const_preserves_pure_runtime :
  forall G c t e v ty,
    runtime_ctx_well_typed G ->
    const_ctx_lookup G c = Some (t, e) ->
    value G v ->
    has_type_pure G (EApp (EConst c) v) ty ->
    has_type_pure G e ty.
Proof.
  intros G c t e v ty Hrt Hlookup Hval Hpure.
  eapply (runtime_ctx_well_typed_const_step_pure _ Hrt); eauto.
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
    + exact H.
    + apply ty_valid_store_update. exact H0.
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
    + apply IHHty1. exact Hlookup.
    + apply IHHty2. exact Hlookup.
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

Lemma has_type_preserved_by_step_ctx_change :
  forall G1 G2 e e'' q tq,
    step (G1, e) (G2, e'') ->
    has_type G1 q tq ->
    has_type G2 q tq.
Proof.
  intros G1 G2 e e'' q tq Hstep.
  revert q tq.
  dependent induction Hstep; intros q tq Hty.
  - eapply IHHstep; [reflexivity | reflexivity | exact Hty].
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - eapply has_type_store_extension_fresh; eauto.
  - exact Hty.
  - eapply has_type_store_update_same_type; eauto.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
Qed.

Lemma ty_valid_preserved_by_step_ctx_change :
  forall G1 G2 e e'' t,
    step (G1, e) (G2, e'') ->
    ty_valid G1 t ->
    ty_valid G2 t.
Proof.
  intros G1 G2 e e'' t Hstep.
  dependent induction Hstep; intro Hvalid.
  - eapply IHHstep; [reflexivity | reflexivity | exact Hvalid].
  - exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
  - eapply ty_valid_store_extension_fresh; eauto.
  - exact Hvalid.
  - eapply ty_valid_store_update; exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
  - exact Hvalid.
Qed.



Lemma has_type_pure_preserved_by_step_ctx_change :
  forall G1 G2 e e'' q tq,
    step (G1, e) (G2, e'') ->
    has_type_pure G1 q tq ->
    has_type_pure G2 q tq.
Proof.
  intros G1 G2 e e'' q tq Hstep.
  revert q tq.
  dependent induction Hstep; intros q tq Hty.
  - eapply IHHstep; [reflexivity | reflexivity | exact Hty].
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - eapply has_type_pure_store_update.
    exact Hty.
  - exact Hty.
  - eapply has_type_pure_store_update.
    exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
Qed.


Lemma pure_fail_ctx_absurd_runtime :
  forall G E t,
    has_type_pure G (plug E EFail) t ->
    False.
Proof.
  induction E; intros t Hpure; simpl in *; inversion Hpure; subst; eauto.
Qed.

Lemma pure_step_ctx_preservation_runtime :
  forall G1 G2 e e' E t,
    step (G1, e) (G2, e') ->
    (forall t0, has_type_pure G1 e t0 -> has_type_pure G2 e' t0) ->
    has_type_pure G1 (plug E e) t ->
    has_type_pure G2 (plug E e') t.
Proof.
  intros G1 G2 e e' E t Hstep Hinner.
  revert t.
  induction E; intros t Hpure; simpl in *; try solve [inversion Hpure].
  - exact (Hinner _ Hpure).
  - inversion Hpure; subst.
    eapply PApp.
    + exact H1.
    + match goal with
      | Hsub : has_type_pure G1 (plug E e) (TArr _ _) |- _ => exact (IHE _ Hsub)
      end.
    + match goal with
      | Hsub : has_type_pure G1 _ _ |- _ =>
          eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hsub]
      end.
  - inversion Hpure; subst.
    eapply PApp.
    + exact H1.
    + match goal with
      | Hsub : has_type_pure G1 _ _ |- _ =>
          eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hsub]
      end.
    + match goal with
      | Hsub : has_type_pure G1 (plug E e) _ |- _ => exact (IHE _ Hsub)
      end.
  - inversion Hpure; subst.
    eapply PPlus.
    + match goal with
      | Hsub : has_type_pure G1 (plug E e) (TBase BNat) |- _ => exact (IHE _ Hsub)
      end.
    + match goal with
      | Hsub : has_type_pure G1 _ (TBase BNat) |- _ =>
          eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hsub]
      end.
  - inversion Hpure; subst.
    eapply PPlus.
    + match goal with
      | Hsub : has_type_pure G1 _ (TBase BNat) |- _ =>
          eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hsub]
      end.
    + match goal with
      | Hsub : has_type_pure G1 (plug E e) (TBase BNat) |- _ => exact (IHE _ Hsub)
      end.
  - inversion Hpure; subst.
    eapply PNot.
    match goal with
    | Hsub : has_type_pure G1 (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
    end.
  - inversion Hpure; subst.
    eapply PAnd.
    + match goal with
      | Hsub : has_type_pure G1 (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
    + match goal with
      | Hsub : has_type_pure G1 _ (TBase BBool) |- _ =>
          eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hsub]
      end.
  - inversion Hpure; subst.
    eapply PAnd.
    + match goal with
      | Hsub : has_type_pure G1 _ (TBase BBool) |- _ =>
          eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hsub]
      end.
    + match goal with
      | Hsub : has_type_pure G1 (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
  - inversion Hpure; subst.
    eapply POr.
    + match goal with
      | Hsub : has_type_pure G1 (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
    + match goal with
      | Hsub : has_type_pure G1 _ (TBase BBool) |- _ =>
          eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hsub]
      end.
  - inversion Hpure; subst.
    eapply POr.
    + match goal with
      | Hsub : has_type_pure G1 _ (TBase BBool) |- _ =>
          eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hsub]
      end.
    + match goal with
      | Hsub : has_type_pure G1 (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
  - inversion Hpure; subst.
    eapply PImp.
    + match goal with
      | Hsub : has_type_pure G1 (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
    + match goal with
      | Hsub : has_type_pure G1 _ (TBase BBool) |- _ =>
          eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hsub]
      end.
  - inversion Hpure; subst.
    eapply PImp.
    + match goal with
      | Hsub : has_type_pure G1 _ (TBase BBool) |- _ =>
          eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hsub]
      end.
    + match goal with
      | Hsub : has_type_pure G1 (plug E e) (TBase BBool) |- _ => exact (IHE _ Hsub)
      end.
  - inversion Hpure; subst.
    match goal with
    | Hsub : has_type_pure G1 (plug E e) (TBase ?tb) |- _ =>
        match goal with
        | Hother : has_type_pure G1 ?er (TBase tb) |- _ =>
            eapply (PEq G2 (plug E e') er tb);
            [ exact (IHE _ Hsub)
            | eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hother] ]
        end
    end.
  - inversion Hpure; subst.
    match goal with
    | Hsub : has_type_pure G1 (plug E e) (TBase ?tb) |- _ =>
        match goal with
        | Hother : has_type_pure G1 ?el (TBase tb) |- _ =>
            eapply (PEq G2 el (plug E e') tb);
            [ eapply has_type_pure_preserved_by_step_ctx_change; [exact Hstep | exact Hother]
            | exact (IHE _ Hsub) ]
        end
    end.
Qed.

Lemma preservation_pure_terms_runtime_sigma :
  forall sigma1 sigma2,
    step sigma1 sigma2 ->
    runtime_ctx_well_typed (fst sigma1) ->
    forall ty,
      has_type_pure (fst sigma1) (snd sigma1) ty ->
      has_type_pure (fst sigma2) (snd sigma2) ty.
Proof.
  intros sigma1 sigma2 Hstep.
  induction Hstep; intros Hrt ty Hpure; simpl in *.
  - eapply pure_step_ctx_preservation_runtime.
    + exact Hstep.
    + intros t0 Hinner. eapply IHHstep; eauto.
    + exact Hpure.
  - eapply step_const_preserves_pure_runtime; eauto.
  - eapply step_var_preserves_pure_runtime; eauto.
  - inversion Hpure; subst; try inversion H1; try inversion H2; try inversion H3.
  - inversion Hpure; subst; try inversion H1; try inversion H2; try inversion H3.
  - inversion Hpure; subst; try inversion H1; try inversion H2; try inversion H3.
  - inversion Hpure; subst; try inversion H1; try inversion H2; try inversion H3.
  - inversion Hpure; subst; try inversion H1; try inversion H2; try inversion H3.
  - inversion Hpure; subst; try inversion H1; try inversion H2; try inversion H3.
  - inversion Hpure; subst; try inversion H1; try inversion H2; try inversion H3.
  - inversion Hpure; subst; try inversion H1; try inversion H2; try inversion H3.
  - exfalso. eapply pure_fail_ctx_absurd_runtime. exact Hpure.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PNat.
Qed.

Lemma has_type_preserved_by_pure_step_ctx_change_add_var_none :
  forall G1 G2 e e'' x tx witness q tq t,
    step (G1, e) (G2, e'') ->
    has_type_pure G1 e t ->
    var_ctx_lookup G1 x = None ->
    has_type (ctx_add_var G1 x tx witness) q tq ->
    has_type (ctx_add_var G2 x tx witness) q tq.
Proof.
  intros G1 G2 e e'' x tx witness q tq t Hstep Hpure Hnone Hty.
  eapply has_type_preserved_by_step_ctx_change.
  - eapply pure_step_preserved_by_add_var_none; eauto.
  - exact Hty.
Qed.

Lemma has_type_pure_preserved_by_pure_step_ctx_change_add_var_none :
  forall G1 G2 e e'' x tx witness q tq t,
    step (G1, e) (G2, e'') ->
    has_type_pure G1 e t ->
    var_ctx_lookup G1 x = None ->
    has_type_pure (ctx_add_var G1 x tx witness) q tq ->
    has_type_pure (ctx_add_var G2 x tx witness) q tq.
Proof.
  intros G1 G2 e e'' x tx witness q tq t Hstep Hpure Hnone Hty.
  eapply has_type_pure_preserved_by_step_ctx_change.
  - eapply pure_step_preserved_by_add_var_none; eauto.
  - exact Hty.
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

Lemma subtype_preserved_by_step_ctx_change :
  forall G1 G2 e e'' t1 t2,
    step (G1, e) (G2, e'') ->
    subtype G1 t1 t2 ->
    subtype G2 t1 t2.
Proof.
  intros G1 G2 e e'' t1 t2 Hstep.
  dependent induction Hstep; intro Hsub.
  - eapply IHHstep; [reflexivity | reflexivity | exact Hsub].
  - exact Hsub.
  - exact Hsub.
  - exact Hsub.
  - exact Hsub.
  - exact Hsub.
  - exact Hsub.
  - exact Hsub.
  - eapply subtype_store_extension_fresh; eauto.
  - exact Hsub.
  - eapply subtype_store_update; eauto.
  - exact Hsub.
  - exact Hsub.
  - exact Hsub.
  - exact Hsub.
  - exact Hsub.
  - exact Hsub.
  - exact Hsub.
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
  forall G v1 v2 t_top,
    has_type G (EFst (EPair v1 v2)) t_top ->
    value G v1 ->
    value G v2 ->
    has_type G v1 t_top.
Proof.
  intros G v1 v2 t_top Hty Hv1 Hv2.
  remember (EFst (EPair v1 v2)) as efst eqn:Heqefst.
  revert v1 v2 Hv1 Hv2 Heqefst.
  induction Hty; intros v1' v2' Hv1' Hv2' Heqefst;
    inversion Heqefst; subst; try discriminate.
  - destruct (inversion_pair _ _ _ _ _ Hty) as [Hleft _].
    exact Hleft.
  - exfalso.
    match goal with
    | Hpure : forall t1 : i_ty, has_type_pure _ (EFst (EPair v1' v2')) t1 |- _ =>
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

Lemma step_if_true_preserves_typing :
  forall G e1 e2 ttop,
    has_type G (EIf (EBool true) e1 e2) ttop ->
    has_type G e1 ttop.
Proof.
  intros G e1 e2 ttop Hty.
  remember (EIf (EBool true) e1 e2) as eif eqn:Heqeif.
  revert e1 e2 Heqeif.
  induction Hty; intros e1' e2' Heqeif; inversion Heqeif; subst; try discriminate.
  - exact Hty1.
  - match goal with
    | H : forall t1 : i_ty, has_type_pure _ (EIf (EBool true) e1' e2') t1 |- _ =>
        specialize (H (TBase BNat)); inversion H
    end.
  - eapply TSub.
    + eapply IHHty; reflexivity.
    + exact H.
Qed.

Lemma step_if_false_preserves_typing :
  forall G e1 e2 ttop,
    has_type G (EIf (EBool false) e1 e2) ttop ->
    has_type G e2 ttop.
Proof.
  intros G e1 e2 ttop Hty.
  remember (EIf (EBool false) e1 e2) as eif eqn:Heqeif.
  revert e1 e2 Heqeif.
  induction Hty; intros e1' e2' Heqeif; inversion Heqeif; subst; try discriminate.
  - exact Hty2.
  - match goal with
    | H : forall t1 : i_ty, has_type_pure _ (EIf (EBool false) e1' e2') t1 |- _ =>
        specialize (H (TBase BNat)); inversion H
    end.
  - eapply TSub.
    + eapply IHHty; reflexivity.
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

Axiom preservation_left_stepctx_assumption :
  forall Γ Γ' E e e' τ,
    runtime_ctx_well_typed Γ ->
    has_type Γ (plug E e) τ ->
    step (Γ, e) (Γ', e') ->
    has_type Γ' (plug E e') τ.


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
  - eapply step_if_true_preserves_typing; exact Hty.
  - eapply step_if_false_preserves_typing; exact Hty.
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
  - eapply step_if_true_preserves_typing; exact Hty.
  - eapply step_if_false_preserves_typing; exact Hty.
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

Lemma progress_pure_nobindings :
  forall G e t,
    (forall x, var_ctx_lookup G x = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    has_type_pure G e t ->
    DTDT.machine_inter.value G e \/
    exists e', step (G, e) (G, e').
Proof.
  intros G e t HnoneVar HnoneConst Hpure.
  induction Hpure as
    [x tau_base witness Hlookup Hbeta
    | n
    | b
    | s
    | u
    | c tau body Hlookup Hsimple
    | e1 e2 tau1 tau2 Hbeta Hfun IHfun Harg IHarg
    | eb Hbool IHbool
    | e1 e2 Hbool1 IH1 Hbool2 IH2
    | e1 e2 Hbool1 IH1 Hbool2 IH2
    | e1 e2 Hbool1 IH1 Hbool2 IH2
    | e1 e2 tb Hbase1 IH1 Hbase2 IH2
    | e1 e2 Hnat1 IH1 Hnat2 IH2].
  - rewrite HnoneVar in Hlookup. discriminate.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - destruct u.
    match goal with
    | |- DTDT.machine_inter.value ?Ctx (EUnit tt) \/ _ => left; exact (VUnit Ctx)
    end.
  - rewrite HnoneConst in Hlookup. discriminate.
  - destruct IHfun as [Hv1 | [e1' Hstep1]].
    + destruct IHarg as [Hv2 | [e2' Hstep2]].
      * exfalso.
        eapply (no_simple_arrow_value_nobindings G e1 tau1 tau2 HnoneVar HnoneConst).
        -- exact (has_type_pure_implies_has_type _ _ _ Hfun).
        -- exact Hv1.
      * right. exists (EApp e1 e2').
        eapply StepCtx with (E := ECAppR e1 ECHole).
        exact Hstep2.
    + right. exists (EApp e1' e2).
      eapply StepCtx with (E := ECAppL ECHole e2).
      exact Hstep1.
  - destruct IHbool as [Hv | [e' Hstep]].
    + pose proof
        (canonical_forms_bool_essential_nobindings G eb (TBase BBool)
          HnoneVar HnoneConst
          (has_type_pure_implies_has_type _ _ _ Hbool) Hv eq_refl) as Hb.
      destruct Hb as [Hb | Hb]; subst.
      * right. exists (EBool false). apply StepNot.
      * right. exists (EBool true). apply StepNot.
    + right. exists (ENot e').
      eapply StepCtx with (E := ECNot ECHole).
      exact Hstep.
  - destruct IH1 as [Hv1 | [e1' Hstep1]].
    + destruct IH2 as [Hv2 | [e2' Hstep2]].
      * pose proof
          (canonical_forms_bool_essential_nobindings G e1 (TBase BBool)
            HnoneVar HnoneConst
            (has_type_pure_implies_has_type _ _ _ Hbool1) Hv1 eq_refl) as Hb1.
        pose proof
          (canonical_forms_bool_essential_nobindings G e2 (TBase BBool)
            HnoneVar HnoneConst
            (has_type_pure_implies_has_type _ _ _ Hbool2) Hv2 eq_refl) as Hb2.
        destruct Hb1 as [Hb1 | Hb1]; destruct Hb2 as [Hb2 | Hb2]; subst;
          right; eexists; apply StepImp.
      * right. exists (EImp e1 e2').
        eapply StepCtx with (E := ECImpR e1 ECHole).
        exact Hstep2.
    + right. exists (EImp e1' e2).
      eapply StepCtx with (E := ECImpL ECHole e2).
      exact Hstep1.
  - destruct IH1 as [Hv1 | [e1' Hstep1]].
    + destruct IH2 as [Hv2 | [e2' Hstep2]].
      * pose proof
          (canonical_forms_bool_essential_nobindings G e1 (TBase BBool)
            HnoneVar HnoneConst
            (has_type_pure_implies_has_type _ _ _ Hbool1) Hv1 eq_refl) as Hb1.
        pose proof
          (canonical_forms_bool_essential_nobindings G e2 (TBase BBool)
            HnoneVar HnoneConst
            (has_type_pure_implies_has_type _ _ _ Hbool2) Hv2 eq_refl) as Hb2.
        destruct Hb1 as [Hb1 | Hb1]; destruct Hb2 as [Hb2 | Hb2]; subst;
          right; eexists; apply StepAnd.
      * right. exists (EAnd e1 e2').
        eapply StepCtx with (E := ECAndR e1 ECHole).
        exact Hstep2.
    + right. exists (EAnd e1' e2).
      eapply StepCtx with (E := ECAndL ECHole e2).
      exact Hstep1.
  - destruct IH1 as [Hv1 | [e1' Hstep1]].
    + destruct IH2 as [Hv2 | [e2' Hstep2]].
      * pose proof
          (canonical_forms_bool_essential_nobindings G e1 (TBase BBool)
            HnoneVar HnoneConst
            (has_type_pure_implies_has_type _ _ _ Hbool1) Hv1 eq_refl) as Hb1.
        pose proof
          (canonical_forms_bool_essential_nobindings G e2 (TBase BBool)
            HnoneVar HnoneConst
            (has_type_pure_implies_has_type _ _ _ Hbool2) Hv2 eq_refl) as Hb2.
        destruct Hb1 as [Hb1 | Hb1]; destruct Hb2 as [Hb2 | Hb2]; subst;
          right; eexists; apply StepOr.
      * right. exists (EOr e1 e2').
        eapply StepCtx with (E := ECOrR e1 ECHole).
        exact Hstep2.
    + right. exists (EOr e1' e2).
      eapply StepCtx with (E := ECOrL ECHole e2).
      exact Hstep1.
  - destruct IH1 as [Hv1 | [e1' Hstep1]].
    + destruct IH2 as [Hv2 | [e2' Hstep2]].
      * pose proof
          (canonical_forms_base_essential_nobindings G e1 (TBase tb) tb
            HnoneVar HnoneConst
            (has_type_pure_implies_has_type _ _ _ Hbase1) Hv1 eq_refl) as Hb1.
        pose proof
          (canonical_forms_base_essential_nobindings G e2 (TBase tb) tb
            HnoneVar HnoneConst
            (has_type_pure_implies_has_type _ _ _ Hbase2) Hv2 eq_refl) as Hb2.
        destruct (base_eq e1 e2) eqn:Hbeq.
        -- right. exists (EBool true). eapply StepEq; eauto.
        -- right. exists (EBool false). eapply StepEq; eauto.
      * right. exists (EEq e1 e2').
        eapply StepCtx with (E := ECEqR e1 ECHole).
        exact Hstep2.
    + right. exists (EEq e1' e2).
      eapply StepCtx with (E := ECEqL ECHole e2).
      exact Hstep1.
  - destruct IH1 as [Hv1 | [e1' Hstep1]].
    + destruct IH2 as [Hv2 | [e2' Hstep2]].
      * destruct
          (canonical_forms_nat_essential_nobindings G e1 (TBase BNat)
            HnoneVar HnoneConst
            (has_type_pure_implies_has_type _ _ _ Hnat1) Hv1 eq_refl) as [n1 Heq1].
        destruct
          (canonical_forms_nat_essential_nobindings G e2 (TBase BNat)
            HnoneVar HnoneConst
            (has_type_pure_implies_has_type _ _ _ Hnat2) Hv2 eq_refl) as [n2 Heq2].
        subst. right. exists (ENat (n1 + n2)). apply StepPlus.
      * right. exists (EPlus e1 e2').
        eapply StepCtx with (E := ECPlusR e1 ECHole).
        exact Hstep2.
    + right. exists (EPlus e1' e2).
      eapply StepCtx with (E := ECPlusL ECHole e2).
      exact Hstep1.
Qed.

Lemma progress_store_typed_ctx_nobindings :
  forall G e t,
    store_well_typed G ->
    (forall x, var_ctx_lookup G x = None) ->
    (forall c, const_ctx_lookup G c = None) ->
    has_type G e t ->
    DTDT.machine_inter.value G e \/
    e = EFail \/
    exists G' e', step (G, e) (G', e').
Proof.
  intros G e t Hstore HnoneVar HnoneConst Hty.
  induction Hty as
    [G0 s
    | G0 n
    | G0 b
    | G0 u
    | G0 c t body Hlookup
    | G0 x t body Hlookup
    | G0 x t body Hlookup Hbeta
    | G0 l t stored Hlookup
    | G0 t Hvalid
    | G0 f x t1 t2 body Hvalid Hbody IHbody
    | G0 e1 e2 x t1 t2 Harg IHarg Hpure Hfun IHfun
    | G0 e1 e2 t1 t2 Harg IHarg Hfun IHfun
    | G0 e1 e2 Hnat1 IH1 Hnat2 IH2
    | G0 eb Hbool IHbool
    | G0 e1 e2 Hbool1 IH1 Hbool2 IH2
    | G0 e1 e2 Hbool1 IH1 Hbool2 IH2
    | G0 e1 e2 Hbool1 IH1 Hbool2 IH2
    | G0 e1 e2 tb Hbase1 IH1 Hbase2 IH2
    | G0 t e Hvalid Hinner IHinner
    | G0 e t Href IHref
    | G0 e1 e2 t Href IHref Hval IHval
    | G0 e1 e2 t1 t2 H1 IH1 H2 IH2
    | G0 e t1 t2 Hpair IHpair
    | G0 e t1 t2 Hpair IHpair
    | G0 cond e1 e2 t Hcond Hthen IHthen Helse IHelse
    | G0 e t Hinner IHinner Hpure
    | G0 e t t' Hinner IHinner Hsub].
  - left. apply VString.
  - left. apply VNat.
  - left. apply VBool.
  - repeat match goal with u : unit |- _ => destruct u end.
    left. apply VUnit.
  - rewrite HnoneConst in Hlookup. discriminate.
  - rewrite HnoneVar in Hlookup. discriminate.
  - rewrite HnoneVar in Hlookup. discriminate.
  - left. econstructor. exact Hlookup.
  - right. left. reflexivity.
  - left. econstructor.
  - destruct (IHfun Hstore HnoneVar HnoneConst) as [Hvfun | [Hfailfun | [G1 [e1' Hstep1]]]].
    + pose proof (progress_pure_nobindings G0 e2 t1 HnoneVar HnoneConst (Hpure t1)) as Hargprog.
      destruct Hargprog as [Hvarg | [e2' Hstep2]].
      * destruct (canonical_forms_fun_dep_nobindings G0 e1 x t1 t2 HnoneVar HnoneConst Hfun Hvfun)
          as [f' [y [t1' [t2' [body' Heqfun]]]]].
        subst.
        right. right. exists G0.
        exists (expr_subst_fun f' (EFix f' y t1' t2' body') (expr_subst y e2 body')).
        apply StepFix. exact Hvarg.
      * right. right. exists G0. exists (EApp e1 e2').
        eapply StepCtx with (E := ECAppR e1 ECHole).
        exact Hstep2.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECAppL ECHole e2).
    + right. right. exists G1. exists (EApp e1' e2).
      eapply StepCtx with (E := ECAppL ECHole e2).
      exact Hstep1.
  - destruct (IHfun Hstore HnoneVar HnoneConst) as [Hvfun | [Hfailfun | [G1 [e1' Hstep1]]]].
    + exfalso.
      eapply (no_simple_arrow_value_nobindings G0 e1 t1 t2 HnoneVar HnoneConst);
        eauto.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECAppL ECHole e2).
    + right. right. exists G1. exists (EApp e1' e2).
      eapply StepCtx with (E := ECAppL ECHole e2).
      exact Hstep1.
  - destruct (IH1 Hstore HnoneVar HnoneConst) as [Hv1 | [Hfail1 | [G1 [e1' Hstep1]]]].
    + destruct (IH2 Hstore HnoneVar HnoneConst) as [Hv2 | [Hfail2 | [G2 [e2' Hstep2]]]].
      * destruct (canonical_forms_nat_essential_nobindings G0 e1 (TBase BNat)
          HnoneVar HnoneConst Hnat1 Hv1 eq_refl) as [n1 Heq1].
        destruct (canonical_forms_nat_essential_nobindings G0 e2 (TBase BNat)
          HnoneVar HnoneConst Hnat2 Hv2 eq_refl) as [n2 Heq2].
        subst. right. right. exists G0. exists (ENat (n1 + n2)).
        apply StepPlus.
      * subst. right. right. exists G0. exists EFail.
        eapply StepFail with (E := ECPlusR e1 ECHole).
      * right. right. exists G2. exists (EPlus e1 e2').
        eapply StepCtx with (E := ECPlusR e1 ECHole).
        exact Hstep2.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECPlusL ECHole e2).
    + right. right. exists G1. exists (EPlus e1' e2).
      eapply StepCtx with (E := ECPlusL ECHole e2).
      exact Hstep1.
  - destruct (IHbool Hstore HnoneVar HnoneConst) as [Hv | [Hfail | [G1 [eb' Hstep]]]].
    + destruct (canonical_forms_bool_essential_nobindings G0 eb (TBase BBool)
        HnoneVar HnoneConst Hbool Hv eq_refl) as [Hb | Hb]; subst.
      * right. right. exists G0. exists (EBool false).
        apply StepNot.
      * right. right. exists G0. exists (EBool true).
        apply StepNot.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECNot ECHole).
    + right. right. exists G1. exists (ENot eb').
      eapply StepCtx with (E := ECNot ECHole).
      exact Hstep.
  - destruct (IH1 Hstore HnoneVar HnoneConst) as [Hv1 | [Hfail1 | [G1 [e1' Hstep1]]]].
    + destruct (IH2 Hstore HnoneVar HnoneConst) as [Hv2 | [Hfail2 | [G2 [e2' Hstep2]]]].
      * destruct (canonical_forms_bool_essential_nobindings G0 e1 (TBase BBool)
          HnoneVar HnoneConst Hbool1 Hv1 eq_refl) as [Hb1 | Hb1];
        destruct (canonical_forms_bool_essential_nobindings G0 e2 (TBase BBool)
          HnoneVar HnoneConst Hbool2 Hv2 eq_refl) as [Hb2 | Hb2];
        subst; right; right; exists G0; eexists; apply StepImp.
      * subst. right. right. exists G0. exists EFail.
        eapply StepFail with (E := ECImpR e1 ECHole).
      * right. right. exists G2. exists (EImp e1 e2').
        eapply StepCtx with (E := ECImpR e1 ECHole).
        exact Hstep2.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECImpL ECHole e2).
    + right. right. exists G1. exists (EImp e1' e2).
      eapply StepCtx with (E := ECImpL ECHole e2).
      exact Hstep1.
  - destruct (IH1 Hstore HnoneVar HnoneConst) as [Hv1 | [Hfail1 | [G1 [e1' Hstep1]]]].
    + destruct (IH2 Hstore HnoneVar HnoneConst) as [Hv2 | [Hfail2 | [G2 [e2' Hstep2]]]].
      * destruct (canonical_forms_bool_essential_nobindings G0 e1 (TBase BBool)
          HnoneVar HnoneConst Hbool1 Hv1 eq_refl) as [Hb1 | Hb1];
        destruct (canonical_forms_bool_essential_nobindings G0 e2 (TBase BBool)
          HnoneVar HnoneConst Hbool2 Hv2 eq_refl) as [Hb2 | Hb2];
        subst; right; right; exists G0; eexists; apply StepAnd.
      * subst. right. right. exists G0. exists EFail.
        eapply StepFail with (E := ECAndR e1 ECHole).
      * right. right. exists G2. exists (EAnd e1 e2').
        eapply StepCtx with (E := ECAndR e1 ECHole).
        exact Hstep2.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECAndL ECHole e2).
    + right. right. exists G1. exists (EAnd e1' e2).
      eapply StepCtx with (E := ECAndL ECHole e2).
      exact Hstep1.
  - destruct (IH1 Hstore HnoneVar HnoneConst) as [Hv1 | [Hfail1 | [G1 [e1' Hstep1]]]].
    + destruct (IH2 Hstore HnoneVar HnoneConst) as [Hv2 | [Hfail2 | [G2 [e2' Hstep2]]]].
      * destruct (canonical_forms_bool_essential_nobindings G0 e1 (TBase BBool)
          HnoneVar HnoneConst Hbool1 Hv1 eq_refl) as [Hb1 | Hb1];
        destruct (canonical_forms_bool_essential_nobindings G0 e2 (TBase BBool)
          HnoneVar HnoneConst Hbool2 Hv2 eq_refl) as [Hb2 | Hb2];
        subst; right; right; exists G0; eexists; apply StepOr.
      * subst. right. right. exists G0. exists EFail.
        eapply StepFail with (E := ECOrR e1 ECHole).
      * right. right. exists G2. exists (EOr e1 e2').
        eapply StepCtx with (E := ECOrR e1 ECHole).
        exact Hstep2.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECOrL ECHole e2).
    + right. right. exists G1. exists (EOr e1' e2).
      eapply StepCtx with (E := ECOrL ECHole e2).
      exact Hstep1.
  - destruct (IH1 Hstore HnoneVar HnoneConst) as [Hv1 | [Hfail1 | [G1 [e1' Hstep1]]]].
    + destruct (IH2 Hstore HnoneVar HnoneConst) as [Hv2 | [Hfail2 | [G2 [e2' Hstep2]]]].
      * pose proof (canonical_forms_base_essential_nobindings G0 e1 (TBase tb) tb
          HnoneVar HnoneConst Hbase1 Hv1 eq_refl) as Hb1.
        pose proof (canonical_forms_base_essential_nobindings G0 e2 (TBase tb) tb
          HnoneVar HnoneConst Hbase2 Hv2 eq_refl) as Hb2.
        destruct (base_eq e1 e2) eqn:Hbeq.
        -- right. right. exists G0. exists (EBool true).
           eapply StepEq; eauto.
        -- right. right. exists G0. exists (EBool false).
           eapply StepEq; eauto.
      * subst. right. right. exists G0. exists EFail.
        eapply StepFail with (E := ECEqR e1 ECHole).
      * right. right. exists G2. exists (EEq e1 e2').
        eapply StepCtx with (E := ECEqR e1 ECHole).
        exact Hstep2.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECEqL ECHole e2).
    + right. right. exists G1. exists (EEq e1' e2).
      eapply StepCtx with (E := ECEqL ECHole e2).
      exact Hstep1.
  - destruct (IHinner Hstore HnoneVar HnoneConst) as [Hv | [Hfail | [G1 [e' Hstep]]]].
    + set (l := fresh_string_list (var_dom G0 ++ store_dom G0)).
      assert (~ In l (var_dom G0 ++ store_dom G0)) as Hfresh.
      { subst l. apply fresh_string_list_not_in. }
      assert (~ In l (var_dom G0)) as HfreshVar.
      { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
      assert (~ In l (store_dom G0)) as HfreshStore.
      { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
      right. right. exists (ctx_add_store G0 l t e). exists (ELoc l).
      apply StepNew; assumption.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECNewRef t ECHole).
    + right. right. exists G1. exists (ENewRef t e').
      eapply StepCtx with (E := ECNewRef t ECHole).
      exact Hstep.
  - destruct (IHref Hstore HnoneVar HnoneConst) as [Hv | [Hfail | [G1 [e' Hstep]]]].
    + destruct (canonical_forms_ref_nobindings G0 e t HnoneVar HnoneConst Href Hv)
        as [l [stored_t [stored [Heq Hlookup]]]].
      subst. right. right. exists G0. exists stored.
      eapply StepGet. exact Hlookup.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECGet ECHole).
    + right. right. exists G1. exists (EGet e').
      eapply StepCtx with (E := ECGet ECHole).
      exact Hstep.
  - destruct (IHref Hstore HnoneVar HnoneConst) as [Hv1 | [Hfail1 | [G1 [e1' Hstep1]]]].
    + destruct (IHval Hstore HnoneVar HnoneConst) as [Hv2 | [Hfail2 | [G2 [e2' Hstep2]]]].
      * destruct (canonical_forms_ref_nobindings G0 e1 t HnoneVar HnoneConst Href Hv1)
          as [l [stored_t [stored [Heq Hlookup]]]].
        subst. right. right. exists (ctx_add_store G0 l stored_t e2). exists (EUnit tt).
        eapply StepSet.
        -- exact Hv2.
        -- exact Hlookup.
      * subst. right. right. exists G0. exists EFail.
        eapply StepFail with (E := ECSetR e1 ECHole).
      * right. right. exists G2. exists (ESet e1 e2').
        eapply StepCtx with (E := ECSetR e1 ECHole).
        exact Hstep2.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECSetL ECHole e2).
    + right. right. exists G1. exists (ESet e1' e2).
      eapply StepCtx with (E := ECSetL ECHole e2).
      exact Hstep1.
  - destruct (IH1 Hstore HnoneVar HnoneConst) as [Hv1 | [Hfail1 | [G1 [e1' Hstep1]]]].
    + destruct (IH2 Hstore HnoneVar HnoneConst) as [Hv2 | [Hfail2 | [G2 [e2' Hstep2]]]].
      * left. exact (DTDT.machine_inter.VPair G0 e1 e2 Hv1 Hv2).
      * subst. right. right. exists G0. exists EFail.
        eapply StepFail with (E := ECPairR e1 ECHole).
      * right. right. exists G2. exists (EPair e1 e2').
        eapply StepCtx with (E := ECPairR e1 ECHole).
        exact Hstep2.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECPairL ECHole e2).
    + right. right. exists G1. exists (EPair e1' e2).
      eapply StepCtx with (E := ECPairL ECHole e2).
      exact Hstep1.
  - destruct (IHpair Hstore HnoneVar HnoneConst) as [Hv | [Hfail | [G1 [e' Hstep]]]].
    + destruct (canonical_forms_pair_nobindings G0 e t1 t2 HnoneVar HnoneConst Hpair Hv)
        as [v1 [v2 Heq]].
      subst. inversion Hv; subst.
      right. right. exists G0. exists v1.
      apply StepFst; assumption.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECFst ECHole).
    + right. right. exists G1. exists (EFst e').
      eapply StepCtx with (E := ECFst ECHole).
      exact Hstep.
  - destruct (IHpair Hstore HnoneVar HnoneConst) as [Hv | [Hfail | [G1 [e' Hstep]]]].
    + destruct (canonical_forms_pair_nobindings G0 e t1 t2 HnoneVar HnoneConst Hpair Hv)
        as [v1 [v2 Heq]].
      subst. inversion Hv; subst.
      right. right. exists G0. exists v2.
      apply StepSnd; assumption.
    + subst. right. right. exists G0. exists EFail.
      eapply StepFail with (E := ECSnd ECHole).
    + right. right. exists G1. exists (ESnd e').
      eapply StepCtx with (E := ECSnd ECHole).
      exact Hstep.
  - destruct (progress_pure_nobindings G0 cond (TBase BBool) HnoneVar HnoneConst Hcond)
      as [Hv | [cond' Hstep]].
    + destruct (canonical_forms_bool_essential_nobindings G0 cond (TBase BBool)
        HnoneVar HnoneConst (has_type_pure_implies_has_type _ _ _ Hcond) Hv eq_refl)
        as [Hb | Hb]; subst.
      * right. right. exists G0. exists e1.
        apply StepIfTrue.
      * right. right. exists G0. exists e2.
        apply StepIfFalse.
    + right. right. exists G0. exists (EIf cond' e1 e2).
      eapply StepCtx with (E := ECIf ECHole e1 e2).
      exact Hstep.
  - exact (IHinner Hstore HnoneVar HnoneConst).
  - exact (IHinner Hstore HnoneVar HnoneConst).
Qed.

(* ==================== PAPER THEOREM 5 ====================
   If ∅ ⊢ e : τ, then e is a value, e = fail, or there exists e' with e → e'. *)

Theorem progress :
  forall e tau,
    has_type empty_ctx e tau ->
    DTDT.machine_inter.value empty_ctx e \/
    e = EFail \/
    exists G' e', step (empty_ctx, e) (G', e').
Proof.
  intros e tau Hty.
  exact (progress_store_typed_ctx_nobindings empty_ctx e tau
    store_well_typed_empty empty_ctx_no_var_bindings empty_ctx_no_const_bindings Hty).
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
      exact (progress_store_typed_ctx_nobindings _ e_start tau_start Hstore HnoneVar HnoneConst Hty0).
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










