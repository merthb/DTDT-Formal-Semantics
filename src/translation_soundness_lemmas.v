Require Import DTDT.syntax.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.semantic_rules_surf.
Require Import DTDT.type_directed_translation.
Require Import DTDT.foundational_lemmas_inter.
Require Import DTDT.type_safety_lemmas_inter.
Require Import Coq.Program.Equality.
From stdpp Require Import fin_maps.

Lemma trans_ctx_surf_lookup_var :
  forall (Gamma : ctx_surf) (x : string) (tau : ty) (e : expr),
    var_ctx_lookup_surf Gamma x = Some (tau, e) ->
    var_ctx_lookup (trans_ctx_surf Gamma) x = Some (trans_type tau, trans_expr_dref_free e).
Proof.
  intros [vars consts] x tau e Hlookup.
  unfold var_ctx_lookup_surf, var_ctx_lookup, trans_ctx_surf in *.
  simpl in *.
  apply lookup_fmap_Some.
  exists (tau, e).
  split; [reflexivity | exact Hlookup].
Qed.

Lemma trans_ctx_surf_lookup_const :
  forall (Gamma : ctx_surf) (c : string) (tau : ty) (e : expr),
    const_ctx_lookup_surf Gamma c = Some (tau, e) ->
    const_ctx_lookup (trans_ctx_surf Gamma) c = Some (trans_type tau, trans_expr_dref_free e).
Proof.
  intros [vars consts] c tau e Hlookup.
  unfold const_ctx_lookup_surf, const_ctx_lookup, trans_ctx_surf in *.
  simpl in *.
  apply lookup_fmap_Some.
  exists (tau, e).
  split; [reflexivity | exact Hlookup].
Qed.

Lemma trans_ctx_surf_add_var :
  forall (Gamma : ctx_surf) (x : string) (tau : ty) (e : expr),
    trans_ctx_surf (ctx_add_var_surf Gamma x tau e) =
    ctx_add_var (trans_ctx_surf Gamma) x (trans_type tau) (trans_expr_dref_free e).
Proof.
  intros [vars consts] x tau e.
  unfold trans_ctx_surf, ctx_add_var_surf, ctx_add_var.
  simpl.
  f_equal.
  rewrite (fmap_insert (fun te => match te with (t, e0) => (trans_type t, trans_expr_dref_free e0) end) vars x (tau, e)).
  reflexivity.
Qed.

Lemma trans_ctx_surf_add_const :
  forall (Gamma : ctx_surf) (c : string) (tau : ty) (e : expr),
    trans_ctx_surf (ctx_add_const_surf Gamma c tau e) =
    ctx_add_const (trans_ctx_surf Gamma) c (trans_type tau) (trans_expr_dref_free e).
Proof.
  intros [vars consts] c tau e.
  unfold trans_ctx_surf, ctx_add_const_surf, ctx_add_const.
  simpl.
  f_equal.
  rewrite (fmap_insert (fun te => match te with (t, e0) => (trans_type t, trans_expr_dref_free e0) end) consts c (tau, e)).
  reflexivity.
Qed.

Lemma trans_type_essential_type :
  forall tau,
    trans_type (essential_type_surf tau) = essential_type (trans_type tau).
Proof.
  intros tau.
  destruct tau; reflexivity.
Qed.

Lemma trans_type_base_flag :
  forall tau,
    essential_type_is_base_type_surf tau = essential_type_is_base_type (trans_type tau).
Proof.
  intros tau.
  destruct tau; reflexivity.
Qed.

Lemma is_simple_type_surf_trans :
  forall tau,
    is_simple_type_surf tau = true ->
    is_simple_type (trans_type tau) = true.
Proof.
  induction tau; simpl; intros Hsimp; try exact Hsimp; try discriminate.
  - apply andb_true_iff in Hsimp as [Hsimp1 Hsimp2].
    rewrite (IHtau1 Hsimp1), (IHtau2 Hsimp2).
    reflexivity.
  - apply andb_true_iff in Hsimp as [Hsimp1 Hsimp2].
    rewrite (IHtau1 Hsimp1), (IHtau2 Hsimp2).
    reflexivity.
  - apply IHtau in Hsimp.
    exact Hsimp.
  - apply IHtau in Hsimp.
    unfold dref_encoding.
    simpl.
    rewrite Hsimp.
    reflexivity.
Qed.

Lemma trans_expr_partial_pure :
  forall (Gamma : ctx_surf) (e : expr) (tau : ty),
    has_type_pure_surf Gamma e tau ->
    exists ep,
      trans_expr_partial e = Some ep /\
      has_type_pure (trans_ctx_surf Gamma) ep (trans_type tau).
Proof.
  intros Gamma e tau Hpure.
  induction Hpure.
  - exists (EVar x).
    split.
    + reflexivity.
    + rewrite trans_type_essential_type.
      apply PVar with (e := trans_expr_dref_free v).
      * eapply trans_ctx_surf_lookup_var; eauto.
      * rewrite <- trans_type_base_flag.
        exact H0.
  - exists (ENat n).
    split.
    + reflexivity.
    + constructor.
  - exists (EBool b).
    split.
    + reflexivity.
    + constructor.
  - exists (EString s).
    split.
    + reflexivity.
    + constructor.
  - exists (EUnit u).
    split.
    + reflexivity.
    + constructor.
  - exists (EConst c).
    split.
    + reflexivity.
    + apply PConst with (e := trans_expr_dref_free v).
      * eapply trans_ctx_surf_lookup_const; eauto.
      * destruct (is_simple_type (trans_type τ)) eqn:Hsimp.
        { exact I. }
        { assert (Hsimp_surf : is_simple_type_surf τ = true).
          { destruct (is_simple_type_surf τ); simpl in H0; [reflexivity | contradiction]. }
          pose proof (is_simple_type_surf_trans τ Hsimp_surf) as Hsimp_true.
          rewrite Hsimp_true in Hsimp.
          discriminate. }
  - destruct IHHpure1 as [e1p Hpair1].
    destruct Hpair1 as [He1p Hty1].
    destruct IHHpure2 as [e2p Hpair2].
    destruct Hpair2 as [He2p Hty2].
    exists (EApp e1p e2p).
    split.
    + simpl.
      rewrite He1p, He2p.
      reflexivity.
    + eapply PApp.
      * rewrite <- trans_type_base_flag.
        exact H.
      * exact Hty1.
      * exact Hty2.
  - destruct IHHpure as [ep Hpair].
    destruct Hpair as [Hep Hty].
    exists (ENot ep).
    split.
    + simpl.
      rewrite Hep.
      reflexivity.
    + apply PNot.
      exact Hty.
  - destruct IHHpure1 as [e1p Hpair1].
    destruct Hpair1 as [He1p Hty1].
    destruct IHHpure2 as [e2p Hpair2].
    destruct Hpair2 as [He2p Hty2].
    exists (EImp e1p e2p).
    split.
    + simpl.
      rewrite He1p, He2p.
      reflexivity.
    + apply PImp; assumption.
  - destruct IHHpure1 as [e1p Hpair1].
    destruct Hpair1 as [He1p Hty1].
    destruct IHHpure2 as [e2p Hpair2].
    destruct Hpair2 as [He2p Hty2].
    exists (EAnd e1p e2p).
    split.
    + simpl.
      rewrite He1p, He2p.
      reflexivity.
    + apply PAnd; assumption.
  - destruct IHHpure1 as [e1p Hpair1].
    destruct Hpair1 as [He1p Hty1].
    destruct IHHpure2 as [e2p Hpair2].
    destruct Hpair2 as [He2p Hty2].
    exists (EOr e1p e2p).
    split.
    + simpl.
      rewrite He1p, He2p.
      reflexivity.
    + apply POr; assumption.
  - destruct IHHpure1 as [e1p Hpair1].
    destruct Hpair1 as [He1p Hty1].
    destruct IHHpure2 as [e2p Hpair2].
    destruct Hpair2 as [He2p Hty2].
    exists (EPlus e1p e2p).
    split.
    + simpl.
      rewrite He1p, He2p.
      reflexivity.
    + apply PPlus; assumption.
Qed.

Lemma trans_expr_partial_pure_sound :
  forall (Gamma : ctx_surf) (e : expr) (tau : ty) (ep : i_expr),
    trans_expr_partial e = Some ep ->
    has_type_pure_surf Gamma e tau ->
    has_type_pure (trans_ctx_surf Gamma) ep (trans_type tau).
Proof.
  intros Gamma e tau ep Htrans Hpure.
  destruct (trans_expr_partial_pure Gamma e tau Hpure) as [ep' Hpair].
  destruct Hpair as [Htrans' Hty].
  rewrite Htrans in Htrans'.
  inversion Htrans'.
  subst.
  exact Hty.
Qed.

Combined Scheme surface_expr_ty_ind from expr_ind_mut, ty_ind_mut.

Lemma free_var_translation_subsets :
  (forall e e' y,
    trans_expr_partial e = Some e' ->
    List.In y (free_exp_vars e') ->
    List.In y (free_exp_vars_surf e)) /\
  (forall t y,
    List.In y (free_ty_vars (trans_type t)) ->
    List.In y (free_ty_vars_surf t)).
Proof.
  apply surface_expr_ty_ind.
  - intros s e' y Htrans Hin.
    simpl in Htrans.
    inversion Htrans; subst.
    simpl in Hin.
    exact Hin.
  - intros b e' y Htrans Hin.
    simpl in Htrans.
    inversion Htrans; subst.
    simpl in Hin.
    exact Hin.
  - intros n e' y Htrans Hin.
    simpl in Htrans.
    inversion Htrans; subst.
    simpl in Hin.
    exact Hin.
  - intros u e' y Htrans Hin.
    simpl in Htrans.
    inversion Htrans; subst.
    simpl in Hin.
    exact Hin.
  - intros c e' y Htrans Hin.
    simpl in Htrans.
    inversion Htrans; subst.
    simpl in Hin.
    exact Hin.
  - intros x e' y Htrans Hin.
    simpl in Htrans.
    inversion Htrans; subst.
    simpl in Hin.
    exact Hin.
  - intros l e' y Htrans Hin.
    simpl in Htrans.
    inversion Htrans; subst.
    simpl in Hin.
    exact Hin.
  - intros f x t1 IHt1 t2 IHt2 body IHbody e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial body) eqn:Hbodytrans;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + simpl.
      apply in_or_app.
      left.
      apply IHt1.
      exact Hin.
    + apply in_remove_string in Hin as [Hin Hneq].
      simpl.
      apply in_or_app.
      right.
      apply in_app_or in Hin as [Hin | Hin].
      * apply in_remove_string_intro.
        { exact Hneq. }
        apply in_or_app.
        left.
        apply IHt2.
        exact Hin.
      * apply in_remove_string_intro.
        { exact Hneq. }
        apply in_or_app.
        right.
        apply IHbody with (e' := i).
        -- exact eq_refl.
        -- exact Hin.
  - intros e1 IHe1 e2 IHe2 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e1) eqn:He1; try discriminate.
    destruct (trans_expr_partial e2) eqn:He2;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHe1 with (e' := i).
      * exact eq_refl.
      * exact Hin.
    + right.
      apply IHe2 with (e' := i0).
      * exact eq_refl.
      * exact Hin.
  - intros e1 IHe1 e2 IHe2 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e1) eqn:He1; try discriminate.
    destruct (trans_expr_partial e2) eqn:He2;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHe1 with (e' := i).
      * exact eq_refl.
      * exact Hin.
    + right.
      apply IHe2 with (e' := i0).
      * exact eq_refl.
      * exact Hin.
  - intros e1 IHe1 e2 IHe2 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e1) eqn:He1; try discriminate.
    destruct (trans_expr_partial e2) eqn:He2;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHe1 with (e' := i).
      * exact eq_refl.
      * exact Hin.
    + right.
      apply IHe2 with (e' := i0).
      * exact eq_refl.
      * exact Hin.
  - intros e0 IHe0 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e0) eqn:He0;
      inversion Htrans; subst; clear Htrans.
    simpl in *.
    apply IHe0 with (e' := i).
    + exact eq_refl.
    + simpl in Hin.
      exact Hin.
  - intros e0 IHe0 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e0) eqn:He0;
      inversion Htrans; subst; clear Htrans.
    simpl in *.
    apply IHe0 with (e' := i).
    + exact eq_refl.
    + exact Hin.
  - intros e1 IHe1 e2 IHe2 e3 IHe3 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e1) eqn:He1; try discriminate.
    destruct (trans_expr_partial e2) eqn:He2; try discriminate.
    destruct (trans_expr_partial e3) eqn:He3;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + simpl.
      apply in_or_app.
      left.
      apply IHe1 with (e' := i).
      * exact eq_refl.
      * exact Hin.
    + apply in_app_or in Hin as [Hin | Hin].
      * simpl.
        apply in_or_app.
        right.
        apply in_or_app.
        left.
        apply IHe2 with (e' := i0).
        -- exact eq_refl.
        -- exact Hin.
      * simpl.
        apply in_or_app.
        right.
        apply in_or_app.
        right.
        apply IHe3 with (e' := i1).
        -- exact eq_refl.
        -- exact Hin.
  - intros e0 IHe0 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e0) eqn:He0;
      inversion Htrans; subst; clear Htrans.
    simpl in *.
    apply IHe0 with (e' := i).
    + exact eq_refl.
    + exact Hin.
  - intros e1 IHe1 e2 IHe2 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e1) eqn:He1; try discriminate.
    destruct (trans_expr_partial e2) eqn:He2;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHe1 with (e' := i).
      * exact eq_refl.
      * exact Hin.
    + right.
      apply IHe2 with (e' := i0).
      * exact eq_refl.
      * exact Hin.
  - intros e1 IHe1 e2 IHe2 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e1) eqn:He1; try discriminate.
    destruct (trans_expr_partial e2) eqn:He2;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHe1 with (e' := i).
      * exact eq_refl.
      * exact Hin.
    + right.
      apply IHe2 with (e' := i0).
      * exact eq_refl.
      * exact Hin.
  - intros e1 IHe1 e2 IHe2 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e1) eqn:He1; try discriminate.
    destruct (trans_expr_partial e2) eqn:He2;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHe1 with (e' := i).
      * exact eq_refl.
      * exact Hin.
    + right.
      apply IHe2 with (e' := i0).
      * exact eq_refl.
      * exact Hin.
  - intros e1 IHe1 e2 IHe2 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e1) eqn:He1; try discriminate.
    destruct (trans_expr_partial e2) eqn:He2;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHe1 with (e' := i).
      * exact eq_refl.
      * exact Hin.
    + right.
      apply IHe2 with (e' := i0).
      * exact eq_refl.
      * exact Hin.
  - intros t IHt e0 IHe0 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e0) eqn:He0;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHt.
      exact Hin.
    + right.
      apply IHe0 with (e' := i).
      * exact eq_refl.
      * exact Hin.
  - intros e0 IHe0 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e0) eqn:He0;
      inversion Htrans; subst; clear Htrans.
    simpl in *.
    apply IHe0 with (e' := i).
    + exact eq_refl.
    + exact Hin.
  - intros e1 IHe1 e2 IHe2 e' y Htrans Hin.
    simpl in Htrans.
    destruct (trans_expr_partial e1) eqn:He1; try discriminate.
    destruct (trans_expr_partial e2) eqn:He2;
      inversion Htrans; subst; clear Htrans.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHe1 with (e' := i).
      * exact eq_refl.
      * exact Hin.
    + right.
      apply IHe2 with (e' := i0).
      * exact eq_refl.
      * exact Hin.
  - intros e0 IHe0 e' y Htrans Hin.
    simpl in Htrans.
    discriminate.
  - intros e0 IHe0 e' y Htrans Hin.
    simpl in Htrans.
    discriminate.
  - intros e1 IHe1 e2 IHe2 e' y Htrans Hin.
    simpl in Htrans.
    discriminate.
  - intros e0 IHe0 t IHt e' y Htrans Hin.
    simpl in Htrans.
    simpl.
    apply in_or_app.
    left.
    eapply IHe0; eauto.
  - intros e0 IHe0 e' y Htrans Hin.
    simpl in Htrans.
    eapply IHe0; eauto.
  - intros e0 IHe0 e' y Htrans Hin.
    simpl in Htrans.
    eapply IHe0; eauto.
  - intros b y Hin.
    simpl in Hin.
    exact Hin.
  - intros x b pred IHpred y Hin.
    simpl in Hin.
    destruct (trans_expr_partial pred) eqn:Hpred.
    + apply in_remove_string in Hin as [Hin Hneq].
      simpl.
      apply in_remove_string_intro.
      { exact Hneq. }
      eapply IHpred; eauto.
    + simpl.
      simpl in Hin.
      contradiction.
  - intros t1 IHt1 t2 IHt2 y Hin.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHt1.
      exact Hin.
    + right.
      apply IHt2.
      exact Hin.
  - intros x t1 IHt1 t2 IHt2 y Hin.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + simpl.
      apply in_or_app.
      left.
      apply IHt1.
      exact Hin.
    + apply in_remove_string in Hin as [Hin Hneq].
      simpl.
      apply in_or_app.
      right.
      apply in_remove_string_intro.
      { exact Hneq. }
      apply IHt2.
      exact Hin.
  - intros t1 IHt1 t2 IHt2 y Hin.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin];
      simpl; apply in_or_app.
    + left.
      apply IHt1.
      exact Hin.
    + right.
      apply IHt2.
      exact Hin.
  - intros t0 IHt0 y Hin.
    simpl in *.
    apply IHt0.
    exact Hin.
  - intros t0 IHt0 y Hin.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + apply IHt0.
      exact Hin.
    + rewrite app_nil_r in Hin.
      apply IHt0.
      exact Hin.
Qed.

Lemma free_exp_vars_trans_expr_partial_subset :
  forall e e' y,
    trans_expr_partial e = Some e' ->
    List.In y (free_exp_vars e') ->
    List.In y (free_exp_vars_surf e).
Proof.
  intros e e' y Htrans Hin.
  exact (proj1 free_var_translation_subsets e e' y Htrans Hin).
Qed.

Lemma free_ty_vars_trans_type_subset :
  forall t y,
    List.In y (free_ty_vars (trans_type t)) ->
    List.In y (free_ty_vars_surf t).
Proof.
  intros t y Hin.
  exact (proj2 free_var_translation_subsets t y Hin).
Qed.

(* Paper Lemma 12. *)
Lemma trans_type_preserves_validity :
  forall (Gamma : ctx_surf) (tau : ty),
    ty_valid_surf Gamma tau ->
    ty_valid (trans_ctx_surf Gamma) (trans_type tau).
Proof.
  intros Gamma tau Hvalid.
  induction Hvalid.
  - constructor.
  - simpl.
    eapply VSet with (v := trans_expr_dref_free v).
    match goal with
    | [ Hpure : has_type_pure_surf (ctx_add_var_surf ?G var (TyBase ?tb) v) e (TyBase BBool) |- _ ] =>
        destruct (trans_expr_partial_pure (ctx_add_var_surf G var (TyBase tb) v) e (TyBase BBool) Hpure) as [ep Hpair]
    end.
    destruct Hpair as [Hep Hty].
    rewrite trans_ctx_surf_add_var in Hty.
    replace ep with (trans_expr_dref_free e) in Hty.
    + exact Hty.
    + unfold trans_expr_dref_free.
      rewrite Hep.
      reflexivity.
  - simpl.
    apply VFun; assumption.
  - simpl.
    assert (Hfresh' : ~ List.In var (free_ty_vars (trans_type t1))).
    { intro Hin.
      eapply free_ty_vars_trans_type_subset in Hin.
      match goal with
      | Hfresh0 : ~ List.In var (free_ty_vars_surf t1) |- _ => exact (Hfresh0 Hin)
      end. }
    eapply VFunDep.
    + exact Hfresh'.
    + exact IHHvalid1.
    + match goal with
      | [ Hv : ty_valid (trans_ctx_surf (ctx_add_var_surf ?G var ?t (ExVar var))) _ |- _ ] =>
          rewrite trans_ctx_surf_add_var in Hv;
          simpl in Hv;
          exact Hv
      end.
  - simpl.
    apply VPair; assumption.
  - simpl.
    apply VRef.
    exact IHHvalid.
  - simpl.
    unfold dref_encoding.
    apply VPair.
    + apply VFun.
      * apply VBase.
      * exact IHHvalid.
    + apply VFun.
      * exact IHHvalid.
      * apply VBase.
Qed.

(* Surface subtyping is respected by translation into internal subtyping. *)
Lemma trans_type_preserves_subtype_surf :
  forall (Gamma : ctx_surf) (tau1 tau2 : ty),
    subtype_surf Gamma tau1 tau2 ->
    subtype (trans_ctx_surf Gamma) (trans_type tau1) (trans_type tau2).
Proof.
  fix IH 4.
  intros Gamma tau1 tau2 Hsub.
  destruct Hsub as
    [b
    | var tb e1 e2 c Hvalid1 Hvalid2 Hent
    | var tb e Hvalid
    | var tb e c Hvalid Hent
    | t1 t1' t2 t2' Hsub1 Hsub2
    | var t1 t1' t2 t2' Hfresh Hsub1 Hsub2
    | t1 t1' t2 t2' Hsub1 Hsub2
    | t t' Hsub1 Hsub2
    | t t' Hsub1 Hsub2].
  - simpl.
    apply SBase.
  - simpl in *.
    eapply SSet; eauto.
  - simpl in *.
    eapply SSetBase; eauto.
  - simpl in *.
    eapply SBaseSet; eauto.
  - simpl in *.
    eapply SFun.
    + eapply IH. exact Hsub1.
    + eapply IH. exact Hsub2.
  - simpl in *.
    eapply SFunDep.
    + assert (Hfresh' : ~ List.In var (free_ty_vars (trans_type t1'))).
      { intro Hin. apply Hfresh. eapply free_ty_vars_trans_type_subset; eauto. }
      exact Hfresh'.
    + eapply IH. exact Hsub1.
    + pose proof (IH _ _ _ Hsub2) as Hsub2'.
      rewrite trans_ctx_surf_add_var in Hsub2'.
      simpl in Hsub2'.
      exact Hsub2'.
  - simpl in *.
    eapply SPair.
    + eapply IH. exact Hsub1.
    + eapply IH. exact Hsub2.
  - simpl in *.
    eapply SRef.
    + eapply IH. exact Hsub1.
    + eapply IH. exact Hsub2.
  - simpl in *.
    unfold dref_encoding.
    eapply SPair.
    + eapply SFun.
      * apply SBase.
      * eapply IH. exact Hsub1.
    + eapply SFun.
      * eapply IH. exact Hsub2.
      * apply SBase.
Qed.

Lemma insert_twice `{FinMap K M} {A} (m : M A) (i : K) (x y : A) :
  <[i := x]>(<[i := y]> m) = <[i := x]> m.
Proof.
  rewrite insert_insert.
  destruct (decide (i = i)) as [_|Hdec].
  - reflexivity.
  - exfalso. apply Hdec. reflexivity.
Qed.

Lemma add_var_twice :
  forall Γ var ty v ty2 v2,
    ctx_add_var (ctx_add_var Γ var ty v) var ty2 v2 =
    ctx_add_var Γ var ty2 v2.
Proof.
  intros.
  unfold ctx_add_var.
  simpl.
  specialize (insert_twice (Γ ▷vars) var (ty2, v2) (ty, v)).
  intros.
  exact (f_equal (fun x => (x, Γ ▷consts, Γ.2)) H).
Qed.

Lemma existsb_string_eqb_false_notin :
  forall x xs,
    existsb (String.eqb x) xs = false ->
    ~ List.In x xs.
Proof.
  intros x xs Hfalse.
  induction xs.
  - intro Hin. contradiction.
  - simpl in Hfalse.
    destruct (String.eqb x a) eqn:Heq.
    + discriminate.
    + intro Hin.
      simpl in Hin.
      destruct Hin as [Hin | Hin].
      * apply String.eqb_neq in Heq. congruence.
      * apply IHxs; assumption.
Qed.

Lemma existsb_string_eqb_false_of_notin :
  forall x xs,
    ~ List.In x xs ->
    existsb (String.eqb x) xs = false.
Proof.
  intros x xs Hnot.
  induction xs.
  - reflexivity.
  - simpl.
    destruct (String.eqb x a) eqn:Heq.
    + apply String.eqb_eq in Heq.
      subst a.
      exfalso.
      apply Hnot.
      simpl.
      auto.
    + apply IHxs.
      intro Hin.
      apply Hnot.
      simpl.
      auto.
Qed.

Combined Scheme internal_expr_ty_ind from i_expr_ind_mut, i_ty_ind_mut.

Lemma free_vars_subset_all_vars :
  (forall e y,
    List.In y (free_exp_vars e) ->
    List.In y (exp_vars e)) /\
  (forall t y,
    List.In y (free_ty_vars t) ->
    List.In y (ty_vars t)).
Proof.
  apply internal_expr_ty_ind.
  - intros s y Hin. contradiction.
  - intros b y Hin. contradiction.
  - intros n y Hin. contradiction.
  - intros u y Hin. contradiction.
  - intros c y Hin. contradiction.
  - intros v y Hin. simpl in *. exact Hin.
  - intros l y Hin. contradiction.
  - intros f x t1 IHt1 t2 IHt2 body IHbody y Hin.
    simpl in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + simpl. right. right. apply in_or_app. left. apply IHt1. exact Hin.
    + apply in_remove_string in Hin as [Hin _].
      apply in_app_or in Hin as [Hin | Hin].
      * simpl. right. right. apply in_or_app. right. apply in_or_app. left. apply IHt2. exact Hin.
      * simpl. right. right. apply in_or_app. right. apply in_or_app. right. apply IHbody. exact Hin.
  - intros e1 IHe1 e2 IHe2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHe1. exact Hin.
    + simpl. apply in_or_app. right. apply IHe2. exact Hin.
  - intros e1 IHe1 e2 IHe2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHe1. exact Hin.
    + simpl. apply in_or_app. right. apply IHe2. exact Hin.
  - intros e1 IHe1 e2 IHe2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHe1. exact Hin.
    + simpl. apply in_or_app. right. apply IHe2. exact Hin.
  - intros e0 IHe0 y Hin. simpl in *. apply IHe0. exact Hin.
  - intros e0 IHe0 y Hin. simpl in *. apply IHe0. exact Hin.
  - intros e1 IHe1 e2 IHe2 e3 IHe3 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHe1. exact Hin.
    + apply in_app_or in Hin as [Hin | Hin].
      * simpl. apply in_or_app. right. apply in_or_app. left. apply IHe2. exact Hin.
      * simpl. apply in_or_app. right. apply in_or_app. right. apply IHe3. exact Hin.
  - intros e0 IHe0 y Hin. simpl in *. apply IHe0. exact Hin.
  - intros e1 IHe1 e2 IHe2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHe1. exact Hin.
    + simpl. apply in_or_app. right. apply IHe2. exact Hin.
  - intros e1 IHe1 e2 IHe2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHe1. exact Hin.
    + simpl. apply in_or_app. right. apply IHe2. exact Hin.
  - intros e1 IHe1 e2 IHe2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHe1. exact Hin.
    + simpl. apply in_or_app. right. apply IHe2. exact Hin.
  - intros e1 IHe1 e2 IHe2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHe1. exact Hin.
    + simpl. apply in_or_app. right. apply IHe2. exact Hin.
  - intros t IHt e0 IHe0 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHt. exact Hin.
    + simpl. apply in_or_app. right. apply IHe0. exact Hin.
  - intros e0 IHe0 y Hin. simpl in *. apply IHe0. exact Hin.
  - intros e1 IHe1 e2 IHe2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHe1. exact Hin.
    + simpl. apply in_or_app. right. apply IHe2. exact Hin.
  - contradiction.
  - intros b y Hin. contradiction.
  - intros x b pred IHpred y Hin.
    apply in_remove_string in Hin as [Hin _].
    simpl. right. apply IHpred. exact Hin.
  - intros t1 IHt1 t2 IHt2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHt1. exact Hin.
    + simpl. apply in_or_app. right. apply IHt2. exact Hin.
  - intros x t1 IHt1 t2 IHt2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. right. apply in_or_app. left. apply IHt1. exact Hin.
    + apply in_remove_string in Hin as [Hin _].
      simpl. right. apply in_or_app. right. apply IHt2. exact Hin.
  - intros t1 IHt1 t2 IHt2 y Hin.
    simpl in Hin. apply in_app_or in Hin as [Hin | Hin].
    + simpl. apply in_or_app. left. apply IHt1. exact Hin.
    + simpl. apply in_or_app. right. apply IHt2. exact Hin.
  - intros t0 IHt0 y Hin. simpl in *. apply IHt0. exact Hin.
Qed.

Lemma free_exp_vars_subset_exp_vars :
  forall e y,
    List.In y (free_exp_vars e) ->
    List.In y (exp_vars e).
Proof.
  intros e y Hin.
  exact (proj1 free_vars_subset_all_vars e y Hin).
Qed.

Lemma free_ty_vars_subset_ty_vars :
  forall t y,
    List.In y (free_ty_vars t) ->
    List.In y (ty_vars t).
Proof.
  intros t y Hin.
  exact (proj2 free_vars_subset_all_vars t y Hin).
Qed.

Lemma erase_dep_var_id_if_fresh_ty_var :
  forall x tau,
    ~ List.In x (ty_vars tau) ->
    erase_dep_var x tau = tau.
Proof.
  intros x tau.
  induction tau; intros Hfresh; simpl in *.
  - reflexivity.
  - assert (Hneq : x <> s).
    { intro Heq. apply Hfresh. subst s. simpl. auto. }
    assert (Hnot_exp : ~ List.In x (exp_vars i)).
    { intro Hin. apply Hfresh. simpl. auto. }
    assert (Hnot_free : ~ List.In x (free_exp_vars i)).
    { intro Hin. apply Hnot_exp. eapply free_exp_vars_subset_exp_vars. exact Hin. }
    destruct (String.eqb x s) eqn:Heq.
    + apply String.eqb_eq in Heq. contradiction.
    + rewrite existsb_string_eqb_false_of_notin by exact Hnot_free.
      reflexivity.
  - assert (Hfresh1 : ~ List.In x (ty_vars tau1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars tau2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHtau1 Hfresh1), (IHtau2 Hfresh2). reflexivity.
  - assert (Hneq : x <> s).
    { intro Heq. apply Hfresh. subst s. simpl. auto. }
    assert (Hfresh1 : ~ List.In x (ty_vars tau1)).
    { intro Hin. apply Hfresh. simpl. right. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars tau2)).
    { intro Hin. apply Hfresh. simpl. right. apply in_or_app. right. exact Hin. }
    destruct (String.eqb x s) eqn:Heq.
    + apply String.eqb_eq in Heq. contradiction.
    + rewrite (IHtau1 Hfresh1), (IHtau2 Hfresh2). reflexivity.
  - assert (Hfresh1 : ~ List.In x (ty_vars tau1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars tau2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHtau1 Hfresh1), (IHtau2 Hfresh2). reflexivity.
  - assert (Hnot_free : ~ List.In x (free_ty_vars tau)).
    { intro Hin. apply Hfresh. eapply free_ty_vars_subset_ty_vars. exact Hin. }
    rewrite existsb_string_eqb_false_of_notin by exact Hnot_free.
    rewrite (IHtau Hfresh). reflexivity.
Qed.

Lemma simple_type_no_ty_vars :
  forall tau,
    is_simple_type tau = true ->
    ty_vars tau = [].
Proof.
  induction tau; simpl; intros Hsimple; try discriminate; try reflexivity.
  - apply andb_true_iff in Hsimple as [Hsimple1 Hsimple2].
    rewrite (IHtau1 Hsimple1), (IHtau2 Hsimple2).
    reflexivity.
  - apply andb_true_iff in Hsimple as [Hsimple1 Hsimple2].
    rewrite (IHtau1 Hsimple1), (IHtau2 Hsimple2).
    reflexivity.
  - rewrite (IHtau Hsimple).
    reflexivity.
Qed.

Lemma erase_dep_var_simple_id :
  forall x tau,
    is_simple_type tau = true ->
    erase_dep_var x tau = tau.
Proof.
  intros x tau Hsimple.
  induction tau; simpl in *; try discriminate; try reflexivity.
  - apply andb_true_iff in Hsimple as [Hsimple1 Hsimple2].
    rewrite (IHtau1 Hsimple1), (IHtau2 Hsimple2).
    reflexivity.
  - apply andb_true_iff in Hsimple as [Hsimple1 Hsimple2].
    rewrite (IHtau1 Hsimple1), (IHtau2 Hsimple2).
    reflexivity.
  - assert (Hnot_free : ~ List.In x (free_ty_vars tau)).
    { intro Hin.
      pose proof (free_ty_vars_subset_ty_vars tau x Hin) as Hall.
      rewrite (simple_type_no_ty_vars tau Hsimple) in Hall.
      exact Hall. }
    rewrite existsb_string_eqb_false_of_notin by exact Hnot_free.
    rewrite (IHtau Hsimple).
    reflexivity.
Qed.

Lemma erase_dep_var_preserves_validity_simple :
  forall (Gamma : ctx_surf) (x : string) (tau : i_ty),
    is_simple_type tau = true ->
    ty_valid (ctx_add_var (trans_ctx_surf Gamma) x (TBase BBool) (EVar x)) tau ->
    ty_valid (trans_ctx_surf Gamma) (erase_dep_var x tau).
Proof.
  intros Gamma x tau Hsimple Hvalid.
  rewrite erase_dep_var_simple_id by exact Hsimple.
  eapply ty_valid_drop_fresh_var.
  - rewrite (simple_type_no_ty_vars tau Hsimple).
    simpl.
    tauto.
  - exact Hvalid.
Qed.

Lemma erase_dep_var_preserves_validity_fresh_ty_var :
  forall (Gamma : ctx_surf) (x : string) (tau : i_ty),
    ~ List.In x (ty_vars tau) ->
    ty_valid (ctx_add_var (trans_ctx_surf Gamma) x (TBase BBool) (EVar x)) tau ->
    ty_valid (trans_ctx_surf Gamma) (erase_dep_var x tau).
Proof.
  intros Gamma x tau Hfresh Hvalid.
  rewrite erase_dep_var_id_if_fresh_ty_var by exact Hfresh.
  eapply ty_valid_drop_fresh_var.
  - exact Hfresh.
  - exact Hvalid.
Qed.

Lemma has_type_pure_drop_unused_var :
  forall C x t w e ty,
    ~ List.In x (free_exp_vars e) ->
    has_type_pure (ctx_add_var C x t w) e ty ->
    has_type_pure C e ty.
Proof.
  intros C x t w e ty Hfresh Hpure.
  induction Hpure; simpl in Hfresh.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + exfalso. apply Hfresh. simpl. auto.
    + eapply PVar.
      * unfold var_ctx_lookup, ctx_add_var in H. simpl in H.
        apply lookup_insert_Some in H.
        destruct H as [Hcase | Hcase].
        { destruct Hcase as [Heq Hentry]. congruence. }
        destruct Hcase as [_ Hbase].
        exact Hbase.
      * exact H0.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst; eauto.
  - match goal with
    | Hty1 : has_type_pure _ ?e_left _,
      Hty2 : has_type_pure _ ?e_right _ |- _ =>
        assert (Hfresh1 : ~ List.In x (free_exp_vars e_left));
        [ intro Hin; apply Hfresh; apply in_or_app; left; exact Hin
        | assert (Hfresh2 : ~ List.In x (free_exp_vars e_right));
          [ intro Hin; apply Hfresh; apply in_or_app; right; exact Hin
          | eapply PApp; eauto ] ]
    end.
  - apply PNot. eauto.
  - match goal with
    | Hty1 : has_type_pure _ ?e_left _,
      Hty2 : has_type_pure _ ?e_right _ |- _ =>
        assert (Hfresh1 : ~ List.In x (free_exp_vars e_left));
        [ intro Hin; apply Hfresh; apply in_or_app; left; exact Hin
        | assert (Hfresh2 : ~ List.In x (free_exp_vars e_right));
          [ intro Hin; apply Hfresh; apply in_or_app; right; exact Hin
          | apply PImp; auto ] ]
    end.
  - match goal with
    | Hty1 : has_type_pure _ ?e_left _,
      Hty2 : has_type_pure _ ?e_right _ |- _ =>
        assert (Hfresh1 : ~ List.In x (free_exp_vars e_left));
        [ intro Hin; apply Hfresh; apply in_or_app; left; exact Hin
        | assert (Hfresh2 : ~ List.In x (free_exp_vars e_right));
          [ intro Hin; apply Hfresh; apply in_or_app; right; exact Hin
          | apply PAnd; auto ] ]
    end.
  - match goal with
    | Hty1 : has_type_pure _ ?e_left _,
      Hty2 : has_type_pure _ ?e_right _ |- _ =>
        assert (Hfresh1 : ~ List.In x (free_exp_vars e_left));
        [ intro Hin; apply Hfresh; apply in_or_app; left; exact Hin
        | assert (Hfresh2 : ~ List.In x (free_exp_vars e_right));
          [ intro Hin; apply Hfresh; apply in_or_app; right; exact Hin
          | apply POr; auto ] ]
    end.
  - match goal with
    | Hty1 : has_type_pure _ ?e_left _,
      Hty2 : has_type_pure _ ?e_right _ |- _ =>
        assert (Hfresh1 : ~ List.In x (free_exp_vars e_left));
        [ intro Hin; apply Hfresh; apply in_or_app; left; exact Hin
        | assert (Hfresh2 : ~ List.In x (free_exp_vars e_right));
          [ intro Hin; apply Hfresh; apply in_or_app; right; exact Hin
          | eapply PEq; eauto ] ]
    end.
  - match goal with
    | Hty1 : has_type_pure _ ?e_left _,
      Hty2 : has_type_pure _ ?e_right _ |- _ =>
        assert (Hfresh1 : ~ List.In x (free_exp_vars e_left));
        [ intro Hin; apply Hfresh; apply in_or_app; left; exact Hin
        | assert (Hfresh2 : ~ List.In x (free_exp_vars e_right));
          [ intro Hin; apply Hfresh; apply in_or_app; right; exact Hin
          | apply PPlus; auto ] ]
    end.
Qed.

Lemma not_in_remove_string_of_not_in :
  forall x y xs,
    ~ List.In x xs ->
    ~ List.In x (remove_string y xs).
Proof.
  intros x y xs Hnot Hin.
  apply Hnot.
  apply in_remove_string in Hin as [Hin _].
  exact Hin.
Qed.

Lemma not_in_remove_string_inv_neq :
  forall x y xs,
    x <> y ->
    ~ List.In x (remove_string y xs) ->
    ~ List.In x xs.
Proof.
  intros x y xs Hneq Hnot Hin.
  apply Hnot.
  apply in_remove_string_intro; assumption.
Qed.

Lemma erase_dep_var_not_in_free_ty_vars_self :
  forall x tau,
    ~ List.In x (free_ty_vars (erase_dep_var x tau)).
Proof.
  intros x tau.
  induction tau; simpl.
  - intro Hin. exact Hin.
  - destruct (String.eqb_spec x s) as [Heq | Hneq].
    + subst s. intro Hin.
      apply in_remove_string in Hin as [_ Hneqself].
      contradiction.
    + destruct (existsb (String.eqb x) (free_exp_vars i)) eqn:Hex.
      * intro Hin. exact Hin.
      * intro Hin.
        apply existsb_string_eqb_false_notin in Hex.
        apply in_remove_string in Hin as [Hin _].
        exact (Hex Hin).
  - intros Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + exact (IHtau1 Hin).
    + exact (IHtau2 Hin).
  - destruct (String.eqb_spec x s) as [Heq | Hneq].
    + subst s. intro Hin.
      apply in_app_or in Hin as [Hin | Hin].
      * exact (IHtau1 Hin).
      * apply in_remove_string in Hin as [_ Hneqself].
        contradiction.
    + intro Hin.
      apply in_app_or in Hin as [Hin | Hin].
      * exact (IHtau1 Hin).
      * apply in_remove_string in Hin as [Hin _].
        exact (IHtau2 Hin).
  - intros Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + exact (IHtau1 Hin).
    + exact (IHtau2 Hin).
  - destruct (existsb (String.eqb x) (free_ty_vars tau)) eqn:Hex.
    + intro Hin.
      unfold dref_encoding in Hin.
      simpl in Hin.
      apply in_app_or in Hin as [Hin | Hin].
      * exact (IHtau Hin).
      * apply in_app_or in Hin as [Hin | Hin].
        -- exact (IHtau Hin).
        -- exact Hin.
    + intro Hin.
      exact (IHtau Hin).
Qed.

Lemma free_ty_vars_erase_dep_var_subset :
  forall x tau y,
    List.In y (free_ty_vars (erase_dep_var x tau)) ->
    List.In y (free_ty_vars tau).
Proof.
  intros x tau.
  induction tau; simpl; intros y Hin.
  - exact Hin.
  - destruct (String.eqb_spec x s) as [Heqxs | Hneqxs].
    + exact Hin.
    + destruct (existsb (String.eqb x) (free_exp_vars i)) eqn:Hex.
      * exfalso. exact Hin.
      * exact Hin.
  - apply in_app_or in Hin as [Hin | Hin].
    + apply in_or_app. left. exact (IHtau1 _ Hin).
    + apply in_or_app. right. exact (IHtau2 _ Hin).
  - destruct (String.eqb_spec x s) as [Heqxs | Hneqxs].
    + subst s.
      apply in_app_or in Hin as [Hin | Hin].
      * apply in_or_app. left. exact (IHtau1 _ Hin).
      * apply in_or_app. right. exact Hin.
    + apply in_app_or in Hin as [Hin | Hin].
      * apply in_or_app. left. exact (IHtau1 _ Hin).
      * apply in_or_app. right.
        apply in_remove_string in Hin as [Hin Hneqys].
        eapply in_remove_string_intro.
        -- exact Hneqys.
        -- exact (IHtau2 _ Hin).
  - apply in_app_or in Hin as [Hin | Hin].
    + apply in_or_app. left. exact (IHtau1 _ Hin).
    + apply in_or_app. right. exact (IHtau2 _ Hin).
  - destruct (existsb (String.eqb x) (free_ty_vars tau)) eqn:Hex.
    + unfold dref_encoding in Hin. simpl in Hin.
      apply in_app_or in Hin as [Hin | Hin].
      * apply IHtau. exact Hin.
      * apply in_app_or in Hin as [Hin | Hin].
        -- apply IHtau. exact Hin.
        -- exfalso. exact Hin.
    + exact (IHtau _ Hin).
Qed.

Lemma erase_dep_var_preserves_not_in_free_ty_vars :
  forall x y tau,
    ~ List.In y (free_ty_vars tau) ->
    ~ List.In y (free_ty_vars (erase_dep_var x tau)).
Proof.
  intros x y tau Hnot Hin.
  apply Hnot.
  eapply free_ty_vars_erase_dep_var_subset.
  exact Hin.
Qed.

Lemma erase_dep_var_id_if_fresh_free_ty_var :
  forall x tau,
    ~ List.In x (free_ty_vars tau) ->
    erase_dep_var x tau = tau.
Proof.
  intros x tau.
  induction tau; intros Hfresh; simpl in *.
  - reflexivity.
  - destruct (String.eqb x s) eqn:Heq.
    + reflexivity.
    + apply String.eqb_neq in Heq.
      assert (Hnot_free : ~ List.In x (free_exp_vars i)).
      { intro Hin.
        apply Hfresh.
        eapply in_remove_string_intro.
        - exact Heq.
        - exact Hin. }
      rewrite existsb_string_eqb_false_of_notin by exact Hnot_free.
      reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_ty_vars tau1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_ty_vars tau2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHtau1 Hfresh1), (IHtau2 Hfresh2).
    reflexivity.
  - destruct (String.eqb x s) eqn:Heq.
    + assert (Hfresh1 : ~ List.In x (free_ty_vars tau1)).
      { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
      rewrite (IHtau1 Hfresh1).
      reflexivity.
    + apply String.eqb_neq in Heq.
      assert (Hfresh1 : ~ List.In x (free_ty_vars tau1)).
      { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
      assert (Hfresh2 : ~ List.In x (free_ty_vars tau2)).
      { intro Hin.
        apply Hfresh.
        apply in_or_app.
        right.
        eapply in_remove_string_intro.
        - exact Heq.
        - exact Hin. }
      rewrite (IHtau1 Hfresh1), (IHtau2 Hfresh2).
      reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_ty_vars tau1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_ty_vars tau2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHtau1 Hfresh1), (IHtau2 Hfresh2).
    reflexivity.
  - assert (Hfresh0 : ~ List.In x (free_ty_vars tau)).
    { exact Hfresh. }
    rewrite existsb_string_eqb_false_of_notin by exact Hfresh0.
    rewrite (IHtau Hfresh0).
    reflexivity.
Qed.

Lemma ctx_add_var_erase_dep_var_id_if_fresh_free_ty_var :
  forall C x t w,
    ~ List.In x (free_ty_vars t) ->
    ctx_add_var C x (erase_dep_var x t) w = ctx_add_var C x t w.
Proof.
  intros C x t w Hfresh.
  rewrite erase_dep_var_id_if_fresh_free_ty_var by exact Hfresh.
  reflexivity.
Qed.

Lemma ty_valid_ctx_add_var_erase_dep_var_id_if_fresh_free_ty_var :
  forall C x t w tau,
    ~ List.In x (free_ty_vars t) ->
    ty_valid (ctx_add_var C x t w) tau ->
    ty_valid (ctx_add_var C x (erase_dep_var x t) w) tau.
Proof.
  intros C x t w tau Hfresh Hvalid.
  rewrite ctx_add_var_erase_dep_var_id_if_fresh_free_ty_var by exact Hfresh.
  exact Hvalid.
Qed.

Lemma ty_valid_drop_unused_var_free :
  forall C x t w tau,
    ~ List.In x (free_ty_vars tau) ->
    ty_valid (ctx_add_var C x t w) tau ->
    ty_valid C tau.
Proof.
  fix IH 7.
  intros C x t w tau Hfresh Hvalid.
  destruct Hvalid as
    [tb
    | var tb e v Hp
    | t1 t2 Hv1 Hv2
    | var t1 t2 Hfresh_dep Hv1 Hv2
    | tp1 tp2 Hv1 Hv2
    | tref Hv].
  - apply VBase.
  - simpl in Hfresh.
    destruct (String.eq_dec x var) as [Heq | Hneq].
    + subst var.
      eapply VSet.
      rewrite ctx_add_var_shadow in Hp.
      exact Hp.
    + assert (Hfresh_e : ~ List.In x (free_exp_vars e)).
      { intro Hin.
        apply Hfresh.
        eapply in_remove_string_intro.
        - exact Hneq.
        - exact Hin. }
      eapply VSet.
      rewrite ctx_add_var_swap in Hp by congruence.
      exact (has_type_pure_drop_unused_var (ctx_add_var C var (TBase tb) v) x t w e (TBase BBool) Hfresh_e Hp).
  - simpl in Hfresh.
    assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply VFun.
    + exact (IH C x t w _ Hfresh1 Hv1).
    + exact (IH C x t w _ Hfresh2 Hv2).
  - simpl in Hfresh.
    destruct (String.eq_dec x var) as [Heq | Hneq].
    + subst var.
      assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
      { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
      eapply VFunDep.
      * exact Hfresh_dep.
      * exact (IH C x t w _ Hfresh1 Hv1).
      * rewrite ctx_add_var_shadow in Hv2.
        exact Hv2.
    + assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
      { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
      assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
      { intro Hin.
        apply Hfresh.
        apply in_or_app.
        right.
        eapply in_remove_string_intro.
        - exact Hneq.
        - exact Hin. }
      eapply VFunDep.
      * exact Hfresh_dep.
      * exact (IH C x t w _ Hfresh1 Hv1).
      * rewrite ctx_add_var_swap in Hv2 by congruence.
        exact (IH (ctx_add_var C var t1 (EVar var)) x t w _ Hfresh2 Hv2).
  - simpl in Hfresh.
    assert (Hfresh1 : ~ List.In x (free_ty_vars tp1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_ty_vars tp2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply VPair.
    + exact (IH C x t w _ Hfresh1 Hv1).
    + exact (IH C x t w _ Hfresh2 Hv2).
  - simpl in Hfresh.
    apply VRef.
    exact (IH C x t w _ Hfresh Hv).
Qed.

Lemma erase_dep_var_preserves_validity_same_binder :
  forall C x t1 t2,
    ty_valid (ctx_add_var C x (TBase BBool) (EVar x)) (TArrDep x t1 t2) ->
    ty_valid C (erase_dep_var x (TArrDep x t1 t2)).
Proof.
  intros C x t1 t2 Hvalid.
  inversion Hvalid; subst.
  simpl.
  rewrite String.eqb_refl.
  rewrite erase_dep_var_id_if_fresh_free_ty_var by exact H2.
  eapply VFunDep.
  - exact H2.
  - exact (ty_valid_drop_unused_var_free C x (TBase BBool) (EVar x) t1 H2 H3).
  - rewrite ctx_add_var_shadow in H4.
    exact H4.
Qed.

Lemma erase_dep_var_preserves_validity_fresh_free_ty_var :
  forall C x tau,
    ~ List.In x (free_ty_vars tau) ->
    ty_valid (ctx_add_var C x (TBase BBool) (EVar x)) tau ->
    ty_valid C (erase_dep_var x tau).
Proof.
  intros C x tau Hfresh Hvalid.
  rewrite erase_dep_var_id_if_fresh_free_ty_var by exact Hfresh.
  exact (ty_valid_drop_unused_var_free C x (TBase BBool) (EVar x) tau Hfresh Hvalid).
Qed.

Lemma erase_dep_var_preserves_beta :
  forall x tau,
    essential_type_is_base_type (erase_dep_var x tau) =
    essential_type_is_base_type tau.
Proof.
  intros x tau.
  destruct tau; simpl; try reflexivity.
  all: repeat match goal with
       | |- context[String.eqb ?a ?b] => destruct (String.eqb a b); simpl
       | |- context[existsb (String.eqb ?a) (free_exp_vars ?e)] =>
           destruct (existsb (String.eqb a) (free_exp_vars e)); simpl
       | |- context[existsb (String.eqb ?a) (free_ty_vars ?t)] =>
           destruct (existsb (String.eqb a) (free_ty_vars t)); simpl
       end; reflexivity.
Qed.

Lemma erase_dep_var_preserves_essential_type_if_beta :
  forall x tau,
    essential_type_is_base_type tau = true ->
    essential_type (erase_dep_var x tau) = essential_type tau.
Proof.
  intros x tau Hbeta.
  destruct tau; simpl in *; try discriminate; try reflexivity.
  destruct (String.eqb x s); simpl; try reflexivity.
  destruct (existsb (String.eqb x) (free_exp_vars i)); reflexivity.
Qed.

Lemma has_type_pure_change_var_annotation_erase_dep_var :
  forall C y t w x e tau,
    has_type_pure (ctx_add_var C y t w) e tau ->
    has_type_pure (ctx_add_var C y (erase_dep_var x t) w) e tau.
Proof.
  intros C y t w x e tau Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 y) as [Heq | Hneq].
    + subst x0.
      rewrite (lookup_lemma_var_ctx_add_var_shadow C y t w) in H.
      inversion H; subst.
      rewrite <- (erase_dep_var_preserves_essential_type_if_beta x τb (bool_prop_eq_true _ H0)).
      eapply PVar.
      * exact (lookup_lemma_var_ctx_add_var_shadow C y (erase_dep_var x τb) e).
      * rewrite (erase_dep_var_preserves_beta x τb).
        exact H0.
    + eapply PVar.
      * eapply lookup_lemma_var_change_type; eauto.
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

Lemma ty_valid_change_var_annotation_erase_dep_var :
  forall C y t w x tau,
    ty_valid (ctx_add_var C y t w) tau ->
    ty_valid (ctx_add_var C y (erase_dep_var x t) w) tau.
Proof.
  fix IH 7.
  intros C y t w x tau Hvalid.
  destruct Hvalid as
    [tb
    | var tb e v Hp
    | t1 t2 Hv1 Hv2
    | var t1 t2 Hfresh Hv1 Hv2
    | tp1 tp2 Hv1 Hv2
    | tref Hv].
  - apply VBase.
  - destruct (String.eq_dec var y) as [Heq | Hneq].
    + subst var.
      eapply VSet.
      rewrite ctx_add_var_shadow in Hp.
      rewrite ctx_add_var_shadow.
      exact Hp.
    + eapply VSet.
      rewrite ctx_add_var_swap by congruence.
      rewrite ctx_add_var_swap in Hp by congruence.
      exact (has_type_pure_change_var_annotation_erase_dep_var
        (ctx_add_var C var (TBase tb) v) y t w x e (TBase BBool) Hp).
  - eapply VFun.
    + exact (IH C y t w x _ Hv1).
    + exact (IH C y t w x _ Hv2).
  - eapply VFunDep.
    + exact Hfresh.
    + exact (IH C y t w x _ Hv1).
    + destruct (String.eq_dec var y) as [Heq | Hneq].
      * subst var.
        rewrite ctx_add_var_shadow in Hv2.
        rewrite ctx_add_var_shadow.
        exact Hv2.
      * rewrite ctx_add_var_swap by congruence.
        rewrite ctx_add_var_swap in Hv2 by congruence.
        exact (IH (ctx_add_var C var t1 (EVar var)) y t w x _ Hv2).
  - eapply VPair.
    + exact (IH C y t w x _ Hv1).
    + exact (IH C y t w x _ Hv2).
  - eapply VRef.
    exact (IH C y t w x _ Hv).
Qed.

Lemma erase_dep_var_preserves_validity_ctx :
  forall C x tau,
    ty_valid (ctx_add_var C x (TBase BBool) (EVar x)) tau ->
    ty_valid C (erase_dep_var x tau).
Proof.
  fix IH 4.
  intros C x tau Hvalid.
  destruct Hvalid as
    [tb
    | var tb e v Hp
    | t1 t2 Hv1 Hv2
    | var t1 t2 Hfresh Hv1 Hv2
    | tp1 tp2 Hv1 Hv2
    | tref Hv].
  - simpl. apply VBase.
  - simpl in *.
    destruct (String.eq_dec x var) as [Heq | Hneq].
    + subst var.
      rewrite String.eqb_refl.
      eapply VSet.
      rewrite ctx_add_var_shadow in Hp.
      exact Hp.
    + destruct (String.eqb x var) eqn:Heqxb.
      { apply String.eqb_eq in Heqxb. contradiction. }
      destruct (existsb (String.eqb x) (free_exp_vars e)) eqn:Hex.
      * apply VBase.
      * eapply VSet.
        rewrite ctx_add_var_swap in Hp by congruence.
        apply existsb_string_eqb_false_notin in Hex.
        exact (has_type_pure_drop_unused_var
          (ctx_add_var C var (TBase tb) v) x (TBase BBool) (EVar x) e (TBase BBool) Hex Hp).
  - simpl.
    apply VFun.
    + exact (IH C x t1 Hv1).
    + exact (IH C x t2 Hv2).
  - destruct (String.eq_dec x var) as [Heq | Hneq].
    + subst var.
      simpl.
      rewrite String.eqb_refl.
      rewrite erase_dep_var_id_if_fresh_free_ty_var by exact Hfresh.
      eapply VFunDep.
      * exact Hfresh.
      * exact (ty_valid_drop_unused_var_free C x (TBase BBool) (EVar x) t1 Hfresh Hv1).
      * rewrite ctx_add_var_shadow in Hv2.
        exact Hv2.
    + simpl.
      destruct (String.eqb x var) eqn:Heqxb.
      { apply String.eqb_eq in Heqxb. contradiction. }
      eapply VFunDep.
      * intro Hin.
        apply Hfresh.
        eapply free_ty_vars_erase_dep_var_subset.
        exact Hin.
      * exact (IH C x t1 Hv1).
      * rewrite ctx_add_var_swap in Hv2 by congruence.
        pose proof (IH (ctx_add_var C var t1 (EVar var)) x t2 Hv2) as Hbody.
        exact (ty_valid_change_var_annotation_erase_dep_var C var t1 (EVar var) x (erase_dep_var x t2) Hbody).
  - simpl.
    apply VPair.
    + exact (IH C x tp1 Hv1).
    + exact (IH C x tp2 Hv2).
  - simpl.
    destruct (existsb (String.eqb x) (free_ty_vars tref)) eqn:Hex.
    + unfold dref_encoding.
      apply VPair.
      * apply VFun.
        -- apply VBase.
        -- exact (IH C x tref Hv).
      * apply VFun.
        -- exact (IH C x tref Hv).
        -- apply VBase.
    + apply VRef.
      exact (IH C x tref Hv).
Qed.
(* Paper Lemma 13. *)
Lemma erase_dep_var_preserves_validity :
  forall (Gamma : ctx_surf) (x : string) (tau : i_ty),
    ty_valid (ctx_add_var (trans_ctx_surf Gamma) x (TBase BBool) (EVar x)) tau ->
    ty_valid (trans_ctx_surf Gamma) (erase_dep_var x tau).
Proof.
  intros Gamma x tau Hvalid.
  exact (erase_dep_var_preserves_validity_ctx (trans_ctx_surf Gamma) x tau Hvalid).
Qed.

Lemma subtype_type_match_helper :
  forall Gamma tau1 tau2,
    subtype Gamma tau1 tau2 ->
    [|tau1|] = [|tau2|].
Proof.
  intros.
  induction H.
  - reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHsubtype1, IHsubtype2. reflexivity.
  - simpl. rewrite IHsubtype1, IHsubtype2. reflexivity.
  - simpl. rewrite IHsubtype1, IHsubtype2. reflexivity.
  - simpl. rewrite IHsubtype1. reflexivity.
Qed.

(* Paper Theorem 6. *)
Theorem soundness_of_type_coercion :
  forall (w : mode) (Gamma : ctx_surf) (e : i_expr) (tau : i_ty) (e' : i_expr) (tau' : i_ty),
    coerce w (trans_ctx_surf Gamma) e tau e' tau' ->
    has_type (trans_ctx_surf Gamma) e tau ->
    has_type (trans_ctx_surf Gamma) e' tau'.
Admitted.

(* Paper Theorems 2 and 7. *)
Theorem soundness_of_translation :
  forall (w : mode) (Gamma : ctx_surf) (e : expr) (e' : i_expr) (tau : i_ty),
    has_type_surf w Gamma e e' tau ->
    has_type (trans_ctx_surf Gamma) e' tau.
Admitted.

Lemma soundness_of_reference_coercion :
  forall (w : mode) (Gamma : ctx_surf) (e : i_expr) (tau : i_ty) (e' : i_expr) (tau' : i_ty),
    coerce w (trans_ctx_surf Gamma) e (TRef tau) e' (TRef tau') ->
    has_type (trans_ctx_surf Gamma) e (TRef tau) ->
    has_type (trans_ctx_surf Gamma) e' (TRef tau').
Proof.
  intros w Gamma e tau e' tau' Hco Hty.
  exact (soundness_of_type_coercion w Gamma e (TRef tau) e' (TRef tau') Hco Hty).
Qed.

Lemma soundness_of_ref_to_dref_coercion :
  forall (Gamma : ctx_surf) (e : i_expr) (tau1 tau2 : ty) (e1 : i_expr),
    co_ref (TyRef tau1) = true ->
    contra_ref (TyDeRef tau2) = true ->
    coerce sim (trans_ctx_surf Gamma) e (TRef (trans_type tau1)) e1 (trans_type (TyDeRef tau2)) ->
    has_type (trans_ctx_surf Gamma) e (TRef (trans_type tau1)) ->
    has_type (trans_ctx_surf Gamma) e1 (trans_type (TyDeRef tau2)).
Proof.
  intros Gamma e tau1 tau2 e1 _ _ Hco Hty.
  exact (soundness_of_type_coercion sim Gamma e (TRef (trans_type tau1)) e1 (trans_type (TyDeRef tau2)) Hco Hty).
Qed.

Lemma soundness_of_dref_coercion :
  forall (Gamma : ctx_surf) (e : i_expr) (tau1 tau2 : ty) (e1 : i_expr),
    co_ref (TyDeRef tau1) = true ->
    contra_ref (TyDeRef tau2) = true ->
    coerce sim (trans_ctx_surf Gamma) e (trans_type (TyDeRef tau1)) e1 (trans_type (TyDeRef tau2)) ->
    has_type (trans_ctx_surf Gamma) e (trans_type (TyDeRef tau1)) ->
    has_type (trans_ctx_surf Gamma) e1 (trans_type (TyDeRef tau2)).
Proof.
  intros Gamma e tau1 tau2 e1 _ _ Hco Hty.
  exact (soundness_of_type_coercion sim Gamma e (trans_type (TyDeRef tau1)) e1 (trans_type (TyDeRef tau2)) Hco Hty).
Qed.


