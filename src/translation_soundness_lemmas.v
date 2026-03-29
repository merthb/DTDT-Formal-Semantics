Require Import DTDT.syntax.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.semantic_rules_surf.
Require Import DTDT.type_directed_translation.
Require Import DTDT.foundational_lemmas_inter.
Require Import DTDT.type_safety_lemmas_inter.

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
    eapply VFunDep with (v := trans_expr_dref_free v).
    + exact IHHvalid1.
    + match goal with
      | [ Hv : ty_valid (trans_ctx_surf (ctx_add_var_surf ?G var ?t v)) _ |- _ ] =>
          rewrite trans_ctx_surf_add_var in Hv;
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
    | var t1 t1' t2 t2' v Hsub1 Hsub2
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
    eapply SFunDep with (v := trans_expr_dref_free v).
    + eapply IH. exact Hsub1.
    + rewrite <- trans_ctx_surf_add_var.
      eapply IH. exact Hsub2.
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

(* Paper Lemma 13. *)
Lemma erase_dep_var_preserves_validity :
  forall (Gamma : ctx_surf) (x : string) (tau : i_ty),
    ty_valid (ctx_add_var (trans_ctx_surf Gamma) x (TBase BBool) (EVar x)) tau ->
    ty_valid (trans_ctx_surf Gamma) (erase_dep_var x tau).
Proof. Admitted.

(* Paper Theorem 6. *)
Lemma soundness_of_type_coercion :
  forall (w : mode) (Gamma : ctx_surf) (e : i_expr) (tau : i_ty) (e' : i_expr) (tau' : i_ty),
    ty_valid (trans_ctx_surf Gamma) tau ->
    ty_valid (trans_ctx_surf Gamma) tau' ->
    coerce w (trans_ctx_surf Gamma) e tau e' tau' ->
    has_type (trans_ctx_surf Gamma) e (erase_i_ty tau) ->
    has_type (trans_ctx_surf Gamma) e' (erase_i_ty tau').
Proof. Admitted.

(* Paper Theorems 2 and 7. *)
Lemma soundness_of_translation :
  forall (w : mode) (Gamma : ctx_surf) (e : expr) (e' : i_expr) (tau : i_ty),
    has_type_surf w Gamma e e' tau ->
    has_type (trans_ctx_surf Gamma) e' (erase_i_ty tau).
Proof. Admitted.

Lemma soundness_of_reference_coercion :
  forall (w : mode) (Gamma : ctx_surf) (e : i_expr) (tau : i_ty) (e' : i_expr) (tau' : i_ty),
    ty_valid (trans_ctx_surf Gamma) (TRef tau) ->
    ty_valid (trans_ctx_surf Gamma) (TRef tau') ->
    coerce w (trans_ctx_surf Gamma) e (TRef tau) e' (TRef tau') ->
    has_type (trans_ctx_surf Gamma) e (erase_i_ty (TRef tau)) ->
    has_type (trans_ctx_surf Gamma) e' (erase_i_ty (TRef tau')).
Proof.
  intros w Gamma e tau e' tau' Hvalid Hvalid' Hco Hty.
  exact (soundness_of_type_coercion w Gamma e (TRef tau) e' (TRef tau') Hvalid Hvalid' Hco Hty).
Qed.

Lemma soundness_of_ref_to_dref_coercion :
  forall (Gamma : ctx_surf) (e : i_expr) (tau1 tau2 : ty) (e1 : i_expr),
    co_ref (TyRef tau1) = true ->
    contra_ref (TyDeRef tau2) = true ->
    ty_valid (trans_ctx_surf Gamma) (TRef (trans_type tau1)) ->
    ty_valid (trans_ctx_surf Gamma) (trans_type (TyDeRef tau2)) ->
    coerce sim (trans_ctx_surf Gamma) e (TRef (trans_type tau1)) e1 (trans_type (TyDeRef tau2)) ->
    has_type (trans_ctx_surf Gamma) e (erase_i_ty (TRef (trans_type tau1))) ->
    has_type (trans_ctx_surf Gamma) e1 (erase_i_ty (trans_type (TyDeRef tau2))).
Proof.
  intros Gamma e tau1 tau2 e1 _ _ Hvalid Hvalid' Hco Hty.
  exact (soundness_of_type_coercion sim Gamma e (TRef (trans_type tau1)) e1 (trans_type (TyDeRef tau2)) Hvalid Hvalid' Hco Hty).
Qed.

Lemma soundness_of_dref_coercion :
  forall (Gamma : ctx_surf) (e : i_expr) (tau1 tau2 : ty) (e1 : i_expr),
    co_ref (TyDeRef tau1) = true ->
    contra_ref (TyDeRef tau2) = true ->
    ty_valid (trans_ctx_surf Gamma) (trans_type (TyDeRef tau1)) ->
    ty_valid (trans_ctx_surf Gamma) (trans_type (TyDeRef tau2)) ->
    coerce sim (trans_ctx_surf Gamma) e (trans_type (TyDeRef tau1)) e1 (trans_type (TyDeRef tau2)) ->
    has_type (trans_ctx_surf Gamma) e (erase_i_ty (trans_type (TyDeRef tau1))) ->
    has_type (trans_ctx_surf Gamma) e1 (erase_i_ty (trans_type (TyDeRef tau2))).
Proof.
  intros Gamma e tau1 tau2 e1 _ _ Hvalid Hvalid' Hco Hty.
  exact (soundness_of_type_coercion sim Gamma e (trans_type (TyDeRef tau1)) e1 (trans_type (TyDeRef tau2)) Hvalid Hvalid' Hco Hty).
Qed.
