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

Axiom free_exp_vars_trans_expr_partial_subset :
  forall e e' y,
    trans_expr_partial e = Some e' ->
    List.In y (free_exp_vars e') ->
    List.In y (free_exp_vars_surf e).

Axiom free_ty_vars_trans_type_subset :
  forall t y,
    List.In y (free_ty_vars (trans_type t)) ->
    List.In y (free_ty_vars_surf t).

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
    + subst s. simpl.
      intros Hin.
      apply in_app_or in Hin as [Hin | Hin].
      * exact (IHtau1 Hin).
      * exact (IHtau2 Hin).
    + simpl.
      intros Hin.
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
      * destruct (String.eq_dec y x) as [Heqyx | Hneqyx].
        -- subst y. exfalso. exact (erase_dep_var_not_in_free_ty_vars_self x tau2 Hin).
        -- apply in_or_app. right.
           eapply in_remove_string_intro.
           ++ exact Hneqyx.
           ++ exact (IHtau2 _ Hin).
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

(* Paper Lemma 13. *)
Lemma erase_dep_var_preserves_validity :
  forall (Gamma : ctx_surf) (x : string) (tau : i_ty),
    ty_valid (ctx_add_var (trans_ctx_surf Gamma) x (TBase BBool) (EVar x)) tau ->
    ty_valid (trans_ctx_surf Gamma) (erase_dep_var x tau).
Proof. Admitted.

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
    ty_valid (trans_ctx_surf Gamma) tau ->
    ty_valid (trans_ctx_surf Gamma) tau' ->
    coerce w (trans_ctx_surf Gamma) e tau e' tau' ->
    has_type (trans_ctx_surf Gamma) e (erase_i_ty tau) ->
    has_type (trans_ctx_surf Gamma) e' (erase_i_ty tau').
Proof.
  intros.
  induction H1; simpl.
  - pose proof (subtype_type_match_helper _ _ _ H1).
    rewrite <- H3. assumption.
  - destruct H3.
    + rewrite H3 in H, H2. simpl in H2. admit.
    + rewrite H3 in H, H2. simpl in H2. admit.
  - destruct (x =? y)%string.
    + simpl in *. pose proof (subtype_type_match_helper _ _ _ H3).
      rewrite H5. admit.
    +
Admitted.

(* Paper Theorems 2 and 7. *)
Theorem soundness_of_translation :
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
