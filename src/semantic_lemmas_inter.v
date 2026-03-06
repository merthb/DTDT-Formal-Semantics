Require Import DTDT.syntax.
Require Import DTDT.big_step_eval_inter.
Require Import DTDT.semantic_rules_inter.

Definition add_ctx (Γ₁ Γ₂ : ctx) : ctx := ((Γ₂ ▷vars) ∪ (Γ₁ ▷vars), (Γ₂ ▷consts) ∪ (Γ₁ ▷consts)).

(* --- Lemmas ------------------------------------------------------------ *)

Lemma lookup_lemma_const : forall Γ₁ Γ₂ Γ₃ c τ e,
  ((add_ctx Γ₂ Γ₁) !!₂ c) = (Some (τ, e)) ->
  ((add_ctx (add_ctx Γ₃ Γ₂) Γ₁) !!₂ c) = (Some (τ, e)).
Proof.
  intros.
  unfold add_ctx, const_ctx_lookup in *. cbn in *.
  destruct ((snd Γ₁) !! c) eqn:H2.
  - (* c is in Γ2 *)
    apply (lookup_union_Some_l (Γ₁.2) _ c _).
    rewrite <- H.
    rewrite H2 at 1.
    symmetry.
    apply (lookup_union_Some_l (Γ₁.2) _ c _).
    exact H2.
  - (* c not in Γ2 *)
    pose proof (lookup_union_r (Γ₁.2) (Γ₂.2) c H2).
    pose proof (lookup_union_r (Γ₁.2) ((Γ₂.2) ∪ (Γ₃.2)) c H2).
    rewrite H1 at 1.
    rewrite H0 in H at 1.
    apply (lookup_union_Some_l (Γ₂.2) _ c _).
    exact H.
Qed.

Lemma lookup_lemma_var : forall Γ₁ Γ₂ Γ₃ c τ e,
  ((add_ctx Γ₂ Γ₁) !!₁ c) = (Some (τ, e)) ->
  ((add_ctx (add_ctx Γ₃ Γ₂) Γ₁) !!₁ c) = (Some (τ, e)).
Proof.
  intros.
  unfold add_ctx, var_ctx_lookup in *. cbn in *.
  destruct ((fst Γ₁) !! c) eqn:H2.
  - (* c is in Γ2 *)
    apply (lookup_union_Some_l (Γ₁.1) _ c _).
    rewrite <- H.
    rewrite H2 at 1.
    symmetry.
    apply (lookup_union_Some_l (Γ₁.1) _ c _).
    exact H2.
  - (* c not in Γ2 *)
    pose proof (lookup_union_r (Γ₁.1) (Γ₂.1) c H2).
    pose proof (lookup_union_r (Γ₁.1) ((Γ₂.1) ∪ (Γ₃.1)) c H2).
    rewrite H1 at 1.
    rewrite H0 in H at 1.
    apply (lookup_union_Some_l (Γ₂.1) _ c _).
    exact H.
Qed.

Lemma lookup_lemma_var_add : forall Γ₁ Γ₂ Γ₃ c τ e v type exp,
  ((ctx_add_var (add_ctx Γ₂ Γ₁) v type exp) !!₁ c) = (Some (τ, e)) ->
  ((ctx_add_var (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) v type exp) !!₁ c) = (Some (τ, e)).
Proof.
  intros.
  unfold ctx_add_var, add_ctx, var_ctx_lookup in *. simpl in *.
  Search union.
  pose proof (insert_union_singleton_l ((Γ₁.1) ∪ ((Γ₂.1) ∪ (Γ₃.1)))).
  rewrite (H0 v (type, exp)) at 1.
  Print lookup_singleton.
  destruct (({[ v := (type,exp) ]} : gmap string (i_ty * i_expr)) !! c) eqn:Hlookup.
  - apply (lookup_union_Some_l ({[ v := (type,exp) ]} : gmap string (i_ty * i_expr)) _ c _).
    rewrite <- H.
    symmetry.
    pose proof (insert_union_singleton_l ((Γ₁.1) ∪ (Γ₂.1))).
    rewrite (H1 v (type, exp)) at 1.
    rewrite Hlookup.
    apply (lookup_union_Some_l ({[ v := (type,exp) ]} : gmap string (i_ty * i_expr)) _ c _).
    exact Hlookup.
  - pose proof (lookup_union_r ({[ v := (type,exp) ]} : gmap string (i_ty * i_expr)) ((Γ₁.1) ∪ ((Γ₂.1) ∪ (Γ₃.1))) c Hlookup).
    rewrite H1 at 1.
    pose proof (lookup_union_r ({[ v := (type,exp) ]} : gmap string (i_ty * i_expr)) ((Γ₁.1) ∪ (Γ₂.1)) c Hlookup).
    pose proof (insert_union_singleton_l ((Γ₁.1) ∪ (Γ₂.1))).
    rewrite (H3 v (type, exp)) in H at 1.
    rewrite H2 in H at 1.
    apply lookup_lemma_var. exact H.
Qed.

Lemma weakening_has_type_pure :
  forall Γ₁ Γ₂ Γ₃ e τ,
    has_type_pure (add_ctx Γ₂ Γ₁) e τ ->
    has_type_pure (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) e τ.
Proof.
  intros.
  revert Γ₁ Γ₂ Γ₃ τ H.
  induction e; intros; inversion H.
  apply PString.
  apply PBool.
  apply PNat.
  apply PUnit.
  eapply PConst. apply lookup_lemma_const. exact H1. exact H2.
  eapply PVar. apply lookup_lemma_var. exact H1. exact H2.
  eapply PApp. exact H2. apply IHe1. exact H3. apply IHe2. exact H5.
  apply PPlus. apply IHe1. exact H2. apply IHe2. exact H4.
  apply PNot. apply IHe. exact H1.
  apply PAnd. apply IHe1. assumption. apply IHe2. assumption.
  apply POr. apply IHe1. assumption. apply IHe2. assumption.
  apply PImp. apply IHe1. assumption. apply IHe2. assumption.
Qed.

Lemma weakening_has_type_pure_add :
  forall Γ₁ Γ₂ Γ₃ var exp type e τ,
    has_type_pure (ctx_add_var (add_ctx Γ₂ Γ₁) var exp type) e τ ->
    has_type_pure (ctx_add_var (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) var exp type) e τ.
Proof.
  intros.
  revert Γ₁ Γ₂ Γ₃ τ H.
  induction e; intros; inversion H; subst.
  apply PString.
  apply PBool.
  apply PNat.
  apply PUnit.
  eapply PConst. apply lookup_lemma_const. exact H1. exact H2.
  eapply PVar. apply lookup_lemma_var_add. exact H1. exact H2.
  eapply PApp. exact H2. apply IHe1. exact H3. apply IHe2. exact H5.
  apply PPlus. apply IHe1. exact H2. apply IHe2. exact H4.
  apply PNot. apply IHe. exact H1.
  apply PAnd. apply IHe1. assumption. apply IHe2. assumption.
  apply POr. apply IHe1. assumption. apply IHe2. assumption.
  apply PImp. apply IHe1. assumption. apply IHe2. assumption.
Qed.

Lemma weakening_ty_valid :
  forall Γ₁ Γ₂ Γ₃ τ,
    ty_valid (add_ctx Γ₂ Γ₁) τ ->
    ty_valid (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) τ.
Proof.
  intros.
  revert Γ₁ Γ₂ Γ₃ H.
  induction τ; intros.
  apply VBase.
  eapply VSet.
  apply (weakening_has_type_pure_add Γ₁ Γ₂ Γ₃ s (TBase b) _ i (TBase BBool)).
  admit.
  apply VFun. apply IHτ1. inversion H. assumption. apply IHτ2. inversion H. assumption.
  eapply VFunDep. apply IHτ1. inversion H. assumption. admit.
  apply VPair. inversion H. apply IHτ1. assumption. inversion H. apply IHτ2. assumption.
  apply VRef. inversion H. apply IHτ. assumption.
Admitted.


Lemma weakening :
  forall Γ₁ Γ₂ Γ₃ e τ,
    has_type (add_ctx Γ₂ Γ₁) e τ ->
    has_type (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) e τ.
Proof.
intros.
simpl.
inversion H.
apply TString.
apply TNat.
apply TBool.
apply TUnit.
eapply TConst.
apply lookup_lemma_const. exact H0.
eapply TVar.
apply lookup_lemma_var. exact H0.
apply TFail. apply weakening_ty_valid. assumption.
eapply TFun. apply weakening_ty_valid. assumption. admit.
eapply TAppPure. admit. admit. admit. admit.
eapply TAppImPure. admit. admit.
apply TPlus. admit. admit. admit.
eapply TFst. admit.
eapply TSnd. admit.
eapply TIf. admit. admit. admit.
apply TSelf. admit. admit.
eapply TSub. admit. admit.
Admitted.

