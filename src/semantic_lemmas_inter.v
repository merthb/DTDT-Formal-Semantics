Require Import DTDT.syntax.
Require Import DTDT.machine_inter.
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
  pose proof (insert_union_singleton_l ((Γ₁.1) ∪ ((Γ₂.1) ∪ (Γ₃.1)))).
  rewrite (H0 v (type, exp)) at 1.
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

(* Lemma add_var_add_ctx_comm :
  forall Γ₁ Γ₂ v τ e,
    Γ₁.1 !! v = None ->
    ctx_add_var (add_ctx Γ₂ Γ₁) v τ e =
    add_ctx (ctx_add_var Γ₂ v τ e) Γ₁.
Proof.
  intros.
  unfold ctx_add_var, add_ctx. simpl.
  rewrite (insert_union_r (Γ₁.1) (Γ₂.1)). reflexivity.
  assumption.
Qed.

Lemma add_ctx_ctx_add_var :
  forall Γ1 Γ2 Γ3 v τ e,
  ctx_add_var (add_ctx (add_ctx Γ3 Γ2) Γ1) v τ e =
  add_ctx Γ3 (ctx_add_var (add_ctx Γ2 Γ1) v τ e).
Proof.
  intros.
  unfold ctx_add_var, add_ctx. simpl.
  Search union.
  rewrite (insert_union_singleton_l ((Γ1.1) ∪ ((Γ2.1) ∪ (Γ3.1)))).
  rewrite (insert_union_singleton_l ((Γ1.1) ∪ (Γ2.1))).
  f_equal.
  apply map_eq; intros k.
Admitted. *)

Lemma weakening_ty_valid :
  forall Γ₁ Γ₂ Γ₃ τ,
    ty_valid (add_ctx Γ₂ Γ₁) τ ->
    ty_valid (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) τ.
Proof.
  intros.
  remember (add_ctx Γ₂ Γ₁) as Γ.
  revert Γ₃.
  induction H; intros.
  apply VBase.
  eapply VSet. rewrite HeqΓ in H. apply weakening_has_type_pure_add. exact H.
  apply VFun. apply IHty_valid1. assumption. apply IHty_valid2. assumption.
  
  eapply VFunDep. apply IHty_valid1. assumption.
  rewrite HeqΓ in *. admit.
  
  apply VPair. apply IHty_valid1. assumption. apply IHty_valid2. assumption.
  apply VRef. apply IHty_valid. assumption.
Admitted.

Lemma weakening_subtype :
  forall Γ₁ Γ₂ Γ₃ τ₁ τ₂,
    subtype (add_ctx Γ₂ Γ₁) τ₁ τ₂ ->
    subtype (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) τ₁ τ₂.
Proof.
  intros.
  remember (add_ctx Γ₂ Γ₁) as Γ.
  revert Γ₃.
  induction H; intros.
  apply SBase.
  eapply SSet. apply weakening_ty_valid. rewrite HeqΓ in H. assumption.
  apply weakening_ty_valid. rewrite HeqΓ in H0. assumption. admit.
  
  apply SSetBase. rewrite HeqΓ in H. apply weakening_ty_valid. assumption.
  
  eapply SBaseSet. apply weakening_ty_valid. rewrite HeqΓ in H. assumption.
  admit.
  
  apply SFun. apply IHsubtype1. assumption. apply IHsubtype2. assumption.
  
  eapply SFunDep. apply IHsubtype1. assumption.
  admit.
  
  apply SPair. apply IHsubtype1. assumption. apply IHsubtype2. assumption.
  apply SRef. apply IHsubtype1. assumption. apply IHsubtype2. assumption.
Admitted.

Lemma weakening :
  forall Γ₁ Γ₂ Γ₃ e τ,
    has_type (add_ctx Γ₂ Γ₁) e τ ->
    has_type (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) e τ.
Proof.
  intros.
  remember (add_ctx Γ₂ Γ₁) as Γ.
  induction H.
  apply TString.
  apply TNat.
  apply TBool.
  apply TUnit.
  eapply TConst. rewrite HeqΓ in H. apply lookup_lemma_const. exact H.
  eapply TVar. rewrite HeqΓ in H. apply lookup_lemma_var. exact H.
  apply TFail. rewrite HeqΓ in H. apply weakening_ty_valid. exact H.

  eapply TFun. rewrite HeqΓ in *. apply weakening_ty_valid. exact H.
  rewrite HeqΓ in *. admit.

  eapply TAppPure. rewrite HeqΓ in *. apply IHhas_type1. reflexivity. 
  rewrite HeqΓ in *. intros. apply weakening_has_type_pure. exact (H0 τ₃).
  rewrite HeqΓ in *. apply IHhas_type2. reflexivity. apply IHhas_type3. assumption.

  eapply TAppImPure. apply IHhas_type1. assumption. apply IHhas_type2. assumption.
  apply TPlus. apply IHhas_type1. assumption. apply IHhas_type2. assumption.
  apply TPair. apply IHhas_type1. assumption. apply IHhas_type2. assumption.
  eapply TFst. apply IHhas_type. assumption.
  eapply TSnd. apply IHhas_type. assumption.

  eapply TIf. rewrite HeqΓ in H. apply weakening_has_type_pure. assumption.
  rewrite HeqΓ in *. admit. admit.

  eapply TSelf. apply IHhas_type. assumption.
  intros. apply weakening_has_type_pure. rewrite HeqΓ in H0. exact (H0 τ₁).

  eapply TSub. apply IHhas_type. assumption.
  rewrite HeqΓ in H0. apply weakening_subtype. assumption.
Admitted.

(* ------------------------------------------------------- *)
(* 
Lemma weakening_entails :
  forall Γ₁ Γ₂ Γ₃ e,
    (add_ctx Γ₂ Γ₁) ⊨ e ->
    (add_ctx (add_ctx Γ₂ Γ₁) Γ₃) ⊨ e.
Proof.
  intros.
  inversion H.
  apply steps_refl.
  econstructor.
  
Admitted. *)





