Require Import Coq.Lists.List.
Require Import DTDT.syntax.
Require Import DTDT.entails_inter.
Require Import DTDT.machine_inter.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.type_directed_translation.

(* Structural lemmas about context combination and lookup. *)

(* Associativity of option union used in context composition proofs. *)
Lemma option_union_assoc : forall (A : Type) (o1 o2 o3 : option A),
  (o1 ∪ o2) ∪ o3 = o1 ∪ (o2 ∪ o3).
Proof.
  intros A o1 o2 o3.
  destruct o1, o2, o3; reflexivity.
Qed.

(* Right identity of context composition. *)
Lemma add_ctx_empty_r : forall Γ,
  add_ctx empty_ctx Γ = Γ.
Proof.
  intros Γ.
  destruct Γ as [env store].
  destruct env as [vars consts].
  unfold add_ctx, empty_ctx. simpl.
  f_equal.
  - f_equal.
    + apply map_eq; intros i.
      rewrite (lookup_union vars ∅ i).
      rewrite lookup_empty.
      change (vars !! i ∪ None = vars !! i).
      destruct (vars !! i); reflexivity.
    + apply map_eq; intros i.
      rewrite (lookup_union consts ∅ i).
      rewrite lookup_empty.
      change (consts !! i ∪ None = consts !! i).
      destruct (consts !! i); reflexivity.
  - apply map_eq; intros i.
    rewrite (lookup_union store ∅ i).
    rewrite lookup_empty.
    change (store !! i ∪ None = store !! i).
    destruct (store !! i); reflexivity.
Qed.

(* Left identity of context composition. *)
Lemma add_ctx_empty_l : forall Γ,
  add_ctx Γ empty_ctx = Γ.
Proof.
  intros Γ.
  destruct Γ as [env store].
  destruct env as [vars consts].
  unfold add_ctx, empty_ctx. simpl.
  f_equal.
  - f_equal.
    + apply map_eq; intros i.
      rewrite (lookup_union ∅ vars i).
      rewrite lookup_empty.
      change (None ∪ vars !! i = vars !! i).
      destruct (vars !! i); reflexivity.
    + apply map_eq; intros i.
      rewrite (lookup_union ∅ consts i).
      rewrite lookup_empty.
      change (None ∪ consts !! i = consts !! i).
      destruct (consts !! i); reflexivity.
  - apply map_eq; intros i.
    rewrite (lookup_union ∅ store i).
    rewrite lookup_empty.
    change (None ∪ store !! i = store !! i).
    destruct (store !! i); reflexivity.
Qed.

(* Associativity of context composition. *)
Lemma add_ctx_assoc : forall Γ₁ Γ₂ Γ₃,
  add_ctx (add_ctx Γ₃ Γ₂) Γ₁ = add_ctx Γ₃ (add_ctx Γ₂ Γ₁).
Proof.
  intros Γ₁ Γ₂ Γ₃.
  destruct Γ₁ as [env1 store1]. destruct env1 as [vars1 consts1].
  destruct Γ₂ as [env2 store2]. destruct env2 as [vars2 consts2].
  destruct Γ₃ as [env3 store3]. destruct env3 as [vars3 consts3].
  unfold add_ctx. simpl.
  f_equal.
  - f_equal.
    + apply map_eq; intros i.
      rewrite (lookup_union vars1 (vars2 ∪ vars3) i).
      rewrite (lookup_union vars2 vars3 i).
      rewrite (lookup_union (vars1 ∪ vars2) vars3 i).
      rewrite (lookup_union vars1 vars2 i).
      symmetry. apply option_union_assoc.
    + apply map_eq; intros i.
      rewrite (lookup_union consts1 (consts2 ∪ consts3) i).
      rewrite (lookup_union consts2 consts3 i).
      rewrite (lookup_union (consts1 ∪ consts2) consts3 i).
      rewrite (lookup_union consts1 consts2 i).
      symmetry. apply option_union_assoc.
  - apply map_eq; intros i.
    rewrite (lookup_union store1 (store2 ∪ store3) i).
    rewrite (lookup_union store2 store3 i).
    rewrite (lookup_union (store1 ∪ store2) store3 i).
    rewrite (lookup_union store1 store2 i).
    symmetry. apply option_union_assoc.
Qed.

(* Variable extension commutes with right-context composition. *)
Lemma add_ctx_ctx_add_var : forall Γ₁ Γ₂ v τ e,
  ctx_add_var (add_ctx Γ₂ Γ₁) v τ e = add_ctx Γ₂ (ctx_add_var Γ₁ v τ e).
Proof.
  intros [envG storeG] [envD storeD] v τ e.
  destruct envG as [varsG constsG].
  destruct envD as [varsD constsD].
  unfold ctx_add_var, add_ctx. simpl.
  f_equal.
  f_equal.
  apply insert_union_l.
Qed.

(* Constant extension commutes with right-context composition. *)
Lemma add_ctx_ctx_add_const : forall Γ₁ Γ₂ f τ e,
  ctx_add_const (add_ctx Γ₂ Γ₁) f τ e = add_ctx Γ₂ (ctx_add_const Γ₁ f τ e).
Proof.
  intros [envG storeG] [envD storeD] f τ e.
  destruct envG as [varsG constsG].
  destruct envD as [varsD constsD].
  unfold ctx_add_const, add_ctx. simpl.
  f_equal.
  f_equal.
  apply insert_union_l.
Qed.


(* Constant lookups are preserved under right weakening. *)
Lemma lookup_lemma_const_right : forall Γ₁ Γ₂ c τ e,
  Γ₁ !!₂ c = Some (τ, e) ->
  (add_ctx Γ₂ Γ₁) !!₂ c = Some (τ, e).
Proof.
  intros [envG storeG] [envD storeD] c τ e H.
  destruct envG as [varsG constsG].
  destruct envD as [varsD constsD].
  unfold add_ctx, const_ctx_lookup in *. simpl in *.
  apply (lookup_union_Some_l constsG constsD c (τ, e)).
  exact H.
Qed.

(* Variable lookups are preserved under right weakening. *)
Lemma lookup_lemma_var_right : forall Γ₁ Γ₂ x τ e,
  Γ₁ !!₁ x = Some (τ, e) ->
  (add_ctx Γ₂ Γ₁) !!₁ x = Some (τ, e).
Proof.
  intros [envG storeG] [envD storeD] x τ e H.
  destruct envG as [varsG constsG].
  destruct envD as [varsD constsD].
  unfold add_ctx, var_ctx_lookup in *. simpl in *.
  apply (lookup_union_Some_l varsG varsD x (τ, e)).
  exact H.
Qed.

(* Lookup preservation restated in the paper's three-context style. *)

(* Constant lookup under three-context weakening. *)
Lemma lookup_lemma_const : forall Γ₁ Γ₂ Γ₃ c τ e,
  (add_ctx Γ₂ Γ₁) !!₂ c = Some (τ, e) ->
  (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) !!₂ c = Some (τ, e).
Proof.
  intros.
  rewrite add_ctx_assoc.
  apply lookup_lemma_const_right.
  exact H.
Qed.

(* Variable lookup under three-context weakening. *)
Lemma lookup_lemma_var : forall Γ₁ Γ₂ Γ₃ x τ e,
  (add_ctx Γ₂ Γ₁) !!₁ x = Some (τ, e) ->
  (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) !!₁ x = Some (τ, e).
Proof.
  intros.
  rewrite add_ctx_assoc.
  apply lookup_lemma_var_right.
  exact H.
Qed.

(* Store lookup is preserved under right weakening. *)
Lemma lookup_lemma_store_right : forall Γ₁ Γ₂ l τ e,
  Γ₁ !!₃ l = Some (τ, e) ->
  (add_ctx Γ₂ Γ₁) !!₃ l = Some (τ, e).
Proof.
  intros [envG storeG] [envD storeD] l τ e H.
  destruct envG as [varsG constsG].
  destruct envD as [varsD constsD].
  unfold add_ctx, store_ctx_lookup in *. simpl in *.
  apply (lookup_union_Some_l storeG storeD l (τ, e)).
  exact H.
Qed.

(* Variable lookup under weakening with an additional local binding. *)
Lemma lookup_lemma_var_add : forall Γ₁ Γ₂ Γ₃ x τ e v τv exp,
  ((add_ctx Γ₂ Γ₁) ,,v v ↦ (τv, exp)) !!₁ x = Some (τ, e) ->
  ((add_ctx (add_ctx Γ₃ Γ₂) Γ₁) ,,v v ↦ (τv, exp)) !!₁ x = Some (τ, e).
Proof.
  intros.
  rewrite add_ctx_ctx_add_var.
  rewrite add_ctx_ctx_add_var in H.
  rewrite add_ctx_assoc.
  apply lookup_lemma_var_right.
  exact H.
Qed.


(* ==================== PAPER LEMMA 3 ====================
   Weakening: adding assumptions on the right preserves entailment, typing,
   validity, and subtyping. *)

(* Weakening for entailment. *)
Lemma weakening_entails_right : forall Γ₁ Γ₂ e,
  Γ₁ ⊨ e ->
  add_ctx Γ₂ Γ₁ ⊨ e.
Proof.
  intros Γ₁ Γ₂ e H.
  pose proof (entails_weakening Γ₁ empty_ctx Γ₂ e) as Hweak.
  rewrite add_ctx_empty_r in Hweak.
  rewrite add_ctx_empty_l in Hweak.
  apply Hweak.
  exact H.
Qed.

(* Weakening lemmas for pure typing. *)

(* Right weakening for pure typing. *)
Lemma weakening_has_type_pure_right :
  forall Γ₁ Γ₂ e τ,
    Γ₁ ⊢pure e : τ ->
    (add_ctx Γ₂ Γ₁) ⊢pure e : τ.
Proof.
  intros Γ₁ Γ₂ e τ H.
  induction H.
  - eapply PVar.
    + apply lookup_lemma_var_right. exact H.
    + exact H0.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst.
    + apply lookup_lemma_const_right. exact H.
    + exact H0.
  - eapply PApp.
    + exact H.
    + exact IHhas_type_pure1.
    + exact IHhas_type_pure2.
  - apply PNot. exact IHhas_type_pure.
  - apply PImp; assumption.
  - apply PAnd; assumption.
  - apply POr; assumption.
  - eapply PEq; eauto.
  - apply PPlus; assumption.
Qed.

(* Three-context weakening for pure typing. *)
Lemma weakening_has_type_pure :
  forall Γ₁ Γ₂ Γ₃ e τ,
    (add_ctx Γ₂ Γ₁) ⊢pure e : τ ->
    (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) ⊢pure e : τ.
Proof.
  intros.
  rewrite add_ctx_assoc.
  apply weakening_has_type_pure_right.
  exact H.
Qed.

(* Weakening for pure typing under an additional variable binding. *)
Lemma weakening_has_type_pure_add :
  forall Γ₁ Γ₂ Γ₃ var exp τ₀ e τ,
    (ctx_add_var (add_ctx Γ₂ Γ₁) var exp τ₀) ⊢pure e : τ ->
    (ctx_add_var (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) var exp τ₀) ⊢pure e : τ.
Proof.
  intros.
  rewrite add_ctx_ctx_add_var.
  rewrite add_ctx_ctx_add_var in H.
  rewrite add_ctx_assoc.
  apply weakening_has_type_pure_right.
  exact H.
Qed.

(* Weakening lemmas for type validity. *)

(* Right weakening for type validity. *)
Lemma weakening_ty_valid_right :
  forall Γ₁ Γ₂ τ,
    Γ₁ ⊢valid τ ->
    (add_ctx Γ₂ Γ₁) ⊢valid τ.
Proof.
  intros Γ₁ Γ₂ τ H.
  induction H.
  - apply VBase.
  - eapply VSet.
    rewrite add_ctx_ctx_add_var.
    apply weakening_has_type_pure_right.
    exact H.
  - apply VFun; assumption.
  - eapply VFunDep.
    + exact IHty_valid1.
    + rewrite add_ctx_ctx_add_var.
      exact IHty_valid2.
  - apply VPair; assumption.
  - apply VRef. exact IHty_valid.
Qed.

(* Three-context weakening for type validity. *)
Lemma weakening_ty_valid :
  forall Γ₁ Γ₂ Γ₃ τ,
    (add_ctx Γ₂ Γ₁) ⊢valid τ ->
    (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) ⊢valid τ.
Proof.
  intros.
  rewrite add_ctx_assoc.
  apply weakening_ty_valid_right.
  exact H.
Qed.

(* Weakening lemmas for subtyping. *)

(* Right weakening for subtyping. *)
Lemma weakening_subtype_right :
  forall Γ₁ Γ₂ τ₁ τ₂,
    subtype Γ₁ τ₁ τ₂ ->
    subtype (add_ctx Γ₂ Γ₁) τ₁ τ₂.
Proof.
  intros Γ₁ Γ₂ τ₁ τ₂ H.
  induction H.
  - apply SBase.
  - eapply SSet.
    + apply weakening_ty_valid_right. exact H.
    + apply weakening_ty_valid_right. exact H0.
    + rewrite add_ctx_ctx_add_var.
      apply weakening_entails_right.
      exact H1.
  - apply SSetBase.
    apply weakening_ty_valid_right.
    exact H.
  - eapply SBaseSet.
    + apply weakening_ty_valid_right. exact H.
    + rewrite add_ctx_ctx_add_var.
      apply weakening_entails_right.
      exact H0.
  - apply SFun; assumption.
  - eapply SFunDep.
    + exact IHsubtype1.
    + rewrite add_ctx_ctx_add_var.
      exact IHsubtype2.
  - apply SPair; assumption.
  - apply SRef.
    + exact IHsubtype1.
    + exact IHsubtype2.
Qed.

(* Three-context weakening for subtyping. *)
Lemma weakening_subtype :
  forall Γ₁ Γ₂ Γ₃ τ₁ τ₂,
    subtype (add_ctx Γ₂ Γ₁) τ₁ τ₂ ->
    subtype (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) τ₁ τ₂.
Proof.
  intros.
  rewrite add_ctx_assoc.
  apply weakening_subtype_right.
  exact H.
Qed.

(* Weakening lemmas for internal typing. *)

(* Right weakening for internal typing. *)
Lemma weakening_right :
  forall Γ₁ Γ₂ e τ,
    has_type Γ₁ e τ ->
    has_type (add_ctx Γ₂ Γ₁) e τ.
Proof.
  intros Γ₁ Γ₂ e τ H.
  induction H.
  - apply TString.
  - apply TNat.
  - apply TBool.
  - apply TUnit.
  - eapply TConst.
    apply lookup_lemma_const_right.
    exact H.
  - eapply TVar.
    apply lookup_lemma_var_right.
    exact H.
  - eapply TEssentialVar.
    + apply lookup_lemma_var_right.
      exact H.
    + exact H0.
  - eapply TLoc.
    apply lookup_lemma_store_right.
    exact H.
  - apply TFail.
    apply weakening_ty_valid_right.
    exact H.
  - eapply TFun.
    + apply weakening_ty_valid_right. exact H.
    + rewrite add_ctx_ctx_add_const.
      rewrite add_ctx_ctx_add_var.
      exact IHhas_type.
  - eapply TAppPure.
    + exact IHhas_type1.
    + intros ty3. apply weakening_has_type_pure_right. exact (H0 ty3).
    + exact IHhas_type2.
  - eapply TAppImPure.
    + exact IHhas_type1.
    + exact IHhas_type2.
  - apply TPlus; assumption.
  - apply TNot. exact IHhas_type.
  - apply TImp; assumption.
  - apply TAnd; assumption.
  - apply TOr; assumption.
  - eapply TEq; eauto.
  - eapply TRefI.
    + apply weakening_ty_valid_right. exact H.
    + exact IHhas_type.
  - eapply TGet. exact IHhas_type.
  - eapply TSetI.
    + exact IHhas_type1.
    + exact IHhas_type2.
  - apply TPair; assumption.
  - eapply TFst. exact IHhas_type.
  - eapply TSnd. exact IHhas_type.
  - eapply TIf.
    + apply weakening_has_type_pure_right. exact H.
    + rewrite add_ctx_ctx_add_var. exact IHhas_type1.
    + rewrite add_ctx_ctx_add_var. exact IHhas_type2.
  - eapply TSelf.
    + exact IHhas_type.
    + intros ty1. apply weakening_has_type_pure_right. exact (H0 ty1).
  - eapply TSub.
    + exact IHhas_type.
    + apply weakening_subtype_right. exact H0.
Qed.

(* Three-context weakening for internal typing. *)
Lemma weakening :
  forall Γ₁ Γ₂ Γ₃ e τ,
    has_type (add_ctx Γ₂ Γ₁) e τ ->
    has_type (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) e τ.
Proof.
  intros.
  rewrite add_ctx_assoc.
  apply weakening_right.
  exact H.
Qed.

(* ==================== PAPER LEMMA 1 ====================
   If Γ ⊢pure e : τ, then Γ ⊢ e : τ. *)
Lemma pure_implies_internal_typing :
  forall Γ e τ,
    Γ ⊢pure e : τ ->
    has_type Γ e τ.
Proof.
  intros Γ e τ Hpure.
  induction Hpure.
  - eapply TEssentialVar; eauto.
  - apply TNat.
  - apply TBool.
  - apply TString.
  - apply TUnit.
  - eapply TConst. exact H.
  - eapply TAppImPure.
    + exact IHHpure2.
    + exact IHHpure1.
  - apply TNot. exact IHHpure.
  - apply TImp; assumption.
  - apply TAnd; assumption.
  - apply TOr; assumption.
  - apply TEq with (τb := τb); assumption.
  - apply TPlus; assumption.
Qed.

(* ==================== PAPER LEMMA 8 ====================
   Inversion principles for the nontrivial value forms used in preservation. *)

(* Inversion principle for typed reference locations. *)
Lemma inversion_ref :
  forall Γ l τ,
    has_type Γ (EVar l) (TRef τ) ->
    exists v, Γ !!₃ l = Some (τ, v).
Admitted.


(* Membership after removal implies prior membership and inequality. *)
Lemma in_remove_string :
  forall x y xs,
    List.In x (remove_string y xs) ->
    List.In x xs /\ x <> y.
Proof.
  intros x y xs HIn.
  unfold remove_string in HIn.
  rewrite <- elem_of_list_In in HIn.
  rewrite elem_of_list_filter in HIn.
  destruct HIn as [Hneq Hin].
  rewrite elem_of_list_In in Hin.
  split.
  - exact Hin.
  - intro Heq. subst.
    rewrite String.eqb_refl in Hneq.
    simpl in Hneq.
    contradiction.
Qed.

(* An unrelated variable lookup survives an added binding. *)
Lemma lookup_lemma_var_added_ne :
  forall Γ y τy val_y x τ e,
    x <> y ->
    (Γ ,,v y ↦ (τy, val_y)) !!₁ x = Some (τ, e) ->
    Γ !!₁ x = Some (τ, e).
Proof.
  intros [env store] y τy val_y x τ e Hneq Hlookup.
  destruct env as [vars consts].
  unfold var_ctx_lookup, ctx_add_var in *.
  simpl in *.
  assert (Hyx : y <> x) by congruence.
  rewrite (lookup_insert_ne vars y x (τy, val_y) Hyx) in Hlookup.
  exact Hlookup.
Qed.

(* ==================== PAPER LEMMA 2 ====================
   Pure-expression clause: if ? ?pure e : ? and x ? FV(e), then x is
   assigned a base essential type in ?. *)
Lemma free_var_pure_is_base_typed :
  forall Γ e τ x,
    Γ ⊢pure e : τ ->
    List.In x (free_exp_vars e) ->
    exists τx val_x, Γ !!₁ x = Some (τx, val_x) /\ β[ τx ].
Proof.
  intros Γ e τ x Hpure.
  induction Hpure; intros Hin; simpl in Hin.
  - destruct Hin as [Heq | Hin].
    + subst.
      exists τb, e.
      split; assumption.
    + contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (IHHpure1 Hin).
    + exact (IHHpure2 Hin).
  - exact (IHHpure Hin).
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (IHHpure1 Hin).
    + exact (IHHpure2 Hin).
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (IHHpure1 Hin).
    + exact (IHHpure2 Hin).
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (IHHpure1 Hin).
    + exact (IHHpure2 Hin).
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (IHHpure1 Hin).
    + exact (IHHpure2 Hin).
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (IHHpure1 Hin).
    + exact (IHHpure2 Hin).
Qed.

(* Paper Lemma 2, valid-type clause.
   If Γ ⊢valid τ and x ∈ FV(τ), then x is assigned a base essential type in Γ. *)
Lemma free_var_valid_type_is_base_typed :
  forall Γ τ x,
    Γ ⊢valid τ ->
    List.In x (free_ty_vars τ) ->
    exists τx val_x, Γ !!₁ x = Some (τx, val_x) /\ β[ τx ].
Proof.
  intros Γ τ x Hvalid.
  induction Hvalid; intros Hin; simpl in Hin.
  - contradiction.
  - apply in_remove_string in Hin.
    destruct Hin as [Hin Hneq].
    destruct (free_var_pure_is_base_typed _ _ _ _ H Hin) as [τx Hrest].
    destruct Hrest as [val_x Hrest].
    destruct Hrest as [Hlookup Hbeta].
    exists τx, val_x.
    split.
    + eapply lookup_lemma_var_added_ne; eauto.
    + exact Hbeta.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (IHHvalid1 Hin).
    + exact (IHHvalid2 Hin).
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (IHHvalid1 Hin).
    + apply in_remove_string in Hin.
      destruct Hin as [Hin Hneq].
      destruct (IHHvalid2 Hin) as [τx Hrest].
      destruct Hrest as [val_x Hrest].
      destruct Hrest as [Hlookup Hbeta].
      exists τx, val_x.
      split.
      * eapply lookup_lemma_var_added_ne; eauto.
      * exact Hbeta.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (IHHvalid1 Hin).
    + exact (IHHvalid2 Hin).
  - exact (IHHvalid Hin).
Qed.

(* Changing one variable's annotation preserves other lookups. *)
Lemma lookup_lemma_var_change_type :
  forall Γ x τ τ' witness y τ₀ e,
    y <> x ->
    (Γ ,,v x ↦ (τ, witness)) !!₁ y = Some (τ₀, e) ->
    (Γ ,,v x ↦ (τ', witness)) !!₁ y = Some (τ₀, e).
Proof.
  intros [env store] x τ τ' witness y τ₀ e Hneq Hlookup.
  destruct env as [vars consts].
  unfold var_ctx_lookup, ctx_add_var in *.
  simpl in *.
  destruct (decide (y = x)) as [Heq | Hneq'].
  - contradiction.
  - assert (Hxy : x ≠ y) by congruence.
    rewrite (lookup_insert_ne vars x y (τ, witness) Hxy) in Hlookup.
    rewrite (lookup_insert_ne vars x y (τ', witness) Hxy).
    exact Hlookup.
Qed.

(* Subtyping preserves the essential carrier of base-like types. *)
Lemma subtype_preserves_essential_type :
  forall Γ τ' τ,
    subtype Γ τ' τ ->
    β[ τ ] ->
    β[ τ' ] /\ essential_type τ' = essential_type τ.
Proof.
  intros Γ τ' τ Hsub Hbeta.
  destruct Hsub; simpl in *; try contradiction; split; reflexivity.
Qed.

(* ==================== PAPER LEMMA 4 ====================
   Entailment clause: subsuming a variable binding in ? preserves semantic
   entailment judgments. *)
Lemma subsumption_entails_var :
  forall Γ₁ Γ₂ x τ τ' witness e,
    subtype Γ₁ τ' τ ->
    ((add_ctx Γ₂ Γ₁) ,,v x ↦ (τ, witness)) ⊨ e ->
    ((add_ctx Γ₂ Γ₁) ,,v x ↦ (τ', witness)) ⊨ e.
Admitted.

(* Paper Lemma 4, pure-typing clause.
   Subsuming a variable binding in Γ preserves judgments of the form Γ ⊢pure e : τ. *)
Lemma subsumption_has_type_pure_var :
  forall Γ₁ Γ₂ x τ τ' witness e τ₁,
    subtype Γ₁ τ' τ ->
    ((add_ctx Γ₂ Γ₁) ,,v x ↦ (τ, witness)) ⊢pure e : τ₁ ->
    ((add_ctx Γ₂ Γ₁) ,,v x ↦ (τ', witness)) ⊢pure e : τ₁.
Proof.
  intros Γ₁ Γ₂ x τ τ' witness e τ₁ Hsub Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [H | H].
      * destruct H as [_ Hbinding].
        inversion Hbinding; subst.
        destruct (subtype_preserves_essential_type Γ₁ τ' τb Hsub H0) as [Hbeta' Hessential].
        rewrite <- Hessential.
        apply PVar with (τb := τ') (e := e).
        -- unfold var_ctx_lookup, ctx_add_var.
           simpl.
           apply lookup_insert.
        -- exact Hbeta'.
      * destruct H as [Hneq' _].
        contradiction.
    + apply PVar with (τb := τb) (e := e).
      * eapply lookup_lemma_var_change_type with (τ := τ) (τ' := τ') (witness := witness); eauto.
      * exact H0.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst; eauto.
  - eapply PApp; eauto.
  - apply PNot. assumption.
  - apply PImp; assumption.
  - apply PAnd; assumption.
  - apply POr; assumption.
  - eapply PEq; eauto.
  - apply PPlus; assumption.
Qed.

(* Paper Lemma 4, validity clause.
   Subsuming a variable binding in Γ preserves judgments of the form Γ ⊢valid τ. *)
Lemma subsumption_ty_valid_var :
  forall Γ₁ Γ₂ x τ τ' witness τ₁,
    subtype Γ₁ τ' τ ->
    ((add_ctx Γ₂ Γ₁) ,,v x ↦ (τ, witness)) ⊢valid τ₁ ->
    ((add_ctx Γ₂ Γ₁) ,,v x ↦ (τ', witness)) ⊢valid τ₁.
Admitted.

(* Paper Lemma 4, subtyping clause.
   Subsuming a variable binding in Γ preserves judgments of the form Γ ⊢ τ₁ ≤ τ₂. *)
Lemma subsumption_subtype_var :
  forall Γ₁ Γ₂ x τ τ' witness τ₁ τ₂,
    subtype Γ₁ τ' τ ->
    subtype ((add_ctx Γ₂ Γ₁) ,,v x ↦ (τ, witness)) τ₁ τ₂ ->
    subtype ((add_ctx Γ₂ Γ₁) ,,v x ↦ (τ', witness)) τ₁ τ₂.
Admitted.

(* Paper Lemma 4, typing clause.
   Subsuming a variable binding in Γ preserves judgments of the form Γ ⊢ e : τ. *)
Lemma subsumption_has_type_var :
  forall Γ₁ Γ₂ x τ τ' witness e τ₁,
    subtype Γ₁ τ' τ ->
    has_type ((add_ctx Γ₂ Γ₁) ,,v x ↦ (τ, witness)) e τ₁ ->
    has_type ((add_ctx Γ₂ Γ₁) ,,v x ↦ (τ', witness)) e τ₁.
Admitted.

(* ==================== PAPER LEMMA 5 ====================
   If Γ ⊢ e : {x:τb | p} and e is a value, then Γ ⊨ p[e/x]. *)
Lemma canonical_forms_set :
  forall Γ e₀ x τb pred,
    DTDT.machine_inter.value Γ e₀ ->
    has_type Γ e₀ (TSet x τb pred) ->
    Γ ⊨ expr_subst x e₀ pred.
Admitted.

(* ==================== PAPER LEMMA 6 ====================
   Pure-typing clause: base substitution preserves derivations of ? ?pure e : ?. *)
Lemma subst_base_has_type_pure :
  forall Γ₁ Γ₂ x e₀ τ₀ e τ,
    has_type_pure Γ₁ e₀ τ₀ ->
    has_type (ctx_add_var (add_ctx Γ₂ Γ₁) x τ₀ e₀) e τ ->
    has_type_pure (add_ctx (ctx_subst x e₀ Γ₂) Γ₁) (expr_subst x e₀ e) (ty_subst x e₀ τ).
Admitted.

(* Paper Lemma 6, validity clause.
   Base substitution preserves type validity derivations Γ ⊢valid τ. *)
Lemma subst_base_ty_valid :
  forall Γ₁ Γ₂ x e₀ τ₀ τ,
    has_type_pure Γ₁ e₀ τ₀ ->
    ty_valid (ctx_add_var (add_ctx Γ₂ Γ₁) x τ₀ e₀) τ ->
    ty_valid (add_ctx (ctx_subst x e₀ Γ₂) Γ₁) (ty_subst x e₀ τ).
Admitted.

(* Paper Lemma 6, subtyping clause.
   Base substitution preserves subtyping derivations Γ ⊢ τ₁ ≤ τ₂. *)
Lemma subst_base_subtype :
  forall Γ₁ Γ₂ x e₀ τ₀ τ₁ τ₂,
    has_type_pure Γ₁ e₀ τ₀ ->
    subtype (ctx_add_var (add_ctx Γ₂ Γ₁) x τ₀ e₀) τ₁ τ₂ ->
    subtype (add_ctx (ctx_subst x e₀ Γ₂) Γ₁) (ty_subst x e₀ τ₁) (ty_subst x e₀ τ₂).
Admitted.

(* Paper Lemma 6, selfification clause.
   Base substitution is compatible with selfification, up to the subtyping relation. *)
Lemma subst_base_self_subtype :
  forall Γ₁ Γ₂ x e₀ τ₀ e τ,
    has_type_pure Γ₁ e₀ τ₀ ->
    has_type (ctx_add_var (add_ctx Γ₂ Γ₁) x τ₀ e₀) e τ ->
    subtype (add_ctx (ctx_subst x e₀ Γ₂) Γ₁)
      (self (ty_subst x e₀ τ) (expr_subst x e₀ e))
      (ty_subst x e₀ (self τ e)).
Admitted.

(* Paper Lemma 6, typing clause.
   Base substitution preserves internal typing derivations Γ ⊢ e : τ. *)
Lemma subst_base_has_type :
  forall Γ₁ Γ₂ x e₀ τ₀ e τ,
    has_type_pure Γ₁ e₀ τ₀ ->
    has_type (ctx_add_var (add_ctx Γ₂ Γ₁) x τ₀ e₀) e τ ->
    has_type (add_ctx (ctx_subst x e₀ Γ₂) Γ₁) (expr_subst x e₀ e) (ty_subst x e₀ τ).
Admitted.

(* ==================== PAPER LEMMA 7 ====================
   Pure-typing clause: non-base substitution preserves derivations of Γ ⊢pure e : τ
   when the substituted type is not base-like. *)
Lemma subst_nonbase_has_type_pure :
  forall Γ₁ Γ₂ x v τ₀ e τ,
    [| τ₀ |] <> TBase BBool ->
    has_type_pure (ctx_add_var (add_ctx Γ₂ Γ₁) x τ₀ v) e τ ->
    has_type_pure (add_ctx Γ₂ Γ₁) (expr_subst x v e) τ.
Admitted.

(* Paper Lemma 7, validity clause.
   Substituting a non-base value for x preserves type validity. *)
Lemma subst_nonbase_ty_valid :
  forall Γ₁ Γ₂ x v τ₀ τ,
    [| τ₀ |] <> TBase BBool ->
    ty_valid (ctx_add_var (add_ctx Γ₂ Γ₁) x τ₀ v) τ ->
    ty_valid (add_ctx Γ₂ Γ₁) τ.
Admitted.

(* Substitution of a non-base value into subtyping derivations. *)
Lemma subst_nonbase_subtype :
  forall Γ₁ Γ₂ x v τ₀ τ₁ τ₂,
    [| τ₀ |] <> TBase BBool ->
    subtype (ctx_add_var (add_ctx Γ₂ Γ₁) x τ₀ v) τ₁ τ₂ ->
    subtype (add_ctx Γ₂ Γ₁) τ₁ τ₂.
Admitted.

(* Substitution of a non-base value into typing derivations. *)
Lemma subst_nonbase_has_type :
  forall Γ₁ Γ₂ x v τ₀ e τ,
    [| τ₀ |] <> TBase BBool ->
    DTDT.machine_inter.value empty_ctx v ->
    has_type (ctx_add_var (add_ctx Γ₂ Γ₁) x τ₀ v) e τ ->
    has_type (add_ctx Γ₂ Γ₁) (expr_subst x v e) τ.
Admitted.

(* Inversion principle for typed fixpoints. *)
Lemma inversion_fix :
  forall Γ f x ty1 ty2 body ty3 ty4,
    has_type Γ (EFix f x ty1 ty2 body) (TArrDep x ty3 ty4) ->
    subtype Γ ty3 ty1 /\
    subtype (ctx_add_var Γ x ty3 (EVar x)) ty2 ty4 /\
    has_type Γ (EFix f x ty1 ty2 body) (TArrDep x ty1 ty2) /\
    has_type (ctx_add_const Γ f (TArrDep x ty1 ty2) (EFix f x ty1 ty2 body)) body ty2.
Admitted.

(* Inversion principle for typed pairs. *)
Lemma inversion_pair :
  forall Γ e1 e2 ty1 ty2,
    has_type Γ (EPair e1 e2) (TProd ty1 ty2) ->
    has_type Γ e1 ty1 /\ has_type Γ e2 ty2.
Admitted.

(* ==================== PAPER LEMMA 10 ====================
   Step lemmas relating one machine step to the logical side conditions used in
   preservation. *)

(* One-step reduction preserves the entailment side condition used in preservation. *)
Lemma step_lemma_entails :
  forall Γ e e' τb τ₁ pred,
    step (Γ, e) (Γ, e') ->
    has_type_pure empty_ctx e (TBase τb) ->
    [| τ₁ |] = TBase τb ->
    has_type_pure (ctx_add_var Γ "x" τ₁ e) pred (TBase BBool) ->
    entails Γ (EImp (expr_subst "x" e' pred) (expr_subst "x" e pred)).
Admitted.

(* One-step reduction preserves the subtype side condition used in preservation. *)
Lemma step_lemma_subtype :
  forall Γ e e' x τb τ₁ τ,
    step (Γ, e) (Γ, e') ->
    has_type_pure empty_ctx e (TBase τb) ->
    [| τ₁ |] = TBase τb ->
    ty_valid (ctx_add_var Γ x τ₁ e) τ ->
    subtype Γ (ty_subst x e' τ) (ty_subst x e τ).
Admitted.

Lemma step_lemma_bool_entails :
  forall Γ₁ Γ₂ u e e' e1,
    step (empty_ctx, e) (empty_ctx, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    (entails (ctx_add_var (add_ctx Γ₂ Γ₁) u (TBase BBool) e) e1 <->
     entails (ctx_add_var (add_ctx Γ₂ Γ₁) u (TBase BBool) e') e1).
Admitted.

Lemma step_lemma_bool_typing :
  forall Γ₁ Γ₂ u e e' e1 ty1,
    step (empty_ctx, e) (empty_ctx, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    (has_type (ctx_add_var (add_ctx Γ₂ Γ₁) u (TBase BBool) e) e1 ty1 <->
     has_type (ctx_add_var (add_ctx Γ₂ Γ₁) u (TBase BBool) e') e1 ty1).
Admitted.







