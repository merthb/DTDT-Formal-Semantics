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
  intros [envΓ storeΓ] [envD storeD] v τ e.
  destruct envΓ as [varsΓ constsΓ].
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
  intros [envΓ storeΓ] [envD storeD] f τ e.
  destruct envΓ as [varsΓ constsΓ].
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
  intros [envΓ storeΓ] [envD storeD] c τ e H.
  destruct envΓ as [varsΓ constsΓ].
  destruct envD as [varsD constsD].
  unfold add_ctx, const_ctx_lookup in *. simpl in *.
  apply (lookup_union_Some_l constsΓ constsD c (τ, e)).
  exact H.
Qed.

(* Variable lookups are preserved under right weakening. *)
Lemma lookup_lemma_var_right : forall Γ₁ Γ₂ x τ e,
  Γ₁ !!₁ x = Some (τ, e) ->
  (add_ctx Γ₂ Γ₁) !!₁ x = Some (τ, e).
Proof.
  intros [envΓ storeΓ] [envD storeD] x τ e H.
  destruct envΓ as [varsΓ constsΓ].
  destruct envD as [varsD constsD].
  unfold add_ctx, var_ctx_lookup in *. simpl in *.
  apply (lookup_union_Some_l varsΓ varsD x (τ, e)).
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
  intros [envΓ storeΓ] [envD storeD] l τ e H.
  destruct envΓ as [varsΓ constsΓ].
  destruct envD as [varsD constsD].
  unfold add_ctx, store_ctx_lookup in *. simpl in *.
  apply (lookup_union_Some_l storeΓ storeD l (τ, e)).
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

(* Inversion principle for typed reference locations.
   In the paper, locations are separate from variables and inversion exposes the
   store typing directly. In this encoding both are represented as EVar, so we
   assume l is not shadowed by the variable context and record the reference
   type's origin through any trailing uses of TSub. *)
Inductive ref_type_origin (Γ : ctx) : i_ty -> i_ty -> Prop :=
| RefOriginHere :
    forall τ,
      ref_type_origin Γ (TRef τ) (TRef τ)
| RefOriginStep :
    forall τ1 τ2 τ3,
      ref_type_origin Γ (TRef τ1) (TRef τ2) ->
      subtype Γ (TRef τ2) (TRef τ3) ->
      ref_type_origin Γ (TRef τ1) (TRef τ3).

Lemma self_ref_inv :
  forall τ e τ',
    self τ e = TRef τ' ->
    τ = TRef τ'.
Proof.
  intros τ e τ' Hself.
  destruct τ; simpl in Hself; try discriminate.
  - destruct τ1; simpl in Hself; discriminate.
  - inversion Hself. reflexivity.
Qed.


Lemma self_pair_inv :
  forall t e1 e2 t1 t2,
    self t (EPair e1 e2) = TProd t1 t2 ->
    t = TProd t1 t2.
Proof.
  intros t e1 e2 t1 t2 Hself.
  destruct t; simpl in Hself; try discriminate.
  - match goal with | tdom : i_ty, tcod : i_ty |- _ => destruct tdom; simpl in Hself; discriminate end.
  - inversion Hself. reflexivity.
Qed.

Lemma inversion_ref :
  forall Γ l τ,
    var_ctx_lookup Γ l = None ->
    has_type Γ (EVar l) (TRef τ) ->
    exists τ' v,
      store_ctx_lookup Γ l = Some (τ', v) /\
      ref_type_origin Γ (TRef τ') (TRef τ).
Proof.
  intros Γ l τ Hnone Hty.
  remember (EVar l) as e eqn:He.
  remember (TRef τ) as tref eqn:Ht.
  revert l τ Hnone He Ht.
  induction Hty; intros l0 τ0 Hnone He Ht.
  all: inversion He; subst; try discriminate.
  all: try (inversion Ht; subst); try discriminate.
  - rewrite H in Hnone. discriminate.
  - rewrite H in Hnone. discriminate.
  - exists τ0, v. split.
    + exact H.
    + apply RefOriginHere.
  - match goal with
    | Hself : self ?τ (EVar l0) = TRef τ0 |- _ =>
        apply self_ref_inv in Hself;
        inversion Hself; subst
    end.
    eapply IHHty; eauto.
  - inversion H; subst; try discriminate.
    pose proof (IHHty l0 t Hnone eq_refl eq_refl) as Hinv.
    destruct Hinv as [τ_store Hinv].
    destruct Hinv as [v Hinv].
    destruct Hinv as [Hstore Horigin].
    exists τ_store, v. split.
    + exact Hstore.
    + eapply RefOriginStep.
      * exact Horigin.
      * apply SRef; assumption.
Qed.


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

Lemma has_type_pure_empty_ctx_closed :
  forall e t,
    has_type_pure empty_ctx e t ->
    free_exp_vars e = [].
Proof.
  intros e t Hpure.
  remember (free_exp_vars e) as fvs eqn:Hfv.
  destruct fvs.
  - reflexivity.
  - exfalso.
    assert (Hin : List.In s (free_exp_vars e)).
    { rewrite <- Hfv. simpl. auto. }
    pose proof (free_var_pure_is_base_typed empty_ctx e t s Hpure Hin) as Hlookupx.
    destruct Hlookupx as [tx Hlookupx].
    destruct Hlookupx as [val_x Hlookupx].
    destruct Hlookupx as [Hlookup Hbeta].
    unfold var_ctx_lookup, empty_ctx in Hlookup.
    simpl in Hlookup.
    discriminate.
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

Lemma in_var_dom_lookup :
  forall Γ l,
    List.In l (var_dom Γ) ->
    is_Some (var_ctx_lookup Γ l).
Proof.
  intros Γ l Hin.
  destruct Γ as [env store].
  destruct env as [vars consts].
  unfold var_dom, var_ctx_lookup in *.
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

Lemma lookup_in_var_dom :
  forall Γ l entry,
    var_ctx_lookup Γ l = Some entry ->
    List.In l (var_dom Γ).
Proof.
  intros Γ l entry Hlookup.
  destruct Γ as [env store].
  destruct env as [vars consts].
  unfold var_dom, var_ctx_lookup in *.
  simpl in *.
  apply in_map_iff.
  exists (l, entry).
  split.
  - reflexivity.
  - apply elem_of_list_In.
    apply elem_of_map_to_list.
    exact Hlookup.
Qed.

Lemma fresh_var_dom_change_type :
  forall Γ x τold τnew witness l,
    var_ctx_lookup Γ x = Some (τold, witness) ->
    ~ List.In l (var_dom Γ) ->
    ~ List.In l (var_dom (ctx_add_var Γ x τnew witness)).
Proof.
  intros Γ x τold τnew witness l Hbind Hfresh Hin.
  apply Hfresh.
  destruct (in_var_dom_lookup (ctx_add_var Γ x τnew witness) l Hin) as [entry Hlookup].
  unfold var_ctx_lookup, ctx_add_var in Hlookup.
  simpl in Hlookup.
  apply lookup_insert_Some in Hlookup.
  destruct Hlookup as [Hcase | Hcase].
  - destruct Hcase as [Heq _].
    subst l.
    eapply lookup_in_var_dom.
    exact Hbind.
  - destruct Hcase as [_ Hlookup].
    eapply lookup_in_var_dom.
    exact Hlookup.
Qed.

Lemma ctx_add_var_store_comm :
  forall Γ x τ witness l τstore v,
    ctx_add_var (ctx_add_store Γ l τstore v) x τ witness =
    ctx_add_store (ctx_add_var Γ x τ witness) l τstore v.
Proof.
  intros Γ x τ witness l τstore v.
  destruct Γ as [env store].
  destruct env as [vars consts].
  reflexivity.
Qed.

Lemma value_change_var_type :
  forall Γ x τold τnew witness v,
    var_ctx_lookup Γ x = Some (τold, witness) ->
    value Γ v ->
    value (ctx_add_var Γ x τnew witness) v.
Proof.
  intros Γ x τold τnew witness v Hbind Hv.
  induction Hv.
  - apply VNat.
  - apply VBool.
  - apply VUnit.
  - apply VString.
  - eapply VConst.
    unfold const_ctx_lookup, ctx_add_var in *.
    simpl in *.
    exact H.
  - apply VFix.
  - constructor.
    + exact IHHv1.
    + exact IHHv2.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + apply (@VVar (ctx_add_var Γ x τnew witness) x τnew witness).
      unfold var_ctx_lookup, ctx_add_var.
      simpl.
      apply lookup_insert.
    + eapply (@VVar (ctx_add_var Γ x τnew witness) x0).
      unfold var_ctx_lookup, ctx_add_var in *.
      simpl in *.
      rewrite (lookup_insert_ne (fst (fst Γ)) x x0 (τnew, witness)); auto.
      exact H.
  - eapply VLoc.
    unfold store_ctx_lookup, ctx_add_var in *.
    simpl in *.
    exact H.
Qed.

Lemma step_preserves_env :
  forall Γ e Γ' e',
    step (Γ, e) (Γ', e') ->
    fst (fst Γ) = fst (fst Γ') /\ snd (fst Γ) = snd (fst Γ').
Proof.
  intros Γ e Γ' e' Hstep.
  set (P := fun c1 c2 : ctx * i_expr =>
    fst (fst (fst c1)) = fst (fst (fst c2)) /\
    snd (fst (fst c1)) = snd (fst (fst c2))).
  change (P (Γ, e) (Γ', e')).
  induction Hstep; unfold P in *; simpl in *; try (split; reflexivity).
  exact IHHstep.
Qed.

Lemma step_preserves_var_lookup :
  forall Γ e Γ' e' x τ witness,
    step (Γ, e) (Γ', e') ->
    var_ctx_lookup Γ x = Some (τ, witness) ->
    var_ctx_lookup Γ' x = Some (τ, witness).
Proof.
  intros Γ e Γ' e' x τ witness Hstep Hlookup.
  destruct (step_preserves_env _ _ _ _ Hstep) as [Hvars _].
  unfold var_ctx_lookup in *.
  simpl in *.
  rewrite <- Hvars.
  exact Hlookup.
Qed.

Lemma step_change_var_type :
  forall Γ e Γ' e' x τ_old τ_new witness,
    step (Γ, e) (Γ', e') ->
    var_ctx_lookup Γ x = Some (τ_old, witness) ->
    step (ctx_add_var Γ x τ_new witness, e) (ctx_add_var Γ' x τ_new witness, e').
Proof.
  intros Γ e Γ' e' x τ_old τ_new witness Hstep.
  set (P := fun c1 c2 : ctx * i_expr =>
    match c1, c2 with
    | (Γ0, e0), (Γ1, e1) =>
        var_ctx_lookup Γ0 x = Some (τ_old, witness) ->
        step (ctx_add_var Γ0 x τ_new witness, e0)
             (ctx_add_var Γ1 x τ_new witness, e1)
    end).
  change (P (Γ, e) (Γ', e')).
  induction Hstep; unfold P in *; simpl in *; intros Hbind.
  - apply StepCtx.
    apply IHHstep.
    exact Hbind.
  - eapply StepConst.
    + unfold const_ctx_lookup, ctx_add_var in *.
      simpl in *.
      exact H.
    + eapply value_change_var_type; eauto.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + rewrite Hbind in H.
      inversion H. subst.
      eapply StepVar.
      unfold var_ctx_lookup, ctx_add_var.
      simpl.
      apply lookup_insert.
    + eapply StepVar.
      unfold var_ctx_lookup, ctx_add_var in *.
      simpl in *.
      match goal with
      | |- <[_:=_]> ?m !! ?y = Some _ =>
          rewrite (lookup_insert_ne m x y (τ_new, witness)); auto
      end.
      exact H.
  - apply StepFix.
    eapply value_change_var_type; eauto.
  - apply StepFst.
    + eapply value_change_var_type; eauto.
    + eapply value_change_var_type; eauto.
  - apply StepSnd.
    + eapply value_change_var_type; eauto.
    + eapply value_change_var_type; eauto.
  - apply StepIfTrue.
  - apply StepIfFalse.
  - rewrite ctx_add_var_store_comm.
    apply StepNew.
    + eapply value_change_var_type; eauto.
    + eapply fresh_var_dom_change_type; eauto.
    + unfold store_dom, ctx_add_var in *.
      simpl in *.
      exact H1.
  - eapply StepGet.
    unfold store_ctx_lookup, ctx_add_var in *.
    simpl in *.
    exact H.
  - rewrite ctx_add_var_store_comm.
    eapply StepSet.
    + eapply value_change_var_type; eauto.
    + unfold store_ctx_lookup, ctx_add_var in *.
      simpl in *.
      exact H0.
  - apply StepFail.
  - apply StepNot.
  - apply StepAnd.
  - apply StepOr.
  - apply StepImp.
  - apply StepEq.
    + exact H.
    + exact H0.
    + exact H1.
  - apply StepPlus.
Qed.


Lemma eval_change_var_type :
  forall Γ e Γ' e' x τ_old τ_new witness,
    eval (Γ, e) (Γ', e') ->
    var_ctx_lookup Γ x = Some (τ_old, witness) ->
    eval (ctx_add_var Γ x τ_new witness, e) (ctx_add_var Γ' x τ_new witness, e').
Proof.
  intros Γ e Γ' e' x τ_old τ_new witness Heval.
  set (P := fun c1 c2 : ctx * i_expr =>
    var_ctx_lookup (fst c1) x = Some (τ_old, witness) ->
    eval (ctx_add_var (fst c1) x τ_new witness, snd c1)
         (ctx_add_var (fst c2) x τ_new witness, snd c2)).
  change (P (Γ, e) (Γ', e')).
  induction Heval; unfold P in *; simpl in *; intros Hbind.
  - apply steps_refl.
  - lazymatch type of H with
    | step ?s1 ?s2 =>
        destruct s1 as [Γ1 e1];
        destruct s2 as [Γ2 e2]
    end.
    simpl in *.
    lazymatch type of Heval with
    | eval ?s2 ?s3 =>
        destruct s3 as [Γ3 e3]
    end.
    simpl in *.
    apply (steps_step
      (ctx_add_var Γ1 x τ_new witness, e1)
      (ctx_add_var Γ2 x τ_new witness, e2)
      (ctx_add_var Γ3 x τ_new witness, e3)).
    + exact (step_change_var_type Γ1 e1 Γ2 e2 x τ_old τ_new witness H Hbind).
    + apply IHHeval.
      exact (step_preserves_var_lookup Γ1 e1 Γ2 e2 x τ_old witness H Hbind).
Qed.

(* ==================== PAPER LEMMA 4 ====================
   Entailment clause: subsuming a variable binding in ? preserves semantic
   entailment judgments. *)
Lemma subsumption_entails_var :
  forall G1 G2 x t_old t_new witness e,
    subtype G1 t_new t_old ->
    entails (add_ctx G2 (ctx_add_var G1 x t_old witness)) e ->
    entails (add_ctx G2 (ctx_add_var G1 x t_new witness)) e.
Proof.
  intros G1 G2 x t_old t_new witness e _ Hent.
  rewrite <- add_ctx_ctx_add_var in Hent |- *.
  unfold entails in *.
  eapply (eval_change_var_type
    (ctx_add_var (add_ctx G2 G1) x t_old witness) e
    (ctx_add_var (add_ctx G2 G1) x t_old witness) (EBool true)
    x t_old t_new witness) in Hent.
  2: {
    unfold var_ctx_lookup, ctx_add_var.
    simpl.
    apply lookup_insert.
  }
  assert (Hctx :
    ctx_add_var (ctx_add_var (add_ctx G2 G1) x t_old witness) x t_new witness =
    ctx_add_var (add_ctx G2 G1) x t_new witness).
  {
    destruct (add_ctx G2 G1) as [env store].
    destruct env as [vars consts].
    unfold ctx_add_var.
    simpl.
    assert (Hins :
      <[x := (t_new, witness)]> (<[x := (t_old, witness)]> vars) =
      <[x := (t_new, witness)]> vars).
    { apply insert_insert. }
    rewrite Hins.
    reflexivity.
  }
  rewrite Hctx in Hent.
  exact Hent.
Qed.

(* Paper Lemma 4, pure-typing clause.
   Subsuming a variable binding in Γ preserves judgments of the form Γ ⊢pure e : τ. *)
Lemma subsumption_has_type_pure_var :
  forall G1 G2 x t_old t_new witness e t1,
    subtype G1 t_new t_old ->
    has_type_pure (add_ctx G2 (ctx_add_var G1 x t_old witness)) e t1 ->
    has_type_pure (add_ctx G2 (ctx_add_var G1 x t_new witness)) e t1.
Proof.
  intros G1 G2 x t_old t_new witness e t1 Hsub Hpure.
  rewrite <- add_ctx_ctx_add_var in Hpure |- *.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [H | H].
      * destruct H as [_ Hbinding].
        inversion Hbinding; subst.
        destruct (subtype_preserves_essential_type G1 t_new _ Hsub H0) as [Hbeta_new Hessential].
        rewrite <- Hessential.
        apply PVar with (e := e).
        -- unfold var_ctx_lookup, ctx_add_var.
           simpl.
           apply lookup_insert.
        -- exact Hbeta_new.
      * destruct H as [Hneq' _].
        contradiction.
    + apply PVar with (e := e).
      * eapply lookup_lemma_var_change_type; eauto.
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
Lemma ctx_add_var_shadow :
  forall C x t_old e_old t_new e_new,
    ctx_add_var (ctx_add_var C x t_old e_old) x t_new e_new =
    ctx_add_var C x t_new e_new.
Proof.
  intros C x t_old e_old t_new e_new.
  destruct C as [vc store].
  destruct vc as [vars consts].
  unfold ctx_add_var.
  simpl.
  f_equal.
  f_equal.
  apply insert_insert.
Qed.

Lemma ctx_add_var_swap :
  forall C x tx ex y ty ey,
    x <> y ->
    ctx_add_var (ctx_add_var C x tx ex) y ty ey =
    ctx_add_var (ctx_add_var C y ty ey) x tx ex.
Proof.
  intros C x tx ex y ty ey Hneq.
  destruct C as [vc store].
  destruct vc as [vars consts].
  unfold ctx_add_var.
  simpl.
  f_equal.
  f_equal.
  apply insert_commute.
  congruence.

Qed.
Lemma ctx_add_const_var_comm :
  forall C x tx ex f tf ef,
    ctx_add_const (ctx_add_var C x tx ex) f tf ef =
    ctx_add_var (ctx_add_const C f tf ef) x tx ex.
Proof.
  intros C x tx ex f tf ef.
  destruct C as [vc store].
  destruct vc as [vars consts].
  reflexivity.
Qed.

Lemma subsumption_entails_var_ctx :
  forall C x t_old t_new witness expr,
    entails (ctx_add_var C x t_old witness) expr ->
    entails (ctx_add_var C x t_new witness) expr.
Proof.
  intros C x t_old t_new witness expr Hent.
  unfold entails in *.
  eapply (eval_change_var_type
    (ctx_add_var C x t_old witness) expr
    (ctx_add_var C x t_old witness) (EBool true)
    x t_old t_new witness) in Hent.
  2: {
    unfold var_ctx_lookup, ctx_add_var.
    simpl.
    apply lookup_insert.
  }
  rewrite ctx_add_var_shadow in Hent.
  exact Hent.
Qed.

Lemma subsumption_has_type_pure_var_ctx :
  forall Delta C x t_old t_new witness expr ty,
    subtype Delta t_new t_old ->
    has_type_pure (ctx_add_var C x t_old witness) expr ty ->
    has_type_pure (ctx_add_var C x t_new witness) expr ty.
Proof.
  intros Delta C x t_old t_new witness expr ty Hsub Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [_ Hbinding].
        inversion Hbinding; subst.
        destruct (subtype_preserves_essential_type Delta t_new τb Hsub H0) as [Hbeta_new Hessential].
        rewrite <- Hessential.
        apply PVar with (τb := t_new) (e := e).
        -- unfold var_ctx_lookup, ctx_add_var.
           simpl.
           apply lookup_insert.
        -- exact Hbeta_new.
      * destruct Hcase as [Hneq' _].
        contradiction.
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

Lemma subsumption_ty_valid_var_ctx :
  forall Delta x t_old t_new witness,
    subtype Delta t_new t_old ->
    forall C ty,
      ty_valid (ctx_add_var C x t_old witness) ty ->
      ty_valid (ctx_add_var C x t_new witness) ty.
Proof.
  intros Delta x t_old t_new witness Hsub.
  fix IH 3.
  intros C ty Hvalid.
  destruct Hvalid as
    [τb
    | var τb e v Hp
    | τ₁ τ₂ Hv1 Hv2
    | var τ₁ τ₂ v Hv1 Hv2
    | τ₁ τ₂ Hv1 Hv2
    | τ Hv].
  - apply VBase.
  - eapply VSet.
    destruct (String.eq_dec var x) as [-> | Hneq].
    + rewrite ctx_add_var_shadow.
      rewrite ctx_add_var_shadow in Hp.
      exact Hp.
    + rewrite ctx_add_var_swap by congruence.
      rewrite ctx_add_var_swap in Hp by congruence.
      eapply subsumption_has_type_pure_var_ctx; eauto.
  - eapply VFun.
    + exact (IH C _ Hv1).
    + exact (IH C _ Hv2).
  - eapply VFunDep.
    + exact (IH C _ Hv1).
    + destruct (String.eq_dec var x) as [-> | Hneq].
      * rewrite ctx_add_var_shadow.
        rewrite ctx_add_var_shadow in Hv2.
        exact Hv2.
      * rewrite ctx_add_var_swap by congruence.
        rewrite ctx_add_var_swap in Hv2 by congruence.
        exact (IH (ctx_add_var C var _ v) _ Hv2).
  - eapply VPair.
    + exact (IH C _ Hv1).
    + exact (IH C _ Hv2).
  - eapply VRef.
    exact (IH C _ Hv).
Qed.

Lemma subsumption_subtype_var_ctx :
  forall Delta x t_old t_new witness,
    subtype Delta t_new t_old ->
    forall C t1 t2,
      subtype (ctx_add_var C x t_old witness) t1 t2 ->
      subtype (ctx_add_var C x t_new witness) t1 t2.
Proof.
  intros Delta x t_old t_new witness Hsub.
  fix IH 4.
  intros C t1 t2 Hsubtype.
  destruct Hsubtype as
    [b
    | var τb e₁ e₂ c Hv1 Hv2 Hent
    | var τb e Hv
    | var τb e c Hv Hent
    | τ₁ τ₁' τ₂ τ₂' Hs1 Hs2
    | var τ₁ τ₁' τ₂ τ₂' v Hs1 Hs2
    | τ₁ τ₁' τ₂ τ₂' Hs1 Hs2
    | t t' Hs1 Hs2].
  - apply SBase.
  - eapply SSet.
    + exact (subsumption_ty_valid_var_ctx Delta x t_old t_new witness Hsub C _ Hv1).
    + exact (subsumption_ty_valid_var_ctx Delta x t_old t_new witness Hsub C _ Hv2).
    + destruct (String.eq_dec var x) as [-> | Hneq].
      * rewrite ctx_add_var_shadow.
        rewrite ctx_add_var_shadow in Hent.
        exact Hent.
      * rewrite ctx_add_var_swap by congruence.
        rewrite ctx_add_var_swap in Hent by congruence.
        exact (subsumption_entails_var_ctx (ctx_add_var C var (TBase τb) (make_expr τb c)) x t_old t_new witness _ Hent).
  - eapply SSetBase.
    exact (subsumption_ty_valid_var_ctx Delta x t_old t_new witness Hsub C _ Hv).
  - eapply SBaseSet.
    + exact (subsumption_ty_valid_var_ctx Delta x t_old t_new witness Hsub C _ Hv).
    + destruct (String.eq_dec var x) as [-> | Hneq].
      * rewrite ctx_add_var_shadow.
        rewrite ctx_add_var_shadow in Hent.
        exact Hent.
      * rewrite ctx_add_var_swap by congruence.
        rewrite ctx_add_var_swap in Hent by congruence.
        exact (subsumption_entails_var_ctx (ctx_add_var C var (TBase τb) (make_expr τb c)) x t_old t_new witness _ Hent).
  - eapply SFun.
    + exact (IH C _ _ Hs1).
    + exact (IH C _ _ Hs2).
  - eapply SFunDep.
    + exact (IH C _ _ Hs1).
    + destruct (String.eq_dec var x) as [-> | Hneq].
      * rewrite ctx_add_var_shadow.
        rewrite ctx_add_var_shadow in Hs2.
        exact Hs2.
      * rewrite ctx_add_var_swap by congruence.
        rewrite ctx_add_var_swap in Hs2 by congruence.
        exact (IH (ctx_add_var C var _ v) _ _ Hs2).
  - eapply SPair.
    + exact (IH C _ _ Hs1).
    + exact (IH C _ _ Hs2).
  - eapply SRef.
    + exact (IH C _ _ Hs1).
    + exact (IH C _ _ Hs2).
Qed.

Lemma subsumption_has_type_var_ctx :
  forall x t_old t_new witness,
    (forall C, subtype (ctx_add_var C x t_new witness) t_new t_old) ->
    forall C expr ty,
      has_type (ctx_add_var C x t_old witness) expr ty ->
      has_type (ctx_add_var C x t_new witness) expr ty.
Proof.
  intros x t_old t_new witness Hsub C expr ty Hty.
  remember (ctx_add_var C x t_old witness) as G eqn:HG.
  revert C HG.
  induction Hty; intros C0 HG; subst.
  - apply TString.
  - apply TNat.
  - apply TBool.
  - apply TUnit.
  - eapply TConst.
    unfold const_ctx_lookup, ctx_add_var in *.
    simpl in *.
    exact H.
  - destruct (String.eq_dec v x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [_ Hbinding].
        inversion Hbinding; subst.
        eapply TSub.
        -- eapply TVar.
           unfold var_ctx_lookup, ctx_add_var.
           simpl.
           apply lookup_insert.
        -- exact (Hsub C0).
      * destruct Hcase as [Hneq' _].
        contradiction.
    + eapply TVar.
      eapply lookup_lemma_var_change_type; eauto.
  - destruct (String.eq_dec v x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [_ Hbinding].
        inversion Hbinding; subst.
        destruct (subtype_preserves_essential_type _ _ _ (Hsub C0) H0) as [Hbeta_new Hessential].
        rewrite <- Hessential.
        eapply TEssentialVar.
        -- unfold var_ctx_lookup, ctx_add_var.
           simpl.
           apply lookup_insert.
        -- exact Hbeta_new.
      * destruct Hcase as [Hneq' _].
        contradiction.
    + eapply TEssentialVar.
      * eapply lookup_lemma_var_change_type; eauto.
      * exact H0.
  - eapply TLoc.
    unfold store_ctx_lookup, ctx_add_var in *.
    simpl in *.
    exact H.
  - eapply TFail.
    exact (subsumption_ty_valid_var_ctx (ctx_add_var C0 x t_new witness) x t_old t_new witness (Hsub C0) C0 _ H).
  - eapply TFun.
    + exact (subsumption_ty_valid_var_ctx (ctx_add_var C0 x t_new witness) x t_old t_new witness (Hsub C0) C0 _ H).
    + destruct (String.eq_dec x0 x) as [-> | Hneq].
      * rewrite ctx_add_const_var_comm.
        rewrite ctx_add_var_shadow.
        match goal with
        | Hbody : has_type _ _ _ |- _ =>
            rewrite ctx_add_const_var_comm in Hbody;
            rewrite ctx_add_var_shadow in Hbody;
            exact Hbody
        end.
      * rewrite ctx_add_const_var_comm.
        rewrite ctx_add_var_swap by congruence.
        apply IHHty.
        rewrite ctx_add_const_var_comm.
        rewrite ctx_add_var_swap by congruence.
        reflexivity.
  - eapply TAppPure.
    + exact (IHHty1 C0 eq_refl).
    + intros ty3.
      exact (subsumption_has_type_pure_var_ctx (ctx_add_var C0 x t_new witness) C0 x t_old t_new witness _ ty3 (Hsub C0) (H ty3)).
    + exact (IHHty2 C0 eq_refl).
  - eapply TAppImPure.
    + exact (IHHty1 C0 eq_refl).
    + exact (IHHty2 C0 eq_refl).
  - eapply TPlus.
    + exact (IHHty1 C0 eq_refl).
    + exact (IHHty2 C0 eq_refl).
  - eapply TNot.
    exact (IHHty C0 eq_refl).
  - eapply TImp.
    + exact (IHHty1 C0 eq_refl).
    + exact (IHHty2 C0 eq_refl).
  - eapply TAnd.
    + exact (IHHty1 C0 eq_refl).
    + exact (IHHty2 C0 eq_refl).
  - eapply TOr.
    + exact (IHHty1 C0 eq_refl).
    + exact (IHHty2 C0 eq_refl).
  - eapply TEq.
    + exact (IHHty1 C0 eq_refl).
    + exact (IHHty2 C0 eq_refl).
  - eapply TRefI.
    + exact (subsumption_ty_valid_var_ctx (ctx_add_var C0 x t_new witness) x t_old t_new witness (Hsub C0) C0 _ H).
    + exact (IHHty C0 eq_refl).
  - eapply TGet.
    exact (IHHty C0 eq_refl).
  - eapply TSetI.
    + exact (IHHty1 C0 eq_refl).
    + exact (IHHty2 C0 eq_refl).
  - eapply TPair.
    + exact (IHHty1 C0 eq_refl).
    + exact (IHHty2 C0 eq_refl).
  - eapply TFst.
    exact (IHHty C0 eq_refl).
  - eapply TSnd.
    exact (IHHty C0 eq_refl).
  - eapply TIf.
    + exact (subsumption_has_type_pure_var_ctx (ctx_add_var C0 x t_new witness) C0 x t_old t_new witness _ (TBase BBool) (Hsub C0) H).
    + destruct (String.eq_dec u x) as [-> | Hneq].
      * rewrite ctx_add_var_shadow.
        rewrite ctx_add_var_shadow in Hty1.
        exact Hty1.
      * rewrite ctx_add_var_swap by congruence.
        apply IHHty1.
        rewrite ctx_add_var_swap by congruence.
        reflexivity.
    + destruct (String.eq_dec u x) as [-> | Hneq].
      * rewrite ctx_add_var_shadow.
        rewrite ctx_add_var_shadow in Hty2.
        exact Hty2.
      * rewrite ctx_add_var_swap by congruence.
        apply IHHty2.
        rewrite ctx_add_var_swap by congruence.
        reflexivity.
  - eapply TSelf.
    + exact (IHHty C0 eq_refl).
    + intros ty1.
      exact (subsumption_has_type_pure_var_ctx (ctx_add_var C0 x t_new witness) C0 x t_old t_new witness _ ty1 (Hsub C0) (H ty1)).
  - eapply TSub.
    + exact (IHHty C0 eq_refl).
    + exact (subsumption_subtype_var_ctx (ctx_add_var C0 x t_new witness) x t_old t_new witness (Hsub C0) C0 _ _ H).
Qed.

Lemma subsumption_ty_valid_var :
  forall G1 G2 x t_old t_new witness t1,
    subtype G1 t_new t_old ->
    ty_valid (add_ctx G2 (ctx_add_var G1 x t_old witness)) t1 ->
    ty_valid (add_ctx G2 (ctx_add_var G1 x t_new witness)) t1.
Proof.
  intros G1 G2 x t_old t_new witness t1 Hsub Hvalid.
  rewrite <- add_ctx_ctx_add_var in Hvalid |- *.
  exact (subsumption_ty_valid_var_ctx G1 x t_old t_new witness Hsub (add_ctx G2 G1) t1 Hvalid).
Qed.

(* Paper Lemma 4, subtyping clause.
   Subsuming a variable binding in Gamma preserves subtyping judgments. *)
Lemma subsumption_subtype_var :
  forall G1 G2 x t_old t_new witness t1 t2,
    subtype G1 t_new t_old ->
    subtype (add_ctx G2 (ctx_add_var G1 x t_old witness)) t1 t2 ->
    subtype (add_ctx G2 (ctx_add_var G1 x t_new witness)) t1 t2.
Proof.
  intros G1 G2 x t_old t_new witness t1 t2 Hsub Hsubtype.
  rewrite <- add_ctx_ctx_add_var in Hsubtype |- *.
  exact (subsumption_subtype_var_ctx G1 x t_old t_new witness Hsub (add_ctx G2 G1) t1 t2 Hsubtype).
Qed.

(* Paper Lemma 4, typing clause.
   Subsuming a variable binding in Gamma preserves typing judgments. *)
Lemma subsumption_has_type_var :
  forall G1 G2 x t_old t_new witness e t1,
    (forall C, subtype (ctx_add_var C x t_new witness) t_new t_old) ->
    has_type (add_ctx G2 (ctx_add_var G1 x t_old witness)) e t1 ->
    has_type (add_ctx G2 (ctx_add_var G1 x t_new witness)) e t1.
Proof.
  intros G1 G2 x t_old t_new witness e t1 Hsub Hty.
  rewrite <- add_ctx_ctx_add_var in Hty |- *.
  exact (subsumption_has_type_var_ctx x t_old t_new witness Hsub (add_ctx G2 G1) e t1 Hty).
Qed.

(* ==================== PAPER LEMMA 5 ====================
   If Gamma |- e : {x:tb | p} and e is a value, then Gamma entails p[e/x]. *)
Lemma canonical_forms_set :
  forall G e0 x tb pred,
    DTDT.machine_inter.value G e0 ->
    has_type G e0 (TBase tb) ->
    subtype G (TBase tb) (TSet x tb pred) ->
    entails G (expr_subst x e0 pred).
Proof.
  intros G e0 x tb pred Hv _ Hsub.
  inversion Hsub; subst; try discriminate.
  match goal with
  | H : entails _ _ |- _ => rename H into Hent
  end.
  assert (Hent' : entails (ctx_add_var (add_ctx empty_ctx G) x (TBase tb) (make_expr tb c)) pred).
  { rewrite add_ctx_empty_r. exact Hent. }
  eapply entails_subst_base with (witness := make_expr tb c) in Hent'; eauto.
  change (entails (add_ctx empty_ctx G) (expr_subst x e0 pred)) in Hent'.
  rewrite add_ctx_empty_r in Hent'.
  exact Hent'.
Qed.

(* ==================== PAPER LEMMA 6 ====================
   Base substitution preserves pure typing. *)
Lemma bool_prop_eq_true :
  forall b : bool,
    b -> b = true.
Proof.
  intros [] H; simpl in *; try contradiction; reflexivity.
Qed.

Lemma ty_subst_preserves_beta :
  forall x e0 t,
    essential_type_is_base_type t = true ->
    essential_type_is_base_type (ty_subst x e0 t) = true.
Proof.
  intros x e0 t Hbeta.
  destruct t; simpl in *; try discriminate; try reflexivity.
  destruct (String.eqb x s); reflexivity.
Qed.

Lemma ty_subst_preserves_essential_type :
  forall x e0 t,
    essential_type_is_base_type t = true ->
    essential_type (ty_subst x e0 t) = ty_subst x e0 (essential_type t).
Proof.
  intros x e0 t Hbeta.
  destruct t; simpl in *; try discriminate; try reflexivity.
  destruct (String.eqb x s); reflexivity.
Qed.

Lemma ty_subst_essential_type_id :
  forall x e0 t,
    essential_type_is_base_type t = true ->
    ty_subst x e0 (essential_type t) = essential_type t.
Proof.
  intros x e0 t Hbeta.
  destruct t; simpl in *; try discriminate; reflexivity.
Qed.

Lemma ty_subst_simple_id :
  forall x e0 t,
    is_simple_type t = true ->
    ty_subst x e0 t = t.
Proof.
  intros x e0 t.
  induction t; simpl; intros Hsimple; try discriminate; try reflexivity.
  - apply andb_true_iff in Hsimple as [H1 H2].
    rewrite IHt1 by exact H1.
    rewrite IHt2 by exact H2.
    reflexivity.
  - apply andb_true_iff in Hsimple as [H1 H2].
    rewrite IHt1 by exact H1.
    rewrite IHt2 by exact H2.
    reflexivity.
  - rewrite IHt by exact Hsimple.
    reflexivity.
Qed.

Lemma ctx_subst_var_binding_fixed :
  forall G x e0 y t witness,
    ctx_subst x e0 G = G ->
    G !!₁ y = Some (t, witness) ->
    ty_subst x e0 t = t /\ expr_subst x e0 witness = witness.
Proof.
  intros G x e0 y t witness Hctx Hlookup.
  destruct G as [env store].
  destruct env as [vars consts].
  unfold var_ctx_lookup in Hlookup.
  simpl in Hlookup.
  pose proof (f_equal (fun H => fst (fst H)) Hctx) as Hvars.
  simpl in Hvars.
  pose proof (f_equal (fun H => H !! y) Hvars) as Hlookup1.
  simpl in Hlookup1.
  rewrite Hlookup in Hlookup1.
  apply lookup_fmap_Some in Hlookup1.
  destruct Hlookup1 as [entry Hlookup1].
  destruct Hlookup1 as [Hmap Hentry].
  assert (Heq : entry = (t, witness)).
  { enough (Some entry = Some (t, witness)) by (inversion H; reflexivity).
    transitivity (vars !! y).
    - symmetry. exact Hentry.
    - exact Hlookup. }
  rewrite Heq in Hmap.
  unfold binding_subst in Hmap.
  simpl in Hmap.
  injection Hmap as Hty Hexpr.
  split; [exact Hty | exact Hexpr].
Qed.

Lemma ctx_subst_const_binding_fixed :
  forall G x e0 c t witness,
    ctx_subst x e0 G = G ->
    G !!₂ c = Some (t, witness) ->
    ty_subst x e0 t = t /\ expr_subst x e0 witness = witness.
Proof.
  intros G x e0 c t witness Hctx Hlookup.
  destruct G as [env store].
  destruct env as [vars consts].
  unfold const_ctx_lookup in Hlookup.
  simpl in Hlookup.
  pose proof (f_equal (fun H => snd (fst H)) Hctx) as Hconsts.
  simpl in Hconsts.
  pose proof (f_equal (fun H => H !! c) Hconsts) as Hlookup1.
  simpl in Hlookup1.
  rewrite Hlookup in Hlookup1.
  apply lookup_fmap_Some in Hlookup1.
  destruct Hlookup1 as [entry Hlookup1].
  destruct Hlookup1 as [Hmap Hentry].
  assert (Heq : entry = (t, witness)).
  { enough (Some entry = Some (t, witness)) by (inversion H; reflexivity).
    transitivity (consts !! c).
    - symmetry. exact Hentry.
    - exact Hlookup. }
  rewrite Heq in Hmap.
  unfold binding_subst in Hmap.
  simpl in Hmap.
  injection Hmap as Hty Hexpr.
  split; [exact Hty | exact Hexpr].
Qed.

Lemma lookup_lemma_var_subst_base :
  forall G1 G2 x e0 y t witness,
    ctx_subst x e0 G1 = G1 ->
    y <> x ->
    (add_ctx G2 G1) !!₁ y = Some (t, witness) ->
    (add_ctx (ctx_subst x e0 G2) G1) !!₁ y = Some (ty_subst x e0 t, expr_subst x e0 witness).
Proof.
  intros G1 G2 x e0 y t witness Hctx Hneq Hlookup.
  destruct G1 as [env1 store1].
  destruct env1 as [vars1 consts1].
  destruct G2 as [env2 store2].
  destruct env2 as [vars2 consts2].
  unfold add_ctx, ctx_subst, var_ctx_lookup, binding_subst in *.
  simpl in *.
  destruct (vars1 !! y) eqn:Hvars1.
  - destruct p as [t1 e1].
    assert (Hlookup_left : (vars1 ∪ vars2) !! y = Some (t1, e1)).
    { apply (lookup_union_Some_l vars1 vars2 y (t1, e1)).
      exact Hvars1. }
    assert (Heq : (t, witness) = (t1, e1)) by congruence.
    inversion Heq; subst t1 e1.
    destruct (ctx_subst_var_binding_fixed ((vars1, consts1), store1) x e0 y t witness Hctx Hvars1) as [Hty Hexp].
    rewrite Hty, Hexp.
    apply (lookup_union_Some_l vars1 (binding_subst x e0 <$> vars2) y (t, witness)).
    exact Hvars1.
  - assert (Hlookup2 : vars2 !! y = Some (t, witness)).
    { eapply lookup_union_Some_inv_r; eauto. }
    apply lookup_union_Some_raw.
    right.
    split.
    * exact Hvars1.
    * apply lookup_fmap_Some.
      exists (t, witness).
      split.
      { reflexivity. }
      { exact Hlookup2. }
Qed.

Lemma lookup_lemma_const_subst_base :
  forall G1 G2 x e0 c t witness,
    ctx_subst x e0 G1 = G1 ->
    (add_ctx G2 G1) !!₂ c = Some (t, witness) ->
    is_simple_type t = true ->
    (add_ctx (ctx_subst x e0 G2) G1) !!₂ c = Some (t, expr_subst x e0 witness).
Proof.
  intros G1 G2 x e0 c t witness Hctx Hlookup Hsimple.
  destruct G1 as [env1 store1].
  destruct env1 as [vars1 consts1].
  destruct G2 as [env2 store2].
  destruct env2 as [vars2 consts2].
  unfold add_ctx, ctx_subst, const_ctx_lookup, binding_subst in *.
  simpl in *.
  destruct (consts1 !! c) eqn:Hconsts1.
  - destruct p as [t1 e1].
    assert (Hlookup_left : (consts1 ∪ consts2) !! c = Some (t1, e1)).
    { apply (lookup_union_Some_l consts1 consts2 c (t1, e1)).
      exact Hconsts1. }
    assert (Heq : (t, witness) = (t1, e1)) by congruence.
    inversion Heq; subst t1 e1.
    destruct (ctx_subst_const_binding_fixed ((vars1, consts1), store1) x e0 c t witness Hctx Hconsts1) as [_ Hexp].
    rewrite Hexp.
    apply (lookup_union_Some_l consts1 (binding_subst x e0 <$> consts2) c (t, witness)).
    exact Hconsts1.
  - assert (Hlookup2 : consts2 !! c = Some (t, witness)).
    { eapply lookup_union_Some_inv_r; eauto. }
    apply lookup_union_Some_raw.
    right.
    split.
    * exact Hconsts1.
    * apply lookup_fmap_Some.
      exists (t, witness).
      split.
      { unfold binding_subst.
        simpl.
        rewrite ty_subst_simple_id by exact Hsimple.
        reflexivity. }
      { exact Hlookup2. }
Qed.

Lemma weakening_value_right :
  forall G1 G2 v,
    DTDT.machine_inter.value G1 v ->
    DTDT.machine_inter.value (add_ctx G2 G1) v.
Proof.
  intros G1 G2 v Hv.
  induction Hv.
  - apply DTDT.machine_inter.VNat.
  - apply DTDT.machine_inter.VBool.
  - apply DTDT.machine_inter.VUnit.
  - apply DTDT.machine_inter.VString.
  - eapply DTDT.machine_inter.VConst.
    exact (lookup_lemma_const_right G1 G2 c _ _ H).
  - apply DTDT.machine_inter.VFix.
  - eapply DTDT.machine_inter.VPair; eauto.
  - eapply DTDT.machine_inter.VVar.
    exact (lookup_lemma_var_right G1 G2 x _ _ H).
  - eapply DTDT.machine_inter.VLoc.
    exact (lookup_lemma_store_right G1 G2 l _ _ H).
Qed.

Lemma lookup_lemma_var_ctx_subst :
  forall C x e0 y t witness,
    var_ctx_lookup C y = Some (t, witness) ->
    var_ctx_lookup (ctx_subst x e0 C) y = Some (ty_subst x e0 t, expr_subst x e0 witness).
Proof.
  intros C x e0 y t witness Hlookup.
  destruct C as [env store].
  destruct env as [vars consts].
  unfold var_ctx_lookup, ctx_subst. simpl.
  apply lookup_fmap_Some.
  exists (t, witness).
  split; [reflexivity | exact Hlookup].
Qed.

Lemma lookup_lemma_const_ctx_subst :
  forall C x e0 c t witness,
    const_ctx_lookup C c = Some (t, witness) ->
    const_ctx_lookup (ctx_subst x e0 C) c = Some (ty_subst x e0 t, expr_subst x e0 witness).
Proof.
  intros C x e0 c t witness Hlookup.
  destruct C as [env store].
  destruct env as [vars consts].
  unfold const_ctx_lookup, ctx_subst. simpl.
  apply lookup_fmap_Some.
  exists (t, witness).
  split; [reflexivity | exact Hlookup].
Qed.

Lemma lookup_lemma_const_ctx_subst_simple :
  forall C x e0 c t witness,
    const_ctx_lookup C c = Some (t, witness) ->
    is_simple_type t = true ->
    const_ctx_lookup (ctx_subst x e0 C) c = Some (t, expr_subst x e0 witness).
Proof.
  intros C x e0 c t witness Hlookup Hsimple.
  pose proof (lookup_lemma_const_ctx_subst C x e0 c t witness Hlookup) as Hlookup'.
  rewrite ty_subst_simple_id in Hlookup' by exact Hsimple.
  exact Hlookup'.
Qed.

Lemma ctx_subst_add_ctx :
  forall G1 G2 x e0,
    ctx_subst x e0 (add_ctx G2 G1) = add_ctx (ctx_subst x e0 G2) (ctx_subst x e0 G1).
Proof.
  intros [env1 store1] [env2 store2] x e0.
  destruct env1 as [vars1 consts1].
  destruct env2 as [vars2 consts2].
  unfold ctx_subst, add_ctx. simpl.
  f_equal.
  - f_equal.
    + apply map_fmap_union.
    + apply map_fmap_union.
  - apply map_fmap_union.
Qed.

Lemma ctx_subst_ctx_add_var :
  forall C y ty witness x e0,
    ctx_subst x e0 (ctx_add_var C y ty witness) =
    ctx_add_var (ctx_subst x e0 C) y (ty_subst x e0 ty) (expr_subst x e0 witness).
Proof.
  intros [env store] y ty witness x e0.
  destruct env as [vars consts].
  unfold ctx_subst, ctx_add_var. simpl.
  f_equal.
  rewrite (fmap_insert (binding_subst x e0) vars y (ty, witness)).
  reflexivity.
Qed.


Lemma weakening_closed_has_type_pure_var :
  forall G x t witness e ty,
    free_exp_vars e = [] ->
    has_type_pure G e ty ->
    has_type_pure (ctx_add_var G x t witness) e ty.
Proof.
  intros G x t witness e ty Hclosed Hpure.
  induction Hpure.
  - simpl in Hclosed. discriminate.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst.
    + unfold const_ctx_lookup, ctx_add_var in *. simpl in *. exact H.
    + exact H0.
  - simpl in Hclosed.
    apply app_eq_nil in Hclosed as [Hc1 Hc2].
    eapply PApp.
    + exact H.
    + exact (IHHpure1 Hc1).
    + exact (IHHpure2 Hc2).
  - simpl in Hclosed. eapply PNot. exact (IHHpure Hclosed).
  - simpl in Hclosed.
    apply app_eq_nil in Hclosed as [Hc1 Hc2].
    apply PImp; [exact (IHHpure1 Hc1) | exact (IHHpure2 Hc2)].
  - simpl in Hclosed.
    apply app_eq_nil in Hclosed as [Hc1 Hc2].
    apply PAnd; [exact (IHHpure1 Hc1) | exact (IHHpure2 Hc2)].
  - simpl in Hclosed.
    apply app_eq_nil in Hclosed as [Hc1 Hc2].
    apply POr; [exact (IHHpure1 Hc1) | exact (IHHpure2 Hc2)].
  - simpl in Hclosed.
    apply app_eq_nil in Hclosed as [Hc1 Hc2].
    eapply PEq; [exact (IHHpure1 Hc1) | exact (IHHpure2 Hc2)].
  - simpl in Hclosed.
    apply app_eq_nil in Hclosed as [Hc1 Hc2].
    apply PPlus; [exact (IHHpure1 Hc1) | exact (IHHpure2 Hc2)].
Qed.

Lemma subst_base_has_type_pure_gen :
  forall C x e0 t0 e t,
    essential_type_is_base_type t0 ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    has_type_pure (ctx_add_var C x t0 e0) e t ->
    has_type_pure (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 t).
Proof.
  intros C x e0 t0 e t Hbeta0 Hpure0 Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [_ Hbind].
        inversion Hbind; subst.
        simpl.
        rewrite String.eqb_refl.
        rewrite ty_subst_essential_type_id by (apply bool_prop_eq_true; exact Hbeta0).
        exact Hpure0.
      * destruct Hcase as [Hneq' _].
        contradiction.
    + lazymatch goal with
      | |- has_type_pure _ _ (ty_subst x e0 (essential_type ?T)) =>
          replace (ty_subst x e0 (essential_type T)) with (essential_type (ty_subst x e0 T))
      end.
      * simpl.
        destruct (String.eqb x x0) eqn:Heq.
        { apply String.eqb_eq in Heq. subst x0. contradiction. }
        eapply PVar.
        -- unfold var_ctx_lookup, ctx_add_var in H.
           simpl in H.
           apply lookup_insert_Some in H.
           destruct H as [Hcase | Hcase].
           { destruct Hcase as [Heq' _].
             subst x0.
             contradiction. }
           destruct Hcase as [_ Hlookup].
           exact (lookup_lemma_var_ctx_subst C x e0 x0 _ _ Hlookup).
        -- rewrite (ty_subst_preserves_beta x e0 _ (bool_prop_eq_true _ H0)).
           exact I.
      * symmetry.
        rewrite ty_subst_preserves_essential_type by (apply bool_prop_eq_true; exact H0).
        reflexivity.
  - simpl. apply PNat.
  - simpl. apply PBool.
  - simpl. apply PString.
  - simpl. apply PUnit.
  - simpl.
    rewrite ty_subst_simple_id by (apply bool_prop_eq_true; exact H0).
    eapply PConst.
    + exact (lookup_lemma_const_ctx_subst_simple C x e0 c _ _ H (bool_prop_eq_true _ H0)).
    + exact H0.
  - simpl.
    eapply PApp.
    + rewrite (ty_subst_preserves_beta x e0 _ (bool_prop_eq_true _ H)). exact I.
    + exact IHHpure1.
    + exact IHHpure2.
  - simpl. apply PNot. exact IHHpure.
  - simpl. apply PImp; assumption.
  - simpl. apply PAnd; assumption.
  - simpl. apply POr; assumption.
  - simpl. eapply PEq; eauto.
  - simpl. apply PPlus; assumption.
Qed.

(* Paper Lemma 6, pure clause.
   Base substitution preserves pure typing. *)
Lemma subst_base_has_type_pure :
  forall G1 G2 x e0 t0 e t,
    DTDT.machine_inter.value G1 e0 ->
    β[ t0 ] ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    ctx_subst x e0 G1 = G1 ->
    has_type_pure (ctx_add_var (add_ctx G2 G1) x t0 e0) e t ->
    has_type_pure (add_ctx (ctx_subst x e0 G2) G1) (expr_subst x e0 e) (ty_subst x e0 t).
Proof.
  intros G1 G2 x e0 t0 e t Hv0 Hbeta0 Hpure0 Hty0 Hctx Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [_ Hbind].
        inversion Hbind; subst.
        simpl.
        rewrite String.eqb_refl.
        rewrite ty_subst_essential_type_id by (apply bool_prop_eq_true; exact Hbeta0).
        apply weakening_has_type_pure_right.
        exact Hpure0.
      * destruct Hcase as [Hneq' Hlookup].
        contradiction.
    + rewrite <- ty_subst_preserves_essential_type by (apply bool_prop_eq_true; exact H0).
      simpl.
      destruct (String.eqb x x0) eqn:Heq.
      * apply String.eqb_eq in Heq. subst x0. contradiction.
      * unfold var_ctx_lookup, ctx_add_var in H.
        simpl in H.
        apply lookup_insert_Some in H.
        destruct H as [Hcase | Hcase].
        { destruct Hcase as [Heq' _]. subst x0. contradiction. }
        destruct Hcase as [_ Hlookup_base].
        pose proof (lookup_lemma_var_subst_base G1 G2 x e0 x0 _ _ Hctx Hneq Hlookup_base) as Hlookup'.
        eapply PVar.
        { exact Hlookup'. }
        { rewrite (ty_subst_preserves_beta x e0 _ (bool_prop_eq_true _ H0)); exact I. }
  - simpl. apply PNat.
  - simpl. apply PBool.
  - simpl. apply PString.
  - simpl. apply PUnit.
  - simpl.
    rewrite ty_subst_simple_id by (apply bool_prop_eq_true; exact H0).
    eapply PConst.
    + eapply lookup_lemma_const_subst_base; eauto.
      apply bool_prop_eq_true. exact H0.
    + exact H0.
  - simpl.
    eapply PApp.
    + rewrite (ty_subst_preserves_beta x e0 _ (bool_prop_eq_true _ H)). exact I.
    + exact IHHpure1.
    + exact IHHpure2.
  - simpl. apply PNot. exact IHHpure.
  - simpl. apply PImp; assumption.
  - simpl. apply PAnd; assumption.
  - simpl. apply POr; assumption.
  - simpl. eapply PEq; eauto.
  - simpl. apply PPlus; assumption.
Qed.

Lemma subst_base_has_type_pure_shadow :
  forall G1 G2 x e0 t0 tb witness e t,
    DTDT.machine_inter.value G1 e0 ->
    essential_type_is_base_type t0 ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    ctx_subst x e0 G1 = G1 ->
    has_type_pure (ctx_add_var (add_ctx G2 G1) x (TBase tb) witness) e t ->
    has_type_pure (ctx_add_var (add_ctx (ctx_subst x e0 G2) G1) x (TBase tb) witness) e t.
Proof.
  intros G1 G2 x e0 t0 tb witness e t Hv0 Hbeta0 Hpure0 Hty0 Hctx Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [_ Hbind].
        inversion Hbind; subst.
        eapply PVar.
        -- unfold var_ctx_lookup, ctx_add_var.
           simpl.
           apply lookup_insert.
        -- exact H0.
      * destruct Hcase as [Hneq' _].
        contradiction.
    + lazymatch goal with
      | |- has_type_pure _ _ (essential_type ?T) =>
          replace (essential_type T) with (essential_type (ty_subst x e0 T))
      end.
      * eapply PVar.
        -- unfold var_ctx_lookup, ctx_add_var in H |- *.
           simpl in H |- *.
           apply lookup_insert_Some in H.
           destruct H as [Hcase | Hcase].
           { destruct Hcase as [Heq _].
             subst x0.
             contradiction. }
           destruct Hcase as [_ Hlookup_base].
           apply lookup_insert_Some.
           right.
           split.
           { congruence. }
           { exact (lookup_lemma_var_subst_base G1 G2 x e0 x0 _ _ Hctx Hneq Hlookup_base). }
        -- rewrite (ty_subst_preserves_beta x e0 _ (bool_prop_eq_true _ H0)).
           exact I.
      * lazymatch goal with
        | |- essential_type (ty_subst x e0 ?T) = essential_type ?T =>
            rewrite ty_subst_preserves_essential_type by (apply bool_prop_eq_true; exact H0);
            rewrite ty_subst_essential_type_id by (apply bool_prop_eq_true; exact H0);
            reflexivity
        end.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst.
    + unfold const_ctx_lookup, ctx_add_var in H |- *.
      simpl in H |- *.
      exact (lookup_lemma_const_subst_base G1 G2 x e0 c _ _ Hctx H (bool_prop_eq_true _ H0)).
    + exact H0.
  - eapply PApp; eauto.
  - apply PNot. exact IHHpure.
  - apply PImp; assumption.
  - apply PAnd; assumption.
  - apply POr; assumption.
  - eapply PEq; eauto.
  - apply PPlus; assumption.
Qed.


Lemma subst_base_has_type_pure_shadow_ctx :
  forall C x e0 t0 t_old witness e t,
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    has_type_pure (ctx_add_var C x t_old witness) e t ->
    has_type_pure (ctx_add_var (ctx_subst x e0 C) x (ty_subst x e0 t_old) witness) e t.
Proof.
  intros C x e0 t0 t_old witness e t Hbeta0 Hpure0 Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [_ Hbind].
        inversion Hbind; subst.
        lazymatch goal with
        | |- has_type_pure _ _ (essential_type ?T) =>
            replace (essential_type T) with (essential_type (ty_subst x e0 T))
        end.
        2:{
          symmetry.
          rewrite ty_subst_preserves_essential_type by (apply bool_prop_eq_true; exact H0).
          rewrite ty_subst_essential_type_id by (apply bool_prop_eq_true; exact H0).
          reflexivity.
        }
        eapply PVar.
        -- unfold var_ctx_lookup, ctx_add_var.
           simpl.
           apply lookup_insert.
        -- rewrite ty_subst_preserves_beta by (apply bool_prop_eq_true; exact H0).
           exact I.
      * destruct Hcase as [Hneq' _].
        contradiction.
    + lazymatch goal with
      | |- has_type_pure _ _ (essential_type ?T) =>
          replace (essential_type T) with (essential_type (ty_subst x e0 T))
      end.
      2:{
        symmetry.
        rewrite ty_subst_preserves_essential_type by (apply bool_prop_eq_true; exact H0).
        rewrite ty_subst_essential_type_id by (apply bool_prop_eq_true; exact H0).
        reflexivity.
      }
      eapply PVar with (e := expr_subst x e0 e).
      * unfold var_ctx_lookup, ctx_add_var in H |- *.
        simpl in H |- *.
        apply lookup_insert_Some in H.
        destruct H as [Hcase | Hcase].
        { destruct Hcase as [Heq _]. subst x0. contradiction. }
        destruct Hcase as [_ Hlookup].
        apply lookup_insert_Some.
        right.
        split.
        -- congruence.
        -- exact (lookup_lemma_var_ctx_subst C x e0 x0 _ _ Hlookup).
      * rewrite ty_subst_preserves_beta by (apply bool_prop_eq_true; exact H0).
        exact I.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst.
    + unfold const_ctx_lookup, ctx_add_var in H |- *.
      simpl in H |- *.
      exact (lookup_lemma_const_ctx_subst_simple C x e0 c _ _ H (bool_prop_eq_true _ H0)).
    + exact H0.
  - eapply PApp.
    + exact H.
    + exact IHHpure1.
    + exact IHHpure2.
  - apply PNot. exact IHHpure.
  - apply PImp; assumption.
  - apply PAnd; assumption.
  - apply POr; assumption.
  - eapply PEq; eauto.
  - apply PPlus; assumption.
Qed.



Lemma subst_base_ty_valid_ctx :
  forall C x e0 t0 t,
    β[ t0 ] ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    ty_valid (ctx_add_var C x t0 e0) t ->
    ty_valid (ctx_subst x e0 C) (ty_subst x e0 t).
Admitted.

(* Paper Lemma 6, validity clause.
   Base substitution preserves type validity. *)
Lemma subst_base_ty_valid :
  forall G1 G2 x e0 t0 t,
    DTDT.machine_inter.value G1 e0 ->
    β[ t0 ] ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    ctx_subst x e0 G1 = G1 ->
    free_exp_vars e0 = [] ->
    ty_valid (ctx_add_var (add_ctx G2 G1) x t0 e0) t ->
    ty_valid (add_ctx (ctx_subst x e0 G2) G1) (ty_subst x e0 t).
Proof.
  intros G1 G2 x e0 t0 t Hv0 Hbeta0 Hpure0 Hty0 Hctx Hclosed Hvalid.
  assert (Hpure_ctx : has_type_pure (ctx_subst x e0 (add_ctx G2 G1)) e0 (essential_type t0)).
  { rewrite ctx_subst_add_ctx.
    rewrite Hctx.
    apply weakening_has_type_pure_right.
    exact Hpure0. }
  pose proof (subst_base_ty_valid_ctx (add_ctx G2 G1) x e0 t0 t Hbeta0 Hpure_ctx Hclosed Hvalid) as Hvalid'.
  rewrite ctx_subst_add_ctx in Hvalid'.
  rewrite Hctx in Hvalid'.
  exact Hvalid'.
Qed.

Lemma subst_base_subtype_ctx :
  forall C x e0 t0 t1 t2,
    β[ t0 ] ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    subtype (ctx_add_var C x t0 e0) t1 t2 ->
    subtype (ctx_subst x e0 C) (ty_subst x e0 t1) (ty_subst x e0 t2).
Admitted.

(* Paper Lemma 6, subtyping clause.
   Base substitution preserves subtyping. *)
Lemma subst_base_subtype :
  forall G1 G2 x e0 t0 t1 t2,
    DTDT.machine_inter.value G1 e0 ->
    β[ t0 ] ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    ctx_subst x e0 G1 = G1 ->
    free_exp_vars e0 = [] ->
    subtype (ctx_add_var (add_ctx G2 G1) x t0 e0) t1 t2 ->
    subtype (add_ctx (ctx_subst x e0 G2) G1) (ty_subst x e0 t1) (ty_subst x e0 t2).
Proof.
  intros G1 G2 x e0 t0 t1 t2 Hv0 Hbeta0 Hpure0 Hty0 Hctx Hclosed Hsub.
  assert (Hpure_ctx : has_type_pure (ctx_subst x e0 (add_ctx G2 G1)) e0 (essential_type t0)).
  { rewrite ctx_subst_add_ctx.
    rewrite Hctx.
    apply weakening_has_type_pure_right.
    exact Hpure0. }
  pose proof (subst_base_subtype_ctx (add_ctx G2 G1) x e0 t0 t1 t2 Hbeta0 Hpure_ctx Hclosed Hsub) as Hsub'.
  rewrite ctx_subst_add_ctx in Hsub'.
  rewrite Hctx in Hsub'.
  exact Hsub'.
Qed.

(* Paper Lemma 6, selfification bridge.
   Base substitution commutes with the selfification step used by typing. *)
Lemma subst_base_self_subtype_ctx :
  forall C x e0 t0 e t,
    β[ t0 ] ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var C x t0 e0) e t ->
    subtype (ctx_subst x e0 C)
      (self (ty_subst x e0 t) (expr_subst x e0 e))
      (ty_subst x e0 (self t e)).
Admitted.

Lemma subst_base_self_subtype :
  forall G1 G2 x e0 t0 e t,
    DTDT.machine_inter.value G1 e0 ->
    β[ t0 ] ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    ctx_subst x e0 G1 = G1 ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var (add_ctx G2 G1) x t0 e0) e t ->
    subtype (add_ctx (ctx_subst x e0 G2) G1)
      (self (ty_subst x e0 t) (expr_subst x e0 e))
      (ty_subst x e0 (self t e)).
Proof.
  intros G1 G2 x e0 t0 e t Hv0 Hbeta0 Hpure0 Hty0 Hctx Hclosed Hty.
  assert (Hpure_ctx : has_type_pure (ctx_subst x e0 (add_ctx G2 G1)) e0 (essential_type t0)).
  { rewrite ctx_subst_add_ctx.
    rewrite Hctx.
    apply weakening_has_type_pure_right.
    exact Hpure0. }
  pose proof (subst_base_self_subtype_ctx (add_ctx G2 G1) x e0 t0 e t Hbeta0 Hpure_ctx Hclosed Hty) as Hsub.
  rewrite ctx_subst_add_ctx in Hsub.
  rewrite Hctx in Hsub.
  exact Hsub.
Qed.

(* Paper Lemma 6, typing clause.
   Base substitution preserves typing. *)
Lemma subst_base_has_type_ctx :
  forall C x e0 t0 e t,
    β[ t0 ] ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var C x t0 e0) e t ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 t).
Admitted.

Lemma subst_base_has_type :
  forall G1 G2 x e0 t0 e t,
    DTDT.machine_inter.value G1 e0 ->
    β[ t0 ] ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    ctx_subst x e0 G1 = G1 ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var (add_ctx G2 G1) x t0 e0) e t ->
    has_type (add_ctx (ctx_subst x e0 G2) G1) (expr_subst x e0 e) (ty_subst x e0 t).
Proof.
  intros G1 G2 x e0 t0 e t Hv0 Hbeta0 Hpure0 Hty0 Hctx Hclosed Hty.
  assert (Hpure_ctx : has_type_pure (ctx_subst x e0 (add_ctx G2 G1)) e0 (essential_type t0)).
  { rewrite ctx_subst_add_ctx.
    rewrite Hctx.
    apply weakening_has_type_pure_right.
    exact Hpure0. }
  pose proof (subst_base_has_type_ctx (add_ctx G2 G1) x e0 t0 e t Hbeta0 Hpure_ctx Hclosed Hty) as Hty'.
  rewrite ctx_subst_add_ctx in Hty'.
  rewrite Hctx in Hty'.
  exact Hty'.
Qed.

(* ==================== PAPER LEMMA 7 ====================
   Non-base substitution preserves typing judgments. *)
Lemma subst_nonbase_has_type_pure :
  forall G1 G2 x v t0 e t,
    essential_type_is_base_type t0 = false ->
    has_type_pure (ctx_add_var (add_ctx G2 G1) x t0 v) e t ->
    has_type_pure (add_ctx G2 G1) (expr_subst x v e) t.
Proof.
  intros G1 G2 x v t0 e t Hnb Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [_ Hbind].
        inversion Hbind; subst.
        pose proof (bool_prop_eq_true _ H0) as Hbt.
        rewrite Hnb in Hbt.
        discriminate.
      * destruct Hcase as [Hneq' _].
        contradiction.
    + simpl.
      destruct (String.eqb x x0) eqn:Heq.
      * apply String.eqb_eq in Heq. subst x0. contradiction.
      * eapply PVar.
        -- eapply lookup_lemma_var_added_ne; eauto.
        -- exact H0.
  - simpl. apply PNat.
  - simpl. apply PBool.
  - simpl. apply PString.
  - simpl. apply PUnit.
  - simpl. eapply PConst; eauto.
  - simpl. eapply PApp; eauto.
  - simpl. apply PNot. exact IHHpure.
  - simpl. apply PImp; assumption.
  - simpl. apply PAnd; assumption.
  - simpl. apply POr; assumption.
  - simpl. eapply PEq; eauto.
  - simpl. apply PPlus; assumption.
Qed.

Lemma subst_nonbase_pure_id :
  forall C x v t0 e t,
    essential_type_is_base_type t0 = false ->
    has_type_pure (ctx_add_var C x t0 v) e t ->
    expr_subst x v e = e.
Proof.
  intros C x v t0 e t Hnb Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [_ Hbind].
        inversion Hbind; subst.
        pose proof (bool_prop_eq_true _ H0) as Hbt.
        rewrite Hnb in Hbt.
        discriminate.
      * destruct Hcase as [Hneq' _].
        contradiction.
    + simpl.
      destruct (String.eqb x x0) eqn:Heq.
      * apply String.eqb_eq in Heq. subst x0. contradiction.
      * reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHHpure1, IHHpure2; reflexivity.
  - simpl. rewrite IHHpure; reflexivity.
  - simpl. rewrite IHHpure1, IHHpure2; reflexivity.
  - simpl. rewrite IHHpure1, IHHpure2; reflexivity.
  - simpl. rewrite IHHpure1, IHHpure2; reflexivity.
  - simpl. rewrite IHHpure1, IHHpure2; reflexivity.
  - simpl. rewrite IHHpure1, IHHpure2; reflexivity.
Qed.

Lemma subst_nonbase_has_type_pure_ctx :
  forall C x v t0 e t,
    essential_type_is_base_type t0 = false ->
    has_type_pure (ctx_add_var C x t0 v) e t ->
    has_type_pure C (expr_subst x v e) t.
Proof.
  intros C x v t0 e t Hnb Hpure.
  rewrite <- (add_ctx_empty_r C) in Hpure |- *.
  exact (subst_nonbase_has_type_pure C empty_ctx x v t0 e t Hnb Hpure).
Qed.

Lemma subst_nonbase_ty_valid_ctx :
  forall x v t0,
    essential_type_is_base_type t0 = false ->
    forall C t,
      ty_valid (ctx_add_var C x t0 v) t ->
      ty_valid C t.
Proof.
  intros x v t0 Hnb.
  fix IH 3.
  intros C t Hvalid.
  destruct Hvalid as
    [tb
    | var tb e witness Hp
    | t1 t2 Hv1 Hv2
    | var t1 t2 witness Hv1 Hv2
    | t1 t2 Hv1 Hv2
    | t Hv].
  - apply VBase.
  - destruct (String.eq_dec var x) as [-> | Hneq].
    + eapply VSet.
      rewrite ctx_add_var_shadow in Hp.
      exact Hp.
    + eapply VSet.
      rewrite ctx_add_var_swap in Hp by congruence.
      pose proof (subst_nonbase_has_type_pure_ctx
        (ctx_add_var C var (TBase tb) witness) x v t0 e (TBase BBool) Hnb Hp) as Hp'.
      rewrite (subst_nonbase_pure_id
        (ctx_add_var C var (TBase tb) witness) x v t0 e (TBase BBool) Hnb Hp) in Hp'.
      exact Hp'.
  - apply VFun.
    + exact (IH C _ Hv1).
    + exact (IH C _ Hv2).
  - destruct (String.eq_dec var x) as [-> | Hneq].
    + eapply VFunDep.
      * exact (IH C _ Hv1).
      * rewrite ctx_add_var_shadow in Hv2.
        exact Hv2.
    + eapply VFunDep.
      * exact (IH C _ Hv1).
      * rewrite ctx_add_var_swap in Hv2 by congruence.
        exact (IH (ctx_add_var C var t1 witness) _ Hv2).
  - apply VPair.
    + exact (IH C _ Hv1).
    + exact (IH C _ Hv2).
  - apply VRef.
    exact (IH C _ Hv).
Qed.

Lemma subst_nonbase_ty_valid :
  forall G1 G2 x v t0 t,
    essential_type_is_base_type t0 = false ->
    ty_valid (ctx_add_var (add_ctx G2 G1) x t0 v) t ->
    ty_valid (add_ctx G2 G1) t.
Proof.
  intros G1 G2 x v t0 t Hnb Hvalid.
  exact (subst_nonbase_ty_valid_ctx x v t0 Hnb (add_ctx G2 G1) t Hvalid).
Qed.

Lemma has_type_pure_change_var_witness :
  forall (C : ctx) (y : string) (t : i_ty) (w_old w_new e : i_expr) (ty : i_ty),
    has_type_pure (ctx_add_var C y t w_old) e ty ->
    has_type_pure (ctx_add_var C y t w_new) e ty.
Proof.
  intros C y t w_old w_new e ty Hpure.
  induction Hpure as
    [x tyb e0 Hlookup Hbeta
    | n
    | b
    | s
    | u
    | c tyc ec Hlookupc Hsimple
    | e1 e2 t1 t2 Hbeta1 Hty1 IH1 Hty2 IH2
    | b Hty IH
    | b1 b2 Hty1 IH1 Hty2 IH2
    | b1 b2 Hty1 IH1 Hty2 IH2
    | b1 b2 Hty1 IH1 Hty2 IH2
    | e1 e2 tb Hty1 IH1 Hty2 IH2
    | n1 n2 Hty1 IH1 Hty2 IH2].
  - destruct (String.eq_dec x y) as [Heq | Hneq].
    + subst x.
      unfold var_ctx_lookup, ctx_add_var in Hlookup. simpl in Hlookup.
      apply lookup_insert_Some in Hlookup.
      destruct Hlookup as [Hcase | Hcase].
      * destruct Hcase as [_ Hentry].
        assert (Hbeta_t : Is_true (essential_type_is_base_type t)).
        { pose proof (bool_prop_eq_true _ Hbeta) as Hbeta_eq.
          inversion Hentry; subst.
          rewrite Hbeta_eq.
          exact I. }
        assert (Ht : t = tyb).
        { inversion Hentry; reflexivity. }
        assert (Hlookup_new : var_ctx_lookup (ctx_add_var C y t w_new) y = Some (t, w_new)).
        { unfold var_ctx_lookup, ctx_add_var. simpl. apply lookup_insert. }
        rewrite <- Ht.
        exact (@PVar (ctx_add_var C y t w_new) y t w_new Hlookup_new Hbeta_t).
      * destruct Hcase as [Hneq' _].
        contradiction.
    + assert (Hlookup_new : var_ctx_lookup (ctx_add_var C y t w_new) x = Some (tyb, e0)).
      { unfold var_ctx_lookup, ctx_add_var in *. simpl in *.
        assert (Hyx : y <> x) by congruence.
        rewrite (lookup_insert_ne (fst (fst C)) y x (t, w_new) Hyx).
        rewrite (lookup_insert_ne (fst (fst C)) y x (t, w_old) Hyx) in Hlookup.
        exact Hlookup. }
      exact (@PVar (ctx_add_var C y t w_new) x tyb e0 Hlookup_new Hbeta).
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst; eauto.
  - eapply PApp; eauto.
  - eapply PNot; eauto.
  - eapply PImp; eauto.
  - eapply PAnd; eauto.
  - eapply POr; eauto.
  - eapply PEq; eauto.
  - eapply PPlus; eauto.
Qed.

Lemma ty_valid_set_pred :
  forall C var tb e w,
    ty_valid C (TSet var tb e) ->
    has_type_pure (ctx_add_var C var (TBase tb) w) e (TBase BBool).
Proof.
  intros C var tb e w Hvalid.
  inversion Hvalid; subst; clear Hvalid.
  match goal with
  | Hp : has_type_pure (ctx_add_var C var (TBase tb) ?w_old) e (TBase BBool) |- _ =>
      exact (has_type_pure_change_var_witness C var (TBase tb) w_old w e (TBase BBool) Hp)
  end.
Qed.

Lemma subst_nonbase_entails_ctx :
  forall C x v t0 e,
    essential_type_is_base_type t0 = false ->
    has_type_pure (ctx_add_var C x t0 v) e (TBase BBool) ->
    entails (ctx_add_var C x t0 v) e ->
    entails C e.
Proof.
  intros C x v t0 e Hnb Hpure Hent.
  pose proof (subst_nonbase_pure_id C x v t0 e (TBase BBool) Hnb Hpure) as Hid.
  assert (Hent' : entails (ctx_add_var (add_ctx empty_ctx C) x t0 v) e).
  { rewrite add_ctx_empty_r. exact Hent. }
  pose proof (entails_drop_unused C empty_ctx x t0 v e Hent' eq_refl Hid) as Hdrop.
  rewrite add_ctx_empty_r in Hdrop.
  exact Hdrop.
Qed.

Lemma subst_nonbase_subtype_ctx :
  forall x v t0,
    essential_type_is_base_type t0 = false ->
    forall C t1 t2,
      subtype (ctx_add_var C x t0 v) t1 t2 ->
      subtype C t1 t2.
Proof.
  intros x v t0 Hnb.
  fix IH 4.
  intros C t1 t2 Hsub.
  destruct Hsub as
    [b
    | var tb e1 e2 c Hv1 Hv2 Hent
    | var tb e Hv
    | var tb e c Hv Hent
    | t_dom t_dom' t_cod t_cod' Hs1 Hs2
    | var t_dom t_dom' t_cod t_cod' w Hs1 Hs2
    | t1a t1b t2a t2b Hs1 Hs2
    | t_left t_right Hs1 Hs2].
  - apply SBase.
  - eapply SSet.
    + exact (subst_nonbase_ty_valid_ctx x v t0 Hnb C _ Hv1).
    + exact (subst_nonbase_ty_valid_ctx x v t0 Hnb C _ Hv2).
    + destruct (String.eq_dec var x) as [-> | Hneq].
      * rewrite ctx_add_var_shadow in Hent.
        exact Hent.
      * rewrite ctx_add_var_swap in Hent by congruence.
        eapply subst_nonbase_entails_ctx.
        -- exact Hnb.
        -- apply PImp.
           ++ pose proof (ty_valid_set_pred (ctx_add_var C x t0 v) var tb e1 (make_expr tb c) Hv1) as Hp1.
              rewrite ctx_add_var_swap in Hp1 by congruence.
              exact Hp1.
           ++ pose proof (ty_valid_set_pred (ctx_add_var C x t0 v) var tb e2 (make_expr tb c) Hv2) as Hp2.
              rewrite ctx_add_var_swap in Hp2 by congruence.
              exact Hp2.
        -- exact Hent.
  - eapply SSetBase.
    exact (subst_nonbase_ty_valid_ctx x v t0 Hnb C _ Hv).
  - eapply SBaseSet.
    + exact (subst_nonbase_ty_valid_ctx x v t0 Hnb C _ Hv).
    + destruct (String.eq_dec var x) as [-> | Hneq].
      * rewrite ctx_add_var_shadow in Hent.
        exact Hent.
      * rewrite ctx_add_var_swap in Hent by congruence.
        eapply subst_nonbase_entails_ctx.
        -- exact Hnb.
        -- pose proof (ty_valid_set_pred (ctx_add_var C x t0 v) var tb e (make_expr tb c) Hv) as Hp.
           rewrite ctx_add_var_swap in Hp by congruence.
           exact Hp.
        -- exact Hent.
  - eapply SFun.
    + exact (IH C _ _ Hs1).
    + exact (IH C _ _ Hs2).
  - eapply SFunDep.
    + exact (IH C _ _ Hs1).
    + destruct (String.eq_dec var x) as [-> | Hneq].
      * rewrite ctx_add_var_shadow in Hs2.
        exact Hs2.
      * rewrite ctx_add_var_swap in Hs2 by congruence.
        exact (IH (ctx_add_var C var t_dom' w) _ _ Hs2).
  - eapply SPair.
    + exact (IH C _ _ Hs1).
    + exact (IH C _ _ Hs2).
  - eapply SRef.
    + exact (IH C _ _ Hs1).
    + exact (IH C _ _ Hs2).
Qed.

Lemma subst_nonbase_subtype :
  forall G1 G2 x v t0 t1 t2,
    essential_type_is_base_type t0 = false ->
    subtype (ctx_add_var (add_ctx G2 G1) x t0 v) t1 t2 ->
    subtype (add_ctx G2 G1) t1 t2.
Proof.
  intros G1 G2 x v t0 t1 t2 Hnb Hsub.
  exact (subst_nonbase_subtype_ctx x v t0 Hnb (add_ctx G2 G1) t1 t2 Hsub).
Qed.

Inductive no_if_binder_shadow (x : string) :
  forall G e t, has_type G e t -> Prop :=
| NString :
    forall G s,
      no_if_binder_shadow x _ _ _ (TString G s)
| NNat :
    forall G n,
      no_if_binder_shadow x _ _ _ (TNat G n)
| NBool :
    forall G b,
      no_if_binder_shadow x _ _ _ (TBool G b)
| NUnit :
    forall G u,
      no_if_binder_shadow x _ _ _ (TUnit G u)
| NConst :
    forall G c t e Hlookup,
      no_if_binder_shadow x _ _ _ (TConst G c t e Hlookup)
| NVar :
    forall G v t e Hlookup,
      no_if_binder_shadow x _ _ _ (TVar G v t e Hlookup)
| NEssentialVar :
    forall G v t e Hlookup Hbeta,
      no_if_binder_shadow x _ _ _ (TEssentialVar G v t e Hlookup Hbeta)
| NLoc :
    forall G l t v Hlookup,
      no_if_binder_shadow x _ _ _ (TLoc G l t v Hlookup)
| NFail :
    forall G t Hvalid,
      no_if_binder_shadow x _ _ _ (TFail G t Hvalid)
| NFun :
    forall G f y t1 t2 body Hvalid Hbody,
      no_if_binder_shadow x _ _ _ Hbody ->
      no_if_binder_shadow x _ _ _ (TFun G f y t1 t2 body Hvalid Hbody)
| NAppPure :
    forall G e1 e2 y t1 t2 Harg Hpure Hfun,
      no_if_binder_shadow x _ _ _ Harg ->
      no_if_binder_shadow x _ _ _ Hfun ->
      no_if_binder_shadow x _ _ _ (TAppPure G e1 e2 y t1 t2 Harg Hpure Hfun)
| NAppImPure :
    forall G e1 e2 t1 t2 Harg Hfun,
      no_if_binder_shadow x _ _ _ Harg ->
      no_if_binder_shadow x _ _ _ Hfun ->
      no_if_binder_shadow x _ _ _ (TAppImPure G e1 e2 t1 t2 Harg Hfun)
| NPlus :
    forall G e1 e2 Hty1 Hty2,
      no_if_binder_shadow x _ _ _ Hty1 ->
      no_if_binder_shadow x _ _ _ Hty2 ->
      no_if_binder_shadow x _ _ _ (TPlus G e1 e2 Hty1 Hty2)
| NNot :
    forall G e Hty,
      no_if_binder_shadow x _ _ _ Hty ->
      no_if_binder_shadow x _ _ _ (TNot G e Hty)
| NImp :
    forall G e1 e2 Hty1 Hty2,
      no_if_binder_shadow x _ _ _ Hty1 ->
      no_if_binder_shadow x _ _ _ Hty2 ->
      no_if_binder_shadow x _ _ _ (TImp G e1 e2 Hty1 Hty2)
| NAnd :
    forall G e1 e2 Hty1 Hty2,
      no_if_binder_shadow x _ _ _ Hty1 ->
      no_if_binder_shadow x _ _ _ Hty2 ->
      no_if_binder_shadow x _ _ _ (TAnd G e1 e2 Hty1 Hty2)
| NOr :
    forall G e1 e2 Hty1 Hty2,
      no_if_binder_shadow x _ _ _ Hty1 ->
      no_if_binder_shadow x _ _ _ Hty2 ->
      no_if_binder_shadow x _ _ _ (TOr G e1 e2 Hty1 Hty2)
| NEq :
    forall G e1 e2 tb Hty1 Hty2,
      no_if_binder_shadow x _ _ _ Hty1 ->
      no_if_binder_shadow x _ _ _ Hty2 ->
      no_if_binder_shadow x _ _ _ (TEq G e1 e2 tb Hty1 Hty2)
| NRefI :
    forall G t e Hvalid Hty,
      no_if_binder_shadow x _ _ _ Hty ->
      no_if_binder_shadow x _ _ _ (TRefI G t e Hvalid Hty)
| NGet :
    forall G e t Hty,
      no_if_binder_shadow x _ _ _ Hty ->
      no_if_binder_shadow x _ _ _ (TGet G e t Hty)
| NSetI :
    forall G e1 e2 t Hty1 Hty2,
      no_if_binder_shadow x _ _ _ Hty1 ->
      no_if_binder_shadow x _ _ _ Hty2 ->
      no_if_binder_shadow x _ _ _ (TSetI G e1 e2 t Hty1 Hty2)
| NPair :
    forall G e1 e2 t1 t2 Hty1 Hty2,
      no_if_binder_shadow x _ _ _ Hty1 ->
      no_if_binder_shadow x _ _ _ Hty2 ->
      no_if_binder_shadow x _ _ _ (TPair G e1 e2 t1 t2 Hty1 Hty2)
| NFst :
    forall G e t1 t2 Hty,
      no_if_binder_shadow x _ _ _ Hty ->
      no_if_binder_shadow x _ _ _ (TFst G e t1 t2 Hty)
| NSnd :
    forall G e t1 t2 Hty,
      no_if_binder_shadow x _ _ _ Hty ->
      no_if_binder_shadow x _ _ _ (TSnd G e t1 t2 Hty)
| NIf :
    forall G e e1 e2 t u Hpure Hty1 Hty2,
      u <> x ->
      no_if_binder_shadow x _ _ _ Hty1 ->
      no_if_binder_shadow x _ _ _ Hty2 ->
      no_if_binder_shadow x _ _ _ (TIf G e e1 e2 t u Hpure Hty1 Hty2)
| NSelf :
    forall G e t Hty Hpure,
      no_if_binder_shadow x _ _ _ Hty ->
      no_if_binder_shadow x _ _ _ (TSelf G e t Hty Hpure)
| NSub :
    forall G e t t' Hty Hsub,
      no_if_binder_shadow x _ _ _ Hty ->
      no_if_binder_shadow x _ _ _ (TSub G e t t' Hty Hsub).

Lemma has_type_pure_empty_ctx_base :
  forall e t,
    has_type_pure empty_ctx e t ->
    β[ t ].
Proof.
  intros e t Hpure.
  induction Hpure.
  - unfold var_ctx_lookup, empty_ctx in H.
    simpl in H.
    discriminate.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - unfold const_ctx_lookup, empty_ctx in H.
    simpl in H.
    discriminate.
  - simpl in IHHpure1.
    contradiction.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
Qed.

Lemma has_type_pure_empty_ctx_app_absurd :
  forall e1 e2 t,
    has_type_pure empty_ctx (EApp e1 e2) t ->
    False.
Proof.
  intros e1 e2 t Hpure.
  inversion Hpure; subst.
  match goal with
  | Hfun : has_type_pure empty_ctx _ (TArr _ _) |- _ =>
      pose proof (has_type_pure_empty_ctx_base _ _ Hfun) as Hbase;
      simpl in Hbase;
      contradiction
  end.
Qed.

Lemma subst_nonbase_has_type :
  forall G1 G2 x v t0 e t,
    essential_type_is_base_type t0 = false ->
    has_type_pure empty_ctx v t0 ->
    forall Hty : has_type (ctx_add_var (add_ctx G2 G1) x t0 v) e t,
      no_if_binder_shadow x _ _ _ Hty ->
      has_type (add_ctx G2 G1) (expr_subst x v e) t.
Proof.
  intros G1 G2 x v t0 e t Hnb Hpure Hty _.
  pose proof (has_type_pure_empty_ctx_base v t0 Hpure) as Hbase.
  pose proof (bool_prop_eq_true _ Hbase) as Hbase_eq.
  rewrite Hnb in Hbase_eq.
  discriminate.
Qed.

Lemma subtype_refl :
  forall G t,
    ty_valid G t ->
    subtype G t t.
Proof.
  intros G t Hvalid.
  induction Hvalid.
  - apply SBase.
  - destruct τb.
    + eapply SSet with (c := EmptyString).
      * eapply VSet. exact H.
      * eapply VSet. exact H.
      * apply entails_imp_refl.
    + eapply SSet with (c := true).
      * eapply VSet. exact H.
      * eapply VSet. exact H.
      * apply entails_imp_refl.
    + eapply SSet with (c := 0).
      * eapply VSet. exact H.
      * eapply VSet. exact H.
      * apply entails_imp_refl.
    + eapply SSet with (c := tt).
      * eapply VSet. exact H.
      * eapply VSet. exact H.
      * apply entails_imp_refl.
  - apply SFun; assumption.
  - eapply SFunDep.
    + exact IHHvalid1.
    + exact IHHvalid2.
  - apply SPair; assumption.
  - eapply SRef.
    + exact IHHvalid.
    + exact IHHvalid.
Qed.

Lemma inversion_fix :
  forall G f x t1 t2 body t,
    has_type G (EFix f x t1 t2 body) t ->
    has_type G (EFix f x t1 t2 body) (TArrDep x t1 t2) /\
    has_type
      (ctx_add_var
        (ctx_add_const G f (TArrDep x t1 t2) (EFix f x t1 t2 body))
        x t1 (EVar x))
      body t2.
Proof.
  intros G f x t1 t2 body t Hty.
  remember (EFix f x t1 t2 body) as ef eqn:Heqef.
  revert f x t1 t2 body Heqef.
  induction Hty; intros f0 x0 t10 t20 body0 Heqef; inversion Heqef; subst; try discriminate.
  - split.
    + eapply TFun; eauto.
    + exact Hty.
  - exact (IHHty _ _ _ _ _ eq_refl).
  - exact (IHHty _ _ _ _ _ eq_refl).
Qed.

Lemma inversion_pair :
  forall G e1 e2 t1 t2,
    has_type G (EPair e1 e2) (TProd t1 t2) ->
    has_type G e1 t1 /\ has_type G e2 t2.
Proof.
  intros G e1 e2 t1 t2 Hty.
  remember (EPair e1 e2) as ep eqn:Heqep.
  remember (TProd t1 t2) as tp eqn:Heqtp.
  revert e1 e2 t1 t2 Heqep Heqtp.
  induction Hty; intros e1' e2' t1' t2' Heqep Heqtp; inversion Heqep; subst; try discriminate.
  - inversion Heqtp; subst.
    split; assumption.
  - apply self_pair_inv in Heqtp.
    inversion Heqtp; subst.
    exact (IHHty _ _ _ _ eq_refl eq_refl).
  - inversion H; subst; try discriminate.
    specialize (IHHty _ _ _ _ eq_refl eq_refl) as [Hleft Hright].
    split; eapply TSub; eauto.
Qed.


(* ==================== PAPER LEMMA 10 ====================
   Step lemmas relating one machine step to preservation side conditions. *)
Lemma eval_trans :
  forall sigma1 sigma2 sigma3,
    eval sigma1 sigma2 ->
    eval sigma2 sigma3 ->
    eval sigma1 sigma3.
Proof.
  intros sigma1 sigma2 sigma3 Heval12 Heval23.
  induction Heval12.
  - exact Heval23.
  - eapply steps_step.
    + exact H.
    + exact (IHHeval12 Heval23).
Qed.

Lemma eval_plug :
  forall E sigma1 sigma2,
    eval sigma1 sigma2 ->
    eval (fst sigma1, plug E (snd sigma1)) (fst sigma2, plug E (snd sigma2)).
Proof.
  intros E sigma1 sigma2 Heval.
  induction Heval as [sigma | sigma1 sigma2 sigma3 Hstep Heval23 IH].
  - destruct sigma as [G e].
    apply steps_refl.
  - destruct sigma1 as [G1 e1].
    destruct sigma2 as [G2 e2].
    destruct sigma3 as [G3 e3].
    simpl in *.
    eapply steps_step.
    + eapply StepCtx.
      exact Hstep.
    + exact IH.
Qed.

Lemma pure_subst_step_eval :
  forall G x e e' pred t,
    step (G, e) (G, e') ->
    has_type_pure (ctx_add_var G x t e) pred (TBase BBool) ->
    eval (G, expr_subst x e pred) (G, expr_subst x e' pred).
Proof.
  intros G x e e' pred t Hstep Hpure.
  induction Hpure; simpl.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + destruct (String.eqb_spec x x) as [_ | Hcontra].
      * eapply steps_step.
        -- exact Hstep.
        -- apply steps_refl.
      * contradiction.
    + destruct (String.eqb_spec x x0) as [Heq | _].
      * congruence.
      * apply steps_refl.
  - apply steps_refl.
  - apply steps_refl.
  - apply steps_refl.
  - apply steps_refl.
  - apply steps_refl.
  - lazymatch goal with
    | |- eval (G, EApp ?l1 ?r1) (G, EApp ?l2 ?r2) =>
        eapply eval_trans with (sigma2 := (G, EApp l2 r1));
        [ exact (eval_plug (ECAppL ECHole r1) (G, l1) (G, l2) IHHpure1)
        | exact (eval_plug (ECAppR l2 ECHole) (G, r1) (G, r2) IHHpure2) ]
    end.
  - exact (eval_plug (ECNot ECHole) (G, expr_subst x e b) (G, expr_subst x e' b) IHHpure).
  - lazymatch goal with
    | |- eval (G, EImp ?l1 ?r1) (G, EImp ?l2 ?r2) =>
        eapply eval_trans with (sigma2 := (G, EImp l2 r1));
        [ exact (eval_plug (ECImpL ECHole r1) (G, l1) (G, l2) IHHpure1)
        | exact (eval_plug (ECImpR l2 ECHole) (G, r1) (G, r2) IHHpure2) ]
    end.
  - lazymatch goal with
    | |- eval (G, EAnd ?l1 ?r1) (G, EAnd ?l2 ?r2) =>
        eapply eval_trans with (sigma2 := (G, EAnd l2 r1));
        [ exact (eval_plug (ECAndL ECHole r1) (G, l1) (G, l2) IHHpure1)
        | exact (eval_plug (ECAndR l2 ECHole) (G, r1) (G, r2) IHHpure2) ]
    end.
  - lazymatch goal with
    | |- eval (G, EOr ?l1 ?r1) (G, EOr ?l2 ?r2) =>
        eapply eval_trans with (sigma2 := (G, EOr l2 r1));
        [ exact (eval_plug (ECOrL ECHole r1) (G, l1) (G, l2) IHHpure1)
        | exact (eval_plug (ECOrR l2 ECHole) (G, r1) (G, r2) IHHpure2) ]
    end.
  - lazymatch goal with
    | |- eval (G, EEq ?l1 ?r1) (G, EEq ?l2 ?r2) =>
        eapply eval_trans with (sigma2 := (G, EEq l2 r1));
        [ exact (eval_plug (ECEqL ECHole r1) (G, l1) (G, l2) IHHpure1)
        | exact (eval_plug (ECEqR l2 ECHole) (G, r1) (G, r2) IHHpure2) ]
    end.
  - lazymatch goal with
    | |- eval (G, EPlus ?l1 ?r1) (G, EPlus ?l2 ?r2) =>
        eapply eval_trans with (sigma2 := (G, EPlus l2 r1));
        [ exact (eval_plug (ECPlusL ECHole r1) (G, l1) (G, l2) IHHpure1)
        | exact (eval_plug (ECPlusR l2 ECHole) (G, r1) (G, r2) IHHpure2) ]
    end.
Qed.

Lemma step_lemma_entails_var :
  forall G e e' x tb t1 pred,
    step (G, e) (G, e') ->
    has_type_pure empty_ctx e (TBase tb) ->
    [| t1 |] = TBase tb ->
    has_type_pure (ctx_add_var G x t1 e) pred (TBase BBool) ->
    entails G (EImp (expr_subst x e' pred) (expr_subst x e pred)).
Proof.
  intros G e e' x tb t1 pred Hstep _ _ Hpred.
  eapply eval_trans with (sigma2 := (G, EImp (expr_subst x e' pred) (expr_subst x e' pred))).
  - exact (eval_plug
      (ECImpR (expr_subst x e' pred) ECHole)
      (G, expr_subst x e pred)
      (G, expr_subst x e' pred)
      (pure_subst_step_eval G x e e' pred t1 Hstep Hpred)).
  - apply entails_imp_refl.
Qed.

Lemma step_lemma_entails :
  forall G e e' tb t1 pred,
    step (G, e) (G, e') ->
    has_type_pure empty_ctx e (TBase tb) ->
    [| t1 |] = TBase tb ->
    has_type_pure (ctx_add_var G "x" t1 e) pred (TBase BBool) ->
    entails G (EImp (expr_subst "x" e' pred) (expr_subst "x" e pred)).
Proof.
  intros G e e' tb t1 pred Hstep Hpure Hbase Hpred.
  exact (step_lemma_entails_var G e e' "x" tb t1 pred Hstep Hpure Hbase Hpred).
Qed.

Lemma step_lemma_subtype_bidir :
  forall G e e' x tb t1 t,
    step (G, e) (G, e') ->
    has_type_pure empty_ctx e (TBase tb) ->
    [| t1 |] = TBase tb ->
    ty_valid (ctx_add_var G x t1 e) t ->
    subtype G (ty_subst x e' t) (ty_subst x e t) /\
    subtype G (ty_subst x e t) (ty_subst x e' t).
Admitted.

Lemma step_lemma_subtype :
  forall G e e' x tb t1 t,
    step (G, e) (G, e') ->
    has_type_pure empty_ctx e (TBase tb) ->
    [| t1 |] = TBase tb ->
    ty_valid (ctx_add_var G x t1 e) t ->
    subtype G (ty_subst x e' t) (ty_subst x e t).
Proof.
  intros G e e' x tb t1 t Hstep Hpure Hbase Hvalid.
  exact (proj1 (step_lemma_subtype_bidir G e e' x tb t1 t Hstep Hpure Hbase Hvalid)).
Qed.

Lemma step_lemma_bool_entails :
  forall G1 G2 u e e' e1,
    step (empty_ctx, e) (empty_ctx, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    (entails (ctx_add_var (add_ctx G2 G1) u (TSet u BBool e) (EBool true)) e1 <->
     entails (ctx_add_var (add_ctx G2 G1) u (TSet u BBool e') (EBool true)) e1).
Proof.
  intros G1 G2 u e e' e1 _ _.
  split; intro Hent;
    eapply subsumption_entails_var_ctx; exact Hent.
Qed.

Lemma step_lemma_bool_subtype_ctx_left :
  forall C u e e',
    step (empty_ctx, e) (empty_ctx, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    subtype (ctx_add_var C u (TSet u BBool e') (EBool true)) (TSet u BBool e') (TSet u BBool e).
Proof.
  intros C u e e' Hstep Hpure.
  set (x0 := if String.eq_dec u "x" then "y" else "x").
  assert (Hx0u : x0 <> u).
  { unfold x0. destruct (String.eq_dec u "x"); congruence. }
  assert (Hsub0 : subtype empty_ctx (TSet u BBool e') (TSet u BBool e)).
  {
    pose proof
      (step_lemma_subtype
        empty_ctx e e' x0 BBool (TBase BBool) (TSet u BBool (EVar x0))
        Hstep Hpure eq_refl) as Hcore.
    assert (Hvalid :
      ty_valid (ctx_add_var empty_ctx x0 (TBase BBool) e) (TSet u BBool (EVar x0))).
    {
      eapply VSet with (v := EBool true).
      change (has_type_pure
        (ctx_add_var (ctx_add_var empty_ctx x0 (TBase BBool) e) u (TBase BBool) (EBool true))
        (EVar x0) (essential_type (TBase BBool))).
      eapply PVar.
      - rewrite ctx_add_var_swap by congruence.
        unfold var_ctx_lookup, ctx_add_var. simpl.
        apply lookup_insert.
      - simpl. exact I.
    }
    specialize (Hcore Hvalid).
    unfold x0 in Hcore.
    destruct (String.eq_dec u "x") as [Hu | Hu].
    - subst u. cbn [ty_subst] in Hcore. exact Hcore.
    - cbn [ty_subst] in Hcore.
      destruct (String.eqb "x" u) eqn:Heq.
      + apply String.eqb_eq in Heq. congruence.
      + exact Hcore.
  }
  pose proof (weakening_subtype_right empty_ctx (ctx_add_var C u (TSet u BBool e') (EBool true)) _ _ Hsub0) as Hweak.
  rewrite add_ctx_empty_l in Hweak.
  exact Hweak.
Qed.
Lemma step_lemma_bool_subtype_ctx_right :
  forall C u e e',
    step (empty_ctx, e) (empty_ctx, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    subtype (ctx_add_var C u (TSet u BBool e) (EBool true)) (TSet u BBool e) (TSet u BBool e').
Proof.
  intros C u e e' Hstep Hpure.
  set (x0 := if String.eq_dec u "x" then "y" else "x").
  assert (Hx0u : x0 <> u).
  { unfold x0. destruct (String.eq_dec u "x"); congruence. }
  assert (Hsub0 : subtype empty_ctx (TSet u BBool e) (TSet u BBool e')).
  {
    pose proof
      (step_lemma_subtype_bidir
        empty_ctx e e' x0 BBool (TBase BBool) (TSet u BBool (EVar x0))
        Hstep Hpure eq_refl) as Hcore.
    assert (Hvalid :
      ty_valid (ctx_add_var empty_ctx x0 (TBase BBool) e) (TSet u BBool (EVar x0))).
    {
      eapply VSet with (v := EBool true).
      change (has_type_pure
        (ctx_add_var (ctx_add_var empty_ctx x0 (TBase BBool) e) u (TBase BBool) (EBool true))
        (EVar x0) (essential_type (TBase BBool))).
      eapply PVar.
      - rewrite ctx_add_var_swap by congruence.
        unfold var_ctx_lookup, ctx_add_var. simpl.
        apply lookup_insert.
      - simpl. exact I.
    }
    specialize (Hcore Hvalid).
    destruct Hcore as [_ Hcore].
    unfold x0 in Hcore.
    destruct (String.eq_dec u "x") as [Hu | Hu].
    - subst u. cbn [ty_subst] in Hcore. exact Hcore.
    - cbn [ty_subst] in Hcore.
      destruct (String.eqb "x" u) eqn:Heq.
      + apply String.eqb_eq in Heq. congruence.
      + exact Hcore.
  }
  pose proof (weakening_subtype_right empty_ctx (ctx_add_var C u (TSet u BBool e) (EBool true)) _ _ Hsub0) as Hweak.
  rewrite add_ctx_empty_l in Hweak.
  exact Hweak.
Qed.

Lemma step_lemma_bool_subtype_ctx :
  forall C u e e',
    step (empty_ctx, e) (empty_ctx, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    subtype (ctx_add_var C u (TSet u BBool e') (EBool true)) (TSet u BBool e') (TSet u BBool e) /\
    subtype (ctx_add_var C u (TSet u BBool e) (EBool true)) (TSet u BBool e) (TSet u BBool e').
Proof.
  intros C u e e' Hstep Hpure.
  split.
  - exact (step_lemma_bool_subtype_ctx_left C u e e' Hstep Hpure).
  - exact (step_lemma_bool_subtype_ctx_right C u e e' Hstep Hpure).
Qed.

Lemma step_lemma_bool_typing :
  forall G1 G2 u e e' e1 t1,
    step (empty_ctx, e) (empty_ctx, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    (has_type (ctx_add_var (add_ctx G2 G1) u (TSet u BBool e) (EBool true)) e1 t1 <->
     has_type (ctx_add_var (add_ctx G2 G1) u (TSet u BBool e') (EBool true)) e1 t1).
Proof.
  intros G1 G2 u e e' e1 t1 Hstep Hpure.
  split; intro Hty.
  - eapply (subsumption_has_type_var_ctx u (TSet u BBool e) (TSet u BBool e') (EBool true)).
    + intros C.
      destruct (step_lemma_bool_subtype_ctx C u e e' Hstep Hpure) as [Hsub _].
      exact Hsub.
    + exact Hty.
  - eapply (subsumption_has_type_var_ctx u (TSet u BBool e') (TSet u BBool e) (EBool true)).
    + intros C.
      destruct (step_lemma_bool_subtype_ctx C u e e' Hstep Hpure) as [_ Hsub].
      exact Hsub.
    + exact Hty.
Qed.
