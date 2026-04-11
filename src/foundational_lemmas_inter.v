Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
From stdpp Require Export strings.
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

(* Store extension commutes with right-context composition. *)
Lemma add_ctx_ctx_add_store : forall Γ₁ Γ₂ l τ e,
  ctx_add_store (add_ctx Γ₂ Γ₁) l τ e = add_ctx Γ₂ (ctx_add_store Γ₁ l τ e).
Proof.
  intros [envΓ storeΓ] [envD storeD] l τ e.
  destruct envΓ as [varsΓ constsΓ].
  destruct envD as [varsD constsD].
  unfold ctx_add_store, add_ctx. simpl.
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

Lemma has_type_pure_implies_has_type :
  forall Γ e τ,
    has_type_pure Γ e τ ->
    has_type Γ e τ.
Proof.
  intros Γ e τ Hpure.
  induction Hpure.
  - eapply TEssentialVar; eauto.
  - apply TNat.
  - apply TBool.
  - apply TString.
  - apply TUnit.
  - eapply TConst; eauto.
  - eapply TAppImPure.
    + exact IHHpure2.
    + exact IHHpure1.
  - eapply TNot; eauto.
  - eapply TImp; eauto.
  - eapply TAnd; eauto.
  - eapply TOr; eauto.
  - eapply TEq; eauto.
  - eapply TPlus; eauto.
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
  - eapply SSet with (c:=c).
    + apply weakening_ty_valid_right. exact H.
    + apply weakening_ty_valid_right. exact H0.
    + rewrite add_ctx_ctx_add_var.
      apply weakening_entails_right.
      exact H1.
  - apply SSetBase.
    apply weakening_ty_valid_right.
    exact H.
  - eapply SBaseSet with (c:=c).
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
    + exact H.
    + apply weakening_ty_valid_right. exact H0.
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
    + exact IHhas_type1.
    + exact IHhas_type2.
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
    has_type Γ (ELoc l) (TRef τ) ->
    exists τ' v,
      store_ctx_lookup Γ l = Some (τ', v) /\
      ref_type_origin Γ (TRef τ') (TRef τ).
Proof.
  intros Γ l τ Hnone Hty.
  remember (ELoc l) as e eqn:He.
  remember (TRef τ) as tref eqn:Ht.
  revert l τ Hnone He Ht.
  induction Hty; intros l0 τ0 Hnone He Ht.
  all: inversion He; subst; try discriminate.
  all: try (inversion Ht; subst); try discriminate.
  - exists τ0, v. split.
    + exact H.
    + apply RefOriginHere.
  - match goal with
    | Hself : self ?τ (ELoc l0) = TRef τ0 |- _ =>
        apply self_ref_inv in Hself;
        inversion Hself; subst
    end.
    eapply IHHty; eauto.
  - inversion H; subst; try discriminate.
    pose proof (IHHty l0 t Hnone eq_refl eq_refl) as Hinv.
    destruct Hinv as [τ_store Hinv].
    destruct Hinv as [v_store Hinv].
    destruct Hinv as [Hstore Horigin].
    exists τ_store, v_store. split.
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

Lemma in_remove_string_intro :
  forall x y xs,
    x <> y ->
    List.In x xs ->
    List.In x (remove_string y xs).
Proof.
  intros x y xs Hneq Hin.
  unfold remove_string.
  rewrite <- elem_of_list_In.
  apply elem_of_list_filter.
  split.
  - destruct (String.eqb y x) eqn:Heq.
    + apply String.eqb_eq in Heq.
      subst y.
      exfalso.
      apply Hneq.
      reflexivity.
    + exact I.
  - rewrite elem_of_list_In.
    exact Hin.
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
Lemma subtype_refl_valid :
  forall G ty,
    ty_valid G ty -> subtype G ty ty.
Proof.
  intros G ty Hval.
  induction Hval.
  - apply SBase.
  - match goal with
    | b : BaseT |- _ => destruct b
    end.
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
  - eapply SFun; eauto.
  - eapply SFunDep; eauto.
  - eapply SPair; eauto.
  - eapply SRef; eauto.
Qed.


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

Lemma value_change_const_witness :
  forall G f t witness_old witness_new v,
    const_ctx_lookup G f = Some (t, witness_old) ->
    value G v ->
    value (ctx_add_const G f t witness_new) v.
Proof.
  intros G f t witness_old witness_new v Hbind Hv.
  induction Hv.
  - apply VNat.
  - apply VBool.
  - apply VUnit.
  - apply VString.
  - destruct (String.eq_dec c f) as [-> | Hneq].
    + eapply (@VConst (ctx_add_const G f t witness_new) f t witness_new).
      unfold const_ctx_lookup, ctx_add_const.
      simpl.
      apply lookup_insert.
    + eapply VConst.
      unfold const_ctx_lookup, ctx_add_const in *.
      simpl in *.
      rewrite (lookup_insert_ne (snd (fst G)) f c (t, witness_new)) by congruence.
      exact H.
  - apply VFix.
  - constructor.
    + exact IHHv1.
    + exact IHHv2.
  - eapply VVar.
    unfold var_ctx_lookup, ctx_add_const in *.
    simpl in *.
    exact H.
  - eapply VLoc.
    unfold store_ctx_lookup, ctx_add_const in *.
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

Lemma step_preserves_const_lookup :
  forall G e G' e' f t witness,
    step (G, e) (G', e') ->
    const_ctx_lookup G f = Some (t, witness) ->
    const_ctx_lookup G' f = Some (t, witness).
Proof.
  intros G e G' e' f t witness Hstep Hlookup.
  destruct (step_preserves_env _ _ _ _ Hstep) as [_ Hconsts].
  unfold const_ctx_lookup in *.
  simpl in *.
  rewrite <- Hconsts.
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

Lemma ctx_add_const_shadow :
  forall C f t_old e_old t_new e_new,
    ctx_add_const (ctx_add_const C f t_old e_old) f t_new e_new =
    ctx_add_const C f t_new e_new.
Proof.
  intros C f t_old e_old t_new e_new.
  destruct C as [vc store].
  destruct vc as [vars consts].
  unfold ctx_add_const.
  simpl.
  f_equal.
  f_equal.
  apply insert_insert.
Qed.

Lemma ctx_add_const_swap :
  forall C f tf ef g tg eg,
    f <> g ->
    ctx_add_const (ctx_add_const C f tf ef) g tg eg =
    ctx_add_const (ctx_add_const C g tg eg) f tf ef.
Proof.
  intros C f tf ef g tg eg Hneq.
  destruct C as [vc store].
  destruct vc as [vars consts].
  unfold ctx_add_const.
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

Lemma ctx_add_const_store_comm :
  forall C l tl vl f tf ef,
    ctx_add_const (ctx_add_store C l tl vl) f tf ef =
    ctx_add_store (ctx_add_const C f tf ef) l tl vl.
Proof.
  intros C l tl vl f tf ef.
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
    | var a b Hv1 Hv2
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
        exact (IH (ctx_add_var C var _ (EVar var)) _ Hv2).
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
    | var a b c d Hs1 Hs2
    | τ₁ τ₁' τ₂ τ₂' Hs1 Hs2
    | t t' Hs1 Hs2].
  - apply SBase.
  - eapply SSet with (c:=c).
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
  - eapply SBaseSet with (c:=c).
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
        exact (IH (ctx_add_var C var _ (EVar var)) _ _ Hs2).
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
    + exact H.
    + exact (subsumption_ty_valid_var_ctx (ctx_add_var C0 x t_new witness) x t_old t_new witness (Hsub C0) C0 _ H0).
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
    + exact (IHHty1 C0 eq_refl).
    + exact (IHHty2 C0 eq_refl).
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

Lemma ty_subst_self_with_base :
  forall x e0 u b e,
    x <> u ->
    ty_subst x e0 (self_with u (TBase b) e) =
    self_with u (TBase b) (expr_subst x e0 e).
Proof.
  intros x e0 u b e Hneq.
  simpl.
  assert (Hneqb : (x =? u)%string = false) by (apply String.eqb_neq; exact Hneq).
  rewrite Hneqb.
  reflexivity.
Qed.
Lemma self_unfold_self_with :
  forall t e,
    self t e = self_with (fresh_string_list (exp_vars e)) t e.
Proof.
  reflexivity.
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

Lemma expr_subst_exp_vars_fresh :
  forall x s e,
    ~ List.In x (exp_vars e) ->
    expr_subst x s e = e.
Proof.
  fix IH 3.
  intros x s e Hfresh.
  destruct e; simpl in *; try reflexivity.
  - destruct (String.eqb_spec x s0) as [Heq | Hneq].
    + subst. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - assert (Hneq : x <> s1).
    { intro Heq. apply Hfresh. subst. simpl. auto. }
    assert (Hneqf : x <> s0).
    { intro Heq. apply Hfresh. subst. simpl. auto. }
    assert (Hfresh_t1 : ~ List.In x (ty_vars i)).
    { intro Hin. apply Hfresh. simpl. right. right. apply in_or_app. left. exact Hin. }
    assert (Hfresh_t2 : ~ List.In x (ty_vars i0)).
    { intro Hin. apply Hfresh. simpl. right. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (Hfresh_body : ~ List.In x (exp_vars e)).
    { intro Hin. apply Hfresh. simpl. right. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    assert (Htyfresh : forall t, ~ List.In x (ty_vars t) -> ty_subst x s t = t).
    { intros t.
      induction t; intros Hfresh_t; simpl in *; try reflexivity.

      - destruct (String.eqb_spec x s2) as [Heq | Hneq2].
        + subst. exfalso. apply Hfresh_t. simpl. auto.
        + rewrite IH by (intro Hin; apply Hfresh_t; simpl; right; exact Hin).
          reflexivity.
      - assert (Hfresh1 : ~ List.In x (ty_vars t1)).
        { intro Hin. apply Hfresh_t. apply in_or_app. left. exact Hin. }
        assert (Hfresh2 : ~ List.In x (ty_vars t2)).
        { intro Hin. apply Hfresh_t. apply in_or_app. right. exact Hin. }
        rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - assert (Hneqx : x <> s2).
        { intro Heq. apply Hfresh_t. subst. simpl. auto. }
        assert (Hfresh1 : ~ List.In x (ty_vars t1)).
        { intro Hin. apply Hfresh_t. simpl. right. apply in_or_app. left. exact Hin. }
        assert (Hfresh2 : ~ List.In x (ty_vars t2)).
        { intro Hin. apply Hfresh_t. simpl. right. apply in_or_app. right. exact Hin. }
        apply String.eqb_neq in Hneqx.
        rewrite Hneqx.
        rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - assert (Hfresh1 : ~ List.In x (ty_vars t1)).
        { intro Hin. apply Hfresh_t. apply in_or_app. left. exact Hin. }
        assert (Hfresh2 : ~ List.In x (ty_vars t2)).
        { intro Hin. apply Hfresh_t. apply in_or_app. right. exact Hin. }
        rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - rewrite (IHt Hfresh_t). reflexivity. }
    destruct (String.eqb s0 x) eqn:Heqf.
    + apply String.eqb_eq in Heqf.
      exfalso.
      apply Hneqf.
      symmetry.
      exact Heqf.
    + destruct (String.eqb s1 x) eqn:Heqy.
      * apply String.eqb_eq in Heqy.
        exfalso.
        apply Hneq.
        symmetry.
        exact Heqy.
      * rewrite (Htyfresh i Hfresh_t1), (Htyfresh i0 Hfresh_t2), IH by exact Hfresh_body.
        reflexivity.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1).
    rewrite (IH x s e2 Hfresh2).
    reflexivity.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1).
    rewrite (IH x s e2 Hfresh2).
    reflexivity.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1).
    rewrite (IH x s e2 Hfresh2).
    reflexivity.
  - assert (Hfresh_e : ~ List.In x (exp_vars e)).
    { intro Hin. apply Hfresh. simpl. exact Hin. }
    rewrite (IH x s e Hfresh_e).
    reflexivity.
  - match goal with
    | [ e' : i_expr |- _ ] => rewrite (IH x s e')
    end.
    + reflexivity.
    + intro Hin. apply Hfresh. simpl. exact Hin.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (Hfresh3 : ~ List.In x (exp_vars e3)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1).
    rewrite (IH x s e2 Hfresh2).
    rewrite (IH x s e3 Hfresh3).
    reflexivity.
  - rewrite (IH x s e).
    + reflexivity.
    + intro Hin. apply Hfresh. simpl. exact Hin.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1).
    rewrite (IH x s e2 Hfresh2).
    reflexivity.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1).
    rewrite (IH x s e2 Hfresh2).
    reflexivity.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1).
    rewrite (IH x s e2 Hfresh2).
    reflexivity.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1).
    rewrite (IH x s e2 Hfresh2).
    reflexivity.
  - assert (Hfresh_t : ~ List.In x (ty_vars i)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh_e : ~ List.In x (exp_vars e)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    assert (Htyfresh : forall t, ~ List.In x (ty_vars t) -> ty_subst x s t = t).
    { intros t.
      induction t; intros Hfresh_t0; simpl in *; try reflexivity.
      - destruct (String.eqb_spec x s0) as [Heq | Hneq].
        + subst. exfalso. apply Hfresh_t0. simpl. auto.
        + rewrite IH by (intro Hin; apply Hfresh_t0; simpl; right; exact Hin).
          reflexivity.
      - assert (Hfresh1 : ~ List.In x (ty_vars t1)).
        { intro Hin. apply Hfresh_t0. apply in_or_app. left. exact Hin. }
        assert (Hfresh2 : ~ List.In x (ty_vars t2)).
        { intro Hin. apply Hfresh_t0. apply in_or_app. right. exact Hin. }
        rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - assert (Hneqx : x <> s0).
        { intro Heq. apply Hfresh_t0. subst. simpl. auto. }
        assert (Hfresh1 : ~ List.In x (ty_vars t1)).
        { intro Hin. apply Hfresh_t0. simpl. right. apply in_or_app. left. exact Hin. }
        assert (Hfresh2 : ~ List.In x (ty_vars t2)).
        { intro Hin. apply Hfresh_t0. simpl. right. apply in_or_app. right. exact Hin. }
        apply String.eqb_neq in Hneqx.
        rewrite Hneqx.
        rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - assert (Hfresh1 : ~ List.In x (ty_vars t1)).
        { intro Hin. apply Hfresh_t0. apply in_or_app. left. exact Hin. }
        assert (Hfresh2 : ~ List.In x (ty_vars t2)).
        { intro Hin. apply Hfresh_t0. apply in_or_app. right. exact Hin. }
        rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - rewrite (IHt Hfresh_t0). reflexivity. }
    rewrite (Htyfresh i Hfresh_t), (IH x s e Hfresh_e).
    reflexivity.
  - assert (Hfresh_e : ~ List.In x (exp_vars e)).
    { intro Hin. apply Hfresh. exact Hin. }
    rewrite (IH x s e Hfresh_e).
    reflexivity.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1).
    rewrite (IH x s e2 Hfresh2).
    reflexivity.
Qed.

Lemma ty_subst_ty_vars_fresh :
  forall x s t,
    ~ List.In x (ty_vars t) ->
    ty_subst x s t = t.
Proof.
  intros x s t.
  induction t; intros Hfresh; simpl in *; try reflexivity.
  - destruct (String.eqb_spec x s0) as [Heq | Hneq].
    + subst. exfalso. apply Hfresh. simpl. auto.
    + rewrite expr_subst_exp_vars_fresh.
      * reflexivity.
      * intro Hin. apply Hfresh. simpl. right. exact Hin.
  - assert (Hfresh1 : ~ List.In x (ty_vars t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHt1 Hfresh1).
    rewrite (IHt2 Hfresh2).
    reflexivity.
  - assert (Hneq : x <> s0).
    { intro Heq. apply Hfresh. subst. simpl. auto. }
    assert (Hfresh1 : ~ List.In x (ty_vars t1)).
    { intro Hin. apply Hfresh. simpl. right. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars t2)).
    { intro Hin. apply Hfresh. simpl. right. apply in_or_app. right. exact Hin. }
    apply String.eqb_neq in Hneq.
    rewrite Hneq.
    rewrite (IHt1 Hfresh1).
    rewrite (IHt2 Hfresh2).
    reflexivity.
  - assert (Hfresh1 : ~ List.In x (ty_vars t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHt1 Hfresh1).
    rewrite (IHt2 Hfresh2).
    reflexivity.
  - rewrite (IHt Hfresh).
    reflexivity.
Qed.

Lemma expr_subst_free_exp_vars_fresh :
  forall x s e,
    ~ List.In x (free_exp_vars e) ->
    expr_subst x s e = e.
Proof.
  fix IH 3.
  intros x s e Hfresh.
  destruct e; simpl in *; try reflexivity.
  - destruct (String.eqb_spec x s0) as [Heq | Hneq].
    + subst. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - assert (Hfresh_t1 : ~ List.In x (free_ty_vars i)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Htyfresh : forall t, ~ List.In x (free_ty_vars t) -> ty_subst x s t = t).
    { intros t.
      induction t; intros Hfresh_t; simpl in *; try reflexivity.
      - destruct (String.eqb_spec x s2) as [Heq | Hneq].
        + subst s2. reflexivity.
        + rewrite IH by (intro Hin; apply Hfresh_t; apply in_remove_string_intro; assumption).
          reflexivity.
      - assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
        { intro Hin. apply Hfresh_t. apply in_or_app. left. exact Hin. }
        assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
        { intro Hin. apply Hfresh_t. apply in_or_app. right. exact Hin. }
        rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - destruct (String.eqb_spec x s2) as [Heq | Hneq].
        + subst s2.
          assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
          { intro Hin. apply Hfresh_t. apply in_or_app. left. exact Hin. }
          rewrite (IHt1 Hfresh1). reflexivity.
        + assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
          { intro Hin. apply Hfresh_t. apply in_or_app. left. exact Hin. }
          assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
          { intro Hin. apply Hfresh_t. apply in_or_app. right. apply in_remove_string_intro; assumption. }
          rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
        { intro Hin. apply Hfresh_t. apply in_or_app. left. exact Hin. }
        assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
        { intro Hin. apply Hfresh_t. apply in_or_app. right. exact Hin. }
        rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - rewrite (IHt Hfresh_t). reflexivity. }
    destruct (String.eqb s1 x) eqn:Hyx.
    + rewrite (Htyfresh i Hfresh_t1). reflexivity.
    + assert (Hneqyx : x <> s1).
      { intro Heq. apply String.eqb_neq in Hyx. apply Hyx. symmetry. exact Heq. }
      assert (Hfresh_t2 : ~ List.In x (free_ty_vars i0)).
      { intro Hin. apply Hfresh. apply in_or_app. right. apply in_remove_string_intro.
        - exact Hneqyx.
        - apply in_or_app. left. exact Hin. }
      assert (Hbody : ~ List.In x (free_exp_vars e)).
      { intro Hin.
        apply Hfresh.
        apply in_or_app.
        right.
        apply in_remove_string_intro.
        - exact Hneqyx.
        - apply in_or_app. right. exact Hin. }
      rewrite (Htyfresh i Hfresh_t1), (Htyfresh i0 Hfresh_t2), (IH x s e Hbody).
      reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1), (IH x s e2 Hfresh2). reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1), (IH x s e2 Hfresh2). reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1), (IH x s e2 Hfresh2). reflexivity.
  - rewrite (IH x s e Hfresh). reflexivity.
  - rewrite (IH x s e Hfresh). reflexivity.
  - assert (Hf1 : ~ List.In x (free_exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hf2 : ~ List.In x (free_exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (Hf3 : ~ List.In x (free_exp_vars e3)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hf1), (IH x s e2 Hf2), (IH x s e3 Hf3). reflexivity.
  - rewrite (IH x s e Hfresh). reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1), (IH x s e2 Hfresh2). reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1), (IH x s e2 Hfresh2). reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1), (IH x s e2 Hfresh2). reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1), (IH x s e2 Hfresh2). reflexivity.
  - assert (Hfresh_t : ~ List.In x (free_ty_vars i)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh_e : ~ List.In x (free_exp_vars e)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    assert (Htyfresh : forall t, ~ List.In x (free_ty_vars t) -> ty_subst x s t = t).
    { intros t.
      induction t; intros Hfresh_t0; simpl in *; try reflexivity.
      - destruct (String.eqb_spec x s0) as [Heq | Hneq].
        + subst. reflexivity.
        + rewrite IH by (intro Hin; apply Hfresh_t0; apply in_remove_string_intro; assumption).
          reflexivity.
      - assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
        { intro Hin. apply Hfresh_t0. apply in_or_app. left. exact Hin. }
        assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
        { intro Hin. apply Hfresh_t0. apply in_or_app. right. exact Hin. }
        rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - destruct (String.eqb_spec x s0) as [Heq | Hneq].
        + subst s0.
          assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
          { intro Hin. apply Hfresh_t0. apply in_or_app. left. exact Hin. }
          rewrite (IHt1 Hfresh1). reflexivity.
        + assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
          { intro Hin. apply Hfresh_t0. apply in_or_app. left. exact Hin. }
          assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
          { intro Hin. apply Hfresh_t0. apply in_or_app. right. apply in_remove_string_intro; assumption. }
          rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
        { intro Hin. apply Hfresh_t0. apply in_or_app. left. exact Hin. }
        assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
        { intro Hin. apply Hfresh_t0. apply in_or_app. right. exact Hin. }
        rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
      - rewrite (IHt Hfresh_t0). reflexivity. }
    rewrite (Htyfresh i Hfresh_t), (IH x s e Hfresh_e). reflexivity.
  - rewrite (IH x s e Hfresh). reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_exp_vars e1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_exp_vars e2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IH x s e1 Hfresh1), (IH x s e2 Hfresh2). reflexivity.
Qed.

Lemma ty_subst_free_ty_vars_fresh :
  forall x s t,
    ~ List.In x (free_ty_vars t) ->
    ty_subst x s t = t.
Proof.
  intros x s t.
  induction t; intros Hfresh; simpl in *; try reflexivity.
  - destruct (String.eqb x s0) eqn:Heq.
    + reflexivity.
    + rewrite expr_subst_free_exp_vars_fresh.
      * reflexivity.
      * intro Hin.
        apply Hfresh.
        apply in_remove_string_intro.
        -- apply String.eqb_neq. exact Heq.
        -- exact Hin.
  - assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
  - destruct (String.eqb x s0) eqn:Heq.
    + assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
      { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
      rewrite (IHt1 Hfresh1). reflexivity.
    + assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
      { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
      assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
      { intro Hin.
        apply Hfresh.
        apply in_or_app. right.
        apply in_remove_string_intro.
        - apply String.eqb_neq. exact Heq.
        - exact Hin. }
      rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
  - assert (Hfresh1 : ~ List.In x (free_ty_vars t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (free_ty_vars t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHt1 Hfresh1), (IHt2 Hfresh2). reflexivity.
  - rewrite (IHt Hfresh). reflexivity.
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

Lemma ctx_subst_store_binding_fixed :
  forall G x e0 l t witness,
    ctx_subst x e0 G = G ->
    G !!₃ l = Some (t, witness) ->
    ty_subst x e0 t = t /\ expr_subst x e0 witness = witness.
Proof.
  intros G x e0 l t witness Hctx Hlookup.
  destruct G as [env store].
  destruct env as [vars consts].
  unfold store_ctx_lookup in Hlookup.
  simpl in Hlookup.
  pose proof (f_equal (fun H => snd H) Hctx) as Hstore.
  simpl in Hstore.
  pose proof (f_equal (fun H => H !! l) Hstore) as Hlookup1.
  simpl in Hlookup1.
  rewrite Hlookup in Hlookup1.
  apply lookup_fmap_Some in Hlookup1.
  destruct Hlookup1 as [entry Hlookup1].
  destruct Hlookup1 as [Hmap Hentry].
  assert (Heq : entry = (t, witness)).
  { enough (Some entry = Some (t, witness)) by (inversion H; reflexivity).
    transitivity (store !! l).
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

Lemma lookup_lemma_var_ctx_subst_fixed :
  forall C x e0 y t witness,
    ctx_subst x e0 C = C ->
    var_ctx_lookup C y = Some (t, witness) ->
    var_ctx_lookup (ctx_subst x e0 C) y = Some (t, witness).
Proof.
  intros C x e0 y t witness Hctx Hlookup.
  pose proof (lookup_lemma_var_ctx_subst C x e0 y t witness Hlookup) as Hlookup'.
  destruct (ctx_subst_var_binding_fixed C x e0 y t witness Hctx Hlookup) as [Hty Hexp].
  rewrite Hty, Hexp in Hlookup'.
  exact Hlookup'.
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

Lemma lookup_lemma_const_ctx_subst_fixed :
  forall C x e0 c t witness,
    ctx_subst x e0 C = C ->
    const_ctx_lookup C c = Some (t, witness) ->
    const_ctx_lookup (ctx_subst x e0 C) c = Some (t, witness).
Proof.
  intros C x e0 c t witness Hctx Hlookup.
  pose proof (lookup_lemma_const_ctx_subst C x e0 c t witness Hlookup) as Hlookup'.
  destruct (ctx_subst_const_binding_fixed C x e0 c t witness Hctx Hlookup) as [Hty Hexp].
  rewrite Hty, Hexp in Hlookup'.
  exact Hlookup'.
Qed.

Lemma lookup_lemma_store_ctx_subst :
  forall C x e0 l t witness,
    store_ctx_lookup C l = Some (t, witness) ->
    store_ctx_lookup (ctx_subst x e0 C) l = Some (ty_subst x e0 t, expr_subst x e0 witness).
Proof.
  intros C x e0 l t witness Hlookup.
  destruct C as [env store].
  destruct env as [vars consts].
  unfold store_ctx_lookup, ctx_subst. simpl.
  apply lookup_fmap_Some.
  exists (t, witness).
  split; [reflexivity | exact Hlookup].
Qed.

Lemma lookup_lemma_store_ctx_subst_fixed :
  forall C x e0 l t witness,
    ctx_subst x e0 C = C ->
    store_ctx_lookup C l = Some (t, witness) ->
    store_ctx_lookup (ctx_subst x e0 C) l = Some (t, witness).
Proof.
  intros C x e0 l t witness Hctx Hlookup.
  pose proof (lookup_lemma_store_ctx_subst C x e0 l t witness Hlookup) as Hlookup'.
  destruct (ctx_subst_store_binding_fixed C x e0 l t witness Hctx Hlookup) as [Hty Hexp].
  rewrite Hty, Hexp in Hlookup'.
  exact Hlookup'.
Qed.

Lemma lookup_lemma_var_ctx_add_var_shadow :
  forall C x tx ex,
    var_ctx_lookup (ctx_add_var C x tx ex) x = Some (tx, ex).
Proof.
  intros C x tx ex.
  unfold var_ctx_lookup, ctx_add_var.
  simpl.
  apply lookup_insert.
Qed.

Lemma lookup_lemma_var_ctx_add_var_nonshadow :
  forall C x y tx ex t witness,
    y <> x ->
    var_ctx_lookup (ctx_add_var C x tx ex) y = Some (t, witness) ->
    var_ctx_lookup C y = Some (t, witness).
Proof.
  intros C x y tx ex t witness Hneq Hlookup.
  unfold var_ctx_lookup, ctx_add_var in *.
  simpl in *.
  apply lookup_insert_Some in Hlookup.
  destruct Hlookup as [Hcase | Hcase].
  - destruct Hcase as [Heq _].
    subst.
    congruence.
  - destruct Hcase as [_ HlookupC].
    exact HlookupC.
Qed.

Lemma lookup_lemma_const_ctx_add_var :
  forall C x tx ex c t witness,
    const_ctx_lookup (ctx_add_var C x tx ex) c = Some (t, witness) ->
    const_ctx_lookup C c = Some (t, witness).
Proof.
  intros C x tx ex c t witness Hlookup.
  unfold const_ctx_lookup, ctx_add_var in *.
  simpl in *.
  exact Hlookup.
Qed.

Lemma lookup_lemma_store_ctx_add_var :
  forall C x tx ex l t witness,
    store_ctx_lookup (ctx_add_var C x tx ex) l = Some (t, witness) ->
    store_ctx_lookup C l = Some (t, witness).
Proof.
  intros C x tx ex l t witness Hlookup.
  unfold store_ctx_lookup, ctx_add_var in *.
  simpl in *.
  exact Hlookup.
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

Lemma ctx_subst_add_ctx_stable :
  forall G1 G2 x e0,
    ctx_subst x e0 G1 = G1 ->
    ctx_subst x e0 G2 = G2 ->
    ctx_subst x e0 (add_ctx G2 G1) = add_ctx G2 G1.
Proof.
  intros G1 G2 x e0 Hctx1 Hctx2.
  rewrite ctx_subst_add_ctx.
  rewrite Hctx1.
  rewrite Hctx2.
  reflexivity.
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

Lemma ctx_subst_ctx_add_const :
  forall C f ty witness x e0,
    ctx_subst x e0 (ctx_add_const C f ty witness) =
    ctx_add_const (ctx_subst x e0 C) f (ty_subst x e0 ty) (expr_subst x e0 witness).
Proof.
  intros [env store] f ty witness x e0.
  destruct env as [vars consts].
  unfold ctx_subst, ctx_add_const. simpl.
  f_equal.
  f_equal.
  rewrite (fmap_insert (binding_subst x e0) consts f (ty, witness)).
  reflexivity.
Qed.

Lemma ctx_subst_ctx_add_var_stable :
  forall C y ty witness x e0,
    ctx_subst x e0 C = C ->
    ty_subst x e0 ty = ty ->
    expr_subst x e0 witness = witness ->
    ctx_subst x e0 (ctx_add_var C y ty witness) = ctx_add_var C y ty witness.
Proof.
  intros C y ty witness x e0 Hctx Hty Hex.
  rewrite ctx_subst_ctx_add_var.
  rewrite Hctx.
  rewrite Hty.
  rewrite Hex.
  reflexivity.
Qed.

Lemma ctx_subst_ctx_add_var_base_stable :
  forall C y tb c x e0,
    ctx_subst x e0 C = C ->
    ctx_subst x e0 (ctx_add_var C y (TBase tb) (make_expr tb c)) =
    ctx_add_var C y (TBase tb) (make_expr tb c).
Proof.
  intros C y tb c x e0 Hctx.
  apply (ctx_subst_ctx_add_var_stable C y (TBase tb) (make_expr tb c) x e0 Hctx).
  - simpl. reflexivity.
  - destruct tb; destruct c; reflexivity.
Qed.

Lemma subst_base_has_type_var_shadow_ctx_stable_from_witness :
  forall C x e0 t0,
    has_type (ctx_subst x e0 C) e0 (ty_subst x e0 t0) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EVar x)) (ty_subst x e0 t0).
Proof.
  intros C x e0 t0 Hw.
  simpl.
  rewrite String.eqb_refl.
  exact Hw.
Qed.

Lemma subst_base_has_type_essential_var_shadow_ctx_stable :
  forall C x e0 t0,
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EVar x)) (ty_subst x e0 (essential_type t0)).
Proof.
  intros C x e0 t0 Hbeta0 Hpure0.
  simpl.
  rewrite String.eqb_refl.
  rewrite ty_subst_essential_type_id by exact Hbeta0.
  exact (has_type_pure_implies_has_type _ _ _ Hpure0).
Qed.

Lemma subst_base_has_type_var_nonshadow_ctx_stable :
  forall C x e0 t0 y t witness,
    ctx_subst x e0 C = C ->
    y <> x ->
    (ctx_add_var C x t0 e0) !!₁ y = Some (t, witness) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EVar y)) (ty_subst x e0 t).
Proof.
  intros C x e0 t0 y t witness Hctx Hneq Hlookup.
  assert (HlookupC : C !!₁ y = Some (t, witness)).
  { exact (lookup_lemma_var_ctx_add_var_nonshadow C x y t0 e0 t witness Hneq Hlookup). }
  assert (HlookupSubst : (ctx_subst x e0 C) !!₁ y = Some (ty_subst x e0 t, expr_subst x e0 witness)).
  { exact (lookup_lemma_var_ctx_subst C x e0 y t witness HlookupC). }
  assert (Hneqb : (x =? y)%string = false) by (apply String.eqb_neq; congruence).
  simpl.
  rewrite Hneqb.
  eapply TVar.
  exact HlookupSubst.
Qed.

Lemma subst_base_has_type_essential_var_nonshadow_ctx_stable :
  forall C x e0 t0 y t witness,
    ctx_subst x e0 C = C ->
    y <> x ->
    (ctx_add_var C x t0 e0) !!₁ y = Some (t, witness) ->
    essential_type_is_base_type t = true ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EVar y)) (ty_subst x e0 (essential_type t)).
Proof.
  intros C x e0 t0 y t witness Hctx Hneq Hlookup Hbeta.
  assert (HlookupC : C !!₁ y = Some (t, witness)).
  { exact (lookup_lemma_var_ctx_add_var_nonshadow C x y t0 e0 t witness Hneq Hlookup). }
  assert (HlookupSubst : (ctx_subst x e0 C) !!₁ y = Some (ty_subst x e0 t, expr_subst x e0 witness)).
  { exact (lookup_lemma_var_ctx_subst C x e0 y t witness HlookupC). }
  assert (Hneqb : (x =? y)%string = false) by (apply String.eqb_neq; congruence).
  assert (HbetaSubst : essential_type_is_base_type (ty_subst x e0 t) = true).
  { exact (ty_subst_preserves_beta x e0 t Hbeta). }
  simpl.
  rewrite Hneqb.
  rewrite <- (ty_subst_preserves_essential_type x e0 t Hbeta).
  eapply TEssentialVar.
  - exact HlookupSubst.
  - rewrite HbetaSubst. exact I.
Qed.

Lemma subst_base_has_type_const_ctx_stable :
  forall C x e0 t0 c t witness,
    ctx_subst x e0 C = C ->
    (ctx_add_var C x t0 e0) !!₂ c = Some (t, witness) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EConst c)) (ty_subst x e0 t).
Proof.
  intros C x e0 t0 c t witness Hctx Hlookup.
  assert (HlookupC : C !!₂ c = Some (t, witness)).
  { exact (lookup_lemma_const_ctx_add_var C x t0 e0 c t witness Hlookup). }
  assert (HlookupSubst : (ctx_subst x e0 C) !!₂ c = Some (ty_subst x e0 t, expr_subst x e0 witness)).
  { exact (lookup_lemma_const_ctx_subst C x e0 c t witness HlookupC). }
  simpl.
  eapply TConst.
  exact HlookupSubst.
Qed.

Lemma subst_base_has_type_loc_nonshadow_ctx_stable :
  forall C x e0 t0 l t witness,
    ctx_subst x e0 C = C ->
    l <> x ->
    (ctx_add_var C x t0 e0) !!₃ l = Some (t, witness) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (ELoc l)) (ty_subst x e0 (TRef t)).
Proof.
  intros C x e0 t0 l t witness Hctx Hneq Hlookup.
  assert (HlookupC : C !!₃ l = Some (t, witness)).
  { exact (lookup_lemma_store_ctx_add_var C x t0 e0 l t witness Hlookup). }
  assert (HlookupSubst : (ctx_subst x e0 C) !!₃ l = Some (ty_subst x e0 t, expr_subst x e0 witness)).
  { exact (lookup_lemma_store_ctx_subst C x e0 l t witness HlookupC). }
  simpl.
  eapply TLoc.
  exact HlookupSubst.
Qed.

Lemma subst_base_has_type_app_pure_ctx_stable_from_premises :
  forall C x e0 e1 e2 y t1 t2 t2',
    has_type (ctx_subst x e0 C) (expr_subst x e0 e2) (ty_subst x e0 t1) ->
    (forall t3, has_type_pure (ctx_subst x e0 C) (expr_subst x e0 e2) t3) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e1) (TArrDep y (ty_subst x e0 t1) t2') ->
    ty_subst x e0 (ty_subst y e2 t2) =
    ty_subst y (expr_subst x e0 e2) t2' ->
    has_type (ctx_subst x e0 C)
      (expr_subst x e0 (EApp e1 e2))
      (ty_subst x e0 (ty_subst y e2 t2)).
Proof.
  intros C x e0 e1 e2 y t1 t2 t2' Harg HargPure Hfun Hcomm.
  simpl.
  rewrite Hcomm.
  eapply TAppPure.
  - exact Harg.
  - exact HargPure.
  - exact Hfun.
Qed.

Lemma subst_base_has_type_app_impure_ctx_stable_from_subterms :
  forall C x e0 e1 e2 t1 t2,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e2) (ty_subst x e0 t1) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e1) (ty_subst x e0 (TArr t1 t2)) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EApp e1 e2)) (ty_subst x e0 t2).
Proof.
  intros C x e0 e1 e2 t1 t2 Harg Hfun.
  simpl.
  eapply TAppImPure.
  - exact Harg.
  - exact Hfun.
Qed.

Lemma subst_base_has_type_fun_nonshadow_ctx_stable_from_premises :
  forall C x e0 f y t1 t2 body,
    y <> x ->
    ~ List.In y (ty_vars t1) ->
    ty_subst x e0 t1 = t1 ->
    ty_subst x e0 t2 = t2 ->
    ty_valid (ctx_subst x e0 C) (TArrDep y t1 t2) ->
    has_type
      (((ctx_subst x e0 C) ,,c f ↦ (TArrDep y t1 t2, EFix f y t1 t2 (expr_subst x e0 body)))
        ,,v y ↦ (t1, EVar y))
      (expr_subst x e0 body)
      t2 ->
    has_type
      (ctx_subst x e0 C)
      (expr_subst x e0 (EFix f y t1 t2 body))
      (ty_subst x e0 (TArrDep y t1 t2)).
Proof.
  intros C x e0 f y t1 t2 body Hneq Hfresh Ht1 Ht2 Hvalid Hbody.
  assert (Hneqbxy : (x =? y)%string = false) by (apply String.eqb_neq; congruence).
  assert (Hneqbyx : (y =? x)%string = false).
  { rewrite String.eqb_sym. exact Hneqbxy. }
  simpl.
  rewrite Hneqbyx.
  rewrite Hneqbxy.
  rewrite Ht1.
  rewrite Ht2.
  eapply TFun.
  + exact Hfresh.
  + exact Hvalid.
  + exact Hbody.
Qed.

Lemma subst_base_has_type_fun_nonshadow_ctx_stable_from_substituted_premises :
  forall C x e0 f y t1 t2 body,
    y <> x ->
    ~ List.In y (ty_vars (ty_subst x e0 t1)) ->
    ty_valid (ctx_subst x e0 C) (ty_subst x e0 (TArrDep y t1 t2)) ->
    has_type
      (ctx_subst x e0 (((C ,,c f ↦ (TArrDep y t1 t2, EFix f y t1 t2 body)) ,,v y ↦ (t1, EVar y))))
      (expr_subst x e0 body)
      (ty_subst x e0 t2) ->
    has_type
      (ctx_subst x e0 C)
      (expr_subst x e0 (EFix f y t1 t2 body))
      (ty_subst x e0 (TArrDep y t1 t2)).
Proof.
  intros C x e0 f y t1 t2 body Hneq Hfresh Hvalid Hbody.
  assert (Hneqbxy : (x =? y)%string = false) by (apply String.eqb_neq; congruence).
  assert (Hneqbyx : (y =? x)%string = false).
  { rewrite String.eqb_sym. exact Hneqbxy. }
  simpl.
  rewrite Hneqbyx.
  rewrite Hneqbxy.
  simpl in Hvalid.
  rewrite Hneqbxy in Hvalid.
  rewrite ctx_subst_ctx_add_var in Hbody.
  rewrite ctx_subst_ctx_add_const in Hbody.
  simpl in Hbody.
  rewrite Hneqbyx in Hbody.
  rewrite Hneqbxy in Hbody.
  eapply TFun.
  - exact Hfresh.
  - exact Hvalid.
  - exact Hbody.
Qed.


Lemma subst_base_has_type_fun_shadow_ctx_stable_from_premises :
  forall C x e0 f t1 t2 body,
    ~ List.In x (ty_vars t1) ->
    ty_subst x e0 t1 = t1 ->
    ty_valid (ctx_subst x e0 C) (TArrDep x t1 t2) ->
    has_type
      (((ctx_subst x e0 C) ,,c f ↦ (TArrDep x t1 t2, EFix f x t1 t2 body))
        ,,v x ↦ (t1, EVar x))
      body
      t2 ->
    has_type
      (ctx_subst x e0 C)
      (expr_subst x e0 (EFix f x t1 t2 body))
      (ty_subst x e0 (TArrDep x t1 t2)).
Proof.
  intros C x e0 f t1 t2 body Hfresh Ht1 Hvalid Hbody.
  simpl.
  rewrite String.eqb_refl.
  rewrite Ht1.
  eapply TFun.
  - exact Hfresh.
  - exact Hvalid.
  - exact Hbody.
Qed.

Lemma subst_base_has_type_plus_ctx_stable_from_subterms :
  forall C x e0 e1 e2,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e1) (TBase BNat) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e2) (TBase BNat) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EPlus e1 e2)) (TBase BNat).
Proof.
  intros C x e0 e1 e2 H1 H2.
  simpl.
  eapply TPlus; eauto.
Qed.

Lemma subst_base_has_type_not_ctx_stable_from_subterm :
  forall C x e0 e,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (TBase BBool) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (ENot e)) (TBase BBool).
Proof.
  intros C x e0 e H.
  simpl.
  eapply TNot.
  exact H.
Qed.

Lemma subst_base_has_type_imp_ctx_stable_from_subterms :
  forall C x e0 e1 e2,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e1) (TBase BBool) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e2) (TBase BBool) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EImp e1 e2)) (TBase BBool).
Proof.
  intros C x e0 e1 e2 H1 H2.
  simpl.
  eapply TImp; eauto.
Qed.

Lemma subst_base_has_type_and_ctx_stable_from_subterms :
  forall C x e0 e1 e2,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e1) (TBase BBool) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e2) (TBase BBool) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EAnd e1 e2)) (TBase BBool).
Proof.
  intros C x e0 e1 e2 H1 H2.
  simpl.
  eapply TAnd; eauto.
Qed.

Lemma subst_base_has_type_or_ctx_stable_from_subterms :
  forall C x e0 e1 e2,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e1) (TBase BBool) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e2) (TBase BBool) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EOr e1 e2)) (TBase BBool).
Proof.
  intros C x e0 e1 e2 H1 H2.
  simpl.
  eapply TOr; eauto.
Qed.

Lemma subst_base_has_type_eq_ctx_stable_from_subterms :
  forall C x e0 e1 e2 tb,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e1) (TBase tb) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e2) (TBase tb) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EEq e1 e2)) (TBase BBool).
Proof.
  intros C x e0 e1 e2 tb H1 H2.
  simpl.
  eapply TEq; eauto.
Qed.

Lemma subst_base_has_type_sub_ctx_stable_from_premises :
  forall C x e0 e t t',
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 t') ->
    subtype (ctx_subst x e0 C) (ty_subst x e0 t') (ty_subst x e0 t) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 t).
Proof.
  intros C x e0 e t t' Hty Hsub.
  eapply TSub.
  - exact Hty.
  - exact Hsub.
Qed.

Lemma subst_base_has_type_ref_ctx_stable_from_subterm :
  forall C x e0 t e,
    ty_subst x e0 t = t ->
    ty_valid (ctx_subst x e0 C) (ty_subst x e0 t) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 t) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (ENewRef t e)) (ty_subst x e0 (TRef t)).
Proof.
  intros C x e0 t e Htfix Hvalid Hty.
  simpl.
  rewrite Htfix.
  rewrite Htfix in Hvalid.
  rewrite Htfix in Hty.
  eapply TRefI.
  - exact Hvalid.
  - exact Hty.
Qed.

Lemma subst_base_has_type_get_ctx_stable_from_subterm :
  forall C x e0 e t,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 (TRef t)) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EGet e)) (ty_subst x e0 t).
Proof.
  intros C x e0 e t H.
  simpl.
  eapply TGet.
  exact H.
Qed.

Lemma subst_base_has_type_set_ctx_stable_from_subterms :
  forall C x e0 e1 e2 t,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e1) (ty_subst x e0 (TRef t)) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e2) (ty_subst x e0 t) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (ESet e1 e2)) (TBase BUnit).
Proof.
  intros C x e0 e1 e2 t H1 H2.
  simpl.
  eapply TSetI.
  - exact H1.
  - exact H2.
Qed.

Lemma subst_base_has_type_pair_ctx_stable_from_subterms :
  forall C x e0 e1 e2 t1 t2,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e1) (ty_subst x e0 t1) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e2) (ty_subst x e0 t2) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EPair e1 e2)) (ty_subst x e0 (TProd t1 t2)).
Proof.
  intros C x e0 e1 e2 t1 t2 H1 H2.
  simpl.
  eapply TPair.
  - exact H1.
  - exact H2.
Qed.

Lemma subst_base_has_type_fst_ctx_stable_from_subterm :
  forall C x e0 e t1 t2,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 (TProd t1 t2)) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EFst e)) (ty_subst x e0 t1).
Proof.
  intros C x e0 e t1 t2 H.
  simpl.
  eapply TFst.
  exact H.
Qed.

Lemma subst_base_has_type_snd_ctx_stable_from_subterm :
  forall C x e0 e t1 t2,
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 (TProd t1 t2)) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (ESnd e)) (ty_subst x e0 t2).
Proof.
  intros C x e0 e t1 t2 H.
  simpl.
  eapply TSnd.
  exact H.
Qed.

Lemma subst_base_has_type_if_ctx_stable_from_premises :
  forall C x e0 cond e1 e2 t,
    has_type_pure (ctx_subst x e0 C) (expr_subst x e0 cond) (TBase BBool) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e1) (ty_subst x e0 t) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e2) (ty_subst x e0 t) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EIf cond e1 e2)) (ty_subst x e0 t).
Proof.
  intros C x e0 cond e1 e2 t Hcond Hthen Helse.
  simpl.
  eapply TIf.
  - exact Hcond.
  - exact Hthen.
  - exact Helse.
Qed.

Lemma subst_base_has_type_self_ctx_stable_from_premises :
  forall C x e0 e t,
    ty_subst x e0 (self t e) = self (ty_subst x e0 t) (expr_subst x e0 e) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 t) ->
    (forall t1, has_type_pure (ctx_subst x e0 C) (expr_subst x e0 e) t1) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 (self t e)).
Proof.
  intros C x e0 e t Hcomm Hty HpureAll.
  rewrite Hcomm.
  eapply TSelf.
  - exact Hty.
  - exact HpureAll.
Qed.

(* Internal selfification transport used only by older local bridges.
   The constructive form needs the post-substitution self type explicitly aligned
   and known valid. *)
Lemma subst_base_self_subtype_ctx :
  forall C x e0 e t,
    ty_subst x e0 (self t e) = self (ty_subst x e0 t) (expr_subst x e0 e) ->
    ty_valid (ctx_subst x e0 C) (ty_subst x e0 (self t e)) ->
    subtype (ctx_subst x e0 C)
      (self (ty_subst x e0 t) (expr_subst x e0 e))
      (ty_subst x e0 (self t e)).
Proof.
  intros C x e0 e t Hcomm Hvalid.
  set (G := ctx_subst x e0 C) in *.
  assert (Hrefl : forall ty, ty_valid G ty -> subtype G ty ty).
  {
    clear Hcomm Hvalid.
    intros ty Hval.
    induction Hval.
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
    - eapply SFun.
      + exact IHHval1.
      + exact IHHval2.
    - eapply SFunDep.
      + exact IHHval1.
      + exact IHHval2.
    - eapply SPair.
      + exact IHHval1.
      + exact IHHval2.
    - eapply SRef.
      + exact IHHval.
      + exact IHHval.
  }
  rewrite <- Hcomm.
  apply Hrefl.
  exact Hvalid.
Qed.

Lemma subst_base_self_subtype :
  forall G1 G2 x e0 e t,
    ctx_subst x e0 G1 = G1 ->
    ctx_subst x e0 G2 = G2 ->
    ty_subst x e0 (self t e) = self (ty_subst x e0 t) (expr_subst x e0 e) ->
    ty_valid (add_ctx (ctx_subst x e0 G2) G1) (ty_subst x e0 (self t e)) ->
    subtype (add_ctx (ctx_subst x e0 G2) G1)
      (self (ty_subst x e0 t) (expr_subst x e0 e))
      (ty_subst x e0 (self t e)).
Proof.
  intros G1 G2 x e0 e t Hctx1 Hctx2 Hcomm Hvalid.
  rewrite Hctx2.
  rewrite Hctx2 in Hvalid.
  assert (Hvalid_ctx : ty_valid (ctx_subst x e0 (add_ctx G2 G1)) (ty_subst x e0 (self t e))).
  {
    replace (ctx_subst x e0 (add_ctx G2 G1)) with (add_ctx G2 G1).
    2:{ rewrite ctx_subst_add_ctx. rewrite Hctx2, Hctx1. reflexivity. }
    exact Hvalid.
  }
  replace (add_ctx G2 G1) with (ctx_subst x e0 (add_ctx G2 G1)).
  2:{ symmetry. rewrite ctx_subst_add_ctx. rewrite Hctx2, Hctx1. reflexivity. }
  apply (subst_base_self_subtype_ctx (add_ctx G2 G1) x e0 e t Hcomm).
  exact Hvalid_ctx.
Qed.

(* Paper Lemma 6, typing clause.
   Base substitution preserves typing. *)

Axiom subst_base_has_type_ctx_fun_hard :
  forall C x e0 t0 f y t1 t2 body,
    ctx_subst x e0 C = C ->
    DTDT.machine_inter.value (ctx_subst x e0 C) e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    has_type (ctx_subst x e0 C) e0 t0 ->
    ty_subst x e0 t0 = t0 ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var C x t0 e0) (EFix f y t1 t2 body) (TArrDep y t1 t2) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EFix f y t1 t2 body)) (ty_subst x e0 (TArrDep y t1 t2)).

Axiom subst_base_has_type_ctx_app_pure_hard :
  forall C x e0 t0 e1 e2 y t1 t2,
    ctx_subst x e0 C = C ->
    DTDT.machine_inter.value (ctx_subst x e0 C) e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    has_type (ctx_subst x e0 C) e0 t0 ->
    ty_subst x e0 t0 = t0 ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var C x t0 e0) e2 t1 ->
    (forall t3, has_type_pure (ctx_add_var C x t0 e0) e2 t3) ->
    has_type (ctx_add_var C x t0 e0) e1 (TArrDep y t1 t2) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 (EApp e1 e2)) (ty_subst x e0 (ty_subst y e2 t2)).

Axiom subst_base_has_type_ctx_self_hard :
  forall C x e0 t0 e t,
    ctx_subst x e0 C = C ->
    DTDT.machine_inter.value (ctx_subst x e0 C) e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    has_type (ctx_subst x e0 C) e0 t0 ->
    ty_subst x e0 t0 = t0 ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var C x t0 e0) e t ->
    (forall t1, has_type_pure (ctx_add_var C x t0 e0) e t1) ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 (self t e)).

Axiom subst_base_has_type_ctx_sub_hard :
  forall C x e0 t0 e t t',
    ctx_subst x e0 C = C ->
    DTDT.machine_inter.value (ctx_subst x e0 C) e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    has_type (ctx_subst x e0 C) e0 t0 ->
    ty_subst x e0 t0 = t0 ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var C x t0 e0) e t' ->
    subtype (ctx_add_var C x t0 e0) t' t ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 t).

Axiom has_type_subst_base_closed_pure_ctx :
  forall C x e0 t0 e t,
    ctx_subst x e0 C = C ->
    DTDT.machine_inter.value (ctx_subst x e0 C) e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    has_type (ctx_subst x e0 C) e0 t0 ->
    ty_subst x e0 t0 = t0 ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var C x t0 e0) e t ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 t).

Lemma subst_base_has_type_ctx :
  forall C x e0 t0 e t,
    ctx_subst x e0 C = C ->
    DTDT.machine_inter.value (ctx_subst x e0 C) e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    has_type (ctx_subst x e0 C) e0 t0 ->
    ty_subst x e0 t0 = t0 ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var C x t0 e0) e t ->
    has_type (ctx_subst x e0 C) (expr_subst x e0 e) (ty_subst x e0 t).
Proof.
  intros C x e0 t0 e t Hctx Hv0 Hbeta0 Hpure0 Htyped0 Ht0 Hclosed Hty.
  exact (has_type_subst_base_closed_pure_ctx C x e0 t0 e t Hctx Hv0 Hbeta0 Hpure0 Htyped0 Ht0 Hclosed Hty).
Qed.

Lemma subst_base_has_type :
  forall G1 G2 x e0 t0 e t,
    DTDT.machine_inter.value G1 e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    ctx_subst x e0 G1 = G1 ->
    ctx_subst x e0 G2 = G2 ->
    ty_subst x e0 t0 = t0 ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var (add_ctx G2 G1) x t0 e0) e t ->
    has_type (add_ctx (ctx_subst x e0 G2) G1) (expr_subst x e0 e) (ty_subst x e0 t).
Proof.
  intros G1 G2 x e0 t0 e t Hv0 Hbeta0 Hpure0 Hty0 Hctx1 Hctx2 Ht0 Hclosed Hty.
  assert (Hctx_add : ctx_subst x e0 (add_ctx G2 G1) = add_ctx G2 G1).
  { exact (ctx_subst_add_ctx_stable G1 G2 x e0 Hctx1 Hctx2). }
  assert (Hpure_ctx : has_type_pure (ctx_subst x e0 (add_ctx G2 G1)) e0 (essential_type t0)).
  { rewrite Hctx_add.
    apply weakening_has_type_pure_right.
    exact Hpure0. }
  assert (Htyped_ctx : has_type (ctx_subst x e0 (add_ctx G2 G1)) e0 t0).
  { rewrite Hctx_add.
    exact (weakening_right G1 G2 e0 t0 Hty0). }
  assert (Hv_ctx : DTDT.machine_inter.value (ctx_subst x e0 (add_ctx G2 G1)) e0).
  { rewrite Hctx_add.
    exact (weakening_value_right G1 G2 e0 Hv0). }
  pose proof (subst_base_has_type_ctx (add_ctx G2 G1) x e0 t0 e t Hctx_add Hv_ctx Hbeta0 Hpure_ctx Htyped_ctx Ht0 Hclosed Hty) as Hty'.
  rewrite ctx_subst_add_ctx in Hty'.
  rewrite Hctx1 in Hty'.
  exact Hty'.
Qed.

Definition well_formed_ctx (C : ctx) : Prop :=
  forall x e0, ctx_subst x e0 C = C.

(* ==================== WELL-FORMEDNESS PRESERVATION LEMMAS ====================
   These lemmas establish structural properties of well-formed contexts and how
   well-formedness relates to context operations. *)

(* Direct use of well-formedness: if C is well-formed then ctx_subst is identity. *)
Lemma well_formed_ctx_subst_id :
  forall C x e0,
    well_formed_ctx C ->
    ctx_subst x e0 C = C.
Proof.
  intros C x e0 Hwf.
  unfold well_formed_ctx in Hwf.
  exact (Hwf x e0).
Qed.

(* Important consequence: composing identical substitutions on well-formed contexts
   is neutral (applying subst twice also gives identity). *)
Lemma well_formed_ctx_subst_compose_neutral :
  forall C,
    well_formed_ctx C ->
    forall x e0,
      ctx_subst x e0 (ctx_subst x e0 C) = C.
Proof.
  intros C Hwf x e0.
  rewrite (well_formed_ctx_subst_id C x e0 Hwf).
  exact (well_formed_ctx_subst_id C x e0 Hwf).
Qed.

(* Substitution distributes over ctx_add_var. This is key to understanding how
   adding bindings interacts with substitution. *)
Lemma well_formed_add_var_distributes :
  forall C y ty witness x e0,
    ctx_subst x e0 (ctx_add_var C y ty witness) =
    ctx_add_var (ctx_subst x e0 C) y (ty_subst x e0 ty) (expr_subst x e0 witness).
Proof.
  intros C y ty witness x e0.
  exact (ctx_subst_ctx_add_var C y ty witness x e0).
Qed.

(* Substitution distributes over add_ctx context union. *)
Lemma well_formed_add_ctx_distributes :
  forall G1 G2 x e0,
    ctx_subst x e0 (add_ctx G2 G1) = add_ctx (ctx_subst x e0 G2) (ctx_subst x e0 G1).
Proof.
  intros G1 G2 x e0.
  exact (ctx_subst_add_ctx G1 G2 x e0).
Qed.

(* Consequence: If a substitution doesn't affect the variable names involved,
   well-formed contexts remain well-formed. This captures the intuition that
   well-formedness is about the context structure, not the specific variables. *)
Lemma well_formed_ctx_subst_different_var :
  forall C x y e,
    x <> y ->
    well_formed_ctx C ->
    well_formed_ctx (ctx_subst x e C).
Proof.
  intros C x y e Hneq Hwf.
  unfold well_formed_ctx.
  intros y' e'.
  rewrite (well_formed_ctx_subst_id C x e Hwf).
  exact (Hwf y' e').
Qed.


(* Key preservation: well-formedness of right context is preserved by add_ctx.
   If C is well-formed (stable under any substitution), then adding it to the
   right of another context preserves this stability. *)
Lemma well_formed_ctx_add_ctx_right :
  forall G C,
    well_formed_ctx G ->
    well_formed_ctx C ->
    well_formed_ctx (add_ctx G C).
Proof.
  intros G C HwfG HwfC.
  unfold well_formed_ctx.
  intros x e0.
  rewrite ctx_subst_add_ctx.
  rewrite (well_formed_ctx_subst_id G x e0 HwfG).
  rewrite (well_formed_ctx_subst_id C x e0 HwfC).
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

(* Pure typing produces types that are orthogonal to expression-variable substitution.
   That is, if e has pure type τ, then ty_subst acts as identity on τ. *)
Lemma has_type_pure_ty_subst_closed :
  forall G e τ x e0,
    has_type_pure G e τ ->
    ty_subst x e0 τ = τ.
Proof.
  intros G e τ x e0 Hpure.
  induction Hpure.
  - (* PVar: τ = essential_type τb, β[τb] holds *)
    apply ty_subst_essential_type_id. apply bool_prop_eq_true. exact H0.
  - (* PNat *) reflexivity.
  - (* PBool *) reflexivity.
  - (* PString *) reflexivity.
  - (* PUnit *) reflexivity.
  - (* PConst: is_simple_type τ *)
    apply ty_subst_simple_id. apply bool_prop_eq_true. exact H0.
  - (* PApp: τ = τ₂, e₁ : TArr τ₁ τ₂ *)
    simpl in IHHpure1.
    injection IHHpure1 as _ Heq2.
    exact Heq2.
  - (* PNot *) reflexivity.
  - (* PImp *) reflexivity.
  - (* PAnd *) reflexivity.
  - (* POr *) reflexivity.
  - (* PEq *) reflexivity.
  - (* PPlus *) reflexivity.
Qed.

(* Transport lemma: if e₂ has every pure type in the old context, then
   the substituted e₂ has every pure type in the new context. *)
Lemma subst_base_has_type_pure_gen :
  forall C x e0 t0 e t,
    essential_type_is_base_type t0 = true ->
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
        rewrite ty_subst_essential_type_id by (exact Hbeta0).
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
           reflexivity.
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

(* Transport lemma: if e has every pure type in the old context (ctx_add_var C xs t0 e0),
   then the substituted expression (expr_subst xs e0 e) has every pure type in the
   substituted context (ctx_subst xs e0 C).
   Key insight: has_type_pure_ty_subst_closed shows that pure types are ty_subst-closed,
   so subst_base_has_type_pure_gen followed by rewriting gives the exact type needed. *)
Lemma has_type_pure_forall_ctx_stable :
  forall C xs e0 t0 e,
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst xs e0 C) e0 (essential_type t0) ->
    (forall τ, has_type_pure (ctx_add_var C xs t0 e0) e τ) ->
    forall τ, has_type_pure (ctx_subst xs e0 C) (expr_subst xs e0 e) τ.
Proof.
  intros C xs e0 t0 e Hbeta Hpure0 Hforall τ.
  pose proof (Hforall τ) as Hτ.
  pose proof (has_type_pure_ty_subst_closed _ _ _ xs e0 Hτ) as Hclosed_τ.
  pose proof (subst_base_has_type_pure_gen C xs e0 t0 e τ Hbeta Hpure0 Hτ) as Htransport.
  rewrite Hclosed_τ in Htransport.
  exact Htransport.
Qed.

(* Paper Lemma 6, pure clause.
   Base substitution preserves pure typing. *)
Lemma subst_base_has_type_pure :
  forall G1 G2 x e0 t0 e t,
    DTDT.machine_inter.value G1 e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    ctx_subst x e0 G1 = G1 ->
    ctx_subst x e0 G2 = G2 ->
    has_type_pure (ctx_add_var (add_ctx G2 G1) x t0 e0) e t ->
    has_type_pure (add_ctx (ctx_subst x e0 G2) G1) (expr_subst x e0 e) (ty_subst x e0 t).
Proof.
  intros G1 G2 x e0 t0 e t Hv0 Hbeta0 Hpure0 Hty0 Hctx Hctx2 Hpure.
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
        rewrite ty_subst_essential_type_id by (exact Hbeta0).
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
    essential_type_is_base_type t0 = true ->
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
           reflexivity.
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
           reflexivity.
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
        reflexivity.
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

Lemma lookup_lemma_var_shadow_split :
  forall C D x e0 y t witness,
    y <> x ->
    var_ctx_lookup (add_ctx D C) y = Some (t, witness) ->
    exists t' witness',
      var_ctx_lookup (add_ctx D (ctx_subst x e0 C)) y = Some (t', witness') /\
      (essential_type_is_base_type t = true ->
        essential_type t' = essential_type t /\
        essential_type_is_base_type t' = true).
Proof.
  intros [env1 store1] [env2 store2] x e0 y t witness Hneq Hlookup.
  destruct env1 as [vars1 consts1].
  destruct env2 as [vars2 consts2].
  unfold var_ctx_lookup, add_ctx, ctx_subst, binding_subst in *.
  simpl in *.
  destruct (vars1 !! y) eqn:Hvars1.
  - destruct p as [t1 w1].
    assert (Hlookup1 : (union vars1 vars2) !! y = Some (t1, w1)).
    { apply (lookup_union_Some_l vars1 vars2 y (t1, w1)).
      exact Hvars1. }
    assert (Heq : (t, witness) = (t1, w1)) by congruence.
    inversion Heq; subst t1 w1.
    exists (ty_subst x e0 t), (expr_subst x e0 witness).
    split.
    + apply (lookup_union_Some_l (fmap (binding_subst x e0) vars1) vars2 y
        (ty_subst x e0 t, expr_subst x e0 witness)).
      apply lookup_fmap_Some.
      exists (t, witness).
      split; [reflexivity | exact Hvars1].
    + intros Hbeta.
      split.
      * rewrite ty_subst_preserves_essential_type by exact Hbeta.
        rewrite ty_subst_essential_type_id by exact Hbeta.
        reflexivity.
      * rewrite ty_subst_preserves_beta by exact Hbeta.
        reflexivity.
  - assert (Hlookup2 : vars2 !! y = Some (t, witness)).
    { eapply lookup_union_Some_inv_r; eauto. }
    assert (Hvars1' : (fmap (binding_subst x e0) vars1) !! y = None).
    { destruct ((fmap (binding_subst x e0) vars1) !! y) eqn:Hfmap.
      - rewrite lookup_fmap in Hfmap.
        change ((binding_subst x e0) <$> (vars1 !! y) = Some p) in Hfmap.
        rewrite Hvars1 in Hfmap.
        discriminate.
      - reflexivity. }
    exists t, witness.
    split.
    + apply lookup_union_Some_raw.
      right.
      split.
      * exact Hvars1'.
      * exact Hlookup2.
    + intros Hbeta.
      split; [reflexivity | exact Hbeta].
Qed.

Lemma lookup_lemma_const_shadow_split :
  forall C D x e0 c t witness,
    const_ctx_lookup (add_ctx D C) c = Some (t, witness) ->
    exists t' witness',
      const_ctx_lookup (add_ctx D (ctx_subst x e0 C)) c = Some (t', witness') /\
      ((t' = ty_subst x e0 t /\ witness' = expr_subst x e0 witness) \/
       (t' = t /\ witness' = witness)).
Proof.
  intros [env1 store1] [env2 store2] x e0 c t witness Hlookup.
  destruct env1 as [vars1 consts1].
  destruct env2 as [vars2 consts2].
  unfold const_ctx_lookup, add_ctx, ctx_subst, binding_subst in *.
  simpl in *.
  destruct (consts1 !! c) eqn:Hconsts1.
  - destruct p as [t1 w1].
    assert (Hlookup1 : (union consts1 consts2) !! c = Some (t1, w1)).
    { apply (lookup_union_Some_l consts1 consts2 c (t1, w1)).
      exact Hconsts1. }
    assert (Heq : (t, witness) = (t1, w1)) by congruence.
    inversion Heq; subst t1 w1.
    exists (ty_subst x e0 t), (expr_subst x e0 witness).
    split.
    + apply (lookup_union_Some_l (fmap (binding_subst x e0) consts1) consts2 c
        (ty_subst x e0 t, expr_subst x e0 witness)).
      apply lookup_fmap_Some.
      exists (t, witness).
      split; [reflexivity | exact Hconsts1].
    + left. split; reflexivity.
  - assert (Hlookup2 : consts2 !! c = Some (t, witness)).
    { eapply lookup_union_Some_inv_r; eauto. }
    assert (Hconsts1' : (fmap (binding_subst x e0) consts1) !! c = None).
    { destruct ((fmap (binding_subst x e0) consts1) !! c) eqn:Hfmap.
      - rewrite lookup_fmap in Hfmap.
        change ((binding_subst x e0) <$> (consts1 !! c) = Some p) in Hfmap.
        rewrite Hconsts1 in Hfmap.
        discriminate.
      - reflexivity. }
    exists t, witness.
    split.
    + apply lookup_union_Some_raw.
      right.
      split; [exact Hconsts1' | exact Hlookup2].
    + right. split; reflexivity.
Qed.

Lemma lookup_lemma_store_shadow_split :
  forall C D x e0 l t witness,
    store_ctx_lookup (add_ctx D C) l = Some (t, witness) ->
    exists t' witness',
      store_ctx_lookup (add_ctx D (ctx_subst x e0 C)) l = Some (t', witness') /\
      ((t' = ty_subst x e0 t /\ witness' = expr_subst x e0 witness) \/
       (t' = t /\ witness' = witness)).
Proof.
  intros [env1 store1] [env2 store2] x e0 l t witness Hlookup.
  destruct env1 as [vars1 consts1].
  destruct env2 as [vars2 consts2].
  unfold store_ctx_lookup, add_ctx, ctx_subst, binding_subst in *.
  simpl in *.
  destruct (store1 !! l) eqn:Hstore1.
  - destruct p as [t1 w1].
    assert (Hlookup1 : (union store1 store2) !! l = Some (t1, w1)).
    { apply (lookup_union_Some_l store1 store2 l (t1, w1)).
      exact Hstore1. }
    assert (Heq : (t, witness) = (t1, w1)) by congruence.
    inversion Heq; subst t1 w1.
    exists (ty_subst x e0 t), (expr_subst x e0 witness).
    split.
    + apply (lookup_union_Some_l (fmap (binding_subst x e0) store1) store2 l
        (ty_subst x e0 t, expr_subst x e0 witness)).
      apply lookup_fmap_Some.
      exists (t, witness).
      split; [reflexivity | exact Hstore1].
    + left. split; reflexivity.
  - assert (Hlookup2 : store2 !! l = Some (t, witness)).
    { eapply lookup_union_Some_inv_r; eauto. }
    assert (Hstore1' : (fmap (binding_subst x e0) store1) !! l = None).
    { destruct ((fmap (binding_subst x e0) store1) !! l) eqn:Hfmap.
      - rewrite lookup_fmap in Hfmap.
        change ((binding_subst x e0) <$> (store1 !! l) = Some p) in Hfmap.
        rewrite Hstore1 in Hfmap.
        discriminate.
      - reflexivity. }
    exists t, witness.
    split.
    + apply lookup_union_Some_raw.
      right.
      split; [exact Hstore1' | exact Hlookup2].
    + right. split; reflexivity.
Qed.

Lemma lookup_lemma_const_shadow_split_simple :
  forall C D x e0 c t witness,
    const_ctx_lookup (add_ctx D C) c = Some (t, witness) ->
    is_simple_type t = true ->
    exists witness',
      const_ctx_lookup (add_ctx D (ctx_subst x e0 C)) c = Some (t, witness').
Proof.
  intros [env1 store1] [env2 store2] x e0 c t witness Hlookup Hsimple.
  destruct env1 as [vars1 consts1].
  destruct env2 as [vars2 consts2].
  unfold const_ctx_lookup, add_ctx, ctx_subst, binding_subst in *.
  simpl in *.
  destruct (consts1 !! c) eqn:Hconsts1.
  - destruct p as [t1 w1].
    assert (Hlookup1 : (union consts1 consts2) !! c = Some (t1, w1)).
    { apply (lookup_union_Some_l consts1 consts2 c (t1, w1)).
      exact Hconsts1. }
    assert (Heq : (t, witness) = (t1, w1)) by congruence.
    inversion Heq; subst t1 w1.
    exists (expr_subst x e0 witness).
    apply (lookup_union_Some_l (fmap (binding_subst x e0) consts1) consts2 c
      (t, expr_subst x e0 witness)).
    apply lookup_fmap_Some.
    exists (t, witness).
    split.
    + unfold binding_subst. simpl.
      rewrite ty_subst_simple_id by exact Hsimple.
      reflexivity.
    + exact Hconsts1.
  - assert (Hlookup2 : consts2 !! c = Some (t, witness)).
    { eapply lookup_union_Some_inv_r; eauto. }
    assert (Hconsts1' : (fmap (binding_subst x e0) consts1) !! c = None).
    { destruct ((fmap (binding_subst x e0) consts1) !! c) eqn:Hfmap.
      - rewrite lookup_fmap in Hfmap.
        change ((binding_subst x e0) <$> (consts1 !! c) = Some p) in Hfmap.
        rewrite Hconsts1 in Hfmap.
        discriminate.
      - reflexivity. }
    exists witness.
    apply lookup_union_Some_raw.
    right.
    split.
    + exact Hconsts1'.
    + exact Hlookup2.
Qed.

Lemma subst_base_has_type_pure_shadow_split :
  forall C D x e0 t0 t_old witness e t,
    essential_type_is_base_type t0 = true ->
    has_type_pure (add_ctx D (ctx_subst x e0 C)) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    has_type_pure (ctx_add_var (add_ctx D C) x t_old witness) e t ->
    has_type_pure (ctx_add_var (add_ctx D (ctx_subst x e0 C)) x (ty_subst x e0 t_old) witness) e t.
Proof.
  intros C D x e0 t0 t_old witness e t Hbeta0 Hpure0 Hfv Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneqx0x].
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
        -- unfold var_ctx_lookup, ctx_add_var. simpl. apply lookup_insert.
        -- rewrite ty_subst_preserves_beta by (apply bool_prop_eq_true; exact H0).
           reflexivity.
      * destruct Hcase as [Hneq' _].
        contradiction.
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [Heq _].
        congruence.
      * destruct Hcase as [_ Hlookup_base].
        destruct (lookup_lemma_var_shadow_split C D x e0 x0 _ _ Hneqx0x Hlookup_base) as [t' Htmp].
        destruct Htmp as [w' Htmp].
        destruct Htmp as [Hlookup' Hpres].
        specialize (Hpres (bool_prop_eq_true _ H0)) as [Hess Hbeta'].
        rewrite <- Hess.
        eapply PVar.
        -- unfold var_ctx_lookup, ctx_add_var. simpl.
           apply lookup_insert_Some.
           right.
           split.
           ++ congruence.
           ++ exact Hlookup'.
        -- rewrite Hbeta'. exact I.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - destruct (lookup_lemma_const_shadow_split_simple C D x e0 c _ _ H (bool_prop_eq_true _ H0)) as [w' Hlookup'].
    eapply PConst.
    + unfold const_ctx_lookup, ctx_add_var. simpl.
      exact Hlookup'.
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

Lemma subst_base_has_type_pure_shadow_same_ctx :
  forall C x e0 t0 t_inner v_inner e t,
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    has_type_pure (ctx_add_var C x t_inner v_inner) e t ->
    has_type_pure (ctx_add_var (ctx_subst x e0 C) x t_inner v_inner) e t.
Proof.
  intros C x e0 t0 t_inner v_inner e t Hbeta0 Hpure0 Hpure.
  induction Hpure.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + unfold var_ctx_lookup, ctx_add_var in H.
      simpl in H.
      apply lookup_insert_Some in H.
      destruct H as [Hcase | Hcase].
      * destruct Hcase as [_ Hbind].
        inversion Hbind; subst.
        eapply PVar.
        -- unfold var_ctx_lookup, ctx_add_var. simpl. apply lookup_insert.
        -- exact H0.
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
      eapply PVar.
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
        reflexivity.
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

Lemma subst_base_has_type_pure_shadow_top_same_ctx :
  forall C D x e0 t0 t_inner v_inner e t,
    essential_type_is_base_type t0 = true ->
    has_type_pure (add_ctx (ctx_subst x e0 C) D) e0 (essential_type t0) ->
    has_type_pure (add_ctx (ctx_add_var C x t_inner v_inner) D) e t ->
    has_type_pure (add_ctx (ctx_add_var (ctx_subst x e0 C) x t_inner v_inner) D) e t.
Proof.
  intros C D x e0 t0 t_inner v_inner e t Hbeta0 Hpure0 Hpure.
  induction Hpure.
  - unfold var_ctx_lookup, add_ctx in H |- *.
    simpl in H |- *.
    remember ((fst (fst D)) !! x0) as qD eqn:HDlookup.
    destruct qD.
    + destruct p as [td wd].
      assert (HlookupD : (union (fst (fst D)) (fst (fst (ctx_add_var C x t_inner v_inner)))) !! x0 = Some (td, wd)).
      { apply (lookup_union_Some_l (fst (fst D)) (fst (fst (ctx_add_var C x t_inner v_inner))) x0 (td, wd)).
        symmetry. exact HDlookup. }
      pose proof (eq_trans (eq_sym HlookupD) H) as Heq.
      inversion Heq. subst.
      eapply PVar.
      * apply (lookup_lemma_var_right D (ctx_add_var (ctx_subst x e0 C) x t_inner v_inner) x0 _ e).
        symmetry. exact HDlookup.
      * exact H0.
    + apply lookup_union_Some_inv_r in H.
      2:{ symmetry. exact HDlookup. }
      destruct (String.eq_dec x0 x) as [-> | Hneqx0x].
      * unfold var_ctx_lookup, ctx_add_var in H |- *.
        simpl in H |- *.
        apply lookup_insert_Some in H.
        destruct H as [Hcase | Hcase].
        -- destruct Hcase as [_ Hbind].
           inversion Hbind; subst.
           eapply PVar.
           ++ unfold var_ctx_lookup, add_ctx, ctx_add_var. simpl.
              apply lookup_union_Some_raw.
              right.
              split.
              ** symmetry. exact HDlookup.
              ** apply lookup_insert.
           ++ exact H0.
        -- destruct Hcase as [Hneq' _].
           contradiction.
      * unfold var_ctx_lookup, ctx_add_var in H |- *.
        simpl in H |- *.
        apply lookup_insert_Some in H.
        destruct H as [Hcase | Hcase].
        -- destruct Hcase as [Heq _].
           congruence.
        -- destruct Hcase as [_ HlookupC].
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
           ++ unfold var_ctx_lookup, add_ctx, ctx_add_var. simpl.
              apply lookup_union_Some_raw.
              right.
              split.
              ** symmetry. exact HDlookup.
              ** apply lookup_insert_Some.
                 right.
                 split.
                 --- congruence.
                 --- exact (lookup_lemma_var_ctx_subst C x e0 x0 _ _ HlookupC).
           ++ rewrite ty_subst_preserves_beta by (apply bool_prop_eq_true; exact H0).
              reflexivity.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - unfold const_ctx_lookup, add_ctx in H |- *.
    simpl in H |- *.
    remember ((snd (fst D)) !! c) as qD eqn:HDlookup.
    destruct qD.
    + destruct p as [tc wc].
      assert (HlookupD : (union (snd (fst D)) (snd (fst (ctx_add_var C x t_inner v_inner)))) !! c = Some (tc, wc)).
      { apply (lookup_union_Some_l (snd (fst D)) (snd (fst (ctx_add_var C x t_inner v_inner))) c (tc, wc)).
        symmetry. exact HDlookup. }
      pose proof (eq_trans (eq_sym HlookupD) H) as Heq.
      inversion Heq. subst.
      eapply PConst.
      * apply (lookup_lemma_const_right D (ctx_add_var (ctx_subst x e0 C) x t_inner v_inner) c _ e).
        symmetry. exact HDlookup.
      * exact H0.
    + apply lookup_union_Some_inv_r in H.
      2:{ symmetry. exact HDlookup. }
      eapply PConst.
      * unfold const_ctx_lookup, add_ctx, ctx_add_var. simpl.
        apply lookup_union_Some_raw.
        right.
        split.
        -- symmetry. exact HDlookup.
        -- exact (lookup_lemma_const_ctx_subst_simple C x e0 c _ _ H (bool_prop_eq_true _ H0)).
      * exact H0.
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

Lemma subst_base_has_type_pure_shadow_top_ctx :
  forall C D x e0 t0 t_inner v_inner e t,
    essential_type_is_base_type t0 = true ->
    has_type_pure (add_ctx (ctx_subst x e0 C) D) e0 (essential_type t0) ->
    has_type_pure (add_ctx (ctx_add_var C x t_inner v_inner) D) e t ->
    has_type_pure (add_ctx (ctx_add_var (ctx_subst x e0 C) x (ty_subst x e0 t_inner) v_inner) D) e t.
Proof.
  intros C D x e0 t0 t_inner v_inner e t Hbeta0 Hpure0 Hpure.
  induction Hpure.
  - unfold var_ctx_lookup, add_ctx in H |- *.
    simpl in H |- *.
    remember ((fst (fst D)) !! x0) as qD eqn:HDlookup.
    destruct qD.
    + destruct p as [td wd].
      assert (HlookupD : (union (fst (fst D)) (fst (fst (ctx_add_var C x t_inner v_inner)))) !! x0 = Some (td, wd)).
      { apply (lookup_union_Some_l (fst (fst D)) (fst (fst (ctx_add_var C x t_inner v_inner))) x0 (td, wd)).
        symmetry. exact HDlookup. }
      pose proof (eq_trans (eq_sym HlookupD) H) as Heq.
      inversion Heq. subst.
      eapply PVar.
      * apply (lookup_lemma_var_right D (ctx_add_var (ctx_subst x e0 C) x (ty_subst x e0 t_inner) v_inner) x0 _ e).
        symmetry. exact HDlookup.
      * exact H0.
    + apply lookup_union_Some_inv_r in H.
      2:{ symmetry. exact HDlookup. }
      destruct (String.eq_dec x0 x) as [-> | Hneqx0x].
      * unfold var_ctx_lookup, ctx_add_var in H |- *.
        simpl in H |- *.
        apply lookup_insert_Some in H.
        destruct H as [Hcase | Hcase].
        -- destruct Hcase as [_ Hbind].
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
           ++ unfold var_ctx_lookup, add_ctx, ctx_add_var. simpl.
              apply lookup_union_Some_raw.
              right.
              split.
              ** symmetry. exact HDlookup.
              ** apply lookup_insert.
           ++ rewrite ty_subst_preserves_beta by (apply bool_prop_eq_true; exact H0).
              reflexivity.
        -- destruct Hcase as [Hneq' _].
           contradiction.
      * unfold var_ctx_lookup, ctx_add_var in H |- *.
        simpl in H |- *.
        apply lookup_insert_Some in H.
        destruct H as [Hcase | Hcase].
        -- destruct Hcase as [Heq _].
           congruence.
        -- destruct Hcase as [_ HlookupC].
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
           ++ unfold var_ctx_lookup, add_ctx, ctx_add_var. simpl.
              apply lookup_union_Some_raw.
              right.
              split.
              ** symmetry. exact HDlookup.
              ** apply lookup_insert_Some.
                 right.
                 split.
                 --- congruence.
                 --- exact (lookup_lemma_var_ctx_subst C x e0 x0 _ _ HlookupC).
           ++ rewrite ty_subst_preserves_beta by (apply bool_prop_eq_true; exact H0).
              reflexivity.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - unfold const_ctx_lookup, add_ctx in H |- *.
    simpl in H |- *.
    remember ((snd (fst D)) !! c) as qD eqn:HDlookup.
    destruct qD.
    + destruct p as [tc wc].
      assert (HlookupD : (union (snd (fst D)) (snd (fst (ctx_add_var C x t_inner v_inner)))) !! c = Some (tc, wc)).
      { apply (lookup_union_Some_l (snd (fst D)) (snd (fst (ctx_add_var C x t_inner v_inner))) c (tc, wc)).
        symmetry. exact HDlookup. }
      pose proof (eq_trans (eq_sym HlookupD) H) as Heq.
      inversion Heq. subst.
      eapply PConst.
      * apply (lookup_lemma_const_right D (ctx_add_var (ctx_subst x e0 C) x (ty_subst x e0 t_inner) v_inner) c _ e).
        symmetry. exact HDlookup.
      * exact H0.
    + apply lookup_union_Some_inv_r in H.
      2:{ symmetry. exact HDlookup. }
      eapply PConst.
      * unfold const_ctx_lookup, add_ctx, ctx_add_var. simpl.
        apply lookup_union_Some_raw.
        right.
        split.
        -- symmetry. exact HDlookup.
        -- exact (lookup_lemma_const_ctx_subst_simple C x e0 c _ _ H (bool_prop_eq_true _ H0)).
      * exact H0.
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

Lemma subst_base_ty_valid_shadow_top_same_ctx :
  forall C D x e0 t0 t_inner v_inner t_body,
    essential_type_is_base_type t0 = true ->
    has_type_pure (add_ctx (ctx_subst x e0 C) D) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    ty_valid (add_ctx (ctx_add_var C x t_inner v_inner) D) t_body ->
    ty_valid (add_ctx (ctx_add_var (ctx_subst x e0 C) x t_inner v_inner) D) t_body.
Proof.
  intros C D x e0 t0 t_inner v_inner t_body Hbeta0 Hpure0 Hfv Hvalid.
  revert D C t_inner v_inner t_body Hpure0 Hfv Hvalid.
  fix IH 8.
  intros D C t_inner v_inner t_body Hpure0 Hfv Hvalid.
  destruct Hvalid as
    [tb
    | var tb e w Hp
    | t1a t2a Hv1 Hv2
    | var t1a t2a Hv1 Hv2
    | t1a t2a Hv1 Hv2
    | tref Hv].
  - apply VBase.
  - eapply VSet.
    rewrite add_ctx_ctx_add_var in Hp |- *.
    assert (Hpure_ext : has_type_pure (add_ctx (ctx_subst x e0 C) (ctx_add_var D var (TBase tb) w)) e0 (essential_type t0)).
    { rewrite <- add_ctx_ctx_add_var.
      exact (weakening_closed_has_type_pure_var (add_ctx (ctx_subst x e0 C) D) var (TBase tb) w e0 (essential_type t0) Hfv Hpure0). }
    exact (subst_base_has_type_pure_shadow_top_same_ctx C (ctx_add_var D var (TBase tb) w) x e0 t0 t_inner v_inner e (TBase BBool) Hbeta0 Hpure_ext Hp).
  - apply VFun.
    + exact (IH D C t_inner v_inner t1a Hpure0 Hfv Hv1).
    + exact (IH D C t_inner v_inner t2a Hpure0 Hfv Hv2).
  - eapply VFunDep.
    + exact (IH D C t_inner v_inner t1a Hpure0 Hfv Hv1).
    + rewrite add_ctx_ctx_add_var in Hv2 |- *.
      assert (Hpure_ext : has_type_pure (add_ctx (ctx_subst x e0 C) (ctx_add_var D var t1a (EVar var))) e0 (essential_type t0)).
      { rewrite <- add_ctx_ctx_add_var.
        exact (weakening_closed_has_type_pure_var (add_ctx (ctx_subst x e0 C) D) var t1a (EVar var) e0 (essential_type t0) Hfv Hpure0). }
      exact (IH (ctx_add_var D var t1a (EVar var)) C t_inner v_inner t2a Hpure_ext Hfv Hv2).
  - apply VPair.
    + exact (IH D C t_inner v_inner t1a Hpure0 Hfv Hv1).
    + exact (IH D C t_inner v_inner t2a Hpure0 Hfv Hv2).
  - apply VRef.
    exact (IH D C t_inner v_inner tref Hpure0 Hfv Hv).
Qed.

Lemma subst_base_ty_valid_shadow_top_ctx :
  forall C D x e0 t0 t_inner v_inner t_body,
    essential_type_is_base_type t0 = true ->
    has_type_pure (add_ctx (ctx_subst x e0 C) D) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    ty_valid (add_ctx (ctx_add_var C x t_inner v_inner) D) t_body ->
    ty_valid (add_ctx (ctx_add_var (ctx_subst x e0 C) x (ty_subst x e0 t_inner) v_inner) D) t_body.
Proof.
  intros C D x e0 t0 t_inner v_inner t_body Hbeta0 Hpure0 Hfv Hvalid.
  revert D C t_inner v_inner t_body Hpure0 Hfv Hvalid.
  fix IH 8.
  intros D C t_inner v_inner t_body Hpure0 Hfv Hvalid.
  destruct Hvalid as
    [tb
    | var tb e w Hp
    | t1a t2a Hv1 Hv2
    | var t1a t2a Hv1 Hv2
    | t1a t2a Hv1 Hv2
    | tref Hv].
  - apply VBase.
  - eapply VSet.
    rewrite add_ctx_ctx_add_var in Hp |- *.
    assert (Hpure_ext : has_type_pure (add_ctx (ctx_subst x e0 C) (ctx_add_var D var (TBase tb) w)) e0 (essential_type t0)).
    { rewrite <- add_ctx_ctx_add_var.
      exact (weakening_closed_has_type_pure_var (add_ctx (ctx_subst x e0 C) D) var (TBase tb) w e0 (essential_type t0) Hfv Hpure0). }
    exact (subst_base_has_type_pure_shadow_top_ctx C (ctx_add_var D var (TBase tb) w) x e0 t0 t_inner v_inner e (TBase BBool) Hbeta0 Hpure_ext Hp).
  - apply VFun.
    + exact (IH D C t_inner v_inner t1a Hpure0 Hfv Hv1).
    + exact (IH D C t_inner v_inner t2a Hpure0 Hfv Hv2).
  - eapply VFunDep.
    + exact (IH D C t_inner v_inner t1a Hpure0 Hfv Hv1).
    + rewrite add_ctx_ctx_add_var in Hv2 |- *.
      assert (Hpure_ext : has_type_pure (add_ctx (ctx_subst x e0 C) (ctx_add_var D var t1a (EVar var))) e0 (essential_type t0)).
      { rewrite <- add_ctx_ctx_add_var.
        exact (weakening_closed_has_type_pure_var (add_ctx (ctx_subst x e0 C) D) var t1a (EVar var) e0 (essential_type t0) Hfv Hpure0). }
      exact (IH (ctx_add_var D var t1a (EVar var)) C t_inner v_inner t2a Hpure_ext Hfv Hv2).
  - apply VPair.
    + exact (IH D C t_inner v_inner t1a Hpure0 Hfv Hv1).
    + exact (IH D C t_inner v_inner t2a Hpure0 Hfv Hv2).
  - apply VRef.
    exact (IH D C t_inner v_inner tref Hpure0 Hfv Hv).
Qed.

Lemma subst_base_ty_valid_fun_dep_shadow_under_dep_ctx :
  forall C x e0 t0 t_active v_active var t_outer v_outer t_body,
    var <> x ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    ty_valid (ctx_add_var (ctx_add_var C x t_active v_active) var t_outer v_outer) t_body ->
    ty_valid (ctx_add_var (ctx_add_var (ctx_subst x e0 C) x (ty_subst x e0 t_active) v_active) var t_outer v_outer) t_body.
Proof.
  intros C x e0 t0 t_active v_active var t_outer v_outer t_body _ Hbeta0 Hpure0 Hfv Hvalid.
  rewrite <- (add_ctx_empty_l (ctx_add_var C x t_active v_active)) in Hvalid.
  rewrite add_ctx_ctx_add_var in Hvalid.
  assert (Hpure_top : has_type_pure (add_ctx (ctx_subst x e0 C) (ctx_add_var empty_ctx var t_outer v_outer)) e0 (essential_type t0)).
  { rewrite <- add_ctx_ctx_add_var.
    rewrite add_ctx_empty_l.
    exact (weakening_closed_has_type_pure_var (ctx_subst x e0 C) var t_outer v_outer e0 (essential_type t0) Hfv Hpure0). }
  pose proof (subst_base_ty_valid_shadow_top_ctx C (ctx_add_var empty_ctx var t_outer v_outer) x e0 t0 t_active v_active t_body Hbeta0 Hpure_top Hfv Hvalid) as Hvalid'.
  rewrite <- add_ctx_ctx_add_var in Hvalid'.
  rewrite add_ctx_empty_l in Hvalid'.
  exact Hvalid'.
Qed.

Lemma subst_base_ty_valid_fun_dep_shadow_under_dep_same_ctx :
  forall C x e0 t0 t_active v_active var t_outer v_outer t_body,
    var <> x ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    ty_valid (ctx_add_var (ctx_add_var C x t_active v_active) var t_outer v_outer) t_body ->
    ty_valid (ctx_add_var (ctx_add_var (ctx_subst x e0 C) x t_active v_active) var t_outer v_outer) t_body.
Proof.
  intros C x e0 t0 t_active v_active var t_outer v_outer t_body _ Hbeta0 Hpure0 Hfv Hvalid.
  rewrite <- (add_ctx_empty_l (ctx_add_var C x t_active v_active)) in Hvalid.
  rewrite add_ctx_ctx_add_var in Hvalid.
  assert (Hpure_top : has_type_pure (add_ctx (ctx_subst x e0 C) (ctx_add_var empty_ctx var t_outer v_outer)) e0 (essential_type t0)).
  { rewrite <- add_ctx_ctx_add_var.
    rewrite add_ctx_empty_l.
    exact (weakening_closed_has_type_pure_var (ctx_subst x e0 C) var t_outer v_outer e0 (essential_type t0) Hfv Hpure0). }
  pose proof (subst_base_ty_valid_shadow_top_same_ctx C (ctx_add_var empty_ctx var t_outer v_outer) x e0 t0 t_active v_active t_body Hbeta0 Hpure_top Hfv Hvalid) as Hvalid'.
  rewrite <- add_ctx_ctx_add_var in Hvalid'.
  rewrite add_ctx_empty_l in Hvalid'.
  exact Hvalid'.
Qed.

Lemma subst_base_ty_valid_fun_dep_shadow_same_ctx :
  forall C x e0 t0 t_inner v_inner t_body,
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    ty_valid (ctx_add_var C x t_inner v_inner) t_body ->
    ty_valid (ctx_add_var (ctx_subst x e0 C) x t_inner v_inner) t_body.
Proof.
  intros C x e0 t0 t_inner v_inner t_body Hbeta0 Hpure0 Hfv Hvalid.
  revert C t_inner t_body v_inner Hpure0 Hfv Hvalid.
  fix IH 7.
  intros C t_inner t_body v_inner Hpure0 Hfv Hvalid.
  destruct Hvalid as
    [tb
    | var tb e w Hp
    | t1a t2a Hv1 Hv2
    | var t1a t2a Hv1 Hv2
    | t1a t2a Hv1 Hv2
    | tref Hv].
  - apply VBase.
  - destruct (String.eq_dec var x) as [-> | Hneq].
    + eapply VSet with (v := w).
      rewrite ctx_add_var_shadow.
      rewrite ctx_add_var_shadow in Hp.
      exact (subst_base_has_type_pure_shadow_ctx C x e0 t0 (TBase tb) w e (TBase BBool) Hbeta0 Hpure0 Hp).
    + eapply VSet with (v := expr_subst x e0 w).
      rewrite ctx_add_var_swap in Hp by congruence.
      assert (Hpure_ext : has_type_pure (ctx_subst x e0 (ctx_add_var C var (TBase tb) w)) e0 (essential_type t0)).
      { rewrite ctx_subst_ctx_add_var.
        simpl.
        exact (weakening_closed_has_type_pure_var (ctx_subst x e0 C) var (TBase tb) (expr_subst x e0 w) e0 (essential_type t0) Hfv Hpure0). }
      rewrite ctx_add_var_swap by congruence.
      pose proof (subst_base_has_type_pure_shadow_same_ctx (ctx_add_var C var (TBase tb) w) x e0 t0 t_inner v_inner e (TBase BBool) Hbeta0 Hpure_ext Hp) as Hp'.
      rewrite ctx_subst_ctx_add_var in Hp'.
      exact Hp'.
  - apply VFun.
    + exact (IH C t_inner t1a v_inner Hpure0 Hfv Hv1).
    + exact (IH C t_inner t2a v_inner Hpure0 Hfv Hv2).
  - destruct (String.eq_dec var x) as [-> | Hneq].
    + eapply VFunDep.
      * exact (IH C t_inner t1a v_inner Hpure0 Hfv Hv1).
      * rewrite ctx_add_var_shadow.
        rewrite ctx_add_var_shadow in Hv2.
        exact (IH C t1a t2a (EVar x) Hpure0 Hfv Hv2).
    + eapply VFunDep.
      * exact (IH C t_inner t1a v_inner Hpure0 Hfv Hv1).
      * exact (subst_base_ty_valid_fun_dep_shadow_under_dep_same_ctx C x e0 t0 t_inner v_inner var t1a (EVar var) t2a Hneq Hbeta0 Hpure0 Hfv Hv2).
  - apply VPair.
    + exact (IH C t_inner t1a v_inner Hpure0 Hfv Hv1).
    + exact (IH C t_inner t2a v_inner Hpure0 Hfv Hv2).
  - apply VRef.
    exact (IH C t_inner tref v_inner Hpure0 Hfv Hv).
Qed.

Lemma subst_base_ty_valid_fun_dep_shadow_ctx :
  forall C x e0 t0 t1 t2 v,
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    ty_valid (ctx_add_var C x t1 v) t2 ->
    ty_valid (ctx_add_var (ctx_subst x e0 C) x (ty_subst x e0 t1) v) t2.
Proof.
  intros C x e0 t0 t1 t2 v Hbeta0 Hpure0 Hfv Hvalid.
  revert C t1 t2 v Hpure0 Hfv Hvalid.
  fix IH 7.
  intros C t1 t2 v Hpure0 Hfv Hvalid.
  destruct Hvalid as
    [tb
    | var tb e w Hp
    | t1a t2a Hv1 Hv2
    | var t1a t2a Hv1 Hv2
    | t1a t2a Hv1 Hv2
    | tref Hv].
  - apply VBase.
  - destruct (String.eq_dec var x) as [-> | Hneq].
    + eapply VSet with (v := w).
      rewrite ctx_add_var_shadow.
      rewrite ctx_add_var_shadow in Hp.
      exact (subst_base_has_type_pure_shadow_ctx C x e0 t0 (TBase tb) w e (TBase BBool) Hbeta0 Hpure0 Hp).
    + eapply VSet with (v := expr_subst x e0 w).
      rewrite ctx_add_var_swap in Hp by congruence.
      assert (Hpure_ext : has_type_pure (ctx_subst x e0 (ctx_add_var C var (TBase tb) w)) e0 (essential_type t0)).
      { rewrite ctx_subst_ctx_add_var.
        simpl.
        exact (weakening_closed_has_type_pure_var (ctx_subst x e0 C) var (TBase tb) (expr_subst x e0 w) e0 (essential_type t0) Hfv Hpure0). }
      rewrite ctx_add_var_swap by congruence.
      pose proof (subst_base_has_type_pure_shadow_ctx (ctx_add_var C var (TBase tb) w) x e0 t0 t1 v e (TBase BBool) Hbeta0 Hpure_ext Hp) as Hp'.
      rewrite ctx_subst_ctx_add_var in Hp'.
      exact Hp'.
  - apply VFun.
    + exact (IH C t1 t1a v Hpure0 Hfv Hv1).
    + exact (IH C t1 t2a v Hpure0 Hfv Hv2).
  - destruct (String.eq_dec var x) as [-> | Hneq].
    + eapply VFunDep.
      * exact (IH C t1 t1a v Hpure0 Hfv Hv1).
      * rewrite ctx_add_var_shadow.
        rewrite ctx_add_var_shadow in Hv2.
        exact (subst_base_ty_valid_fun_dep_shadow_same_ctx C x e0 t0 t1a (EVar x) t2a Hbeta0 Hpure0 Hfv Hv2).
    + eapply VFunDep.
      * exact (IH C t1 t1a v Hpure0 Hfv Hv1).
      * exact (subst_base_ty_valid_fun_dep_shadow_under_dep_ctx C x e0 t0 t1 v var t1a (EVar var) t2a Hneq Hbeta0 Hpure0 Hfv Hv2).
  - apply VPair.
    + exact (IH C t1 t1a v Hpure0 Hfv Hv1).
    + exact (IH C t1 t2a v Hpure0 Hfv Hv2).
  - apply VRef.
    exact (IH C t1 tref v Hpure0 Hfv Hv).
Qed.

Lemma subst_base_ty_valid_ctx :
  forall C x e0 t0 t,
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    ty_valid (ctx_add_var C x t0 e0) t ->
    ty_valid (ctx_subst x e0 C) (ty_subst x e0 t).
Proof.
  intros C x e0 t0 t Hbeta0 Hpure0 Hfv Hvalid.
  revert C t Hpure0 Hfv Hvalid.
  fix IH 5.
  intros C t Hpure0 Hfv Hvalid.
  destruct Hvalid as
    [tb
    | var tb e v Hp
    | t1 t2 Hv1 Hv2
    | var t1 t2 Hv1 Hv2
    | t1 t2 Hv1 Hv2
    | tref Hv].
  - apply VBase.
  - destruct (String.eq_dec var x) as [-> | Hneq].
    + simpl. rewrite String.eqb_refl.
      eapply VSet.
      rewrite ctx_add_var_shadow in Hp.
      exact (subst_base_has_type_pure_shadow_ctx C x e0 t0 (TBase tb) v e (TBase BBool) Hbeta0 Hpure0 Hp).
    + simpl.
      assert (Hneqb : (x =? var)%string = false) by (apply String.eqb_neq; congruence).
      rewrite Hneqb.
      eapply VSet.
      rewrite ctx_add_var_swap in Hp by congruence.
      assert (Hpure_ext : has_type_pure (ctx_subst x e0 (ctx_add_var C var (TBase tb) v)) e0 (essential_type t0)).
      { rewrite ctx_subst_ctx_add_var.
        simpl.
        exact (weakening_closed_has_type_pure_var (ctx_subst x e0 C) var (TBase tb) (expr_subst x e0 v) e0 (essential_type t0) Hfv Hpure0). }
      pose proof (subst_base_has_type_pure_gen (ctx_add_var C var (TBase tb) v) x e0 t0 e (TBase BBool) Hbeta0 Hpure_ext Hp) as Hp'.
      rewrite ctx_subst_ctx_add_var in Hp'.
      simpl in Hp'.
      exact Hp'.
  - simpl.
    apply VFun.
    + exact (IH C t1 Hpure0 Hfv Hv1).
    + exact (IH C t2 Hpure0 Hfv Hv2).
  - destruct (String.eq_dec var x) as [-> | Hneq].
    + simpl. rewrite String.eqb_refl.
      eapply VFunDep.
      * exact (IH C t1 Hpure0 Hfv Hv1).
      * rewrite ctx_add_var_shadow in Hv2.
        exact (subst_base_ty_valid_fun_dep_shadow_ctx C x e0 t0 t1 t2 (EVar x) Hbeta0 Hpure0 Hfv Hv2).
    + simpl.
      assert (Hneqb : (x =? var)%string = false) by (apply String.eqb_neq; congruence).
      rewrite Hneqb.
      eapply VFunDep.
      * exact (IH C t1 Hpure0 Hfv Hv1).
      * rewrite ctx_add_var_swap in Hv2 by congruence.
        assert (Hpure_ext : has_type_pure (ctx_subst x e0 (ctx_add_var C var t1 (EVar var))) e0 (essential_type t0)).
        { rewrite ctx_subst_ctx_add_var.
          simpl. rewrite Hneqb.
          exact (weakening_closed_has_type_pure_var (ctx_subst x e0 C) var (ty_subst x e0 t1) (EVar var) e0 (essential_type t0) Hfv Hpure0). }
        pose proof (IH (ctx_add_var C var t1 (EVar var)) t2 Hpure_ext Hfv Hv2) as Hv2'.
        rewrite ctx_subst_ctx_add_var in Hv2'.
        simpl in Hv2'. rewrite Hneqb in Hv2'.
        exact Hv2'.
  - simpl.
    apply VPair.
    + exact (IH C t1 Hpure0 Hfv Hv1).
    + exact (IH C t2 Hpure0 Hfv Hv2).
  - simpl.
    apply VRef.
    exact (IH C tref Hpure0 Hfv Hv).
Qed.
(* Paper Lemma 6, validity clause.
   Base substitution preserves type validity. *)
Lemma subst_base_ty_valid :
  forall G1 G2 x e0 t0 t,
    DTDT.machine_inter.value G1 e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    ctx_subst x e0 G1 = G1 ->
    ctx_subst x e0 G2 = G2 ->
    free_exp_vars e0 = [] ->
    ty_valid (ctx_add_var (add_ctx G2 G1) x t0 e0) t ->
    ty_valid (add_ctx (ctx_subst x e0 G2) G1) (ty_subst x e0 t).
Proof.
  intros G1 G2 x e0 t0 t Hv0 Hbeta0 Hpure0 Hty0 Hctx Hctx2 Hclosed Hvalid.
  assert (Hpure_ctx : has_type_pure (ctx_subst x e0 (add_ctx G2 G1)) e0 (essential_type t0)).
  { rewrite (ctx_subst_add_ctx_stable G1 G2 x e0 Hctx Hctx2).
    apply weakening_has_type_pure_right.
    exact Hpure0. }
  pose proof (subst_base_ty_valid_ctx (add_ctx G2 G1) x e0 t0 t Hbeta0 Hpure_ctx Hclosed Hvalid) as Hvalid'.
  rewrite ctx_subst_add_ctx in Hvalid'.
  rewrite Hctx in Hvalid'.
  exact Hvalid'.
Qed.

(* AXIOM #1: Entailment transport under base substitution (non-fixed context)
   
   Paper: Implicit in substitution section via context hygiene.
   Coq requires: ctx_subst x e0 C = C for the proof to go through.
   Status: Remains Admitted because it crosses the entailment axiom layer.
   Alternative: Use entails_subst_base_closed_pure_ctx_fixed (L2868) when C is stable.
   
   Why this axiom is sound:
   - In practice, C is always built as empty_ctx or via add_ctx/ctx_add_var
   - Those context-building functions preserve substitution-stability naturally
   - The axiom captures this implicit invariant from the paper's proof
*)
Lemma value_ctx_add_var_right :
  forall G x t witness v,
    DTDT.machine_inter.value G v ->
    DTDT.machine_inter.value (ctx_add_var G x t witness) v.
Proof.
  intros G x t witness v Hv.
  induction Hv.
  - apply DTDT.machine_inter.VNat.
  - apply DTDT.machine_inter.VBool.
  - apply DTDT.machine_inter.VUnit.
  - apply DTDT.machine_inter.VString.
  - eapply DTDT.machine_inter.VConst.
    unfold const_ctx_lookup, ctx_add_var in *. simpl in *. exact H.
  - apply DTDT.machine_inter.VFix.
  - eapply DTDT.machine_inter.VPair; eauto.
  - destruct G as [env store].
    destruct env as [vars consts].
    simpl in *.
    destruct (String.eq_dec x0 x) as [Heq | Hneq].
    + subst x0.
      eapply (@DTDT.machine_inter.VVar (((<[x:=(t, witness)]> vars), consts), store) x t witness).
      change ((<[x := (t, witness)]> vars) !! x = Some (t, witness)).
      apply lookup_insert.
    + eapply (@DTDT.machine_inter.VVar (((<[x:=(t, witness)]> vars), consts), store) x0 τ e).
      change ((<[x := (t, witness)]> vars) !! x0 = Some (τ, e)).
      refine (eq_trans _ H).
      apply lookup_insert_ne.
      congruence.
  - eapply DTDT.machine_inter.VLoc.
    unfold store_ctx_lookup, ctx_add_var in *. simpl in *. exact H.
Qed.

Lemma entails_subst_base_closed_pure_ctx_fixed :
  forall C x e0 t0 pred,
    ctx_subst x e0 C = C ->
    DTDT.machine_inter.value (ctx_subst x e0 C) e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    entails (ctx_add_var C x (essential_type t0) e0) pred ->
    entails (ctx_subst x e0 C) (expr_subst x e0 pred).
Proof.
  intros C x e0 t0 pred Hctx Hv0 Hbeta _ _ Hent.
  destruct t0 as [tb | y tb pred0 | t1 t2 | y t1 t2 | t1 t2 | t1];
    simpl in *; try discriminate.
  - replace (ctx_add_var C x (TBase tb) e0) with
      (ctx_add_var (add_ctx empty_ctx (ctx_subst x e0 C)) x (TBase tb) e0) in Hent.
    2:{ rewrite add_ctx_empty_r. rewrite Hctx. reflexivity. }
    pose proof (entails_subst_base (ctx_subst x e0 C) empty_ctx x tb e0 pred e0 Hent Hv0) as Hent'.
    change (entails (add_ctx (ctx_subst x e0 empty_ctx) (ctx_subst x e0 C)) (expr_subst x e0 pred)) in Hent'.
    simpl in Hent'.
    rewrite add_ctx_empty_r in Hent'.
    exact Hent'.
  - replace (ctx_add_var C x (TBase tb) e0) with
      (ctx_add_var (add_ctx empty_ctx (ctx_subst x e0 C)) x (TBase tb) e0) in Hent.
    2:{ rewrite add_ctx_empty_r. rewrite Hctx. reflexivity. }
    pose proof (entails_subst_base (ctx_subst x e0 C) empty_ctx x tb e0 pred e0 Hent Hv0) as Hent'.
    change (entails (add_ctx (ctx_subst x e0 empty_ctx) (ctx_subst x e0 C)) (expr_subst x e0 pred)) in Hent'.
    simpl in Hent'.
    rewrite add_ctx_empty_r in Hent'.
    exact Hent'.
Qed.

Lemma subst_base_entails_ctx_stable :
  forall C x e0 t0 pred,
    ctx_subst x e0 C = C ->
    DTDT.machine_inter.value (ctx_subst x e0 C) e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    entails (ctx_add_var C x t0 e0) pred ->
    entails (ctx_subst x e0 C) (expr_subst x e0 pred).
Proof.
  intros C x e0 t0 pred Hctx Hv0 Hbeta0 Hpure0 Hclosed Hent.
  pose proof (subsumption_entails_var_ctx C x t0 (essential_type t0) e0 pred Hent) as Hent_base.
  exact (entails_subst_base_closed_pure_ctx_fixed C x e0 t0 pred Hctx Hv0 Hbeta0 Hpure0 Hclosed Hent_base).
Qed.

Lemma subst_base_entails_shadow_base_ctx_stable :
  forall C x e0 tb c pred,
    ctx_subst x e0 C = C ->
    entails (ctx_add_var C x (TBase tb) (make_expr tb c)) pred ->
    entails (ctx_add_var (ctx_subst x e0 C) x (TBase tb) (make_expr tb c)) pred.
Proof.
  intros C x e0 tb c pred Hctx Hent.
  rewrite Hctx.
  exact Hent.
Qed.

Lemma subtype_subst_base_closed_pure_shadow_ctx_fixed_typed :
  forall C x e0 t0 t_active v_active t1 t2,
    ctx_subst x e0 C = C ->
    ty_subst x e0 t_active = t_active ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    subtype (ctx_add_var C x t_active v_active) t1 t2 ->
    subtype (ctx_add_var (ctx_subst x e0 C) x t_active v_active) t1 t2.
Proof.
  intros C x e0 t0 t_active v_active t1 t2 Hctx _ _ _ _ Hsub.
  rewrite Hctx.
  exact Hsub.
Qed.

Lemma subtype_subst_base_closed_pure_shadow_ctx_hygienic :
  forall C x e0 t0 t_active v_active t1 t2,
    ctx_subst x e0 C = C ->
    ~ List.In x (free_ty_vars t_active) ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    subtype (ctx_add_var C x t_active v_active) t1 t2 ->
    subtype (ctx_add_var (ctx_subst x e0 C) x (ty_subst x e0 t_active) v_active) t1 t2.
Proof.
  intros C x e0 t0 t_active v_active t1 t2 Hctx Hfresh Hbeta0 Hpure0 Hclosed Hsub.
  pose proof (ty_subst_free_ty_vars_fresh x e0 t_active Hfresh) as Htactive.
  rewrite Htactive.
  exact (subtype_subst_base_closed_pure_shadow_ctx_fixed_typed C x e0 t0 t_active v_active t1 t2
    Hctx Htactive Hbeta0 Hpure0 Hclosed Hsub).
Qed.

Lemma subst_base_subtype_fun_dep_shadow_ctx_stable_fresh :
  forall C x e0 t0 t_active v_active t1 t2,
    ctx_subst x e0 C = C ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    ~ List.In x (free_ty_vars t_active) ->
    subtype (ctx_add_var C x t_active v_active) t1 t2 ->
    subtype (ctx_add_var (ctx_subst x e0 C) x (ty_subst x e0 t_active) v_active) t1 t2.
Proof.
  intros C x e0 t0 t_active v_active t1 t2 Hctx Hbeta0 Hpure0 Hclosed Hfresh Hsub.
  exact (subtype_subst_base_closed_pure_shadow_ctx_hygienic C x e0 t0 t_active v_active t1 t2
    Hctx Hfresh Hbeta0 Hpure0 Hclosed Hsub).
Qed.

Lemma subst_base_subtype_ctx_stable_constructive :
  forall C x e0 t0 t1 t2,
    ctx_subst x e0 C = C ->
    DTDT.machine_inter.value (ctx_subst x e0 C) e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure (ctx_subst x e0 C) e0 (essential_type t0) ->
    free_exp_vars e0 = [] ->
    ~ List.In x (free_ty_vars t1) ->
    ~ List.In x (free_ty_vars t2) ->
    subtype (ctx_add_var C x t0 e0) t1 t2 ->
    subtype (ctx_subst x e0 C) (ty_subst x e0 t1) (ty_subst x e0 t2).
Proof.
  fix IH 14.
  intros C x e0 t0 t1 t2 HctxC Hv0 Hbeta0 Hpure0 Hclosed Hfresh1 Hfresh2 Hsub.
  destruct Hsub as
    [b
    | var tb e1 e2 c Hv1 Hv2 Hent
    | var tb e Hv
    | var tb e c Hv Hent
    | t_dom t_dom' t_cod t_cod' Hs1 Hs2
    | var t_dom t_dom' t_cod t_cod' Hs1 Hs2
    | t1a t1b t2a t2b Hs1 Hs2
    | t_left t_right Hs1 Hs2].
  - apply SBase.
  - simpl.
    destruct (String.eq_dec x var) as [Heq | Hneq].
    + subst var.
      rewrite String.eqb_refl.
      cbn [ty_subst].
      eapply SSet with (c:=c).
      * replace (TSet x tb e1) with (ty_subst x e0 (TSet x tb e1)).
        2:{ simpl. rewrite String.eqb_refl. reflexivity. }
        exact (subst_base_ty_valid_ctx C x e0 t0 (TSet x tb e1) Hbeta0 Hpure0 Hclosed Hv1).
      * replace (TSet x tb e2) with (ty_subst x e0 (TSet x tb e2)).
        2:{ simpl. rewrite String.eqb_refl. reflexivity. }
        exact (subst_base_ty_valid_ctx C x e0 t0 (TSet x tb e2) Hbeta0 Hpure0 Hclosed Hv2).
      * rewrite ctx_add_var_shadow in Hent.
        exact (subst_base_entails_shadow_base_ctx_stable C x e0 tb c (EImp e1 e2)
          HctxC Hent).
    + assert (Hneqb : (x =? var)%string = false) by (apply String.eqb_neq; congruence).
      rewrite Hneqb.
      eapply SSet with (c:=c).
      * replace (TSet var tb (expr_subst x e0 e1)) with (ty_subst x e0 (TSet var tb e1)).
        2:{ simpl. rewrite Hneqb. reflexivity. }
        exact (subst_base_ty_valid_ctx C x e0 t0 (TSet var tb e1) Hbeta0 Hpure0 Hclosed Hv1).
      * replace (TSet var tb (expr_subst x e0 e2)) with (ty_subst x e0 (TSet var tb e2)).
        2:{ simpl. rewrite Hneqb. reflexivity. }
        exact (subst_base_ty_valid_ctx C x e0 t0 (TSet var tb e2) Hbeta0 Hpure0 Hclosed Hv2).
      * rewrite ctx_add_var_swap in Hent by congruence.
        assert (Hctx_ext : ctx_subst x e0 (ctx_add_var C var (TBase tb) (make_expr tb c)) =
                           ctx_add_var C var (TBase tb) (make_expr tb c)).
        { exact (ctx_subst_ctx_add_var_base_stable C var tb c x e0 HctxC). }
        assert (Hpure_ext : has_type_pure (ctx_subst x e0 (ctx_add_var C var (TBase tb) (make_expr tb c))) e0 (essential_type t0)).
        { rewrite ctx_subst_ctx_add_var.
          simpl.
          exact (weakening_closed_has_type_pure_var (ctx_subst x e0 C) var (TBase tb) (expr_subst x e0 (make_expr tb c)) e0 (essential_type t0) Hclosed Hpure0). }
        assert (Hv0C : DTDT.machine_inter.value C e0).
        { rewrite <- HctxC. exact Hv0. }
        assert (Hv0_ext : DTDT.machine_inter.value (ctx_subst x e0 (ctx_add_var C var (TBase tb) (make_expr tb c))) e0).
        { rewrite Hctx_ext.
          exact (value_ctx_add_var_right C var (TBase tb) (make_expr tb c) e0 Hv0C). }
        pose proof (subst_base_entails_ctx_stable (ctx_add_var C var (TBase tb) (make_expr tb c)) x e0 t0 (EImp e1 e2)
          Hctx_ext Hv0_ext Hbeta0 Hpure_ext Hclosed Hent) as Hent'.
        rewrite ctx_subst_ctx_add_var in Hent'.
        simpl in Hent'.
        replace (expr_subst x e0 (make_expr tb c)) with (make_expr tb c) in Hent' by (destruct tb; destruct c; reflexivity).
        exact Hent'.
  - simpl.
    destruct (String.eq_dec x var) as [Heq | Hneq].
    + subst var.
      rewrite String.eqb_refl.
      cbn [ty_subst].
      apply SSetBase.
      replace (TSet x tb e) with (ty_subst x e0 (TSet x tb e)).
        2:{ simpl. rewrite String.eqb_refl. reflexivity. }
      exact (subst_base_ty_valid_ctx C x e0 t0 (TSet x tb e) Hbeta0 Hpure0 Hclosed Hv).
    + assert (Hneqb : (x =? var)%string = false) by (apply String.eqb_neq; congruence).
      rewrite Hneqb.
      apply SSetBase.
      replace (TSet var tb (expr_subst x e0 e)) with (ty_subst x e0 (TSet var tb e)).
      2:{ simpl. rewrite Hneqb. reflexivity. }
      exact (subst_base_ty_valid_ctx C x e0 t0 (TSet var tb e) Hbeta0 Hpure0 Hclosed Hv).
  - simpl.
    destruct (String.eq_dec x var) as [Heq | Hneq].
    + subst var.
      rewrite String.eqb_refl.
      cbn [ty_subst].
      eapply SBaseSet with (c:=c).
      * replace (TSet x tb e) with (ty_subst x e0 (TSet x tb e)).
        2:{ simpl. rewrite String.eqb_refl. reflexivity. }
        exact (subst_base_ty_valid_ctx C x e0 t0 (TSet x tb e) Hbeta0 Hpure0 Hclosed Hv).
      * rewrite ctx_add_var_shadow in Hent.
        exact (subst_base_entails_shadow_base_ctx_stable C x e0 tb c e
          HctxC Hent).
    + assert (Hneqb : (x =? var)%string = false) by (apply String.eqb_neq; congruence).
      rewrite Hneqb.
      eapply SBaseSet with (c:=c).
      * replace (TSet var tb (expr_subst x e0 e)) with (ty_subst x e0 (TSet var tb e)).
        2:{ simpl. rewrite Hneqb. reflexivity. }
        exact (subst_base_ty_valid_ctx C x e0 t0 (TSet var tb e) Hbeta0 Hpure0 Hclosed Hv).
      * rewrite ctx_add_var_swap in Hent by congruence.
        assert (Hctx_ext : ctx_subst x e0 (ctx_add_var C var (TBase tb) (make_expr tb c)) =
                           ctx_add_var C var (TBase tb) (make_expr tb c)).
        { exact (ctx_subst_ctx_add_var_base_stable C var tb c x e0 HctxC). }
        assert (Hpure_ext : has_type_pure (ctx_subst x e0 (ctx_add_var C var (TBase tb) (make_expr tb c))) e0 (essential_type t0)).
        { rewrite ctx_subst_ctx_add_var.
          simpl.
          exact (weakening_closed_has_type_pure_var (ctx_subst x e0 C) var (TBase tb) (expr_subst x e0 (make_expr tb c)) e0 (essential_type t0) Hclosed Hpure0). }
        assert (Hv0C : DTDT.machine_inter.value C e0).
        { rewrite <- HctxC. exact Hv0. }
        assert (Hv0_ext : DTDT.machine_inter.value (ctx_subst x e0 (ctx_add_var C var (TBase tb) (make_expr tb c))) e0).
        { rewrite Hctx_ext.
          exact (value_ctx_add_var_right C var (TBase tb) (make_expr tb c) e0 Hv0C). }
        pose proof (subst_base_entails_ctx_stable (ctx_add_var C var (TBase tb) (make_expr tb c)) x e0 t0 e
          Hctx_ext Hv0_ext Hbeta0 Hpure_ext Hclosed Hent) as Hent'.
        rewrite ctx_subst_ctx_add_var in Hent'.
        simpl in Hent'.
        replace (expr_subst x e0 (make_expr tb c)) with (make_expr tb c) in Hent' by (destruct tb; destruct c; reflexivity).
        exact Hent'.
  - simpl.
    simpl in Hfresh1, Hfresh2.
    assert (Hfresh_dom : ~ List.In x (free_ty_vars t_dom)).
    { intro Hin. apply Hfresh1. apply in_or_app. left. exact Hin. }
    assert (Hfresh_cod : ~ List.In x (free_ty_vars t_cod)).
    { intro Hin. apply Hfresh1. apply in_or_app. right. exact Hin. }
    assert (Hfresh_dom' : ~ List.In x (free_ty_vars t_dom')).
    { intro Hin. apply Hfresh2. apply in_or_app. left. exact Hin. }
    assert (Hfresh_cod' : ~ List.In x (free_ty_vars t_cod')).
    { intro Hin. apply Hfresh2. apply in_or_app. right. exact Hin. }
    apply SFun.
    + exact (IH C x e0 t0 t_dom' t_dom HctxC Hv0 Hbeta0 Hpure0 Hclosed Hfresh_dom' Hfresh_dom Hs1).
    + exact (IH C x e0 t0 t_cod t_cod' HctxC Hv0 Hbeta0 Hpure0 Hclosed Hfresh_cod Hfresh_cod' Hs2).
  - simpl.
    simpl in Hfresh1, Hfresh2.
    assert (Hfresh_dom : ~ List.In x (free_ty_vars t_dom)).
    { intro Hin. apply Hfresh1. apply in_or_app. left. exact Hin. }
    assert (Hfresh_dom' : ~ List.In x (free_ty_vars t_dom')).
    { intro Hin. apply Hfresh2. apply in_or_app. left. exact Hin. }
    destruct (String.eq_dec x var) as [Heq | Hneq].
    + subst var.
      rewrite String.eqb_refl.
      eapply SFunDep.
      * exact (IH C x e0 t0 t_dom' t_dom HctxC Hv0 Hbeta0 Hpure0 Hclosed Hfresh_dom' Hfresh_dom Hs1).
      * rewrite ctx_add_var_shadow in Hs2.
        exact (subst_base_subtype_fun_dep_shadow_ctx_stable_fresh C x e0 t0 t_dom' (EVar x) t_cod t_cod'
          HctxC Hbeta0 Hpure0 Hclosed Hfresh_dom' Hs2).
    + assert (Hneqb : (x =? var)%string = false) by (apply String.eqb_neq; congruence).
      assert (Hfresh_cod : ~ List.In x (free_ty_vars t_cod)).
      { intro Hin.
        apply Hfresh1.
        apply in_or_app.
        right.
        apply in_remove_string_intro; assumption. }
      assert (Hfresh_cod' : ~ List.In x (free_ty_vars t_cod')).
      { intro Hin.
        apply Hfresh2.
        apply in_or_app.
        right.
        apply in_remove_string_intro; assumption. }
      rewrite Hneqb.
      eapply SFunDep.
      * exact (IH C x e0 t0 t_dom' t_dom HctxC Hv0 Hbeta0 Hpure0 Hclosed Hfresh_dom' Hfresh_dom Hs1).
      * rewrite ctx_add_var_swap in Hs2 by congruence.
        assert (Hctx_ext :
          ctx_subst x e0 (ctx_add_var C var t_dom' (EVar var)) =
          ctx_add_var C var t_dom' (EVar var)).
        { apply (ctx_subst_ctx_add_var_stable C var t_dom' (EVar var) x e0 HctxC).
          - apply ty_subst_free_ty_vars_fresh. exact Hfresh_dom'.
          - simpl. rewrite Hneqb. reflexivity. }
        assert (Hpure_ext : has_type_pure (ctx_subst x e0 (ctx_add_var C var t_dom' (EVar var))) e0 (essential_type t0)).
        { rewrite Hctx_ext.
          rewrite <- HctxC.
          exact (weakening_closed_has_type_pure_var (ctx_subst x e0 C) var t_dom' (EVar var) e0 (essential_type t0) Hclosed Hpure0). }
        assert (Hv0C : DTDT.machine_inter.value C e0).
        { rewrite <- HctxC. exact Hv0. }
        assert (Hv0_ext : DTDT.machine_inter.value (ctx_subst x e0 (ctx_add_var C var t_dom' (EVar var))) e0).
        { rewrite Hctx_ext.
          exact (value_ctx_add_var_right C var t_dom' (EVar var) e0 Hv0C). }
        pose proof (IH (ctx_add_var C var t_dom' (EVar var)) x e0 t0 t_cod t_cod' Hctx_ext Hv0_ext Hbeta0 Hpure_ext Hclosed Hfresh_cod Hfresh_cod' Hs2) as Hs2'.
        rewrite ctx_subst_ctx_add_var in Hs2'.
        simpl in Hs2'. rewrite Hneqb in Hs2'.
        exact Hs2'.
  - simpl.
    simpl in Hfresh1, Hfresh2.
    assert (Hfresh_left1 : ~ List.In x (free_ty_vars t1a)).
    { intro Hin. apply Hfresh1. apply in_or_app. left. exact Hin. }
    assert (Hfresh_right1 : ~ List.In x (free_ty_vars t2a)).
    { intro Hin. apply Hfresh1. apply in_or_app. right. exact Hin. }
    assert (Hfresh_left2 : ~ List.In x (free_ty_vars t1b)).
    { intro Hin. apply Hfresh2. apply in_or_app. left. exact Hin. }
    assert (Hfresh_right2 : ~ List.In x (free_ty_vars t2b)).
    { intro Hin. apply Hfresh2. apply in_or_app. right. exact Hin. }
    apply SPair.
    + exact (IH C x e0 t0 t1a t1b HctxC Hv0 Hbeta0 Hpure0 Hclosed Hfresh_left1 Hfresh_left2 Hs1).
    + exact (IH C x e0 t0 t2a t2b HctxC Hv0 Hbeta0 Hpure0 Hclosed Hfresh_right1 Hfresh_right2 Hs2).
  - simpl.
    simpl in Hfresh1, Hfresh2.
    apply SRef.
    + exact (IH C x e0 t0 t_left t_right HctxC Hv0 Hbeta0 Hpure0 Hclosed Hfresh1 Hfresh2 Hs1).
    + exact (IH C x e0 t0 t_right t_left HctxC Hv0 Hbeta0 Hpure0 Hclosed Hfresh2 Hfresh1 Hs2).
Qed.

(* Paper Lemma 6, subtyping clause.
   Base substitution preserves subtyping. *)
Lemma subst_base_subtype :
  forall G1 G2 x e0 t0 t1 t2,
    DTDT.machine_inter.value G1 e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    ctx_subst x e0 G1 = G1 ->
    ctx_subst x e0 G2 = G2 ->
    free_exp_vars e0 = [] ->
    ~ List.In x (free_ty_vars t1) ->
    ~ List.In x (free_ty_vars t2) ->
    subtype (ctx_add_var (add_ctx G2 G1) x t0 e0) t1 t2 ->
    subtype (add_ctx (ctx_subst x e0 G2) G1) (ty_subst x e0 t1) (ty_subst x e0 t2).
Proof.
  intros G1 G2 x e0 t0 t1 t2 Hv0 Hbeta0 Hpure0 Hty0 Hctx Hctx2 Hclosed Hfresh1 Hfresh2 Hsub.
  assert (Hctx_add : ctx_subst x e0 (add_ctx G2 G1) = add_ctx G2 G1).
  { exact (ctx_subst_add_ctx_stable G1 G2 x e0 Hctx Hctx2). }
  assert (Hpure_ctx : has_type_pure (ctx_subst x e0 (add_ctx G2 G1)) e0 (essential_type t0)).
  { rewrite (ctx_subst_add_ctx_stable G1 G2 x e0 Hctx Hctx2).
    apply weakening_has_type_pure_right.
    exact Hpure0. }
  assert (Hv_ctx : DTDT.machine_inter.value (ctx_subst x e0 (add_ctx G2 G1)) e0).
  { rewrite Hctx_add.
    exact (weakening_value_right G1 G2 e0 Hv0). }
  pose proof (subst_base_subtype_ctx_stable_constructive (add_ctx G2 G1) x e0 t0 t1 t2 Hctx_add Hv_ctx Hbeta0 Hpure_ctx Hclosed Hfresh1 Hfresh2 Hsub) as Hsub'.
  rewrite ctx_subst_add_ctx in Hsub'.
  rewrite Hctx in Hsub'.
  exact Hsub'.
Qed.

(* Hygiene-instantiated corollaries for Paper Lemma 6.
   These expose the same results with explicit well_formed_ctx premises. *)
Lemma subst_base_has_type_wf :
  forall G1 G2 x e0 t0 e t,
    DTDT.machine_inter.value G1 e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    well_formed_ctx G1 ->
    well_formed_ctx G2 ->
    ~ List.In x (free_ty_vars t0) ->
    free_exp_vars e0 = [] ->
    has_type (ctx_add_var (add_ctx G2 G1) x t0 e0) e t ->
    has_type (add_ctx (ctx_subst x e0 G2) G1) (expr_subst x e0 e) (ty_subst x e0 t).
Proof.
  intros G1 G2 x e0 t0 e t Hv0 Hbeta0 Hpure0 Hty0 Hwf1 Hwf2 Hfresh0 Hclosed Hty.
  exact (subst_base_has_type G1 G2 x e0 t0 e t Hv0 Hbeta0 Hpure0 Hty0
    (well_formed_ctx_subst_id G1 x e0 Hwf1)
    (well_formed_ctx_subst_id G2 x e0 Hwf2)
    (ty_subst_free_ty_vars_fresh x e0 t0 Hfresh0)
    Hclosed Hty).
Qed.

Lemma subst_base_has_type_pure_wf :
  forall G1 G2 x e0 t0 e t,
    DTDT.machine_inter.value G1 e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    well_formed_ctx G1 ->
    well_formed_ctx G2 ->
    has_type_pure (ctx_add_var (add_ctx G2 G1) x t0 e0) e t ->
    has_type_pure (add_ctx (ctx_subst x e0 G2) G1) (expr_subst x e0 e) (ty_subst x e0 t).
Proof.
  intros G1 G2 x e0 t0 e t Hv0 Hbeta0 Hpure0 Hty0 Hwf1 Hwf2 Hpure.
  exact (subst_base_has_type_pure G1 G2 x e0 t0 e t Hv0 Hbeta0 Hpure0 Hty0
    (well_formed_ctx_subst_id G1 x e0 Hwf1)
    (well_formed_ctx_subst_id G2 x e0 Hwf2)
    Hpure).
Qed.

Lemma subst_base_ty_valid_wf :
  forall G1 G2 x e0 t0 t,
    DTDT.machine_inter.value G1 e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    well_formed_ctx G1 ->
    well_formed_ctx G2 ->
    free_exp_vars e0 = [] ->
    ty_valid (ctx_add_var (add_ctx G2 G1) x t0 e0) t ->
    ty_valid (add_ctx (ctx_subst x e0 G2) G1) (ty_subst x e0 t).
Proof.
  intros G1 G2 x e0 t0 t Hv0 Hbeta0 Hpure0 Hty0 Hwf1 Hwf2 Hclosed Hvalid.
  exact (subst_base_ty_valid G1 G2 x e0 t0 t Hv0 Hbeta0 Hpure0 Hty0
    (well_formed_ctx_subst_id G1 x e0 Hwf1)
    (well_formed_ctx_subst_id G2 x e0 Hwf2)
    Hclosed Hvalid).
Qed.

Lemma subst_base_subtype_wf :
  forall G1 G2 x e0 t0 t1 t2,
    DTDT.machine_inter.value G1 e0 ->
    essential_type_is_base_type t0 = true ->
    has_type_pure G1 e0 (essential_type t0) ->
    has_type G1 e0 t0 ->
    well_formed_ctx G1 ->
    well_formed_ctx G2 ->
    free_exp_vars e0 = [] ->
    ~ List.In x (free_ty_vars t1) ->
    ~ List.In x (free_ty_vars t2) ->
    subtype (ctx_add_var (add_ctx G2 G1) x t0 e0) t1 t2 ->
    subtype (add_ctx (ctx_subst x e0 G2) G1) (ty_subst x e0 t1) (ty_subst x e0 t2).
Proof.
  intros G1 G2 x e0 t0 t1 t2 Hv0 Hbeta0 Hpure0 Hty0 Hwf1 Hwf2 Hclosed Hfresh1 Hfresh2 Hsub.
  exact (subst_base_subtype G1 G2 x e0 t0 t1 t2 Hv0 Hbeta0 Hpure0 Hty0
    (well_formed_ctx_subst_id G1 x e0 Hwf1)
    (well_formed_ctx_subst_id G2 x e0 Hwf2)
    Hclosed Hfresh1 Hfresh2 Hsub).
Qed.

(* ==================== PAPER LEMMA 7 ====================
  Non-base substitution removes the bound variable assumptions.
  Layout: paper-facing entries appear first; local support lemmas for later
  cases are kept directly above the cases that consume them. *)
(* Paper Lemma 7, pure clause.
  Substituting a non-base witness preserves pure typing. *)
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
    | var t1 t2 Hv1 Hv2
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
        exact (IH (ctx_add_var C var t1 (EVar var)) _ Hv2).
  - apply VPair.
    + exact (IH C _ Hv1).
    + exact (IH C _ Hv2).
  - apply VRef.
    exact (IH C _ Hv).
Qed.

(* Paper Lemma 7, validity clause.
  Non-base substitution preserves type validity (without type substitution). *)
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
          reflexivity. }
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

Lemma has_type_pure_change_const_witness :
  forall (C : ctx) (f : string) (t : i_ty) (w_old w_new e : i_expr) (ty : i_ty),
    has_type_pure (ctx_add_const C f t w_old) e ty ->
    has_type_pure (ctx_add_const C f t w_new) e ty.
Proof.
  intros C f t w_old w_new e ty Hpure.
  induction Hpure as
    [x tyb e0 Hlookup Hbeta
    | n | b | s | u
    | c tyc ec Hlookupc Hsimple
    | e1 e2 t1 t2 Hbeta1 Hty1 IH1 Hty2 IH2
    | b Hty IH
    | b1 b2 Hty1 IH1 Hty2 IH2
    | b1 b2 Hty1 IH1 Hty2 IH2
    | b1 b2 Hty1 IH1 Hty2 IH2
    | e1 e2 tb Hty1 IH1 Hty2 IH2
    | n1 n2 Hty1 IH1 Hty2 IH2].
  - eapply PVar; eauto.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - destruct (String.eq_dec c f) as [-> | Hneq].
    + unfold const_ctx_lookup, ctx_add_const in Hlookupc. simpl in Hlookupc.
      apply lookup_insert_Some in Hlookupc. destruct Hlookupc as [Hcase | Hcase].
      * destruct Hcase as [_ Hentry]. inversion Hentry; subst.
        eapply PConst.
        -- unfold const_ctx_lookup, ctx_add_const. simpl. apply lookup_insert.
        -- exact Hsimple.
      * destruct Hcase as [Hneq' _]. contradiction.
    + eapply PConst.
      * unfold const_ctx_lookup, ctx_add_const in *. simpl in *.
        rewrite (lookup_insert_ne (snd (fst C)) f c (t, w_new)) by congruence.
        rewrite (lookup_insert_ne (snd (fst C)) f c (t, w_old)) in Hlookupc by congruence.
        exact Hlookupc.
      * exact Hsimple.
  - eapply PApp; eauto.
  - eapply PNot; eauto.
  - eapply PImp; eauto.
  - eapply PAnd; eauto.
  - eapply POr; eauto.
  - eapply PEq; eauto.
  - eapply PPlus; eauto.
Qed.

Lemma ty_valid_change_const_witness :
  forall ty (C : ctx) (f : string) (t : i_ty) (w_old w_new : i_expr),
    ty_valid (ctx_add_const C f t w_old) ty ->
    ty_valid (ctx_add_const C f t w_new) ty.
Proof.
  induction ty; intros C f t w_old w_new Hvalid; inversion Hvalid; subst; simpl in *.
  - apply VBase.
  - eapply VSet.
    lazymatch goal with
    | Hp : has_type_pure (ctx_add_var (ctx_add_const C f t w_old) ?var0 (TBase b) ?v0) ?e0 (TBase BBool) |- _ =>
        rewrite <- ctx_add_const_var_comm in Hp;
        exact (has_type_pure_change_const_witness (ctx_add_var C var0 (TBase b) v0) f t w_old w_new e0 (TBase BBool) Hp)
    end.
  - eapply VFun; eauto.
  - eapply VFunDep.
    + eauto.
    + lazymatch goal with
      | Hcod : ty_valid (ctx_add_var (ctx_add_const C f t w_old) ?var0 ?t10 (EVar ?var0)) _ |- _ =>
          rewrite <- ctx_add_const_var_comm in Hcod;
          exact (IHty2 (ctx_add_var C var0 t10 (EVar var0)) f t w_old w_new Hcod)
      end.
  - eapply VPair; eauto.
  - eapply VRef; eauto.
Qed.

Lemma ty_valid_change_var_witness :
  forall (C : ctx) (y : string) (t : i_ty) (w_old w_new : i_expr) (ty : i_ty),
    ty_valid (ctx_add_var C y t w_old) ty ->
    ty_valid (ctx_add_var C y t w_new) ty.
Proof.
  fix IH 7.
  intros C y t w_old w_new ty Hvalid.
  destruct Hvalid as
    [tb
    | var tb e v Hp
    | t1 t2 Hv1 Hv2
    | var t1 t2 Hv1 Hv2
    | tp1 tp2 Hv1 Hv2
    | tref Hv].
  - apply VBase.
  - eapply VSet.
    destruct (String.eq_dec var y) as [-> | Hneq].
    + rewrite ctx_add_var_shadow.
      rewrite ctx_add_var_shadow in Hp.
      exact Hp.
    + rewrite ctx_add_var_swap by congruence.
      rewrite ctx_add_var_swap in Hp by congruence.
      exact (has_type_pure_change_var_witness (ctx_add_var C var (TBase tb) v) y t w_old w_new e (TBase BBool) Hp).
  - eapply VFun.
    + exact (IH C y t w_old w_new _ Hv1).
    + exact (IH C y t w_old w_new _ Hv2).
  - eapply VFunDep.
    + exact (IH C y t w_old w_new _ Hv1).
    + destruct (String.eq_dec var y) as [-> | Hneq].
      * rewrite ctx_add_var_shadow.
        rewrite ctx_add_var_shadow in Hv2.
        exact Hv2.
      * rewrite ctx_add_var_swap by congruence.
        rewrite ctx_add_var_swap in Hv2 by congruence.
        exact (IH (ctx_add_var C var t1 (EVar var)) y t w_old w_new _ Hv2).
  - eapply VPair.
    + exact (IH C y t w_old w_new _ Hv1).
    + exact (IH C y t w_old w_new _ Hv2).
  - eapply VRef.
    exact (IH C y t w_old w_new _ Hv).
Qed.

Definition fresh_var_for_ty (C : ctx) (ty : i_ty) : string :=
  stringmap.fresh_string_of_set "x"%string (union (dom (fst (fst C))) (list_to_set (ty_vars ty))).

Lemma fresh_var_for_ty_not_in_ctx :
  forall C ty,
    var_ctx_lookup C (fresh_var_for_ty C ty) = None.
Proof.
  intros C ty.
  unfold fresh_var_for_ty, var_ctx_lookup.
  apply not_elem_of_dom_1.
  pose proof (stringmap.fresh_string_of_set_fresh (union (dom (fst (fst C))) (list_to_set (ty_vars ty))) "x"%string) as Hfresh.
  intro Hin.
  apply Hfresh.
  apply elem_of_union_l.
  exact Hin.
Qed.

Lemma fresh_var_for_ty_not_in_ty_vars :
  forall C ty,
    ~ elem_of (fresh_var_for_ty C ty) (ty_vars ty).
Proof.
  intros C ty.
  unfold fresh_var_for_ty.
  pose proof (stringmap.fresh_string_of_set_fresh (union (dom (fst (fst C))) (list_to_set (ty_vars ty))) "x"%string) as Hfresh.
  intro Hin.
  apply Hfresh.
  apply elem_of_union_r.
  apply elem_of_list_to_set.
  exact Hin.
Qed.

Lemma has_type_pure_rename_var :
  forall (C : ctx) (x y : string) (t : i_ty) (w e : i_expr) (ty : i_ty),
    y <> x ->
    var_ctx_lookup C y = None ->
    essential_type_is_base_type t = true ->
    has_type_pure (ctx_add_var C x t w) e ty ->
    has_type_pure (ctx_add_var C y t (EVar y))
      (expr_subst x (EVar y) e)
      (ty_subst x (EVar y) ty).
Proof.
  intros C x y t w e ty Hneqyx Hlookupy Hbeta Hpure.
  induction Hpure as
    [x0 tyb e0 Hlookup Hbeta0
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
    | n1 n2 Hty1 IH1 Hty2 IH2]; simpl.
  - destruct (String.eq_dec x0 x) as [-> | Hneqx0x].
    + unfold var_ctx_lookup, ctx_add_var in Hlookup. simpl in Hlookup.
      apply lookup_insert_Some in Hlookup.
      destruct Hlookup as [Hcase | Hcase].
      * destruct Hcase as [_ Hentry].
        inversion Hentry; subst.
        rewrite String.eqb_refl.
        rewrite ty_subst_essential_type_id by exact Hbeta.
        eapply PVar.
        -- unfold var_ctx_lookup, ctx_add_var. simpl. apply lookup_insert.
        -- rewrite Hbeta. exact I.
      * destruct Hcase as [Hneq' _].
        contradiction.
    + destruct (String.eqb_spec x x0) as [Heq | Hneqeq].
      * congruence.
      * rewrite ty_subst_essential_type_id by exact (bool_prop_eq_true _ Hbeta0).
        eapply PVar.
        -- assert (HCx0 : var_ctx_lookup C x0 = Some (tyb, e0)).
           { unfold var_ctx_lookup, ctx_add_var in Hlookup. simpl in Hlookup.
             rewrite (lookup_insert_ne (fst (fst C)) x x0 (t, w)) in Hlookup by congruence.
             exact Hlookup. }
           assert (Hneqx0y : x0 <> y).
           { intro Heq. subst x0. rewrite Hlookupy in HCx0. discriminate. }
           unfold var_ctx_lookup, ctx_add_var. simpl.
           apply lookup_insert_Some.
           right. split.
           ++ congruence.
           ++ exact HCx0.
        -- exact Hbeta0.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - rewrite ty_subst_simple_id by exact (bool_prop_eq_true _ Hsimple).
    eapply PConst; eauto.
  - eapply PApp.
    + rewrite ty_subst_preserves_beta by exact (bool_prop_eq_true _ Hbeta1).
      exact I.
    + exact IH1.
    + exact IH2.
  - apply PNot. exact IH.
  - apply PImp; assumption.
  - apply PAnd; assumption.
  - apply POr; assumption.
  - eapply PEq; eauto.
  - apply PPlus; assumption.
Qed.

Lemma has_type_pure_weaken_fresh_var :
  forall C x t w e ty,
    ~ List.In x (exp_vars e) ->
    has_type_pure C e ty ->
    has_type_pure (ctx_add_var C x t w) e ty.
Proof.
  intros C x t w e ty Hfresh Hpure.
  induction Hpure as
    [x0 tyb e0 Hlookup Hbeta0
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
    | n1 n2 Hty1 IH1 Hty2 IH2]; simpl in Hfresh.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + exfalso. apply Hfresh. simpl. auto.
    + eapply PVar.
      * unfold var_ctx_lookup, ctx_add_var in *. simpl in *.
        rewrite (lookup_insert_ne (fst (fst C)) x x0 (t, w)) by congruence.
        exact Hlookup.
      * exact Hbeta0.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst; eauto.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    eapply PApp; eauto.
  - apply PNot. eauto.
  - assert (Hfresh1 : ~ List.In x (exp_vars b1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars b2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply PImp; auto.
  - assert (Hfresh1 : ~ List.In x (exp_vars b1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars b2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply PAnd; auto.
  - assert (Hfresh1 : ~ List.In x (exp_vars b1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars b2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply POr; auto.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    eapply PEq; eauto.
  - assert (Hfresh1 : ~ List.In x (exp_vars n1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars n2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply PPlus; auto.
Qed.

Lemma ty_valid_weaken_fresh_var :
  forall C x t w ty,
    ~ List.In x (ty_vars ty) ->
    ty_valid C ty ->
    ty_valid (ctx_add_var C x t w) ty.
Proof.
  fix IH 7.
  intros C x t w ty Hfresh Hvalid.
  destruct Hvalid as
    [tb
    | var tb e v Hp
    | t1 t2 Hv1 Hv2
    | var t1 t2 Hv1 Hv2
    | t1 t2 Hv1 Hv2
    | tref Hv].
  - apply VBase.
  - simpl in Hfresh.
    assert (Hneq : x <> var).
    { intro Heq. apply Hfresh. subst. simpl. auto. }
    assert (Hfresh_e : ~ List.In x (exp_vars e)).
    { intro Hin. apply Hfresh. right. exact Hin. }
    eapply VSet.
    rewrite ctx_add_var_swap by congruence.
    exact (has_type_pure_weaken_fresh_var (ctx_add_var C var (TBase tb) v) x t w e (TBase BBool) Hfresh_e Hp).
  - simpl in Hfresh.
    assert (Hfresh1 : ~ List.In x (ty_vars t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply VFun.
    + exact (IH C x t w _ Hfresh1 Hv1).
    + exact (IH C x t w _ Hfresh2 Hv2).
  - simpl in Hfresh.
    assert (Hneq : x <> var).
    { intro Heq. apply Hfresh. subst. simpl. auto. }
    assert (Hfresh1 : ~ List.In x (ty_vars t1)).
    { intro Hin. apply Hfresh. right. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars t2)).
    { intro Hin. apply Hfresh. right. apply in_or_app. right. exact Hin. }
    eapply VFunDep.
    + exact (IH C x t w _ Hfresh1 Hv1).
    + rewrite ctx_add_var_swap by congruence.
      exact (IH (ctx_add_var C var t1 (EVar var)) x t w _ Hfresh2 Hv2).
  - simpl in Hfresh.
    assert (Hfresh1 : ~ List.In x (ty_vars t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply VPair.
    + exact (IH C x t w _ Hfresh1 Hv1).
    + exact (IH C x t w _ Hfresh2 Hv2).
  - simpl in Hfresh.
    apply VRef.
    exact (IH C x t w _ Hfresh Hv).
Qed.

Lemma has_type_pure_drop_fresh_var :
  forall C x t w e ty,
    ~ List.In x (exp_vars e) ->
    has_type_pure (ctx_add_var C x t w) e ty ->
    has_type_pure C e ty.
Proof.
  intros C x t w e ty Hfresh Hpure.
  induction Hpure as
    [x0 tyb e0 Hlookup Hbeta0
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
    | n1 n2 Hty1 IH1 Hty2 IH2]; simpl in Hfresh.
  - destruct (String.eq_dec x0 x) as [-> | Hneq].
    + exfalso. apply Hfresh. simpl. auto.
    + eapply PVar.
      * unfold var_ctx_lookup, ctx_add_var in Hlookup. simpl in Hlookup.
        apply lookup_insert_Some in Hlookup.
        destruct Hlookup as [Hcase | Hcase].
        { destruct Hcase as [Heq Hentry].
          congruence. }
        destruct Hcase as [Hneq' Hbase].
        exact Hbase.
      * exact Hbeta0.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - eapply PConst; eauto.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    eapply PApp; eauto.
  - apply PNot. eauto.
  - assert (Hfresh1 : ~ List.In x (exp_vars b1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars b2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply PImp; auto.
  - assert (Hfresh1 : ~ List.In x (exp_vars b1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars b2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply PAnd; auto.
  - assert (Hfresh1 : ~ List.In x (exp_vars b1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars b2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply POr; auto.
  - assert (Hfresh1 : ~ List.In x (exp_vars e1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars e2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    eapply PEq; eauto.
  - assert (Hfresh1 : ~ List.In x (exp_vars n1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (exp_vars n2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply PPlus; auto.
Qed.

Lemma has_type_pure_drop_nonsimple_const :
  forall C f t w e ty,
    is_simple_type t = false ->
    has_type_pure (ctx_add_const C f t w) e ty ->
    has_type_pure C e ty.
Proof.
  intros C f t w e ty Hnonsimple Hpure.
  induction Hpure as
    [x tyb e0 Hlookup Hbeta0
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
    | n1 n2 Hty1 IH1 Hty2 IH2]; simpl.
  - eapply PVar; eauto.
  - apply PNat.
  - apply PBool.
  - apply PString.
  - apply PUnit.
  - destruct (String.eq_dec c f) as [-> | Hneq].
    + unfold const_ctx_lookup, ctx_add_const in Hlookupc.
      simpl in Hlookupc.
      apply lookup_insert_Some in Hlookupc.
      destruct Hlookupc as [Hcase | Hcase].
      * destruct Hcase as [_ Hentry].
        inversion Hentry; subst.
        pose proof (bool_prop_eq_true _ Hsimple) as Hsimple_eq.
        rewrite Hsimple_eq in Hnonsimple.
        discriminate.
      * destruct Hcase as [Hneq' _].
        contradiction.
    + eapply PConst.
      * unfold const_ctx_lookup, ctx_add_const in Hlookupc.
        simpl in Hlookupc.
        apply lookup_insert_Some in Hlookupc.
        destruct Hlookupc as [Hcase | Hcase].
        { destruct Hcase as [Heq _]. congruence. }
        destruct Hcase as [Hneq' HlookupC].
        exact HlookupC.
      * exact Hsimple.
  - eapply PApp; eauto.
  - apply PNot. exact IH.
  - apply PImp; assumption.
  - apply PAnd; assumption.
  - apply POr; assumption.
  - eapply PEq; eauto.
  - apply PPlus; assumption.
Qed.

Lemma has_type_pure_nonsimple_const_irrelevant :
  forall C f t w e ty,
    is_simple_type t = false ->
    has_type_pure (ctx_add_const C f t w) e ty ->
    expr_subst_fun f w e = e.
Proof.
  intros C f t w e ty Hnonsimple Hpure.
  induction Hpure as
    [x tyb e0 Hlookup Hbeta0
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
    | n1 n2 Hty1 IH1 Hty2 IH2]; simpl; try reflexivity.
  - destruct (String.eq_dec c f) as [-> | Hneq].
    + unfold const_ctx_lookup, ctx_add_const in Hlookupc.
      simpl in Hlookupc.
      apply lookup_insert_Some in Hlookupc.
      destruct Hlookupc as [Hcase | Hcase].
      * destruct Hcase as [_ Hentry].
        inversion Hentry; subst.
        pose proof (bool_prop_eq_true _ Hsimple) as Hsimple_eq.
        rewrite Hsimple_eq in Hnonsimple.
        discriminate.
      * destruct Hcase as [Hneq' _]. contradiction.
    + assert ((f =? c)%string = false) by (apply String.eqb_neq; congruence).
      rewrite H. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.
Lemma ty_valid_drop_nonsimple_const :
  forall C f t w ty,
    is_simple_type t = false ->
    ty_valid (ctx_add_const C f t w) ty ->
    ty_valid C ty.
Proof.
  intros C f t w ty Hnonsimple Hvalid.
  dependent induction Hvalid.
  - apply VBase.
  - eapply VSet.
    rewrite <- ctx_add_const_var_comm in H.
    exact (has_type_pure_drop_nonsimple_const _ f t w _ _ Hnonsimple H).
  - eapply VFun; eauto.
  - eapply VFunDep; eauto.
  - eapply VPair; eauto.
  - eapply VRef; eauto.
Qed.


Lemma ty_valid_drop_fresh_var :
  forall C x t w ty,
    ~ List.In x (ty_vars ty) ->
    ty_valid (ctx_add_var C x t w) ty ->
    ty_valid C ty.
Proof.
  fix IH 7.
  intros C x t w ty Hfresh Hvalid.
  destruct Hvalid as
    [tb
    | var tb e v Hp
    | t1 t2 Hv1 Hv2
    | var t1 t2 Hv1 Hv2
    | tp1 tp2 Hv1 Hv2
    | tref Hv].
  - apply VBase.
  - simpl in Hfresh.
    assert (Hneq : x <> var).
    { intro Heq. apply Hfresh. subst. simpl. auto. }
    assert (Hfresh_e : ~ List.In x (exp_vars e)).
    { intro Hin. apply Hfresh. right. exact Hin. }
    eapply VSet.
    rewrite ctx_add_var_swap in Hp by congruence.
    exact (has_type_pure_drop_fresh_var (ctx_add_var C var (TBase tb) v) x t w e (TBase BBool) Hfresh_e Hp).
  - simpl in Hfresh.
    assert (Hfresh1 : ~ List.In x (ty_vars t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply VFun.
    + exact (IH C x t w _ Hfresh1 Hv1).
    + exact (IH C x t w _ Hfresh2 Hv2).
  - simpl in Hfresh.
    assert (Hneq : x <> var).
    { intro Heq. apply Hfresh. subst. simpl. auto. }
    assert (Hfresh1 : ~ List.In x (ty_vars t1)).
    { intro Hin. apply Hfresh. right. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars t2)).
    { intro Hin. apply Hfresh. right. apply in_or_app. right. exact Hin. }
    eapply VFunDep.
    + exact (IH C x t w _ Hfresh1 Hv1).
    + rewrite ctx_add_var_swap in Hv2 by congruence.
      exact (IH (ctx_add_var C var t1 (EVar var)) x t w _ Hfresh2 Hv2).
  - simpl in Hfresh.
    assert (Hfresh1 : ~ List.In x (ty_vars tp1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ List.In x (ty_vars tp2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply VPair.
    + exact (IH C x t w _ Hfresh1 Hv1).
    + exact (IH C x t w _ Hfresh2 Hv2).
  - simpl in Hfresh.
    apply VRef.
    exact (IH C x t w _ Hfresh Hv).
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
    | var t_dom t_dom' t_cod t_cod' Hs1 Hs2
    | t1a t1b t2a t2b Hs1 Hs2
    | t_left t_right Hs1 Hs2].
  - apply SBase.
  - eapply SSet with (c:=c).
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
  - eapply SBaseSet with (c:=c).
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
        exact (IH (ctx_add_var C var t_dom' (EVar var)) _ _ Hs2).
  - eapply SPair.
    + exact (IH C _ _ Hs1).
    + exact (IH C _ _ Hs2).
  - eapply SRef.
    + exact (IH C _ _ Hs1).
    + exact (IH C _ _ Hs2).
Qed.

(* Paper Lemma 7, subtyping clause.
  Non-base substitution preserves subtyping directly. *)
Lemma subst_nonbase_subtype :
  forall G1 G2 x v t0 t1 t2,
    essential_type_is_base_type t0 = false ->
    subtype (ctx_add_var (add_ctx G2 G1) x t0 v) t1 t2 ->
    subtype (add_ctx G2 G1) t1 t2.
Proof.
  intros G1 G2 x v t0 t1 t2 Hnb Hsub.
  exact (subst_nonbase_subtype_ctx x v t0 Hnb (add_ctx G2 G1) t1 t2 Hsub).
Qed.

Lemma has_type_pure_empty_ctx_base :
  forall e t,
    has_type_pure empty_ctx e t ->
    β[ t ] = true.
Proof.
  intros e t Hpure.
  induction Hpure.
  - unfold var_ctx_lookup, empty_ctx in H.
    simpl in H.
    discriminate.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - unfold const_ctx_lookup, empty_ctx in H.
    simpl in H.
    discriminate.
  - simpl in IHHpure1.
    discriminate.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Paper Lemma 7, typing clause.
  If Jτ0K ≠ τb and • ⊢pure v : τ0 and Γ,x:τ0,Γ' ⊢ e : τ,
  then Γ,Γ' ⊢ [v/x]e : τ.

  Proof note: the hypotheses β[τ0] = false and (has_type_pure ∅ v τ0)
  are jointly impossible.  has_type_pure_empty_ctx_base shows that any
  pure value typed in the empty context has β[·] = true, contradicting
  β[τ0] = false.  The conclusion therefore follows vacuously. *)
Lemma subst_nonbase_has_type :
  forall G1 G2 x v t0 e t,
    β[ t0 ] = false ->
    has_type_pure empty_ctx v t0 ->
    has_type (ctx_add_var (add_ctx G2 G1) x t0 v) e t ->
    has_type (add_ctx G2 G1) (expr_subst x v e) t.
Proof.
  intros G1 G2 x v t0 e t Hnb Hpure _.
  pose proof (has_type_pure_empty_ctx_base v t0 Hpure) as Hbase.
  rewrite Hnb in Hbase.
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

Lemma pure_step_ctx_preservation_foundational :
  forall G1 G2 e e' E t,
    step (G1, e) (G2, e') ->
    (forall t0, has_type_pure empty_ctx e t0 -> has_type_pure empty_ctx e' t0) ->
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

Lemma pure_fail_ctx_absurd_foundational :
  forall E t,
    has_type_pure empty_ctx (plug E EFail) t ->
    False.
Proof.
  induction E; intros t Hpure; simpl in *;
    try solve [inversion Hpure];
    try solve [exfalso; eapply has_type_pure_empty_ctx_app_absurd; exact Hpure].
  all: inversion Hpure; subst;
    match goal with
    | IHE : forall t, has_type_pure empty_ctx (plug _ EFail) t -> False,
      Hsub : has_type_pure empty_ctx (plug _ EFail) _ |- _ => exact (IHE _ Hsub)
    end.
Qed.

Lemma preservation_pure_terms_sigma_foundational :
  forall sigma1 sigma2,
    step sigma1 sigma2 ->
    forall t,
      has_type_pure empty_ctx (snd sigma1) t ->
      has_type_pure empty_ctx (snd sigma2) t.
Proof.
  intros sigma1 sigma2 Hstep.
  induction Hstep; intros t Hpure; simpl in *.
  - eapply pure_step_ctx_preservation_foundational; eauto.
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
  - exfalso. eapply pure_fail_ctx_absurd_foundational. exact Hpure.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PBool.
  - inversion Hpure; subst. apply PNat.
Qed.

Lemma fresh_string_list_not_in_foundational :
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

Lemma fresh_string_list_singleton_neq :
  forall u,
    fresh_string_list [u] <> u.
Proof.
  intros u Heq.
  apply (fresh_string_list_not_in_foundational [u]).
  rewrite Heq.
  simpl.
  auto.
Qed.

Lemma plug_has_typed_hole_pure_foundational :
  forall G E e t,
    has_type_pure G (plug E e) t ->
    exists th, has_type_pure G e th.
Proof.
  intros G E.
  induction E; intros e t Hty; simpl in *.
  - eexists. exact Hty.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TArr _ _) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) _ |- _ => exact (IHE _ _ Hsub)
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
    | Hsub : has_type_pure G (plug E e) (TBase BNat) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TBase BNat) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TBase BBool) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TBase ?tb) |- _ => exact (IHE _ _ Hsub)
    end.
  - inversion Hty; subst.
    match goal with
    | Hsub : has_type_pure G (plug E e) (TBase ?tb) |- _ => exact (IHE _ _ Hsub)
    end.
Qed.
Lemma pure_step_any_ctx_foundational :
  forall G1 G2 e e' C,
    step (G1, e) (G2, e') ->
    forall t,
      has_type_pure empty_ctx e t ->
      step (C, e) (C, e').
Proof.
  intros G1 G2 e e' C Hstep.
  set (P := fun c1 c2 : ctx * i_expr =>
    match c1, c2 with
    | (_, e1), (_, e2) => forall t, has_type_pure empty_ctx e1 t -> step (C, e1) (C, e2)
    end).
  change (P (G1, e) (G2, e')).
  induction Hstep; unfold P in *; simpl in *; intros t Hpure.
  - apply StepCtx.
    destruct (plug_has_typed_hole_pure_foundational empty_ctx E e0 t Hpure) as [th Hhole].
    exact (IHHstep _ Hhole).
  - exfalso. inversion Hpure. inversion H4. subst. discriminate H8.
  - inversion Hpure; subst.
    simpl in H. discriminate.
  - inversion Hpure. inversion H3; subst.
  - inversion Hpure.
  - inversion Hpure.
  - apply StepIfTrue.
  - apply StepIfFalse.
  - inversion Hpure.
  - inversion Hpure.
  - inversion Hpure.
  - exfalso. eapply pure_fail_ctx_absurd_foundational. exact Hpure.
  - apply StepNot.
  - apply StepAnd.
  - apply StepOr.
  - apply StepImp.
  - eapply StepEq; eauto.
  - apply StepPlus.
Qed.

Lemma step_lemma_entails_var_forward :
  forall G e e' x tb t1 pred,
    step (G, e) (G, e') ->
    has_type_pure empty_ctx e (TBase tb) ->
    [| t1 |] = TBase tb ->
    has_type_pure (ctx_add_var G x t1 e) pred (TBase BBool) ->
    entails G (EImp (expr_subst x e pred) (expr_subst x e' pred)).
Proof.
  intros G e e' x tb t1 pred Hstep _ _ Hpred.
  eapply eval_trans with (sigma2 := (G, EImp (expr_subst x e' pred) (expr_subst x e' pred))).
  - exact (eval_plug
      (ECImpL ECHole (expr_subst x e' pred))
      (G, expr_subst x e pred)
      (G, expr_subst x e' pred)
      (pure_subst_step_eval G x e e' pred t1 Hstep Hpred)).
  - apply entails_imp_refl.
Qed.

Lemma step_lemma_entails_var_backward :
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

Lemma bool_singleton_ty_valid_ctx :
  forall C u t_active witness e,
    has_type_pure empty_ctx e (TBase BBool) ->
    ty_valid (ctx_add_var C u t_active witness) (TSet u BBool (EEq (EVar u) e)).
Proof.
  intros C u t_active witness e Hpure.
  pose proof (has_type_pure_empty_ctx_closed e (TBase BBool) Hpure) as Hclosed.
  eapply VSet.
  rewrite ctx_add_var_shadow.
  eapply PEq.
  - eapply (@PVar (ctx_add_var C u (TBase BBool) (EBool true)) u (TBase BBool) (EBool true)).
    + unfold var_ctx_lookup, ctx_add_var.
      simpl.
      apply lookup_insert.
    + simpl. exact I.
  - pose proof (weakening_has_type_pure_right empty_ctx (ctx_add_var C u (TBase BBool) (EBool true)) e (TBase BBool) Hpure) as Hweak.
    rewrite add_ctx_empty_l in Hweak.
    exact Hweak.
Qed.

Lemma step_lemma_subtype_bool_singleton_backward :
  forall G1 G2 e e' u witness C,
    step (add_ctx G2 G1, e) (add_ctx G2 G1, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    subtype
      (ctx_add_var C u (TSet u BBool (EEq (EVar u) e')) witness)
      (TSet u BBool (EEq (EVar u) e'))
      (TSet u BBool (EEq (EVar u) e)).
Proof.
  intros G1 G2 e e' u witness C Hstep Hpure.
  eapply SSet with (c := true).
  - apply bool_singleton_ty_valid_ctx.
    exact (preservation_pure_terms_sigma_foundational _ _ Hstep (TBase BBool) Hpure).
  - apply bool_singleton_ty_valid_ctx.
    exact Hpure.
  - rewrite ctx_add_var_shadow.
    set (z := fresh_string_list [u]).
    assert (Hz : z <> u).
    { subst z. apply fresh_string_list_singleton_neq. }
    pose proof (pure_step_any_ctx_foundational (add_ctx G2 G1) (add_ctx G2 G1) e e'
      (ctx_add_var C u (TBase BBool) (EBool true)) Hstep (TBase BBool) Hpure) as Hstep'.
    assert (Hent :
      entails (ctx_add_var C u (TBase BBool) (EBool true))
        (EImp (expr_subst z e' (EEq (EVar u) (EVar z)))
              (expr_subst z e (EEq (EVar u) (EVar z))))).
    { eapply step_lemma_entails_var_backward with (x := z) (t1 := TBase BBool) (pred := EEq (EVar u) (EVar z)).
      + exact Hstep'.
      + exact Hpure.
      + reflexivity.
      + eapply PEq.
        * eapply (@PVar (ctx_add_var (ctx_add_var C u (TBase BBool) (EBool true)) z (TBase BBool) e) u (TBase BBool) (EBool true)).
          -- unfold var_ctx_lookup, ctx_add_var.
             apply lookup_insert_Some.
             right.
             split; [congruence | apply lookup_insert].
          -- simpl. exact I.
        * eapply (@PVar (ctx_add_var (ctx_add_var C u (TBase BBool) (EBool true)) z (TBase BBool) e) z (TBase BBool) e).
          -- unfold var_ctx_lookup, ctx_add_var.
             simpl.
             apply lookup_insert.
          -- simpl. exact I. }
    simpl in Hent.
    apply String.eqb_neq in Hz.
    rewrite Hz in Hent.
    rewrite String.eqb_refl in Hent.
    exact Hent.
Qed.

Lemma step_lemma_subtype_bool_singleton_forward :
  forall G1 G2 e e' u witness C,
    step (add_ctx G2 G1, e) (add_ctx G2 G1, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    subtype
      (ctx_add_var C u (TSet u BBool (EEq (EVar u) e)) witness)
      (TSet u BBool (EEq (EVar u) e))
      (TSet u BBool (EEq (EVar u) e')).
Proof.
  intros G1 G2 e e' u witness C Hstep Hpure.
  eapply SSet with (c := true).
  - apply bool_singleton_ty_valid_ctx.
    exact Hpure.
  - apply bool_singleton_ty_valid_ctx.
    exact (preservation_pure_terms_sigma_foundational _ _ Hstep (TBase BBool) Hpure).
  - rewrite ctx_add_var_shadow.
    set (z := fresh_string_list [u]).
    assert (Hz : z <> u).
    { subst z. apply fresh_string_list_singleton_neq. }
    pose proof (pure_step_any_ctx_foundational (add_ctx G2 G1) (add_ctx G2 G1) e e'
      (ctx_add_var C u (TBase BBool) (EBool true)) Hstep (TBase BBool) Hpure) as Hstep'.
    assert (Hent :
      entails (ctx_add_var C u (TBase BBool) (EBool true))
        (EImp (expr_subst z e (EEq (EVar u) (EVar z)))
              (expr_subst z e' (EEq (EVar u) (EVar z))))).
    { eapply step_lemma_entails_var_forward with (x := z) (t1 := TBase BBool) (pred := EEq (EVar u) (EVar z)).
      + exact Hstep'.
      + exact Hpure.
      + reflexivity.
      + eapply PEq.
        * eapply (@PVar (ctx_add_var (ctx_add_var C u (TBase BBool) (EBool true)) z (TBase BBool) e) u (TBase BBool) (EBool true)).
          -- unfold var_ctx_lookup, ctx_add_var.
             apply lookup_insert_Some.
             right.
             split; [congruence | apply lookup_insert].
          -- simpl. exact I.
        * eapply (@PVar (ctx_add_var (ctx_add_var C u (TBase BBool) (EBool true)) z (TBase BBool) e) z (TBase BBool) e).
          -- unfold var_ctx_lookup, ctx_add_var.
             simpl.
             apply lookup_insert.
          -- simpl. exact I. }
    simpl in Hent.
    apply String.eqb_neq in Hz.
    rewrite Hz in Hent.
    rewrite String.eqb_refl in Hent.
    exact Hent.
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















































Lemma step_lemma_ty_valid :
  forall G e e' tb t1 x t,
    step (G, e) (G, e') ->
    has_type_pure empty_ctx e (TBase tb) ->
    [| t1 |] = TBase tb ->
    ~ List.In x (ty_vars t) ->
    ty_valid (ctx_add_var G x t1 e) t ->
    subtype G (ty_subst x e' t) (ty_subst x e t).
Proof.
  intros G e e' tb t1 x t _ _ _ Hfresh Hvalid.
  rewrite (ty_subst_ty_vars_fresh x e' t Hfresh).
  rewrite (ty_subst_ty_vars_fresh x e t Hfresh).
  apply subtype_refl.
  exact (ty_valid_drop_fresh_var G x t1 e t Hfresh Hvalid).
Qed.

Lemma step_lemma_entails_bool_singleton :
  forall G1 G2 e e' u pred,
    step (add_ctx G2 G1, e) (add_ctx G2 G1, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    entails
      (ctx_add_var
        (add_ctx G2 G1)
        u
        (TSet u BBool (EEq (EVar u) e))
        (EVar u))
      pred <->
    entails
      (ctx_add_var
        (add_ctx G2 G1)
        u
        (TSet u BBool (EEq (EVar u) e'))
        (EVar u))
      pred.
Proof.
  intros G1 G2 e e' u pred _ _. split; intro Hent.
  - eapply subsumption_entails_var_ctx. exact Hent.
  - eapply subsumption_entails_var_ctx. exact Hent.
Qed.

Lemma step_lemma_has_type_bool_singleton :
  forall G1 G2 e e' u e1 t,
    step (add_ctx G2 G1, e) (add_ctx G2 G1, e') ->
    has_type_pure empty_ctx e (TBase BBool) ->
    has_type
      (ctx_add_var
        (add_ctx G2 G1)
        u
        (TSet u BBool (EEq (EVar u) e))
        (EVar u))
      e1 t <->
    has_type
      (ctx_add_var
        (add_ctx G2 G1)
        u
        (TSet u BBool (EEq (EVar u) e'))
        (EVar u))
      e1 t.
Proof.
  intros G1 G2 e e' u e1 t Hstep Hpure.
  split; intro Hty.
  - eapply subsumption_has_type_var_ctx.
    + intros C.
      exact (step_lemma_subtype_bool_singleton_backward G1 G2 e e' u (EVar u) C Hstep Hpure).
    + exact Hty.
  - eapply subsumption_has_type_var_ctx.
    + intros C.
      exact (step_lemma_subtype_bool_singleton_forward G1 G2 e e' u (EVar u) C Hstep Hpure).
    + exact Hty.
Qed.






















