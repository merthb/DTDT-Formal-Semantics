Require Import Coq.Program.Equality.
Require Import DTDT.syntax.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.semantic_rules_surf.
Require Import DTDT.type_directed_translation.
Require Import DTDT.translation_soundness_lemmas.

(* ==================== PAPER LEMMA 14 ====================
   If translated subtyping holds, then the corresponding erased simple types agree. *)
Lemma simple_type_match_subtype :
  forall Γ τ₁ τ₂,
    subtype (trans_ctx_surf Γ) (trans_type τ₁) (trans_type τ₂) ->
    [| ⟦ τ₁ ⟧ |] = [| ⟦ τ₂ ⟧ |].
Proof.
  intros Γ τ₁ τ₂ Hsub.
  induction Hsub; simpl; try reflexivity.
  - rewrite IHHsub1, IHHsub2. reflexivity.
  - rewrite IHHsub1, IHHsub2. reflexivity.
  - rewrite IHHsub1, IHHsub2. reflexivity.
  - rewrite IHHsub1, IHHsub2. reflexivity.
Qed.

(* Completeness-side simple-type match for coercions (paper form).
   A coercion judgment relates terms whose erased simple types coincide. *)
Lemma simple_type_match_coercion :
  forall w Γ e τ e'' τ'',
    ⟦ Γ ⟧c ⊢[ w ] e : ⟦ τ ⟧ ↦ e'' : ⟦ τ'' ⟧ ->
    [| ⟦ τ ⟧ |] = [| ⟦ τ'' ⟧ |].
Admitted.

(* Reference simple-type match (paper form).
   Subtyping between translated references implies equality of their erased carriers. *)
Lemma simple_type_match_ref :
  forall Γ τ₁ τ₂,
    subtype (trans_ctx_surf Γ) (TRef (trans_type τ₁)) (TRef (trans_type τ₂)) ->
    TRef [| ⟦ τ₁ ⟧ |] = TRef [| ⟦ τ₂ ⟧ |].
Proof.
  intros Γ τ₁ τ₂ Hsub.
  inversion Hsub; subst; try discriminate.
  match goal with
  | Hleft : subtype (trans_ctx_surf Γ) (trans_type τ₁) (trans_type τ₂),
    Hright : subtype (trans_ctx_surf Γ) (trans_type τ₂) (trans_type τ₁) |- _ =>
      rewrite (simple_type_match_subtype Γ τ₁ τ₂ Hleft);
      rewrite (simple_type_match_subtype Γ τ₂ τ₁ Hright);
      reflexivity
  end.
Qed.

(* ==================== PAPER LEMMA 15 ====================
   Reference completeness clause: equal erased ordinary-reference types admit a
   coercion witness. *)
Lemma completeness_of_reference_coercion :
  forall w Γ e τ e' τ',
    [| TRef ⟦ τ ⟧ |] = [| TRef ⟦ τ' ⟧ |] ->
    has_type (trans_ctx_surf Γ) e (TRef [| ⟦ τ ⟧ |]) ->
    ⟦ Γ ⟧c ⊢[ w ] e : TRef ⟦ τ ⟧ ↦ e' : TRef ⟦ τ' ⟧.
Admitted.

(* ==================== PAPER LEMMA 16 ====================
   Completeness for ordinary-to-dynamic reference coercions. *)
Lemma completeness_of_ref_to_dref_coercion :
  forall Γ e τ₁ τ₂ e₁,
    co_ref (TyRef τ₁) = true ->
    contra_ref (TyDeRef τ₂) = true ->
    has_type (trans_ctx_surf Γ) e (TRef [| ⟦ τ₁ ⟧ |]) ->
    ⟦ Γ ⟧c ⊢[ sim ] e : TRef ⟦ τ₁ ⟧ ↦
      e₁ : ⟦ TyDeRef τ₂ ⟧.
Admitted.

(* ==================== PAPER LEMMA 17 ====================
   Completeness for dynamic-to-dynamic reference coercions. *)
Lemma completeness_of_dref_coercion :
  forall Γ e τ₁ τ₂ e₁,
    co_ref (TyDeRef τ₁) = true ->
    contra_ref (TyDeRef τ₂) = true ->
    has_type (trans_ctx_surf Γ) e [| ⟦ TyDeRef τ₁ ⟧ |] ->
    ⟦ Γ ⟧c ⊢[ sim ] e : ⟦ TyDeRef τ₁ ⟧ ↦
      e₁ : ⟦ TyDeRef τ₂ ⟧.
Admitted.

(* Reference completeness theorem (paper form).
   If an internal term has the erased ordinary-reference type, then it arises from
   a source typing/translation derivation in the reference fragment. *)
Theorem completeness_of_reference_translation :
  forall w Γ e e' τ,
    has_type (trans_ctx_surf Γ) e' (TRef [| ⟦ τ ⟧ |]) ->
    Γ ⊢[ w ] e ; e' : TRef ⟦ τ ⟧ \/ Γ ⊢[ w ] e ; e' : ⟦ τ ⟧.
Admitted.

(* Dynamic-reference completeness theorem (paper form).
   If an internal term has the erased encoded-dref type, then it arises from a
   source typing/translation derivation for a dynamic reference. *)
Theorem completeness_of_dynamic_reference_translation :
  forall w Γ e e' τ,
    has_type (trans_ctx_surf Γ) e' [| dref_encoding ⟦ τ ⟧ |] ->
    Γ ⊢[ w ] e ; e' : ⟦ TyDeRef τ ⟧.
Admitted.




(* ==================== PAPER THEOREM 8 ====================
   Appendix completeness theorem for the translation. *)
(* ==================== PAPER THEOREM 3 ====================
   Completeness of translation: if ⟦Γ⟧c ⊢ e₀ : [|⟦τ⟧|], then there exist a mode
   and a source term whose translation yields e₀ at translated type ⟦τ⟧. *)
Theorem paper_theorem_3_translation_completeness :
  forall Γ e₀ τ,
    has_type (trans_ctx_surf Γ) e₀ [| ⟦ τ ⟧ |] ->
    exists w e, Γ ⊢[ w ] e ; e₀ : ⟦ τ ⟧.
Admitted.
