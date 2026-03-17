Require Import DTDT.syntax.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.semantic_rules_surf.
Require Import DTDT.type_directed_translation.
Require Import DTDT.foundational_lemmas_inter.
Require Import DTDT.type_safety_lemmas_inter.

(* ==================== PAPER LEMMA 12 ====================
   If Γ ⊢ₛvalid τ, then ⟦Γ⟧c ⊢valid ⟦τ⟧. *)
Lemma trans_type_preserves_validity :
  forall Γ τ,
    Γ ⊢ₛvalid τ ->
    ⟦ Γ ⟧c ⊢valid ⟦ τ ⟧.
Admitted.

(* The paper also has a subtyping-respect lemma here, but the current surface
   development does not yet expose a surface subtyping judgment. *)

(* ==================== PAPER LEMMA 13 ====================
   If x is available in context, then validity of τ is preserved by the erasure [[τ]]x. *)
Lemma erase_dep_var_preserves_validity :
  forall Γ x τ,
    (ctx_add_var ⟦ Γ ⟧c x (TBase BBool) (EVar x)) ⊢valid τ ->
    ⟦ Γ ⟧c ⊢valid [[ τ ]] x.
Admitted.

(* ==================== PAPER THEOREM 6 ====================
   If Γ ⊢^w e : τ ↦ e' : τ' and e has erased type [|τ|], then e' has erased type [|τ'|]. *)
Theorem soundness_of_type_coercion :
  forall w Γ e τ e' τ',
    ⟦ Γ ⟧c ⊢valid τ ->
    ⟦ Γ ⟧c ⊢valid τ' ->
    ⟦ Γ ⟧c ⊢[ w ] e : τ ↦ e' : τ' ->
    has_type (trans_ctx_surf Γ) e [| τ |] ->
    has_type (trans_ctx_surf Γ) e' [| τ' |].
Admitted.

(* ==================== PAPER THEOREM 2 ====================
   Soundness of translation: if ? ?^w e ; e' : ?, then ???c ? e' : [|?|]. *)
(* ==================== PAPER THEOREM 7 ====================
   If Γ ⊢^w e ; e' : τ, then ⟦Γ⟧c ⊢ e' : [|τ|]. *)
Theorem soundness_of_translation :
  forall w Γ e e' τ,
    Γ ⊢[ w ] e ; e' : τ ->
    has_type (trans_ctx_surf Γ) e' [| τ |].
Admitted.
(* Reference soundness clause (paper form).
   Coercions between ordinary reference types preserve the corresponding erased
   internal reference typing. *)
Lemma soundness_of_reference_coercion :
  forall w Γ e τ e' τ',
    ⟦ Γ ⟧c ⊢valid TRef τ ->
    ⟦ Γ ⟧c ⊢valid TRef τ' ->
    ⟦ Γ ⟧c ⊢[ w ] e : TRef τ ↦ e' : TRef τ' ->
    has_type (trans_ctx_surf Γ) e (TRef [| τ |]) ->
    has_type (trans_ctx_surf Γ) e' (TRef [| τ' |]).
Admitted.

(* Reference soundness clause for ref-to-dref (paper form).
   A coercion from τ ref to the encoded dynamic-reference view preserves erased typing. *)
Lemma soundness_of_ref_to_dref_coercion :
  forall Γ e τ₁ τ₂ e₁,
    co_ref (TyRef τ₁) = true ->
    contra_ref (TyDeRef τ₂) = true ->
    ⟦ Γ ⟧c ⊢valid TRef ⟦ τ₁ ⟧ ->
    ⟦ Γ ⟧c ⊢valid ⟦ TyDeRef τ₂ ⟧ ->
    ⟦ Γ ⟧c ⊢[ sim ] e : TRef ⟦ τ₁ ⟧ ↦ e₁ : ⟦ TyDeRef τ₂ ⟧ ->
    has_type (trans_ctx_surf Γ) e (TRef [| ⟦ τ₁ ⟧ |]) ->
    has_type (trans_ctx_surf Γ) e₁ [| ⟦ TyDeRef τ₂ ⟧ |].
Admitted.

(* Reference soundness clause for dref-to-dref (paper form).
   Coercions between encoded dynamic references preserve the corresponding erased typing. *)
Lemma soundness_of_dref_coercion :
  forall Γ e τ₁ τ₂ e₁,
    co_ref (TyDeRef τ₁) = true ->
    contra_ref (TyDeRef τ₂) = true ->
    ⟦ Γ ⟧c ⊢valid ⟦ TyDeRef τ₁ ⟧ ->
    ⟦ Γ ⟧c ⊢valid ⟦ TyDeRef τ₂ ⟧ ->
    ⟦ Γ ⟧c ⊢[ sim ] e : ⟦ TyDeRef τ₁ ⟧ ↦ e₁ : ⟦ TyDeRef τ₂ ⟧ ->
    has_type (trans_ctx_surf Γ) e [| ⟦ TyDeRef τ₁ ⟧ |] ->
    has_type (trans_ctx_surf Γ) e₁ [| ⟦ TyDeRef τ₂ ⟧ |].
Admitted.
