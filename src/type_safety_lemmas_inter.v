Require Import DTDT.syntax.
Require Import DTDT.entails_inter.
Require Import DTDT.machine_inter.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.foundational_lemmas_inter.

(* ==================== PAPER LEMMA 9 ====================
   If ∅ ⊢pure e : τ and e → e', then ∅ ⊢pure e' : τ. *)
Lemma preservation_pure_terms :
  forall Γ e e' τ,
    step (Γ, e) (Γ, e') ->
    empty_ctx ⊢pure e : τ ->
    empty_ctx ⊢pure e' : τ.
Admitted.

(* ==================== PAPER LEMMA 11 ====================
   If ∅ ⊢ v : bool and v is a value, then v = true or v = false. *)
Lemma canonical_forms_bool :
  forall v,
    has_type empty_ctx v (TBase BBool) ->
    DTDT.machine_inter.value empty_ctx v ->
    v = EBool true \/ v = EBool false.
Admitted.

(* Paper Lemma 11, function canonical forms.
   If ∅ ⊢ v : Πx:τ₁.τ₂ and v is a value, then v is a constant or a fixpoint. *)
Lemma canonical_forms_fun :
  forall v x τ₁ τ₂,
    has_type empty_ctx v (TArrDep x τ₁ τ₂) ->
    DTDT.machine_inter.value empty_ctx v ->
    (exists c, v = EConst c) \/
    (exists f x' dom cod body, v = EFix f x' dom cod body).
Admitted.

(* Paper Lemma 11, pair canonical forms.
   If ∅ ⊢ v : τ₁ × τ₂ and v is a value, then v = (v₁, v₂). *)
Lemma canonical_forms_pair :
  forall v τ₁ τ₂,
    has_type empty_ctx v (TProd τ₁ τ₂) ->
    DTDT.machine_inter.value empty_ctx v ->
    exists v1 v2, v = EPair v1 v2.
Admitted.

(* Paper Lemma 11, reference canonical forms.
   If ∅ ⊢ v : τ ref and v is a value, then v is a location in the store. *)
Lemma canonical_forms_ref :
  forall v τ,
    has_type empty_ctx v (TRef τ) ->
    DTDT.machine_inter.value empty_ctx v ->
    exists l stored,
      v = EVar l /\ store_ctx_lookup empty_ctx l = Some (τ, stored).
Admitted.

(* ==================== PAPER THEOREM 4 ====================
   If Γ ⊢ e : τ and (Γ, e) → (Γ', e'), then Γ' ⊢ e' : τ. *)
Theorem preservation :
  forall Γ e Γ' e' τ,
    has_type Γ e τ ->
    step (Γ, e) (Γ', e') ->
    has_type Γ' e' τ.
Admitted.

(* ==================== PAPER THEOREM 5 ====================
   If ∅ ⊢ e : τ, then e is a value, e = fail, or there exists e' with e → e'. *)
Theorem progress :
  forall e τ,
    has_type empty_ctx e τ ->
    DTDT.machine_inter.value empty_ctx e \/
    e = EFail \/
    exists e', step (empty_ctx, e) (empty_ctx, e').
Admitted.

(* ==================== PAPER THEOREM 1 ====================
   Type safety: if ∅ ⊢ e : τ and (∅, e) ↠* (∅, e₀), then e₀ is a value,
   e₀ = fail, or there exists a further step from e₀. *)
Theorem paper_theorem_1_type_safety :
  forall e τ e₀,
    has_type empty_ctx e τ ->
    (empty_ctx, e) ↠* (empty_ctx, e₀) ->
    DTDT.machine_inter.value empty_ctx e₀ \/
    e₀ = EFail \/
    exists e₁, step (empty_ctx, e₀) (empty_ctx, e₁).
Admitted.
