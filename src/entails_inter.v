Require Import DTDT.syntax.
Require Import DTDT.machine_inter.

(* Semantic entailment for internal predicates.
   Paper form: Γ ⊨ e.
   The judgment holds exactly when the internal predicate e evaluates to true in
   the current runtime context Γ. The subsequent axioms record the Appendix B.1
   structural principles assumed by the development. *)
Definition entails (Γ : ctx) (e : i_expr) : Prop :=
  (Γ, e) ↠* (Γ, EBool true).

Notation "Γ ⊨ e" := (entails Γ e) (at level 80).

(* Substitute a term through one context entry. *)
Definition binding_subst (x : string) (s : i_expr) (entry : i_ty * i_expr) : i_ty * i_expr :=
  (ty_subst x s (fst entry), expr_subst x s (snd entry)).

(* Substitute a term throughout an internal context. *)
Definition ctx_subst (x : string) (s : i_expr) (g : ctx) : ctx :=
  ((fmap (binding_subst x s) (fst (fst g)), fmap (binding_subst x s) (snd (fst g))),
   fmap (binding_subst x s) (snd g)).

(* B.1.1 Hypothesis *)
Axiom entails_hypothesis :
  forall Γ₁ Γ₂ x y τb pred witness,
    (ctx_add_var (add_ctx Γ₂ Γ₁) x (TSet y τb pred) witness) ⊨
      (expr_subst y (EVar x) pred).

(* B.1.2 Weakening *)
Axiom entails_weakening :
  forall Γ₁ Γ₂ Γ₃ e,
    (add_ctx Γ₂ Γ₁) ⊨ e ->
    (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) ⊨ e.

(* B.1.3 Substitution of a base-typed variable.
   The paper assumes the substituted term is a value or a variable; the
   current machine semantics already classifies looked-up variables as values. *)
Axiom entails_subst_base :
  forall Γ₁ Γ₂ x τb witness e e₀,
    (ctx_add_var (add_ctx Γ₂ Γ₁) x (TBase τb) witness) ⊨ e ->
    value Γ₁ e₀ ->
    (add_ctx (ctx_subst x e₀ Γ₂) Γ₁) ⊨ (expr_subst x e₀ e).

(* B.1.4 Substitution of a set-typed variable. *)
Axiom entails_subst_set :
  forall Γ₁ Γ₂ x τb pred witness e e₀,
    (ctx_add_var (add_ctx Γ₂ Γ₁) x (TSet x τb pred) witness) ⊨ e ->
    value Γ₁ e₀ ->
    Γ₁ ⊨ (expr_subst x e₀ pred) ->
    (add_ctx (ctx_subst x e₀ Γ₂) Γ₁) ⊨ (expr_subst x e₀ e).

(* B.1.5 Equality. *)
Axiom entails_equality :
  forall G x u y v tb pred wx wu wy wv,
    entails
      (ctx_add_var
        (ctx_add_var
          (ctx_add_var
            (ctx_add_var G x (TBase tb) wx)
            u (TSet u BBool pred) wu)
          y (TBase tb) wy)
        v (TSet v BBool (EEq (EVar x) (EVar y))) wv)
      (expr_subst x (EVar y) pred).

(* B.1.6 If a binding is unused in both G2 and e, it can be dropped.
   We phrase the side condition via substitution being syntactically inert, which
   matches the current implementation more directly than an explicit FV judgment. *)
Axiom entails_drop_unused :
  forall G1 G2 x t witness e,
    entails (ctx_add_var (add_ctx G2 G1) x t witness) e ->
    ctx_subst x witness G2 = G2 ->
    expr_subst x witness e = e ->
    entails (add_ctx G2 G1) e.

(* Store updates preserve refinement entailments whose predicate context only
   adds the distinguished refinement variable.  This is an entailment-layer
   structural principle: store mutation changes the runtime store entry, not the
   logical variable binding used to check the refinement predicate. *)
Axiom entails_store_update_refinement :
  forall Γ x τ oldv newv var τb witness pred,
    Γ !!₃ x = Some (τ, oldv) ->
    entails (ctx_add_var Γ var (TBase τb) witness) pred ->
    entails (ctx_add_var (Γ ,,s x ↦ (τ, newv)) var (TBase τb) witness) pred.

(* B.1.7 Compatibility with primitive constant interpretation under evaluation
   contexts. In the current implementation, the paper's I(c, v) is represented by
   the corresponding constant-application machine step. *)
Axiom entails_const_step :
  forall G c t e v E,
    const_ctx_lookup G c = Some (t, e) ->
    value G v ->
    (entails G (plug E (EApp (EConst c) v)) <-> entails G (plug E e)).

(* B.1.8 Classical propositional logic. *)
Lemma entails_true :
  forall G,
    entails G (EBool true).
Proof.
  intros G.
  unfold entails.
  apply steps_refl.
Qed.

Lemma entails_not_false :
  forall G,
    entails G (ENot (EBool false)).
Proof.
  intros G.
  unfold entails.
  eapply steps_step.
  - apply StepNot.
  - apply steps_refl.
Qed.

Axiom entails_imp_refl :
  forall G e,
    entails G (EImp e e).

Axiom entails_modus_ponens :
  forall G p q,
    entails G (EImp p q) ->
    entails G p ->
    entails G q.

(* Convenience restatement of entailment weakening. *)
Lemma entails_weaken_right :
  forall Γ₁ Γ₂ Γ₃ e,
    (add_ctx Γ₂ Γ₁) ⊨ e ->
    (add_ctx (add_ctx Γ₃ Γ₂) Γ₁) ⊨ e.
Proof.
  exact entails_weakening.
Qed.
