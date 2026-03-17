(* Archived big-step semantics.
   This file is intentionally kept in the repository for reference,
   but it has been removed from the active build/dependency chain.

Require Import DTDT.syntax.
From stdpp Require Export base.
From stdpp Require Export strings.

(* --- Evaluation ---------------------------------------------------------------------- *)

Inductive value : i_expr -> Prop :=
| ValString : forall s, value (EString s)
| ValBool   : forall b, value (EBool b)
| ValNat    : forall n, value (ENat n)
| ValUnit   : value (EUnit tt)
| ValVar    : forall x, value (EVar x)
| ValConst  : forall c, value (EConst c)
| ValPair   : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
| ValFix    : forall f x τ1 τ2 e, value (EFix f x τ1 τ2 e).

Inductive eval_bigstep
  (Γ : ctx) :
  i_expr -> i_expr -> Prop :=
  | eval_bool :
    forall b,
      eval_bigstep Γ (EBool b) (EBool b)
  | eval_nat :
    forall n,
      eval_bigstep Γ (ENat n) (ENat n)
  | eval_string :
    forall s,
      eval_bigstep Γ (EString s) (EString s)
  | eval_unit :
    forall u,
      eval_bigstep Γ (EUnit u) (EUnit u)
  | eval_var :
    forall v τ e,
      Γ !!₁ v = Some (τ, e) -> 
      eval_bigstep Γ (EVar v) e
  | eval_const :
    forall c τ e,
      Γ !!₂ c = Some (τ, e) -> 
      eval_bigstep Γ (EConst c) e
  | eval_fix :
    forall f x τ₁ τ₂ e,
      eval_bigstep Γ (EFix f x τ₁ τ₂ e) (EFix f x τ₁ τ₂ e)
  | eval_app :
    forall e₁ e₂ f x τ₁ τ₂ body v₁ v₂,
      eval_bigstep Γ e₁ (EFix f x τ₁ τ₂ body) ->
      eval_bigstep Γ e₂ v₂ ->
      value v₂ ->
      eval_bigstep (((Γ ,,c f ↦ (TArr τ₁ τ₂, EFix f x τ₁ τ₂ body)) ,,v x ↦ (τ₁, v₂))) body v₁ ->
      eval_bigstep Γ (EApp e₁ e₂) v₁
  | eval_plus :
    forall e₁ e₂ n₁ n₂,
      eval_bigstep Γ e₁ (ENat n₁) ->
      eval_bigstep Γ e₂ (ENat n₂) ->
      eval_bigstep Γ (EPlus e₁ e₂) (ENat (n₁ + n₂))
  | eval_pair :
    forall e₁ e₂,
      eval_bigstep Γ (EPair e₁ e₂) (EPair e₁ e₂)
  | eval_fst :
    forall e₁ e₂ v,
      eval_bigstep Γ v (EPair e₁ e₂) ->
      eval_bigstep Γ (EFst v) e₁
  | eval_snd :
    forall e₁ e₂ v,
      eval_bigstep Γ v (EPair e₁ e₂) ->
      eval_bigstep Γ (ESnd v) e₂
  | eval_if_true :
    forall e₁ e₂ e₃,
      eval_bigstep Γ e₁ (EBool true) ->
      eval_bigstep Γ (EIf e₁ e₂ e₃) e₂
  | eval_if_false :
    forall e₁ e₂ e₃,
      eval_bigstep Γ e₁ (EBool false) ->
      eval_bigstep Γ (EIf e₁ e₂ e₃) e₃
  | eval_not :
    forall e b,
      eval_bigstep Γ e (EBool b) ->
      eval_bigstep Γ (ENot e) (EBool (negb b))
  | eval_and :
    forall e₁ e₂ b₁ b₂,
      eval_bigstep Γ e₁ (EBool b₁) ->
      eval_bigstep Γ e₂ (EBool b₂) ->
      eval_bigstep Γ (EAnd e₁ e₂) (EBool (b₁ && b₂))
  | eval_or :
    forall e₁ e₂ b₁ b₂,
      eval_bigstep Γ e₁ (EBool b₁) ->
      eval_bigstep Γ e₂ (EBool b₂) ->
      eval_bigstep Γ (EOr e₁ e₂) (EBool (b₁ || b₂))
  | eval_imp :
      forall e₁ e₂ b₁ b₂,
        eval_bigstep Γ e₁ (EBool b₁) ->
        eval_bigstep Γ e₂ (EBool b₂) ->
        eval_bigstep Γ (EImp e₁ e₂) (EBool (negb b₁ || b₂))
  | eval_eq_true :
    forall e₁ e₂ v₁ v₂,
      eval_bigstep Γ e₁ v₁ ->
      eval_bigstep Γ e₂ v₂ ->
      v₁ = v₂ -> 
      eval_bigstep Γ (EEq e₁ e₂) (EBool true)
  | eval_eq_false :
    forall e₁ e₂ v₁ v₂,
      eval_bigstep Γ e₁ v₁ ->
      eval_bigstep Γ e₂ v₂ ->
      v₁ <> v₂ -> 
      eval_bigstep Γ (EEq e₁ e₂) (EBool false)
  .

Lemma eval_app_test : forall Γ, eval_bigstep Γ (EApp (EFix "f" "x" (TProd (TBase BNat) (TBase BBool)) (TBase BBool) (ESnd (EVar "x"))) (EPair (ENat 42) (EBool false))) (EBool false).
Proof.
intros.
eapply eval_app.
apply eval_fix.
apply eval_pair.
apply ValPair.
apply ValNat.
apply ValBool.
eapply eval_snd.
eapply eval_var.
unfold var_ctx_lookup.
(* rewrite StringFacts.add_eq_o.
reflexivity.
reflexivity. *)
Admitted.

Lemma eval_eq_test : forall Γ, eval_bigstep (Γ ,,v "x" ↦ (TBase BNat, ENat 2)) (EEq (ENat 2) (EVar "x")) (EBool true).
Proof.
intros.
eapply eval_eq_true.
apply eval_nat.
eapply eval_var.
unfold var_ctx_lookup.
(* rewrite StringFacts.add_eq_o.
reflexivity.
reflexivity.
reflexivity. *)
Admitted.

Lemma eval_bool_test : forall Γ, eval_bigstep Γ (EEq (EImp (ENot (EBool false)) (EEq (EPair (ENat 2) (EBool true)) (EString "hehe"))) (EAnd (EOr (EBool true) (EBool false)) (EIf (EEq (EUnit ()) (EUnit ())) (EBool false) (EBool true)))) (EBool true).
Proof.
intros.
eapply eval_eq_true.
apply eval_imp.
apply eval_not.
apply eval_bool.
eapply eval_eq_false.
apply eval_pair.
apply eval_string.
discriminate.
apply eval_and.
apply eval_or.
apply eval_bool.
apply eval_bool.
apply eval_if_true.
eapply eval_eq_true.
apply eval_unit.
apply eval_unit.
reflexivity.
simpl. reflexivity.
Qed.

*)
