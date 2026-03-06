Require Import DTDT.syntax.
From stdpp Require Export base.
From stdpp Require Export strings.

(* --- Evaluation ---------------------------------------------------------------------- *)

Inductive value : i_expr -> Prop :=
| ValString : forall s, value (EString s)
| ValBool   : forall b, value (EBool b)
| ValNat    : forall n, value (ENat n)
| ValUnit   : value (EUnit tt)
| ValPair   : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
| ValFix    : forall f x τ1 τ2 e, value (EFix f x τ1 τ2 e).

Inductive eval
  (Γ : ctx) :
  i_expr -> i_expr -> Prop :=
  | eval_bool :
    forall b,
      eval Γ (EBool b) (EBool b)
  | eval_nat :
    forall n,
      eval Γ (ENat n) (ENat n)
  | eval_string :
    forall s,
      eval Γ (EString s) (EString s)
  | eval_unit :
    forall u,
      eval Γ (EUnit u) (EUnit u)
  | eval_var :
    forall v τ e,
      Γ !!₁ v = Some (τ, e) -> 
      eval Γ (EVar v) e
  | eval_const :
    forall c τ e,
      Γ !!₂ c = Some (τ, e) -> 
      eval Γ (EConst c) e
  | eval_fix :
    forall f x τ₁ τ₂ e,
      eval Γ (EFix f x τ₁ τ₂ e) (EFix f x τ₁ τ₂ e)
  | eval_app :
    forall e₁ e₂ f x τ₁ τ₂ body v₁ v₂,
      eval Γ e₁ (EFix f x τ₁ τ₂ body) ->
      eval Γ e₂ v₂ ->
      value v₂ ->
      eval (ctx_add_var (ctx_add_const Γ f (TArr τ₁ τ₂) (EFix f x τ₁ τ₂ body)) x τ₁ v₂) body v₁ ->
      eval Γ (EApp e₁ e₂) v₁
  | eval_plus :
    forall e₁ e₂ n₁ n₂,
      eval Γ e₁ (ENat n₁) ->
      eval Γ e₂ (ENat n₂) ->
      eval Γ (EPlus e₁ e₂) (ENat (n₁ + n₂))
  | eval_pair :
    forall e₁ e₂,
      eval Γ (EPair e₁ e₂) (EPair e₁ e₂)
  | eval_fst :
    forall e₁ e₂ v,
      eval Γ v (EPair e₁ e₂) ->
      eval Γ (EFst v) e₁
  | eval_snd :
    forall e₁ e₂ v,
      eval Γ v (EPair e₁ e₂) ->
      eval Γ (ESnd v) e₂
  | eval_if_true :
    forall e₁ e₂ e₃,
      eval Γ e₁ (EBool true) ->
      eval Γ (EIf e₁ e₂ e₃) e₂
  | eval_if_false :
    forall e₁ e₂ e₃,
      eval Γ e₁ (EBool false) ->
      eval Γ (EIf e₁ e₂ e₃) e₃
  | eval_not :
    forall e b,
      eval Γ e (EBool b) ->
      eval Γ (ENot e) (EBool (negb b))
  | eval_and :
    forall e₁ e₂ b₁ b₂,
      eval Γ e₁ (EBool b₁) ->
      eval Γ e₂ (EBool b₂) ->
      eval Γ (EAnd e₁ e₂) (EBool (b₁ && b₂))
  | eval_or :
    forall e₁ e₂ b₁ b₂,
      eval Γ e₁ (EBool b₁) ->
      eval Γ e₂ (EBool b₂) ->
      eval Γ (EOr e₁ e₂) (EBool (b₁ || b₂))
  | eval_imp :
      forall e₁ e₂ b₁ b₂,
        eval Γ e₁ (EBool b₁) ->
        eval Γ e₂ (EBool b₂) ->
        eval Γ (EImp e₁ e₂) (EBool (negb b₁ || b₂))
  | eval_eq_true :
    forall e₁ e₂ v₁ v₂,
      eval Γ e₁ v₁ ->
      eval Γ e₂ v₂ ->
      v₁ = v₂ -> 
      eval Γ (EEq e₁ e₂) (EBool true)
  | eval_eq_false :
    forall e₁ e₂ v₁ v₂,
      eval Γ e₁ v₁ ->
      eval Γ e₂ v₂ ->
      v₁ <> v₂ -> 
      eval Γ (EEq e₁ e₂) (EBool false)
  .

Lemma eval_app_test : forall Γ, eval Γ (EApp (EFix "f" "x" (TProd (TBase BNat) (TBase BBool)) (TBase BBool) (ESnd (EVar "x"))) (EPair (ENat 42) (EBool false))) (EBool false).
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

Lemma eval_eq_test : forall Γ, eval (ctx_add_var Γ "x" (TBase BNat) (ENat 2)) (EEq (ENat 2) (EVar "x")) (EBool true).
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

Lemma eval_bool_test : forall Γ, eval Γ (EEq (EImp (ENot (EBool false)) (EEq (EPair (ENat 2) (EBool true)) (EString "hehe"))) (EAnd (EOr (EBool true) (EBool false)) (EIf (EEq (EUnit ()) (EUnit ())) (EBool false) (EBool true)))) (EBool true).
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
