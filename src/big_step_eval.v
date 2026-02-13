Require Import DTDT.syntax.
Import ListNotations.
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
  (Γ : var_context)
  (Γv : varval_context)
  (Φ : const_context)
  (ι : fun_imp_list) :
  i_expr -> i_expr -> Prop :=
  | eval_bool :
    forall b,
      eval Γ Γv Φ ι (EBool b) (EBool b)
  | eval_nat :
    forall n,
      eval Γ Γv Φ ι (ENat n) (ENat n)
  | eval_string :
    forall s,
      eval Γ Γv Φ ι (EString s) (EString s)
  | eval_unit :
    forall u,
      eval Γ Γv Φ ι (EUnit u) (EUnit u)
  | eval_var :
    forall v τ e,
      Γ[ v ] Γ = Some τ ->
      Γv[ v ] Γv = Some e -> 
      eval Γ Γv Φ ι (EVar v) e
  | eval_const :
    forall c τ e,
      Φ[ c ] Φ = Some τ ->
      ι[ c ] ι = Some e -> 
      eval Γ Γv Φ ι (EConst c) e
  | eval_fix :
    forall f x τ₁ τ₂ e,
      eval Γ Γv Φ ι (EFix f x τ₁ τ₂ e) (EFix f x τ₁ τ₂ e)
  | eval_app :
    forall e₁ e₂ f x τ₁ τ₂ body v₁ v₂,
      eval Γ Γv Φ ι e₁ (EFix f x τ₁ τ₂ body) ->
      eval Γ Γv Φ ι e₂ v₂ ->
      value v₂ ->
      eval ((x , τ₁) :: Γ) ((x , v₂) :: Γv) ((f , TArr τ₁ τ₂) :: Φ) ((f , EFix f x τ₁ τ₂ body) :: ι)
        body v₁ ->
      eval Γ Γv Φ ι (EApp e₁ e₂) v₁
  | eval_plus :
    forall e₁ e₂ n₁ n₂,
      eval Γ Γv Φ ι e₁ (ENat n₁) ->
      eval Γ Γv Φ ι e₂ (ENat n₂) ->
      eval Γ Γv Φ ι (EPlus e₁ e₂) (ENat (n₁ + n₂))
  | eval_pair :
    forall e₁ e₂,
      eval Γ Γv Φ ι (EPair e₁ e₂) (EPair e₁ e₂)
  | eval_fst :
    forall e₁ e₂ v,
      eval Γ Γv Φ ι v (EPair e₁ e₂) ->
      eval Γ Γv Φ ι (EFst v) e₁
  | eval_snd :
    forall e₁ e₂ v,
      eval Γ Γv Φ ι v (EPair e₁ e₂) ->
      eval Γ Γv Φ ι (ESnd v) e₂
  | eval_if_true :
    forall e₁ e₂ e₃,
      eval Γ Γv Φ ι e₁ (EBool true) ->
      eval Γ Γv Φ ι (EIf e₁ e₂ e₃) e₂
  | eval_if_false :
    forall e₁ e₂ e₃,
      eval Γ Γv Φ ι e₁ (EBool false) ->
      eval Γ Γv Φ ι (EIf e₁ e₂ e₃) e₃
  | eval_not :
    forall e b,
      eval Γ Γv Φ ι e (EBool b) ->
      eval Γ Γv Φ ι (ENot e) (EBool (negb b))
  | eval_and :
    forall e₁ e₂ b₁ b₂,
      eval Γ Γv Φ ι e₁ (EBool b₁) ->
      eval Γ Γv Φ ι e₂ (EBool b₂) ->
      eval Γ Γv Φ ι (EAnd e₁ e₂) (EBool (b₁ && b₂))
  | eval_or :
    forall e₁ e₂ b₁ b₂,
      eval Γ Γv Φ ι e₁ (EBool b₁) ->
      eval Γ Γv Φ ι e₂ (EBool b₂) ->
      eval Γ Γv Φ ι (EOr e₁ e₂) (EBool (b₁ || b₂))
  | eval_imp :
      forall e₁ e₂ b₁ b₂,
        eval Γ Γv Φ ι e₁ (EBool b₁) ->
        eval Γ Γv Φ ι e₂ (EBool b₂) ->
        eval Γ Γv Φ ι (EImp e₁ e₂) (EBool (negb b₁ || b₂))
  | eval_eq_true :
    forall e₁ e₂ v₁ v₂,
      eval Γ Γv Φ ι e₁ v₁ ->
      eval Γ Γv Φ ι e₂ v₂ ->
      v₁ = v₂ -> 
      eval Γ Γv Φ ι (EEq e₁ e₂) (EBool true)
  | eval_eq_false :
    forall e₁ e₂ v₁ v₂,
      eval Γ Γv Φ ι e₁ v₁ ->
      eval Γ Γv Φ ι e₂ v₂ ->
      v₁ <> v₂ -> 
      eval Γ Γv Φ ι (EEq e₁ e₂) (EBool false)
  .

Lemma eval_app_test : forall Γ Γv Φ ι, eval Γ Γv Φ ι (EApp (EFix "f" "x" (TProd (TBase BNat) (TBase BBool)) (TBase BBool) (ESnd (EVar "x"))) (EPair (ENat 42) (EBool false))) (EBool false).
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
simpl. reflexivity.
simpl. reflexivity.
Qed.

Lemma eval_eq_test : forall Γ Γv Φ ι, eval (("x" , TBase BNat) :: Γ) (("x" , ENat 2) :: Γv) Φ ι (EEq (ENat 2) (EVar "x")) (EBool true).
Proof.
intros.
eapply eval_eq_true.
apply eval_nat.
eapply eval_var.
simpl. reflexivity.
simpl. reflexivity.
reflexivity.
Qed.

Lemma eval_bool_test : forall Γ Γv Φ ι, eval Γ Γv Φ ι (EEq (EImp (ENot (EBool false)) (EEq (EPair (ENat 2) (EBool true)) (EString "hehe"))) (EAnd (EOr (EBool true) (EBool false)) (EIf (EEq (EUnit ()) (EUnit ())) (EBool false) (EBool true)))) (EBool true).
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
simpl.
reflexivity.
Qed.
