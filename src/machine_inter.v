Require Import DTDT.syntax.

Definition var_dom (Γ : ctx) : list string := map fst (map_to_list (Γ.1)).

Inductive value (Γ : ctx) : i_expr -> Prop :=
  | VNat : forall n, value Γ (ENat n)
  | VBool : forall b, value Γ (EBool b)
  | VUnit : value Γ (EUnit tt)
  | VString : forall s, value Γ (EString s)
  | VConst :
    forall c τ e,
      Γ !!₂ c = Some (τ, e) ->
      value Γ (EConst c)
  | VFix :
    forall τ₁ τ₂ f x e,
      value Γ (EFix f x τ₁ τ₂ e)
  | VPair :
    forall v₁ v₂,
      value Γ v₁ ->
      value Γ v₂ ->
      value Γ (EPair v₁ v₂)
  | VVar :
    forall x τ e,
      Γ !!₁ x = Some (τ, e) ->
      value Γ (EVar x).

Inductive eval_ctx : Type :=
| ECHole
| ECAppL (E : eval_ctx) (e2 : i_expr)
| ECAppR (v1 : i_expr) (E : eval_ctx)
| ECPairL (E : eval_ctx) (e2 : i_expr)
| ECPairR (v1 : i_expr) (E : eval_ctx)
| ECFst (E : eval_ctx)
| ECSnd (E : eval_ctx)
| ECIf (E : eval_ctx) (e2 e3 : i_expr)
| ECNewRef (τ : i_ty) (E : eval_ctx)
| ECGet (E : eval_ctx)
| ECSetL (E : eval_ctx) (e2 : i_expr)
| ECSetR (v1 : i_expr) (E : eval_ctx)
| ECPlusL (E : eval_ctx) (e2 : i_expr)
| ECPlusR (v1 : i_expr) (E : eval_ctx)
| ECNot (E : eval_ctx)
| ECAndL (E : eval_ctx) (e2 : i_expr)
| ECAndR (v1 : i_expr) (E : eval_ctx)
| ECOrL (E : eval_ctx) (e2 : i_expr)
| ECOrR (v1 : i_expr) (E : eval_ctx)
| ECImpL (E : eval_ctx) (e2 : i_expr)
| ECImpR (v1 : i_expr) (E : eval_ctx)
| ECEqL (E : eval_ctx) (e2 : i_expr)
| ECEqR (v1 : i_expr) (E : eval_ctx).

Fixpoint plug (E : eval_ctx) (e : i_expr) : i_expr :=
  match E with
  | ECHole => e
  | ECAppL E' e2 => EApp (plug E' e) e2
  | ECAppR v1 E' => EApp v1 (plug E' e)
  | ECPairL E' e2 => EPair (plug E' e) e2
  | ECPairR v1 E' => EPair v1 (plug E' e)
  | ECFst E' => EFst (plug E' e)
  | ECSnd E' => ESnd (plug E' e)
  | ECIf E' e2 e3 => EIf (plug E' e) e2 e3
  | ECNewRef τ E' => ENewRef τ (plug E' e)
  | ECGet E' => EGet (plug E' e)
  | ECSetL E' e2 => ESet (plug E' e) e2
  | ECSetR v1 E' => ESet v1 (plug E' e)
  | ECPlusL E e2 => EPlus (plug E e) e2
  | ECPlusR v1 E => EPlus v1 (plug E e)
  | ECNot E => ENot (plug E e)
  | ECAndL E e2 => EAnd (plug E e) e2
  | ECAndR v1 E => EAnd v1 (plug E e)
  | ECOrL E e2 => EOr (plug E e) e2
  | ECOrR v1 E => EOr v1 (plug E e)
  | ECImpL E e2 => EImp (plug E e) e2
  | ECImpR v1 E => EImp v1 (plug E e)
  | ECEqL E e2 => EEq (plug E e) e2
  | ECEqR v1 E => EEq v1 (plug E e)
  end.

Definition base_eq (v1 v2 : i_expr) : bool :=
  match v1, v2 with
  | ENat n1, ENat n2 => Nat.eqb n1 n2
  | EBool b1, EBool b2 => Bool.eqb b1 b2
  | EString s1, EString s2 => String.eqb s1 s2
  | EUnit _, EUnit _ => true
  | _, _ => false
  end.

Fixpoint expr_subst (x : string) (s : i_expr) (e : i_expr) : i_expr :=
  match e with
  | EVar y => if String.eqb x y then s else EVar y
  | EConst c => EConst c
  | EString v => EString v
  | EBool b => EBool b
  | ENat n => ENat n
  | EUnit u => EUnit u
  | EFix f y τ1 τ2 body =>
    if String.eqb f x || String.eqb y x then EFix f y τ1 τ2 body
    else EFix f y τ1 τ2 (expr_subst x s body)
  | EApp e1 e2 => EApp (expr_subst x s e1) (expr_subst x s e2)
  | EPlus e1 e2 => EPlus (expr_subst x s e1) (expr_subst x s e2)
  | EPair e1 e2 => EPair (expr_subst x s e1) (expr_subst x s e2)
  | EFst e1 => EFst (expr_subst x s e1)
  | ESnd e1 => ESnd (expr_subst x s e1)
  | EIf e1 e2 e3 => EIf (expr_subst x s e1) (expr_subst x s e2) (expr_subst x s e3)
  | ENot e1 => ENot (expr_subst x s e1)
  | EAnd e1 e2 => EAnd (expr_subst x s e1) (expr_subst x s e2)
  | EOr e1 e2 => EOr (expr_subst x s e1) (expr_subst x s e2)
  | EImp e1 e2 => EImp (expr_subst x s e1) (expr_subst x s e2)
  | EEq e1 e2 => EEq (expr_subst x s e1) (expr_subst x s e2)
  | ENewRef τ e1 => ENewRef τ (expr_subst x s e1)
  | EGet e1 => EGet (expr_subst x s e1)
  | ESet e1 e2 => ESet (expr_subst x s e1) (expr_subst x s e2)
  | EFail => EFail
  end.

Fixpoint ty_subst (x : string) (s : i_expr) (τ : i_ty) : i_ty :=
  match τ with
  | TBase b => TBase b
  | TSet y b pred => if String.eqb x y then TSet y b pred else TSet y b (expr_subst x s pred)
  | TArr t1 t2 => TArr (ty_subst x s t1) (ty_subst x s t2)
  | TArrDep y t1 t2 =>
    if String.eqb x y then TArrDep y (ty_subst x s t1) t2
    else TArrDep y (ty_subst x s t1) (ty_subst x s t2)
  | TProd t1 t2 => TProd (ty_subst x s t1) (ty_subst x s t2)
  | TRef t => TRef (ty_subst x s t)
  end.

Inductive step : (ctx * i_expr) -> (ctx * i_expr) -> Prop :=
  | StepCtx :
    forall Γ₁ Γ₂ e e' E,
      step (Γ₁, e) (Γ₂, e') ->
      step (Γ₁, plug E e) (Γ₂, plug E e')
  | StepConst :
    forall Γ c τ e v,
      Γ !!₂ c = Some (τ, e) ->
      value Γ v ->
      step
        (Γ, EApp (EConst c) v)
        (Γ, e)
  | StepVar :
    forall Γ x τ v,
      Γ !!₁ x = Some (τ, v) ->
      step
        (Γ, EVar x)
        (Γ, v)
  | StepFix :
    forall Γ f x τ₁ τ₂ e v,
      value Γ v ->
      step
        (Γ, EApp (EFix f x τ₁ τ₂ e) v)
        (Γ, expr_subst f (EFix f x τ₁ τ₂ e) (expr_subst x v e))
  | StepFst :
    forall Γ v₁ v₂,
      value Γ v₁ ->
      value Γ v₂ ->
      step
        (Γ, EFst (EPair v₁ v₂))
        (Γ, v₁)
  | StepSnd :
    forall Γ v₁ v₂,
      value Γ v₁ ->
      value Γ v₂ ->
      step
        (Γ, ESnd (EPair v₁ v₂))
        (Γ, v₂)
  | StepIfTrue :
    forall Γ e₁ e₂,
      step
        (Γ, EIf (EBool true) e₁ e₂)
        (Γ, e₁)
  | StepIfFalse :
    forall Γ e₁ e₂,
      step
        (Γ, EIf (EBool false) e₁ e₂)
        (Γ, e₂)
  | StepNew :
    forall Γ τ v l,
      value Γ v ->
      l ∉ (var_dom Γ) ->
      step
        (Γ, ENewRef τ v)
        (Γ ,,v l ↦ (τ, v), EVar l)
  | StepGet :
    forall Γ x τ v,
      Γ !!₁ x = Some (τ, v) ->
      step
        (Γ, EGet (EVar x))
        (Γ, v)
  | StepSet :
    forall Γ x τ v e,
      value Γ v ->
      Γ !!₁ x = Some (τ, e) ->
      step
        (Γ, ESet (EVar x) v)
        (Γ ,,v x ↦ (τ, v), EUnit tt)
  | StepFail :
    forall Γ E,
      step
        (Γ, plug E EFail)
        (Γ, EFail)
  | StepNot :
    forall Γ b,
      step
        (Γ, ENot (EBool b))
        (Γ, EBool (negb b))
  | StepAnd :
    forall Γ b₁ b₂,
      step
        (Γ, EAnd (EBool b₁) (EBool b₂))
        (Γ, EBool (andb b₁ b₂))
  | StepOr :
    forall Γ b₁ b₂,
      step
        (Γ, EOr (EBool b₁) (EBool b₂))
        (Γ, EBool (orb b₁ b₂))
  | StepImp :
    forall Γ b₁ b₂,
      step
        (Γ, EImp (EBool b₁) (EBool b₂))
        (Γ, EBool (implb b₁ b₂))
  | StepEq :
    forall Γ v₁ v₂ b,
      value Γ v₁ ->
      value Γ v₂ ->
      base_eq v₁ v₂ = b ->
      step
        (Γ, EEq v₁ v₂)
        (Γ, EBool b)
  | StepPlus :
    forall Γ n₁ n₂,
      step
        (Γ, EPlus (ENat n₁) (ENat n₂))
        (Γ, ENat (n₁ + n₂)).

Inductive eval : (ctx * i_expr) -> (ctx * i_expr) -> Prop :=
| steps_refl :
    forall σ,
    eval σ σ
| steps_step :
    forall σ1 σ2 σ3,
      step σ1 σ2 ->
      eval σ2 σ3 ->
      eval σ1 σ3.

Ltac solve_var :=
  eapply StepVar;
  unfold ctx_add_var, var_ctx_lookup;
  simpl;
  apply lookup_insert; simpl.

Lemma eval_app_test : forall Γ, eval (Γ, (EApp (EFix "f" "x" (TProd (TBase BNat) (TBase BBool)) (TBase BBool) (ESnd (EVar "x"))) (EPair (ENat 42) (EBool false)))) (Γ, (EBool false)).
Proof.
  intros.
  eapply steps_step.
  apply StepFix.
  apply VPair.
  apply VNat.
  apply VBool.
  simpl.
  eapply steps_step.
  apply StepSnd.
  apply VNat.
  apply VBool.
  apply steps_refl.
Qed.

Lemma eval_eq_test : forall Γ, eval ((ctx_add_var Γ "x" (TBase BNat) (ENat 2)), (EEq (ENat 2) (EVar "x"))) ((ctx_add_var Γ "x" (TBase BNat) (ENat 2)), (EBool true)).
Proof.
  intros.
  econstructor.
  eapply StepCtx with (E := ECEqR (ENat 2) ECHole). solve_var.
  simpl. econstructor.
  apply StepEq.
  econstructor.
  econstructor.
  simpl. reflexivity.
  apply steps_refl.
Qed.

Lemma eval_bool_test : forall Γ, eval (Γ, (EEq (EImp (ENot (EBool false)) (EEq (EPair (ENat 2) (EBool true)) (EString "hehe"))) (EAnd (EOr (EBool true) (EBool false)) (EIf (EEq (EUnit ()) (EUnit ())) (EBool false) (EBool true))))) (Γ, (EBool true)).
Proof.
  intros.
  econstructor.
  eapply StepCtx with (E := ECEqL ECHole (EAnd (EOr (EBool true) (EBool false)) (EIf (EEq (EUnit ()) (EUnit ())) (EBool false) (EBool true)))).
  eapply StepCtx with (E := ECImpL ECHole (EEq (EPair (ENat 2) (EBool true)) (EString "hehe"))).
  apply StepNot.
  simpl. econstructor.
  eapply StepCtx with (E := ECEqL ECHole (EAnd (EOr (EBool true) (EBool false)) (EIf (EEq (EUnit ()) (EUnit ())) (EBool false) (EBool true)))).
  eapply StepCtx with (E := ECImpR (EBool true) ECHole).
  apply StepEq.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  simpl. reflexivity.
  econstructor.
  simpl. eapply StepCtx with (E := ECEqL ECHole (EAnd (EOr (EBool true) (EBool false)) (EIf (EEq (EUnit ()) (EUnit ())) (EBool false) (EBool true)))).
  apply StepImp.
  econstructor.
  simpl. eapply StepCtx with (E := ECEqR (EBool false) ECHole).
  eapply StepCtx with (E := ECAndL ECHole (EIf (EEq (EUnit ()) (EUnit ())) (EBool false) (EBool true))). apply StepOr.
  econstructor. simpl.
  eapply StepCtx with (E := ECEqR (EBool false) ECHole).
  eapply StepCtx with (E := ECAndR (EBool true) ECHole).
  eapply StepCtx with (E := ECIf ECHole (EBool false) (EBool true)).
  apply StepEq. econstructor. econstructor. simpl. reflexivity. simpl.
  econstructor.
  eapply StepCtx with (E := ECEqR (EBool false) ECHole).
  eapply StepCtx with (E := ECAndR (EBool true) ECHole).
  apply StepIfTrue. simpl.
  econstructor.
  eapply StepCtx with (E := ECEqR (EBool false) ECHole).
  apply StepAnd. simpl.
  econstructor.
  apply StepEq. econstructor. econstructor. simpl. reflexivity.
  apply steps_refl.
Qed.