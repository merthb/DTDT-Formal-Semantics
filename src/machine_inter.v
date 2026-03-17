Require Import DTDT.syntax.

Definition var_dom (Γ : ctx) : list string := map fst (map_to_list (Γ ▷vars)).
Definition store_dom (Γ : ctx) : list string := map fst (map_to_list (Γ ▷store)).

(* Value judgment for the internal machine.
   Values are parameterized by the current context because constants, variables,
   and locations are recognized through context and store lookup. *)
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
      value Γ (EVar x)
  | VLoc :
    forall l τ v,
      Γ !!₃ l = Some (τ, v) ->
      value Γ (EVar l).

(* Evaluation contexts determine the reduction position for the small-step machine.
   They encode the left-to-right call-by-value order used by the operational semantics. *)
Inductive eval_ctx : Type :=
| ECHole
| ECAppL (E : eval_ctx) (e₂ : i_expr)
| ECAppR (v₁ : i_expr) (E : eval_ctx)
| ECPairL (E : eval_ctx) (e₂ : i_expr)
| ECPairR (v₁ : i_expr) (E : eval_ctx)
| ECFst (E : eval_ctx)
| ECSnd (E : eval_ctx)
| ECIf (E : eval_ctx) (e₂ e₃ : i_expr)
| ECNewRef (τ : i_ty) (E : eval_ctx)
| ECGet (E : eval_ctx)
| ECSetL (E : eval_ctx) (e₂ : i_expr)
| ECSetR (v₁ : i_expr) (E : eval_ctx)
| ECPlusL (E : eval_ctx) (e₂ : i_expr)
| ECPlusR (v₁ : i_expr) (E : eval_ctx)
| ECNot (E : eval_ctx)
| ECAndL (E : eval_ctx) (e₂ : i_expr)
| ECAndR (v₁ : i_expr) (E : eval_ctx)
| ECOrL (E : eval_ctx) (e₂ : i_expr)
| ECOrR (v₁ : i_expr) (E : eval_ctx)
| ECImpL (E : eval_ctx) (e₂ : i_expr)
| ECImpR (v₁ : i_expr) (E : eval_ctx)
| ECEqL (E : eval_ctx) (e₂ : i_expr)
| ECEqR (v₁ : i_expr) (E : eval_ctx).

Fixpoint plug (E : eval_ctx) (e : i_expr) : i_expr :=
  match E with
  | ECHole => e
  | ECAppL E' e₂ => EApp (plug E' e) e₂
  | ECAppR v₁ E' => EApp v₁ (plug E' e)
  | ECPairL E' e₂ => EPair (plug E' e) e₂
  | ECPairR v₁ E' => EPair v₁ (plug E' e)
  | ECFst E' => EFst (plug E' e)
  | ECSnd E' => ESnd (plug E' e)
  | ECIf E' e₂ e₃ => EIf (plug E' e) e₂ e₃
  | ECNewRef τ E' => ENewRef τ (plug E' e)
  | ECGet E' => EGet (plug E' e)
  | ECSetL E' e₂ => ESet (plug E' e) e₂
  | ECSetR v₁ E' => ESet v₁ (plug E' e)
  | ECPlusL E' e₂ => EPlus (plug E' e) e₂
  | ECPlusR v₁ E' => EPlus v₁ (plug E' e)
  | ECNot E' => ENot (plug E' e)
  | ECAndL E' e₂ => EAnd (plug E' e) e₂
  | ECAndR v₁ E' => EAnd v₁ (plug E' e)
  | ECOrL E' e₂ => EOr (plug E' e) e₂
  | ECOrR v₁ E' => EOr v₁ (plug E' e)
  | ECImpL E' e₂ => EImp (plug E' e) e₂
  | ECImpR v₁ E' => EImp v₁ (plug E' e)
  | ECEqL E' e₂ => EEq (plug E' e) e₂
  | ECEqR v₁ E' => EEq v₁ (plug E' e)
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
  | EFix f y τ₁ τ₂ body =>
    if String.eqb f x || String.eqb y x then EFix f y τ₁ τ₂ body
    else EFix f y τ₁ τ₂ (expr_subst x s body)
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

(* One-step machine reduction on configurations.
   A reduction may update both the expression and the runtime context, in particular
   through allocation and mutation of the store component. *)
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
      ~ In l (var_dom Γ) ->
      ~ In l (store_dom Γ) ->
      step
        (Γ, ENewRef τ v)
        (Γ ,,s l ↦ (τ, v), EVar l)
  | StepGet :
    forall Γ x τ v,
      Γ !!₃ x = Some (τ, v) ->
      step
        (Γ, EGet (EVar x))
        (Γ, v)
  | StepSet :
    forall Γ x τ v e,
      value Γ v ->
      Γ !!₃ x = Some (τ, e) ->
      step
        (Γ, ESet (EVar x) v)
        (Γ ,,s x ↦ (τ, v), EUnit tt)
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

(* Reflexive-transitive closure of the small-step reduction relation.
   This judgment is used as the ambient execution notion for semantic entailment. *)
Inductive eval : (ctx * i_expr) -> (ctx * i_expr) -> Prop :=
| steps_refl :
    forall σ,
    eval σ σ
| steps_step :
    forall σ₁ σ₂ σ₃,
      step σ₁ σ₂ ->
      eval σ₂ σ₃ ->
      eval σ₁ σ₃.

Notation "σ₁ ↠* σ₂" := (eval σ₁ σ₂)
  (at level 70).
