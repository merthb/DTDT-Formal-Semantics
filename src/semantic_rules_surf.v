Require Import DTDT.syntax.
Require Import DTDT.big_step_eval_inter.
Require Import DTDT.semantic_rules_inter.

(* --- Pure term validation - surface language -------------------------------------------- *)

Fixpoint is_simple_type_surf (type : ty) : bool :=
  match type with
  | TyBase _ => true
  | TyArr t1 t2 => is_simple_type_surf t1 && is_simple_type_surf t2
  | TyProd t1 t2 => is_simple_type_surf t1 && is_simple_type_surf t2
  | _ => false
  end.

Definition essential_type_is_base_type_surf (type : ty) : bool :=
  match type with
  | TyBase _ => true
  | TySet _ _ _ => true
  | _ => false
  end.
Notation "βs[ t ]" := (essential_type_is_base_type_surf t) (at level 10).

Inductive has_type_pure_surf
  ( Γ : ctx_surf)
  : expr -> ty -> Prop :=
  | PVarS :
    forall x τb v,
      Γ !!₁ₛ x = Some (τb, v) ->
      βs[ τb ] ->
      has_type_pure_surf Γ (ExVar x) τb
  | PNatS :
    forall n,
      has_type_pure_surf Γ (ExNat n) (TyBase BNat)
  | PBoolS :
    forall b,
      has_type_pure_surf Γ (ExBool b) (TyBase BBool)
  | PStringS :
    forall s,
      has_type_pure_surf Γ (ExString s) (TyBase BString)
  | PUnitS :
    forall u,
      has_type_pure_surf Γ (ExUnit u) (TyBase BUnit)
  | PConstS :
    forall c τ v,
      Γ !!₂ₛ c = Some (τ, v) ->
      is_simple_type_surf τ ->
      has_type_pure_surf Γ (ExConst c) τ
  | PAppS :
    forall e₁ e₂ τ₁ τ₂,
      βs[ τ₁ ] ->
      has_type_pure_surf Γ e₁ (TyArr τ₁ τ₂) ->
      has_type_pure_surf Γ e₂ τ₁ ->
      has_type_pure_surf Γ (ExApp e₁ e₂) τ₂
  | PNotS :
    forall b,
      has_type_pure_surf Γ b (TyBase BBool) ->
      has_type_pure_surf Γ (ExNot b) (TyBase BBool)
  | PImpS :
    forall b₁ b₂,
      has_type_pure_surf Γ b₁ (TyBase BBool) ->
      has_type_pure_surf Γ b₂ (TyBase BBool) ->
      has_type_pure_surf Γ (ExImp b₁ b₂) (TyBase BBool)
  | PAndS :
    forall b₁ b₂,
      has_type_pure_surf Γ b₁ (TyBase BBool) ->
      has_type_pure_surf Γ b₂ (TyBase BBool) ->
      has_type_pure_surf Γ (ExAnd b₁ b₂) (TyBase BBool)
  | POrS :
    forall b₁ b₂,
      has_type_pure_surf Γ b₁ (TyBase BBool) ->
      has_type_pure_surf Γ b₂ (TyBase BBool) ->
      has_type_pure_surf Γ (ExOr b₁ b₂) (TyBase BBool)
  | PPlusS :
    forall n₁ n₂,
      has_type_pure_surf Γ n₁ (TyBase BNat) ->
      has_type_pure_surf Γ n₂ (TyBase BNat) ->
      has_type_pure_surf Γ (ExPlus n₁ n₂) (TyBase BNat).

(* --- Type wellformedness for surface language -----------------------------*)

Inductive ty_valid_surf
  (Γ : ctx_surf)
  : ty -> Prop :=
  | VBaseS :
    forall (τb : BaseT),
      ty_valid_surf Γ (TyBase τb)
  | VSetS :
    forall var (τb : BaseT) e v,
      has_type_pure_surf (ctx_add_var_surf Γ var (TyBase τb) v) e (TyBase BBool) ->
      ty_valid_surf Γ (TySet var τb e)
  | VFunS :
    forall τ₁ τ₂,
      ty_valid_surf Γ τ₁ ->
      ty_valid_surf Γ τ₂ ->
      ty_valid_surf Γ (TyArr τ₁ τ₂)
  | VFunDepS :
    forall var τ₁ τ₂ v,
      ty_valid_surf Γ τ₁ ->
      ty_valid_surf (ctx_add_var_surf Γ var τ₁ v) τ₂ ->
      ty_valid_surf Γ (TyArrDep var τ₁ τ₂)
  | VPairS :
    forall τ₁ τ₂,
      ty_valid_surf Γ τ₁ ->
      ty_valid_surf Γ τ₂ ->
      ty_valid_surf Γ (TyProd τ₁ τ₂)
  | VRefS :
    forall τ₁,
      ty_valid_surf Γ τ₁ ->
      ty_valid_surf Γ (TyRef τ₁)
  | VDeRefS :
    forall τ₁,
      ty_valid_surf Γ τ₁ ->
      ty_valid_surf Γ (TyDeRef τ₁).

(* --- Substitution for surface language ----------------------------------- *)

Fixpoint expr_subst_surf (x : string) (s : expr) (e : expr) : expr :=
  match e with
  | ExVar y =>
      if String.eqb x y then s else ExVar y
  | ExConst c => ExConst c
  | ExString v => ExString v
  | ExBool b => ExBool b
  | ExNat n => ExNat n
  | ExUnit u => ExUnit u
  | ExFix f y τ1 τ2 body =>
      if String.eqb f x || String.eqb y x then ExFix f y τ1 τ2 body
      else ExFix f y τ1 τ2 (expr_subst_surf x s body)
  | ExApp e1 e2 => ExApp (expr_subst_surf x s e1) (expr_subst_surf x s e2)
  | ExPlus e1 e2 => ExPlus (expr_subst_surf x s e1) (expr_subst_surf x s e2)
  | ExPair e1 e2 => ExPair (expr_subst_surf x s e1) (expr_subst_surf x s e2)
  | ExFst e1 => ExFst (expr_subst_surf x s e1)
  | ExSnd e1 => ExSnd (expr_subst_surf x s e1)
  | ExIf e1 e2 e3 => ExIf (expr_subst_surf x s e1) (expr_subst_surf x s e2) (expr_subst_surf x s e3)
  | ExNot e1 => ExNot (expr_subst_surf x s e1)
  | ExAnd e1 e2 => ExAnd (expr_subst_surf x s e1) (expr_subst_surf x s e2)
  | ExOr e1 e2 => ExOr (expr_subst_surf x s e1) (expr_subst_surf x s e2)
  | ExImp e1 e2 => ExImp (expr_subst_surf x s e1) (expr_subst_surf x s e2)
  | ExEq e1 e2 => ExEq (expr_subst_surf x s e1) (expr_subst_surf x s e2)
  | ExNewRef τ e1 => ExNewRef τ (expr_subst_surf x s e1)
  | ExGet e1 => ExGet (expr_subst_surf x s e1)
  | ExSet e1 e2 => ExSet (expr_subst_surf x s e1) (expr_subst_surf x s e2)
  | ExDeRef e1 => ExDeRef (expr_subst_surf x s e1)
  | ExGetDep e1 => ExGetDep (expr_subst_surf x s e1)
  | ExSetDep e1 e2 => ExSetDep (expr_subst_surf x s e1) (expr_subst_surf x s e2)
  | EAssert e τ => EAssert (expr_subst_surf x s e) τ
  | ESimple e => ESimple (expr_subst_surf x s e)
  | EDep e => EDep (expr_subst_surf x s e)
  end.

Fixpoint ty_subst_surf (x : string) (s : expr) (τ : ty) : ty :=
  match τ with
  | TyBase b => TyBase b
  | TySet y b pred =>
      if String.eqb x y then TySet y b pred
      else TySet y b (expr_subst_surf x s pred)
  | TyArr t1 t2 => TyArr (ty_subst_surf x s t1) (ty_subst_surf x s t2)
  | TyArrDep y t1 t2 =>
      if String.eqb x y then TyArrDep y (ty_subst_surf x s t1) t2
      else TyArrDep y (ty_subst_surf x s t1) (ty_subst_surf x s t2)
  | TyProd t1 t2 => TyProd (ty_subst_surf x s t1) (ty_subst_surf x s t2)
  | TyRef t => TyRef (ty_subst_surf x s t)
  | TyDeRef t => TyDeRef (ty_subst_surf x s t)
  end.
