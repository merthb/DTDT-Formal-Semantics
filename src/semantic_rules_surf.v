Require Import DTDT.syntax.
Require Import DTDT.entails_inter.
Require Import DTDT.semantic_rules_inter.

(* Pure typing for surface expressions. *)

Fixpoint is_simple_type_surf (τ : ty) : bool :=
  match τ with
  | TyBase _ => true
  | TyArr t1 t2 => is_simple_type_surf t1 && is_simple_type_surf t2
  | TyProd t1 t2 => is_simple_type_surf t1 && is_simple_type_surf t2
  | TyRef t => is_simple_type_surf t
  | TyDeRef t => is_simple_type_surf t
  | _ => false
  end.

Definition essential_type_surf (τ : ty) : ty :=
  match τ with
  | TySet _ b _ => TyBase b
  | _ => τ
  end.

Definition essential_type_is_base_type_surf (τ : ty) : bool :=
  match τ with
  | TyBase _ => true
  | TySet _ _ _ => true
  | _ => false
  end.
Notation "βs[ t ]" := (essential_type_is_base_type_surf t) (at level 10).

Reserved Notation "Γ ⊢ₛpure e : τ" (at level 74, e, τ at next level).
Reserved Notation "Γ ⊢ₛvalid τ" (at level 74, τ at next level).

(* Pure typing judgment for surface expressions.
   Paper form: Γ ⊢ₛpure e : τ.
   This is the source-language analogue of internal pure typing and identifies the
   fragment that may appear in refinements and other purity-sensitive positions. *)
Inductive has_type_pure_surf
  ( Γ : ctx_surf)
  : expr -> ty -> Prop :=
  | PVarS :
    forall x τb v,
      Γ !!₁ₛ x = Some (τb, v) ->
      βs[ τb ] ->
      has_type_pure_surf Γ (ExVar x) (essential_type_surf τb)
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

Notation "Γ ⊢ₛpure e : τ" := (has_type_pure_surf Γ e τ)
  (at level 74, e, τ at next level).

(* Well-formedness of surface types. *)

(* Type validity judgment for surface types.
   Paper form: Γ ⊢ₛvalid τ.
   A valid surface type is well-formed relative to Γ, including the well-typedness
   of refinement predicates in the surface pure fragment. *)
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

Notation "Γ ⊢ₛvalid τ" := (ty_valid_surf Γ τ)
  (at level 74, τ at next level).

(* Capture-avoiding substitution on surface expressions and types. *)

Fixpoint expr_subst_surf (x : string) (s : expr) (e : expr) : expr :=
  match e with
  | ExVar y =>
      if String.eqb x y then s else ExVar y
  | ExLoc l => ExLoc l
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

(* Internal encoding of dynamic references.
   Paper form: ⟦τ dref⟧ = (unit → ⟦τ⟧) × (⟦τ⟧ → unit). *)
Definition dref_encoding (τ : i_ty) : i_ty :=
  TProd (TArr (TBase BUnit) τ) (TArr τ (TBase BUnit)).

(* Translation of surface types and the dref-free fragment of expressions.
   Paper forms: ⟦τ⟧ for type translation and ⟦Γ⟧c for context translation. *)
Fixpoint trans_type (τ : ty) : i_ty :=
  match τ with
  | TyBase b => TBase b
  | TySet v b e => TSet v b (match trans_expr_partial e with | Some e' => e' | None => EFail end)
  | TyArr t1 t2 => TArr (trans_type t1) (trans_type t2)
  | TyArrDep v t1 t2 => TArrDep v (trans_type t1) (trans_type t2)
  | TyProd t1 t2 => TProd (trans_type t1) (trans_type t2)
  | TyRef t => TRef (trans_type t)
  | TyDeRef t => dref_encoding (trans_type t)
  end
with trans_expr_partial (e : expr) : option i_expr :=
  match e with
  | ExString s => Some (EString s)
  | ExBool b => Some (EBool b)
  | ExNat n => Some (ENat n)
  | ExUnit u => Some (EUnit u)
  | ExConst c => Some (EConst c)
  | ExVar v => Some (EVar v)
  | ExLoc l => Some (ELoc l)
  | ExFix f x τ₁ τ₂ e1 =>
      match trans_expr_partial e1 with
      | Some e1' => Some (EFix f x (trans_type τ₁) (trans_type τ₂) e1')
      | None => None
      end
  | ExApp e1 e2 =>
      match trans_expr_partial e1, trans_expr_partial e2 with
      | Some e1', Some e2' => Some (EApp e1' e2')
      | _, _ => None
      end
  | ExPlus e1 e2 =>
      match trans_expr_partial e1, trans_expr_partial e2 with
      | Some e1', Some e2' => Some (EPlus e1' e2')
      | _, _ => None
      end
  | ExPair e1 e2 =>
      match trans_expr_partial e1, trans_expr_partial e2 with
      | Some e1', Some e2' => Some (EPair e1' e2')
      | _, _ => None
      end
  | ExFst e1 =>
      match trans_expr_partial e1 with
      | Some e1' => Some (EFst e1')
      | None => None
      end
  | ExSnd e1 =>
      match trans_expr_partial e1 with
      | Some e1' => Some (ESnd e1')
      | None => None
      end
  | ExIf e1 e2 e3 =>
      match trans_expr_partial e1, trans_expr_partial e2, trans_expr_partial e3 with
      | Some e1', Some e2', Some e3' => Some (EIf e1' e2' e3')
      | _, _, _ => None
      end
  | ExNot e1 =>
      match trans_expr_partial e1 with
      | Some e1' => Some (ENot e1')
      | None => None
      end
  | ExAnd e1 e2 =>
      match trans_expr_partial e1, trans_expr_partial e2 with
      | Some e1', Some e2' => Some (EAnd e1' e2')
      | _, _ => None
      end
  | ExOr e1 e2 =>
      match trans_expr_partial e1, trans_expr_partial e2 with
      | Some e1', Some e2' => Some (EOr e1' e2')
      | _, _ => None
      end
  | ExImp e1 e2 =>
      match trans_expr_partial e1, trans_expr_partial e2 with
      | Some e1', Some e2' => Some (EImp e1' e2')
      | _, _ => None
      end
  | ExEq e1 e2 =>
      match trans_expr_partial e1, trans_expr_partial e2 with
      | Some e1', Some e2' => Some (EEq e1' e2')
      | _, _ => None
      end
  | ExNewRef τ e1 =>
      match trans_expr_partial e1 with
      | Some e1' => Some (ENewRef (trans_type τ) e1')
      | None => None
      end
  | ExGet e1 =>
      match trans_expr_partial e1 with
      | Some e1' => Some (EGet e1')
      | None => None
      end
  | ExSet e1 e2 =>
      match trans_expr_partial e1, trans_expr_partial e2 with
      | Some e1', Some e2' => Some (ESet e1' e2')
      | _, _ => None
      end
  | ExDeRef _ => None
  | ExGetDep _ => None
  | ExSetDep _ _ => None
  | EAssert e1 _ => trans_expr_partial e1
  | ESimple e1 => trans_expr_partial e1
  | EDep e1 => trans_expr_partial e1
  end.

(* Total wrapper for positions that are required to be dref-free. *)
Definition trans_expr_dref_free (e : expr) : i_expr :=
  match trans_expr_partial e with
  | Some e' => e'
  | None => EFail
  end.

(* Translate a surface typing context into an internal context. *)
Definition trans_ctx_surf (gs : ctx_surf) : ctx :=
  let empty : store_context := snd empty_ctx in
  ((fmap (fun te => match te with (t, e) => (trans_type t, trans_expr_dref_free e) end) (fst gs),
    fmap (fun te => match te with (t, e) => (trans_type t, trans_expr_dref_free e) end) (snd gs)), empty).
Notation "⟦ τ ⟧" := (trans_type τ) (at level 1).
Notation "⟦ Γ ⟧c" := (trans_ctx_surf Γ) (at level 1).

(* Surface-level subtyping judgment.
   Structure follows internal subtyping, while refinement obligations are
   discharged through internal validity/entailment over translated artifacts. *)
Inductive subtype_surf
  (Γ : ctx_surf) :
  ty -> ty -> Prop :=
  | SBaseS :
    forall b,
      subtype_surf Γ (TyBase b) (TyBase b)
  | SSetS :
    forall var tb e1 e2 (c : base_to_set tb),
      ty_valid (trans_ctx_surf Γ) (trans_type (TySet var tb e1)) ->
      ty_valid (trans_ctx_surf Γ) (trans_type (TySet var tb e2)) ->
      entails (ctx_add_var (trans_ctx_surf Γ) var (TBase tb) (make_expr tb c))
        (EImp (trans_expr_dref_free e1) (trans_expr_dref_free e2)) ->
      subtype_surf Γ (TySet var tb e1) (TySet var tb e2)
  | SSetBaseS :
    forall var tb e,
      ty_valid (trans_ctx_surf Γ) (trans_type (TySet var tb e)) ->
      subtype_surf Γ (TySet var tb e) (TyBase tb)
  | SBaseSetS :
    forall var tb e (c : base_to_set tb),
      ty_valid (trans_ctx_surf Γ) (trans_type (TySet var tb e)) ->
      entails (ctx_add_var (trans_ctx_surf Γ) var (TBase tb) (make_expr tb c))
        (trans_expr_dref_free e) ->
      subtype_surf Γ (TyBase tb) (TySet var tb e)
  | SFunS :
    forall t1 t1' t2 t2',
      subtype_surf Γ t1' t1 ->
      subtype_surf Γ t2 t2' ->
      subtype_surf Γ (TyArr t1 t2) (TyArr t1' t2')
  | SFunDepS :
    forall var t1 t1' t2 t2' v,
      subtype_surf Γ t1' t1 ->
      subtype_surf (ctx_add_var_surf Γ var t1' v) t2 t2' ->
      subtype_surf Γ (TyArrDep var t1 t2) (TyArrDep var t1' t2')
  | SPairS :
    forall t1 t1' t2 t2',
      subtype_surf Γ t1 t1' ->
      subtype_surf Γ t2 t2' ->
      subtype_surf Γ (TyProd t1 t2) (TyProd t1' t2')
  | SRefS :
    forall t t',
      subtype_surf Γ t t' ->
      subtype_surf Γ t' t ->
      subtype_surf Γ (TyRef t) (TyRef t')
  | SDRefS :
    forall t t',
      subtype_surf Γ t t' ->
      subtype_surf Γ t' t ->
      subtype_surf Γ (TyDeRef t) (TyDeRef t').


