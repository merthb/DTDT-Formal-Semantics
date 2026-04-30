Require Import DTDT.syntax.
Require Import DTDT.machine_inter.
Require Import DTDT.entails_inter.
From stdpp Require Export base.
From stdpp Require Export strings.
From stdpp Require Import stringmap.

(* Auxiliary variable collection for selfification and dependency erasure. *)

Fixpoint exp_vars (term : i_expr) : list string :=
  match term with
  | EConst var => [var]
  | EVar var => [var]
  | EFix v1 v2 ty1 ty2 exp => v1 :: v2 :: ty_vars ty1 ++ ty_vars ty2 ++ exp_vars exp
  | EApp exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EPlus exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EPair exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EFst exp => exp_vars exp
  | ESnd exp => exp_vars exp
  | EIf exp1 exp2 exp3 => exp_vars exp1 ++ exp_vars exp2 ++ exp_vars exp3
  | ENot exp => exp_vars exp
  | EAnd exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EOr exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EImp exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | EEq exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | ENewRef τ exp => ty_vars τ ++ exp_vars exp
  | EGet exp => exp_vars exp
  | ESet exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | _ => []
  end
with ty_vars (τ : i_ty) : list string :=
  match τ with
  | TBase _ => []
  | TSet var _ exp => var :: exp_vars exp
  | TArr ty1 ty2 => ty_vars ty1 ++ ty_vars ty2
  | TArrDep var ty1 ty2 => var :: ty_vars ty1 ++ ty_vars ty2
  | TProd ty1 ty2 => ty_vars ty1 ++ ty_vars ty2
  | TRef τ => ty_vars τ
  end.

(* Remove one variable name from a free-variable list. *)
Definition remove_string (x : string) (xs : list string) : list string :=
  filter (fun y => negb (String.eqb x y)) xs.

(* Free variables for internal expressions and types. *)
Fixpoint free_exp_vars (e : i_expr) : list string :=
  match e with
  | EString _ => []
  | EBool _ => []
  | ENat _ => []
  | EUnit _ => []
  | EConst _ => []
  | EVar v => [v]
  | ELoc _ => []
  | EFix f x t1 t2 body =>
      free_ty_vars t1 ++ remove_string x (free_ty_vars t2 ++ free_exp_vars body)
  | EApp e1 e2 => free_exp_vars e1 ++ free_exp_vars e2
  | EPlus e1 e2 => free_exp_vars e1 ++ free_exp_vars e2
  | EPair e1 e2 => free_exp_vars e1 ++ free_exp_vars e2
  | EFst e0 => free_exp_vars e0
  | ESnd e0 => free_exp_vars e0
  | EIf e1 e2 e3 => free_exp_vars e1 ++ free_exp_vars e2 ++ free_exp_vars e3
  | ENot e0 => free_exp_vars e0
  | EAnd e1 e2 => free_exp_vars e1 ++ free_exp_vars e2
  | EOr e1 e2 => free_exp_vars e1 ++ free_exp_vars e2
  | EImp e1 e2 => free_exp_vars e1 ++ free_exp_vars e2
  | EEq e1 e2 => free_exp_vars e1 ++ free_exp_vars e2
  | ENewRef t e0 => free_ty_vars t ++ free_exp_vars e0
  | EGet e0 => free_exp_vars e0
  | ESet e1 e2 => free_exp_vars e1 ++ free_exp_vars e2
  | EFail => []
  end
with free_ty_vars (t : i_ty) : list string :=
  match t with
  | TBase _ => []
  | TSet x _ pred => remove_string x (free_exp_vars pred)
  | TArr t1 t2 => free_ty_vars t1 ++ free_ty_vars t2
  | TArrDep x t1 t2 => free_ty_vars t1 ++ remove_string x (free_ty_vars t2)
  | TProd t1 t2 => free_ty_vars t1 ++ free_ty_vars t2
  | TRef t0 => free_ty_vars t0
  end.

(* Pick a fresh variable name outside the given list. *)
Definition fresh_string_list (l : list string) : string :=
  fresh_string_of_set ("x"%string) (list_to_set l).

Definition if_branch_var (e1 e2 : i_expr) : string :=
  fresh_string_list (exp_vars (EPair e1 e2)).

(* Internal binder-stable selfification helper. *)
Fixpoint self_with (u : string) (τ : i_ty) (term : i_expr) : i_ty :=
  match τ with
  | TBase b => TSet u b (EEq (EVar u) term)
  | TSet var tb expr => TSet var tb (EAnd expr (EEq (EVar var) term))
  | TArr (TBase b) τ₂ => TArrDep u (TBase b) (self_with u τ₂ (EApp term (EVar u)))
  | TRef τ => TRef τ
  | x => x
  end.

(* Selfification refines a type with the information that a term inhabits it. *)
Definition self (τ : i_ty) (term : i_expr) : i_ty :=
  self_with (fresh_string_list (exp_vars term)) τ term.

(* Compute self (TBase BNat) (EVar ("x"%string)).
Compute self (TArr (TBase BNat) (TArr (TBase BNat) (TBase BNat))) (EVar ("+"%string)). *)


(* Pure internal typing for the fragment used inside refinements. *)

(*
Pure terms are:
- variables whose essential type is a base type
- constants with simple type (τb1 → τb2 → ... → τbn)
- application of pure terms to pure terms
 *)

(* Simple types are the types admitted for pure constants. *)
Fixpoint is_simple_type (τ : i_ty) : bool :=
  match τ with
  | TBase _ => true
  | TArr t1 t2 => is_simple_type t1 && is_simple_type t2
  | TProd t1 t2 => is_simple_type t1 && is_simple_type t2
  | TRef t => is_simple_type t
  | _ => false
  end.

(* Erase a refinement to its underlying simple carrier. *)
Definition essential_type (τ : i_ty) : i_ty :=
  match τ with
  | TSet _ b _ => TBase b
  | _ => τ
  end.

Definition essential_type_is_base_type (τ : i_ty) : bool :=
  match τ with
  | TBase _ => true
  | TSet _ _ _ => true
  | _ => false
  end.
Notation "β[ t ]" := (essential_type_is_base_type t) (at level 10).

Reserved Notation "Γ ⊢pure e : τ" (at level 74, e, τ at next level).
Reserved Notation "Γ ⊢valid τ" (at level 74, τ at next level).
Reserved Notation "Γ ⊢ τ₁ ≤ τ₂" (at level 74, τ₁, τ₂ at next level).
Reserved Notation "Γ ⊢ e : τ" (at level 74, e, τ at next level).

(* Pure typing judgment for internal expressions.
   Paper form: Γ ⊢pure e : τ.
   This judgment isolates the fragment admissible inside refinements and semantic
   premises: base values, simple constants, and applications that remain pure. *)
Inductive has_type_pure
  ( Γ : ctx)
  : i_expr -> i_ty -> Prop :=
  | PVar :
    forall x τb e,
      Γ !!₁ x = Some (τb, e) ->
      β[ τb ] ->
      has_type_pure Γ (EVar x) (essential_type τb)
  | PNat :
    forall n,
      has_type_pure Γ (ENat n) (TBase BNat)
  | PBool :
    forall b,
      has_type_pure Γ (EBool b) (TBase BBool)
  | PString :
    forall s,
      has_type_pure Γ (EString s) (TBase BString)
  | PUnit :
    forall u,
      has_type_pure Γ (EUnit u) (TBase BUnit)
  | PConst :
    forall c τ e,
      Γ !!₂ c = Some (τ, e) ->
      is_simple_type τ ->
      has_type_pure Γ (EConst c) τ
  | PApp :
    forall e₁ e₂ τ₁ τ₂,
      β[ τ₁ ] ->
      has_type_pure Γ e₁ (TArr τ₁ τ₂) ->
      has_type_pure Γ e₂ τ₁ ->
      has_type_pure Γ (EApp e₁ e₂) τ₂
  | PNot :
    forall b,
      has_type_pure Γ b (TBase BBool) ->
      has_type_pure Γ (ENot b) (TBase BBool)
  | PImp :
    forall b₁ b₂,
      has_type_pure Γ b₁ (TBase BBool) ->
      has_type_pure Γ b₂ (TBase BBool) ->
      has_type_pure Γ (EImp b₁ b₂) (TBase BBool)
  | PAnd :
    forall b₁ b₂,
      has_type_pure Γ b₁ (TBase BBool) ->
      has_type_pure Γ b₂ (TBase BBool) ->
      has_type_pure Γ (EAnd b₁ b₂) (TBase BBool)
  | POr :
    forall b₁ b₂,
      has_type_pure Γ b₁ (TBase BBool) ->
      has_type_pure Γ b₂ (TBase BBool) ->
      has_type_pure Γ (EOr b₁ b₂) (TBase BBool)
  | PEq :
    forall e₁ e₂ τb,
      has_type_pure Γ e₁ (TBase τb) ->
      has_type_pure Γ e₂ (TBase τb) ->
      has_type_pure Γ (EEq e₁ e₂) (TBase BBool)
  | PPlus :
    forall n₁ n₂,
      has_type_pure Γ n₁ (TBase BNat) ->
      has_type_pure Γ n₂ (TBase BNat) ->
      has_type_pure Γ (EPlus n₁ n₂) (TBase BNat).

Notation "Γ ⊢pure e : τ" := (has_type_pure Γ e τ)
  (at level 74, e, τ at next level).

(* Well-formedness of internal types. *)

(* Type validity judgment for internal types.
   Paper form: Γ ⊢valid τ.
   A valid type is well-formed relative to Γ, including the requirement that every
   refinement predicate is itself well-typed in the pure fragment. *)
Inductive ty_valid
  (Γ : ctx)
  : i_ty -> Prop :=
  | VBase :
    forall (τb : BaseT),
      ty_valid Γ (TBase τb)
  | VSet :
    forall var (τb : BaseT) e v,
      has_type_pure (ctx_add_var Γ var (TBase τb) v) e (TBase BBool) ->
      ty_valid Γ (TSet var τb e)
  | VFun :
    forall τ₁ τ₂,
      ty_valid Γ τ₁ ->
      ty_valid Γ τ₂ ->
      ty_valid Γ (TArr τ₁ τ₂)
  | VFunDep :
    forall var t1 t2,
      ~ List.In var (free_ty_vars t1) ->
      ty_valid Γ t1 ->
      ty_valid (ctx_add_var Γ var t1 (EVar var)) t2 ->
      ty_valid Γ (TArrDep var t1 t2)
  | VPair :
    forall τ₁ τ₂,
      ty_valid Γ τ₁ ->
      ty_valid Γ τ₂ ->
      ty_valid Γ (TProd τ₁ τ₂)
  | VRef :
    forall τ,
      ty_valid Γ τ ->
      ty_valid Γ (TRef τ).

Notation "Γ ⊢valid τ" := (ty_valid Γ τ)
  (at level 74, τ at next level).

(* Semantic subtyping for internal types. *)

(* Internal subtyping judgment.
   Paper form: Γ ⊢ τ₁ ≤ τ₂.
   This relation combines ordinary structural rules with semantic implications for
   refinement types, and it is the subtyping notion used by typing and coercion. *)
Inductive subtype 
  (Γ : ctx) :
  i_ty -> i_ty -> Prop :=
  | SBase :
    forall b,
      subtype Γ (TBase b) (TBase b)
  | SSet :
    forall var τb e₁ e₂ (c : (base_to_set τb)),
      ty_valid Γ (TSet var τb e₁) ->
      ty_valid Γ (TSet var τb e₂) ->
      (ctx_add_var Γ var (TBase τb) (make_expr τb c)) ⊨ (EImp e₁ e₂) ->
      subtype Γ (TSet var τb e₁) (TSet var τb e₂)
  | SSetBase :
    forall var τb e,
      ty_valid Γ (TSet var τb e) ->
      subtype Γ (TSet var τb e) (TBase τb)
  | SBaseSet :
    forall var τb e (c : (base_to_set τb)),
      ty_valid Γ (TSet var τb e) ->
      (ctx_add_var Γ var (TBase τb) (make_expr τb c)) ⊨ e ->
      subtype Γ (TBase τb) (TSet var τb e)
  | SFun :
    forall τ₁ τ₁' τ₂ τ₂',
      subtype Γ τ₁' τ₁ ->
      subtype Γ τ₂ τ₂' ->
      subtype Γ (TArr τ₁ τ₂) (TArr τ₁' τ₂')
  | SFunDep :
    forall var t1 t1' t2 t2',
      ~ List.In var (free_ty_vars t1') ->
      subtype Γ t1' t1 ->
      subtype (ctx_add_var Γ var t1' (EVar var)) t2 t2' ->
      subtype Γ (TArrDep var t1 t2) (TArrDep var t1' t2')
  | SPair :
    forall τ₁ τ₁' τ₂ τ₂',
      subtype Γ τ₁ τ₁' ->
      subtype Γ τ₂ τ₂' ->
      subtype Γ (TProd τ₁ τ₂) (TProd τ₁' τ₂')
  | SRef :
    forall t t',
      subtype Γ t t' ->
      subtype Γ t' t ->
      subtype Γ (TRef t) (TRef t').

(* Main typing judgment for internal expressions. *)

(* Internal typing judgment.
   Paper form: Ψ ; Γ ⊢ e : τ.
   In the current Coq encoding the single context Γ packages the variable, constant,
   and store components that are separated notationally in the paper. *)
Inductive has_type
  ( Γ : ctx)
  : i_expr -> i_ty -> Prop :=
  | TString :
    forall s,
      has_type Γ (EString s) (TBase BString)
  | TNat :
    forall n,
      has_type Γ (ENat n) (TBase BNat)
  | TBool :
    forall b,
      has_type Γ (EBool b) (TBase BBool)
  | TUnit :
    forall u,
      has_type Γ (EUnit u) (TBase BUnit)
  | TConst :
    forall c τ e,
      Γ !!₂ c = Some (τ, e) ->
      has_type Γ (EConst c) τ
  | TVar :
    forall v τ e,
      Γ !!₁ v = Some (τ, e) ->
      has_type Γ (EVar v) τ
  | TEssentialVar :
    forall v τ e,
      Γ !!₁ v = Some (τ, e) ->
      β[ τ ] ->
      has_type Γ (EVar v) (essential_type τ)
  | TLoc :
    forall l t v,
      Γ !!₃ l = Some (t, v) ->
      has_type Γ (ELoc l) (TRef t)
  | TFail :
    forall τ,
      ty_valid Γ τ ->
      has_type Γ EFail τ
  | TFunDep :
    forall f x τ₁ τ₂ e,
      ~ List.In x (ty_vars τ₁) ->
      ty_valid Γ (TArrDep x τ₁ τ₂) ->
      has_type ((Γ ,,c f ↦ (TArrDep x τ₁ τ₂, EFix f x τ₁ τ₂ e)) ,,v x ↦ (τ₁, EVar x)) e τ₂ ->
      has_type Γ (EFix f x τ₁ τ₂ e) (TArrDep x τ₁ τ₂)
  | TFun :
    forall f x τ₁ τ₂ e,
      ty_valid Γ (TArr τ₁ τ₂) ->
      has_type ((Γ ,,c f ↦ (TArr τ₁ τ₂, EFix f x τ₁ τ₂ e)) ,,v x ↦ (τ₁, EVar x)) e τ₂ ->
      has_type Γ (EFix f x τ₁ τ₂ e) (TArr τ₁ τ₂)
  | TAppPure :
    forall e₁ e₂ x τ₁ τ₂,
      has_type Γ e₂ τ₁ ->
      has_type_pure Γ e₂ (essential_type τ₁) ->
      has_type Γ e₁ (TArrDep x τ₁ τ₂) ->
      has_type Γ (EApp e₁ e₂) (ty_subst x e₂ τ₂)
  | TAppImPure :
    forall e₁ e₂ τ₁ τ₂,
      has_type Γ e₂ τ₁ ->
      has_type Γ e₁ (TArr τ₁ τ₂) ->
      has_type Γ (EApp e₁ e₂) τ₂
  | TPlus :
    forall e₁ e₂,
      has_type Γ e₁ (TBase BNat) ->
      has_type Γ e₂ (TBase BNat) ->
      has_type Γ (EPlus e₁ e₂) (TBase BNat)
  | TNot :
    forall e,
      has_type Γ e (TBase BBool) ->
      has_type Γ (ENot e) (TBase BBool)
  | TImp :
    forall e₁ e₂,
      has_type Γ e₁ (TBase BBool) ->
      has_type Γ e₂ (TBase BBool) ->
      has_type Γ (EImp e₁ e₂) (TBase BBool)
  | TAnd :
    forall e₁ e₂,
      has_type Γ e₁ (TBase BBool) ->
      has_type Γ e₂ (TBase BBool) ->
      has_type Γ (EAnd e₁ e₂) (TBase BBool)
  | TOr :
    forall e₁ e₂,
      has_type Γ e₁ (TBase BBool) ->
      has_type Γ e₂ (TBase BBool) ->
      has_type Γ (EOr e₁ e₂) (TBase BBool)
  | TEq :
    forall e₁ e₂ τb,
      has_type Γ e₁ (TBase τb) ->
      has_type Γ e₂ (TBase τb) ->
      has_type Γ (EEq e₁ e₂) (TBase BBool)
  | TRefI :
    forall τ e,
      ty_valid Γ τ ->
      has_type Γ e τ ->
      has_type Γ (ENewRef τ e) (TRef τ)
  | TGet :
    forall e τ,
      has_type Γ e (TRef τ) ->
      has_type Γ (EGet e) τ
  | TSetI :
    forall e1 e2 τ,
      has_type Γ e1 (TRef τ) ->
      has_type Γ e2 τ ->
      has_type Γ (ESet e1 e2) (TBase BUnit)
  | TPair :
    forall e₁ e₂ τ₁ τ₂,
      has_type Γ e₁ τ₁ ->
      has_type Γ e₂ τ₂ ->
      has_type Γ (EPair e₁ e₂) (TProd τ₁ τ₂)
  | TFst :
    forall e τ₁ τ₂,
      has_type Γ e (TProd τ₁ τ₂) ->
      has_type Γ (EFst e) τ₁
  | TSnd :
    forall e τ₁ τ₂,
      has_type Γ e (TProd τ₁ τ₂) ->
      has_type Γ (ESnd e) τ₂
  | TIf :
    forall e e1 e2 t,
      has_type_pure Γ e (TBase BBool) ->
      has_type Γ e1 t ->
      has_type Γ e2 t ->
      has_type Γ (EIf e e1 e2) t
  | TSelf :
    forall e τ,
      has_type Γ e τ ->
      has_type_pure Γ e (essential_type τ) ->
      has_type Γ e (self τ e)
  | TSub :
    forall e τ τ',
      has_type Γ e τ' ->
      subtype Γ τ' τ ->
      has_type Γ e τ.

(* Store well-typedness invariant.
   Auxiliary paper-style reading: every location l in the store of Γ satisfies
   Γ(l) = (τ, v) only if Γ ⊢valid τ and Γ ⊢ v : τ. This invariant
   supports the reference fragment of preservation. *)
Inductive store_well_typed (Γ : ctx) : Prop :=
  | StoreWellTyped :
    (forall l t v,
      Γ !!₃ l = Some (t, v) ->
      ty_valid Γ t /\ has_type Γ v t) ->
    store_well_typed Γ.

Definition var_well_typed (Γ : ctx) : Prop :=
  forall x t v,
    var_ctx_lookup Γ x = Some (t, v) ->
    ty_valid Γ t /\ has_type Γ v t.

Definition const_well_typed (Γ : ctx) : Prop :=
  forall c t e,
    const_ctx_lookup Γ c = Some (t, e) ->
    ty_valid Γ t /\ has_type Γ e t.

Definition var_base_pure_well_typed (G : ctx) : Prop :=
  forall x t v,
    var_ctx_lookup G x = Some (t, v) ->
    essential_type_is_base_type t = true ->
    has_type_pure G v (essential_type t).

Definition const_step_well_typed (G : ctx) : Prop :=
  forall c t e v ttop,
    const_ctx_lookup G c = Some (t, e) ->
    value G v ->
    has_type G (EApp (EConst c) v) ttop ->
    has_type G (EApp e v) ttop.

Definition const_step_pure_well_typed (G : ctx) : Prop :=
  forall c t e v ty,
    const_ctx_lookup G c = Some (t, e) ->
    value G v ->
    has_type_pure G (EApp (EConst c) v) ty ->
    has_type_pure G (EApp e v) ty.

Inductive runtime_ctx_well_typed (G : ctx) : Prop :=
  | RuntimeCtxWellTyped :
    var_well_typed G ->
    var_base_pure_well_typed G ->
    const_well_typed G ->
    const_step_well_typed G ->
    const_step_pure_well_typed G ->
    store_well_typed G ->
    runtime_ctx_well_typed G.
