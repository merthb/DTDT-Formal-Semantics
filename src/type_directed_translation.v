Require Import DTDT.syntax.
Require Import DTDT.big_step_eval.
Require Import DTDT.semantic_rules.

(* --- Type directed translation from surface language to internal language -------------- *)

Inductive mode : Type :=
  | sim : mode
  | dep : mode.

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
  ( Γ : var_context_surf)
  (Φ : const_context_surf)
  : expr -> ty -> Prop :=
  | PVarS :
    forall x τb,
      Γs[ x ] Γ = Some τb ->
      βs[ τb ] ->
      has_type_pure_surf Γ Φ (ExVar x) τb
  | PNatS :
    forall n,
      has_type_pure_surf Γ Φ (ExNat n) (TyBase BNat)
  | PBoolS :
    forall b,
      has_type_pure_surf Γ Φ (ExBool b) (TyBase BBool)
  | PStringS :
    forall s,
      has_type_pure_surf Γ Φ (ExString s) (TyBase BString)
  | PUnitS :
    forall u,
      has_type_pure_surf Γ Φ (ExUnit u) (TyBase BUnit)
  | PConstS :
    forall c τ,
      Φs[ c ] Φ = Some τ ->
      is_simple_type_surf τ ->
      has_type_pure_surf Γ Φ (ExConst c) τ
  | PAppS :
    forall e₁ e₂ τ₁ τ₂,
      βs[ τ₁ ] ->
      has_type_pure_surf Γ Φ e₁ (TyArr τ₁ τ₂) ->
      has_type_pure_surf Γ Φ e₂ τ₁ ->
      has_type_pure_surf Γ Φ (ExApp e₁ e₂) τ₂
  | PNotS :
    forall b,
      has_type_pure_surf Γ Φ b (TyBase BBool) ->
      has_type_pure_surf Γ Φ (ExNot b) (TyBase BBool)
  | PImpS :
    forall b₁ b₂,
      has_type_pure_surf Γ Φ b₁ (TyBase BBool) ->
      has_type_pure_surf Γ Φ b₂ (TyBase BBool) ->
      has_type_pure_surf Γ Φ (ExImp b₁ b₂) (TyBase BBool)
  | PAndS :
    forall b₁ b₂,
      has_type_pure_surf Γ Φ b₁ (TyBase BBool) ->
      has_type_pure_surf Γ Φ b₂ (TyBase BBool) ->
      has_type_pure_surf Γ Φ (ExAnd b₁ b₂) (TyBase BBool)
  | POrS :
    forall b₁ b₂,
      has_type_pure_surf Γ Φ b₁ (TyBase BBool) ->
      has_type_pure_surf Γ Φ b₂ (TyBase BBool) ->
      has_type_pure_surf Γ Φ (ExOr b₁ b₂) (TyBase BBool)
  | PPlusS :
    forall n₁ n₂,
      has_type_pure_surf Γ Φ n₁ (TyBase BNat) ->
      has_type_pure_surf Γ Φ n₂ (TyBase BNat) ->
      has_type_pure_surf Γ Φ (ExPlus n₁ n₂) (TyBase BNat).

(* --- Translate surface type to internal type --------------------------------------- *)

Fixpoint trans_type (ty : ty) : i_ty :=
  match ty with
  | TyBase b => TBase b
  | TySet v b e => TSet v b (trans_expr e)
  | TyArr t1 t2 => TArr (trans_type t1) (trans_type t2)
  | TyArrDep v t1 t2 => TArrDep v (trans_type t1) (trans_type t2)
  | TyProd t1 t2 => TProd (trans_type t1) (trans_type t2)
  | TyRef t => TRef (trans_type t)
  | TyDeRef t => trans_type t  (* dereference at type level just removes TRef *)
  end

with trans_expr (e : expr) : i_expr :=
  match e with
  | ExString s => EString s
  | ExBool b => EBool b
  | ExNat n => ENat n
  | ExUnit u => EUnit u
  | ExConst c => EConst c
  | ExVar v => EVar v
  | ExFix f x ty1 ty2 e => EFix f x (trans_type ty1) (trans_type ty2) (trans_expr e)
  | ExApp e1 e2 => EApp (trans_expr e1) (trans_expr e2)
  | ExPlus e1 e2 => EPlus (trans_expr e1) (trans_expr e2)
  | ExPair e1 e2 => EPair (trans_expr e1) (trans_expr e2)
  | ExFst e => EFst (trans_expr e)
  | ExSnd e => ESnd (trans_expr e)
  | ExIf e1 e2 e3 => EIf (trans_expr e1) (trans_expr e2) (trans_expr e3)
  | ExNot e => ENot (trans_expr e)
  | ExAnd e1 e2 => EAnd (trans_expr e1) (trans_expr e2)
  | ExOr e1 e2 => EOr (trans_expr e1) (trans_expr e2)
  | ExImp e1 e2 => EImp (trans_expr e1) (trans_expr e2)
  | ExEq e1 e2 => EEq (trans_expr e1) (trans_expr e2)
  | ExNewRef ty e => ENewRef (trans_type ty) (trans_expr e)
  | ExGet e => EGet (trans_expr e)
  | ExSet e1 e2 => ESet (trans_expr e1) (trans_expr e2)
  | ExDeRef e => EGet (trans_expr e)
  | ExGetDep e => EGet (trans_expr e)
  | ExSetDep e1 e2 => ESet (trans_expr e1) (trans_expr e2)
  | EAssert e ty => trans_expr e
  | ESimple e => trans_expr e
  | EDep e => trans_expr e
  end.

Definition trans_var_context_surf (Γs : var_context_surf) : var_context :=
  map (fun p => (fst p, trans_type (snd p))) Γs.
Notation "x >>ᵥ" := (trans_var_context_surf x) (at level 1).

Definition trans_varval_context_surf (Γvs : varval_context_surf) : varval_context :=
  map (fun p => (fst p, trans_expr (snd p))) Γvs.
Notation "x >>ᵥᵥ" := (trans_varval_context_surf x) (at level 1).

Definition trans_const_context_surf (Φs : const_context_surf) : const_context :=
  map (fun p => (fst p, trans_type (snd p))) Φs.
Notation "x >>φ" := (trans_const_context_surf x) (at level 1).

Definition trans_fun_imp_list_surf (ιs : fun_imp_list_surf) : fun_imp_list :=
  map (fun p => (fst p, trans_expr (snd p))) ιs.
Notation "x >>ᵢ" := (trans_fun_imp_list_surf x) (at level 1).

(* ------------------------------------------------------------------------- *)
(* Erase dependency occurrences of a variable `x` from an internal type      *)
(* (implements the paper's `[ ]ₓ` operation                                *)
(* ------------------------------------------------------------------------- *)

Fixpoint erase_dep_var (x : string) (τ : i_ty) : i_ty :=
  match τ with
  | TBase b => TBase b
  | TSet y b pred => if String.eqb x y then TSet y b pred else
                      if in_dec string_dec x (exp_vars pred) then TBase b else TSet y b pred
  | TArr t1 t2 => TArr (erase_dep_var x t1) (erase_dep_var x t2)
  | TArrDep y t1 t2 => TArr (erase_dep_var x t1) (erase_dep_var x t2)
  | TProd t1 t2 => TProd (erase_dep_var x t1) (erase_dep_var x t2)
  | TRef t => TRef (erase_dep_var x t)
  end.
Notation "[[ t ]] x" := (erase_dep_var x t) (at level 1).

(* ------------------------------------------------------------------------- *)
(* Type coercion judgment (internal language)                                *)
(*   coerce ω Γ Γv Φ ι e τₛ e' τₜ  represents:                               *)
(*     Γ Γv Φ ι ⊢ω e : τₛ → e' : τₜ                                          *)
(* ------------------------------------------------------------------------- *)

Inductive coerce (w : mode) (Γ : var_context) (Γv : varval_context) (Φ : const_context) (ι : fun_imp_list) :
  i_expr -> i_ty -> i_expr -> i_ty -> Prop :=
  | CSub :
    forall e τ τ',
      (* when subtype holds no runtime conversion required *)
      subtype Γ Γv Φ ι τ τ' ->
      coerce w Γ Γv Φ ι
        e τ
        e τ'
  | CBase :
    forall e e₁ e₂ τ τb var,
      w = sim ->
      τ = (TBase τb) \/ ty_valid Γ Φ (TSet var τb e₂) ->
      coerce w Γ Γv Φ ι
        e τ
        (expr_subst var e (EIf e₁ (EVar var) EFail)) (TSet var τb e₁)
  | CFunCo :
    forall e x τ₁ τ₂ τ₁' τ₂' y eᵦ,
      w = sim ->
      subtype Γ Γv Φ ι τ₁' τ₁ ->
      coerce w ((y , TArrDep x τ₁ τ₂) :: (x, τ₁') :: Γ) Γv Φ ι
        (EApp (EVar y) (EVar x)) τ₂
        eᵦ τ₂' ->
      coerce w Γ Γv Φ ι
        e (TArr τ₁ τ₂)
        (expr_subst y e (EFix (fresh_string_list (exp_vars eᵦ)) x τ₁' τ₂' eᵦ)) (TArr τ₁' τ₂')
  | CFunContNonDep :
    forall e eᵦ eₓ x y τ₁ τ₂ τ₁' τ₂',
      w = sim ->
      ~ subtype Γ Γv Φ ι τ₁' τ₁ ->
      coerce w ((x , τ₁') :: Γ) Γv Φ ι
        (EVar x) τ₁'
        eₓ τ₁ ->
      coerce w ((y , TArr τ₁ τ₂) :: (x , τ₁') :: Γ) Γv Φ ι
        (EApp (EVar y) eₓ) τ₂
        eᵦ τ₂' ->
      coerce w Γ Γv Φ ι
        e (TArr τ₁ τ₂)
        (expr_subst y e (EFix (fresh_string_list (exp_vars eᵦ)) x τ₁' τ₂' eᵦ)) (TArr τ₁' τ₂')
  | CFunContDep :
    forall e eᵦ eᵦ' e₁ e₁' x y τ₁ τ₂ τ₁' τ₂' τb,
      w = sim ->
      ~ subtype Γ Γv Φ ι τ₁' τ₁ ->
      τ₁ = TSet x τb e₁ ->
      τ₁' = TSet x τb e₁' \/ τ₁' = TBase τb ->
      coerce w ((y , TArrDep x τ₁ τ₂) :: (x , τ₁) :: Γ) Γv Φ ι
        (EApp (EVar y) (EVar x)) τ₂
        eᵦ τ₂' ->
      eᵦ' = EIf e₁ eᵦ EFail ->
      coerce w Γ Γv Φ ι
        e (TArrDep x τ₁ τ₂)
        (expr_subst y e (EFix (fresh_string_list (exp_vars eᵦ')) x τ₁' τ₂' eᵦ')) (TArrDep x τ₁' τ₂')
  | CPair :
    forall e τ₁ τ₂ y e₁ e₂ τ₁' τ₂',
      w = sim ->
      coerce w ((y, TProd τ₁ τ₂) :: Γ) Γv Φ ι (EFst (EVar y)) τ₁ e₁ τ₁' ->
      coerce w ((y, TProd τ₁ τ₂) :: Γ) Γv Φ ι (ESnd (EVar y)) τ₂ e₂ τ₂' ->
      coerce w Γ Γv Φ ι e (TProd τ₁ τ₂)
             (expr_subst y e (EPair e₁ e₂)) (TProd τ₁' τ₂')
.

(* --- Type wellformedness for surface language -----------------------------*)

Inductive ty_valid_surf
  (Γ : var_context_surf)
  (Φ : const_context_surf)
  : ty -> Prop :=
  | VBaseS :
    forall (τb : BaseT),
      ty_valid_surf Γ Φ (TyBase τb)
  | VSetS :
    forall var (τb : BaseT) e,
      has_type_pure_surf ((var , TyBase τb) :: Γ) Φ e (TyBase BBool) ->
      ty_valid_surf Γ Φ (TySet var τb e)
  | VFunS :
    forall τ₁ τ₂,
      ty_valid_surf Γ Φ τ₁ ->
      ty_valid_surf Γ Φ τ₂ ->
      ty_valid_surf Γ Φ (TyArr τ₁ τ₂)
  | VFunDepS :
    forall var τ₁ τ₂,
      ty_valid_surf Γ Φ τ₁ ->
      ty_valid_surf ((var, τ₁) :: Γ) Φ τ₂ ->
      ty_valid_surf Γ Φ (TyArrDep var τ₁ τ₂)
  | VPairS :
    forall τ₁ τ₂,
      ty_valid_surf Γ Φ τ₁ ->
      ty_valid_surf Γ Φ τ₂ ->
      ty_valid_surf Γ Φ (TyProd τ₁ τ₂)
  | VRefS :
    forall τ₁,
      ty_valid_surf Γ Φ τ₁ ->
      ty_valid_surf Γ Φ (TyRef τ₁)
  | VDeRefS :
    forall τ₁,
      ty_valid_surf Γ Φ τ₁ ->
      ty_valid_surf Γ Φ (TyDeRef τ₁).

(* ------------------------------------------------------------------------- *)
(* Surface language typing & translation judgment                            *)
(*   has_type_surf w Γ Φ e e0 τ  corresponds to  ⊢^w e ; e0 : τ              *)
(* ------------------------------------------------------------------------- *)

Inductive has_type_surf (w : mode) (Γ : var_context_surf) (Γv : varval_context_surf) (Φ : const_context_surf) (ι : fun_imp_list_surf) :
  expr -> i_expr -> i_ty -> Prop :=
  | ATNat :
    forall n,
      has_type_surf w Γ Γv Φ ι (ExNat n) (ENat n) (TBase BNat)
  | ATBool :
    forall b,
      has_type_surf w Γ Γv Φ ι (ExBool b) (EBool b) (TBase BBool)
  | ATString :
    forall s,
      has_type_surf w Γ Γv Φ ι (ExString s) (EString s) (TBase BString)
  | ATUnit :
    forall u,
      has_type_surf w Γ Γv Φ ι (ExUnit u) (EUnit u) (TBase BUnit)
  | ATConstSelf :
    forall c τs,
      Φs[ c ] Φ = Some τs ->
      has_type_pure_surf Γ Φ (ExConst c) τs ->
      has_type_surf w Γ Γv Φ ι (ExConst c) (EConst c) (self (trans_type τs) (EConst c))
  | ATConst :
    forall c τs,
      Φs[ c ] Φ = Some τs ->
      ~ has_type_pure_surf Γ Φ (ExConst c) τs ->
      has_type_surf w Γ Γv Φ ι (ExConst c) (EConst c) (trans_type τs)
  | ATVarSelf :
    forall x τs,
      Γs[ x ] Γ = Some τs ->
      has_type_pure_surf Γ Φ (ExVar x) τs ->
      has_type_surf w Γ Γv Φ ι (ExVar x) (EVar x) (self (trans_type τs) (EVar x))
  | ATVar :
    forall x τs,
      Γs[ x ] Γ = Some τs ->
      ~ has_type_pure_surf Γ Φ (ExVar x) τs ->
      has_type_surf w Γ Γv Φ ι (ExVar x) (EVar x) (trans_type τs)
  | ATFun :
    forall f x τ₁ τ₂ τ₂' e e₁ e₂,
      ty_valid_surf Γ Φ (TyArrDep x τ₁ τ₂) ->
      has_type_surf w ((f , TyArrDep x τ₁ τ₂) :: (x , τ₁) :: Γ) Γv Φ ι e e₁ τ₂' ->
      coerce w (((f , TyArrDep x τ₁ τ₂) :: (x , τ₁) :: Γ) >>ᵥ) (Γv >>ᵥᵥ) (Φ >>φ) (ι >>ᵢ)
        e₁ τ₂'
        e₂ (trans_type τ₂) ->
      has_type_surf w Γ Γv Φ ι (ExFix f x τ₁ τ₂ e)
                    (EFix f x (trans_type τ₁) (trans_type τ₁) e₂)
                    (TArrDep x (trans_type τ₁) (trans_type τ₂))
  | ATAppPure :
    forall e₁ e₂ e₁' e₂' e₂'' x τ₁ τ₂ τ₁',
      has_type_surf w Γ Γv Φ ι e₁ e₁' (TArrDep x τ₁ τ₂) ->
      has_type_surf w Γ Γv Φ ι e₂ e₂' τ₁' ->
      coerce w (Γ >>ᵥ) (Γv >>ᵥᵥ) (Φ >>φ) (ι >>ᵢ)
        e₂' τ₁'
        e₂'' τ₁ ->
      (forall τ, has_type_pure (Γ >>ᵥ) (Φ >>φ) e₂'' τ) ->
      has_type_surf w Γ Γv Φ ι (ExApp e₁ e₂) (EApp e₁' e₂'') (ty_subst x e₂'' τ₂)
  | ATAppImPure :
    forall e₁ e₂ e₁' e₁'' e₂' e₂'' x τ₁ τ₂ τ₁',
      has_type_surf w Γ Γv Φ ι e₁ e₁' (TArrDep x τ₁ τ₂) ->
      has_type_surf w Γ Γv Φ ι e₂ e₂' τ₁' ->
      coerce w (Γ >>ᵥ) (Γv >>ᵥᵥ) (Φ >>φ) (ι >>ᵢ)
        e₂' τ₁'
        e₂'' τ₁ ->
      ~ (forall τ, has_type_pure (Γ >>ᵥ) (Φ >>φ) e₂'' τ) ->
      coerce w (Γ >>ᵥ) (Γv >>ᵥᵥ) (Φ >>φ) (ι >>ᵢ)
        e₁' (TArrDep x τ₁ τ₂)
        e₁'' (TArr τ₁ ([[ τ₂ ]] x)) ->
      has_type_surf w Γ Γv Φ ι (ExApp e₁ e₂) (EApp e₁'' e₂'') ([[ τ₂ ]] x)
  | ATProd :
    forall e₁ e₂ e₁' e₂' τ₁ τ₂,
      has_type_surf w Γ Γv Φ ι e₁ e₁' τ₁ ->
      has_type_surf w Γ Γv Φ ι e₂ e₂' τ₂ ->
      has_type_surf w Γ Γv Φ ι (ExPair e₁ e₂) (EPair e₁' e₂') (TProd τ₁ τ₂)
  | ATFst :
    forall e e' τ₁ τ₂,
      has_type_surf w Γ Γv Φ ι e e' (TProd τ₁ τ₂) ->
      has_type_surf w Γ Γv Φ ι (ExFst e) (EFst e') τ₁
  | ATSnd :
    forall e e' τ₁ τ₂,
      has_type_surf w Γ Γv Φ ι e e' (TProd τ₁ τ₂) ->
      has_type_surf w Γ Γv Φ ι (ExSnd e) (ESnd e') τ₂
  | ATIfPure :
    forall e e₁ e₂ e₁' e₁'' e₂' e₂'' τ₁ τ₂ τ₃ u,
      has_type_pure_surf Γ Φ e (TyBase BBool) ->
      has_type_surf w ((u , TyBase BBool) :: Γ) ((u , e) :: Γv) Φ ι e₁ e₁' τ₁ ->
      has_type_surf w ((u , TyBase BBool) :: Γ) ((u , ExNot e) :: Γv) Φ ι e₂ e₂' τ₂ ->
      coerce w (((u , TyBase BBool) :: Γ) >>ᵥ) (((u , e) :: Γv) >>ᵥᵥ) (Φ >>φ) (ι >>ᵢ)
        e₁' τ₁
        e₁'' τ₃ ->
      coerce w (((u , TyBase BBool) :: Γ) >>ᵥ) (((u , ExNot e) :: Γv) >>ᵥᵥ) (Φ >>φ) (ι >>ᵢ)
        e₂' τ₂
        e₂'' τ₃ ->
      (* TODO |_| definition *)
      has_type_surf w Γ Γv Φ ι (ExIf e e₁ e₂) (EIf (trans_expr e) e₁'' e₂'') τ₃
  | ATIfImPure :
    forall e e₁ e₂ e' x τ,
      ~ (forall τ', has_type_pure_surf Γ Φ e τ') ->
      has_type_surf w Γ Γv Φ ι (* TODO kell surface subst is *)(ExIf (ExVar x) e₁ e₂) e' τ ->
      has_type_surf w Γ Γv Φ ι (ExIf e e₁ e₂) e' τ
  (* TODO reference type rules *)
  | ATAssert :
    forall e e' e'' τ τ',
      w = dep ->
      has_type_surf w Γ Γv Φ ι e e' τ' ->
      ty_valid (Γ >>ᵥ) (Φ >>φ) (trans_type τ) ->
      coerce sim (Γ >>ᵥ) (Γv >>ᵥᵥ) (Φ >>φ) (ι >>ᵢ)
        e' τ'
        e'' (trans_type τ) ->
      has_type_surf w Γ Γv Φ ι (EAssert e τ) e'' (trans_type τ)
  | ATDynamic :
    forall e e' τ,
      w = dep ->
      has_type_surf sim Γ Γv Φ ι e e' τ ->
      has_type_surf w Γ Γv Φ ι (ESimple e) e' τ
  | ATStatic :
    forall e e' τ,
      w = sim ->
      has_type_surf dep Γ Γv Φ ι e e' τ ->
      has_type_surf w Γ Γv Φ ι (EDep e) e' τ.
