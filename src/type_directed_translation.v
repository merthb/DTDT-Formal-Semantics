Require Import DTDT.syntax.
Require Import DTDT.big_step_eval_inter.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.semantic_rules_surf.

(* --- Type directed translation from surface language to internal language -------------- *)

Inductive mode : Type :=
  | sim : mode
  | dep : mode.

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

Definition trans_ctx_surf (Γs : ctx_surf) : ctx :=
  (fmap (λ '(t, e), (trans_type t, trans_expr e)) (Γs ▷surfvars),
   fmap (λ '(t, e), (trans_type t, trans_expr e)) (Γs ▷surfconsts)).
Notation "x >>" := (trans_ctx_surf x) (at level 1).

(* ------------------------------------------------------------------------- *)
(* Erase dependency occurrences of a variable `x` from an internal type      *)
(* (implements the paper's `[ ]ₓ` operation                                *)
(* ------------------------------------------------------------------------- *)

Fixpoint erase_dep_var (x : string) (τ : i_ty) : i_ty :=
  match τ with
  | TBase b => TBase b
  | TSet y b pred => if String.eqb x y then TSet y b pred else
                      if existsb (String.eqb x) (exp_vars pred) then TBase b else TSet y b pred
  | TArr t1 t2 => TArr (erase_dep_var x t1) (erase_dep_var x t2)
  | TArrDep y t1 t2 => TArr (erase_dep_var x t1) (erase_dep_var x t2)
  | TProd t1 t2 => TProd (erase_dep_var x t1) (erase_dep_var x t2)
  | TRef t => TRef (erase_dep_var x t)
  end.
Notation "[[ t ]] x" := (erase_dep_var x t) (at level 1).

(* --- Erase dependency in i_ty -------------------------------------------- *)

Fixpoint erase_i_ty (τ : i_ty) : i_ty :=
  match τ with
  | TBase b =>
      TBase b
  | TSet x b _ =>
      TSet x b (EBool true)
  | TArr t1 t2 =>
      TArr (erase_i_ty t1) (erase_i_ty t2)
  | TArrDep _ t1 t2 =>
      TArr (erase_i_ty t1) (erase_i_ty t2)
  | TProd t1 t2 =>
      TProd (erase_i_ty t1) (erase_i_ty t2)
  | TRef t =>
      TRef (erase_i_ty t)
  end.
Notation "[| t |]" := (erase_i_ty t) (at level 1).

(* ------------------------------------------------------------------------- *)
(* Type coercion judgment (internal language)                                *)
(*   coerce ω Γ Γv Φ ι e τₛ e' τₜ  represents:                               *)
(*     Γ Γv Φ ι ⊢ω e : τₛ → e' : τₜ                                          *)
(* ------------------------------------------------------------------------- *)

Inductive coerce (w : mode) (Γ : ctx) :
  i_expr -> i_ty -> i_expr -> i_ty -> Prop :=
  | CSub :
    forall e τ τ',
      (* when subtype holds no runtime conversion required *)
      subtype Γ τ τ' ->
      coerce w Γ
        e τ
        e τ'
  | CBase :
    forall e e₁ e₂ τ τb var,
      w = sim ->
      τ = (TBase τb) \/ τ = (TSet var τb e₂) ->
      coerce w Γ
        e                                             τ
        (expr_subst var e (EIf e₁ (EVar var) EFail)) (TSet var τb e₁)
  | CFunCo :
    forall e x τ₁ τ₂ τ₁' τ₂' y eᵦ v₁ v₂,
      w = sim ->
      subtype Γ τ₁' τ₁ ->
      coerce w (ctx_add_var (ctx_add_const Γ y (TArrDep x τ₁ τ₂) v₁) x τ₁' v₂)
        (EApp (EVar y) (EVar x)) τ₂
        eᵦ                       τ₂' ->
      coerce w Γ
        e                                                                     (TArr τ₁ τ₂)
        (expr_subst y e (EFix (fresh_string_list (exp_vars eᵦ)) x τ₁' τ₂' eᵦ)) (TArr τ₁' τ₂')
  | CFunContNonDep :
    forall e eᵦ eₓ x y τ₁ τ₂ τ₁' τ₂' v₁ v₂,
      w = sim ->
      ~ subtype Γ τ₁' τ₁ ->
      coerce w (ctx_add_var Γ x τ₁' v₁)
        (EVar x) τ₁'
        eₓ       τ₁ ->
      coerce w (ctx_add_var (ctx_add_const Γ y (TArrDep x τ₁ τ₂) v₁) x τ₁' v₂)
        (EApp (EVar y) eₓ) τ₂
        eᵦ                 τ₂' ->
      coerce w Γ
        e                                                                     (TArr τ₁ τ₂)
        (expr_subst y e (EFix (fresh_string_list (exp_vars eᵦ)) x τ₁' τ₂' eᵦ)) (TArr τ₁' τ₂')
  | CFunContDep :
    forall e eᵦ eᵦ' e₁ e₁' x y τ₁ τ₂ τ₁' τ₂' τb v₁ v₂,
      w = sim ->
      ~ subtype Γ τ₁' τ₁ ->
      τ₁ = TSet x τb e₁ ->
      τ₁' = TSet x τb e₁' \/ τ₁' = TBase τb ->
      coerce w (ctx_add_var (ctx_add_const Γ y (TArr τ₁ τ₂) v₂) x τ₁' v₁)
        (EApp (EVar y) (EVar x)) τ₂
        eᵦ                       τ₂' ->
      eᵦ' = EIf e₁ eᵦ EFail ->
      coerce w Γ
        e                                                                       (TArrDep x τ₁ τ₂)
        (expr_subst y e (EFix (fresh_string_list (exp_vars eᵦ')) x τ₁' τ₂' eᵦ')) (TArrDep x τ₁' τ₂')
  | CPair :
    forall e τ₁ τ₂ y e₁ e₂ τ₁' τ₂' v,
      w = sim ->
      coerce w (ctx_add_var Γ y (TProd τ₁ τ₂) v)
        (EFst (EVar y)) τ₁
        e₁              τ₁' ->
      coerce w (ctx_add_var Γ y (TProd τ₁ τ₂) v)
        (ESnd (EVar y)) τ₂
        e₂              τ₂' ->
      coerce w Γ
        e                              (TProd τ₁ τ₂)
        (expr_subst y e (EPair e₁ e₂)) (TProd τ₁' τ₂')
.

(* --- Meet and join (τ₁ ⊓ τ₂ / τ₁ ⊔ τ₂) ----------------------------------- *)

Inductive ty_meet (Γ : ctx) : i_ty -> i_ty -> i_ty -> Prop :=
  | MeetBase :
    forall b,
      ty_meet Γ (TBase b) (TBase b) (TBase b)
  | MeetSet :
    forall x b e1 e2,
      ty_meet Γ (TSet x b e1) (TSet x b e2) (TSet x b (EAnd e1 e2))
  | MeetBaseLeft :
    forall x b e,
      ty_meet Γ (TBase b) (TSet x b e) (TSet x b e)
  | MeetBaseRight :
    forall x b e,
      ty_meet Γ (TSet x b e) (TBase b) (TSet x b e)
  | MeetArr :
    forall τ1 τ1' τ2 τ2' dom cod,
      ty_join Γ τ1 τ1' dom ->
      ty_meet Γ τ2 τ2' cod ->
      ty_meet Γ (TArr τ1 τ2) (TArr τ1' τ2') (TArr dom cod)
  | MeetArrDep :
    forall x τ1 τ1' τ2 τ2' dom cod v,
      ty_join Γ τ1 τ1' dom ->
      ty_meet (ctx_add_var Γ x τ1 v) τ2 τ2' cod ->
      ty_meet Γ (TArrDep x τ1 τ2) (TArrDep x τ1' τ2') (TArrDep x dom cod)
  | MeetProd :
    forall τ1 τ1' τ2 τ2' m1 m2,
      ty_meet Γ τ1 τ1' m1 ->
      ty_meet Γ τ2 τ2' m2 ->
      ty_meet Γ (TProd τ1 τ2) (TProd τ1' τ2') (TProd m1 m2)
  | MeetRef :
    forall τ τ' m,
      ty_meet Γ τ τ' m ->
      ty_meet Γ (TRef τ) (TRef τ') (TRef m)

with ty_join (Γ : ctx) : i_ty -> i_ty -> i_ty -> Prop :=
  | JoinBase :
    forall b,
      ty_join Γ (TBase b) (TBase b) (TBase b)
  | JoinSet :
    forall x b e1 e2,
      ty_join Γ (TSet x b e1) (TSet x b e2) (TSet x b (EOr e1 e2))
  | JoinBaseLeft :
    forall x b e,
      ty_join Γ (TBase b) (TSet x b e) (TSet x b e)
  | JoinBaseRight :
    forall x b e,
      ty_join Γ (TSet x b e) (TBase b) (TSet x b e)
  | JoinArr :
    forall τ1 τ1' τ2 τ2' dom cod,
      ty_meet Γ τ1 τ1' dom ->
      ty_join Γ τ2 τ2' cod ->
      ty_join Γ (TArr τ1 τ2) (TArr τ1' τ2') (TArr dom cod)
  | JoinArrDep :
    forall x τ1 τ1' τ2 τ2' dom cod v,
      ty_meet Γ τ1 τ1' dom ->
      ty_join (ctx_add_var Γ x dom v) τ2 τ2' cod ->
      ty_join Γ (TArrDep x τ1 τ2) (TArrDep x τ1' τ2') (TArrDep x dom cod)
  | JoinProd :
    forall τ1 τ1' τ2 τ2' j1 j2,
      ty_join Γ τ1 τ1' j1 ->
      ty_join Γ τ2 τ2' j2 ->
      ty_join Γ (TProd τ1 τ2) (TProd τ1' τ2') (TProd j1 j2)
  | JoinRef :
    forall τ τ' j,
      ty_join Γ τ τ' j ->
      ty_join Γ (TRef τ) (TRef τ') (TRef [| j |]).

(* ------------------------------------------------------------------------- *)
(* Surface language typing & translation judgment                            *)
(*   has_type_surf w Γ Φ e e0 τ  corresponds to  ⊢^w e ; e0 : τ              *)
(* ------------------------------------------------------------------------- *)

Inductive has_type_surf (w : mode) (Γ : ctx_surf) :
  expr -> i_expr -> i_ty -> Prop :=
  | ATNat :
    forall n,
      has_type_surf w Γ (ExNat n) (ENat n) (TBase BNat)
  | ATBool :
    forall b,
      has_type_surf w Γ (ExBool b) (EBool b) (TBase BBool)
  | ATString :
    forall s,
      has_type_surf w Γ (ExString s) (EString s) (TBase BString)
  | ATUnit :
    forall u,
      has_type_surf w Γ (ExUnit u) (EUnit u) (TBase BUnit)
  | ATConstSelf :
    forall c τs v,
      Γ !!₂ₛ c = Some (τs, v) ->
      has_type_pure_surf Γ (ExConst c) τs ->
      has_type_surf w Γ (ExConst c) (EConst c) (self (trans_type τs) (EConst c))
  | ATConst :
    forall c τs v,
      Γ !!₂ₛ c = Some (τs, v) ->
      ~ has_type_pure_surf Γ (ExConst c) τs ->
      has_type_surf w Γ (ExConst c) (EConst c) (trans_type τs)
  | ATVarSelf :
    forall x τs v,
      Γ !!₁ₛ x = Some (τs, v) ->
      has_type_pure_surf Γ (ExVar x) τs ->
      has_type_surf w Γ (ExVar x) (EVar x) (self (trans_type τs) (EVar x))
  | ATVar :
    forall x τs v,
      Γ !!₁ₛ x = Some (τs, v) ->
      ~ has_type_pure_surf Γ (ExVar x) τs ->
      has_type_surf w Γ (ExVar x) (EVar x) (trans_type τs)
  | ATFun :
    forall f x τ₁ τ₂ τ₂' e e₁ e₂ v₁ v₂,
      ty_valid_surf Γ (TyArrDep x τ₁ τ₂) ->
      has_type_surf w (ctx_add_var_surf (ctx_add_const_surf Γ f (TyArrDep x τ₁ τ₂) v₂) x τ₁ v₁) e e₁ τ₂' ->
      coerce w ((ctx_add_var_surf (ctx_add_const_surf Γ f (TyArrDep x τ₁ τ₂) v₂) x τ₁ v₁) >>)
        e₁ τ₂'
        e₂ (trans_type τ₂) ->
      has_type_surf w Γ (ExFix f x τ₁ τ₂ e)
                    (EFix f x (trans_type τ₁) (trans_type τ₁) e₂)
                    (TArrDep x (trans_type τ₁) (trans_type τ₂))
  | ATAppPure :
    forall e₁ e₂ e₁' e₂' e₂'' x τ₁ τ₂ τ₁',
      has_type_surf w Γ e₁ e₁' (TArrDep x τ₁ τ₂) ->
      has_type_surf w Γ e₂ e₂' τ₁' ->
      coerce w (Γ >>)
        e₂' τ₁'
        e₂'' τ₁ ->
      (forall τ, has_type_pure (Γ >>) e₂'' τ) ->
      has_type_surf w Γ (ExApp e₁ e₂) (EApp e₁' e₂'') (ty_subst x e₂'' τ₂)
  | ATAppImPure :
    forall e₁ e₂ e₁' e₁'' e₂' e₂'' x τ₁ τ₂ τ₁',
      has_type_surf w Γ e₁ e₁' (TArrDep x τ₁ τ₂) ->
      has_type_surf w Γ e₂ e₂' τ₁' ->
      coerce w (Γ >>)
        e₂' τ₁'
        e₂'' τ₁ ->
      ~ (forall τ, has_type_pure (Γ >>) e₂'' τ) ->
      coerce w (Γ >>)
        e₁' (TArrDep x τ₁ τ₂)
        e₁'' (TArr τ₁ ([[ τ₂ ]] x)) ->
      has_type_surf w Γ (ExApp e₁ e₂) (EApp e₁'' e₂'') ([[ τ₂ ]] x)
  | ATProd :
    forall e₁ e₂ e₁' e₂' τ₁ τ₂,
      has_type_surf w Γ e₁ e₁' τ₁ ->
      has_type_surf w Γ e₂ e₂' τ₂ ->
      has_type_surf w Γ (ExPair e₁ e₂) (EPair e₁' e₂') (TProd τ₁ τ₂)
  | ATFst :
    forall e e' τ₁ τ₂,
      has_type_surf w Γ e e' (TProd τ₁ τ₂) ->
      has_type_surf w Γ (ExFst e) (EFst e') τ₁
  | ATSnd :
    forall e e' τ₁ τ₂,
      has_type_surf w Γ e e' (TProd τ₁ τ₂) ->
      has_type_surf w Γ (ExSnd e) (ESnd e') τ₂
  | ATIfPure :
    forall e e₁ e₂ e₁' e₁'' e₂' e₂'' τ₁ τ₂ τ₃ u,
      has_type_pure_surf Γ e (TyBase BBool) ->
      has_type_surf w (ctx_add_var_surf Γ u (TyBase BBool) e) e₁ e₁' τ₁ ->
      has_type_surf w (ctx_add_var_surf Γ u (TyBase BBool) (ExNot e)) e₂ e₂' τ₂ ->
      coerce w ((ctx_add_var_surf Γ u (TyBase BBool) e) >>)
        e₁' τ₁
        e₁'' τ₃ ->
      coerce w ((ctx_add_var_surf Γ u (TyBase BBool) (ExNot e)) >>)
        e₂' τ₂
        e₂'' τ₃ ->
      ty_join (Γ >>) τ₁ τ₂ τ₃ ->
      has_type_surf w Γ (ExIf e e₁ e₂) (EIf (trans_expr e) e₁'' e₂'') τ₃
  | ATIfImPure :
    forall e e₁ e₂ e' x τ,
      ~ (forall τ', has_type_pure_surf Γ e τ') ->
      has_type_surf w Γ (expr_subst_surf x e (ExIf (ExVar x) e₁ e₂)) e' τ ->
      has_type_surf w Γ (ExIf e e₁ e₂) e' τ
  (* TODO reference type rules *)
  | ATAssert :
    forall e e' e'' τ τ',
      w = dep ->
      has_type_surf w Γ e e' τ' ->
      ty_valid (Γ >>) (trans_type τ) ->
      coerce sim (Γ >>)
        e' τ'
        e'' (trans_type τ) ->
      has_type_surf w Γ (EAssert e τ) e'' (trans_type τ)
  | ATDynamic :
    forall e e' τ,
      w = dep ->
      has_type_surf sim Γ e e' τ ->
      has_type_surf w Γ (ESimple e) e' τ
  | ATStatic :
    forall e e' τ,
      w = sim ->
      has_type_surf dep Γ e e' τ ->
      has_type_surf w Γ (EDep e) e' τ.
