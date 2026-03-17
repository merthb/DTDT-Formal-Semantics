Require Import DTDT.syntax.
Require Import DTDT.machine_inter.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.semantic_rules_surf.

(* Type-directed translation from surface syntax to internal syntax. *)

(* Translation mode: simple or dependent. *)
Inductive mode : Type :=
  | sim : mode
  | dep : mode.

(* Internal encoding of dynamic references.
   Paper form: ⟦τ dref⟧ = (unit → ⟦τ⟧) × (⟦τ⟧ → unit). *)
Definition dref_encoding (τ : i_ty) : i_ty :=
  TProd (TArr (TBase BUnit) τ) (TArr τ (TBase BUnit)).

(* Read through the encoded dynamic-reference interface. *)
Definition dget (e : i_expr) : i_expr :=
  EApp (EFst e) (EUnit tt).

(* Write through the encoded dynamic-reference interface. *)
Definition dset (e1 e2 : i_expr) : i_expr :=
  EApp (ESnd e1) e2.

(* Package an ordinary reference as an encoded dynamic reference. *)
Definition pack_dref (τ : i_ty) (e : i_expr) : i_expr :=
  let u := fresh_string_list (exp_vars e) in
  let x := fresh_string_list (u :: exp_vars e) in
  EPair
    (EFix "" u (TBase BUnit) τ (EGet e))
    (EFix "" x τ (TBase BUnit) (ESet e (EVar x))).

(* Translation of surface types and the dref-free fragment of expressions.
   Paper forms: ⟦τ⟧ for type translation and ⟦Γ⟧c for context translation. *)

Fixpoint trans_type (τ : ty) : i_ty :=
  match τ with
  | TyBase b => TBase b
  | TySet v b e => TSet v b (match trans_expr_partial e with | Some e => e | None => EFail end)
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
  | ExFix f x τ₁ τ₂ e =>
      match trans_expr_partial e with
      | Some e' => Some (EFix f x (trans_type τ₁) (trans_type τ₂) e')
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
  | ExFst e =>
      match trans_expr_partial e with
      | Some e' => Some (EFst e')
      | None => None
      end
  | ExSnd e =>
      match trans_expr_partial e with
      | Some e' => Some (ESnd e')
      | None => None
      end
  | ExIf e1 e2 e3 =>
      match trans_expr_partial e1, trans_expr_partial e2, trans_expr_partial e3 with
      | Some e1', Some e2', Some e3' => Some (EIf e1' e2' e3')
      | _, _, _ => None
      end
  | ExNot e =>
      match trans_expr_partial e with
      | Some e' => Some (ENot e')
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
  | ExNewRef τ e =>
      match trans_expr_partial e with
      | Some e' => Some (ENewRef (trans_type τ) e')
      | None => None
      end
  | ExGet e =>
      match trans_expr_partial e with
      | Some e' => Some (EGet e')
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
  | EAssert e _ => trans_expr_partial e
  | ESimple e => trans_expr_partial e
  | EDep e => trans_expr_partial e
  end
.

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

(* ------------------------------------------------------------------------- *)
(* Erase dependency occurrences of a variable `x` from an internal type      *)
(* (implements the paper's `[[ ? ]] x` operation)                         *)
(* ------------------------------------------------------------------------- *)

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
  | EFix f x t1 t2 body =>
      free_ty_vars t1 ++ remove_string f (remove_string x (free_ty_vars t2 ++ free_exp_vars body))
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
with free_ty_vars (τ : i_ty) : list string :=
  match τ with
  | TBase _ => []
  | TSet x _ pred => remove_string x (free_exp_vars pred)
  | TArr t1 t2 => free_ty_vars t1 ++ free_ty_vars t2
  | TArrDep x t1 t2 => free_ty_vars t1 ++ remove_string x (free_ty_vars t2)
  | TProd t1 t2 => free_ty_vars t1 ++ free_ty_vars t2
  | TRef t0 => free_ty_vars t0
  end.

(* Erase the dependency on a distinguished variable from an internal type. *)
Fixpoint erase_dep_var (x : string) (τ : i_ty) : i_ty :=
  match τ with
  | TBase b => TBase b
  | TSet y b pred => if String.eqb x y then TSet y b pred else
                      if existsb (String.eqb x) (free_exp_vars pred) then TBase b else TSet y b pred
  | TArr t1 t2 => TArr (erase_dep_var x t1) (erase_dep_var x t2)
  | TArrDep y t1 t2 => TArr (erase_dep_var x t1) (erase_dep_var x t2)
  | TProd t1 t2 => TProd (erase_dep_var x t1) (erase_dep_var x t2)
  | TRef τ =>
      if existsb (String.eqb x) (free_ty_vars τ)
      then dref_encoding (erase_dep_var x τ)
      else TRef (erase_dep_var x τ)
  end.
Notation "[[ t ]] x" := (erase_dep_var x t) (at level 1).

(* Full dependency erasure for internal types. *)

(* Compute the simple internal type used by the translation metatheory. *)
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
  | TRef τ =>
      dref_encoding (erase_i_ty τ)
  end.
Notation "[| t |]" := (erase_i_ty t) (at level 1).

(* Paper-exact admissibility predicates for source reference types.
   These implement the appendix definitions of co ref and contra ref on the
   surface language, where dynamic references remain source-only. *)
Fixpoint co_ref (τ : ty) : bool :=
  match τ with
  | TyBase _ => true
  | TySet _ _ _ => true
  | TyArr τ₁ τ₂ => contra_ref τ₁ && co_ref τ₂
  | TyArrDep _ τ₁ τ₂ => contra_ref τ₁ && co_ref τ₂
  | TyProd τ₁ τ₂ => co_ref τ₁ && co_ref τ₂
  | TyRef τ₀ => co_ref τ₀ && contra_ref τ₀
  | TyDeRef τ₀ => co_ref τ₀ && contra_ref τ₀
  end

with contra_ref (τ : ty) : bool :=
  match τ with
  | TyBase _ => true
  | TySet _ _ _ => true
  | TyArr τ₁ τ₂ => co_ref τ₁ && contra_ref τ₂
  | TyArrDep _ τ₁ τ₂ => co_ref τ₁ && contra_ref τ₂
  | TyProd τ₁ τ₂ => contra_ref τ₁ && contra_ref τ₂
  | TyRef _ => false
  | TyDeRef τ₀ => co_ref τ₀ && contra_ref τ₀
  end.

(* Internal reflection of the source admissibility predicates.
   These helpers are used by the internal coercion constructors, while the
   source-facing statements quantify over co_ref and contra_ref above. *)

(* Admissibility predicates for reference coercions.
   These boolean classifiers encode the co/contra-side conditions used by the
   reference fragment of the translation and its soundness/completeness lemmas. *)
Fixpoint co_ref_ty (τ : i_ty) : bool :=
  match τ with
  | TBase _ => true
  | TSet _ _ _ => true
  | TArr t1 t2 => contra_ref_ty t1 && co_ref_ty t2
  | TArrDep _ t1 t2 => contra_ref_ty t1 && co_ref_ty t2
  | TProd t1 t2 => co_ref_ty t1 && co_ref_ty t2
  | TRef t0 => co_ref_ty t0 && contra_ref_ty t0
  end

with contra_ref_ty (τ : i_ty) : bool :=
  match τ with
  | TBase _ => true
  | TSet _ _ _ => true
  | TArr t1 t2 => co_ref_ty t1 && contra_ref_ty t2
  | TArrDep _ t1 t2 => co_ref_ty t1 && contra_ref_ty t2
  | TProd t1 t2 => contra_ref_ty t1 && contra_ref_ty t2
  | TRef _ => false
  end.

(* ------------------------------------------------------------------------- *)
(* Type coercion judgment (internal language)                                *)
(*   coerce ω Γ Γv Φ ι e τₛ e' τₜ  represents:                               *)
(*     Γ Γv Φ ι ⊢ω e : τₛ → e' : τₜ                                          *)
(* ------------------------------------------------------------------------- *)

(* Coercion judgment generated by the translation.
   Paper form: Γ ⊢^w e : τ ↦ e' : τ'.
   A derivation constructs an internal witness e' that converts e from source type
   τ to target type τ' in mode w. *)
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
      coerce w (((Γ ,,c y ↦ (TArrDep x τ₁ τ₂, v₁)) ,,v x ↦ (τ₁', v₂)))
        (EApp (EVar y) (EVar x)) τ₂
        eᵦ                       τ₂' ->
      coerce w Γ
        e                                                                     (TArr τ₁ τ₂)
        (expr_subst y e (EFix (fresh_string_list (exp_vars eᵦ)) x τ₁' τ₂' eᵦ)) (TArr τ₁' τ₂')
  | CFunContNonDep :
    forall e eᵦ eₓ x y τ₁ τ₂ τ₁' τ₂' v₁ v₂,
      w = sim ->
      ~ subtype Γ τ₁' τ₁ ->
      coerce w (Γ ,,v x ↦ (τ₁', v₁))
        (EVar x) τ₁'
        eₓ       τ₁ ->
      coerce w (((Γ ,,c y ↦ (TArrDep x τ₁ τ₂, v₁)) ,,v x ↦ (τ₁', v₂)))
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
      coerce w (((Γ ,,c y ↦ (TArr τ₁ τ₂, v₂)) ,,v x ↦ (τ₁', v₁)))
        (EApp (EVar y) (EVar x)) τ₂
        eᵦ                       τ₂' ->
      eᵦ' = EIf e₁ eᵦ EFail ->
      coerce w Γ
        e                                                                       (TArrDep x τ₁ τ₂)
        (expr_subst y e (EFix (fresh_string_list (exp_vars eᵦ')) x τ₁' τ₂' eᵦ')) (TArrDep x τ₁' τ₂')
  | CFunEraseDep :
    forall e x τ₁ τ₂ y body vy vx,
      w = sim ->
      coerce w (((Γ ,,c y ↦ (TArrDep x τ₁ τ₂, vy)) ,,v x ↦ (τ₁, vx)))
        (EApp (EVar y) (EVar x)) τ₂
        body                     ([[ τ₂ ]] x) ->
      coerce w Γ
        e (TArrDep x τ₁ τ₂)
        (expr_subst y e (EFix (fresh_string_list (exp_vars body)) x τ₁ ([[ τ₂ ]] x) body))
        (TArr τ₁ ([[ τ₂ ]] x))
  | CPair :
    forall e τ₁ τ₂ y e₁ e₂ τ₁' τ₂' v,
      w = sim ->
      coerce w (Γ ,,v y ↦ (TProd τ₁ τ₂, v))
        (EFst (EVar y)) τ₁
        e₁              τ₁' ->
      coerce w (Γ ,,v y ↦ (TProd τ₁ τ₂, v))
        (ESnd (EVar y)) τ₂
        e₂              τ₂' ->
      coerce w Γ
        e                              (TProd τ₁ τ₂)
        (expr_subst y e (EPair e₁ e₂)) (TProd τ₁' τ₂')
  | CRefToDRef :
    forall e y u x τ τ' get_body set_arg vy vx,
      w = sim ->
      co_ref_ty (TRef τ) = true ->
      contra_ref_ty (dref_encoding τ') = true ->
      coerce w (Γ ,,v y ↦ (TRef τ, vy))
        (EGet (EVar y)) τ
        get_body        τ' ->
      coerce w (((Γ ,,v y ↦ (TRef τ, vy)) ,,v x ↦ (τ', vx)))
        (EVar x) τ'
        set_arg  τ ->
      coerce w Γ
        e (TRef τ)
        (expr_subst y e
          (EPair
            (EFix "" u (TBase BUnit) τ' get_body)
            (EFix "" x τ' (TBase BUnit) (ESet (EVar y) set_arg))))
        (dref_encoding τ')
  | CDRef :
    forall e y u x τ τ' get_body set_arg vy vx,
      w = sim ->
      co_ref_ty (dref_encoding τ) = true ->
      contra_ref_ty (dref_encoding τ') = true ->
      coerce w (Γ ,,v y ↦ (dref_encoding τ, vy))
        (dget (EVar y)) τ
        get_body        τ' ->
      coerce w (((Γ ,,v y ↦ (dref_encoding τ, vy)) ,,v x ↦ (τ', vx)))
        (EVar x) τ'
        set_arg  τ ->
      coerce w Γ
        e (dref_encoding τ)
        (expr_subst y e
          (EPair
            (EFix "" u (TBase BUnit) τ' get_body)
            (EFix "" x τ' (TBase BUnit) (dset (EVar y) set_arg))))
        (dref_encoding τ')
.

Notation "Γ ⊢[ w ] e : τ ↦ e' : τ'" := (coerce w Γ e τ e' τ')
  (at level 74, w at next level, e, τ, e', τ' at next level).
Notation "Γ ⊢sim e : τ ↦ e' : τ'" := (coerce sim Γ e τ e' τ')
  (at level 74, e, τ, e', τ' at next level).
Notation "Γ ⊢dep e : τ ↦ e' : τ'" := (coerce dep Γ e τ e' τ')
  (at level 74, e, τ, e', τ' at next level).

(* Binary meet and join operations used in conditional translation. *)

(* Meet judgment for internal types.
   Paper-style reading: Γ ⊢ τ₁ ⊓ τ₂ ⇒ τ₃.
   This judgment computes the greatest common result type used for conditional
   translation when control flow merges compatible branches. *)
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
      ty_meet (Γ ,,v x ↦ (τ1, v)) τ2 τ2' cod ->
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

(* Join judgment for internal types.
   Paper-style reading: Γ ⊢ τ₁ ⊔ τ₂ ⇒ τ₃.
   This judgment computes the least common supertype used to reconcile branch
   results in the translated internal language. *)
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
      ty_join (Γ ,,v x ↦ (dom, v)) τ2 τ2' cod ->
      ty_join Γ (TArrDep x τ1 τ2) (TArrDep x τ1' τ2') (TArrDep x dom cod)
  | JoinProd :
    forall τ1 τ1' τ2 τ2' j1 j2,
      ty_join Γ τ1 τ1' j1 ->
      ty_join Γ τ2 τ2' j2 ->
      ty_join Γ (TProd τ1 τ2) (TProd τ1' τ2') (TProd j1 j2)
  | JoinRef :
    forall τ τ' j,
      ty_join Γ τ τ' j ->
      ty_join Γ (TRef τ) (TRef τ') (TRef [| j |]) .

Notation "Γ ⊢ τ₁ ⊓ τ₂ ⇒ τ₃" := (ty_meet Γ τ₁ τ₂ τ₃)
  (at level 74, τ₁, τ₂, τ₃ at next level).
Notation "Γ ⊢ τ₁ ⊔ τ₂ ⇒ τ₃" := (ty_join Γ τ₁ τ₂ τ₃)
  (at level 74, τ₁, τ₂, τ₃ at next level).

(* ------------------------------------------------------------------------- *)
(* Surface language typing & translation judgment                            *)
(*   has_type_surf w Γ Φ e e0 τ  corresponds to  ⊢^w e ; e0 : τ              *)
(* ------------------------------------------------------------------------- *)

(* Surface typing together with its translated internal witness.
   Paper form: Γ ⊢^w e ; e' : τ.
   A derivation simultaneously assigns the source term e a translated internal term
   e' and an internal target type τ in mode w. *)
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
      has_type_surf w (((Γ ,,sc f ↦ (TyArrDep x τ₁ τ₂, v₂)) ,,sv x ↦ (τ₁, v₁))) e e₁ τ₂' ->
      coerce w ⟦ ((Γ ,,sc f ↦ (TyArrDep x τ₁ τ₂, v₂)) ,,sv x ↦ (τ₁, v₁)) ⟧c
        e₁ τ₂'
        e₂ (trans_type τ₂) ->
      has_type_surf w Γ (ExFix f x τ₁ τ₂ e)
                    (EFix f x (trans_type τ₁) (trans_type τ₂) e₂)
                    (TArrDep x (trans_type τ₁) (trans_type τ₂))
  | ATAppPure :
    forall e₁ e₂ e₁' e₂' e₂'' x τ₁ τ₂ τ₁',
      has_type_surf w Γ e₁ e₁' (TArrDep x τ₁ τ₂) ->
      has_type_surf w Γ e₂ e₂' τ₁' ->
      coerce w ⟦ Γ ⟧c
        e₂' τ₁'
        e₂'' τ₁ ->
      (forall τ, has_type_pure ⟦ Γ ⟧c e₂'' τ) ->
      has_type_surf w Γ (ExApp e₁ e₂) (EApp e₁' e₂'') (ty_subst x e₂'' τ₂)
  | ATAppImPure :
    forall e₁ e₂ e₁' e₁'' e₂' e₂'' x τ₁ τ₂ τ₁',
      has_type_surf w Γ e₁ e₁' (TArrDep x τ₁ τ₂) ->
      has_type_surf w Γ e₂ e₂' τ₁' ->
      coerce w ⟦ Γ ⟧c
        e₂' τ₁'
        e₂'' τ₁ ->
      ~ (forall τ, has_type_pure ⟦ Γ ⟧c e₂'' τ) ->
      coerce w ⟦ Γ ⟧c
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
  | ATNewRef :
    forall e e' e'' τ τ',
      ty_valid_surf Γ (TyRef τ) ->
      has_type_surf w Γ e e' τ' ->
      coerce w ⟦ Γ ⟧c
        e' τ'
        e'' (trans_type τ) ->
      has_type_surf w Γ (ExNewRef τ e) (ENewRef (trans_type τ) e'') (TRef (trans_type τ))
  | ATGet :
    forall e e' τ,
      has_type_surf w Γ e e' (TRef τ) ->
      has_type_surf w Γ (ExGet e) (EGet e') τ
  | ATSet :
    forall e1 e2 e1' e2' e2'' τ τ',
      has_type_surf w Γ e1 e1' (TRef τ) ->
      has_type_surf w Γ e2 e2' τ' ->
      coerce w ⟦ Γ ⟧c
        e2' τ'
        e2'' τ ->
      has_type_surf w Γ (ExSet e1 e2) (ESet e1' e2'') (TBase BUnit)
  | ATDeRef :
    forall e e₁ e₂ τ,
      co_ref (TyRef τ) = true ->
      contra_ref (TyDeRef τ) = true ->
      has_type_surf w Γ e e₁ (TRef (trans_type τ)) ->
      coerce sim ⟦ Γ ⟧c
        e₁ (TRef (trans_type τ))
        e₂ (trans_type (TyDeRef τ)) ->
      has_type_surf w Γ (ExDeRef e) e₂ (trans_type (TyDeRef τ))
  | ATGetDep :
    forall e e' τ,
      has_type_surf w Γ e e' (trans_type (TyDeRef τ)) ->
      has_type_surf w Γ (ExGetDep e) (dget e') (trans_type τ)
  | ATSetDep :
    forall e1 e2 e1' e2' e2'' τ τ',
      has_type_surf w Γ e1 e1' (trans_type (TyDeRef τ)) ->
      has_type_surf w Γ e2 e2' τ' ->
      coerce w ⟦ Γ ⟧c
        e2' τ'
        e2'' (trans_type τ) ->
      has_type_surf w Γ (ExSetDep e1 e2) (dset e1' e2'') (TBase BUnit)
  | ATIfPure :
    forall e e₁ e₂ e₁' e₁'' e₂' e₂'' τ₁ τ₂ τ₃ u,
      has_type_pure_surf Γ e (TyBase BBool) ->
      has_type_surf w (Γ ,,sv u ↦ (TyBase BBool, e)) e₁ e₁' τ₁ ->
      has_type_surf w (Γ ,,sv u ↦ (TyBase BBool, ExNot e)) e₂ e₂' τ₂ ->
      coerce w ⟦ (Γ ,,sv u ↦ (TyBase BBool, e)) ⟧c
        e₁' τ₁
        e₁'' τ₃ ->
      coerce w ⟦ (Γ ,,sv u ↦ (TyBase BBool, ExNot e)) ⟧c
        e₂' τ₂
        e₂'' τ₃ ->
      ty_join ⟦ Γ ⟧c τ₁ τ₂ τ₃ ->
      has_type_surf w Γ (ExIf e e₁ e₂) (EIf (trans_expr_dref_free e) e₁'' e₂'') τ₃
  | ATIfImPure :
    forall e e₁ e₂ e' x τ,
      ~ (forall τ', has_type_pure_surf Γ e τ') ->
      has_type_surf w Γ (expr_subst_surf x e (ExIf (ExVar x) e₁ e₂)) e' τ ->
      has_type_surf w Γ (ExIf e e₁ e₂) e' τ
  | ATAssert :
    forall e e' e'' τ τ',
      w = dep ->
      has_type_surf w Γ e e' τ' ->
      ty_valid ⟦ Γ ⟧c (trans_type τ) ->
      coerce sim ⟦ Γ ⟧c
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

Notation "Γ ⊢[ w ] e ; e' : τ" := (has_type_surf w Γ e e' τ)
  (at level 74, w at next level, e, e', τ at next level).
Notation "Γ ⊢sim e ; e' : τ" := (has_type_surf sim Γ e e' τ)
  (at level 74, e, e', τ at next level).
Notation "Γ ⊢dep e ; e' : τ" := (has_type_surf dep Γ e e' τ)
  (at level 74, e, e', τ at next level).
