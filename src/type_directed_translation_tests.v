Require Import DTDT.syntax.
Require Import DTDT.machine_inter.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.semantic_rules_surf.
Require Import DTDT.type_directed_translation.

(* Example derivations for translation, coercion, and translated typing. *)

Definition surf_newref_nat_expr : expr :=
  ExNewRef (TyBase BNat) (ExNat 5).

Definition inter_newref_nat_expr : i_expr :=
  ENewRef (TBase BNat) (ENat 5).

Definition inter_dref_nat_expr : i_expr :=
  expr_subst "y" inter_newref_nat_expr
    (EPair
      (EFix "" "u" (TBase BUnit) (TBase BNat) (EGet (EVar "y")))
      (EFix "" "x" (TBase BNat) (TBase BUnit) (ESet (EVar "y") (EVar "x")))).
Definition surf_dref_if_nat_expr : expr :=
  ExIf (ExBool true)
       (ExGetDep (ExDeRef surf_newref_nat_expr))
       (ExNat 0).

Definition inter_dref_if_nat_expr : i_expr :=
  EIf (EBool true) (dget inter_dref_nat_expr) (ENat 0).

Definition surf_dref_set_if_unit_expr : expr :=
  ExIf (ExBool true)
       (ExSetDep (ExDeRef surf_newref_nat_expr) (ExNat 7))
       (ExUnit tt).

Definition inter_dref_set_if_unit_expr : i_expr :=
  EIf (EBool true) (dset inter_dref_nat_expr (ENat 7)) (EUnit tt).

Definition surf_const_dep_fun_nat_expr : expr :=
  ExFix "f" "x" (TyBase BNat) (TyBase BNat) (ExNat 0).

Definition surf_impure_app_ctx : ctx_surf :=
  ((empty_ctx_surf ,,sv "f" ↦
      ((TyArrDep "x" (TyBase BNat) (TyBase BNat)), surf_const_dep_fun_nat_expr))
    ,,sv "r" ↦ (TyRef (TyBase BNat), ExVar "r")).

Definition erased_dep_fun_var_term : i_expr :=
  expr_subst "y" (EVar "f")
    (EFix (fresh_string_list (exp_vars (EApp (EVar "y") (EVar "x"))))
      "x" (TBase BNat) (TBase BNat) (EApp (EVar "y") (EVar "x"))).

(* Example coercion from an ordinary reference to an encoded dynamic reference. *)
Lemma coerce_newref_nat_to_dref_example : forall Γ,
  coerce sim Γ
    inter_newref_nat_expr (TRef (TBase BNat))
    inter_dref_nat_expr (dref_encoding (TBase BNat)).
Proof.
  intro Γ.
  unfold inter_dref_nat_expr, inter_newref_nat_expr.
  eapply CRefToDRef with
    (y := "y")
    (u := "u")
    (x := "x")
    (get_body := EGet (EVar "y"))
    (set_arg := EVar "x")
    (vy := EUnit tt)
    (vx := ENat 0).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply CSub. apply SBase.
  - apply CSub. apply SBase.
Qed.

(* Example translation of dynamic-reference introduction. *)
Lemma has_type_surf_deref_nat_example : forall Γ,
  has_type_surf sim Γ
    (ExDeRef surf_newref_nat_expr)
    inter_dref_nat_expr
    (dref_encoding (TBase BNat)).
Proof.
  intro Γ.
  eapply (@ATDeRef sim _ surf_newref_nat_expr inter_newref_nat_expr inter_dref_nat_expr (TyBase BNat)).
  - reflexivity.
  - reflexivity.
  - unfold surf_newref_nat_expr, inter_newref_nat_expr.
    eapply ATNewRef with (e' := ENat 5) (e'' := ENat 5).
    + apply VRefS. apply VBaseS.
    + apply ATNat.
    + apply CSub. apply SBase.
  - apply coerce_newref_nat_to_dref_example.
Qed.

(* Example translation derivation for a conditional that reads through a dynamic reference. *)
Lemma has_type_surf_dref_if_nat_test :
  has_type_surf sim empty_ctx_surf
    surf_dref_if_nat_expr
    inter_dref_if_nat_expr
    (TBase BNat).
Proof.
  unfold surf_dref_if_nat_expr, inter_dref_if_nat_expr.
  simple eapply (@ATIfPure sim empty_ctx_surf
    (ExBool true)
    (ExGetDep (ExDeRef surf_newref_nat_expr))
    (ExNat 0)
    (dget inter_dref_nat_expr) (dget inter_dref_nat_expr)
    (ENat 0) (ENat 0)
    (TBase BNat) (TBase BNat) (TBase BNat) "u").
  - apply PBoolS.
  - eapply ATGetDep with (e' := inter_dref_nat_expr) (τ := TyBase BNat).
    apply has_type_surf_deref_nat_example.
  - apply ATNat.
  - apply CSub. apply SBase.
  - apply CSub. apply SBase.
  - apply JoinBase.
Qed.

(* Example translation derivation for a conditional that writes through a dynamic reference. *)
Lemma has_type_surf_dref_set_if_unit_test :
  has_type_surf sim empty_ctx_surf
    surf_dref_set_if_unit_expr
    inter_dref_set_if_unit_expr
    (TBase BUnit).
Proof.
  unfold surf_dref_set_if_unit_expr, inter_dref_set_if_unit_expr.
  simple eapply (@ATIfPure sim empty_ctx_surf
    (ExBool true)
    (ExSetDep (ExDeRef surf_newref_nat_expr) (ExNat 7))
    (ExUnit tt)
    (dset inter_dref_nat_expr (ENat 7)) (dset inter_dref_nat_expr (ENat 7))
    (EUnit tt) (EUnit tt)
    (TBase BUnit) (TBase BUnit) (TBase BUnit) "u").
  - apply PBoolS.
  - eapply ATSetDep with
      (e1' := inter_dref_nat_expr)
      (e2' := ENat 7)
      (e2'' := ENat 7)
      (τ := TyBase BNat)
      (τ' := TBase BNat).
    + apply has_type_surf_deref_nat_example.
    + apply ATNat.
    + apply CSub. apply SBase.
  - apply ATUnit.
  - apply CSub. apply SBase.
  - apply CSub. apply SBase.
  - apply JoinBase.
Qed.

(* Example translation derivation for impure application through function erasure. *)
Lemma has_type_surf_app_impure_nat_test :
  has_type_surf sim surf_impure_app_ctx
    (ExApp (ExVar "f") (ExGet (ExVar "r")))
    (EApp erased_dep_fun_var_term (EGet (EVar "r")))
    (TBase BNat).
Proof.
  simple eapply (@ATAppImPure sim surf_impure_app_ctx
    (ExVar "f") (ExGet (ExVar "r"))
    (EVar "f") erased_dep_fun_var_term
    (EGet (EVar "r")) (EGet (EVar "r"))
    "x" (TBase BNat) (TBase BNat) (TBase BNat)).
  - simple eapply (@ATVar sim surf_impure_app_ctx "f"
      (TyArrDep "x" (TyBase BNat) (TyBase BNat)) surf_const_dep_fun_nat_expr).
    + unfold surf_impure_app_ctx, var_ctx_lookup_surf, ctx_add_var_surf. compute. reflexivity.
    + intro H.
      inversion H; subst.
      destruct τb; simpl in *; try contradiction; discriminate.
  - simple eapply (@ATGet sim surf_impure_app_ctx (ExVar "r") (EVar "r") (TBase BNat)).
    simple eapply (@ATVar sim surf_impure_app_ctx "r" (TyRef (TyBase BNat)) (ExVar "r")).
    + unfold surf_impure_app_ctx, var_ctx_lookup_surf, ctx_add_var_surf. compute. reflexivity.
    + intro H.
      inversion H; subst.
      destruct τb; simpl in *; try contradiction; discriminate.
  - apply CSub. apply SBase.
  - intro Hpure.
    specialize (Hpure (TBase BNat)).
    inversion Hpure.
  - unfold erased_dep_fun_var_term.
    eapply CFunEraseDep with
      (y := "y")
      (body := EApp (EVar "y") (EVar "x"))
      (vy := ENat 0)
      (vx := ENat 0).
    + reflexivity.
    + apply CSub. apply SBase.
Qed.
