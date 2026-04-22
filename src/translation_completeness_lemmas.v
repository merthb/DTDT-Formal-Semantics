Require Import Coq.Program.Equality.
Require Import DTDT.syntax.
Require Import DTDT.machine_inter.
Require Import DTDT.semantic_rules_inter.
Require Import DTDT.semantic_rules_surf.
Require Import DTDT.type_directed_translation.
Require Import DTDT.foundational_lemmas_inter.
Require Import DTDT.translation_soundness_lemmas.

(* ==================== PAPER LEMMA 14 ====================
   Simple-type erasure is preserved by translated subtyping and coercions. *)
Lemma simple_type_match_subtype :
  forall Gamma tau1 tau2,
    subtype (trans_ctx_surf Gamma) (trans_type tau1) (trans_type tau2) ->
    [| trans_type tau1 |] = [| trans_type tau2 |].
Proof.
  intros Gamma tau1 tau2 Hsub.
  induction Hsub; simpl; try reflexivity.
  - rewrite IHHsub1, IHHsub2. reflexivity.
  - rewrite IHHsub1, IHHsub2. reflexivity.
  - rewrite IHHsub1, IHHsub2. reflexivity.
  - rewrite IHHsub1, IHHsub2. reflexivity.
Qed.

Lemma simple_type_match_coercion :
  forall w Gamma e tau e'' tau'',
    coerce w (trans_ctx_surf Gamma) e (trans_type tau) e'' (trans_type tau'') ->
    [| trans_type tau |] = [| trans_type tau'' |].
Proof.
  intros w Gamma e tau e'' tau'' Hco.
  induction Hco; simpl; try eauto.
  - exact (subtype_type_match_helper _ _ _ H).
  - destruct H0 as [Htau | Htau]; rewrite Htau; reflexivity.
  - rewrite IHHco.
    rewrite (subtype_type_match_helper _ _ _ H0).
    reflexivity.
  - rewrite IHHco1, IHHco2. reflexivity.
  - destruct H2 as [Htau | Htau]; rewrite H1, Htau, IHHco; simpl; reflexivity.
  - rewrite IHHco. reflexivity.
  - rewrite IHHco1, IHHco2. reflexivity.
  - rewrite IHHco1. unfold dref_encoding. reflexivity.
  - rewrite IHHco1. reflexivity.
Qed.

(* Reference-specialized helper used in the reference fragment of Lemma 15. *)
Lemma simple_type_match_ref :
  forall Gamma tau1 tau2,
    subtype (trans_ctx_surf Gamma) (TRef (trans_type tau1)) (TRef (trans_type tau2)) ->
    TRef [| trans_type tau1 |] = TRef [| trans_type tau2 |].
Proof.
  intros Gamma tau1 tau2 Hsub.
  inversion Hsub; subst; try discriminate.
  match goal with
  | Hleft : subtype (trans_ctx_surf Gamma) (trans_type tau1) (trans_type tau2),
    Hright : subtype (trans_ctx_surf Gamma) (trans_type tau2) (trans_type tau1) |- _ =>
      rewrite (simple_type_match_subtype Gamma tau1 tau2 Hleft);
      rewrite (simple_type_match_subtype Gamma tau2 tau1 Hright);
      reflexivity
  end.
Qed.

(* Surface-level context admissibility predicates corresponding to the paper's
   co_ref(Gamma) and co_ref(F) side conditions. *)
Definition co_ref_vars_surf (Gamma : ctx_surf) : Prop :=
  forall x tau v,
    var_ctx_lookup_surf Gamma x = Some (tau, v) ->
    co_ref tau = true.

Definition co_ref_consts_surf (Gamma : ctx_surf) : Prop :=
  forall c tau v,
    const_ctx_lookup_surf Gamma c = Some (tau, v) ->
    co_ref tau = true.

(* Appendix B.4 introduces a simple source-language type grammar
     tau ::= base | tau -> tau | tau x tau | tau dref
   together with the judgment Gamma |-0 e : tau.
   We reuse the existing surface syntax and represent simple-source types as the
   corresponding subset of [ty]. *)
Inductive simple_surface_type : ty -> Prop :=
  | SSTBase :
      forall b,
        simple_surface_type (TyBase b)
  | SSTArr :
      forall tau1 tau2,
        simple_surface_type tau1 ->
        simple_surface_type tau2 ->
        simple_surface_type (TyArr tau1 tau2)
  | SSTProd :
      forall tau1 tau2,
        simple_surface_type tau1 ->
        simple_surface_type tau2 ->
        simple_surface_type (TyProd tau1 tau2)
  | SSTDRef :
      forall tau,
        simple_surface_type tau ->
        simple_surface_type (TyDeRef tau).

(* Source-side simple-type erasure matching the paper's [tau] operation. *)
Fixpoint erase_simple_surf_ty (tau : ty) : ty :=
  match tau with
  | TyBase b => TyBase b
  | TySet _ b _ => TyBase b
  | TyArr t1 t2 => TyArr (erase_simple_surf_ty t1) (erase_simple_surf_ty t2)
  | TyArrDep _ t1 t2 => TyArr (erase_simple_surf_ty t1) (erase_simple_surf_ty t2)
  | TyProd t1 t2 => TyProd (erase_simple_surf_ty t1) (erase_simple_surf_ty t2)
  | TyRef t => TyDeRef (erase_simple_surf_ty t)
  | TyDeRef t => TyDeRef (erase_simple_surf_ty t)
  end.

Lemma erase_simple_surf_ty_is_simple :
  forall tau,
    simple_surface_type (erase_simple_surf_ty tau).
Proof.
  induction tau; simpl.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma erase_simple_surf_ty_id :
  forall tau,
    simple_surface_type tau ->
    erase_simple_surf_ty tau = tau.
Proof.
  intros tau Hsimple.
  induction Hsimple; simpl; try rewrite IHHsimple1; try rewrite IHHsimple2; try rewrite IHHsimple; reflexivity.
Qed.

Lemma simple_surface_type_no_free_ty_vars :
  forall tau,
    simple_surface_type tau ->
    free_ty_vars_surf tau = [].
Proof.
  intros tau Hsimple.
  induction Hsimple; simpl; try rewrite IHHsimple1; try rewrite IHHsimple2; try rewrite IHHsimple; reflexivity.
Qed.

Lemma simple_surface_type_valid_surf :
  forall Gamma tau,
    simple_surface_type tau ->
    ty_valid_surf Gamma tau.
Proof.
  intros Gamma tau Hsimple.
  induction Hsimple.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma trans_type_erase_simple_surf_ty :
  forall tau,
    trans_type (erase_simple_surf_ty tau) = erase_i_ty (trans_type tau).
Proof.
  induction tau; simpl; try reflexivity.
  - rewrite IHtau1, IHtau2. reflexivity.
  - rewrite IHtau1, IHtau2. reflexivity.
  - rewrite IHtau1, IHtau2. reflexivity.
  - rewrite IHtau. reflexivity.
  - rewrite IHtau. reflexivity.
Qed.

Lemma simple_surface_type_co_ref_contra_ref :
  forall tau,
    simple_surface_type tau ->
    co_ref tau = true /\ contra_ref tau = true.
Proof.
  intros tau Hsimple.
  induction Hsimple.
  - split; reflexivity.
  - destruct IHHsimple1 as [Hco1 Hcontra1].
    destruct IHHsimple2 as [Hco2 Hcontra2].
    split.
    + simpl. rewrite Hcontra1, Hco2. reflexivity.
    + simpl. rewrite Hco1, Hcontra2. reflexivity.
  - destruct IHHsimple1 as [Hco1 Hcontra1].
    destruct IHHsimple2 as [Hco2 Hcontra2].
    split.
    + simpl. rewrite Hco1, Hco2. reflexivity.
    + simpl. rewrite Hcontra1, Hcontra2. reflexivity.
  - destruct IHHsimple as [Hco Hcontra].
    split; simpl; rewrite Hco, Hcontra; reflexivity.
Qed.

Lemma simple_surface_type_co_ref_true :
  forall tau,
    simple_surface_type tau ->
    co_ref tau = true.
Proof.
  intros tau Hsimple.
  exact (proj1 (simple_surface_type_co_ref_contra_ref tau Hsimple)).
Qed.

Lemma simple_surface_type_contra_ref_true :
  forall tau,
    simple_surface_type tau ->
    contra_ref tau = true.
Proof.
  intros tau Hsimple.
  exact (proj2 (simple_surface_type_co_ref_contra_ref tau Hsimple)).
Qed.

Lemma simple_surface_type_trans_type_fixed :
  forall tau,
    simple_surface_type tau ->
    erase_i_ty (trans_type tau) = trans_type tau.
Proof.
  intros tau Hsimple.
  induction Hsimple; simpl; try rewrite IHHsimple1; try rewrite IHHsimple2; try rewrite IHHsimple; reflexivity.
Qed.

Lemma erase_i_ty_self_with :
  forall u tau e,
    erase_i_ty (self_with u tau e) = erase_i_ty tau.
Proof.
  intros u tau.
  induction tau; intros e; simpl; try reflexivity.
  - destruct tau1; simpl; try reflexivity.
    rewrite IHtau2. reflexivity.
Qed.

Lemma erase_i_ty_self :
  forall tau e,
    erase_i_ty (self tau e) = erase_i_ty tau.
Proof.
  intros tau e.
  unfold self.
  apply erase_i_ty_self_with.
Qed.

Lemma erase_i_ty_ty_subst :
  forall x e tau,
    erase_i_ty (ty_subst x e tau) = erase_i_ty tau.
Proof.
  intros x e tau.
  induction tau; simpl; try reflexivity.
  - destruct (String.eqb x s); reflexivity.
  - rewrite IHtau1, IHtau2. reflexivity.
  - destruct (String.eqb x s).
    + simpl. rewrite IHtau1. reflexivity.
    + simpl. rewrite IHtau1, IHtau2. reflexivity.
  - rewrite IHtau1, IHtau2. reflexivity.
  - rewrite IHtau. reflexivity.
Qed.

Lemma erase_i_ty_erase_dep_var :
  forall x tau,
    erase_i_ty (erase_dep_var x tau) = erase_i_ty tau.
Proof.
  intros x tau.
  induction tau; simpl; try reflexivity.
  - destruct (String.eqb x s); simpl; try reflexivity.
    destruct (existsb (String.eqb x) (free_exp_vars i)); reflexivity.
  - rewrite IHtau1, IHtau2. reflexivity.
  - destruct (String.eqb x s); simpl; rewrite ?IHtau1, ?IHtau2; reflexivity.
  - rewrite IHtau1, IHtau2. reflexivity.
  - destruct (existsb (String.eqb x) (free_ty_vars tau)); simpl; rewrite IHtau; reflexivity.
Qed.

Lemma erase_i_ty_idempotent :
  forall tau,
    erase_i_ty (erase_i_ty tau) = erase_i_ty tau.
Proof.
  induction tau; simpl; try reflexivity.
  - rewrite IHtau1, IHtau2. reflexivity.
  - rewrite IHtau1, IHtau2. reflexivity.
  - rewrite IHtau1, IHtau2. reflexivity.
  - rewrite IHtau. reflexivity.
Qed.

Lemma ty_meet_preserves_erase :
  forall Gamma tau1 tau2 tau3,
    ty_meet Gamma tau1 tau2 tau3 ->
    erase_i_ty tau1 = erase_i_ty tau3 /\ erase_i_ty tau2 = erase_i_ty tau3
with ty_join_preserves_erase :
  forall Gamma tau1 tau2 tau3,
    ty_join Gamma tau1 tau2 tau3 ->
    erase_i_ty tau1 = erase_i_ty tau3 /\ erase_i_ty tau2 = erase_i_ty tau3.
Proof.
  - intros Gamma tau1 tau2 tau3 Hmeet.
    destruct Hmeet as
      [b
      | x b e1 e2
      | x b e
      | x b e
      | a a' b b' dom cod Hjoin Hmeet
      | x a a' b b' dom cod v Hjoin Hmeet
      | a a' b b' m1 m2 Hmeet1 Hmeet2
      | a a' m Hmeet].
    + split; reflexivity.
    + split; reflexivity.
    + split; reflexivity.
    + split; reflexivity.
    + destruct (ty_join_preserves_erase _ _ _ _ Hjoin) as [Hdom1 Hdom2].
      destruct (ty_meet_preserves_erase _ _ _ _ Hmeet) as [Hcod1 Hcod2].
      split.
      * simpl. rewrite Hdom1, Hcod1. reflexivity.
      * simpl. rewrite Hdom2, Hcod2. reflexivity.
    + destruct (ty_join_preserves_erase _ _ _ _ Hjoin) as [Hdom1 Hdom2].
      destruct (ty_meet_preserves_erase _ _ _ _ Hmeet) as [Hcod1 Hcod2].
      split.
      * simpl. rewrite Hdom1, Hcod1. reflexivity.
      * simpl. rewrite Hdom2, Hcod2. reflexivity.
    + destruct (ty_meet_preserves_erase _ _ _ _ Hmeet1) as [Hm1a Hm1b].
      destruct (ty_meet_preserves_erase _ _ _ _ Hmeet2) as [Hm2a Hm2b].
      split.
      * simpl. rewrite Hm1a, Hm2a. reflexivity.
      * simpl. rewrite Hm1b, Hm2b. reflexivity.
    + destruct (ty_meet_preserves_erase _ _ _ _ Hmeet) as [Hm1 Hm2].
      split.
      * simpl. rewrite Hm1. reflexivity.
      * simpl. rewrite Hm2. reflexivity.
  - intros Gamma tau1 tau2 tau3 Hjoin.
    destruct Hjoin as
      [b
      | x b e1 e2
      | x b e
      | x b e
      | a a' b b' dom cod Hmeet Hjoin
      | x a a' b b' dom cod v Hmeet Hjoin
      | a a' b b' j1 j2 Hjoin1 Hjoin2
      | a a' j Hjoin].
    + split; reflexivity.
    + split; reflexivity.
    + split; reflexivity.
    + split; reflexivity.
    + destruct (ty_meet_preserves_erase _ _ _ _ Hmeet) as [Hdom1 Hdom2].
      destruct (ty_join_preserves_erase _ _ _ _ Hjoin) as [Hcod1 Hcod2].
      split.
      * simpl. rewrite Hdom1, Hcod1. reflexivity.
      * simpl. rewrite Hdom2, Hcod2. reflexivity.
    + destruct (ty_meet_preserves_erase _ _ _ _ Hmeet) as [Hdom1 Hdom2].
      destruct (ty_join_preserves_erase _ _ _ _ Hjoin) as [Hcod1 Hcod2].
      split.
      * simpl. rewrite Hdom1, Hcod1. reflexivity.
      * simpl. rewrite Hdom2, Hcod2. reflexivity.
    + destruct (ty_join_preserves_erase _ _ _ _ Hjoin1) as [Hj1a Hj1b].
      destruct (ty_join_preserves_erase _ _ _ _ Hjoin2) as [Hj2a Hj2b].
      split.
      * simpl. rewrite Hj1a, Hj2a. reflexivity.
      * simpl. rewrite Hj1b, Hj2b. reflexivity.
    + destruct (ty_join_preserves_erase _ _ _ _ Hjoin) as [Hj1 Hj2].
      split.
      * simpl. rewrite Hj1, erase_i_ty_idempotent. reflexivity.
      * simpl. rewrite Hj2, erase_i_ty_idempotent. reflexivity.
Qed.

(* Paper Appendix B.4 simple-source typing relation.
   The repository's surface syntax also contains literals and arithmetic, so we
   include the obvious base cases for those forms in addition to the rules shown
   explicitly in the PDF. *)
Inductive has_type_simple_surf (Gamma : ctx_surf) : expr -> ty -> Prop :=
  | SConstS :
      forall c tau v,
        const_ctx_lookup_surf Gamma c = Some (tau, v) ->
        has_type_simple_surf Gamma (ExConst c) (erase_simple_surf_ty tau)
  | SVarS :
      forall x tau v,
        var_ctx_lookup_surf Gamma x = Some (tau, v) ->
        has_type_simple_surf Gamma (ExVar x) (erase_simple_surf_ty tau)
  | SNatS :
      forall n,
        has_type_simple_surf Gamma (ExNat n) (TyBase BNat)
  | SBoolS :
      forall b,
        has_type_simple_surf Gamma (ExBool b) (TyBase BBool)
  | SStringS :
      forall s,
        has_type_simple_surf Gamma (ExString s) (TyBase BString)
  | SUnitS :
      forall u,
        has_type_simple_surf Gamma (ExUnit u) (TyBase BUnit)
  | SFunS :
      forall f x tau1 tau2 e,
        simple_surface_type tau1 ->
        simple_surface_type tau2 ->
        ty_valid_surf Gamma (TyArr tau1 tau2) ->
        has_type_simple_surf (ctx_add_var_surf (ctx_add_const_surf Gamma f (TyArr tau1 tau2) (ExVar f)) x tau1 (ExVar x)) e tau2 ->
        has_type_simple_surf Gamma (ExFix f x tau1 tau2 e) (TyArr tau1 tau2)
  | SAppS :
      forall e1 e2 tau1 tau2,
        has_type_simple_surf Gamma e1 (TyArr tau1 tau2) ->
        has_type_simple_surf Gamma e2 tau1 ->
        has_type_simple_surf Gamma (ExApp e1 e2) tau2
  | SProdS :
      forall e1 e2 tau1 tau2,
        has_type_simple_surf Gamma e1 tau1 ->
        has_type_simple_surf Gamma e2 tau2 ->
        has_type_simple_surf Gamma (ExPair e1 e2) (TyProd tau1 tau2)
  | SProjLS :
      forall e tau1 tau2,
        has_type_simple_surf Gamma e (TyProd tau1 tau2) ->
        has_type_simple_surf Gamma (ExFst e) tau1
  | SProjRS :
      forall e tau1 tau2,
        has_type_simple_surf Gamma e (TyProd tau1 tau2) ->
        has_type_simple_surf Gamma (ExSnd e) tau2
  | SIfS :
      forall e e1 e2 tau,
        has_type_pure_surf Gamma e (TyBase BBool) ->
        has_type_simple_surf Gamma e1 tau ->
        has_type_simple_surf Gamma e2 tau ->
        has_type_simple_surf Gamma (ExIf e e1 e2) tau
  | SNewS :
      forall e tau,
        simple_surface_type tau ->
        has_type_simple_surf Gamma e tau ->
        has_type_simple_surf Gamma (ExNewRef tau e) (TyDeRef tau)
  | SGetS :
      forall e tau,
        simple_surface_type tau ->
        has_type_simple_surf Gamma e (TyDeRef tau) ->
        has_type_simple_surf Gamma (ExGetDep e) tau
  | SSetS :
      forall e1 e2 tau,
        simple_surface_type tau ->
        has_type_simple_surf Gamma e1 (TyDeRef tau) ->
        has_type_simple_surf Gamma e2 tau ->
        has_type_simple_surf Gamma (ExSetDep e1 e2) (TyBase BUnit)
  | SPlusS :
      forall e1 e2,
        has_type_simple_surf Gamma e1 (TyBase BNat) ->
        has_type_simple_surf Gamma e2 (TyBase BNat) ->
        has_type_simple_surf Gamma (ExPlus e1 e2) (TyBase BNat).

Lemma has_type_simple_surf_simple :
  forall Gamma e tau,
    has_type_simple_surf Gamma e tau ->
    simple_surface_type tau.
Proof.
  intros Gamma e tau Hty.
  induction Hty.
  - apply erase_simple_surf_ty_is_simple.
  - apply erase_simple_surf_ty_is_simple.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor; assumption.
  - match goal with
    | Hsimp : simple_surface_type (TyArr _ _) |- _ =>
        inversion Hsimp; subst; assumption
    end.
  - constructor; assumption.
  - match goal with
    | Hsimp : simple_surface_type (TyProd _ _) |- _ =>
        inversion Hsimp; subst; assumption
    end.
  - match goal with
    | Hsimp : simple_surface_type (TyProd _ _) |- _ =>
        inversion Hsimp; subst; assumption
    end.
  - assumption.
  - constructor; assumption.
  - match goal with
    | Hsimp : simple_surface_type (TyDeRef _) |- _ =>
        inversion Hsimp; subst; assumption
    end.
  - constructor.
  - constructor.
Qed.

Lemma has_type_simple_surf_valid :
  forall Gamma e tau,
    has_type_simple_surf Gamma e tau ->
    ty_valid_surf Gamma tau.
Proof.
  intros Gamma e tau Hty.
  apply simple_surface_type_valid_surf.
  exact (has_type_simple_surf_simple Gamma e tau Hty).
Qed.

Lemma has_type_pure_surf_weaken_var_fresh :
  forall Gamma e tau y tauy vy,
    ~ List.In y (free_exp_vars_surf e) ->
    has_type_pure_surf Gamma e tau ->
    has_type_pure_surf (ctx_add_var_surf Gamma y tauy vy) e tau.
Proof.
  intros Gamma e tau y tauy vy Hfresh Hty.
  revert y tauy vy Hfresh.
  induction Hty; intros y tauy vy Hfresh; simpl in *.
  - assert (Hneq : y <> x).
    { intro Heq. apply Hfresh. subst. simpl. auto. }
    eapply PVarS.
    + unfold var_ctx_lookup_surf, ctx_add_var_surf in *.
      simpl.
      apply lookup_insert_Some.
      right.
      split.
      * exact Hneq.
      * exact H.
    + exact H0.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - eapply PConstS; eauto.
  - eapply PAppS.
    + exact H.
    + apply IHHty1.
      intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHHty2.
      intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - apply PNotS.
    apply IHHty.
    exact Hfresh.
  - apply PImpS.
    + apply IHHty1.
      intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHHty2.
      intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - apply PAndS.
    + apply IHHty1.
      intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHHty2.
      intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - apply POrS.
    + apply IHHty1.
      intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHHty2.
      intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - apply PPlusS.
    + apply IHHty1.
      intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHHty2.
      intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
Qed.

Lemma ctx_add_var_surf_shadow :
  forall Gamma x tau1 e1 tau2 e2,
    ctx_add_var_surf (ctx_add_var_surf Gamma x tau1 e1) x tau2 e2 =
    ctx_add_var_surf Gamma x tau2 e2.
Proof.
  intros [vars consts] x tau1 e1 tau2 e2.
  unfold ctx_add_var_surf.
  simpl.
  f_equal.
  apply insert_insert.
Qed.

Lemma ctx_add_var_surf_swap :
  forall Gamma x tau1 e1 y tau2 e2,
    x <> y ->
    ctx_add_var_surf (ctx_add_var_surf Gamma x tau1 e1) y tau2 e2 =
    ctx_add_var_surf (ctx_add_var_surf Gamma y tau2 e2) x tau1 e1.
Proof.
  intros [vars consts] x tau1 e1 y tau2 e2 Hneq.
  unfold ctx_add_var_surf.
  simpl.
  f_equal.
  apply insert_commute.
  congruence.
Qed.

Lemma ctx_add_var_surf_add_const_surf_comm :
  forall Gamma x tau e f tau' e',
    ctx_add_var_surf (ctx_add_const_surf Gamma f tau' e') x tau e =
    ctx_add_const_surf (ctx_add_var_surf Gamma x tau e) f tau' e'.
Proof.
  intros [vars consts] x tau e f tau' e'.
  reflexivity.
Qed.

Lemma has_type_simple_surf_weaken_var_fresh :
  forall Gamma e tau y tauy vy,
    ~ List.In y (free_exp_vars_surf e) ->
    has_type_simple_surf Gamma e tau ->
    has_type_simple_surf (ctx_add_var_surf Gamma y tauy vy) e tau.
Proof.
  intros Gamma e tau y tauy vy Hfresh Hty.
  revert y tauy vy Hfresh.
  induction Hty; intros y tauy vy Hfresh.
  - econstructor. exact H.
  - econstructor.
    assert (Hneq : y <> x).
    { intro Heq. apply Hfresh. subst. simpl. auto. }
    unfold var_ctx_lookup_surf, ctx_add_var_surf in *.
    simpl.
    apply lookup_insert_Some.
    right.
    split.
    + exact Hneq.
    + exact H.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - apply SFunS.
    + assumption.
    + assumption.
    + apply simple_surface_type_valid_surf.
      constructor; assumption.
    + destruct (String.eq_dec y x).
      * subst y.
        rewrite ctx_add_var_surf_add_const_surf_comm.
        rewrite ctx_add_var_surf_shadow.
        assumption.
      * assert (Hclosed1 : free_ty_vars_surf tau1 = []).
        { apply simple_surface_type_no_free_ty_vars. exact H. }
        assert (Hclosed2 : free_ty_vars_surf tau2 = []).
        { apply simple_surface_type_no_free_ty_vars. exact H0. }
        assert (Hfresh_body : ~ List.In y (free_exp_vars_surf e)).
        { intro Hin.
          apply Hfresh.
          simpl.
          rewrite Hclosed1, Hclosed2.
          apply in_remove_string_intro; assumption. }
        specialize (IHHty y tauy vy Hfresh_body).
        rewrite ctx_add_var_surf_add_const_surf_comm.
        rewrite <- ctx_add_var_surf_swap by congruence.
        rewrite ctx_add_var_surf_add_const_surf_comm in IHHty.
        exact IHHty.
  - eapply SAppS.
    + apply IHHty1.
      intro Hin.
      apply Hfresh.
      simpl. apply in_or_app. left. exact Hin.
    + apply IHHty2.
      intro Hin.
      apply Hfresh.
      simpl. apply in_or_app. right. exact Hin.
  - eapply SProdS.
    + apply IHHty1.
      intro Hin.
      apply Hfresh.
      simpl. apply in_or_app. left. exact Hin.
    + apply IHHty2.
      intro Hin.
      apply Hfresh.
      simpl. apply in_or_app. right. exact Hin.
  - eapply SProjLS.
    apply IHHty.
    exact Hfresh.
  - eapply SProjRS.
    apply IHHty.
    exact Hfresh.
  - eapply SIfS.
    + apply has_type_pure_surf_weaken_var_fresh.
      * intro Hin.
        apply Hfresh.
        simpl. apply in_or_app. left. exact Hin.
      * exact H.
    + apply IHHty1.
      intro Hin.
      apply Hfresh.
      simpl. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IHHty2.
      intro Hin.
      apply Hfresh.
      simpl. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - eapply SNewS.
    + assumption.
    + apply IHHty.
      assert (Hclosed : free_ty_vars_surf tau = []).
      { apply simple_surface_type_no_free_ty_vars. exact H. }
      intro Hin.
      apply Hfresh.
      simpl.
      rewrite Hclosed.
      simpl.
      exact Hin.
  - apply SGetS.
    + assumption.
    + apply IHHty.
      exact Hfresh.
  - eapply SSetS.
    + exact H.
    + apply IHHty1.
      intro Hin.
      apply Hfresh.
      simpl. apply in_or_app. left. exact Hin.
    + apply IHHty2.
      intro Hin.
      apply Hfresh.
      simpl. apply in_or_app. right. exact Hin.
  - eapply SPlusS.
    + apply IHHty1.
      intro Hin.
      apply Hfresh.
      simpl. apply in_or_app. left. exact Hin.
    + apply IHHty2.
      intro Hin.
      apply Hfresh.
      simpl. apply in_or_app. right. exact Hin.
Qed.

Lemma simple_surface_type_trans_type_co_ref_ty_true :
  forall tau,
    simple_surface_type tau ->
    co_ref_ty (trans_type tau) = true /\ contra_ref_ty (trans_type tau) = true.
Proof.
  intros tau Hsimple.
  induction Hsimple.
  - split; reflexivity.
  - destruct IHHsimple1 as [Hco1 Hcontra1].
    destruct IHHsimple2 as [Hco2 Hcontra2].
    split.
    + simpl. rewrite Hcontra1, Hco2. reflexivity.
    + simpl. rewrite Hco1, Hcontra2. reflexivity.
  - destruct IHHsimple1 as [Hco1 Hcontra1].
    destruct IHHsimple2 as [Hco2 Hcontra2].
    split.
    + simpl. rewrite Hco1, Hco2. reflexivity.
    + simpl. rewrite Hcontra1, Hcontra2. reflexivity.
  - destruct IHHsimple as [Hco Hcontra].
    split.
    + unfold dref_encoding. simpl. rewrite Hco, Hcontra. reflexivity.
    + unfold dref_encoding. simpl. rewrite Hco, Hcontra. reflexivity.
Qed.

Lemma simple_surface_type_trans_type_eq :
  forall tau tau',
    simple_surface_type tau ->
    simple_surface_type tau' ->
    [| trans_type tau |] = [| trans_type tau' |] ->
    trans_type tau = trans_type tau'.
Proof.
  intros tau tau' Hsimple Hsimple' Herase.
  rewrite <- (simple_surface_type_trans_type_fixed tau Hsimple).
  rewrite <- (simple_surface_type_trans_type_fixed tau' Hsimple').
  exact Herase.
Qed.

Lemma simple_surface_type_subtype_refl_trans :
  forall Gamma tau,
    simple_surface_type tau ->
    subtype Gamma (trans_type tau) (trans_type tau).
Proof.
  intros Gamma tau Hsimple.
  induction Hsimple.
  - apply SBase.
  - simpl. apply SFun; assumption.
  - simpl. apply SPair; assumption.
  - unfold dref_encoding. simpl.
    destruct (simple_surface_type_trans_type_co_ref_ty_true tau Hsimple) as [Hco Hcontra].
    apply SPair.
    + apply SFun.
      * apply SBase.
      * exact IHHsimple.
    + apply SFun.
      * exact IHHsimple.
      * apply SBase.
Qed.

Lemma dref_encoding_inj :
  forall tau1 tau2,
    dref_encoding tau1 = dref_encoding tau2 ->
    tau1 = tau2.
Proof.
  intros tau1 tau2 Heq.
  unfold dref_encoding in Heq.
  inversion Heq; subst.
  inversion H1; subst.
  reflexivity.
Qed.

Lemma simple_surface_type_dref_encoding_admissible :
  forall tau,
    simple_surface_type tau ->
    co_ref_ty (dref_encoding (trans_type tau)) = true /\
    contra_ref_ty (dref_encoding (trans_type tau)) = true.
Proof.
  intros tau Hsimple.
  destruct (simple_surface_type_trans_type_co_ref_ty_true tau Hsimple) as [Hco Hcontra].
  unfold dref_encoding. simpl. rewrite Hco, Hcontra. split; reflexivity.
Qed.

(* ==================== PAPER LEMMA 15 ====================
   Existence of type coercion. *)
Lemma existence_of_type_coercion :
  forall Gamma e tau tau',
    simple_surface_type tau ->
    simple_surface_type tau' ->
    [| trans_type tau |] = [| trans_type tau' |] ->
    exists e', coerce sim (trans_ctx_surf Gamma) e (trans_type tau) e' (trans_type tau').
Proof.
  intros Gamma e tau tau' Hsimple Hsimple' Herase.
  exists e.
  apply CSub.
  rewrite (simple_surface_type_trans_type_eq tau tau' Hsimple Hsimple' Herase).
  apply simple_surface_type_subtype_refl_trans.
  exact Hsimple'.
Qed.

(* Reference-fragment helper lemmas for the proof of Lemma 15. *)
Lemma completeness_of_reference_coercion :
  forall w Gamma e tau tau',
    simple_surface_type tau ->
    simple_surface_type tau' ->
    [| TRef (trans_type tau) |] = [| TRef (trans_type tau') |] ->
    has_type (trans_ctx_surf Gamma) e (TRef [| trans_type tau |]) ->
    exists e', coerce w (trans_ctx_surf Gamma) e (TRef (trans_type tau)) e' (TRef (trans_type tau')).
Proof.
  intros w Gamma e tau tau' Hsimple Hsimple' Herase Hty.
  pose proof (simple_surface_type_trans_type_eq tau tau' Hsimple Hsimple') as Htrans.
  simpl in Herase.
  pose proof (dref_encoding_inj _ _ Herase) as Herase'.
  specialize (Htrans Herase').
  rewrite (simple_surface_type_trans_type_fixed tau Hsimple) in Hty.
  exists e.
  rewrite Htrans.
  apply CSub.
  apply SRef.
  - apply simple_surface_type_subtype_refl_trans. exact Hsimple'.
  - apply simple_surface_type_subtype_refl_trans. exact Hsimple'.
Qed.

Lemma completeness_of_ref_to_dref_coercion :
  forall Gamma e tau1 tau2,
    simple_surface_type tau1 ->
    simple_surface_type tau2 ->
    [| trans_type tau1 |] = [| trans_type tau2 |] ->
    has_type (trans_ctx_surf Gamma) e (TRef [| trans_type tau1 |]) ->
    exists e1,
      coerce sim (trans_ctx_surf Gamma) e (TRef (trans_type tau1)) e1 (trans_type (TyDeRef tau2)).
Proof.
  intros Gamma e tau1 tau2 Hsimple1 Hsimple2 Herase Hty.
  pose proof (simple_surface_type_trans_type_eq tau1 tau2 Hsimple1 Hsimple2 Herase) as Htrans.
  rewrite (simple_surface_type_trans_type_fixed tau1 Hsimple1) in Hty.
  destruct (simple_surface_type_trans_type_co_ref_ty_true tau1 Hsimple1) as [Hco1 Hcontra1].
  exists (expr_subst "y" e
    (EPair
      (EFix "" "u" (TBase BUnit) (trans_type tau2) (EGet (EVar "y")))
      (EFix "" "x" (trans_type tau2) (TBase BUnit) (ESet (EVar "y") (EVar "x"))))).
  refine (@CRefToDRef sim (trans_ctx_surf Gamma) e "y" "u" "x"
    (trans_type tau1) (trans_type tau2)
    (EGet (EVar "y")) (EVar "x") (EVar "y") (EVar "x") _ _ _ _ _).
  - reflexivity.
  - simpl. rewrite Hco1, Hcontra1. reflexivity.
  - exact (proj2 (simple_surface_type_dref_encoding_admissible tau2 Hsimple2)).
  - rewrite Htrans. apply CSub. apply simple_surface_type_subtype_refl_trans. exact Hsimple2.
  - rewrite <- Htrans. apply CSub. apply simple_surface_type_subtype_refl_trans. exact Hsimple1.
Qed.

Lemma completeness_of_dref_coercion :
  forall Gamma e tau1 tau2,
    simple_surface_type tau1 ->
    simple_surface_type tau2 ->
    [| trans_type tau1 |] = [| trans_type tau2 |] ->
    has_type (trans_ctx_surf Gamma) e [| trans_type (TyDeRef tau1) |] ->
    exists e1,
      coerce sim (trans_ctx_surf Gamma) e (trans_type (TyDeRef tau1)) e1 (trans_type (TyDeRef tau2)).
Proof.
  intros Gamma e tau1 tau2 Hsimple1 Hsimple2 Herase Hty.
  pose proof (simple_surface_type_trans_type_eq tau1 tau2 Hsimple1 Hsimple2 Herase) as Htrans.
  exists (expr_subst "y" e
    (EPair
      (EFix "" "u" (TBase BUnit) (trans_type tau2) (dget (EVar "y")))
      (EFix "" "x" (trans_type tau2) (TBase BUnit) (dset (EVar "y") (EVar "x"))))).
  refine (@CDRef sim (trans_ctx_surf Gamma) e "y" "u" "x"
    (trans_type tau1) (trans_type tau2)
    (dget (EVar "y")) (EVar "x") (EVar "y") (EVar "x") _ _ _ _ _).
  - reflexivity.
  - exact (proj1 (simple_surface_type_dref_encoding_admissible tau1 Hsimple1)).
  - exact (proj2 (simple_surface_type_dref_encoding_admissible tau2 Hsimple2)).
  - rewrite Htrans. apply CSub. apply simple_surface_type_subtype_refl_trans. exact Hsimple2.
  - rewrite <- Htrans. apply CSub. apply simple_surface_type_subtype_refl_trans. exact Hsimple1.
Qed.

(* ==================== PAPER LEMMA 16 ====================
   If co_ref(Gamma), co_ref(F), and e belongs to the simply typed source
   language, then the translated result type is reference-admissible. *)
Lemma simple_source_translation_preserves_co_ref :
  forall w Gamma e e' tau tau',
    co_ref_vars_surf Gamma ->
    co_ref_consts_surf Gamma ->
    has_type_simple_surf Gamma e tau ->
    has_type_surf w Gamma e e' tau' ->
    co_ref tau = true.
Proof.
  intros w Gamma e e' tau tau' _ _ Hsimple _.
  apply simple_surface_type_co_ref_true.
  exact (has_type_simple_surf_simple Gamma e tau Hsimple).
Qed.

(* ==================== PAPER LEMMA 17 ====================
   Relation between Gamma |-0 e : tau and Gamma |-sim e ; e' : tau'.
   In Coq the paper equation [tau'] = tau is expressed after translating the
   source simple type tau into the internal language. *)
Lemma simple_source_and_translation_types_agree :
  forall Gamma e e' tau tau',
    has_type_simple_surf Gamma e tau ->
    has_type_surf sim Gamma e e' tau' ->
    [| tau' |] = trans_type tau.
Proof.
  intros Gamma e e' tau tau' Hsimple Htr.
  revert tau Hsimple.
  induction Htr; intros tau0 Hsimple; inversion Hsimple; subst; clear Hsimple; simpl in *; try reflexivity.
  - match goal with
    | Hlookup1 : const_ctx_lookup_surf _ _ = Some _,
      Hlookup2 : const_ctx_lookup_surf _ _ = Some _ |- _ =>
        rewrite Hlookup1 in Hlookup2; inversion Hlookup2; subst; clear Hlookup2
    end.
    rewrite erase_i_ty_self.
    rewrite trans_type_erase_simple_surf_ty.
    reflexivity.
  - match goal with
    | Hlookup1 : const_ctx_lookup_surf _ _ = Some _,
      Hlookup2 : const_ctx_lookup_surf _ _ = Some _ |- _ =>
        rewrite Hlookup1 in Hlookup2; inversion Hlookup2; subst; clear Hlookup2
    end.
    rewrite trans_type_erase_simple_surf_ty.
    reflexivity.
  - match goal with
    | Hlookup1 : var_ctx_lookup_surf _ _ = Some _,
      Hlookup2 : var_ctx_lookup_surf _ _ = Some _ |- _ =>
        rewrite Hlookup1 in Hlookup2; inversion Hlookup2; subst; clear Hlookup2
    end.
    rewrite erase_i_ty_self.
    rewrite trans_type_erase_simple_surf_ty.
    reflexivity.
  - match goal with
    | Hlookup1 : var_ctx_lookup_surf _ _ = Some _,
      Hlookup2 : var_ctx_lookup_surf _ _ = Some _ |- _ =>
        rewrite Hlookup1 in Hlookup2; inversion Hlookup2; subst; clear Hlookup2
    end.
    rewrite trans_type_erase_simple_surf_ty.
    reflexivity.
  - match goal with
    | Hsimp1 : simple_surface_type _,
      Hsimp2 : simple_surface_type _ |- _ =>
        rewrite (simple_surface_type_trans_type_fixed _ Hsimp1);
        rewrite (simple_surface_type_trans_type_fixed _ Hsimp2)
      end.
    reflexivity.
  - match goal with
    | Hs1 : has_type_simple_surf _ _ (TyArr _ _),
      Hs2 : has_type_simple_surf _ _ _ |- _ =>
        pose proof (IHHtr1 _ Hs1) as Hfun;
        pose proof (IHHtr2 _ Hs2) as _
      end.
    simpl in Hfun.
    inversion Hfun; subst.
    rewrite erase_i_ty_ty_subst.
    reflexivity.
  - match goal with
    | Hs1 : has_type_simple_surf _ _ (TyArr _ _),
      Hs2 : has_type_simple_surf _ _ _ |- _ =>
        pose proof (IHHtr1 _ Hs1) as Hfun;
        pose proof (IHHtr2 _ Hs2) as _
      end.
    simpl in Hfun.
    inversion Hfun; subst.
    rewrite erase_i_ty_erase_dep_var.
    reflexivity.
  - match goal with
    | Hs1 : has_type_simple_surf _ _ _,
      Hs2 : has_type_simple_surf _ _ _ |- _ =>
        pose proof (IHHtr1 _ Hs1) as Hleft;
        pose proof (IHHtr2 _ Hs2) as Hright
      end.
    rewrite Hleft, Hright.
    reflexivity.
  - match goal with
    | Hs : has_type_simple_surf _ _ (TyProd _ _) |- _ =>
        pose proof (IHHtr _ Hs) as Hpair
      end.
    simpl in Hpair.
    inversion Hpair; subst.
    reflexivity.
  - match goal with
    | Hs : has_type_simple_surf _ _ (TyProd _ _) |- _ =>
        pose proof (IHHtr _ Hs) as Hpair
      end.
    simpl in Hpair.
    inversion Hpair; subst.
    reflexivity.
  - rewrite (simple_surface_type_trans_type_fixed _ H3).
    reflexivity.
  - match goal with
    | Hs : has_type_simple_surf _ _ (TyDeRef _) |- _ =>
        pose proof (IHHtr _ Hs) as Hdref
      end.
    simpl in Hdref.
    apply dref_encoding_inj in Hdref.
    exact Hdref.
  - assert (Hs1w : has_type_simple_surf (ctx_add_var_surf Γ u (TyBase BBool) e) e₁ tau0).
    { apply has_type_simple_surf_weaken_var_fresh.
      - intro Hin. apply H0. apply in_or_app. left. exact Hin.
      - exact H9. }
    assert (Hs2w : has_type_simple_surf (ctx_add_var_surf Γ u (TyBase BBool) (ExNot e)) e₂ tau0).
    { apply has_type_simple_surf_weaken_var_fresh.
      - intro Hin. apply H0. apply in_or_app. right. exact Hin.
      - exact H10. }
    pose proof (IHHtr1 _ Hs1w) as Hbranch1.
    pose proof (IHHtr2 _ Hs2w) as Hbranch2.
    destruct (ty_join_preserves_erase _ _ _ _ H3) as [Hj1 Hj2].
    rewrite <- Hbranch1.
    symmetry.
    exact Hj1.
  - exfalso.
    match goal with
    | Hnpure : ~ (exists tau', has_type_pure_surf _ _ tau'),
      Hpure : has_type_pure_surf _ _ (TyBase BBool) |- _ =>
        apply Hnpure; exists (TyBase BBool); exact Hpure
    end.
Qed.

(* Internal-language helper retained from the previous development. This is not a

   direct paper statement, but it records the inversion-style completeness shape

   that the repo was already exploring using the internal typing judgment. *)

Theorem internal_translation_completeness_helper :

  forall Gamma e0 tau,

    has_type (trans_ctx_surf Gamma) e0 [| trans_type tau |] ->

    exists w e, has_type_surf w Gamma e e0 (trans_type tau).

Admitted.



(* Helper completeness statements for the reference fragment. These are useful

   stepping stones, but they are not numbered paper results. *)

Theorem completeness_of_reference_translation :
  forall Gamma e' tau,
    has_type (trans_ctx_surf Gamma) e' (TRef [| trans_type tau |]) ->
    exists w e,
      has_type_surf w Gamma e e' (TRef (trans_type tau)) \/
      has_type_surf w Gamma e e' (trans_type tau).
Admitted.

Theorem completeness_of_dynamic_reference_translation :

  forall Gamma e' tau,

    has_type (trans_ctx_surf Gamma) e' [| dref_encoding (trans_type tau) |] ->

    exists w e,

      has_type_surf w Gamma e e' (trans_type (TyDeRef tau)).

Proof.

  intros Gamma e' tau Hty.

  exact (internal_translation_completeness_helper Gamma e' (TyDeRef tau) Hty).

Qed.



(* ==================== PAPER THEOREM 8 ====================

   Appendix completeness theorem for the translation. *)

Theorem paper_theorem_8_translation_completeness :

  forall Gamma e tau,

    co_ref_vars_surf Gamma ->

    co_ref_consts_surf Gamma ->

    has_type_simple_surf Gamma e tau ->

    exists e' tau', has_type_surf sim Gamma e e' tau'.

Admitted.



(* ==================== PAPER THEOREM 3 ====================

   Main-text restatement of the same completeness theorem. *)

Theorem paper_theorem_3_translation_completeness :

  forall Gamma e tau,

    co_ref_vars_surf Gamma ->

    co_ref_consts_surf Gamma ->

    has_type_simple_surf Gamma e tau ->

    exists e' tau', has_type_surf sim Gamma e e' tau'.

Proof.

  exact paper_theorem_8_translation_completeness.

Qed.


