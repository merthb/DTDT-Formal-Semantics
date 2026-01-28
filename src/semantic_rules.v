Require Import DTDT.syntax.
Import ListNotations.
From stdpp Require Export base.
From stdpp Require Export strings.
From stdpp Require Import stringmap.


(* --- Pure term validation ------------------------------------------------------ *)

(*
Pure terms are:
- variables whose essential type is a base type
- constants with simple type (τb1 → τb2 → ... → τbn)
- application of pure terms to pure terms
 *)

Fixpoint is_simple_type (type : i_ty) : bool :=
  match type with
  | TBase _ => true
  | TArr fname t1 t2 => is_simple_type t1 && is_simple_type t2
  | TProd t1 t2 => is_simple_type t1 && is_simple_type t2
  | _ => false
  end.

Definition essential_type_is_base_type (type : i_ty) : bool :=
  match type with
  | TBase _ => true
  | TSet _ _ _ => true
  | _ => false
  end.

Fixpoint is_pure_term (term : i_expr) (var_con : var_context) (const_con : const_context) : bool :=
  match term with
  | EConst con_name => match (const_ctx_lookup const_con con_name) with
    | Some type => is_simple_type type
    | _ => false
    end
  | EVar var_name => match (var_ctx_lookup var_con var_name) with
    | Some type => essential_type_is_base_type type
    | _ => false
    end
  | EApp exp1 exp2 => is_pure_term exp1 var_con const_con && is_pure_term exp2 var_con const_con
  | _ => false
  end.

(* Some testing just in case *)
Compute is_pure_term (EApp (EConst "f") (EVar "a")) [] [].
Compute is_pure_term (EApp (EConst "f") (EVar "a")) [("a"%string , TSet "x" BBool (EBool false))] [].
Compute is_pure_term (EApp (EConst "f") (EVar "a")) [("a"%string , TSet "x" BBool (EConst "b"))] [("f"%string , TArr "f" (TBase BBool) (TBase BBool))].

(* --- Selfification rule ------------------------------------------------------ *)

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
  | ENewRef type exp => ty_vars type ++ exp_vars exp
  | EGet exp => exp_vars exp
  | ESet exp1 exp2 => exp_vars exp1 ++ exp_vars exp2
  | _ => []
  end
with ty_vars (type : i_ty) : list string :=
  match type with
  | TBase _ => []
  | TSet var _ exp => var :: exp_vars exp
  | TArr var ty1 ty2 => var :: ty_vars ty1 ++ ty_vars ty2
  | TProd ty1 ty2 => ty_vars ty1 ++ ty_vars ty2
  | TRef type => ty_vars type
  end.

Definition fresh_string_list (l : list string) : string :=
  fresh_string_of_set ("x"%string) (list_to_set l).

Fixpoint self (type : i_ty) (term : i_expr) : i_ty :=
  match type with
  | TBase ty => TSet (fresh_string_list (exp_vars term)) ty (EEq (EVar (fresh_string_list (exp_vars term))) term)
  | TSet var tb expr => TSet var tb (EAnd expr (EEq (EVar var) term))
  | TArr _ (TBase ty) ty2 => TArr (fresh_string_list (exp_vars term)) (TBase ty) (self ty2 (EApp term (EVar (fresh_string_list (exp_vars term)))))
  | x => x
  end.

Compute self (TBase BNat) (EVar ("x"%string)).
Compute self (TArr ("n"%string) (TBase BNat) (TArr ("m"%string) (TBase BNat) (TSet ("l"%string) BNat (EEq (EVar ("l"%string)) (EPlus (EVar ("n"%string)) (EVar ("m"%string))))))) (EVar ("+"%string)).
