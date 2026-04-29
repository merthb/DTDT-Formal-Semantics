# DTDT Formal Semantics

## Overview

This repository contains a Coq formalisation of a concrete reconstruction of the system from **Dynamic Typing with Dependent Types** by Ou et al. The development is not meant to introduce a new type system. Its purpose is to make the paper's semantic core explicit and machine-checkable in Coq.

The formalisation separates two object-language layers:

- an **internal language**, where the core static semantics, semantic subtyping, references, small-step operational semantics, runtime store, and `fail` are formalised; and
- a **surface language**, where programmer-facing constructs such as `assert`, `simple`, `dependent`, and dynamic references are translated into the internal language.

The central idea is that statically unavailable refinement/dependency information can be recovered by **type-directed translation** and **coercions**. In simple mode, the translation may insert runtime checks. In dependent mode, more information is kept statically where possible.

The strongest mechanised part of the repository is the **internal language type-safety layer**: preservation, progress, and the final type-safety theorem are present in Coq. The translation layer is also formalised, but it is less closed: several hard soundness cases are axiomatized, and the main translation-completeness theorem is currently `Admitted`.

In the terminology of the thesis, the repository formalises:

- syntax of the internal and surface languages;
- pure expressions used inside refinements;
- internal type validity, typing, and semantic subtyping;
- surface validity, pure typing, and surface subtyping;
- small-step dynamic semantics over `(context, expression)` configurations;
- type-directed translation from surface expressions to internal expressions;
- coercions, dependency erasure, and dynamic-reference encoding;
- internal type safety;
- partial soundness and completeness metatheory for the translation.

The project uses the logical Coq namespace `DTDT`, so imports have the form:

```coq
Require Import DTDT.syntax.
Require Import DTDT.machine_inter.
Require Import DTDT.semantic_rules_inter.
```

## Requirements

The intended environment is:

- **Coq 8.20**
- `stdpp`
- `opam`
- `make`
- UTF-8 source support, because the files use Unicode identifiers and notations such as `Γ`, `τ`, `⊢`, `≤`, `↠*`, and `⊨`.

The code imports `stdpp` modules such as:

```coq
From stdpp Require Export base.
From stdpp Require Export strings.
From stdpp Require Export gmap.
From stdpp Require Import stringmap.
From stdpp Require Import fin_maps.
```

A typical compatible setup is Coq 8.20 with a Coq-8.20-compatible `coq-stdpp` package.

## Build Guide

### 1. Clone the repository

```sh
git clone https://github.com/merthb/DTDT-Formal-Semantics.git
cd DTDT-Formal-Semantics
```

### 2. Create an opam switch

```sh
opam update
opam switch create dtdt-coq-8.20 ocaml-base-compiler.4.14.1
eval $(opam env --switch=dtdt-coq-8.20)
```

Other OCaml versions supported by Coq 8.20 may also work, but OCaml 4.14.x is a conservative choice.

### 3. Install Coq and dependencies

```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq.8.20 coq-stdpp
```

If opam asks to choose a specific `coq-stdpp` version, choose one compatible with Coq 8.20.

### 4. Build the development

The repository contains a generated `Makefile` and an `_CoqProject` file. The normal build command is:

```sh
make
```

For parallel builds:

```sh
make -j$(nproc)
```

On macOS:

```sh
make -j$(sysctl -n hw.ncpu)
```

### 5. Regenerate the Makefile if needed

The `_CoqProject` file declares the logical namespace and compilation order:

```text
-Q src DTDT ...
```

If you add, remove, or reorder Coq files, regenerate the `Makefile`:

```sh
coq_makefile -f _CoqProject -o Makefile
make clean
make
```

### 6. Build one file during development

For early files, direct `coqc` calls are possible:

```sh
coqc -Q src DTDT src/syntax.v
coqc -Q src DTDT src/machine_inter.v
```

For files later in the dependency chain, prefer `make`, because `_CoqProject` records the correct compilation order.

## Repository Structure

### Root files

| Path | Role |
|---|---|
| `_CoqProject` | Declares `-Q src DTDT` and lists the active Coq files in build order. |
| `Makefile` | Generated build file, normally used through `make`. |
| `Makefile.conf` | Generated configuration fragment from `coq_makefile`. |
| `DTDT-tr.pdf` | Paper/report artifact included with the repository. |
| `src/` | Coq source files. |

The active build files listed in `_CoqProject` are:

```text
src/syntax.v
src/machine_inter.v
src/machine_inter_tests.v
src/entails_inter.v
src/semantic_rules_inter.v
src/semantic_rules_inter_tests.v
src/semantic_rules_surf.v
src/type_directed_translation.v
src/type_directed_translation_tests.v
src/foundational_lemmas_inter.v
src/type_safety_lemmas_inter.v
src/translation_soundness_lemmas.v
src/translation_completeness_lemmas.v
```

`src/big_step_eval_inter.v` is present in the repository, but it is intentionally archived and not part of the active build.

### `src/syntax.v`

Defines the syntax of both language layers and the context representations.

Main definitions:

- `BaseT`
  - `BString`
  - `BBool`
  - `BNat`
  - `BUnit`
- `base_to_set`
- internal types and expressions:
  - `i_ty`
  - `i_expr`
- internal context components:
  - `var_context`
  - `const_context`
  - `store_context`
  - `ctx`
- internal context operations:
  - `empty_ctx`
  - `var_ctx_lookup`
  - `const_ctx_lookup`
  - `store_ctx_lookup`
  - `ctx_add_var`
  - `ctx_add_const`
  - `ctx_add_store`
  - `add_ctx`
- surface types and expressions:
  - `ty`
  - `expr`
- surface contexts:
  - `var_context_surf`
  - `const_context_surf`
  - `ctx_surf`
  - `empty_ctx_surf`
  - `var_ctx_lookup_surf`
  - `const_ctx_lookup_surf`
  - `ctx_add_var_surf`
  - `ctx_add_const_surf`

Internal types include:

```coq
TBase
TSet
TArr
TArrDep
TProd
TRef
```

Internal expressions include literals, constants, variables, locations, fixpoints, application, arithmetic, products, projections, conditionals, Boolean connectives, equality, reference allocation, dereference, assignment, and `EFail`.

Surface types include all ordinary type forms plus:

```coq
TyDeRef
```

Surface expressions include the internal-style source constructs plus:

```coq
ExDeRef
ExGetDep
ExSetDep
EAssert
ESimple
EDep
```

`EFail` is deliberately internal-only. The surface language has no source-level `fail`; failures are introduced by translated runtime checks.

### `src/machine_inter.v`

Defines the internal operational semantics.

Main definitions:

- `var_dom`
- `store_dom`
- `value`
- `base_value`
- `eval_ctx`
- `plug`
- `base_eq`
- `expr_subst`
- `ty_subst`
- `expr_subst_fun`
- `step`
- `eval`

The machine state is a pair:

```coq
(ctx * i_expr)
```

The one-step relation is:

```coq
step : (ctx * i_expr) -> (ctx * i_expr) -> Prop
```

The multi-step relation is:

```coq
eval : (ctx * i_expr) -> (ctx * i_expr) -> Prop
```

with notation:

```coq
σ₁ ↠* σ₂
```

Important design detail: `value` is indexed by the current context. Constants, variables, and locations count as values only when they are found in the corresponding context component.

Reduction rules include:

- evaluation-context closure: `StepCtx`
- constant application: `StepConst`
- variable lookup: `StepVar`
- recursive function application: `StepFix`
- projections: `StepFst`, `StepSnd`
- conditionals: `StepIfTrue`, `StepIfFalse`
- reference allocation: `StepNew`
- dereference: `StepGet`
- assignment: `StepSet`
- failure propagation: `StepFail`
- Boolean and arithmetic primitives:
  - `StepNot`
  - `StepAnd`
  - `StepOr`
  - `StepImp`
  - `StepEq`
  - `StepPlus`

### `src/big_step_eval_inter.v`

This file is archived reference material. Its entire contents are inside a comment block headed:

```coq
(* Archived big-step semantics.
   This file is intentionally kept in the repository for reference,
   but it has been removed from the active build/dependency chain.
```

It sketches an older big-step evaluator:

- `value`
- `eval_bigstep`
- `eval_app_test`
- `eval_eq_test`
- `eval_bool_test`

Use `machine_inter.v`, not this file, for the current operational semantics.

### `src/entails_inter.v`

Defines semantic entailment for internal predicates.

Main definitions:

- `entails`
- notation `Γ ⊨ e`
- `binding_subst`
- `ctx_subst`

The definition is:

```coq
Definition entails (Γ : ctx) (e : i_expr) : Prop :=
  (Γ, e) ↠* (Γ, EBool true).
```

The file also records the semantic-entailment interface as axioms. These axioms are an intentional abstraction boundary for refinement reasoning and correspond to the thesis' description of semantic consequence as an axiomatic background layer.

Axioms:

- `entails_hypothesis`
- `entails_weakening`
- `entails_subst_base`
- `entails_subst_set`
- `entails_equality`
- `entails_drop_unused`
- `entails_store_update_refinement`
- `entails_const_step`
- `entails_imp_refl`
- `entails_modus_ponens`

Proved lemmas:

- `entails_true`
- `entails_not_false`
- `entails_weaken_right`

### `src/semantic_rules_inter.v`

Defines the internal static semantics.

Main definitions and judgments:

- `exp_vars`
- `ty_vars`
- `remove_string`
- `free_exp_vars`
- `free_ty_vars`
- `fresh_string_list`
- `if_branch_var`
- `self_with`
- `self`
- `is_simple_type`
- `essential_type`
- `essential_type_is_base_type`
- `has_type_pure`
- `ty_valid`
- `subtype`
- `has_type`
- `store_well_typed`
- `var_well_typed`
- `const_well_typed`
- `var_base_pure_well_typed`
- `const_step_well_typed`
- `const_step_pure_well_typed`
- `runtime_ctx_well_typed`

Important notations:

```coq
Γ ⊢pure e : τ
Γ ⊢valid τ
Γ ⊢ τ₁ ≤ τ₂
Γ ⊢ e : τ
```

This file defines four core internal relations:

1. **Pure typing**: `has_type_pure`
2. **Type validity**: `ty_valid`
3. **Semantic subtyping**: `subtype`
4. **Full internal typing**: `has_type`

The pure fragment is the subset allowed inside refinements. It admits base literals, variables whose essential type is base-like, simple constants, pure applications, Boolean connectives, equality, and addition.

The full internal typing relation includes:

- literal typing;
- variable and constant typing;
- location typing;
- failure typing at any valid type;
- dependent and non-dependent recursive function typing;
- pure and impure application;
- arithmetic and Boolean operations;
- reference operations;
- products and projections;
- conditionals;
- selfification;
- subsumption.

The runtime invariants package the conditions needed by preservation and progress. The most important aggregate invariant is:

```coq
runtime_ctx_well_typed
```

### `src/semantic_rules_surf.v`

Defines surface-language static infrastructure and the non-type-directed parts of translation.

Main definitions and judgments:

- `free_exp_vars_surf`
- `free_ty_vars_surf`
- `is_simple_type_surf`
- `essential_type_surf`
- `essential_type_is_base_type_surf`
- `has_type_pure_surf`
- `ty_valid_surf`
- `expr_subst_surf`
- `ty_subst_surf`
- `dref_encoding`
- `trans_type`
- `trans_expr_partial`
- `trans_expr_dref_free`
- `trans_ctx_surf`
- `subtype_surf`

Important notations:

```coq
Γ ⊢ₛpure e : τ
Γ ⊢ₛvalid τ
⟦ τ ⟧
⟦ Γ ⟧c
```

Dynamic references are encoded internally as a pair of getter and setter functions:

```coq
Definition dref_encoding (τ : i_ty) : i_ty :=
  TProd (TArr (TBase BUnit) τ) (TArr τ (TBase BUnit)).
```

`trans_expr_partial` translates the dref-free fragment. Source-only dynamic-reference constructs are handled later by type-directed translation, not by this partial structural translation.

### `src/type_directed_translation.v`

Defines the type-directed translation and coercion machinery.

Main definitions:

- `mode`
  - `sim`
  - `dep`
- `dget`
- `dset`
- `pack_dref`
- `erase_dep_var`
- notation `[[ t ]] x`
- `erase_i_ty`
- notation `[| t |]`
- `co_ref`
- `contra_ref`
- `co_ref_ty`
- `contra_ref_ty`
- `coerce`
- `ty_meet`
- `ty_join`
- `has_type_surf`

Important notations:

```coq
Γ ⊢[ w ] e : τ ↦ e' : τ'
Γ ⊢sim e : τ ↦ e' : τ'
Γ ⊢dep e : τ ↦ e' : τ'

Γ ⊢ τ₁ ⊓ τ₂ ⇒ τ₃
Γ ⊢ τ₁ ⊔ τ₂ ⇒ τ₃

Γ ⊢[ w ] e ; e' : τ
Γ ⊢sim e ; e' : τ
Γ ⊢dep e ; e' : τ
```

Coercion constructors:

- `CSub`
- `CBase`
- `CFunCo`
- `CFunContNonDep`
- `CFunContDep`
- `CFunEraseDep`
- `CPair`
- `CRefToDRef`
- `CDRef`

Meet constructors:

- `MeetBase`
- `MeetSet`
- `MeetBaseLeft`
- `MeetBaseRight`
- `MeetArr`
- `MeetArrDep`
- `MeetProd`
- `MeetRef`

Join constructors:

- `JoinBase`
- `JoinSet`
- `JoinBaseLeft`
- `JoinBaseRight`
- `JoinArr`
- `JoinArrDep`
- `JoinProd`
- `JoinRef`

Type-directed translation constructors:

- literals and primitive expressions:
  - `ATNat`
  - `ATBool`
  - `ATString`
  - `ATUnit`
  - `ATPlus`
- constants and variables:
  - `ATConstSelf`
  - `ATConst`
  - `ATVarSelf`
  - `ATVar`
- functions and applications:
  - `ATFun`
  - `ATApp`
  - `ATAppPure`
  - `ATAppImPure`
- products:
  - `ATProd`
  - `ATFst`
  - `ATSnd`
- references:
  - `ATNewRef`
  - `ATGet`
  - `ATSet`
- dynamic references:
  - `ATDeRef`
  - `ATGetDep`
  - `ATSetDep`
- conditionals:
  - `ATIfPure`
  - `ATIfImPure`
- mode/control constructs:
  - `ATAssert`
  - `ATDynamic`
  - `ATStatic`

### `src/foundational_lemmas_inter.v`

Contains the large technical support library for the internal metatheory.

It proves context algebra, weakening, free-variable properties, subtyping support, substitution lemmas, inversion lemmas, context/stores facts, and evaluation-context support. This is the proof infrastructure that makes the later type-safety and translation proofs manageable.

Key groups:

| Group | Main names |
|---|---|
| Context algebra | `option_union_assoc`, `add_ctx_empty_r`, `add_ctx_empty_l`, `add_ctx_assoc`, `add_ctx_ctx_add_var`, `add_ctx_ctx_add_const`, `add_ctx_ctx_add_store` |
| Lookup preservation | `lookup_lemma_const_right`, `lookup_lemma_var_right`, `lookup_lemma_const`, `lookup_lemma_var`, `lookup_lemma_store_right`, `lookup_lemma_var_add` |
| Weakening | `weakening_entails_right`, `weakening_has_type_pure_right`, `weakening_has_type_pure`, `weakening_has_type_pure_add`, `weakening_ty_valid_right`, `weakening_ty_valid`, `weakening_subtype_right`, `weakening_subtype`, `weakening_right`, `weakening` |
| Pure-to-internal typing | `has_type_pure_implies_has_type`, `pure_implies_internal_typing` |
| Selfification/reference inversion | `ref_type_origin`, `self_ref_inv`, `self_pair_inv`, `inversion_ref` |
| Free-variable lemmas | `free_var_pure_is_base_typed`, `has_type_pure_empty_ctx_closed`, `free_var_valid_type_is_base_typed` |
| Subtyping basics | `subtype_refl_valid`, `subtype_preserves_essential_type`, `subtype_refl` |
| Context and store mutation | `ctx_add_var_store_comm`, `value_change_var_type`, `value_change_const_witness`, `step_preserves_env`, `step_preserves_var_lookup`, `step_preserves_const_lookup`, `step_change_var_type`, `eval_change_var_type` |
| Subsumption under variable assumptions | `subsumption_entails_var`, `subsumption_has_type_pure_var`, `subsumption_entails_var_ctx`, `subsumption_has_type_pure_var_ctx`, `subsumption_ty_valid_var_ctx`, `subsumption_subtype_var_ctx`, `subsumption_has_type_var_ctx`, `subsumption_ty_valid_var`, `subsumption_subtype_var`, `subsumption_has_type_var` |
| Refinement canonical form | `canonical_forms_set` |
| Substitution support | `ty_subst_preserves_beta`, `ty_subst_preserves_essential_type`, `ty_subst_essential_type_id`, `ty_subst_self_with_base`, `ty_subst_simple_id`, `expr_subst_exp_vars_fresh`, `ty_subst_ty_vars_fresh`, `expr_subst_free_exp_vars_fresh`, `free_exp_vars_subst_subset`, `free_ty_vars_subst_closed`, `ty_subst_free_ty_vars_fresh` |
| Base substitution | `subst_base_has_type_pure`, `subst_base_ty_valid`, `subst_base_subtype`, `subst_base_has_type`, `subst_base_has_type_wf`, `subst_base_has_type_pure_wf`, `subst_base_ty_valid_wf`, `subst_base_subtype_wf` |
| Non-base substitution | `subst_nonbase_has_type_pure`, `subst_nonbase_pure_id`, `subst_nonbase_has_type_pure_ctx`, `subst_nonbase_ty_valid_ctx`, `subst_nonbase_ty_valid`, `subst_nonbase_entails_ctx`, `subst_nonbase_subtype_ctx`, `subst_nonbase_subtype`, `subst_nonbase_has_type` |
| Freshness and weakening | `fresh_var_for_ty`, `fresh_var_for_ty_not_in_ctx`, `fresh_var_for_ty_not_in_ty_vars`, `has_type_pure_rename_var`, `has_type_pure_weaken_fresh_var`, `ty_valid_weaken_fresh_var`, `has_type_pure_drop_fresh_var`, `ty_valid_drop_fresh_var` |
| Inversion and evaluation | `inversion_fix`, `inversion_pair`, `eval_trans`, `eval_plug`, `pure_subst_step_eval` |
| Step lemmas | `step_lemma_entails_var_forward`, `step_lemma_entails_var_backward`, `step_lemma_subtype_bool_singleton_backward`, `step_lemma_subtype_bool_singleton_forward`, `step_lemma_entails_var`, `step_lemma_entails`, `step_lemma_ty_valid`, `step_lemma_entails_bool_singleton`, `step_lemma_has_type_bool_singleton` |

Trusted assumption in this file:

```coq
Axiom has_type_subst_base_closed_pure_ctx
```

This packages the hardest closed/pure base-substitution typing case.

### `src/type_safety_lemmas_inter.v`

Contains the internal type-safety proof development.

Important definitions:

- `compose_eval_ctx`
- `no_var_bindings`
- `no_const_bindings`
- `state_ok`

Important theorem and lemma groups:

| Paper item / role | Exact names | Informal meaning |
|---|---|---|
| Paper Lemma 9 | `pure_step_ctx_preservation`, `pure_fail_ctx_absurd`, `preservation_pure_terms_sigma`, `preservation_pure_terms` | Pure typing is preserved by reduction in the pure fragment. |
| Paper Lemma 11: Booleans | `subtype_base_essential_inv`, `subtype_bool_essential_inv`, `canonical_forms_bool_essential`, `canonical_forms_bool` | Well-typed Boolean values are `true` or `false`. |
| Paper Lemma 11: products/references/functions | `canonical_forms_pair`, `canonical_forms_ref`, `canonical_forms_fun_nobindings`, `canonical_forms_fun_dep_nobindings`, `canonical_forms_pair_nobindings`, `canonical_forms_ref_nobindings` | Canonical forms for products, references, and functions. |
| Selfification support | `self_to_TArr`, `self_to_TArrDep_cases`, `self_to_TProd`, `self_to_TRef`, `self_essential_base_inv` | Inversion facts for selfified types. |
| Empty/runtime context invariants | `store_well_typed_empty`, `var_well_typed_empty`, `const_well_typed_empty`, `var_base_pure_well_typed_empty`, `const_step_well_typed_empty`, `const_step_pure_well_typed_empty`, `runtime_ctx_well_typed_empty` | The empty runtime context satisfies the runtime invariants. |
| Runtime invariant projections | `var_well_typed_lookup`, `const_well_typed_lookup`, `runtime_ctx_well_typed_var`, `runtime_ctx_well_typed_var_base_pure`, `runtime_ctx_well_typed_const`, `runtime_ctx_well_typed_store`, `runtime_ctx_well_typed_const_step`, `runtime_ctx_well_typed_const_step_pure` | Extract components of `runtime_ctx_well_typed`. |
| Store support | `store_well_typed_lookup`, `store_lookup_add_eq`, `store_lookup_add_neq`, `step_new_preserves_store_well_typed`, `step_set_preserves_store_well_typed` | Store invariants for allocation and update. |
| Evaluation contexts | `plug_has_typed_hole`, `compose_eval_ctx`, `plug_compose_eval_ctx`, `plug_has_typed_hole_pure` | Recover and compose typed evaluation contexts. |
| Per-rule preservation | `step_new_preserves_typing`, `step_set_preserves_typing`, `step_get_preserves_typing`, `step_fst_preserves_typing`, `step_snd_preserves_typing`, `step_if_true_preserves_typing`, `step_if_false_preserves_typing`, `step_not_preserves_typing`, `step_and_preserves_typing`, `step_or_preserves_typing`, `step_imp_preserves_typing`, `step_eq_preserves_typing`, `step_plus_preserves_typing` | Typing is preserved by individual reduction rules. |
| Preservation, paper theorem 4 | `preservation_left_same_ctx_step`, `preservation_left_store_typed_ctx_by_step`, `preservation_left_store_typed_ctx`, `preservation_left_runtime_ctx_by_step`, `preservation_left_runtime_ctx`, `preservation_left`, `preservation_right_store_typed_ctx_by_step`, `preservation_right_store_typed_ctx`, `preservation_right`, `preservation_typed_store`, `preservation` | Well-typed configurations remain well typed after evaluation. |
| Progress, paper theorem 5 | `progress_pure_nobindings`, `progress_store_typed_ctx_nobindings`, `progress_ok`, `progress`, `progress_empty` | A well-typed closed expression is a value, `EFail`, or can step. |
| Type safety, paper theorem 1 | `paper_theorem_1_type_safety` | If a well-typed closed expression evaluates to a state, the resulting expression is a value, `EFail`, or can step further. |

Trusted assumption in this file:

```coq
Axiom preservation_left_stepctx_assumption
```

This isolates a context-preservation case used by the preservation proof.

### `src/translation_soundness_lemmas.v`

Contains soundness results for translating surface syntax and coercions into internal syntax.

Important groups:

| Group | Exact names |
|---|---|
| Surface context translation | `trans_ctx_surf_lookup_var`, `trans_ctx_surf_lookup_const`, `trans_ctx_surf_add_var`, `trans_ctx_surf_add_const` |
| Essential/simple type translation | `trans_type_essential_type`, `trans_type_base_flag`, `is_simple_type_surf_trans` |
| Pure translation | `trans_expr_partial_pure`, `trans_expr_partial_pure_sound`, `trans_expr_dref_free_pure_sound`, `pure_surface_translation_sound` |
| Free-variable preservation | `free_var_translation_subsets`, `free_exp_vars_trans_expr_partial_subset`, `free_ty_vars_trans_type_subset` |
| Validity/subtyping preservation | `trans_type_preserves_validity`, `trans_type_preserves_subtype_surf` |
| Erasure support | `erase_dep_var_id_if_fresh_ty_var`, `simple_type_no_ty_vars`, `erase_dep_var_simple_id`, `erase_dep_var_preserves_validity_simple`, `erase_dep_var_preserves_validity_fresh_ty_var`, `erase_dep_var_preserves_validity`, `subtype_type_match_helper` |
| Coercion soundness | `soundness_of_dep_type_coercion`, `soundness_of_sim_type_coercion`, `soundness_of_type_coercion` |
| Translation soundness | `soundness_of_translation_fun_case`, `soundness_of_translation_if_pure_case`, `soundness_of_translation` |
| Reference/dref soundness | `soundness_of_reference_coercion`, `soundness_of_ref_to_dref_coercion`, `soundness_of_dref_coercion` |

Main theorem:

```coq
Theorem soundness_of_translation
```

It states that if a surface expression has a type-directed translation, then the generated internal expression is well typed in the translated context.

Trusted assumptions in this file:

```coq
Axiom soundness_of_sim_type_coercion
Axiom soundness_of_translation_fun_case
Axiom soundness_of_translation_if_pure_case
```

### `src/translation_completeness_lemmas.v`

Contains the current completeness-side development for the simple surface fragment.

Important definitions:

- `co_ref_vars_surf`
- `co_ref_consts_surf`
- `simple_surface_type`
- `erase_simple_surf_ty`
- `has_type_simple_surf`

Important theorem and lemma groups:

| Paper item / role | Exact names | Informal meaning |
|---|---|---|
| Type matching | `simple_type_match_subtype`, `simple_type_match_coercion`, `simple_type_match_ref` | Relates simple erased types to subtyping/coercion structure. |
| Reference admissibility contexts | `co_ref_vars_surf`, `co_ref_consts_surf`, `co_ref_vars_surf_add_var`, `co_ref_consts_surf_add_var`, `co_ref_consts_surf_add_const`, `co_ref_vars_surf_add_const` | Tracks `co_ref`/`contra_ref` side conditions in surface contexts. |
| Paper Lemma 14 / simple types | `simple_surface_type`, `erase_simple_surf_ty`, `erase_simple_surf_ty_is_simple`, `erase_simple_surf_ty_id`, `simple_surface_type_no_free_ty_vars`, `simple_surface_type_valid_surf`, `trans_type_erase_simple_surf_ty`, `simple_surface_type_co_ref_contra_ref`, `simple_surface_type_co_ref_true`, `simple_surface_type_contra_ref_true` | Defines and proves basic facts about the simple surface type fragment. |
| Erasure infrastructure | `simple_surface_type_trans_type_fixed`, `simple_surface_type_trans_type_no_ty_vars`, `erase_i_ty_self_with`, `erase_i_ty_self`, `erase_i_ty_ty_subst`, `erase_i_ty_erase_dep_var`, `erase_i_ty_idempotent`, `ty_meet_preserves_erase` | Shows that erasure and translation produce matching internal type shapes. |
| Simple surface typing | `has_type_simple_surf`, `has_type_simple_surf_simple`, `has_type_simple_surf_valid` | Restricted source typing relation used by completeness. |
| Translation existence for simple terms | `simple_const_translation_exists`, `simple_var_translation_exists`, `simple_literal_translation_exists`, `simple_nat_translation_exists`, `simple_bool_translation_exists`, `simple_string_translation_exists`, `simple_unit_translation_exists` | Basic existence facts for translated simple source terms. |
| Context operations | `ctx_add_var_surf_shadow`, `ctx_add_var_surf_swap`, `ctx_add_var_surf_add_const_surf_comm`, `ctx_add_const_surf_shadow`, `ctx_add_const_surf_swap`, `has_type_pure_surf_weaken_var_fresh`, `has_type_simple_surf_weaken_var_fresh` | Surface context manipulation. |
| Paper Lemma 15 | `existence_of_type_coercion`, `completeness_of_reference_coercion`, `completeness_of_ref_to_dref_coercion`, `completeness_of_dref_coercion` | Existence of coercions, including reference and dynamic-reference cases. |
| Paper Lemma 16 | `simple_source_translation_preserves_co_ref` | Simple-source translations preserve reference admissibility. |
| Paper Lemma 17 | `simple_source_and_translation_types_agree` | Source simple types and translated/erased internal types agree. |
| Paper Theorem 8 | `paper_theorem_8_translation_completeness` | Appendix completeness theorem for simple-mode translation; currently `Admitted`. |
| Paper Theorem 3 | `paper_theorem_3_translation_completeness` | Main-text restatement, proved by `exact paper_theorem_8_translation_completeness`. |

### Test files

#### `src/machine_inter_tests.v`

Examples for the internal machine and references:

- `machine_ref_ctx`
- `machine_ref_update_fun`
- `eval_if_get_set_test`
- `eval_app_with_store_effect_test`
- `rewards_ctx`
- `rewards_points_lookup`
- `rewards_member_lookup`
- `award_bonus_fun`
- `award_bonus_program`
- `eval_award_bonus_program_test`

#### `src/semantic_rules_inter_tests.v`

Examples for internal typing, pure typing, refinement subtyping, and reference typing:

- `var_lookup_add`
- `var_lookup_add_ne`
- `pure_nat_ctx`
- `ref_nat_ctx`
- `ref_inspecting_fun`
- `pure_guarded_arithmetic_test`
- `subtype_refinement_implication_test`
- `has_type_reference_conditional_test`
- `has_type_reference_inspecting_function_test`

#### `src/type_directed_translation_tests.v`

Examples for coercions, dynamic references, conditionals, and impure application:

- `surf_newref_nat_expr`
- `inter_newref_nat_expr`
- `inter_dref_nat_expr`
- `surf_dref_if_nat_expr`
- `inter_dref_if_nat_expr`
- `surf_dref_set_if_unit_expr`
- `inter_dref_set_if_unit_expr`
- `surf_const_dep_fun_nat_expr`
- `surf_impure_app_ctx`
- `erased_dep_fun_var_term`
- `coerce_newref_nat_to_dref_example`
- `has_type_surf_deref_nat_example`
- `has_type_surf_dref_if_nat_test`
- `has_type_surf_dref_set_if_unit_test`
- `has_type_surf_app_impure_nat_test`

## Main Lemmas and Theorems

This section lists the paper-facing or structurally important results. The repository also contains many small helper lemmas for context, substitution, lookup, freshness, and store manipulation.

### Entailment layer

File: `src/entails_inter.v`

| Name | Kind | Role |
|---|---|---|
| `entails_hypothesis` | Axiom | A refinement hypothesis entails its predicate. |
| `entails_weakening` | Axiom | Entailment is stable under context extension. |
| `entails_subst_base` | Axiom | Base substitution preserves entailment. |
| `entails_subst_set` | Axiom | Set/refinement substitution preserves entailment when the replacement satisfies the refinement. |
| `entails_equality` | Axiom | Equality can transport a predicate. |
| `entails_drop_unused` | Axiom | Unused bindings can be dropped. |
| `entails_store_update_refinement` | Axiom | Store updates preserve suitable refinement entailments. |
| `entails_const_step` | Axiom | Entailment is compatible with primitive constant stepping under contexts. |
| `entails_imp_refl` | Axiom | Propositional implication reflexivity. |
| `entails_modus_ponens` | Axiom | Semantic modus ponens. |
| `entails_true` | Lemma | Every context entails `true`. |
| `entails_not_false` | Lemma | Every context entails `not false`. |
| `entails_weaken_right` | Lemma | Convenience wrapper around entailment weakening. |

### Internal foundational lemmas

File: `src/foundational_lemmas_inter.v`

The main paper-facing groups are:

- **Weakening**:
  - `weakening_entails_right`
  - `weakening_has_type_pure_right`
  - `weakening_has_type_pure`
  - `weakening_has_type_pure_add`
  - `weakening_ty_valid_right`
  - `weakening_ty_valid`
  - `weakening_subtype_right`
  - `weakening_subtype`
  - `weakening_right`
  - `weakening`
- **Pure typing implies ordinary typing**:
  - `has_type_pure_implies_has_type`
  - `pure_implies_internal_typing`
- **Free-variable discipline**:
  - `free_var_pure_is_base_typed`
  - `has_type_pure_empty_ctx_closed`
  - `free_var_valid_type_is_base_typed`
- **Subsumption under variable binding changes**:
  - `subsumption_entails_var`
  - `subsumption_has_type_pure_var`
  - `subsumption_entails_var_ctx`
  - `subsumption_has_type_pure_var_ctx`
  - `subsumption_ty_valid_var_ctx`
  - `subsumption_subtype_var_ctx`
  - `subsumption_has_type_var_ctx`
  - `subsumption_ty_valid_var`
  - `subsumption_subtype_var`
  - `subsumption_has_type_var`
- **Refinement canonical form**:
  - `canonical_forms_set`
- **Base substitution**:
  - `subst_base_has_type_pure`
  - `subst_base_ty_valid`
  - `subst_base_subtype`
  - `subst_base_has_type`
- **Non-base substitution**:
  - `subst_nonbase_has_type_pure`
  - `subst_nonbase_ty_valid`
  - `subst_nonbase_subtype`
  - `subst_nonbase_has_type`
- **Evaluation and step support**:
  - `eval_trans`
  - `eval_plug`
  - `pure_subst_step_eval`
  - `step_lemma_entails`
  - `step_lemma_ty_valid`
  - `step_lemma_has_type_bool_singleton`

Important dependency structure:

1. context algebra and lookup lemmas support weakening;
2. weakening supports substitution and typing preservation under context extension;
3. semantic entailment axioms support refinement subtyping and `canonical_forms_set`;
4. substitution lemmas support dependent application and selfification cases;
5. step lemmas support preservation and translation soundness.

Trusted assumption:

- `has_type_subst_base_closed_pure_ctx`

### Internal type safety

File: `src/type_safety_lemmas_inter.v`

Main exact theorem names:

```coq
Theorem preservation_typed_store
Theorem preservation
Theorem progress_ok
Theorem progress
Theorem paper_theorem_1_type_safety
```

Auxiliary theorem/lemma path:

1. `preservation_pure_terms` proves pure-term preservation for the pure fragment.
2. canonical-forms lemmas such as `canonical_forms_bool`, `canonical_forms_pair`, `canonical_forms_ref`, `canonical_forms_fun_nobindings`, and `canonical_forms_fun_dep_nobindings` analyse well-typed values.
3. per-step lemmas such as `step_new_preserves_typing`, `step_set_preserves_typing`, and `step_get_preserves_typing` handle operational rules.
4. `preservation_left` and `preservation_right` combine expression typing and store/runtime-context preservation.
5. `preservation_typed_store` and `preservation` give the paper-style preservation theorem.
6. `progress_ok`, `progress`, and `progress_empty` give progress.
7. `paper_theorem_1_type_safety` combines multi-step evaluation with progress.

Trusted assumption:

- `preservation_left_stepctx_assumption`

### Translation soundness

File: `src/translation_soundness_lemmas.v`

Main exact theorem names:

```coq
Theorem soundness_of_type_coercion
Theorem soundness_of_translation
```

Important lemmas:

- `trans_type_preserves_validity`
- `trans_type_preserves_subtype_surf`
- `soundness_of_dep_type_coercion`
- `soundness_of_reference_coercion`
- `soundness_of_ref_to_dref_coercion`
- `soundness_of_dref_coercion`

The dependency flow is:

1. context translation lemmas show that surface lookups correspond to internal lookups after `trans_ctx_surf`;
2. pure translation lemmas show that surface-pure expressions translate to internal-pure/internal-well-typed expressions;
3. validity and subtyping preservation connect surface judgments to internal judgments;
4. dependency-erasure lemmas handle simple and dependent cases;
5. coercion soundness proves that generated coercions produce well-typed internal terms;
6. `soundness_of_translation` combines these results for the full type-directed translation judgment.

Trusted assumptions:

- `soundness_of_sim_type_coercion`
- `soundness_of_translation_fun_case`
- `soundness_of_translation_if_pure_case`

### Translation completeness

File: `src/translation_completeness_lemmas.v`

Main exact theorem names:

```coq
Theorem paper_theorem_8_translation_completeness
Theorem paper_theorem_3_translation_completeness
```

`paper_theorem_8_translation_completeness` is currently `Admitted`.

`paper_theorem_3_translation_completeness` is a restatement proved by:

```coq
exact paper_theorem_8_translation_completeness.
```

Important lemmas:

- `simple_type_match_subtype`
- `simple_type_match_coercion`
- `simple_type_match_ref`
- `simple_surface_type_valid_surf`
- `trans_type_erase_simple_surf_ty`
- `simple_surface_type_co_ref_contra_ref`
- `simple_const_translation_exists`
- `simple_var_translation_exists`
- `simple_literal_translation_exists`
- `existence_of_type_coercion`
- `completeness_of_reference_coercion`
- `completeness_of_ref_to_dref_coercion`
- `completeness_of_dref_coercion`
- `simple_source_translation_preserves_co_ref`
- `simple_source_and_translation_types_agree`

## Assumptions, Axioms, and Open Results

The development is intentionally not axiom-free. The thesis also presents the current state as mixed: definitions are formalised, internal type safety is the strongest layer, semantic entailment is treated as an abstraction boundary, and translation completeness remains open.

### Axioms in `entails_inter.v`

```coq
entails_hypothesis
entails_weakening
entails_subst_base
entails_subst_set
entails_equality
entails_drop_unused
entails_store_update_refinement
entails_const_step
entails_imp_refl
entails_modus_ponens
```

These axiomatize the semantic consequence layer and propositional principles used by refinement reasoning.

### Axiom in `foundational_lemmas_inter.v`

```coq
has_type_subst_base_closed_pure_ctx
```

This packages a difficult base-substitution typing case.

### Axiom in `type_safety_lemmas_inter.v`

```coq
preservation_left_stepctx_assumption
```

This isolates an evaluation-context preservation side condition.

### Axioms in `translation_soundness_lemmas.v`

```coq
soundness_of_sim_type_coercion
soundness_of_translation_fun_case
soundness_of_translation_if_pure_case
```

These cover hard translation/coercion soundness cases.

### Admitted theorem in `translation_completeness_lemmas.v`

```coq
paper_theorem_8_translation_completeness
```

This is the main open completeness theorem for the simple source fragment. `paper_theorem_3_translation_completeness` directly reuses it.

## How to Read the Formalisation

Suggested reading order:

1. `src/syntax.v`
   - Read this first to understand the split between internal and surface syntax.
2. `src/machine_inter.v`
   - Read `value`, `eval_ctx`, `plug`, `step`, and `eval`.
3. `src/entails_inter.v`
   - Understand that refinement entailment is evaluation to `EBool true`, plus an axiomatic interface.
4. `src/semantic_rules_inter.v`
   - Read `has_type_pure`, `ty_valid`, `subtype`, and `has_type`.
5. `src/semantic_rules_surf.v`
   - Read the surface pure/valid judgments and the structural translation functions.
6. `src/type_directed_translation.v`
   - Read `mode`, `coerce`, `ty_meet`, `ty_join`, and `has_type_surf`.
7. Test files:
   - `machine_inter_tests.v`
   - `semantic_rules_inter_tests.v`
   - `type_directed_translation_tests.v`
8. `src/foundational_lemmas_inter.v`
   - Do not read this linearly at first. Follow the paper-lemma comment markers and the groups listed above.
9. `src/type_safety_lemmas_inter.v`
   - Read the canonical-forms section, then preservation, then progress, then `paper_theorem_1_type_safety`.
10. `src/translation_soundness_lemmas.v`
    - Read context translation, pure translation, validity/subtyping preservation, coercion soundness, and `soundness_of_translation`.
11. `src/translation_completeness_lemmas.v`
    - Read the simple-fragment definitions first, then the coercion-existence lemmas, and finally the admitted completeness theorem.

Entry-point table:

| Goal | Start with |
|---|---|
| Syntax and object language | `syntax.v` |
| Internal evaluation | `machine_inter.v` |
| Refinement entailment | `entails_inter.v` |
| Internal typing and subtyping | `semantic_rules_inter.v` |
| Surface language | `semantic_rules_surf.v` |
| Dynamic references | `semantic_rules_surf.v`, then `type_directed_translation.v` |
| Type-directed translation | `type_directed_translation.v` |
| Internal type safety | `type_safety_lemmas_inter.v` |
| Translation soundness | `translation_soundness_lemmas.v` |
| Translation completeness status | `translation_completeness_lemmas.v` |
| Examples | the three `*_tests.v` files |
| Trusted assumptions | search for `Axiom` and `Admitted` |

## Development Notes

### Naming conventions

- Internal types and expressions use `T...` and `E...` constructors:
  - `TBase`, `TSet`, `TArrDep`
  - `ENat`, `EVar`, `EFix`, `EFail`
- Surface types and expressions use `Ty...` and `Ex...` constructors:
  - `TyBase`, `TySet`, `TyDeRef`
  - `ExNat`, `ExVar`, `ExDeRef`, `ExGetDep`
- Surface wrapper constructs use:
  - `EAssert`
  - `ESimple`
  - `EDep`
- Translation constructors use the prefix `AT`.
- Coercion constructors use the prefix `C`.
- Meet and join constructors use the prefixes `Meet` and `Join`.
- Weakening lemmas use the prefix `weakening_`.
- Substitution lemmas use prefixes such as `subst_base_` and `subst_nonbase_`.
- Runtime invariant lemmas mention `store_well_typed`, `runtime_ctx_well_typed`, or `state_ok`.

### Common proof patterns

The development repeatedly uses:

- induction or dependent induction over typing, subtyping, step, and evaluation derivations;
- explicit context algebra with `add_ctx_assoc`, `add_ctx_empty_l`, `add_ctx_empty_r`, and `add_ctx_ctx_add_*`;
- `stdpp` finite-map lemmas such as `lookup_insert`, `lookup_insert_ne`, `lookup_union`, `lookup_union_Some_l`, `map_eq`, and `fmap_insert`;
- inversion on typing derivations for canonical forms;
- explicit freshness and free-variable reasoning with `free_exp_vars`, `free_ty_vars`, `remove_string`, `fresh_string_list`, and `existsb (String.eqb x)`;
- splitting preservation into expression-typing preservation and store/runtime-context preservation;
- treating semantic entailment as evaluation to `EBool true` while relying on the `entails_inter.v` axiomatic interface.

### Important modelling choices

The formalisation deliberately makes several paper-level implicit assumptions explicit:

- the internal context packages variables, constants, and store information together;
- references are handled by a runtime store component inside `ctx`;
- `EFail` is an internal expression and is typed at any valid type;
- dynamic references are not primitive internal references, but are encoded as getter/setter pairs;
- semantic entailment is a relation over internal expressions and machine evaluation;
- substitution through expressions, types, and contexts is explicit and technically central;
- the translation layer and internal type-safety layer should be read separately, because they have different proof statuses.

## Current Status Summary

| Component | Status |
|---|---|
| Internal and surface syntax | Formalised. |
| Internal small-step semantics | Formalised. |
| Internal pure typing, validity, subtyping, and full typing | Formalised. |
| Surface pure typing, validity, and subtyping | Formalised. |
| Type-directed translation and coercions | Formalised. |
| Internal preservation/progress/type safety | Present, but relies on stated axioms. |
| Semantic entailment | Axiomatic interface over evaluation to `true`. |
| Translation soundness | Present, with several axiomatized hard cases. |
| Translation completeness | Main theorem `paper_theorem_8_translation_completeness` currently `Admitted`. |
| Big-step semantics | Archived/commented out; not active. |
| Tests/examples | Present for the machine, internal semantic rules, and type-directed translation. |
