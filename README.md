# DTDT Formal Semantics

A Coq formalisation of a concrete reconstruction of the system from **Dynamic Typing with Dependent Types** by Ou et al.

The project makes the paper's semantic core explicit and machine-checkable. It separates the development into two object-language layers:

- **Internal language**: core static semantics, semantic subtyping, references, small-step operational semantics, runtime store, and internal `fail`.
- **Surface language**: programmer-facing constructs such as `assert`, `simple`, `dependent`, and dynamic references, translated into the internal language.

The central idea is that refinement and dependency information that is not statically available can be recovered through **type-directed translation** and **coercions**. In simple mode, translation may insert runtime checks; in dependent mode, more information is kept statically when possible.

The strongest mechanised part is the **internal language type-safety layer**: preservation, progress, and the final type-safety theorem are present in Coq. The translation layer is also formalised, but some hard soundness cases are axiomatized, and the main translation-completeness theorem is currently `Admitted`.

## What is formalised?

The repository contains:

- syntax for the internal and surface languages;
- pure expressions used inside refinements;
- internal type validity, typing, and semantic subtyping;
- surface validity, pure typing, and surface subtyping;
- small-step dynamic semantics over `(context, expression)` configurations;
- type-directed translation from surface expressions to internal expressions;
- coercions, dependency erasure, and dynamic-reference encoding;
- internal type safety;
- partial soundness and completeness metatheory for translation.

The logical Coq namespace is `DTDT`, so imports look like:

```coq
Require Import DTDT.syntax.
Require Import DTDT.machine_inter.
Require Import DTDT.semantic_rules_inter.
```

## Requirements

The intended environment is:

- Coq 8.20
- `coq-stdpp`
- `opam`
- `make`
- UTF-8 source support

The files use Unicode identifiers and notations such as `Γ`, `τ`, `⊢`, `≤`, `↠*`, and `⊨`.

The development imports `stdpp` modules including:

```coq
From stdpp Require Export base.
From stdpp Require Export strings.
From stdpp Require Export gmap.
From stdpp Require Import stringmap.
From stdpp Require Import fin_maps.
```

A typical compatible setup is Coq 8.20 with a Coq-8.20-compatible `coq-stdpp`.

## Build

Clone the repository:

```sh
git clone https://github.com/merthb/DTDT-Formal-Semantics.git
cd DTDT-Formal-Semantics
```

Create an opam switch:

```sh
opam update
opam switch create dtdt-coq-8.20 ocaml-base-compiler.4.14.1
eval $(opam env --switch=dtdt-coq-8.20)
```

Install Coq and dependencies:

```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq.8.20 coq-stdpp
```

Build the development:

```sh
make
```

For a parallel build:

```sh
make -j$(nproc)
```

On macOS:

```sh
make -j$(sysctl -n hw.ncpu)
```

If files are added, removed, or reordered, regenerate the build files:

```sh
coq_makefile -f _CoqProject -o Makefile
make clean
make
```

For early files, direct `coqc` calls are also possible:

```sh
coqc -Q src DTDT src/syntax.v
coqc -Q src DTDT src/machine_inter.v
```

For later files in the dependency chain, prefer `make`, since `_CoqProject` records the intended compilation order.

## Repository layout

| Path | Role |
|---|---|
| `_CoqProject` | Declares `-Q src DTDT` and the active build order. |
| `Makefile` | Generated build file, normally used through `make`. |
| `Makefile.conf` | Generated configuration fragment from `coq_makefile`. |
| `README.md` | Project overview, build guide, and proof-status summary. |
| `src/` | Coq source files. |

The active build order is:

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

`src/big_step_eval_inter.v` is archived reference material and is not part of the active build.

## Source files

### `src/syntax.v`

Defines the syntax of both language layers and the context representations.

Main definitions:

- base types: `BaseT`, `BString`, `BBool`, `BNat`, `BUnit`
- semantic interpretation of base types: `base_to_set`
- internal syntax: `i_ty`, `i_expr`
- internal contexts: `var_context`, `const_context`, `store_context`, `ctx`
- internal context operations: `empty_ctx`, lookups, `ctx_add_*`, `add_ctx`
- surface syntax: `ty`, `expr`
- surface contexts and operations: `ctx_surf`, `empty_ctx_surf`, surface lookups, `ctx_add_*_surf`

Internal types include:

```text
TBase
TSet
TArr
TArrDep
TProd
TRef
```

Surface types include ordinary type forms plus:

```text
TyDeRef
```

Surface expressions include the internal-style constructs plus:

```text
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

- `var_dom`, `store_dom`
- `value`, `base_value`
- `eval_ctx`, `plug`
- `base_eq`
- `expr_subst`, `ty_subst`, `expr_subst_fun`
- `step`, `eval`

The machine state is:

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

Values are indexed by the current context: constants, variables, and locations count as values only when they are present in the corresponding context component.

Reduction rules cover evaluation contexts, constants, variables, fixpoints, projections, conditionals, references, failure propagation, Boolean operations, equality, and addition.

### `src/big_step_eval_inter.v`

Archived reference material. The file sketches an older big-step evaluator but is commented out and removed from the active build/dependency chain.

Use `machine_inter.v` for the current operational semantics.

### `src/entails_inter.v`

Defines semantic entailment for internal predicates.

Main definitions:

- `entails`
- notation `Γ ⊨ e`
- `binding_subst`
- `ctx_subst`

The core definition is:

```coq
Definition entails (Γ : ctx) (e : i_expr) : Prop :=
  (Γ, e) ↠* (Γ, EBool true).
```

The file also gives an axiomatic interface for semantic consequence. These axioms serve as an abstraction boundary for refinement reasoning.

Axioms:

```text
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

Proved lemmas include:

```text
entails_true
entails_not_false
entails_weaken_right
```

### `src/semantic_rules_inter.v`

Defines the internal static semantics.

Core judgments:

```coq
Γ ⊢pure e : τ
Γ ⊢valid τ
Γ ⊢ τ₁ ≤ τ₂
Γ ⊢ e : τ
```

The four central relations are:

1. `has_type_pure` — pure typing
2. `ty_valid` — type validity
3. `subtype` — semantic subtyping
4. `has_type` — full internal typing

The pure fragment is the subset allowed inside refinements. It includes base literals, suitable variables and constants, pure applications, Boolean connectives, equality, and addition.

Full internal typing covers literals, variables, constants, locations, `EFail`, dependent and non-dependent recursive functions, pure and impure application, arithmetic and Boolean operations, references, products, projections, conditionals, selfification, and subsumption.

Important runtime invariant:

```text
runtime_ctx_well_typed
```

### `src/semantic_rules_surf.v`

Defines surface-language static infrastructure and the non-type-directed parts of translation.

Important judgments and translations:

```coq
Γ ⊢ₛpure e : τ
Γ ⊢ₛvalid τ
⟦ τ ⟧
⟦ Γ ⟧c
```

Dynamic references are encoded internally as getter/setter pairs:

```coq
Definition dref_encoding (τ : i_ty) : i_ty :=
  TProd (TArr (TBase BUnit) τ) (TArr τ (TBase BUnit)).
```

`trans_expr_partial` handles the dref-free fragment. Source-only dynamic-reference constructs are handled later by type-directed translation.

### `src/type_directed_translation.v`

Defines type-directed translation and coercion machinery.

Main definitions include:

- modes: `sim`, `dep`
- dynamic-reference operations: `dget`, `dset`, `pack_dref`
- dependency erasure: `erase_dep_var`, `erase_i_ty`
- reference variance helpers: `co_ref`, `contra_ref`, `co_ref_ty`, `contra_ref_ty`
- coercions: `coerce`
- type meet and join: `ty_meet`, `ty_join`
- translation judgment: `has_type_surf`

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

```text
CSub
CBase
CFunCo
CFunContNonDep
CFunContDep
CFunEraseDep
CPair
CRefToDRef
CDRef
```

Type-directed translation constructors cover literals, constants, variables, functions, applications, products, references, dynamic references, conditionals, and mode/control constructs such as `ATAssert`, `ATDynamic`, and `ATStatic`.

### `src/foundational_lemmas_inter.v`

Large support library for the internal metatheory.

It proves context algebra, lookup preservation, weakening, pure-to-internal typing, free-variable facts, subtyping support, substitution lemmas, inversion lemmas, context/store facts, freshness facts, and evaluation-context support.

Important groups include:

| Group | Examples |
|---|---|
| Context algebra | `option_union_assoc`, `add_ctx_empty_l`, `add_ctx_empty_r`, `add_ctx_assoc` |
| Lookup preservation | `lookup_lemma_const`, `lookup_lemma_var`, `lookup_lemma_store_right` |
| Weakening | `weakening_entails_right`, `weakening_ty_valid`, `weakening_subtype`, `weakening` |
| Pure-to-internal typing | `has_type_pure_implies_has_type`, `pure_implies_internal_typing` |
| Selfification/reference inversion | `ref_type_origin`, `self_ref_inv`, `self_pair_inv`, `inversion_ref` |
| Free-variable lemmas | `free_var_pure_is_base_typed`, `has_type_pure_empty_ctx_closed` |
| Substitution | `subst_base_*`, `subst_nonbase_*` |
| Evaluation support | `eval_trans`, `eval_plug`, `pure_subst_step_eval` |
| Step lemmas | `step_lemma_entails`, `step_lemma_ty_valid`, `step_lemma_has_type_bool_singleton` |

Trusted assumption:

```coq
Axiom has_type_subst_base_closed_pure_ctx
```

### `src/type_safety_lemmas_inter.v`

Contains the internal type-safety proof development.

Important definitions:

```text
compose_eval_ctx
no_var_bindings
no_const_bindings
state_ok
```

Main theorem names:

```coq
Theorem preservation_typed_store
Theorem preservation
Theorem progress_ok
Theorem progress
Theorem paper_theorem_1_type_safety
```

Proof structure:

1. pure-term preservation;
2. canonical forms for Booleans, products, references, and functions;
3. per-step preservation lemmas for operational rules;
4. preservation for expression typing and store/runtime-context typing;
5. progress;
6. final internal type-safety theorem.

Trusted assumption:

```coq
Axiom preservation_left_stepctx_assumption
```

### `src/translation_soundness_lemmas.v`

Contains soundness results for translating surface syntax and coercions into internal syntax.

Important groups:

| Group | Examples |
|---|---|
| Surface context translation | `trans_ctx_surf_lookup_var`, `trans_ctx_surf_lookup_const` |
| Essential/simple type translation | `trans_type_essential_type`, `is_simple_type_surf_trans` |
| Pure translation | `trans_expr_partial_pure_sound`, `pure_surface_translation_sound` |
| Free-variable preservation | `free_var_translation_subsets` |
| Validity/subtyping preservation | `trans_type_preserves_validity`, `trans_type_preserves_subtype_surf` |
| Erasure support | `erase_dep_var_preserves_validity`, `subtype_type_match_helper` |
| Coercion soundness | `soundness_of_dep_type_coercion`, `soundness_of_type_coercion` |
| Translation soundness | `soundness_of_translation` |
| Reference/dref soundness | `soundness_of_reference_coercion`, `soundness_of_dref_coercion` |

Main theorem:

```coq
Theorem soundness_of_translation
```

It states that if a surface expression has a type-directed translation, then the generated internal expression is well typed in the translated context.

Trusted assumptions:

```coq
Axiom soundness_of_sim_type_coercion
Axiom soundness_of_translation_fun_case
Axiom soundness_of_translation_if_pure_case
```

### `src/translation_completeness_lemmas.v`

Contains the current completeness-side development for the simple surface fragment.

Important definitions:

```text
co_ref_vars_surf
co_ref_consts_surf
simple_surface_type
erase_simple_surf_ty
has_type_simple_surf
```

Important results include:

| Item | Main names |
|---|---|
| Type matching | `simple_type_match_subtype`, `simple_type_match_coercion`, `simple_type_match_ref` |
| Simple types | `simple_surface_type`, `erase_simple_surf_ty`, `simple_surface_type_valid_surf` |
| Erasure infrastructure | `erase_i_ty_idempotent`, `ty_meet_preserves_erase` |
| Simple surface typing | `has_type_simple_surf`, `has_type_simple_surf_valid` |
| Translation existence | `simple_const_translation_exists`, `simple_var_translation_exists`, `simple_literal_translation_exists` |
| Coercion existence | `existence_of_type_coercion`, `completeness_of_reference_coercion`, `completeness_of_dref_coercion` |
| Translation/type agreement | `simple_source_translation_preserves_co_ref`, `simple_source_and_translation_types_agree` |

Main theorem names:

```coq
Theorem paper_theorem_8_translation_completeness
Theorem paper_theorem_3_translation_completeness
```

`paper_theorem_8_translation_completeness` is currently `Admitted`.

`paper_theorem_3_translation_completeness` is a restatement proved by:

```coq
exact paper_theorem_8_translation_completeness.
```

## Tests and examples

### `src/machine_inter_tests.v`

Examples for the internal machine and references, including:

```text
machine_ref_ctx
machine_ref_update_fun
eval_if_get_set_test
eval_app_with_store_effect_test
rewards_ctx
rewards_points_lookup
rewards_member_lookup
award_bonus_fun
award_bonus_program
eval_award_bonus_program_test
```

### `src/semantic_rules_inter_tests.v`

Examples for internal typing, pure typing, refinement subtyping, and reference typing, including:

```text
var_lookup_add
var_lookup_add_ne
pure_nat_ctx
ref_nat_ctx
ref_inspecting_fun
pure_guarded_arithmetic_test
subtype_refinement_implication_test
has_type_reference_conditional_test
has_type_reference_inspecting_function_test
```

### `src/type_directed_translation_tests.v`

Examples for coercions, dynamic references, conditionals, and impure application, including:

```text
surf_newref_nat_expr
inter_newref_nat_expr
inter_dref_nat_expr
surf_dref_if_nat_expr
inter_dref_if_nat_expr
surf_dref_set_if_unit_expr
inter_dref_set_if_unit_expr
surf_const_dep_fun_nat_expr
surf_impure_app_ctx
erased_dep_fun_var_term
coerce_newref_nat_to_dref_example
has_type_surf_deref_nat_example
has_type_surf_dref_if_nat_test
has_type_surf_dref_set_if_unit_test
has_type_surf_app_impure_nat_test
```

## Assumptions, axioms, and open results

The development is intentionally not axiom-free. It treats semantic entailment as an abstraction boundary, proves the strongest results for the internal language, and leaves translation completeness open.

### Entailment axioms

In `src/entails_inter.v`:

```text
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

### Foundational assumption

In `src/foundational_lemmas_inter.v`:

```coq
has_type_subst_base_closed_pure_ctx
```

This packages a difficult closed/pure base-substitution typing case.

### Type-safety assumption

In `src/type_safety_lemmas_inter.v`:

```coq
preservation_left_stepctx_assumption
```

This isolates an evaluation-context preservation side condition.

### Translation-soundness assumptions

In `src/translation_soundness_lemmas.v`:

```coq
soundness_of_sim_type_coercion
soundness_of_translation_fun_case
soundness_of_translation_if_pure_case
```

These cover hard translation/coercion soundness cases.

### Open completeness theorem

In `src/translation_completeness_lemmas.v`:

```coq
paper_theorem_8_translation_completeness
```

This is the main open completeness theorem for the simple source fragment. `paper_theorem_3_translation_completeness` directly reuses it.

## How to read the formalisation

Suggested reading order:

1. `src/syntax.v` — internal and surface syntax.
2. `src/machine_inter.v` — `value`, `eval_ctx`, `plug`, `step`, and `eval`.
3. `src/entails_inter.v` — entailment as evaluation to `EBool true`, plus the axiomatic interface.
4. `src/semantic_rules_inter.v` — `has_type_pure`, `ty_valid`, `subtype`, and `has_type`.
5. `src/semantic_rules_surf.v` — surface pure/valid judgments and structural translation.
6. `src/type_directed_translation.v` — `mode`, `coerce`, `ty_meet`, `ty_join`, and `has_type_surf`.
7. Test files — examples for the machine, semantic rules, and translation.
8. `src/foundational_lemmas_inter.v` — use the grouped lemma structure; do not read it linearly at first.
9. `src/type_safety_lemmas_inter.v` — canonical forms, preservation, progress, then `paper_theorem_1_type_safety`.
10. `src/translation_soundness_lemmas.v` — context translation, pure translation, validity/subtyping preservation, coercion soundness, and `soundness_of_translation`.
11. `src/translation_completeness_lemmas.v` — simple-fragment definitions, coercion-existence lemmas, and the admitted completeness theorem.

Entry points by topic:

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

## Development notes

### Naming conventions

- Internal types and expressions use `T...` and `E...` constructors:
  - `TBase`, `TSet`, `TArrDep`
  - `ENat`, `EVar`, `EFix`, `EFail`
- Surface types and expressions use `Ty...` and `Ex...` constructors:
  - `TyBase`, `TySet`, `TyDeRef`
  - `ExNat`, `ExVar`, `ExDeRef`, `ExGetDep`
- Surface wrapper constructs: `EAssert`, `ESimple`, `EDep`
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
- preservation split into expression-typing preservation and store/runtime-context preservation;
- semantic entailment as evaluation to `EBool true`, supported by the axiomatic interface in `entails_inter.v`.

### Important modelling choices

The formalisation makes several paper-level implicit assumptions explicit:

- the internal context packages variables, constants, and store information together;
- references are represented by a runtime store component inside `ctx`;
- `EFail` is internal and is typed at any valid type;
- dynamic references are encoded as getter/setter pairs, not as primitive internal references;
- semantic entailment is a relation over internal expressions and machine evaluation;
- substitution through expressions, types, and contexts is explicit and technically central;
- the translation layer and internal type-safety layer should be read separately, because they have different proof statuses.

## Current status

| Component | Status |
|---|---|
| Internal and surface syntax | Formalised |
| Internal small-step semantics | Formalised |
| Internal pure typing, validity, subtyping, and full typing | Formalised |
| Surface pure typing, validity, and subtyping | Formalised |
| Type-directed translation and coercions | Formalised |
| Internal preservation/progress/type safety | Present, relying on stated axioms |
| Semantic entailment | Axiomatic interface over evaluation to `true` |
| Translation soundness | Present, with several axiomatized hard cases |
| Translation completeness | Main theorem `paper_theorem_8_translation_completeness` currently `Admitted` |
| Big-step semantics | Archived/commented out; not active |
| Tests/examples | Present for the machine, internal semantic rules, and type-directed translation |

## Reference

This repository formalises the extended dependently typed lambda calculus described in:

- **Dynamic Typing with Dependent Types**, Ou et al.
