# Proof status: forward Parikh theorem and exact finite witness

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #14](https://github.com/focs-lab/parikh-theorem/pull/14)
have merged, with CI passing.

Current milestone: [PR #15](https://github.com/focs-lab/parikh-theorem/pull/15),
forward Parikh theorem and exact finite witness, branch `codex/forward-parikh`,
based on merged `main` (`eb4699fcc65fabe3050ca9a2a50554c1c374494a`).
CI evidence is recorded in the PR.
There are **8 direct `sorry` obligations**, zero project axioms, and 8 declarations
transitively dependent on `sorryAx`, down from 11. The forward theorem is proved;
converse/regular realization, executable construction, and quantitative bounds remain.

## Completed in this milestone

Three accepted public contracts now have checked proofs:

| Declaration (namespace `Parikh`) | Result |
| --- | --- |
| `grammar_image` | A Mathlib grammar's Parikh image is semilinear (`thm:parikh-statement`). |
| `grammar_witness` | An exact finite indexed witness exists for that image (`thm:main`). |
| `contextFree_image` | Every Mathlib context-free language has a semilinear Parikh image. |

Their statements are unchanged and removed from both unresolved allowlists.
They require a finite terminal alphabet but impose no finite or decidable-equality
hypothesis on the grammar's ambient nonterminal type.

Three new, immediately proved adapters in `FiniteRepresentation.lean` complete
the finite-union argument:

| Declaration (namespace `Parikh`) | Role |
| --- | --- |
| `bases_finite` | Simple complete start trees are a subset of the bounded active-open family, using `simple_height`. |
| `bounded_cycles_finite` | A cycle's sole hole is active because its matching root belongs to production support; the bounded active-open family covers all bounded cycles. |
| `treeRepresentation_isSemilinearSet` | The finite base family and the finite powerset of cycles, filtered by activation, give the exact component union; Mathlib finite-union closure proves semilinearity. |

The finite-union proof converts the two finite sets to finsets, retaining actual
context syntax as indices. The union is exactly `treeRepresentation`, including
empty context sets, zero periods, and distinct contexts with equal weights.
`component_isLinearSet` and Mathlib's `IsSemilinearSet.biUnion_finset` supply
linearity and finite-union closure. `treeRepresentation_eq` gives the public
forward theorem. The already proved `exists_witness` bridge gives the exact
finite witness, and unpacking Mathlib's context-free grammar witness gives the
language-level specialization. No quantitative-bound obligation is used.

All six audited declarations depend only on standard Lean foundations:
`propext`, `Classical.choice`, and `Quot.sound`. None depends on `sorryAx`
or a project axiom. All existing definitions, instances, syntax, statistics,
and previously completed proofs are retained.

All **522 prior contract entries** are preserved exactly. The three proved
adapters and five generated equation/simplification declarations extend the
manifest to **530 entries**, including the generated equation for the existing
`treeRepresentation` definition. No previous declaration is deleted or moved.
The checker, immutable baseline, existing signatures and definition meanings,
instances, and Lean/Mathlib pins are unchanged. The only new import is the
project's `FiniteRepresentation` module; no Mathlib import or cache target changes.

The exact witness is established by classical existence. It is not an executable
compiler, nor does this milestone prove the stated quantitative bounds.

## Previously completed

- [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3): `counts_append`, `component_isLinearSet`, `witness_isSemilinearSet`, and `exists_witness`, with `Component.denotation_eq_vadd_closure` (`eq:word-add`, `sec:statement`).
- [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4): `derives_iff_tree` and seven supporting frontier/derivation lemmas (`prop:tree-word`, `app:derivations`).
- [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5): `plugging` and four supporting validity/root, size, count, and support lemmas (`lem:plug`).
- [PR #6](https://github.com/focs-lab/parikh-theorem/pull/6): `insertion_enabled`, `insertion_accounting`, and three supporting occurrence/context lemmas (`lem:enabled`, `lem:insertion-laws`).
- [PR #7](https://github.com/focs-lab/parikh-theorem/pull/7): `first_occurrences`, `positive_multiplicities`, and three abstract support/list lemmas (`lem:first-occurrence`, `lem:multiplicities`).
- [PR #8](https://github.com/focs-lab/parikh-theorem/pull/8): `Cycle.root_mem_support`, `InsertionSequence.accounting`, `activationOrder_iff_insertionSequence`, and `ContextsActivatable.realize` (`eq:cycle-root`, `cor:sequence`, `lem:activation-realize`, `eq:activated-wt`, `eq:activated-supp`).
- [PR #9](https://github.com/focs-lab/parikh-theorem/pull/9): `one_linear`, with `contextComponent.mem_denotation_iff` (`prop:one-linear`, `eq:one-linear`, `eq:component`).
- [PR #10](https://github.com/focs-lab/parikh-theorem/pull/10): `complete_support_active`, `simple_height`, `Valid.support_active`, `ParseTree.labelPath_subset_support`, and `ParseTree.exists_labelPath_height` (`def:statistics`, `lem:simple-height`).
- [PR #11](https://github.com/focs-lab/parikh-theorem/pull/11): `bounded_open_finite`, with finite-list and explicit-height adapters kept inside its proof (`lem:finite`).

- [PR #12](https://github.com/focs-lab/parikh-theorem/pull/12): `bounded_cut` and five structural adapters for minimal non-simple subtrees, height, production count, and reversible indexed replacement (`lem:cut`).

- [PR #13](https://github.com/focs-lab/parikh-theorem/pull/13): `decomposition` and `InsertionSequence.append`, by strong induction on production count and exact bounded-context reinsertion (`thm:decomposition`, `eq:decomposition`).

- [PR #14](https://github.com/focs-lab/parikh-theorem/pull/14): `treeRepresentation_eq` and `InsertionSequence.contextsActivatable`, proving exact equality with the grammar Parikh image while retaining actual context identities (`thm:main`, `eq:main`).

Their statements and proofs are unchanged here. The grammar/tree bridge supports
arbitrary derivation order and nonterminal types. Witness existence and tree
semantics are semantic proofs, not executable compiler implementations.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- Affected modules and full `lake build` pass, with only expected theorem-hole warnings in the 8 remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. New witness examples distinguish an unproductive grammar's empty denotation from a grammar deriving the empty word over an empty terminal alphabet, whose exact witness contains the zero vector. Both have infinite ambient nonterminals; the empty-language example also exercises `contextFree_image`. Existing grammar/tree, silent cycles, distinct equal-weight contexts, activation, finiteness, decomposition, and exact equality examples still pass.
- `python3 scripts/check-contracts.py` checks 530 declarations against the accepted skeleton and merged `main`, preserving all 522 earlier contracts. The checker and baseline pointer are unchanged.
- `#print axioms` for the three public theorems and three finiteness/union adapters reports only standard foundations, with no unresolved dependencies.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 8 outstanding holes. Full project completion still requires converse/regular realization, algorithms, and bounds.
- Cloud Lean 4.34.1 / Lake 5.0.0, the pinned dependencies and selected Mathlib cache, and GitHub authentication/read/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible work: representative-word counting (`representative_counts`), then
correctness and DFA-regularity of the witness expression (`witnessExpression_correct`),
feeding `converse` and `regular_realization`. Executable algorithms with checked
correctness and the quantitative bounds remain separately tracked. Keep accepted
contracts unchanged and publish each coherent increment as a new PR.
