# Proof status: exact tree-representation equality

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #13](https://github.com/focs-lab/parikh-theorem/pull/13)
have merged, with CI passing.

Current milestone: exact tree-representation equality, branch
`codex/tree-representation-equality`, based on merged `main`
(`cdf98728a37fac9910a8fd9f3babe22e3df8e74c`). Publication and CI evidence will
be recorded in the PR.
There are **11 direct `sorry` obligations**, zero project axioms, and 11 declarations
transitively dependent on `sorryAx`, down from 12. The forward semilinearity and
finite-witness contracts remain unproved.

## Completed in this milestone

`Parikh.treeRepresentation_eq` (`thm:main`, `eq:main`) now identifies the exact
union of activatable tree/context components with the Mathlib grammar's Parikh
image. Both inclusions are proved. Its existing statement is unchanged and
removed from both unresolved allowlists. No finite or decidable-equality
hypothesis is added for the grammar's ambient nonterminal type.

For a represented vector, `one_linear` realizes it with an insertion sequence
from the selected simple complete start tree. Sequence accounting preserves
completeness and the start root. `derives_iff_tree` and Mathlib's
`ContextFreeGrammar.mem_language_iff` place the resulting yield in the grammar
language, with exactly the represented counts.

Conversely, a generated word gives a complete start tree by the same semantics
bridge. `decomposition` supplies a simple base and a bounded-context sequence.
The new `InsertionSequence.contextsActivatable` adapter certifies that the set
of distinct contexts in this sequence is activatable. It extracts matching
cycles from the insertion steps, selects their roots locally by classical
choice, reuses `activationOrder_iff_insertionSequence`, and applies
`first_occurrences`. `List.mem_toFinset` retains precisely the contexts used,
including distinct contexts with equal or zero weights. `one_linear` then places
the original tree's exact weight in the corresponding component.

Both audited declarations depend only on standard Lean foundations:
`propext`, `Classical.choice`, and `Quot.sound`. Neither depends on `sorryAx`
or a project axiom. All existing definitions, instances, syntax, statistics,
and previously completed proofs are retained.

All **521 prior contract entries** are preserved exactly. The single proved
activation adapter extends the manifest to **522 entries**. No previous declaration
is deleted or moved. The checker, immutable baseline, existing signatures and
definition meanings, instances, and Lean/Mathlib pins are unchanged. No additional
Mathlib import or cache dependency is required.

This proves exact equality. Semilinearity and finite witness construction still
require the bounded-family finiteness argument. Classical existence proofs do
not provide executable enumeration, activation testing, or compilation.

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
| Statements | `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- Affected modules and full `lake build` pass, with only expected theorem-hole warnings in the 11 remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. New equality examples distinguish a grammar with no productions (empty representation) from an empty-alphabet grammar deriving the empty word (exactly the zero vector), both over infinite ambient nonterminals. Existing zero-weight cycles, equal-weight distinct contexts, positional insertion, activation order, finiteness, and decomposition examples still pass.
- `python3 scripts/check-contracts.py` checks 522 declarations against the accepted skeleton and merged `main`, preserving all 521 earlier contracts. The checker and baseline pointer are unchanged.
- `#print axioms` for `treeRepresentation_eq` and `InsertionSequence.contextsActivatable` reports only standard foundations, with no unresolved dependencies.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 11 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0, the pinned dependencies and selected Mathlib cache, and GitHub read/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible milestone: `grammar_image`, `grammar_witness`, and
`contextFree_image`, deriving the forward semilinearity and exact finite witness
from `treeRepresentation_eq`, bounded-family finiteness, and the proved
counting/witness bridges. Keep accepted contracts unchanged and publish a new PR.
