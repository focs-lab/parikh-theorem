# Proof status: activation orders realized by tree insertion sequences

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
The counting/witness [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3),
grammar/tree semantics [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4),
one-hole plugging [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5),
insertion [PR #6](https://github.com/focs-lab/parikh-theorem/pull/6),
and abstract activation [PR #7](https://github.com/focs-lab/parikh-theorem/pull/7)
have merged, with CI passing.

Current milestone: insertion-sequence accounting and tree realization of activation, branch
[`codex/activation-tree-realization`](https://github.com/focs-lab/parikh-theorem/tree/codex/activation-tree-realization),
based on merged `main` (`c2aa4e7a5673704b9d59543a9110dfae9b1c11ed`).
There are **18 direct `sorry` obligations**, zero project axioms, and 18 declarations
transitively dependent on `sorryAx`. Parikh's theorem is not yet proved.

## Completed in this milestone

All names have namespace `Parikh`. Source: `eq:cycle-root`, `cor:sequence`,
`lem:activation-realize`, `eq:activated-wt`, and `eq:activated-supp`.

| Declaration | Proof / role |
| --- | --- |
| `Cycle.root_mem_support` | A nontrivial cycle's root is a production-node label in its support, rather than a hole label. |
| `InsertionSequence.accounting` | A sequence from a complete base preserves completeness/root and exactly adds the listed weights/production counts and unions their supports. |
| `activationOrder_iff_insertionSequence` | A list of matching cycles is enabled exactly when it can be realized by a tree insertion sequence from the complete base. Repeats are allowed. |
| `ContextsActivatable.realize` | Each member of an activatable finite set is inserted once, with exact finite-set weight/support accounting, and remains enabled afterwards. |

These four theorems discharge source lemmas deliberately deferred from the
skeleton. They are proved immediately, with no new holes. The 18 named skeleton
obligations and their allowlists are unchanged. `one_linear` remains the next
major equality to prove.

Cycle-root support and sequence accounting live in `InsertionSequences.lean`;
the two realization adapters live in `Activation.lean`. All 457 earlier contract
entries are preserved exactly. Four proved declarations and six Lean-generated
proof/simplification helpers extend the manifest to 467 entries. No existing
declaration is removed, moved, or changed. Definition meanings, instances, and
Lean/Mathlib pins are unchanged; the only new import is the support module.

Sequence accounting is induction using the existing insertion identities. The
list/order correspondence uses enabledness for the next step and support
accounting for the remaining order. Its reverse direction extracts those same
facts from the sequence constructor. It retains cycle syntax and order, including
repeated cycles, and needs no finite nonterminal type or public equality instance.

The finite-set realization uses the witness already supplied by
`ContextsActivatable`. `List.sum_toFinset` changes the distinct list sum to the
finite-set sum. Cycle-root membership and final support accounting make every
selected cycle enabled again. The empty set, a terminal-rooted complete base,
empty productions, and zero-weight cycles are supported. This is a semantic
existence proof; it does not provide an executable compiler implementation.

All four new theorems have no `sorryAx` or project-axiom dependencies. Their
axiom audits report only standard Lean foundations: `propext`, `Classical.choice`,
and `Quot.sound`. All previously published hypotheses and statements are preserved.

## Previously completed

- [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3): `counts_append`, `component_isLinearSet`, `witness_isSemilinearSet`, and `exists_witness`, with `Component.denotation_eq_vadd_closure` (`eq:word-add`, `sec:statement`).
- [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4): `derives_iff_tree` and seven supporting frontier/derivation lemmas (`prop:tree-word`, `app:derivations`).
- [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5): `plugging` and four supporting validity/root, size, count, and support lemmas (`lem:plug`).
- [PR #6](https://github.com/focs-lab/parikh-theorem/pull/6): `insertion_enabled`, `insertion_accounting`, and three supporting occurrence/context lemmas (`lem:enabled`, `lem:insertion-laws`).
- [PR #7](https://github.com/focs-lab/parikh-theorem/pull/7): `first_occurrences`, `positive_multiplicities`, and three abstract support/list lemmas (`lem:first-occurrence`, `lem:multiplicities`).

Their statements and proofs are unchanged here. The grammar/tree bridge supports
arbitrary derivation order and nonterminal types. Witness existence and tree
semantics are semantic proofs, not executable compiler implementations.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| GrammarTrees | `complete_support_active`, `bounded_open_finite` |
| Decomposition | `simple_height`, `bounded_cut`, `decomposition` |
| Activation | `one_linear` |
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- `lake build Parikh.InsertionSequences`, `lake build Parikh.Activation`, and full `lake build` pass, with only expected theorem-hole warnings in remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. New examples realize a cycle that introduces the second cycle's required label, reject the reverse order, repeat a zero-weight cycle with exact production count, and verify that each selected cycle is enabled afterwards. Both cycles have the same zero weight but different roots; the nonterminal type is infinite (`ℕ`). An empty context set preserves a terminal-rooted base and its nonzero weight.
- `python3 scripts/check-contracts.py` checks 467 declarations against the accepted skeleton and merged `main`. All 457 earlier signatures and definition fingerprints are preserved. The checker and baseline pointer are unchanged.
- `#print axioms` for all four new theorems reports only standard foundations; none depends on unresolved obligations.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 18 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned Mathlib access, and GitHub authentication/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible milestone: the exact `one_linear` component equality
(`prop:one-linear`), using the proved counting, activation, and tree-realization
lemmas. Keep that increment in a new PR with the accepted statements unchanged.
