# Proof status: exact linear component for one activated context set

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
The counting/witness [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3),
grammar/tree semantics [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4),
one-hole plugging [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5),
insertion [PR #6](https://github.com/focs-lab/parikh-theorem/pull/6),
abstract activation [PR #7](https://github.com/focs-lab/parikh-theorem/pull/7),
and tree realization [PR #8](https://github.com/focs-lab/parikh-theorem/pull/8)
have merged, with CI passing.

Current milestone: the exact `one_linear` component equality, branch
[`codex/one-linear`](https://github.com/focs-lab/parikh-theorem/tree/codex/one-linear),
based on merged `main` (`ae109deebb2602a1511faf6e777afbf51b116108`).
There are **17 direct `sorry` obligations**, zero project axioms, and 17 declarations
transitively dependent on `sorryAx`, down from 18. Parikh's theorem is not yet proved.

## Completed in this milestone

All names have namespace `Parikh`. Source: `prop:one-linear`, `eq:one-linear`,
`eq:component-base`, and `eq:component`.

| Declaration | Proof / role |
| --- | --- |
| `one_linear` | The weights of insertion sequences using exactly the selected context set equal its linear component, with every selected context contributing once to the base. |
| `contextComponent.mem_denotation_iff` | A thin Mathlib adapter expressing the indexed-list denotation with independent natural coefficients for context identities. |

The existing `one_linear` statement is unchanged; its direct and transitive
unresolved status is removed from the named allowlists. The new adapter is proved
immediately and introduces no hole. Both declarations have no `sorryAx` or
project-axiom dependencies. Their audits report only standard Lean foundations:
`propext`, `Classical.choice`, and `Quot.sound`.

All 467 earlier contract entries are preserved exactly. One new proved adapter
and six Lean-generated equation/proof/simplification helpers extend the manifest
to 474 entries. The generated `contextComponent.eq_1` records the existing
concrete definition's equation. No existing declaration is deleted or moved.
All earlier signatures, definition meanings, instances, imports, and Lean/Mathlib
pins are unchanged.

For the forward inclusion, sequence accounting and
`Finset.sum_list_map_count` express the final weight using each context's count.
Every selected context occurs, so its count minus one is a natural coefficient;
the first copies supply the component base. For the reverse inclusion, add one
to each chosen coefficient, use `positive_multiplicities` to produce an enabled
order with those counts, and realize that order as an insertion sequence.

The coefficient adapter uses `Component.denotation_eq_vadd_closure`,
`AddSubmonoid.mem_closure_range_iff_of_fintype`, and `Finset.sum_coe_sort` to
reindex finite sums. Context syntax still determines membership, roots, and
support. Equal weights, zero weights, repeated contexts, empty context sets,
terminal-rooted bases, and infinite ambient nonterminal types are supported.
No new equality instance or finite-nonterminal hypothesis is public. These are
semantic proofs; executable compiler values remain separate work.

## Previously completed

- [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3): `counts_append`, `component_isLinearSet`, `witness_isSemilinearSet`, and `exists_witness`, with `Component.denotation_eq_vadd_closure` (`eq:word-add`, `sec:statement`).
- [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4): `derives_iff_tree` and seven supporting frontier/derivation lemmas (`prop:tree-word`, `app:derivations`).
- [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5): `plugging` and four supporting validity/root, size, count, and support lemmas (`lem:plug`).
- [PR #6](https://github.com/focs-lab/parikh-theorem/pull/6): `insertion_enabled`, `insertion_accounting`, and three supporting occurrence/context lemmas (`lem:enabled`, `lem:insertion-laws`).
- [PR #7](https://github.com/focs-lab/parikh-theorem/pull/7): `first_occurrences`, `positive_multiplicities`, and three abstract support/list lemmas (`lem:first-occurrence`, `lem:multiplicities`).
- [PR #8](https://github.com/focs-lab/parikh-theorem/pull/8): `Cycle.root_mem_support`, `InsertionSequence.accounting`, `activationOrder_iff_insertionSequence`, and `ContextsActivatable.realize` (`eq:cycle-root`, `cor:sequence`, `lem:activation-realize`, `eq:activated-wt`, `eq:activated-supp`).

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
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- `lake build Parikh.Activation` and full `lake build` pass, with only expected theorem-hole warnings in the 17 remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. Two distinct contexts with different roots but equal nonzero weights require at least two terminal contributions; every count at least two is realized, and smaller counts are rejected. The nonterminal type is infinite (`ℕ`). A zero-weight context gives exactly the zero vector, and an empty context set gives exactly a terminal-rooted base's nonzero weight.
- `python3 scripts/check-contracts.py` checks 474 declarations against the accepted skeleton and merged `main`. All 467 earlier signatures and definition fingerprints are preserved. The checker and baseline pointer are unchanged.
- `#print axioms` for `one_linear` and its new adapter reports only standard foundations; neither depends on unresolved obligations.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 17 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned Mathlib access, and GitHub authentication/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible milestone: active-support and simple-tree height bounds
(`complete_support_active`, `simple_height`), preparing the bounded-family,
bounded-cut, and decomposition proofs. Keep each increment in a new PR with
the accepted statements unchanged.
