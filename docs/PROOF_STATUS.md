# Proof status: counting, tree semantics, and one-hole plugging proved

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
The counting/witness [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3)
and grammar/tree semantics [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4)
have merged, with CI passing.

Current milestone: one-hole plugging, branch
[`codex/one-hole-plugging`](https://github.com/focs-lab/parikh-theorem/tree/codex/one-hole-plugging),
based on merged `main` (`61ea99e6bfd4d1a8e4298cf1b63786f653fb2f43`).
There are **22 direct `sorry` obligations**, zero project axioms, and 22 declarations
transitively dependent on `sorryAx`. Parikh's theorem is not yet proved.

## Completed in this milestone

All names have namespace `Parikh`. Source: `lem:plug`, `eq:plug-wt`,
`eq:plug-size`, and `eq:plug-supp`.

| Declaration | Proof / role |
| --- | --- |
| `plugging` | The accepted one-hole contract: plugging a matching complete tree preserves completeness/root, adds weight/production count, and unions support. |
| `Valid.plug_complete` | Induction on grammar validity: filling holes with a matching complete tree preserves child-root matching and leaves no holes. |
| `ParseTree.productionSize_plug` | Structural induction gives context size plus hole count times inserted size, using Mathlib list-sum identities. |
| `ParseTree.count_yield_plug` | Coordinatewise counts obey the same formula; reuse `List.count_flatten` and list-sum identities. |
| `ParseTree.mem_support_plug` | A production label is retained from the context or comes from the inserted tree when there is at least one hole. |

The four support lemmas live in `TreePlugging.lean`; `plugging` remains in its
original place in `Decomposition.lean`, with only its proof body changed. All
372 earlier contract entries are preserved exactly. Four supporting theorems
and 33 Lean-generated equation/simplification/proof helpers extend the manifest.
No existing declaration is removed or moved. Definitions, instances, and
Lean/Mathlib pins are unchanged; the only new import is the support module.

The formulas for arbitrary hole counts specialize to one inserted copy because
`OneHole` fixes the holes list to `[A]`. They also account for no-hole side
branches and multiple holes without changing the meaning of `ParseTree.plug`.
The root of the context may differ from its hole label. Empty productions,
zero terminal weight, overlapping supports, and infinite nonterminal types
remain supported. Production count is independent of terminal yield length.

The target and all four support lemmas have no `sorryAx` or project-axiom
dependencies. Only standard Lean foundations (`propext`, `Classical.choice`,
`Quot.sound`) occur in their axiom audits.

## Previously completed

- [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3): `counts_append`, `component_isLinearSet`, `witness_isSemilinearSet`, and `exists_witness`, with `Component.denotation_eq_vadd_closure` (`eq:word-add`, `sec:statement`).
- [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4): `derives_iff_tree` and seven supporting frontier/derivation lemmas (`prop:tree-word`, `app:derivations`).

Their statements and proofs are unchanged here. The grammar/tree bridge supports
arbitrary derivation order and nonterminal types. Witness existence and tree
semantics are semantic proofs, not executable compiler implementations.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| GrammarTrees | `complete_support_active`, `bounded_open_finite` |
| Decomposition | `insertion_enabled`, `insertion_accounting`, `simple_height`, `bounded_cut`, `decomposition` |
| Activation | `first_occurrences`, `positive_multiplicities`, `one_linear` |
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- `lake build Parikh.Decomposition` and full `lake build` pass, with 22 expected theorem-hole warnings in the remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. New examples exercise plugging an empty production into a unit context, and a nested context with a different root/hole label, terminal siblings, exact yield/count/size, and support union over infinitely many nonterminals.
- `python3 scripts/check-contracts.py` checks 409 declarations against the accepted skeleton and merged `main`. All 372 earlier signatures and definition fingerprints are preserved. The checker and baseline pointer are unchanged.
- `#print axioms` for `plugging` and its four support lemmas reports only standard foundations; none depends on unresolved obligations.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 22 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned Mathlib access, and GitHub authentication/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible milestone: occurrence-based insertion, its enabledness equivalence
and exact root/weight/size/support accounting (`lem:enabled`, `lem:insertion-laws`).
Keep that increment in a new PR with the accepted statements unchanged.
