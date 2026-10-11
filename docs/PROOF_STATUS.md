# Proof status: counting, tree semantics, plugging, and insertion proved

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
The counting/witness [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3),
grammar/tree semantics [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4),
and one-hole plugging [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5)
have merged, with CI passing.

Current milestone: occurrence-based insertion, branch
[`codex/insertion-laws`](https://github.com/focs-lab/parikh-theorem/tree/codex/insertion-laws),
based on merged `main` (`5046427c6229da0e4a969d0aa463a59c7b258559`).
There are **20 direct `sorry` obligations**, zero project axioms, and 20 declarations
transitively dependent on `sorryAx`. Parikh's theorem is not yet proved.

## Completed in this milestone

All names have namespace `Parikh`. Source: `lem:enabled`, `lem:insertion-laws`,
`eq:insert-wt`, `eq:insert-size`, and `eq:insert-supp`.

| Declaration | Proof / role |
| --- | --- |
| `insertion_enabled` | A cycle can be inserted exactly when its root label occurs in the complete tree's support. |
| `insertion_accounting` | An insertion preserves the original root, adds exactly the cycle's weight/production count, and unions its support. |
| `ParseTree.plug_of_holes_eq_nil` | Complete side branches are unchanged by filling holes. |
| `Complete.mem_support_iff_subtree` | Support is precisely existence of a nonterminal-rooted subtree at a position, including empty-production nodes. |
| `Complete.subtree_context` | A selected subtree is complete; cutting it out produces a valid one-hole outer context that reconstructs the tree and exactly represents replacement at that position. |

The three supporting theorems live in `TreeReplacement.lean`. Both insertion
statements remain in their original places in `Decomposition.lean`, with only
their proof bodies changed. All 409 earlier contract entries are preserved
exactly. Three supporting theorems and 32 Lean-generated
equation/simplification/proof helpers extend the manifest to 444 entries.
No existing declaration is removed or moved. Definition meanings, instances,
and Lean/Mathlib pins are unchanged; the only new import is the support module.

For the selected subtree `u` and outer context `E`, the proof establishes
`t = E.plug u` and `t' = E.plug (C.plug u)`. Applying the already proved
`plugging` contract twice gives all accounting identities, exactly as in the
reference. Index-based replacement distinguishes repeated occurrences of a
label. No-hole side branches remain intact. Empty productions, zero terminal
weight, overlapping supports, and infinite nonterminal types remain supported.
Production count is independent of terminal yield length.

The two targets and all three support lemmas have no `sorryAx` or project-axiom
dependencies. Only standard Lean foundations (`propext`, `Classical.choice`,
`Quot.sound`) occur in their axiom audits. The local classical terminal-equality
instance in enabledness adds no hypothesis to its frozen statement.

## Previously completed

- [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3): `counts_append`, `component_isLinearSet`, `witness_isSemilinearSet`, and `exists_witness`, with `Component.denotation_eq_vadd_closure` (`eq:word-add`, `sec:statement`).
- [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4): `derives_iff_tree` and seven supporting frontier/derivation lemmas (`prop:tree-word`, `app:derivations`).
- [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5): `plugging` and four supporting validity/root, size, count, and support lemmas (`lem:plug`).

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
| Activation | `first_occurrences`, `positive_multiplicities`, `one_linear` |
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- `lake build Parikh.TreeReplacement`, `lake build Parikh.Decomposition`, and full `lake build` pass, with only expected theorem-hole warnings in remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. New examples use an infinite nonterminal type, two equally labelled empty-production siblings, and a zero-weight unit cycle around only the second sibling. They check occurrence selection, unchanged first sibling, out-of-range replacement failure, enabledness, absent support, and exact root/weight/size/support accounting.
- `python3 scripts/check-contracts.py` checks 444 declarations against the accepted skeleton and merged `main`. All 409 earlier signatures and definition fingerprints are preserved. The checker and baseline pointer are unchanged.
- `#print axioms` for both insertion targets and their three support lemmas reports only standard foundations; none depends on unresolved obligations.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 20 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned Mathlib access, and GitHub authentication/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible milestone: abstract activation's first-occurrence reduction and
positive multiplicities (`lem:first-occurrence`, `lem:multiplicities`). Keep
that increment in a new PR with the accepted statements unchanged.
