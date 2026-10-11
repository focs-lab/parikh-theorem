# Proof status: counting/witness bridges and grammar/tree semantics proved

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline is the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
The counting/witness milestone in [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3)
has merged, with CI passing.

Current milestone: [grammar/tree semantics PR #4](https://github.com/focs-lab/parikh-theorem/pull/4), branch
[`codex/grammar-tree-semantics`](https://github.com/focs-lab/parikh-theorem/tree/codex/grammar-tree-semantics),
based on merged `main` (`c1e2d3010feae79e8a429334db639c8836ad2545`).
There are **23 direct `sorry` obligations**, zero project axioms, and 23 declarations
transitively dependent on `sorryAx`. Parikh's theorem is not yet proved.

## Completed in this milestone

All names have namespace `Parikh`. Source: `prop:tree-word`, `app:derivations`,
including the context property `eq:word-context`.

| Declaration | Proof / role |
| --- | --- |
| `derives_iff_tree` | The accepted equivalence between Mathlib derivations and complete trees, for every grammar, root, and word. |
| `rewrites_append_cases` | A context-free rewrite in a concatenation occurs in one of the two parts. Supports the forest step without a new rewrite relation. |
| `ParseTree.frontier_holes` | The frontier's nonterminals are exactly the ordered holes. |
| `ParseTree.frontier_yield` | The frontier's terminals are exactly the ordered yield. |
| `ParseTree.frontier_of_holes_eq_nil` | A tree without holes has frontier equal to its terminal yield. |
| `Valid.derives_frontier` | Structural induction on validity; apply the production and concatenate child derivations using Mathlib prefix/suffix closure. |
| `Valid.frontier_step` | Expand one hole according to a grammar step, retaining validity and root. |
| `derives_tree_frontier` | Induct on Mathlib's reflexive transitive derivation, starting with a root hole and expanding the frontier one step at a time. |

No definition meanings, theorem signatures, instances, imports, or dependency pins
changed. Seven support theorems and 21 Lean-generated equation/simplification
helpers extend the manifest; all 344 earlier entries are preserved exactly.
The existing active-support and bounded-family statements remain unresolved.
Their declarations precede the new helpers so Lean's generated binder identities
remain stable in the strict elaborated-contract check.

All completed declarations and new helpers have no `sorryAx` or project-axiom
dependencies. The axiom audit reports only standard foundations: `propext`,
`Classical.choice`, and `Quot.sound`. The proofs permit infinite terminal and
nonterminal types, arbitrary derivation order, empty productions, unit rules,
and ambiguous derivations. No grammar normal form or finiteness assumption was
added. The frontier construction is a semantic existence proof, not an executable
compiler claim.

## Previously completed

[PR #3](https://github.com/focs-lab/parikh-theorem/pull/3) proves `counts_append`
(`eq:word-add`), `component_isLinearSet`, `witness_isSemilinearSet`, and
`exists_witness`, with helper `Component.denotation_eq_vadd_closure`. It reuses
Mathlib finite-range additive closure, finite unions and finite-set enumeration.
Those proofs support empty witnesses, duplicate/zero periods, and arbitrary
terminal types. Their signatures and proofs are unchanged here.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| GrammarTrees | `complete_support_active`, `bounded_open_finite` |
| Decomposition | `plugging`, `insertion_enabled`, `insertion_accounting`, `simple_height`, `bounded_cut`, `decomposition` |
| Activation | `first_occurrences`, `positive_multiplicities`, `one_linear` |
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- `lake build Parikh.GrammarTrees` and `lake build` pass, with 23 expected theorem-hole warnings in the remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. New kernel-checked examples exercise empty alphabet/production, a unit rule over infinitely many nonterminals, and mixed terminal/nonterminal siblings with two silent expansions. Both directions of the bridge are used.
- `python3 scripts/check-contracts.py` checks 372 declarations against the accepted skeleton and merged `main`. All earlier signatures and definition fingerprints are preserved. The audit implementation is unchanged.
- `#print axioms` for the completed target and seven support theorems reports only the standard foundations above; none depends on unresolved obligations.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 23 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0 and the pinned Mathlib revision were verified. Git dependency access and authenticated GitHub publication access work with the existing cloud credentials. CI results are reported in the PR separately from local validation.

Next eligible milestone: one-hole plugging and its root, weight, production-size,
and support identities (`lem:plug`), then occurrence-based insertion. Keep the
next increment in a new PR, preserving accepted statements. Active-support and
bounded-family proofs are separate pending prerequisites for bounded decomposition.
