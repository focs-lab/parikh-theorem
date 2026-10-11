# Proof status: active support and simple-tree height bounds

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
The counting/witness [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3),
grammar/tree semantics [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4),
one-hole plugging [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5),
insertion [PR #6](https://github.com/focs-lab/parikh-theorem/pull/6),
abstract activation [PR #7](https://github.com/focs-lab/parikh-theorem/pull/7),
tree realization [PR #8](https://github.com/focs-lab/parikh-theorem/pull/8),
and exact linear component [PR #9](https://github.com/focs-lab/parikh-theorem/pull/9)
have merged, with CI passing.

Current milestone: [PR #10](https://github.com/focs-lab/parikh-theorem/pull/10),
active support and the simple-tree height bound, branch
[`codex/active-support-height`](https://github.com/focs-lab/parikh-theorem/tree/codex/active-support-height),
based on merged `main` (`37dfb799e8ef23ba6e0782bab77fcf0af4946f19`).
There are **15 direct `sorry` obligations**, zero project axioms, and 15 declarations
transitively dependent on `sorryAx`, down from 17. Parikh's theorem is not yet proved.

## Completed in this milestone

All names have namespace `Parikh`. Source: `def:statistics`, `lem:simple-height`,
and the active-alphabet prerequisite for `lem:finite`.

| Declaration | Proof / role |
| --- | --- |
| `complete_support_active` | Every production-node label of a complete tree lies in the grammar's finite active alphabet. |
| `simple_height` | A simple complete tree's production height is at most the active nonterminal cardinality, with no finite ambient nonterminal hypothesis. |
| `Valid.support_active` | Stronger support containment for any valid open tree; holes contribute no production label. |
| `ParseTree.labelPath_subset_support` | Every label on any production-label path belongs to the tree's support. |
| `ParseTree.exists_labelPath_height` | A longest production-label path has length equal to production height, including terminal/hole and empty-production cases. |

Both existing theorem statements are unchanged and removed from the direct and
transitive unresolved allowlists. Three supporting lemmas are proved immediately
and introduce no holes. All five audited declarations depend only on standard
Lean foundations: `propext`, `Classical.choice`, and `Quot.sound`. None depends
on `sorryAx` or a project axiom.

All 474 earlier contract entries are preserved exactly, including generated
helpers. Three proved adapters and 20 Lean-generated equation, matching,
proof, and simplification declarations extend the manifest to 497 entries.
No existing declaration is deleted or moved. All earlier signatures,
definition meanings, instances, and Lean/Mathlib pins are unchanged.
The only new import is the project's structural path module, `ParseTreePaths`.

Support containment is induction on validity: each production is a member of the
grammar's finite rule set, so its input label is active; child supports satisfy
the same property. The proof unfolds the existing well-founded label recursion
explicitly so previously published generated simplification helpers remain
stable. The complete-tree contract is a direct specialization.

The path proofs are structural adapters for the existing syntax. Mathlib/core
list maxima select a tallest child, with a separate singleton path for an empty
production. Simplicity makes the chosen path duplicate-free. Its length equals
its finite-set cardinality, and support containment makes that finite set a
subset of the active alphabet. Mathlib's cardinality monotonicity finishes the
height bound. Neither new paths nor new statistics are defined.

Height counts production nodes, not yield length. Terminal-only trees have
height zero; empty productions have height one. Repeated labels on separate
branches remain permitted. Arbitrary valid holes outside the active alphabet
still have empty support; this does not establish `ActiveOpen`, so its hole
restriction remains essential for the next finite-family obligation.
These are semantic proofs; enumeration and executable compiler values remain
separate work.

## Previously completed

- [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3): `counts_append`, `component_isLinearSet`, `witness_isSemilinearSet`, and `exists_witness`, with `Component.denotation_eq_vadd_closure` (`eq:word-add`, `sec:statement`).
- [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4): `derives_iff_tree` and seven supporting frontier/derivation lemmas (`prop:tree-word`, `app:derivations`).
- [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5): `plugging` and four supporting validity/root, size, count, and support lemmas (`lem:plug`).
- [PR #6](https://github.com/focs-lab/parikh-theorem/pull/6): `insertion_enabled`, `insertion_accounting`, and three supporting occurrence/context lemmas (`lem:enabled`, `lem:insertion-laws`).
- [PR #7](https://github.com/focs-lab/parikh-theorem/pull/7): `first_occurrences`, `positive_multiplicities`, and three abstract support/list lemmas (`lem:first-occurrence`, `lem:multiplicities`).
- [PR #8](https://github.com/focs-lab/parikh-theorem/pull/8): `Cycle.root_mem_support`, `InsertionSequence.accounting`, `activationOrder_iff_insertionSequence`, and `ContextsActivatable.realize` (`eq:cycle-root`, `cor:sequence`, `lem:activation-realize`, `eq:activated-wt`, `eq:activated-supp`).
- [PR #9](https://github.com/focs-lab/parikh-theorem/pull/9): `one_linear`, with `contextComponent.mem_denotation_iff` (`prop:one-linear`, `eq:one-linear`, `eq:component`).

Their statements and proofs are unchanged here. The grammar/tree bridge supports
arbitrary derivation order and nonterminal types. Witness existence and tree
semantics are semantic proofs, not executable compiler implementations.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| GrammarTrees | `bounded_open_finite` |
| Decomposition | `bounded_cut`, `decomposition` |
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- Affected modules and full `lake build` pass, with only expected theorem-hole warnings in the 15 remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. A unit/empty-production chain over infinite nonterminals (`ℕ`) and an empty terminal alphabet reaches the active-cardinality bound. Repeated siblings are simple despite duplicate total production labels; repeating a label along one branch violates simplicity and can exceed the bound. A terminal-only tree is complete and simple even in a grammar without productions. An inactive hole is valid and has active support, but fails `ActiveOpen`.
- `python3 scripts/check-contracts.py` checks 497 declarations against the accepted skeleton and merged `main`. All 474 earlier signatures and definition fingerprints are preserved. The checker and baseline pointer are unchanged.
- `#print axioms` for both completed targets and all three supporting lemmas reports only standard foundations; none depends on unresolved obligations.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 15 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned Mathlib access, and GitHub authentication/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible milestone: `bounded_open_finite` (`lem:finite`), using finite
productions, their fixed child arities, finite terminals, and the existing
active-hole restriction. Then prove bounded cut and decomposition. Keep each
increment in a new PR with accepted statements unchanged.
