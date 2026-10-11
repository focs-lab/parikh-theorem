# Proof status: bounded removable-context extraction

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #11](https://github.com/focs-lab/parikh-theorem/pull/11)
have merged, with CI passing.

Current milestone: bounded removable-context extraction, branch `codex/bounded-cut`,
based on merged `main` (`0d25dff22496b4b96c3e43ce8fd1cb5ba6473956`).
Publication and CI evidence are recorded in the milestone PR.
There are **13 direct `sorry` obligations**, zero project axioms, and 13 declarations
transitively dependent on `sorryAx`, down from 14. Parikh's theorem is not yet proved.

## Completed in this milestone

`Parikh.bounded_cut` (`lem:cut`) now extracts a bounded removable cycle context
from every non-simple complete tree. The result includes a smaller complete tree
with the same root, exact occurrence-based reinsertion reconstructing the original
tree, and strict decrease in production-node count. Its existing statement is
unchanged and removed from both unresolved allowlists. It introduces no finite
terminal or ambient nonterminal hypothesis.

Five supporting lemmas in `BoundedCutSupport.lean` are proved immediately:

| Declaration (namespace `Parikh`) | Role |
| --- | --- |
| `Complete.exists_minimal_nonsimple_subtree` | Descend through non-simple children to an occurrence whose children are all simple. |
| `ParseTree.exists_root_mem_child_support` | With simple children, a repeated path must include the root label, which therefore occurs in a child. |
| `ParseTree.height_le_height_plug` | Filling holes cannot decrease production height. |
| `ParseTree.productionSize_subtree_bound` | A proper subtree has strictly fewer production nodes. |
| `ParseTree.subtree_replacement` | Replacing a selected occurrence retains its position and can be undone exactly. |

The source's minimal-subtree argument needs simple side branches. Structural
descent supplies precisely that property. `simple_height` bounds the selected
node by the active cardinality plus one. The support/subtree bridge locates a
proper descendant with the same root. The existing `Complete.subtree_context`
extracts its one-hole context; height monotonicity bounds that context, while
strict subtree size and `productionSize_plug` show it has a positive production
count. The outer context replaces the selected node by its matching descendant.
Reversible indexed replacement certifies reinsertion at the same position,
preserving every production label, child order, and side branch. Exact size
accounting proves strict decrease even when the removed context has zero weight.

All six audited declarations depend only on standard Lean foundations:
`propext`, `Classical.choice`, and `Quot.sound` (the replacement adapter needs
only `propext` and `Quot.sound`). None depends on `sorryAx` or a project axiom.
All existing syntax, statistics, definitions, instances, and previously completed
proofs are retained.

All **501 prior contract entries** are preserved exactly. The five proved
adapters and 14 generated equation/proof/simplification declarations extend the
manifest to **520 entries**, including the generated equation for the existing
`ParseTree.Simple` predicate. No previous declaration is deleted or moved.
The checker, immutable baseline, existing signatures and definition meanings,
instances, and Lean/Mathlib pins are unchanged. No additional Mathlib import or
cache dependency is required.

This is a semantic existence proof. Executable decomposition, enumeration, and
compiler implementations remain separate work.

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

Their statements and proofs are unchanged here. The grammar/tree bridge supports
arbitrary derivation order and nonterminal types. Witness existence and tree
semantics are semantic proofs, not executable compiler implementations.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| Decomposition | `decomposition` |
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- Affected modules and full `lake build` pass, with only expected theorem-hole warnings in the 13 remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. A new example has two deep, repeated-label siblings over infinite nonterminals: the original height is 5, above the active bound of 3, but the extracted context is bounded and reinsertion is exact. Both the smaller tree and context have zero terminal weight, while production count strictly decreases. Existing empty-alphabet, empty-production, positional-sibling, and finiteness checks still pass.
- `python3 scripts/check-contracts.py` checks 520 declarations against the accepted skeleton and merged `main`, preserving all 501 earlier contracts. The checker and baseline pointer are unchanged.
- `#print axioms` for `bounded_cut` and its five supporting lemmas reports only standard foundations, with no unresolved dependencies.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 13 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0, the pinned Mathlib checkout, and GitHub authentication/read/push access were verified. The merged finiteness branch was removed locally and remotely after ancestry and head checks. CI results are reported in the PR separately from local validation.

Next eligible milestone: `decomposition` (`thm:decomposition`), using strong
induction on production count and exact reinsertion to obtain a simple complete
base plus a sequence of bounded cycle contexts. Keep each increment in a new PR
with the accepted contracts unchanged.
