# Proof status: bounded active-open-tree finiteness

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #10](https://github.com/focs-lab/parikh-theorem/pull/10)
have merged, with CI passing.

Current milestone: [PR #11](https://github.com/focs-lab/parikh-theorem/pull/11),
bounded active-open-tree finiteness, branch `codex/bounded-open-finiteness`,
based on merged `main` (`98ef9a17e4c68ef98027ae1bfc12c25e483b197a`).
CI evidence is recorded in the milestone PR.
There are **14 direct `sorry` obligations**, zero project axioms, and 14 declarations
transitively dependent on `sorryAx`, down from 15. Parikh's theorem is not yet proved.

## Completed in this milestone

`Parikh.bounded_open_finite` (`lem:finite`) now proves that, for every finite
terminal alphabet, grammar, and height bound, the family of valid trees with
active holes and bounded production height is finite. The grammar's ambient
nonterminal type may be infinite. Its existing statement is unchanged.
The declaration is removed from both direct and transitive unresolved allowlists.
Its audited dependencies are only standard Lean foundations: `propext`,
`Classical.choice`, and `Quot.sound`. It has no `sorryAx` or project-axiom dependency.

The proof follows the source's height induction. At height zero, terminals and
active holes give a finite family; production nodes have positive height even
when the production is empty. In the successor case, each grammar rule fixes a
child-list length through the existing RHS-root equality. Mathlib's
`List.finite_length_eq`, applied to the previous family's finite subtype, gives
finitely many possible child lists. Finite images and a finite union over the
rules cover all production nodes. Children inherit validity and the active-hole
restriction; list-maximum lemmas show that each child satisfies the smaller bound.

Two local proof adapters handle fixed-length child lists and explicit unfolding
of the existing height recursion. They stay inside the theorem; no public helper,
new syntax, statistic, definition, or instance is introduced. Explicit
`WellFounded.fix_eq` unfolding preserves previously published generated height
helpers. Validity filters the finite node superset, retaining root matching.

All **497 earlier contract entries** are preserved exactly. Four Lean-generated
proof/simplification helpers extend the manifest to **501 entries**. No prior
declaration is deleted or moved. The checker, baseline pointer, existing
signatures, definition meanings, instances, and Lean/Mathlib pins are unchanged.
The sole new Mathlib import is `Mathlib.Data.Set.Finite.List`; its cache target is
included in CI and the build instructions.

This establishes semantic finiteness. It does not implement the separately
specified executable enumeration or compiler.

## Previously completed

- [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3): `counts_append`, `component_isLinearSet`, `witness_isSemilinearSet`, and `exists_witness`, with `Component.denotation_eq_vadd_closure` (`eq:word-add`, `sec:statement`).
- [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4): `derives_iff_tree` and seven supporting frontier/derivation lemmas (`prop:tree-word`, `app:derivations`).
- [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5): `plugging` and four supporting validity/root, size, count, and support lemmas (`lem:plug`).
- [PR #6](https://github.com/focs-lab/parikh-theorem/pull/6): `insertion_enabled`, `insertion_accounting`, and three supporting occurrence/context lemmas (`lem:enabled`, `lem:insertion-laws`).
- [PR #7](https://github.com/focs-lab/parikh-theorem/pull/7): `first_occurrences`, `positive_multiplicities`, and three abstract support/list lemmas (`lem:first-occurrence`, `lem:multiplicities`).
- [PR #8](https://github.com/focs-lab/parikh-theorem/pull/8): `Cycle.root_mem_support`, `InsertionSequence.accounting`, `activationOrder_iff_insertionSequence`, and `ContextsActivatable.realize` (`eq:cycle-root`, `cor:sequence`, `lem:activation-realize`, `eq:activated-wt`, `eq:activated-supp`).
- [PR #9](https://github.com/focs-lab/parikh-theorem/pull/9): `one_linear`, with `contextComponent.mem_denotation_iff` (`prop:one-linear`, `eq:one-linear`, `eq:component`).
- [PR #10](https://github.com/focs-lab/parikh-theorem/pull/10): `complete_support_active`, `simple_height`, `Valid.support_active`, `ParseTree.labelPath_subset_support`, and `ParseTree.exists_labelPath_height` (`def:statistics`, `lem:simple-height`).

Their statements and proofs are unchanged here. The grammar/tree bridge supports
arbitrary derivation order and nonterminal types. Witness existence and tree
semantics are semantic proofs, not executable compiler implementations.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| Decomposition | `bounded_cut`, `decomposition` |
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- Affected module and full `lake build` pass, with only expected theorem-hole warnings in the 14 remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. New checks identify exactly the two terminals and the start hole in a height-zero active family over infinite nonterminals with no productions, and prove the unrestricted height-zero family infinite. Existing empty-alphabet, empty-production, repeated-sibling, and unit-chain examples still pass.
- `python3 scripts/check-contracts.py` checks 501 declarations against the accepted skeleton and merged `main`, preserving all 497 earlier signatures and definition fingerprints. The checker and baseline pointer are unchanged.
- `#print axioms Parikh.bounded_open_finite` reports only standard foundations, with no unresolved dependencies.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 14 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned Mathlib access and the new cache target, and GitHub authentication/read/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible milestone: `bounded_cut` (`lem:cut`), locating a minimal non-simple
subtree and extracting a bounded removable context with exact reconstruction and
strict production-size decrease. Then prove `decomposition`. Keep each increment
in a new PR with the accepted contracts unchanged.
