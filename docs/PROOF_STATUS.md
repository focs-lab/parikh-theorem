# Proof status: exact tree decomposition

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #12](https://github.com/focs-lab/parikh-theorem/pull/12)
have merged, with CI passing.

Current milestone: [PR #13](https://github.com/focs-lab/parikh-theorem/pull/13),
exact tree decomposition, branch `codex/decomposition`, based on merged
`main` (`a69e23943c3226ba1a178cdb0c201466f669b4be`). CI evidence is recorded in the PR.
There are **12 direct `sorry` obligations**, zero project axioms, and 12 declarations
transitively dependent on `sorryAx`, down from 13. Parikh's theorem is not yet proved.

## Completed in this milestone

`Parikh.decomposition` (`thm:decomposition`, `eq:decomposition`) now reconstructs
every complete tree exactly from a simple complete base with the same root and
a finite ordered list of bounded cycle contexts. Its existing statement is
unchanged and removed from both unresolved allowlists. There is no restriction
to the grammar's start symbol, finite terminals, or finite ambient nonterminals.

The proof uses Mathlib's `Nat.strong_induction_on`, quantified over all complete
trees of the given production count. A simple tree is its own base with no
contexts. Otherwise the already proved `bounded_cut` gives a smaller complete
tree with the same root and a bounded context whose reinsertion recovers the
original tree. Apply the induction hypothesis to the smaller tree, append that
final context, and retain boundedness for every entry by list membership.
Strict decrease is in production-node count, so silent unit cycles and empty
productions remain supported.

The one new adapter, `Parikh.InsertionSequence.append`, concatenates existing
insertion sequences while preserving their context order. It is proved directly
by induction on the existing constructors; no new tree or reconstruction
relation is introduced. The decomposition keeps actual context syntax and
occurrence-based insertion witnesses, rather than just terminal-count equality.

Both audited declarations depend only on standard Lean foundations:
`propext`, `Classical.choice`, and `Quot.sound`. Neither depends on `sorryAx`
or a project axiom. All existing definitions, instances, syntax, statistics,
and previously completed proofs are retained.

All **520 prior contract entries** are preserved exactly. The single proved
sequence adapter extends the manifest to **521 entries**. No previous declaration
is deleted or moved. The checker, immutable baseline, existing signatures and
definition meanings, instances, and Lean/Mathlib pins are unchanged. No additional
Mathlib import or cache dependency is required.

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

- [PR #12](https://github.com/focs-lab/parikh-theorem/pull/12): `bounded_cut` and five structural adapters for minimal non-simple subtrees, height, production count, and reversible indexed replacement (`lem:cut`).

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
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems.

## Validation

- Affected modules and full `lake build` pass, with only expected theorem-hole warnings in the 12 remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. The new decomposition example has infinite ambient nonterminals and a non-start-rooted silent unit chain. It obtains a simple zero-weight base, a nonempty bounded-context list, exact ordered reconstruction, and the production-count identity. Existing empty-alphabet, empty-production, positional-sibling, activation, finiteness, and bounded-cut checks still pass.
- `python3 scripts/check-contracts.py` checks 521 declarations against the accepted skeleton and merged `main`, preserving all 520 earlier contracts. The checker and baseline pointer are unchanged.
- `#print axioms` for `decomposition` and `InsertionSequence.append` reports only standard foundations, with no unresolved dependencies.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 12 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0 and GitHub authentication/read/push access were verified. The existing pinned dependencies and selected Mathlib cache were reused. CI results are reported in the PR separately from local validation.

Next eligible milestone: `treeRepresentation_eq` (`thm:main`), combining exact
decomposition, activation, `one_linear`, and the grammar/tree semantics bridge.
Then prove the forward semilinearity and exact-witness contracts using bounded
family finiteness. Keep each increment in a new PR with accepted contracts unchanged.
