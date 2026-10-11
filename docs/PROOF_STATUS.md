# Proof status: counting, tree semantics, insertion, and abstract activation proved

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
The counting/witness [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3),
grammar/tree semantics [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4),
one-hole plugging [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5),
and insertion [PR #6](https://github.com/focs-lab/parikh-theorem/pull/6)
have merged, with CI passing.

Current milestone: abstract activation, branch
[`codex/abstract-activation`](https://github.com/focs-lab/parikh-theorem/tree/codex/abstract-activation),
based on merged `main` (`d30ffd717da0e202dca3e388880272379ba30c64`).
There are **18 direct `sorry` obligations**, zero project axioms, and 18 declarations
transitively dependent on `sorryAx`. Parikh's theorem is not yet proved.

## Completed in this milestone

All names have namespace `Parikh`. Source: `lem:first-occurrence` and
`lem:multiplicities`, with the syntax-independent support interpretation
described in `sec:formalization`.

| Declaration | Proof / role |
| --- | --- |
| `first_occurrences` | Every enabled finite operation sequence yields an enabled enumeration without repeats of exactly the same operation set. |
| `positive_multiplicities` | An activatable finite set admits any prescribed positive occurrence counts, using only its members. |
| `ActivationOrder.filter_of_covered` | Removing operations whose added support is already present preserves activation. |
| `ActivationOrder.of_forall_mem` | Any finite sequence is enabled if all its required labels are already present. |
| `ActivationOrder.append_of_covered` | An enabled pass may be followed by any operations whose roots occur initially or in support added by that pass. |

The three supporting theorems are in namespace `ActivationOrder` in
`Activation.lean`. Both target statements remain in their original places,
with only their proof bodies changed. All 444 earlier contract entries are
preserved exactly. Three supporting theorems and ten Lean-generated
equation/simplification/proof helpers extend the manifest to 457 entries.
No existing declaration is removed or moved. Definition meanings, imports,
instances, and Lean/Mathlib pins are unchanged.

First-occurrence reduction proceeds by induction, retaining the head and
filtering its repeats from an enabled distinct tail. Those repeats add only
support already supplied by the head. It does not require an operation to add
its own required label. Keeping the last occurrence instead could move an
enabling operation behind the operation it enables.

For multiplicities, the witness is the accepted activation order followed by
`order.flatMap (fun c => List.replicate (m c - 1) c)`. The initial pass supplies
all required roots via the frozen self-support hypothesis. Each initial count
is one; Mathlib's `List.count_flatMap`, `List.count_replicate`, and
`List.sum_map_eq_nsmul_single` give exactly the remaining `m c - 1` copies.
The operation and label types remain arbitrary; labels need no decidable
equality or finiteness. Empty sets and multiplicity one are supported.

This milestone proves abstract support/list results. Realizing these schedules
as actual tree insertion sequences and proving `one_linear` remain pending.

The two targets and all three support lemmas have no `sorryAx` or project-axiom
dependencies. Only standard Lean foundations occur: the targets use `propext`,
`Classical.choice`, and `Quot.sound`; the helpers use `propext`, with `Quot.sound`
also used by filtering and appending. No new hypotheses are introduced.

## Previously completed

- [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3): `counts_append`, `component_isLinearSet`, `witness_isSemilinearSet`, and `exists_witness`, with `Component.denotation_eq_vadd_closure` (`eq:word-add`, `sec:statement`).
- [PR #4](https://github.com/focs-lab/parikh-theorem/pull/4): `derives_iff_tree` and seven supporting frontier/derivation lemmas (`prop:tree-word`, `app:derivations`).
- [PR #5](https://github.com/focs-lab/parikh-theorem/pull/5): `plugging` and four supporting validity/root, size, count, and support lemmas (`lem:plug`).
- [PR #6](https://github.com/focs-lab/parikh-theorem/pull/6): `insertion_enabled`, `insertion_accounting`, and three supporting occurrence/context lemmas (`lem:enabled`, `lem:insertion-laws`).

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

- `lake build Parikh.Activation` and full `lake build` pass, with only expected theorem-hole warnings in remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. New examples check interleaved repeated operations, a disabled reversed order, first-occurrence reduction without self-support, independent multiplicities three and two, multiplicity one, and the empty operation set with zero requested counts. The label type is infinite (`ℕ`).
- `python3 scripts/check-contracts.py` checks 457 declarations against the accepted skeleton and merged `main`. All 444 earlier signatures and definition fingerprints are preserved. The checker and baseline pointer are unchanged.
- `#print axioms` for both activation targets and their three support lemmas reports only standard foundations; none depends on unresolved obligations.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 18 outstanding holes. This milestone does not complete Parikh's theorem.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned Mathlib access, and GitHub authentication/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible milestone: insertion-sequence accounting and realization of
activation orders (`cor:sequence`, `lem:activation-realize`), connecting these
abstract results to the pending `one_linear` contract. Keep that increment in
a new PR with the accepted statements unchanged.
