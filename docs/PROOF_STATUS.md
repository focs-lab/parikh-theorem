# Proof status: exact witnesses with all four size bounds

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #24](https://github.com/focs-lab/parikh-theorem/pull/24)
have merged, with CI passing. Documentation PRs #18/#19 and the math-rendering
fix in PR #21 have also merged.

Current milestone: exact bounded semilinear witness existence (`thm:size-bound`),
branch `codex/bounded-witness`, based on merged `main`
(`f2bab08d401a50c7c4ea0632e1b6753214d947a7`).
Published as [PR #25](https://github.com/focs-lab/parikh-theorem/pull/25);
the PR's [checks](https://github.com/focs-lab/parikh-theorem/pull/25/checks)
record CI evidence for the submitted head.
There is **1 direct `sorry` obligation**, zero project axioms, and 1 declaration
transitively dependent on `sorryAx`. This milestone removes `bounded_witness`
from both unresolved lists. All qualitative Parikh results, bounded-family
counts/weights and witness size bounds are proved. Activation testing and tree
enumeration have executable implementations with complete correctness proofs.
The bit budget and executable grammar-to-witness compiler remain.

## Completed in this milestone

The accepted `bounded_witness` theorem now constructs an exact semilinear
witness and proves every part of `WithinBounds`:

| Quantity | Proved bound |
| --- | --- |
| Components | At most `K * 2^K` |
| Periods in each component | At most `K` |
| Each component's base norm | At most `(K+1) * M` |
| Each period's norm | At most `M` |

Here `K` and `M` are the accepted grammar tree/position budgets. The witness's
denotation is exactly the grammar's Parikh image, not an overapproximation.
The grammar may have an infinite ambient nonterminal type; only the active
base/context families and terminal alphabet need the stated finiteness.

`FiniteWitness.lean` adds the classical `familyWitness` constructor. It takes
finite base and cycle families, forms base/subset pairs using Mathlib's finite
product and powerset, filters by the existing `ContextsActivatable` predicate,
and maps each retained pair to its existing `contextComponent`. Its membership
lemma retains the actual base and context identities. `familyWitness_denotation`
reuses the proved exact tree representation when the input families contain
exactly all bases and bounded cycles. `familyWitness_length_le` reuses product,
powerset and filter cardinality laws.

`contextComponent_size_bounds` in `Construction.lean` counts one period per
selected context and bounds the sum of the original base weight and all first
context copies. Mathlib's finite-sum commutation, additivity and bounded-sum
inequality provide the norm accounting. The completed theorem applies these
results to the families from `bounded_family_bounds` and enlarges the local
budgets using their cardinality bounds.

Distinct contexts remain distinct period-list positions, even when their weights
are equal or zero; no weight deduplication occurs. Empty families produce an
empty witness, and the empty context subset remains a candidate for each base.
This construction uses classical finite-set listing and activation filtering.
It proves bounded existence and supplies reusable assembly support; it is not
an implementing value of the executable `Compiler` interface.

All **644 earlier contract entries** are preserved. The manifest appends
**14 entries** (five named support declarations and nine generated proof/equation
helpers), for **658 declarations** in total. Every previously published theorem
remains in its original module. The accepted baseline, checker, definition
meanings and Lean/Mathlib pins remain unchanged. Only the completed theorem's
direct/transitive obligation entries are removed. There is no new Mathlib import,
cache target, datatype, instance, partial runtime helper, unsafe declaration or
project axiom.

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

- [PR #13](https://github.com/focs-lab/parikh-theorem/pull/13): `decomposition` and `InsertionSequence.append`, by strong induction on production count and exact bounded-context reinsertion (`thm:decomposition`, `eq:decomposition`).

- [PR #14](https://github.com/focs-lab/parikh-theorem/pull/14): `treeRepresentation_eq` and `InsertionSequence.contextsActivatable`, proving exact equality with the grammar Parikh image while retaining actual context identities (`thm:main`, `eq:main`).

- [PR #15](https://github.com/focs-lab/parikh-theorem/pull/15): `bases_finite`, `bounded_cycles_finite`, `treeRepresentation_isSemilinearSet`, `grammar_image`, `grammar_witness`, and `contextFree_image`, completing forward semilinearity and exact finite witness existence (`thm:main`, `thm:parikh-statement`).

- [PR #16](https://github.com/focs-lab/parikh-theorem/pull/16): `representative_counts` and six expression-image adapters, including `componentExpression_image` and `witnessExpression_image`, proving both inclusions of the constructed expression images (`eq:representative`, `lem:linear-regular`, `eq:regular-construction`).

- [PR #17](https://github.com/focs-lab/parikh-theorem/pull/17): `witnessExpression_correct`, `converse`, and `regular_realization`, with finite continuation-language automata and specialized word-prefix adapters (`lem:linear-regular`, `thm:converse`, `thm:parikh-statement`).

- [PR #20](https://github.com/focs-lab/parikh-theorem/pull/20): `regular_image`, exact DFA-to-Mathlib-grammar language equality, and shared forward-image support, completing every accepted qualitative Parikh theorem (`thm:parikh-statement`).


- [PR #22](https://github.com/focs-lab/parikh-theorem/pull/22): executable `activationTest`, exact sufficient-fuel correctness, support monotonicity, and enabled-operation/batch removal equivalences (`lem:activation-test`).

- [PR #23](https://github.com/focs-lab/parikh-theorem/pull/23): executable `boundedEnumeration`, exact height-bounded membership, ordered child-root products, and declared-leaf enumeration (`lem:finite`, `sec:effective`).

- [PR #24](https://github.com/focs-lab/parikh-theorem/pull/24): `bounded_family_bounds`, finite syntax covers, cardinality budgets and terminal-yield/weight-norm bounds (`lem:count-trees`).

## Remaining named theorem obligation

The entry below is directly and transitively incomplete. The machine-readable
allowlists in `docs/contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declaration |
| --- | --- |
| Construction | `witness_bit_bound` |

`ActivationTest` and `BoundedEnumeration` have executable implementing values
with proved correctness fields. `Compiler` still has no implementing value;
its `correct` and `bounded` fields remain requirements. The one remaining
theorem hole does not account for the missing compiler. Classical bounded
witness existence does not itself compute a witness from encoded input.

## Validation

- Affected modules and full `lake build` pass, with only the tracked bit-bound warning in `Construction.lean`.
- `lake env lean scripts/SkeletonExamples.lean` passes, including empty-family witness assembly and two distinct zero-weight contexts retaining two period positions with zero base/period norms. All earlier examples pass.
- Contract checking audits 658 declarations, preserves all 644 earlier fingerprints and reports direct holes / transitive holes / project axioms as **1 / 1 / 0**.
- `#print axioms` for `bounded_witness` and all five new named support declarations reports only standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx` or project axioms.
- `git diff --check` passes.
- Final-mode checking still rejects `witness_bit_bound`. Whole-project completion also requires exact executable witness compilation.
- Cloud Lean 4.34.1 / Lake 5.0.0 and pinned Mathlib/GitHub access are verified. CI evidence is reported separately in the PR.

Next eligible theorem milestone: prove the numerical bit budget and coordinate
widths in `witness_bit_bound`. The executable compiler must still reuse the
proved enumeration and activation test, preserve context identities and handle
duplicate input productions, with exact denotation and size proofs. Keep
accepted contracts unchanged and publish each coherent increment as a new PR,
stopping for review.
