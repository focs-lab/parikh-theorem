# Proof status: executable activation testing

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #20](https://github.com/focs-lab/parikh-theorem/pull/20)
have merged, with CI passing. The independent documentation increments
[PR #18](https://github.com/focs-lab/parikh-theorem/pull/18) and
[PR #19](https://github.com/focs-lab/parikh-theorem/pull/19), plus the math-rendering
fix [PR #21](https://github.com/focs-lab/parikh-theorem/pull/21), have also merged.

Current milestone: executable activation testing (`lem:activation-test`),
branch `codex/executable-activation-test`, based on merged `main`
(`73ff517a0cd9cabc38932497b798ef0d337eeeb4`).
Published as [PR #22](https://github.com/focs-lab/parikh-theorem/pull/22);
the PR's [checks](https://github.com/focs-lab/parikh-theorem/pull/22/checks)
record CI evidence for the submitted head.
There are **3 direct `sorry` obligations**, zero project axioms, and 3 declarations
transitively dependent on `sorryAx`, unchanged in this milestone. All accepted
qualitative Parikh results are proved. This increment implements the first
algorithm interface with a complete correctness proof; bounded enumeration,
exact compilation, and quantitative bounds remain.

## Completed in this milestone

`activationTest N C` is a computable value of the accepted `ActivationTest N C`
interface. Its `run` field returns a Boolean, and its checked `correct` field
proves that it returns `true` exactly when `Activatable` holds. It needs only
decidable equality on labels and operations; neither ambient type must be finite.
The required labels, added finite supports, initial support and selected operation
set are the inputs. Operation identities remain distinct even when their supports
or eventual weights coincide.

The new `ActivationAlgorithm.lean` module contains six support/implementation
declarations, all complete:

| Declaration (namespace `Parikh`) | Role |
| --- | --- |
| `ActivationOrder.mono` | Enlarging available support preserves an enabled order. |
| `Activatable.erase_iff_of_enabled` | Any enabled selected operation can go first; updating support and removing it preserves activation exactly. |
| `Activatable.batch_iff_of_enabled` | An entire subset enabled at the start can be processed together, accumulating its supports by finite union. |
| `activationRounds` | Executable search with a structural natural-number round budget; reject if remaining operations have no enabled member. |
| `activationRounds_correct` | If the budget is at least the selected set's cardinality, the Boolean result is equivalent to the accepted activation predicate. |
| `activationTest` | Supplies that cardinality as the budget and packages the algorithm with its exact correctness proof. |

Each round filters the remaining set for enabled operations, adds their supports
using Mathlib's `Finset.biUnion`, and subtracts those operations. An empty remaining
set succeeds, including with zero budget. A nonempty enabled batch strictly
decreases the remaining cardinality, so the initial cardinality supplies enough
rounds. A stalled nonempty set cannot have an activation order: the first operation
of such an order would be enabled. The single-operation equivalence is proved
using support monotonicity and the existing `filter_of_covered`; finite-set
induction gives the batch equivalence. No operation must add its own required label.

Processing a whole enabled batch avoids choosing an ordering of a `Finset`.
Mathlib's `Finset.toList` is noncomputable, so the runtime does not use it or a
classical selection function. Structural recursion is explicit; no partial or
unsafe helper is added. The proof allowlists, checker, immutable baseline,
existing definitions and instances, all prior declarations, Lean/Mathlib pins,
and cache selections are unchanged. Only the interface's explanatory comment
is updated in `Activation.lean`; its signature and meaning stay fixed.

The contract manifest preserves all 572 earlier entries and appends 15 entries:
the six named declarations above and nine Lean-generated proof/equation helpers,
for 587 declarations in total.
The completed declarations depend only on standard Lean foundations:
`propext`, `Classical.choice`, and `Quot.sound`. Some proof fields and Mathlib
finite-set proof infrastructure use these foundations; the algorithm's finite-set
operations and supplied equality decisions compile and evaluate normally.
No completed declaration depends on `sorryAx` or a project axiom.

This is an actual activation algorithm, independent of grammar syntax. It does
not yet enumerate bounded trees or compile a grammar to a semilinear witness.

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

All prior statements, definition meanings and proof bodies are unchanged here.
The grammar/tree bridge supports arbitrary derivation order and nonterminal types.
Witness and automaton existence are classical proofs; the activation implementation
in this increment is a separate executable value.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `docs/contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |

`ActivationTest` now has the executable `activationTest` implementation and a
proved correctness field. `BoundedEnumeration` and `Compiler` still have no
implementing values; their correctness fields remain requirements, not assumed
theorems. The exact finite
grammar witness and regular-language realization are classical existence proofs.
The small remaining theorem-hole count does not account for those unimplemented
algorithm values.

## Validation

- Affected modules and full `lake build` pass (1322 jobs), with only the 3 expected theorem-hole warnings in `Construction.lean`.
- `lake env lean scripts/SkeletonExamples.lean` passes. New kernel-checked computations cover C enabling E, a blocked singleton, empty work/support, a mutually blocked cycle with and without an initial label, a non-self-adding four-operation chain using the full round budget, and batches with empty or overlapping supports. Positive and negative examples also apply the implementation's correctness field. Compiled `#eval` returns `[true, false, true]`; all earlier semantic examples still pass.
- `python3 scripts/check-contracts.py` audits 587 declarations and preserves all 572 prior contracts; the append-only manifest extension records the six new named declarations and nine generated proof/equation helpers. Direct holes, transitive holes and project axioms remain 3 / 3 / 0.
- `#print axioms` for all six completed declarations reports only standard foundations, with no unresolved dependencies.
- `git diff --check` passes.
- Final-mode contract checking continues to reject the 3 outstanding bounds holes. Whole-project completion also requires bounded enumeration and exact compilation with correctness proofs.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned dependency/cache access and GitHub read/write authentication were verified. CI evidence is reported separately in the PR.

Next eligible work: implement `BoundedEnumeration.enumerate` for finite encoded
grammars and prove its exact membership contract: every valid tree up to the
height bound is enumerated, and every enumerated tree is valid and within that
bound. Then assemble exact compilation and prove the quantitative size/bit bounds.
Keep accepted contracts unchanged and publish each coherent increment as a new PR.
