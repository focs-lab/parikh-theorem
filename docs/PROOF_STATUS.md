# Proof status: all theorem obligations proved; executable compiler pending

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #25](https://github.com/focs-lab/parikh-theorem/pull/25)
have merged, with CI passing. Documentation PRs #18/#19 and the math-rendering
fix in PR #21 have also merged.

Current milestone: fixed coordinate widths and the numerical entry-bit budget
(`eq:bit-bound`), branch `codex/witness-bit-bound`, based on merged `main`
(`afd1f37e93a0dec0db2562b45408e31660bdc9b7`).
Publication and final-head CI evidence will be recorded when the PR is opened.
There are **0 direct `sorry` obligations**, **0 project axioms**, and **0
transitively unresolved declarations**. The completed `witness_bit_bound` removes
the last entry from both proof-hole allowlists. All qualitative Parikh results,
bounded-family counts/weights, witness size bounds and numerical bit bounds are
proved. Activation testing and tree enumeration have executable implementations
with complete correctness proofs. The executable grammar-to-witness compiler
still needs an implementing value; zero theorem holes do not finish effectivity.

## Completed in this milestone

The accepted `witness_bit_bound` theorem now proves:

| Quantity | Proved bound |
| --- | --- |
| Each base coordinate | Strictly below `2^L` |
| Each period coordinate | Strictly below `2^L` |
| All numerical vector entries | At most `K * 2^K * (K+1) * d * L` bits |

Here `M`, `K` and `d` are the accepted position, tree and terminal budgets, and
`L = max 1 (Nat.clog 2 ((K+1)*M+1))`. The budget excludes list-length metadata,
as required by the reference and the frozen definition of `entryBits`.

Mathlib's `Nat.le_pow_clog` and power monotonicity make the fixed width large
enough. `Finset.single_le_sum` bounds any coordinate by its vector norm; the
accepted norm bounds then give coordinate fit. `List.sum_le_length_nsmul`
bounds the sum of component entry widths using the existing component and
period-count budgets. No grammar positivity assumptions or terminal equality
instance are added to the theorem. Duplicate and zero indexed periods continue
to count as separate entries.

All **658 earlier contract entries** are preserved. The manifest appends
**3 generated entries** (the `vectorBits` equation and two proof helpers), for
**661 declarations** in total. No named helper is added and every previously
published theorem remains in its original module. The accepted baseline,
checker, definition meanings and Lean/Mathlib pins remain unchanged. Only the
completed theorem's direct/transitive obligation entries are removed. There is
no new import/cache target, datatype, instance, partial runtime helper, unsafe
declaration or project axiom.

CI now invokes the existing checker with `--final`, rejecting every project
hole, axiom and transitive unresolved dependency. The eleven previously
allowlisted compiler-generated recursion helpers remain separately audited;
standard Lean foundations remain disclosed and permitted.

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

- [PR #25](https://github.com/focs-lab/parikh-theorem/pull/25): `bounded_witness`, classical `familyWitness` assembly with exact denotation and component-count bounds, and `contextComponent_size_bounds`, proving all four witness size bounds while preserving actual context identities (`thm:size-bound`).

## Remaining implementation

No named theorem obligation remains. The machine-readable proof-hole and
project-axiom allowlists in `docs/contracts/obligations.json` are empty.
`ActivationTest` and `BoundedEnumeration` have executable implementing values
with proved correctness fields. `Compiler` still has no implementing value;
its `correct` and `bounded` fields remain requirements. This missing value is
not represented by a `sorry`, so declaration auditing alone cannot certify
whole-project completion. Classical `familyWitness` and `bounded_witness`
prove bounded existence without an executable encoded-input compiler.

## Validation

- Affected `Parikh.Construction` and full `lake build` pass without proof-hole warnings.
- `lake env lean scripts/SkeletonExamples.lean` passes, including the exact-power ceiling-log boundary, duplicate indexed periods and zero entry bits for a nonempty witness over an empty alphabet. All earlier examples pass.
- Final contract checking audits 661 declarations, preserves all 658 earlier fingerprints and reports direct holes / transitive holes / project axioms as **0 / 0 / 0**.
- `#print axioms` for `witness_bit_bound` and `bounded_witness` reports only standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx` or project axioms.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` passes; CI now requires this mode. Whole-project completion also requires exact executable witness compilation.
- Cloud Lean 4.34.1 / Lake 5.0.0 and pinned Mathlib/GitHub access are verified. Final-head CI evidence is reported in the PR.

Next eligible milestone: implement the executable grammar-to-witness compiler
with exact denotation and all four size proofs. Reuse the proved enumeration
and activation test, preserve context identities and account for duplicate
input productions in cardinality bounds. The bit theorem then supplies the
numerical encoding guarantee for its bounded output. Keep accepted contracts
unchanged and publish each coherent increment as a new PR, stopping for review.
