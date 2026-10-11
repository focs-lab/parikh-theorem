# Proof status: bounded-family cardinality and leaf-weight bounds

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #23](https://github.com/focs-lab/parikh-theorem/pull/23)
have merged, with CI passing. Documentation PRs #18/#19 and the math-rendering
fix in PR #21 have also merged.

Current milestone: quantitative bounded-family and leaf-weight bounds
(`lem:count-trees`), branch `codex/bounded-family-bounds`, based on merged `main`
(`d6472d423d4248db5bb294ab2f626fc90788e686`).
Publication pending.
There are **2 direct `sorry` obligations**, zero project axioms, and 2 declarations
transitively dependent on `sorryAx`. This milestone removes `bounded_family_bounds`
from both unresolved lists. All accepted qualitative Parikh results are proved;
activation testing and bounded-tree enumeration have executable implementations
with complete correctness proofs. Witness compilation and the witness size/bit
bounds remain.

## Completed in this milestone

The accepted `bounded_family_bounds` theorem now proves all three conclusions:

- A finite family contains exactly the bases, and has cardinality at most `K`.
- A finite family contains exactly the bounded cycles, and has cardinality at most `K`.
- Each base or bounded cycle has terminal-count norm at most `M`.

Here `n` counts active nonterminals, `d` terminals, `p` distinct productions,
`b` is at least one and bounds every production's arity, `M` is the sum of `b^i`
for `i = 0, …, n+1`, and `K = (1+d+n+p)^M`. The ambient nonterminal type remains
arbitrary, including infinite types. No grammar normalization is assumed.

`BoundedFamilySupport.lean` constructs a classical finite covering family for
counting. At height zero it contains terminal leaves and active holes. At the
next height it includes production nodes with all child tuples of that
production's fixed arity. Dropping child-root compatibility only enlarges the
family. Mathlib's finite function-space cardinality bounds each tuple family,
and its finite union bounds yield the recurrence
`card(F_(H+1)) ≤ q * (q^P_H)^b`, where `P_H = ∑ i≤H, b^i` and `q = 1+d+n+p`.
The identity `P_(H+1) = 1 + b*P_H` gives `card(F_H) ≤ q^P_H` by induction.
Filtering the cover yields the exact base and cycle families. This cover is
noncomputable proof support; the earlier executable enumerator remains the
algorithm for valid trees and preserves ordered child roots.

A separate height induction bounds terminal-yield length by `P_H`, using
Mathlib's bounded-list-sum inequality. The total terminal-count norm equals
yield length by Mathlib's occurrence-count sum law. Simple bases have height
at most `n`; bounded cycles have height at most `n+1`, and their unique holes
are active by the proved root-in-support result. Together these give the
frozen theorem without extra assumptions.

All previously published declarations remain in their original modules.
The counting proof uses the existing generated height, holes and yield equations,
keeping the executable enumerator and its helpers untouched. Every earlier
signature and definition fingerprint is preserved by the contract audit.
No new datatype, instance, Mathlib import, cache target, partial runtime helper,
unsafe declaration or project axiom is introduced. Lean/Mathlib pins, the
baseline and checker remain unchanged. All **609 earlier entries** are preserved.
The manifest appends **35 entries** (15 named counting declarations and 20
generated proof/equation helpers), for **644 declarations** in total. Only the
completed theorem's direct and transitive obligation-list entries are removed.

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

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `docs/contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| Construction | `bounded_witness`, `witness_bit_bound` |

`ActivationTest` and `BoundedEnumeration` have executable implementing values
with proved correctness fields. `Compiler` still has no implementing value;
its `correct` and `bounded` fields remain requirements. The theorem-hole count
does not account for that missing compiler. Enumeration alone does not yet
compute a semilinear witness.

## Validation

- Affected modules and full `lake build` pass, with only the two tracked bounds-hole warnings in `Construction.lean`.
- `lake env lean scripts/SkeletonExamples.lean` passes, including numeric `M = 4`, `K = 625` and exact bounded families for an empty terminal alphabet with infinite ambient nonterminals and an empty production. All earlier examples still pass.
- Contract checking audits 644 declarations, preserves every earlier fingerprint and reports direct holes / transitive holes / project axioms as **2 / 2 / 0**.
- `#print axioms` for the completed theorem and counting/leaf-weight support reports only standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx` or project axioms.
- `git diff --check` passes.
- Final-mode checking still rejects the two outstanding theorem holes. Whole-project completion also requires exact executable witness compilation.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned dependency/cache access and GitHub read/write access are available. CI evidence is reported separately in the PR.

Next eligible milestone: construct an exact semilinear witness satisfying
`WithinBounds`, using the proved finite-family and leaf-weight budgets. The
executable compiler must reuse enumeration and activation testing, retain
context identities and handle duplicate input productions. The separate bit
budget proof also remains. Keep accepted contracts unchanged and publish one
coherent increment per PR, stopping for review.
