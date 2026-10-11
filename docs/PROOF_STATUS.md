# Proof status: certified executable compiler complete

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previously published declaration fingerprints are
unchanged. All proof increments through [PR #26](https://github.com/focs-lab/parikh-theorem/pull/26)
have merged, with CI passing. Documentation PRs #18/#19 and the math-rendering
fix in PR #21 have also merged.

Current milestone: the certified executable grammar-to-witness compiler
(`sec:effective`, `eq:main`, `thm:size-bound`, `eq:bit-bound`), branch
`codex/executable-compiler`, based on merged `main`
(`d89ece29dadbdc519f34e8c85f09f459ab4e5201`).
Published as [PR #27](https://github.com/focs-lab/parikh-theorem/pull/27);
the PR's [checks](https://github.com/focs-lab/parikh-theorem/pull/27/checks)
record CI evidence for the submitted head.
There are **0 direct `sorry` obligations**, **0 project axioms**, and **0
transitively unresolved declarations**. The public `compiler` now implements
the accepted interface with exact-denotation and all four size proofs. The
forward theorem, exact finite witnesses, converse, regular specialization,
executable construction and all specified quantitative bounds are complete on
this branch, subject to the owner's PR review.

## Completed in this milestone

`ExecutableCompiler.lean` supplies `EncodedGrammar.compile` and the public
`compiler : Compiler`. The computed witness satisfies:

| Guarantee | Checked declaration |
| --- | --- |
| Exact grammar Parikh image | `EncodedGrammar.compile_correct`, `compiler.correct` |
| All four declared-size bounds | `EncodedGrammar.compile_bounded`, `compiler.bounded` |
| Fixed-width coordinates and numerical entry-bit budget | `EncodedGrammar.compile_bit_bound` |

`CompilerSupport.lean` compares existing tree syntax through an explicit height
budget using `Nat.rec` and `List.isEqv`. The correctness lemma yields computable
structural equality for deduplication, without a global instance or new partial
helper. `listComponent_denotation` proves that list-order assembly has exactly
the mathematical component's denotation. `contextActivation_correct` connects
the existing activation test on finite production-label supports to the frozen
grammar activation predicate, using actual tree identities.

`CompilerTrees.lean` computes the active alphabet, proves agreement with
`activeNonterminals`, and filters the certified enumeration into exact base
and cycle lists. Cycle height uses the active count; enumeration uses the larger
declared finite height. Only repeated syntax is removed. Distinct contexts
with equal or zero weights remain different list positions.

`CompilerBounds.lean` applies the existing counting cover at the declared height.
The active alphabet is at most the declared nonterminal count, and production
arity is at most the existing encoded branching budget. Thus the exact lists
have at most `K` trees and each weight has norm at most `M`, even when input
productions repeat or some declared symbols are unused.

For each base, the compiler lists every cycle sublist, filters using the proved
activation test, and assembles its list component. Exact membership and component
bridges let `compile_correct` reuse `treeRepresentation_correct` for both
inclusions. Mathlib's sublist/filter/length laws bound output cardinality;
`contextComponent_size_bounds` bounds output norms, and `witness_bit_bound`
provides the bit corollary. The result may include overlapping components, as
the accepted contract allows; it is exact without claiming a minimal witness.

All **661 earlier contract entries** are preserved. The manifest appends
**76 entries** (31 named declarations and 45 generated proof/equation/matcher
helpers), for **737 declarations** in total. Every previously published theorem
remains in its original module. The baseline, checker, obligation allowlists,
definition meanings and Lean/Mathlib pins are unchanged. Existing construction
comments are updated to identify the implementing value; no definition or
statement changes. There is no new Mathlib import/cache target, datatype,
global instance, partial runtime helper, unsafe declaration or project axiom.

The runtime definitions are computable and execute without classical finite-set
listing or selection. Their axiom reports disclose standard foundations inherited
through certified equality and proof fields; they are not axiom-free kernel
expressions. The eleven previously allowlisted compiler-generated recursion
helpers remain separately audited. All logical proofs are kernel checked;
no `native_decide` or runtime proof override is introduced.

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

- [PR #26](https://github.com/focs-lab/parikh-theorem/pull/26): `witness_bit_bound`, proving fixed-width coordinate fit and total numerical entry-bit bounds; CI now requires final-mode checking (`eq:bit-bound`).

## Remaining work

No named mathematical proof or executable-construction obligation remains.
`ActivationTest`, `BoundedEnumeration` and `Compiler` all have computable
implementing values with complete correctness fields. The theorem-hole and
project-axiom allowlists are empty. This increment awaits owner review and merge.

The construction is deliberately coarse: tree enumeration and the context
powerset can be very large. Optimization, additional convenience interfaces
and release packaging are optional follow-up work, not missing formalization
contracts. The repository has no selected license metadata; release publication
and license choice remain owner decisions.

## Validation

- Affected compiler modules and full `lake build` pass without proof-hole warnings.
- `lake env lean scripts/SkeletonExamples.lean` passes. It checks the public compiler fields and asserts computed outputs for empty rules, epsilon/empty alphabets, distinct silent contexts, duplicate productions, unreachable cycles and unary recursion. All earlier examples pass.
- The unary example executes to `[([0], []), ([1], [[1]]), ([2], [[2]]), ([3], [[1], [2]])]`; empty rules give no component, epsilon gives one zero component, and separate silent contexts retain two independent zero-period positions.
- `python3 scripts/check-contracts.py --final` audits 737 declarations, preserves all 661 prior fingerprints and reports direct holes / transitive holes / project axioms as **0 / 0 / 0**.
- `#print axioms` for `EncodedGrammar.compile`, `compile_correct`, `compile_bounded` and `compiler` reports only standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx` or project axioms. The same audit checks all new helper declarations.
- The previously audited partial-helper set is unchanged at eleven entries. No unsafe declaration or unlisted runtime helper is added.
- `git diff --check` passes; Lean 4.34.1 / Lake 5.0.0 and pinned Mathlib/GitHub access are verified in Codex Cloud. Final-head CI evidence is reported in the PR.

Read [COMPILER.md](COMPILER.md) for the public executable API, a complete small
execution, the correctness/budget fields and the implementation's practical
limits. Preserve all accepted contracts and stop for the owner's review.
