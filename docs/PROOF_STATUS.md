# Proof status: DFA regularity and converse realization

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #16](https://github.com/focs-lab/parikh-theorem/pull/16)
have merged, with CI passing.

Current milestone: [PR #17](https://github.com/focs-lab/parikh-theorem/pull/17),
DFA regularity of witness expressions and converse realization,
branch `codex/witness-dfa-regularity`, based on merged `main`
(`827f731822028459f17b6f83b448ae86ba27affc`).
CI evidence is recorded in the PR.
There are **4 direct `sorry` obligations**, zero project axioms, and 4 declarations
transitively dependent on `sorryAx`, down from 7. The forward theorem, exact finite
witness existence, converse, and equal-image regular realization are proved.
Regular-language specialization, executable construction, and quantitative bounds remain.

## Completed in this milestone

Three accepted public contracts now have complete proofs:

| Declaration (namespace `Parikh`) | Result |
| --- | --- |
| `witnessExpression_correct` | The expression has exactly the indexed witness image and is regular according to Mathlib's finite-state DFA predicate (`thm:converse`). |
| `converse` | Every semilinear set over a finite terminal alphabet is the exact Parikh image of a DFA-regular language (`thm:converse`). |
| `regular_realization` | Every Mathlib grammar has a DFA-regular language with the same Parikh image (`thm:parikh-statement`). |

Their signatures and all referenced meanings are unchanged. They are removed
from both unresolved allowlists. The grammar theorem still permits arbitrary
ambient nonterminal types.

Six immediately proved adapters in the new `WordBlockAutomata.lean` module
supply the specialized regularity operations required by this construction:

| Declaration (namespace `Parikh`) | Role |
| --- | --- |
| `isRegular_of_finite_language_cover` | A finite family of continuation languages covering every one-letter continuation gives a sound and complete finite NFA; Mathlib's subset construction gives its DFA. |
| `isRegular_zero` | A rejecting NFA realizes the empty language. |
| `isRegular_one` | An accepting NFA with no transitions realizes epsilon. |
| `mem_word_mul_cons` | Reading the head of a literal-word prefix leaves the tail as the prefix. |
| `isRegular_word_mul` | Prepending a fixed word preserves DFA regularity. |
| `isRegular_word_star_mul` | Prepending any number of copies of a fixed word preserves DFA regularity, including an empty repeated word. |

The NFA states are an existing finite subtype of languages. A transition from
`K` to `J` on `a` requires every word in `J` to continue to a word of `K` after
reading `a`; the cover hypothesis gives a successor for every accepted
continuation. Induction on the input word proves the NFA accepts exactly the
starting language. `NFA.toDFA_correct` and `Language.isRegular_iff` supply
finite-state DFA regularity without new determinization infrastructure.

For a fixed-word prefix, the finite family consists of all continuation-DFA
state languages together with the prefixed word's finitely many suffixes followed
by that continuation. For a starred-word prefix, suffix states instead lead
back to the same starred prefix. Mathlib's Kleene-star unfolding law allows a
choice between starting another copy and entering the continuation DFA. The
empty repeated word simplifies using `kstar_one`, without epsilon-loop reasoning.
No general regex-to-DFA equivalence, generic concatenation/star closure, new
language semantics, global data definitions, or instances are introduced.

Three proved adapters in `RegularRealization.lean` combine these operations:
`periodExpressions_regular`, `componentExpression_regular`, and
`witnessExpression_regular`. The last reuses Mathlib's regular finite-union law.
The existing image proof completes `witnessExpression_correct`. Classical
finite alphabet ordering and `exists_witness` give `converse`; the already
proved forward theorem gives `regular_realization`.

All twelve completed public/support declarations depend only on standard Lean
foundations: `propext`, `Classical.choice`, and `Quot.sound` (a subset suffices for
`mem_word_mul_cons`). None depends on `sorryAx` or a project axiom.
All **548 prior contract entries** are preserved exactly. Nine proved helpers
and six generated simplification declarations extend the manifest to **563 entries**.
No earlier declaration is deleted or moved. The checker, immutable baseline,
existing signatures and definition meanings, instances, and Lean/Mathlib pins
are unchanged. The new module imports Mathlib NFA and finite-range infrastructure;
NFA is added to the documented and CI cache selections. All existing cache
selections remain.

These regularity and converse proofs establish semantic existence. The finite
state family and transitions use classical language equality and inclusion;
this is not an executable grammar compiler or a new compiler implementation.

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

Their statements and proofs are unchanged here. The grammar/tree bridge supports
arbitrary derivation order and nonterminal types. Witness existence and tree
semantics are semantic proofs, not executable compiler implementations.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| RegularRealization | `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems. The exact finite
grammar witness and regular-language realization are classical existence proofs.
The small remaining theorem-hole count does not account for those unimplemented
algorithm values.

## Validation

- Affected modules and full `lake build` pass, with only expected theorem-hole warnings in the 4 remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. New examples distinguish an empty union from epsilon over an empty alphabet, exhibit a finite DFA accepting the ordered repeated-word language while rejecting an equal-count permutation, and show that equal-image realization of an unproductive grammar is actually empty despite infinite ambient nonterminals. All previous semantic examples still pass.
- `python3 scripts/check-contracts.py` checks 563 declarations against the accepted skeleton and merged `main`, preserving all 548 earlier contracts. The checker and baseline pointer are unchanged.
- `#print axioms` for the twelve completed declarations reports only standard foundations, with no unresolved dependencies.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 4 outstanding holes. Full project completion still requires regular specialization, executable algorithms with checked correctness, and bounds.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned dependency access, the newly selected NFA cache, and GitHub authentication/read/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible work: `regular_image`, using a thin Mathlib DFA-to-grammar bridge
or finite-path specialization. Then supply executable activation and bounded
syntax enumeration, assemble the exact compiler with correctness proofs, and
prove the quantitative bounds. Keep accepted contracts unchanged and publish
each coherent increment as a new PR.
