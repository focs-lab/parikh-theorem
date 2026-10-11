# Proof status: exact images of the witness expressions

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #15](https://github.com/focs-lab/parikh-theorem/pull/15)
have merged, with CI passing.

Current milestone: [PR #16](https://github.com/focs-lab/parikh-theorem/pull/16),
representative counting and exact expression images,
branch `codex/witness-expression-image`, based on merged `main`
(`481c029f74539db64bbc1d7bcc3a9db3126d46a0`).
CI evidence is recorded in the PR.
There are **7 direct `sorry` obligations**, zero project axioms, and 7 declarations
transitively dependent on `sorryAx`, down from 8. The forward theorem is proved.
Expression-image correctness is now proved; DFA regularity, the converse,
regular specialization, executable construction, and quantitative bounds remain.

## Completed in this milestone

The accepted `representative_counts` contract now has a checked proof
(`eq:representative`). For each letter, Mathlib's `List.count_flatten`,
`List.count_replicate`, and `List.sum_map_eq_nsmul_single` reduce the count to the
alphabet list's one occurrence of that letter. Exhaustiveness and `Nodup` supply
that occurrence. The empty terminal alphabet needs no special assumption.

Six new, immediately proved adapters in `RegularRealization.lean` establish
both inclusions of the exact-image construction:

| Declaration (namespace `Parikh`) | Role |
| --- | --- |
| `wordExpression_matches` | A literal-word expression accepts exactly its word. |
| `image_mul` | Concatenation of languages becomes pointwise addition of their Parikh images. |
| `wordExpression_star_image` | The star of a literal word realizes the additive closure of its count vector, including zero repetitions and the empty word. |
| `periodExpressions_image` | The ordered product of starred period words realizes the additive closure of the period values. |
| `componentExpression_image` | Each component expression has exactly its accepted indexed linear denotation (`lem:linear-regular`). |
| `witnessExpression_image` | The finite union expression has exactly the witness denotation (`eq:regular-construction`, `thm:converse`). |

The period proof reuses Mathlib's `AddSubmonoid.closure_union` and `mem_sup`.
The existing `Component.denotation_eq_vadd_closure` identifies this closure with
independent natural coefficients at every period-list position. No replacement
coefficient semantics, permutation closure, or language datatype is introduced.
Zero and repeated periods, an empty period list, an empty witness, and an empty
alphabet are all covered.

The frozen `witnessExpression_correct` theorem is retained with exactly its
original signature. Its first conjunct now uses `witnessExpression_image`;
**only its DFA-regularity conjunct remains a hole**. Neither this combined theorem
nor `converse`, `regular_realization`, or `regular_image` is claimed as completed.
The pinned Mathlib provides regex semantics but explicitly lacks general
regex-to-DFA equivalence; `DFA.lean` also has no concatenation/star regularity
lemmas. The next milestone should prove DFA regularity of these constructed
finite unions of word-block products, reusing existing automata conversion.
A general regex-equivalence development is unnecessary.

All seven completed declarations depend only on standard Lean foundations:
`propext`, `Classical.choice`, and `Quot.sound` (a subset suffices for `image_mul`).
None depends on `sorryAx` or a project axiom. All existing definitions, instances,
and previously completed proofs are retained.

All **530 prior contract entries** are preserved exactly. The six proved
adapters and twelve generated equation/simplification declarations extend the
manifest to **548 entries**, including equations for the existing `image` and
`witnessExpression` definitions. No previous declaration is deleted or moved.
The checker, immutable baseline, existing signatures and definition meanings,
instances, Lean/Mathlib pins, imports, and cache targets are unchanged.
Only `representative_counts` is removed from both unresolved allowlists.

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

Their statements and proofs are unchanged here. The grammar/tree bridge supports
arbitrary derivation order and nonterminal types. Witness existence and tree
semantics are semantic proofs, not executable compiler implementations.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| RegularRealization | `witnessExpression_correct` (DFA clause only), `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems. The existing exact
finite grammar witness is classical existence, not an executable compiler.

## Validation

- Affected module and full `lake build` pass, with only expected theorem-hole warnings in the 7 remaining obligations.
- `lake env lean scripts/SkeletonExamples.lean` passes. New examples distinguish an empty witness from epsilon over an empty alphabet, check a singleton component with no periods, and exercise zero and duplicate periods with independent coefficients. An equal-count word in a different letter order is excluded from the expression language while its vector belongs to the exact image. Earlier grammar, tree, activation, decomposition, and witness examples still pass.
- `python3 scripts/check-contracts.py` checks 548 declarations against the accepted skeleton and merged `main`, preserving all 530 earlier contracts. The checker and baseline pointer are unchanged.
- `#print axioms` for the seven completed declarations reports only standard foundations, with no unresolved dependencies. The combined `witnessExpression_correct` still reports `sorryAx`, as recorded above.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 7 outstanding holes. Full project completion still requires DFA regularity, the converse and regular specialization, algorithms, and bounds.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned dependency access and selected Mathlib cache, and GitHub authentication/read/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible work: DFA regularity of the constructed expressions, completing
`witnessExpression_correct`, then `converse` and `regular_realization`.
`regular_image` requires the separate Mathlib DFA-to-grammar bridge or finite-path
specialization. Executable algorithms with checked correctness and quantitative
bounds remain separately tracked. Keep accepted contracts unchanged and publish
each coherent increment as a new PR.
