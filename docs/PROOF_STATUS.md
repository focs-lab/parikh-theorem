# Proof status: regular-language specialization

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #17](https://github.com/focs-lab/parikh-theorem/pull/17)
have merged, with CI passing. The independent README guide in
[PR #18](https://github.com/focs-lab/parikh-theorem/pull/18) has also merged.

Current milestone: regular-language specialization (`regular_image`),
branch `codex/regular-language-image`, based on merged `main`
(`08d1dfbb1177505ae936a722da8580ea900e5b66`).
The PR and CI evidence will be linked after publication.
There are **3 direct `sorry` obligations**, zero project axioms, and 3 declarations
transitively dependent on `sorryAx`, down from 4. All accepted qualitative Parikh
results are now proved: forward semilinearity, exact finite witness existence,
converse, equal-image regular realization, and regular-language specialization.
Executable construction and quantitative bounds remain.

## Completed in this milestone

The accepted public contract `regular_image` is proved: every Mathlib DFA-regular
language over a finite terminal alphabet has a semilinear Parikh image
(`thm:parikh-statement`). Its signature and all referenced meanings are unchanged.
It is removed from both unresolved allowlists.

The new `DFAGrammar.lean` module is a thin adapter between existing Mathlib types:

| Declaration (namespace `Parikh`) | Role |
| --- | --- |
| `dfaGrammar` | A finite DFA becomes a Mathlib right-linear grammar: a transition emits its letter and next state; an accepting state may erase itself. |
| `dfaGrammar_derives_iff` | From every state, deriving a terminal word is equivalent to DFA acceptance started at that state. |
| `dfaGrammar_language` | The grammar language equals the DFA language exactly, preserving word order, epsilon, rejection and empty alphabets. |

For derivation soundness, each reachable sentential form is either a terminal
prefix followed by its reached DFA state, or a completed accepted terminal word.
There is exactly one possible nonterminal position; terminal-only forms cannot
rewrite. Induction over Mathlib's relation closure preserves this invariant.
For completeness, induction over the input word applies its transition rules
and finishes with an accepting-state erasure. No grammar/tree semantics, DFA
semantics, determinization, regex equivalence or general automata theory is
reimplemented. The pinned Mathlib sources have no DFA-to-context-free-grammar
adapter, as recorded in `MATHLIB_REUSE.md`.

The new shared `GrammarImage.lean` module proves `treeRepresentation_correct`,
combining the already checked exact tree union proof with its semilinearity.
The existing `treeRepresentation_eq` and `grammar_image` remain in
`Statements.lean` with their exact signatures; their proofs project the shared
result. This permits `regular_image` to reuse the forward proof without creating
an import cycle. The general grammar theorem still allows arbitrary ambient
nonterminal types. Only the adapter has finite DFA states.

Six previously generated simplification declarations belonging to
`periodExpressions_image` are now retained explicitly with their exact old
names, kernel types and universe parameters, reconstructed from the same Mathlib
proofs using kernel-checked theorem declarations. The same proof uses these equalities
instead of depending on which imported module first preprocesses a Mathlib
lemma. This preserves every frozen helper; no theorem is deleted or moved.

All **563 prior contract entries** are preserved exactly. Four new support
declarations and five generated declarations extend the manifest to **572 entries**.
The completed public/support proofs, including the refactored forward proofs
and retained simplifier equalities, use only standard Lean foundations:
`propext`, `Classical.choice`, and `Quot.sound`. None depends on `sorryAx` or a
project axiom. The checker, immutable baseline, instances, existing definition
meanings, Lean/Mathlib pins and cache selection are unchanged.

The DFA-to-grammar adapter uses classical finite filtering. It supplies semantic
correctness for this specialization and is not an executable compiler. Algorithm
implementations and their correctness proofs remain separate work.

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

All prior statements and meanings are unchanged. Only the forward equality and
semilinearity proof bodies are factored here, and the six generated simplifier
equalities are retained explicitly. The grammar/tree bridge supports
arbitrary derivation order and nonterminal types. Witness existence and tree
semantics are semantic proofs, not executable compiler implementations.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `docs/contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` remain concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems. The exact finite
grammar witness and regular-language realization are classical existence proofs.
The small remaining theorem-hole count does not account for those unimplemented
algorithm values.

## Validation

- Affected modules and full `lake build` pass (1321 jobs), with only the 3 expected theorem-hole warnings in `Construction.lean`.
- `lake env lean scripts/SkeletonExamples.lean` passes. A concrete three-state DFA accepts epsilon and repeated `false true` blocks while rejecting an equal-count permutation; its grammar accepts precisely these words. A noninitial state can derive its accepted continuation. Empty-alphabet accepting and rejecting DFAs retain their epsilon distinction and both have semilinear images. All earlier examples still pass.
- `python3 scripts/check-contracts.py` checks 572 declarations, preserving all 563 earlier contracts. The checker and baseline pointer are unchanged.
- `#print axioms` for the completed adapter, shared support, regular specialization, retained simplifier equalities and existing forward/converse declarations reports only standard foundations, with no unresolved dependencies.
- `git diff --check` passes.
- `python3 scripts/check-contracts.py --final` correctly rejects the 3 outstanding holes. Full project completion still requires executable algorithms with checked correctness and quantitative bounds.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned dependency access, selected cache, and GitHub authentication/read/push access were verified. CI results are reported in the PR separately from local validation.

Next eligible work: implement the finite `ActivationTest` algorithm and prove
its `correct` contract. Then implement bounded syntax enumeration, assemble the
exact compiler with correctness proofs, and prove the quantitative bounds.
Keep accepted contracts unchanged and publish each coherent increment as a new PR.
