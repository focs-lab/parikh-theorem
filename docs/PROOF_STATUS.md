# Proof status: executable bounded-tree enumeration

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11. The immutable baseline remains the reviewed head
`6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, including the requested `ParseTree`
rename. Its pointer and all previous contract fingerprints remain unchanged.
All proof increments through [PR #22](https://github.com/focs-lab/parikh-theorem/pull/22)
have merged, with CI passing. Documentation PRs #18/#19 and the math-rendering
fix in PR #21 have also merged.

Current milestone: executable bounded-tree enumeration (`lem:finite`,
`sec:effective`), branch `codex/bounded-tree-enumeration`, based on merged `main`
(`d490885f9c64567a379a6036198d1bd31870e5ce`).
The PR and CI evidence will be linked after publication.
There are **3 direct `sorry` obligations**, zero project axioms, and 3 declarations
transitively dependent on `sorryAx`, unchanged here. All accepted qualitative
Parikh results are proved. Activation testing and bounded-tree enumeration now
have executable implementations with complete correctness proofs. Full witness
compilation and quantitative bounds remain.

## Completed in this milestone

`boundedEnumeration` is a computable value of the accepted `BoundedEnumeration`
interface. For every encoded grammar `g`, height `H` and tree `t`, its checked
`correct` field proves:

```lean
t ∈ boundedEnumeration.enumerate g H ↔ Valid g.decode t ∧ t.height ≤ H
```

The result includes valid open trees with arbitrary declared holes, not only
complete trees or trees rooted at the start symbol. Unused terminal and
nonterminal declarations are included. Duplicate productions may cause repeated
trees; the accepted list contract requires exact membership, not `Nodup`.
Production identity and child order remain part of the original `ParseTree`.

The new `BoundedEnumeration.lean` module contains nine named declarations:

| Declaration (namespace `Parikh`) | Role |
| --- | --- |
| `ParseTree.height_node_eq` | Express a node's height as one plus its largest child height. |
| `ParseTree.height_node_le_iff` | A node fits bound `H+1` exactly when each child fits `H`. |
| `ParseTree.mem_root_sections` | Root-filtered Cartesian products preserve child membership and ordered root matching. |
| `Valid.node_iff` | Eliminate node validity into rule membership, child validity and exact ordered roots. |
| `EncodedGrammar.leaves` | Enumerate all declared terminal and nonterminal leaves using `List.finRange`. |
| `EncodedGrammar.leaves_correct` | The leaf list is exactly the valid height-zero family. |
| `EncodedGrammar.enumerateTrees` | Enumerate larger trees by finite production choices and Mathlib `List.sections`. |
| `EncodedGrammar.enumerateTrees_correct` | Prove both directions of the exact membership contract by height induction. |
| `boundedEnumeration` | Package the runtime with its complete correctness field. |

At height zero, only terminal leaves and holes are possible. At the successor
bound, each production fixes an ordered list of required child roots. Filter the
previous family by each root, take its ordered Cartesian product, and map each
child list to that production node. Mathlib's product membership law and the
child-height equivalence prove soundness and completeness. An empty output has
one empty child tuple and therefore generates a height-one production node.
The algorithm terminates by explicit `Nat.rec` on the height bound.

The two runtime definitions, `leaves` and `enumerateTrees`, have no axiom
dependencies. The proofs and packaged interface depend only on standard Lean
foundations (`propext`, `Classical.choice`, `Quot.sound`); none depends on `sorryAx`
or a project axiom. There is no classical runtime selection, new tree datatype,
instance, partial helper or unsafe declaration.

All 587 earlier contract entries are preserved. The manifest appends 22 entries:
nine named declarations and thirteen generated proof/equation/matcher helpers,
for **609 declarations** in total. Baseline, checker, obligation allowlists,
existing statements and definition meanings, and Lean/Mathlib pins are unchanged.
`Construction.lean` changes only explanatory comments. The sole new Mathlib
import/cache target is `Mathlib.Data.List.Sections`, included in CI and the build
guide; the selected cache was fetched successfully in Codex Cloud.

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

All prior statements, definition meanings and proof bodies are unchanged here.
The grammar/tree bridge still supports arbitrary derivation order and ambient
nonterminal types. Classical semantic existence is distinguished from the two
implemented executable interfaces.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `docs/contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |

`ActivationTest` and `BoundedEnumeration` now have executable implementing values
with proved correctness fields. `Compiler` still has no implementing value;
its `correct` and `bounded` fields remain requirements, not assumed theorems.
The small remaining theorem-hole count does not account for that missing compiler.
In particular, enumeration alone does not yet compute a semilinear witness.

## Validation

- Affected modules and full `lake build` pass, with only the three tracked bounds-hole warnings in `Construction.lean`.
- `lake env lean scripts/SkeletonExamples.lean` passes. Kernel-checked examples cover all declared height-zero roots, a duplicate production, a unit cycle, empty alphabets/productions and no productions. The exact correctness field proves inclusion at height two, exclusion at height one, and exclusion of reversed child order. Compiled evaluation returns tree counts `[4, 8, 14]` at successive height bounds and epsilon-tree `(height, hole-count)` pairs `[(0, 1), (1, 0)]`. Earlier examples still pass.
- `python3 scripts/check-contracts.py` audits 609 declarations, preserving all 587 earlier fingerprints with an append-only manifest extension. Direct holes / transitive holes / project axioms remain **3 / 3 / 0**.
- `#print axioms` for all nine new named declarations reports no unresolved dependencies; the two runtime definitions have no axioms.
- `git diff --check` passes.
- Final-mode contract checking continues to reject the three outstanding bounds holes. Whole-project completion also requires exact executable witness compilation.
- Cloud Lean 4.34.1 / Lake 5.0.0, pinned dependency/cache access and GitHub read/write access are available. CI evidence is reported separately in the PR.

Next eligible theorem work: the quantitative finite-family cardinality and
leaf-weight bounds in `bounded_family_bounds` (`lem:count-trees`). These support
witness bounds and a complete `Compiler` value, whose accepted interface requires
both exact denotation and size bounds. Executable witness assembly must retain
context identities, handle duplicate input productions, and reuse the proved
enumerator and activation test. Keep accepted contracts unchanged and publish
each coherent increment as a new PR.
