# Proof map

Read the [proof guide](../docs/PROOF_GUIDE.md) alongside the
[mathematical reference](../reference/parikh_theorem.tex). The labels below
refer to that reference. All listed results are proved.

## Source modules

| Part | Modules in `Parikh/` |
| --- | --- |
| Public interface | `Api`, `Statements` |
| Count vectors and semilinear representations | `Counting` |
| Tree semantics and positions | `GrammarTrees`, `ParseTreePaths` |
| Plugging and subtree replacement | `TreePlugging`, `TreeReplacement`, `InsertionSequences` |
| Bounded cuts and decomposition | `BoundedCutSupport`, `Decomposition` |
| Activation and finite representation | `Activation`, `ActivationAlgorithm`, `FiniteRepresentation`, `GrammarImage` |
| Regular-language realization | `RegularRealization`, `WordBlockAutomata`, `DFAGrammar` |
| Enumeration and bounds | `Construction`, `BoundedEnumeration`, `BoundedFamilySupport`, `FiniteWitness` |
| Executable compiler | `CompilerSupport`, `CompilerTrees`, `CompilerBounds`, `ExecutableCompiler` |
| JSON interface | `Cli`, `../cli/Main.lean` |

## Main results

Declaration names are in namespace `Parikh`. This map uses the underlying proof
names; [Api.lean](../Parikh/Api.lean) supplies the descriptive client names.

| Source label | Declaration | Meaning |
| --- | --- | --- |
| `eq:word-add` | `counts_append` | Concatenation adds count vectors. |
| `sec:statement` | `Component.denotation`, `Witness.denotation`, `exists_witness` | Concrete descriptions and their bridge to Mathlib semilinearity. |
| `prop:tree-word`, `app:derivations` | `derives_iff_tree` | Complete trees and grammar derivations describe the same words. |
| `lem:plug` | `plugging` | Plugging preserves validity and adds counts, size, and support. |
| `lem:enabled`, `lem:insertion-laws` | `insertion_enabled`, `insertion_accounting` | Matching occurrences enable insertion with exact accounting. |
| `cor:sequence` | `InsertionSequence.accounting` | Accounting extends to insertion sequences. |
| `lem:simple-height`, `lem:finite` | `simple_height`, `bases_finite`, `bounded_cycles_finite` | Base and cycle families are finite. |
| `lem:cut` | `bounded_cut` | A non-simple tree admits a bounded cut that decreases production count. |
| `thm:decomposition` | `decomposition` | Exact reconstruction from a base and bounded contexts. |
| `lem:activation-realize` | `activationOrder_iff_insertionSequence`, `ContextsActivatable.realize` | Activation orders are realized by tree insertions. |
| `lem:first-occurrence`, `lem:multiplicities` | `first_occurrences`, `positive_multiplicities` | First copies enable arbitrary additional repetitions. |
| `prop:one-linear` | `one_linear` | An activatable family gives exactly one linear set. |
| `thm:main` | `treeRepresentation_eq`, `grammar_witness` | The finite tree formula equals the grammar's image. |
| `thm:parikh-statement` | `grammar_image`, `contextFree_image` | Forward Parikh theorem. |
| `thm:converse` | `witnessExpression_correct`, `converse` | A semilinear set is the image of a regular language. |
| `thm:parikh-statement` | `regular_realization`, `regular_image` | Equal-image regular realization and the regular specialization. |
| `lem:activation-test` | `activationTest`, `activationRounds_correct` | Executable activation decision with an exact Boolean result. |
| `lem:finite`, `sec:effective` | `boundedEnumeration`, `EncodedGrammar.enumerateTrees_correct` | Complete enumeration through a height bound. |
| `lem:count-trees` | `bounded_family_bounds` | Bounds on tree counts and terminal weights. |
| `thm:size-bound` | `bounded_witness`, `EncodedGrammar.compile_bounded` | Component, period, and norm bounds. |
| `eq:bit-bound` | `witness_bit_bound`, `EncodedGrammar.compile_bit_bound` | Coordinate widths and numerical entry-bit bounds. |
| `sec:effective` | `compiler`, `EncodedGrammar.compile_correct` | Computation with exact Parikh-image denotation. |

## Invariants used by the proof

Production-node count is the decreasing measure for decomposition. Holes
contribute neither a production node nor a nonterminal to support. Positions
identify occurrences for replacement. Context identities remain distinct until
activation is checked, even if their weights agree. Every selected context
contributes once to the base before further copies become periods.

General grammar results allow arbitrary nonterminal types: the finite rules
and start symbol determine the active alphabet. Existence theorems use a finite
terminal alphabet; the executable compiler uses numeric finite labels.
