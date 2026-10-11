# Proof status: counting and finite-witness bridges proved

The owner accepted the reviewed skeleton in [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2)
on 2026-10-11 and authorized its merge and the next proof milestone. The immutable
baseline is the reviewed head `6bff9679d7ea03e5401815b80c5a3dc1300f9d36`, which
includes the requested `ParseTree` rename. The baseline pointer is now recorded
in `contracts/baseline.json`; no existing contract fingerprints were changed.

Current milestone: [PR #3](https://github.com/focs-lab/parikh-theorem/pull/3),
branch `codex/counting-witness-proofs`, based on merged `main`.
There are **24 direct `sorry` obligations**, zero project axioms, and 24 declarations
transitively dependent on `sorryAx`. Parikh's theorem is not yet proved.

## Completed in this milestone

All names have namespace `Parikh`.

| Declaration | Proof and source |
| --- | --- |
| `counts_append` | Coordinatewise Mathlib `List.count_append`; `eq:word-add`. |
| `Component.denotation_eq_vadd_closure` | New helper identifying indexed natural-coefficient sums with Mathlib's finite-range additive closure. Reuses `AddSubmonoid.mem_closure_range_iff_of_fintype`. |
| `component_isLinearSet` | The period values form a finite range; apply the closure helper to the existing definition of linearity. |
| `witness_isSemilinearSet` | Rewrite witness denotation as a finite union and reuse Mathlib's semilinear union theorem. |
| `exists_witness` | Enumerate each finite generator set as a list, identify its range, and induct over the finite family of linear components. |

These proofs support arbitrary terminal types, empty period/witness lists,
duplicate and zero periods. They require no grammar assumptions or finite-alphabet
restriction beyond the original statements. `exists_witness` is an existence
result; its use of classical finite-set enumeration is not an executable grammar
compiler.

The axiom audit finds no `sorryAx` or project-axiom dependencies in any completed
declaration or new helper. Only standard Lean foundations (`propext`,
`Classical.choice`, `Quot.sound`) occur. The append-only manifest extension records
one new public helper and nine Lean-generated simplification/equation lemmas.

## Remaining named theorem obligations

Every entry below is directly and transitively incomplete. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI.

| Module | Outstanding declarations |
| --- | --- |
| GrammarTrees | `derives_iff_tree`, `complete_support_active`, `bounded_open_finite` |
| Decomposition | `plugging`, `insertion_enabled`, `insertion_accounting`, `simple_height`, `bounded_cut`, `decomposition` |
| Activation | `first_occurrences`, `positive_multiplicities`, `one_linear` |
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

`ActivationTest`, `BoundedEnumeration`, and `Compiler` are concrete structures
specifying future finite algorithms, with no implementing values yet. Their
correctness fields are requirements, not assumed theorems. No effectivity claim
follows from the completed witness-existence lemma.

## Validation

- `lake build` succeeds, with 24 expected theorem-hole warnings in other modules.
- `lake env lean scripts/SkeletonExamples.lean` checks the existing small semantic examples.
- `python3 scripts/check-contracts.py` checks 344 declarations against the accepted
  skeleton and the current base. All earlier signatures and non-proof definition
  fingerprints are preserved; pins and the audit implementation are unchanged.
- `git diff --check` checks whitespace.
- `python3 scripts/check-contracts.py --final` correctly rejects the 24 outstanding
  holes. No completed milestone is presented as completion of the whole theorem.
- The selected-cache command now includes the reused Mathlib submonoid/Finsupp
  module. CI result is reported in the PR separately from local validation.

Next eligible milestone in the accepted plan: the grammar/tree semantics bridge,
starting with the helper lemmas needed for `derives_iff_tree`. Keep that work in a
new PR, with unchanged accepted statements. Independent regular-realization or
abstract activation obligations can instead be selected by the owner.
