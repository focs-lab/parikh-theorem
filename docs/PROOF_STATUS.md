# Proof status: statement skeleton, awaiting owner review

Review: [PR #2](https://github.com/focs-lab/parikh-theorem/pull/2), branch
`codex/readable-statement-skeleton`, based on `main` after merged handoff PR #1.

The library builds with **28 named direct `sorry` obligations**, no project axioms,
and 28 declarations transitively dependent on `sorryAx`. No main mathematical
proof has been implemented. Foundational data definitions are concrete. The
proposed contracts are not yet owner-accepted; `contracts/baseline.json` records
that explicitly. Do not start proof work in this run.

## Named theorem obligations

All names below have namespace `Parikh`. Every entry is directly and transitively
incomplete; intended prerequisites are in `PROOF_PLAN.md`. The machine-readable
allowlists in `contracts/obligations.json` are authoritative for CI and must agree
with this ledger.

| Module | Outstanding declarations |
| --- | --- |
| Counting | `counts_append`, `component_isLinearSet`, `witness_isSemilinearSet`, `exists_witness` |
| GrammarTrees | `derives_iff_tree`, `complete_support_active`, `bounded_open_finite` |
| Decomposition | `plugging`, `insertion_enabled`, `insertion_accounting`, `simple_height`, `bounded_cut`, `decomposition` |
| Activation | `first_occurrences`, `positive_multiplicities`, `one_linear` |
| RegularRealization | `representative_counts`, `witnessExpression_correct`, `converse`, `regular_image` |
| Construction | `bounded_family_bounds`, `bounded_witness`, `witness_bit_bound` |
| Statements | `treeRepresentation_eq`, `grammar_image`, `grammar_witness`, `contextFree_image`, `regular_realization` |

## Implementation obligations without hidden assumptions

`ActivationTest`, `BoundedEnumeration`, and `Compiler` are concrete structures
specifying future finite algorithms. There are no values implementing them yet.
Their correctness fields are requirements of any such value, not assumed
theorems or typeclass instances. In particular, no compiler or enumerator is
defined through `Classical.choose`, and existence of a semilinear witness is not
reported as effectivity. The first-occurrence order, syntax enumeration,
finite support decisions and explicit alphabet order must supply the eventual
executable implementation. Runtime execution checks belong to that later PR.

## Validation of this milestone

- Lean 4.34.1 and Lake 5.0.0 verified in Codex Cloud, using the elan installation
  prepared during onboarding. No assumptions about the owner's server are used.
- Mathlib v4.34.1 and eight transitive dependencies are pinned by exact revisions
  in the committed Lake manifest. Git dependency reads and selected Mathlib cache
  download/decompression succeeded. The additional selected imports fetched 686
  cache artifacts; `Nat.Log` also built successfully locally.
- `lake build` succeeds (1309 jobs, including cached dependencies). The expected
  `sorry` warnings are intentional and explicitly allowlisted.
- `python3 scripts/check-contracts.py` audits 334 project declarations, including
  generated declarations and definition meanings, and reports the 28 unresolved
  theorem dependencies. It distinguishes standard Lean foundational axioms.
- `lake env lean scripts/SkeletonExamples.lean` checks activation order, rejection
  of an unenabled operation, zero-arity production statistics, hole support,
  empty witness denotation and empty regular realization. These small checks do
  not discharge the theorem obligations.
- Negative checks rejected an added implicit theorem binder and a changed counting
  definition. Both probes were restored; `--final` rejected the remaining holes
  as intended.
- Basic CI performs dependency/cache retrieval, library build, contract audit and
  examples. CI's remote result is reported in the PR; a local build alone does
  not establish remote CI success.

The accepted baseline remains pending. After owner acceptance and a request to
continue, record the accepted skeleton SHA and begin with the counting/witness
bridges, as one coherent proof milestone in a new PR. Audit both local holes and
transitive assumptions before marking any declaration complete. Every increment
is published separately; no self-merge or license/release decision is included.
