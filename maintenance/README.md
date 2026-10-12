# Extending the library

The [proof map](proof-map.md) locates each part of the argument in the source.
The [public API](../docs/API.md) is the starting point for clients; supporting
tree and activation lemmas live in their respective modules.

Reuse Mathlib definitions and results wherever possible. Keep new helpers close
to the result that needs them, and submit changes as a reviewed PR.

Contributions to Mathlib or CSlib are welcome. The library uses
[Apache 2.0](../LICENSE), matching both projects. An upstream version can follow
the target library's naming and module conventions; the compatibility audit
below applies to this repository.

## Checks

After [installing the dependencies](../docs/BUILD.md), run:

```sh
lake build
python3 scripts/check-contracts.py --final
lake env lean tests/ProofExamples.lean
python3 tests/cli.py
```

CI runs the same checks. `tests/ProofExamples.lean` exercises the mathematical
interfaces and concrete compiler outputs. `tests/cli.py` checks JSON input,
diagnostics, and the supplied grammars, including their images in `[0, 12]^2`.

## Public API and declaration stability

The names in `Parikh/Api.lean` are thin aliases for the existing definitions
and proofs. Prefer these descriptive names in examples and documentation.
Existing names remain available for compatibility.

The audit preserves declaration names, elaborated types, universe parameters,
definition bodies, reducibility, and instance registrations. Proof bodies may
change. It also checks dependency pins and direct and transitive proof holes.

The files in [contracts/](contracts/) contain the accepted baseline pointer,
declaration fingerprints, and obligation lists. The baseline is the reviewed
PR #2 commit `6bff9679d7ea03e5401815b80c5a3dc1300f9d36`. The checker reads its
original manifest directly from that commit. Earlier base commits use the old
`docs/contracts/` path; current snapshots use `maintenance/contracts/`.

When adding declarations, append their fingerprints to `proposed.json` while
preserving every existing entry. The checker compares against both the accepted
baseline and the PR's base. Set `CONTRACT_BASE_REF` to a parent branch for a
stacked PR. The baseline pointer and earlier fingerprints stay fixed.

`scripts/ContractAudit.lean` exports full kernel expressions and axiom reports
to `.lake/contract-audit.json`. Standard Lean foundations are allowed:
`propext`, `Classical.choice`, and `Quot.sound`. The audit rejects project axioms,
proof holes, unsafe proofs, and runtime overrides. The runtime allowlist records
Lean's compiler-generated recursion helpers.
New notation, attributes, instances, or audit changes need explicit review.

## Mathlib reuse

| Mathlib infrastructure | Use in this library |
| --- | --- |
| `Language`, `ContextFreeGrammar`, grammar rewriting | Word and grammar semantics, including the tree/derivation bridge. |
| `List.count`, finite sums, `AddSubmonoid.closure` | Count vectors and linear-set denotation. |
| `IsLinearSet`, `IsSemilinearSet` | The public mathematical predicates and finite-union results. |
| `RegularExpression`, DFA/NFA determinization | Regular realization of semilinear sets. |
| Finite sets, products, powersets, `List.sections` | Bounded tree families and executable enumeration. |
| Natural strong induction and `Nat.clog` | Decomposition termination and numerical bit bounds. |
| Lean's `Json`, `Fin`, and list APIs | Validated CLI input and lossless coordinate conversion. |

The project adds production-labelled trees with explicit holes, occurrence-based
replacement, and activation accounting for the decomposition proof. The pinned
Mathlib grammar interface does not supply these structures. Regular realization
uses specialized word-block automata and Mathlib determinization.

