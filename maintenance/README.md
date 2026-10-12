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

## Compatibility

The public names in `Parikh/Api.lean` reuse the existing definitions and proofs.
Prefer them in examples and documentation; existing names remain available for
compatibility.

The contract check compares definitions and theorem types against recorded
versions to catch accidental interface changes. It also checks proof dependencies
and rejects placeholders or project-specific axioms. The audit data lives in
[contracts/](contracts/), and full reports are written to `.lake/contract-audit.json`.

When adding declarations, append their fingerprints to `proposed.json` while
preserving existing entries and the baseline pointer. The checker compares
against both the baseline and the PR's base. Set `CONTRACT_BASE_REF` to the
parent branch for a stacked PR.

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
