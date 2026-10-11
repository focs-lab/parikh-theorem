# Contract and proof audits

Run `python3 scripts/check-contracts.py` after `lake build`. Lean imports the
compiled library and exports each project declaration's kernel expression type,
universe parameters, kind, definition value, reducibility and instance status.
This includes implicit binders, section variables, generated constructors and
supporting definitions. The JSON proposal stores SHA-256 fingerprints of the
structural expression representations, not theorem-line text. The full current
expressions and per-declaration axiom reports are in `.lake/contract-audit.json`.
Pins and the complete dependency manifest are also frozen by fingerprint.

The submitted proposal is `docs/contracts/proposed.json`. The owner accepted PR #2 on 2026-10-11; `baseline.json` records its reviewed
head `6bff9679d7ea03e5401815b80c5a3dc1300f9d36` as `accepted_commit`. The checker then reads the proposal directly
from that Git commit, independently of the working file. Existing entries must
match it. For new declarations, extend the current proposal manifest explicitly
and preserve all older entries; do not regenerate an accepted baseline. Review
the baseline pointer itself against the accepted PR. CI must fetch full Git
history so an accepted commit is available. The checker also preserves every
entry from the PR's base snapshot (CI supplies `CONTRACT_BASE_REF`; local default
is `origin/main`). Set this variable to the immediate parent for stacked PRs.
This freezes helpers added in later published increments as well as the initial
skeleton. Review changes to that reference and the checker itself.

Proof bodies may change. Non-proof definition bodies may not change, including
generated equations and recursors that support the contracts. Axioms and theorem
proof dependencies are audited separately. All remaining direct holes, project
axioms (even unused ones), and declarations transitively depending on unresolved
assumptions must match their named allowlists in `obligations.json`. Removing a
local hole does not mark a declaration complete while it still uses `sorryAx`.
No temporary project axioms exist in this skeleton. If one is introduced in an
authorized increment, its precise signature and dependent obligations require
visible ledger entries; replacing a hole by an axiom is not progress.

Lean generates eleven partial `._unsafe_rec` compiler helpers for ordinary
structural recursion. These are explicitly listed and fingerprinted; no logical
project declaration may reference them in its kernel type/body. They are not
unsafe proofs or project assumptions. The audit rejects other partial functions,
all unsafe declarations, unrecognized axioms, and source runtime overrides.
Standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) are
reported separately and permitted. `native_decide` is not allowed.

The skeleton adds no notation, macros or attribute changes; the checker rejects
such commands for separate review. Instance registrations and elaborated meanings
are checked. Source review remains necessary for any future elaboration machinery,
new imports, attributes, instances or notation; fingerprints are not a substitute
for reviewing a proposed mathematical contract. Audit-script and allowlist changes
themselves must be reviewed, and source comments must continue to describe the
accepted meanings accurately.

`python3 scripts/check-contracts.py --final` additionally rejects every direct
hole, project axiom and transitive unresolved dependency. It intentionally fails
on this intermediate skeleton. Final completion requires that check, not merely
a successful `lake build`.
