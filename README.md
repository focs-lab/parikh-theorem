# Parikh theorem

An independent, reusable Lean 4 library for Parikh's theorem.
**The statement skeleton is accepted. The counting/witness bridges, grammar/tree equivalence,
plugging/insertion, abstract activation laws, activation's tree realization, and the exact
linear-component equality are proved;
Parikh's theorem itself remains in progress.**

Start with the [public statements](Parikh/Statements.lean),
[proof plan](docs/PROOF_PLAN.md), and [proof-status ledger](docs/PROOF_STATUS.md).
The [build instructions](docs/BUILD.md), [Mathlib reuse audit](docs/MATHLIB_REUSE.md),
and [contract checks](docs/CONTRACT_CHECKS.md) describe the pinned environment and
the incremental proof workflow. All 17 remaining theorem holes are explicitly tracked.

## References and agent handoff

- [Mathematical proof (PDF)](reference/parikh_theorem.pdf)
- [Mathematical proof (LaTeX)](reference/parikh_theorem.tex)
- [Codex formalization prompt](docs/CODEX_FORMALIZATION_PROMPT.md)
- [Reference build instructions](reference/README.md)

Ask the Codex agent to read the formalization prompt. Its first deliverable is a
readable, compiling statement-skeleton PR for owner review. In Codex Cloud, use
the cloud-specific environment/authentication checks in the build instructions.
After acceptance, each increment fills in one part of the proof without changing
the accepted statements and is published as a separate, potentially stacked PR.

The library targets the full context-free theorem, finite semilinear witnesses, the converse regular realization, effective construction, and quantitative bounds. It does not depend on the trace-membership project.
