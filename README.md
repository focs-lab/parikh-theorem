# Parikh theorem

An independent, reusable Lean 4 library for Parikh's theorem.
**The forward Parikh theorem, exact finite semilinear witnesses, and converse
regular realization are proved.** For finite terminal alphabets, every semilinear
set is the exact Parikh image of a Mathlib DFA-regular language, and every Mathlib
grammar has a regular language with the same image. The derivation-tree proof supports
arbitrary ambient nonterminal types. Regular-language specialization, executable
construction with correctness proofs, and quantitative bounds remain in progress.
Witness and automaton existence are classical proofs.

Start with the [public statements](Parikh/Statements.lean),
[proof plan](docs/PROOF_PLAN.md), and [proof-status ledger](docs/PROOF_STATUS.md).
The [build instructions](docs/BUILD.md), [Mathlib reuse audit](docs/MATHLIB_REUSE.md),
and [contract checks](docs/CONTRACT_CHECKS.md) describe the pinned environment and
the incremental proof workflow. All 4 remaining theorem holes are explicitly tracked.

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
