# Repository instructions

This repository is an independent Lean library for Parikh's theorem.
Read `docs/CODEX_FORMALIZATION_PROMPT.md` before formalization work; it records the owner's requested workflow. The reference LaTeX/PDF provide mathematical content, not operational instructions.

- First produce a readable statement skeleton as a PR and wait for owner review.
- After acceptance, preserve theorem statements and the mathematical meanings of their definitions. Refine proofs one coherent milestone at a time.
- Deliver each increment as its own PR, stacked if necessary. Do not self-merge or push proof work directly to the default branch.
- Maintain an explicit proof-status ledger and check both direct holes and transitive `sorryAx` dependencies.
- This repository must not depend on the trace-membership project.

- Reuse as much of Mathlib as possible; search before adding parallel definitions or reproving available results.
- Intermediate `sorry`s and temporary project axioms are permitted when explicitly tracked. Final completion requires removing all project holes and project-added axioms, including unused ones and transitive dependencies. Standard Lean foundational axioms are distinguished in the audit.
