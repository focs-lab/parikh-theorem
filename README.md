# Parikh theorem

An independent, reusable Lean 4 library for Parikh's theorem is planned here.
**No Lean formalization has been implemented yet.**

## References and agent handoff

- [Mathematical proof (PDF)](reference/parikh_theorem.pdf)
- [Mathematical proof (LaTeX)](reference/parikh_theorem.tex)
- [Codex formalization prompt](docs/CODEX_FORMALIZATION_PROMPT.md)
- [Reference build instructions](reference/README.md)

On the server, give the Codex agent the contents of the formalization prompt, or ask it to read and carry out that file. Its first deliverable is a readable, compiling statement-skeleton PR for owner review. After acceptance, each increment fills in one part of the proof without changing the accepted statements and is published as a separate, potentially stacked PR.

The library targets the full context-free theorem, finite semilinear witnesses, the converse regular realization, effective construction, and quantitative bounds. It does not depend on the trace-membership project.
