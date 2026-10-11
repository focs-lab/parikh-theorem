# Mathematical reference

- [LaTeX source](parikh_theorem.tex): the owner's supplied proof, preserved byte-for-byte.
- [PDF](parikh_theorem.pdf): compiled from that source using pdfTeX (TeX Live 2021).

Run `./scripts/build-reference.sh` from the repository checkout to regenerate the PDF with `latexmk` and a TeX distribution containing the packages used by the source. Build intermediates are kept outside the repository. The script disables shell escape and ignores local latexmk configuration.

The source is a mathematical blueprint, not a machine-checked proof. Agent workflow instructions live in `AGENTS.md` and `docs/CODEX_FORMALIZATION_PROMPT.md`.

The original title-page/page-number reset produces a duplicate `page.1` PDF destination warning. The source is preserved rather than edited for this cosmetic navigation issue. Cross-references resolve after the repeated compilation passes.
