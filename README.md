# Parikh's theorem in Lean

Parikh's theorem says that, over a finite alphabet, the letter counts of a
context-free language form a semilinear set: a finite union of sets obtained by
adding natural multiples of fixed period vectors to a base vector.
For example, the language `{a^n b^n | n ≥ 0}` has count vectors `{(n, n) | n ≥ 0}`,
with base `(0, 0)` and period `(1, 1)`.

This Lean 4 library proves the theorem using Mathlib's languages, grammars, and
semilinear sets. It also proves that every semilinear set is the Parikh image of
a regular language, and provides a compiler that computes a finite semilinear
representation from a grammar, with correctness and size bounds proved in Lean.

## Try the compiler

Follow the [build instructions](docs/BUILD.md) to install Lean and fetch Mathlib.
Then run:

```sh
lake build
./bin/parikh examples/cli/balanced.json
```

The command reads a grammar and prints its bases and periods as JSON.
The [CLI guide](docs/CLI.md) explains the format and includes six examples,
from an empty language to palindromes and a union of two linear sets.

## Use it in Lean

```lean
import Parikh

example {T : Type*} [Finite T] [DecidableEq T]
    (L : Language T) (hL : L.IsContextFree) :
    IsSemilinearSet (Parikh.parikhImage L) :=
  Parikh.parikhImage_isSemilinear_of_isContextFree L hL
```

`parikhVector` counts letters in a word; `parikhImage` collects the count vectors
of a language. `LinearComponent` stores one base and a list of periods, and
`SemilinearRepresentation` stores a finite list of components.

Use `compileGrammar` to compute a representation from an `EncodedGrammar`.
`compileGrammar_correct` proves that its denotation equals the grammar's Parikh
image. See the [Lean API](docs/API.md) for the main definitions and theorems, or
the [compiler example](docs/COMPILER.md) to run it from Lean.

## Read the proof

The proof decomposes derivation trees into bounded base trees and repeatable
contexts. The bases and contexts give the bases and periods of the semilinear
representation. The [proof guide](docs/PROOF_GUIDE.md) develops this argument
through a running grammar; the [reference](reference/parikh_theorem.pdf) gives
the full mathematical exposition.

To extend the library, start with the [contributor guide](maintenance/README.md).
It contains the source map, Mathlib reuse notes, and commands for checking
declaration stability and proof dependencies.
Contributions that bring these results into Mathlib or CSlib are welcome.

## References

- R. J. Parikh, *On Context-Free Languages*, JACM 13(4), 1966.
  [DOI](https://doi.org/10.1145/321356.321364).
- R. Sin'ya, *Simple proof of Parikh's theorem à la Takahashi*, 2019.
  [arXiv](https://arxiv.org/abs/1909.09393).
- A. Rubtsov, *The Simplest Proof of Parikh's Theorem via Derivation Trees*, 2022.
  [arXiv](https://arxiv.org/abs/2301.00047).

The formalization follows the derivation-tree approach of the latter two papers.
