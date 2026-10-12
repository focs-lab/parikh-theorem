# Lean API

```lean
import Parikh
open Parikh
```

All public names below are in the `Parikh` namespace. Languages and grammars use
Mathlib's `Language` and `ContextFreeGrammar` types.

## Count vectors and representations

`CountVector T` is the function type `T → ℕ`. For a word `w`, `parikhVector w a`
counts occurrences of the letter `a`. For a language `L`, `parikhImage L` is the
set of vectors of its words. Concatenation adds vectors:

```lean
example {T : Type*} [DecidableEq T] (u v : List T) :
    parikhVector (u ++ v) = parikhVector u + parikhVector v :=
  parikhVector_append u v
```

A `LinearComponent T` has a `base : CountVector T` and
`periods : List (CountVector T)`. Its `denotation` consists of the base plus
arbitrary natural multiples of the periods. A `SemilinearRepresentation T`
is a list of components, with `denotation` given by their union.
An empty representation denotes the empty set; a component with no periods
denotes just its base.

`LinearComponent.isLinearSet` and `SemilinearRepresentation.isSemilinearSet`
connect these concrete descriptions to Mathlib's predicates.

## Main theorems

| Theorem | Result |
| --- | --- |
| `parikhImage_isSemilinear_of_isContextFree` | A context-free language has a semilinear Parikh image. |
| `parikhImage_isSemilinear_of_grammar` | The same result for a concrete grammar. |
| `exists_semilinearRepresentation_of_grammar` | A finite representation whose denotation equals the grammar's image. |
| `exists_regularLanguage_with_parikhImage` | Every semilinear set is the Parikh image of a regular language. |
| `exists_regularLanguage_with_grammar_parikhImage` | Every grammar has a regular language with the same Parikh image. |
| `parikhImage_isSemilinear_of_isRegular` | A regular language has a semilinear Parikh image. |

These theorems assume `[Finite T] [DecidableEq T]` for the terminal alphabet.
Grammar results allow an arbitrary nonterminal type. For example:

```lean
example {T : Type*} [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : SemilinearRepresentation T, W.denotation = parikhImage g.language :=
  exists_semilinearRepresentation_of_grammar g
```

For bounds on an existential representation, use
`exists_boundedSemilinearRepresentation_of_grammar`, which assumes `[Fintype T]`.
For a computation, use the finite encoding below.

## Computing a representation

An `EncodedGrammar` uses numeric terminal and nonterminal labels. Given one,
`compileGrammar g` returns a `SemilinearRepresentation (Fin g.terminalCount)`.

```lean
example (g : EncodedGrammar) :
    (compileGrammar g).denotation = parikhImage g.decode.language :=
  compileGrammar_correct g
```

`compileGrammar_size_bounds` proves the bounds on components, periods, and
vector norms. `compileGrammar_bit_bound` proves the numerical encoding bound.
The [compiler guide](COMPILER.md) gives a complete runnable example.

The interface is defined in [Api.lean](../Parikh/Api.lean). Earlier names such
as `counts`, `image`, and `grammar_image` remain available for compatibility.
