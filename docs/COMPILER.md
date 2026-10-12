# Computing a semilinear representation

`compileGrammar` takes a finite grammar and returns bases and periods whose
denotation is exactly its Parikh image. To supply a grammar as JSON instead,
use the [CLI](CLI.md).

Consider `S → ε | aS`, with both `S` and `a` labelled `0`:

```lean
import Parikh
open Parikh

def unaryGrammar : EncodedGrammar where
  terminalCount := 1
  extraNonterminalCount := 0
  initial := 0
  rules := [⟨0, []⟩, ⟨0, [.terminal 0, .nonterminal 0]⟩]

#eval (compileGrammar unaryGrammar).map fun c =>
  (List.ofFn c.base, c.periods.map (fun p => List.ofFn p))
```

This prints:

```text
[([0], []), ([1], [[1]]), ([2], [[2]]), ([3], [[1], [2]])]
```

The components overlap, and their union is all natural counts of `a`.
`List.ofFn` reads the coordinates of each vector for display.

An `EncodedGrammar` declares `terminalCount` terminals and
`extraNonterminalCount + 1` nonterminals. The latter ensures that a start symbol
exists. Labels use `Fin`; productions use Mathlib's rule and symbol types.
`g.decode` gives the corresponding `ContextFreeGrammar`.

## Correctness and bounds

The library proves these statements for every encoded grammar:

```lean
example (g : EncodedGrammar) :
    (compileGrammar g).denotation = parikhImage g.decode.language :=
  compileGrammar_correct g

example (g : EncodedGrammar) :
    WithinBounds g.size (compileGrammar g) :=
  compileGrammar_size_bounds g
```

Write `M = g.size.positions` and `K = g.size.trees`. `WithinBounds` gives at
most `K * 2^K` components and `K` periods per component. Base norms are at most
`(K+1)*M`, and period norms are at most `M`. `compileGrammar_bit_bound` bounds
the coordinate widths and total numerical entry bits.

## Construction

The compiler enumerates bounded derivation trees, selects simple base trees
and repeatable contexts, and tests which context families can be activated.
Each accepted family contributes a component: its base pays for the first
copy of every selected context, and further copies contribute its periods.

This enumeration can grow quickly. Start with small grammars. The compiler
preserves distinct contexts and produces an exact representation that may
contain redundant components or periods.
