# Running the certified compiler

Import `Parikh` and call `Parikh.compiler.compile` on an `EncodedGrammar`.
The result is a finite `Witness`: a list of components, each with a base vector
and an indexed list of periods. Terminal and nonterminal labels use `Fin`.
`extraNonterminalCount + 1` is the declared nonterminal count, ensuring that the
start symbol exists. Rules are lists of Mathlib symbols; unused declared symbols
and duplicate productions are allowed.

For the grammar `S → epsilon | aS`, with `S` and `a` both labelled `0`:

```lean
import Parikh
open Parikh

def unaryGrammar : EncodedGrammar :=
  ⟨1, 0, 0, [⟨0, []⟩, ⟨0, [.terminal 0, .nonterminal 0]⟩]⟩

#eval (compiler.compile unaryGrammar).map fun c =>
  (List.ofFn c.base, c.periods.map (fun p => List.ofFn p))
```

This prints:

```text
[([0], []), ([1], [[1]]), ([2], [[2]]), ([3], [[1], [2]])]
```

A vector is a finite-domain function; `List.ofFn` reads its coordinates for
display. The output includes overlapping components. Together they denote all
natural counts of `a`, including zero. The construction guarantees exactness
and coarse bounds, without minimizing the representation.

## Correctness and budgets

The public implementing value is
[`compiler`](../Parikh/ExecutableCompiler.lean). Its fields certify the function
that was executed above:

```lean
example (g : EncodedGrammar) :
    (compiler.compile g).denotation = image g.decode.language :=
  compiler.correct g

example (g : EncodedGrammar) :
    WithinBounds g.size (compiler.compile g) :=
  compiler.bounded g
```

`WithinBounds` states at most `K * 2^K` components, `K` indexed periods per
component, base norm at most `(K+1)*M`, and period norm at most `M`.
`EncodedGrammar.compile_bit_bound` proves every coordinate fits the fixed width
and the numerical entries satisfy `g.size.vectorBits`, excluding list-length
metadata. These are kernel-checked theorems for every encoded grammar, rather
than conclusions inferred from the displayed example.

## How it computes

1. Use `boundedEnumeration` through the declared nonterminal count plus one.
2. Filter simple complete start trees and nontrivial bounded same-root/hole
   contexts. Cycle height uses the computed active alphabet, exactly matching
   the general grammar formula.
3. Remove repeated trees using certified structural equality. Different trees
   remain different contexts even if their weights are equal or zero.
4. List every context sublist for each base and run the proved activation test
   on finite production-label supports.
5. For each accepted pair, pay for one copy of each context in the base and
   retain each context's weight as its own period position.

The runtime definitions are computable and use no classical finite-set listing
or selection. Their proofs use standard Lean foundations; the axiom audit
reports `propext`, `Classical.choice` and `Quot.sound`, including dependencies
inherited through certified equality and proof fields. No project axiom or
`sorryAx` is used. Explicit height recursion adds no new partial runtime helper.

The bounds are deliberately coarse. Enumeration and the context powerset can
be very large; this implementation is intended as a certified finite
construction, with no claim of practical efficiency on large grammars.

## Validation

Run the ordinary build, final audit and example script described in
[BUILD.md](BUILD.md). The example script checks general compiler fields and
runtime assertions for empty productions, empty languages/alphabets, distinct
silent contexts, duplicate productions, unreachable cycles and unary recursion.
Failures in a runtime assertion fail the example check. The frozen contracts
and pins remain unchanged; the [proof ledger](PROOF_STATUS.md) records review
and final-head CI evidence.
