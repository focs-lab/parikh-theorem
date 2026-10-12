# Command-line compiler

After [building the library](BUILD.md), run:

```sh
./bin/parikh examples/cli/balanced.json
```

The command reads a grammar and prints a semilinear representation as JSON.
It also accepts standard input:

```sh
./bin/parikh < examples/cli/balanced.json
./bin/parikh - < examples/cli/balanced.json
./bin/parikh --help
```

Input paths are relative to your current directory. The launcher can be invoked
by absolute path from another directory.

## Input

This grammar is `S → ε | aSb`, with terminal labels `0 = a`, `1 = b`, and
nonterminal `0 = S`:

```json
{
  "terminalCount": 2,
  "nonterminalCount": 1,
  "initial": 0,
  "rules": [
    {"input": 0, "output": []},
    {"input": 0, "output": [{"terminal": 0}, {"nonterminal": 0}, {"terminal": 1}]}
  ]
}
```

Counts and labels are nonnegative integers. `nonterminalCount` is positive,
and `initial` is a nonterminal label. Labels range from zero to the relevant
count minus one. Every output symbol has exactly one tag, `terminal` or
`nonterminal`.

An empty rule output is an epsilon production. An empty `rules` array gives
no productions. Duplicate rules and unused labels are allowed; missing or
unknown fields and out-of-range labels are errors.

## Output

The balanced example produces:

```json
{
  "terminalCount": 2,
  "components": [
    {"base": [0, 0], "periods": []},
    {"base": [1, 1], "periods": [[1, 1]]},
    {"base": [2, 2], "periods": [[2, 2]]},
    {"base": [3, 3], "periods": [[1, 1], [2, 2]]}
  ]
}
```

Coordinate `i` counts terminal label `i`. A component represents its base plus
arbitrary natural multiples of its periods; the output represents their union.
Here that union is `{(n, n) | n ≥ 0}`. Components may overlap, and equal or zero
periods may occupy separate positions.

`components: []` represents the empty image. For an empty alphabet, the zero
vector is `[]`, and `{"base": [], "periods": []}` represents that vector.

Results go to stdout and errors to stderr. Exit codes are `0` for success or
help, `2` for invalid input or arguments, and `1` for file errors.

## Examples

In the two-terminal examples, `0 = a` and `1 = b`. All parameters below are
nonnegative integers.

| File | Grammar | Parikh image |
| --- | --- | --- |
| [unary.json](../examples/cli/unary.json) | `S → ε \| aS` | `{n}` |
| [balanced.json](../examples/cli/balanced.json) | `S → ε \| aSb` | `{(n, n)}` |
| [even-palindromes.json](../examples/cli/even-palindromes.json) | `S → ε \| aSa \| bSb` | `{(2i, 2j)}` |
| [offset-rays.json](../examples/cli/offset-rays.json) | `S → a \| b \| aaSbb` | `{(2n+1, 2n)} ∪ {(2n, 2n+1)}` |
| [epsilon.json](../examples/cli/epsilon.json) | `S → ε`, no terminals | The zero vector `[]` |
| [empty.json](../examples/cli/empty.json) | No productions | The empty set |

The palindrome example illustrates what the image forgets: `abba` is a
generated palindrome and `aabb` is not, but both have counts `(2, 2)`.
The offset example needs a union of two linear sets. A single linear set
containing both `(1, 0)` and `(0, 1)` would have to have base `(0, 0)`,
which is absent from this image.

The compiler enumerates bounded trees and context subsets, so start with small
grammars. [Compiler usage](COMPILER.md) describes the construction and its
correctness theorems. Lean checks the compiler and coordinate conversions;
JSON and file handling use Lean's standard runtime libraries.
