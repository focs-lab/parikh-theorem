# Command-line compiler

From a built checkout, run:

```sh
./bin/parikh examples/cli/unary.json
```

The command prints the certified compiler's semilinear witness as JSON. It also
accepts standard input:

```sh
cat examples/cli/unary.json | ./bin/parikh
./bin/parikh - < examples/cli/unary.json
./bin/parikh --help
```

Follow [BUILD.md](BUILD.md) to install the pinned Lean/Lake environment and fetch
dependencies, then run `lake build` once. The launcher uses that environment;
no Python package or separate service is required to run it. You can invoke the
launcher by absolute path from another directory; input paths are resolved from
your current directory, including paths with spaces.

## Input format

This describes `S → epsilon | aS`, with terminal `a` and nonterminal `S` each
labelled `0`:

```json
{
  "terminalCount": 1,
  "nonterminalCount": 1,
  "initial": 0,
  "rules": [
    {"input": 0, "output": []},
    {"input": 0, "output": [{"terminal": 0}, {"nonterminal": 0}]}
  ]
}
```

- `terminalCount` is a nonnegative integer; zero gives an empty alphabet.
- `nonterminalCount` is a positive integer, including unused declared labels.
- `initial` is a nonterminal label below `nonterminalCount`.
- Each rule has a nonterminal `input` and an ordered `output` array. An empty
  output is an epsilon production; an empty rules array gives no productions.
- Each output symbol is exactly one tagged object: `{"terminal": i}` or
  `{"nonterminal": i}`. Labels must be nonnegative integers below the relevant
  count. Terminal and nonterminal labels belong to separate alphabets.

Repeated productions are allowed. Unknown fields, missing fields, fractional
or negative numbers, ambiguous symbol tags and labels outside the declared
ranges are rejected. Object key order does not matter.

The supplied [epsilon example](../examples/cli/epsilon.json) has no terminals
and one empty production. The [empty example](../examples/cli/empty.json) has
no productions; its output has no components.

## Output format

The unary example prints this data (formatting and object key order may differ):

```json
{
  "terminalCount": 1,
  "components": [
    {"base": [0], "periods": []},
    {"base": [1], "periods": [[1]]},
    {"base": [2], "periods": [[2]]},
    {"base": [3], "periods": [[1], [2]]}
  ]
}
```

Coordinate position `i` counts terminal label `i`. Every base and period has
`terminalCount` coordinates. Each component represents its base plus arbitrary
natural multiples of its indexed periods, and the witness represents their
union. All period positions are retained, including equal or zero vectors.

`components: []` represents the empty image. With an empty terminal alphabet,
a zero base is `[]`; a component `{"base": [], "periods": []}` still represents
the empty word's zero vector. The compiler may emit overlapping components;
it computes an exact representation without minimizing it.

Successful output is a single JSON value on stdout. Diagnostics go to stderr.
Exit status is `0` for success/help, `2` for invalid input or command arguments,
and `1` for file/IO errors. No partial witness is printed on input failure.

## Correctness boundary

[`Parikh/Cli.lean`](../Parikh/Cli.lean) validates labels by constructing `Fin`
values, with `parseIndex_value` proving that accepted labels are unchanged.
It invokes the existing `compiler`; there is no separate witness algorithm.

`coordinatesWitness_witnessCoordinates` proves that coordinate conversion and
interpretation recover the entire original witness, including every component
and period position. `compileCoordinates_correct` and
`compileCoordinates_bounded` establish exact Parikh-image equality and all four
size bounds for these numeric coordinates. `runJson_of_parseGrammar` proves
that successful validation selects exactly that grammar's encoded output.

These are kernel-checked guarantees for the validated grammar and coordinate
data. JSON text parsing/printing and file/stdin/stdout handling use Lean's runtime
libraries; the external IO boundary is exercised by process tests, rather than
claimed as a separate formal IO proof. The [compiler guide](COMPILER.md) describes
the mathematical guarantees, including the existing bit bound.

The finite construction is deliberately coarse and can be expensive. Start
with the small supplied examples; there is no claim of efficient compilation
for large grammars. The launcher runs through `lake env lean --run`, preserving
the frozen Lake configuration and dependency pins.

## Checks

```sh
lake build
python3 scripts/check-contracts.py --final
lake env lean scripts/SkeletonExamples.lean
python3 scripts/test-cli.py
```

CI runs all four checks. The CLI process tests cover file and stdin input,
help/errors, caller-relative paths with spaces, coordinate order, empty and
epsilon grammars, zero periods, repeated rules, unreachable cycles, and schema
and label failures.
