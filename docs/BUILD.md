# Installation

The library uses Lean **4.34.1** and the Mathlib revision in `lake-manifest.json`.

## Build a checkout

Install [elan](https://github.com/leanprover/elan) if you do not already have it:

```sh
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/v4.2.4/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none --no-modify-path
export PATH="$HOME/.elan/bin:$PATH"
```

Clone the repository and fetch the cached Mathlib dependencies:

```sh
git clone https://github.com/focs-lab/parikh-theorem.git
cd parikh-theorem
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get \
  Mathlib.Algebra.Group.Submonoid.Finsupp \
  Mathlib.Computability.ContextFreeGrammar \
  Mathlib.Computability.RegularExpressions \
  Mathlib.Computability.DFA Mathlib.Computability.NFA \
  Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs \
  Mathlib.Data.Nat.Log Mathlib.Data.Set.Finite.List Mathlib.Data.List.Sections
lake build
```

Lake reads the pinned dependency revisions from the manifest. The cache supplies
compiled Mathlib files, so the build only needs to compile the library itself.

Try the [command-line compiler](CLI.md):

```sh
./bin/parikh examples/cli/balanced.json
```

## Use in another Lean project

Use the same Lean version and add this dependency to your `lakefile.toml`:

```toml
[[require]]
name = "parikh"
git = "https://github.com/focs-lab/parikh-theorem.git"
rev = "main"
```

Then run `lake update` and import `Parikh`. To pin a particular version, replace
`main` with a commit or release tag. The [Lean API](API.md) shows how to apply
the theorems and compute a representation.

Contributor checks are described in [maintenance/](../maintenance/README.md).
