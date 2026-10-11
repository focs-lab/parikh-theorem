# Build and audit

The pins are Lean `leanprover/lean4:v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Use the committed manifest;
do not run `lake update` just to build or opportunistically upgrade dependencies.
No external service, trace-membership checkout or project secret is needed.

## Standard elan environment

Install elan from the official Lean repository if it is absent:

```sh
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/v4.2.4/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none --no-modify-path
export PATH="$HOME/.elan/bin:$PATH"
```

From the checkout root:

```sh
elan toolchain install "$(cat lean-toolchain)"
lean --version
lake --version
lake exe cache get Mathlib.Algebra.Group.Submonoid.Finsupp Mathlib.Computability.ContextFreeGrammar Mathlib.Computability.RegularExpressions Mathlib.Computability.DFA Mathlib.Computability.NFA Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs Mathlib.Data.Nat.Log Mathlib.Data.Set.Finite.List
LEAN_NUM_THREADS=4 lake build
python3 scripts/check-contracts.py
lake env lean scripts/SkeletonExamples.lean
```

Lake fetches missing dependency checkouts from the exact manifest revisions.
Four threads were appropriate for the onboarding cloud instance's four-CPU quota.
Use the cache rather than rebuilding all of Mathlib. Intermediate `sorry` warnings
are expected; the declaration allowlists are checked and unlisted assumptions
fail the audit. Use `python3 scripts/check-contracts.py --final` for completion;
it must fail on this skeleton.

## This Codex Cloud instance

Activate the retained tools before the same build/audit commands:

```sh
source /workspace/lean-setup/activate.sh
cd /workspace/parikh-theorem
```

The activation script sets elan's location, executable path and a writable cache
directory. The installed toolchain was taken from the official GitHub Lean
release archive and linked through elan. The existing Mathlib package cache was
reused locally; a fresh checkout need not have that shared cache. CI uses elan
and the manifest without the cloud-specific symlink.

Cloud tasks are already isolated; use the existing checkout. Do not create a
worktree unless the owner asks. Preserve existing edits before changing branches.
GitHub authentication may be supplied by the cloud HTTPS proxy rather than a
normal `gh` login. Check Git access separately from API access:

```sh
git ls-remote origin HEAD
git push --dry-run origin HEAD:refs/heads/codex/your-branch
gh api repos/focs-lab/parikh-theorem --jq '{default_branch,permissions}'
gh pr list --repo focs-lab/parikh-theorem
```

Inspect credential presence only, never print tokens. A `gh auth status` failure
does not establish that the proxy's repository access is missing. This task
verified read, dry-run push and API access on the actual cloud instance. Required
hosts include GitHub's Git/release endpoints, `api.github.com`, Lean's
`release.lean-lang.org`, and Mathlib's `cache.mathlib.org` /
`lakecache.blob.core.windows.net`. Review cloud network settings for a proxy
denial rather than requesting a new token merely because the CLI reports an
invalid placeholder.

The repository currently has no license metadata. This milestone does not choose
a release license on the owner's behalf.
