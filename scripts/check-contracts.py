#!/usr/bin/env python3
"""Compare elaborated contracts and audit holes; never silently refresh a baseline."""
import argparse
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def fail(message):
    raise SystemExit(message)


def run(*args):
    subprocess.run(args, cwd=ROOT, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--propose", action="store_true", help="write the initial proposal once")
    parser.add_argument("--final", action="store_true", help="reject all holes and project axioms")
    args = parser.parse_args()
    run("lake", "env", "lean", "scripts/ContractAudit.lean")
    rows = json.loads((ROOT / ".lake/contract-audit.json").read_text())
    if not rows:
        fail("Audit imported zero project declarations")
    current = {}
    for row in rows:
        contract = dict(row["contract"])
        for field in ("type", "value"):
            if contract[field] is not None:
                contract[field] = hashlib.sha256(contract[field].encode()).hexdigest()
        current[row["name"]] = contract
    pins = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
            for p in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")}
    snapshot = {"pins": pins, "declarations": current}
    proposed = ROOT / "docs/contracts/proposed.json"
    if args.propose:
        if proposed.exists():
            fail("Proposal already exists; baseline regeneration is forbidden")
        proposed.write_text(json.dumps(snapshot, indent=2, sort_keys=True) + "\n")
    config = json.loads((ROOT / "docs/contracts/baseline.json").read_text())
    accepted = config["accepted_commit"]
    if accepted:
        # Load the immutable proposal FROM the owner-accepted commit, not a mutable local file.
        baseline = json.loads(subprocess.check_output(
            ["git", "show", f"{accepted}:docs/contracts/proposed.json"], cwd=ROOT))
    else:
        baseline = json.loads(proposed.read_text())
        print("Owner-accepted baseline pending; checking the submitted proposal")
    # Preserve helper contracts introduced by earlier published increments, too.
    base_ref = os.environ.get("CONTRACT_BASE_REF") or "origin/main"
    prior = subprocess.run(["git", "show", f"{base_ref}:docs/contracts/proposed.json"],
                           cwd=ROOT, capture_output=True, text=True)
    baselines = [baseline]
    if prior.returncode == 0:
        baselines.append(json.loads(prior.stdout))
    if pins != baseline["pins"]:
        fail("Lean/Lake/dependency pins differ from the contract baseline")
    for frozen in baselines:
        for name, old in frozen["declarations"].items():
            if current.get(name) != old:
                fail(f"Frozen signature, definition meaning, instance, or declaration changed: {name}")
    # Once accepted, extensions must preserve all old entries and explicitly list additions.
    if snapshot != json.loads(proposed.read_text()):
        fail("New declarations need an explicit append-only proposal-manifest extension")
    obligations = json.loads((ROOT / "docs/contracts/obligations.json").read_text())
    direct = {r["name"] for r in rows if r["directSorry"]}
    axioms = {r["name"] for r in rows if r["contract"]["kind"] == "axiom"}
    if direct != set(obligations["sorry"]):
        fail(f"Direct hole allowlist mismatch: added={sorted(direct-set(obligations['sorry']))}, "
             f"removed={sorted(set(obligations['sorry'])-direct)}")
    if axioms != set(obligations["temporary_axioms"]):
        fail("Project axiom allowlist mismatch (including unused axioms)")
    runtime_helpers = {r["name"] for r in rows if r["contract"]["partial"]}
    if runtime_helpers != set(obligations["compiler_generated_partial"]):
        fail("Compiler-generated partial helper allowlist mismatch")
    if any(not n.endswith("._unsafe_rec") for n in runtime_helpers):
        fail("Only Lean's generated runtime recursion helpers may be partial")
    for row in rows:
        if row["contract"]["unsafe"]:
            fail(f"Unsafe project declaration: {row['name']}")
        if row["name"] not in runtime_helpers and set(row["dependencies"]) & runtime_helpers:
            fail(f"Logical declaration references partial runtime code: {row['name']}")
        unknown = set(row["axioms"]) - STANDARD - {"sorryAx"} - axioms
        if unknown:
            fail(f"Unrecognized proof dependencies in {row['name']}: {sorted(unknown)}")
    # Attribute/notation commands can change elaboration outside ordinary declarations.
    # The skeleton introduces none; any future addition needs an explicit owner-reviewed audit.
    for path in [ROOT / "Parikh.lean", *sorted((ROOT / "Parikh").rglob("*.lean"))]:
        text = path.read_text()
        if re.search(r"\b(?:native_decide|implemented_by|extern)\b|^\s*(?:unsafe|partial)\b", text, re.MULTILINE):
            fail(f"Unreviewed runtime or unsafe proof extension: {path.relative_to(ROOT)}")
        if re.search(r"^\s*(?:local\s+|scoped\s+)?(?:notation|infix[lr]?|prefix|postfix|macro|syntax|attribute)\b",
                     text, re.MULTILINE):
            fail(f"Notation/attribute extension requires contract review: {path.relative_to(ROOT)}")
    transitive = {r["name"] for r in rows if "sorryAx" in r["axioms"] or set(r["axioms"]) & axioms}
    if transitive != set(obligations["dependent_on_unresolved"]):
        fail("Transitive unresolved-dependency allowlist mismatch")
    if args.final and (direct or axioms or transitive):
        fail("Final audit rejects direct/transitive holes and all project axioms")
    print(f"Audited {len(rows)} declarations: {len(direct)} direct holes, "
          f"{len(axioms)} project axioms, {len(transitive)} declarations depend on unresolved assumptions")
    print("Foundational dependencies allowed: propext, Classical.choice, Quot.sound")


if __name__ == "__main__":
    main()
