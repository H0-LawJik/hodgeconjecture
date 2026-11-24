#!/usr/bin/env python3
"""Project checker: build, scan for sorry, verify axioms, validate the ledger.

Run from the repo root:  python3 tools/check.py [--no-build]

Exit 0 means every check passed. Output lines start with ACCEPTED or REJECTED so
CI logs and humans read them the same way. Standard library only.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "HodgeConjecture"
LEDGER = ROOT / "ledger" / "ladder.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STATUSES = {"checked", "stated", "open", "refuted", "dead"}
KINDS = {"foundation", "interface", "statement", "case", "reduction", "front"}

failures: list[str] = []


def reject(msg: str) -> None:
    failures.append(msg)
    print(f"REJECTED ({msg})")


def accept(msg: str) -> None:
    print(f"ACCEPTED ({msg})")


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True, **kw)


def check_build() -> bool:
    r = run(["lake", "build"])
    if r.returncode != 0:
        reject("build")
        sys.stdout.write(r.stdout[-4000:])
        sys.stderr.write(r.stderr[-4000:])
        return False
    accept("build")
    return True


def check_no_sorry() -> None:
    pat = re.compile(r"\bsorry\b")
    hits = []
    for f in sorted(LIB.rglob("*.lean")) + [ROOT / "HodgeConjecture.lean"]:
        for n, line in enumerate(f.read_text().splitlines(), 1):
            code = line.split("--", 1)[0]
            if pat.search(code):
                hits.append(f"{f.relative_to(ROOT)}:{n}")
    if hits:
        reject("sorry: " + ", ".join(hits))
    else:
        accept("no sorry")


def load_ledger() -> dict | None:
    try:
        data = json.loads(LEDGER.read_text())
    except (OSError, json.JSONDecodeError) as e:
        reject(f"ledger unreadable: {e}")
        return None
    ids = set()
    for r in data.get("rungs", []):
        rid = r.get("id")
        if not rid or rid in ids:
            reject(f"ledger: missing or duplicate rung id {rid!r}")
        ids.add(rid)
        if r.get("kind") not in KINDS:
            reject(f"ledger: rung {rid} has kind {r.get('kind')!r}; allowed {sorted(KINDS)}")
        if r.get("status") not in STATUSES:
            reject(f"ledger: rung {rid} has status {r.get('status')!r}; allowed {sorted(STATUSES)}")
        if r.get("status") in {"checked", "stated"} and not (r.get("module") and r.get("declarations")):
            reject(f"ledger: rung {rid} is {r['status']} but names no module/declarations")
    for r in data.get("rungs", []):
        for d in r.get("depends_on", []):
            if d not in ids:
                reject(f"ledger: rung {r['id']} depends on unknown rung {d!r}")
    if not failures:
        accept("ledger well-formed")
    return data


def check_axioms(data: dict) -> None:
    decls = []
    for r in data.get("rungs", []):
        if r.get("status") in {"checked", "stated"}:
            for d in r.get("declarations", []):
                decls.append((r["module"], d))
    if not decls:
        accept("axioms: nothing to check")
        return
    modules = sorted({m for m, _ in decls})
    src = "".join(f"import {m}\n" for m in modules)
    for _, d in decls:
        src += f"#print axioms {d}\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT, delete=False) as tmp:
        tmp.write(src)
        tmp_path = Path(tmp.name)
    try:
        r = run(["lake", "env", "lean", str(tmp_path)])
    finally:
        tmp_path.unlink(missing_ok=True)
    if r.returncode != 0:
        reject("axioms: lean failed")
        sys.stdout.write(r.stdout[-4000:])
        return
    seen = {}
    # Lean wraps long axiom lists across lines; match on the joined text.
    flat = " ".join(r.stdout.split())
    for m in re.finditer(r"'(.+?)' depends on axioms: \[(.*?)\]", flat):
        seen[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    for m in re.finditer(r"'(.+?)' does not depend on any axioms", flat):
        seen[m.group(1)] = set()
    for _, d in decls:
        if d not in seen:
            reject(f"axioms: no report for {d}")
            continue
        extra = seen[d] - ALLOWED_AXIOMS
        if extra:
            reject(f"axioms: {d} uses {sorted(extra)}")
        else:
            accept(f"axioms: {d} [{', '.join(sorted(seen[d])) or 'none'}]")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true", help="skip lake build (assume built)")
    args = ap.parse_args()
    if not args.no_build and not check_build():
        return 1
    check_no_sorry()
    data = load_ledger()
    if data is not None:
        check_axioms(data)
    print()
    if failures:
        print(f"REJECTED: {len(failures)} failure(s)")
        return 1
    print("ACCEPTED: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
