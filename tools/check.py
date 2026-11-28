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
LIB = ROOT / "HodgeLadder"
PORT = ROOT / "port"
LEDGER = ROOT / "ledger" / "ladder.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STATUSES = {"checked", "stated", "open", "refuted", "dead"}
KINDS = {"foundation", "interface", "statement", "case", "reduction", "front", "test"}

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
    check_build_log(r.stdout + r.stderr)
    return True


SORRY_WARNING = re.compile(r"declaration uses [`'\"]sorry[`'\"]")


def check_build_log(log: str) -> None:
    """Reject a build whose log carries Lean's placeholder warning (decision 0014).

    `sorry`, `admit` and `stop` all elaborate to `sorryAx` and make Lean print this
    warning; the text scan below catches only the literal word. Lake replays the
    logs of cached modules, so the warning survives an up-to-date build.
    """
    hits = sorted({line.strip() for line in log.splitlines() if SORRY_WARNING.search(line)})
    if hits:
        reject("placeholder in build log: " + "; ".join(hits[:20]))
    else:
        accept("build log: no placeholder warning")


def check_replayed_log() -> None:
    """In `--no-build` mode, replay cached build logs and scan them (decision 0014)."""
    r = run(["lake", "build", "--no-build"])
    check_build_log(r.stdout + r.stderr)


def check_no_sorry() -> None:
    pat = re.compile(r"\bsorry\b")
    hits = []
    for f in sorted(LIB.rglob("*.lean")) + sorted(PORT.rglob("*.lean")) + [ROOT / "HodgeLadder.lean"]:
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
        ext = r.get("external")
        if ext is not None:
            # Checked by a reproduced build at another pin; recorded, not re-run here.
            need = {"repo", "commit", "toolchain", "declarations", "axioms", "record"}
            if not isinstance(ext, dict) or not need <= set(ext):
                reject(f"ledger: rung {rid} external record needs {sorted(need)}")
            elif not set(ext["axioms"]) <= ALLOWED_AXIOMS:
                reject(f"ledger: rung {rid} external axioms {ext['axioms']} outside the standard three")
            elif not (ROOT / ext["record"]).exists():
                reject(f"ledger: rung {rid} external record file {ext['record']} missing")
        elif r.get("status") in {"checked", "stated"} and not (r.get("module") and r.get("declarations")):
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
        if r.get("status") in {"checked", "stated"} and r.get("external") is None:
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
    # One pass over both report forms; a name has no whitespace, so a match cannot run from one
    # report into the next (an axiom-free declaration after another report used to be missed).
    for m in re.finditer(
            r"'(\S+?)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", flat):
        axioms = m.group(2) or ""
        seen[m.group(1)] = {a.strip() for a in axioms.split(",") if a.strip()}
    for _, d in decls:
        if d not in seen:
            reject(f"axioms: no report for {d}")
            continue
        extra = seen[d] - ALLOWED_AXIOMS
        if extra:
            reject(f"axioms: {d} uses {sorted(extra)}")
        else:
            accept(f"axioms: {d} [{', '.join(sorted(seen[d])) or 'none'}]")


def check_import_clash() -> None:
    """Import all of Mathlib together with both libraries. A declaration name that Mathlib also
    declares (red team on the port, finding M1) fails here instead of at the next pin bump."""
    src = "import Mathlib\nimport HodgeLadder\nimport LefschetzPort\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT, delete=False) as tmp:
        tmp.write(src)
        tmp_path = Path(tmp.name)
    try:
        r = run(["lake", "env", "lean", str(tmp_path)])
    finally:
        tmp_path.unlink(missing_ok=True)
    if r.returncode != 0:
        reject("import clash: Mathlib + HodgeLadder + LefschetzPort do not import together")
        sys.stdout.write(r.stdout[-4000:])
        return
    accept("import clash: none with Mathlib")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true", help="skip lake build (assume built)")
    args = ap.parse_args()
    if not args.no_build and not check_build():
        return 1
    if args.no_build:
        check_replayed_log()
    check_no_sorry()
    check_import_clash()
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
