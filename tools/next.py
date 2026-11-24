#!/usr/bin/env python3
"""Print a prover brief for the next ready rung, or for a named rung.

  python3 tools/next.py            # cheapest ready rung
  python3 tools/next.py <id>       # that rung
  python3 tools/next.py --all      # every rung with readiness
  python3 tools/next.py --json     # machine-readable

"Ready" means status open and every dependency checked or stated. Standard library only.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "ledger" / "ladder.json"


def load():
    return json.loads(LEDGER.read_text())


def ready(r, by_id):
    return r["status"] == "open" and all(by_id[d]["status"] in {"checked", "stated"} for d in r.get("depends_on", []))


def module_for(r):
    if r.get("module"):
        return r["module"]
    words = [w for w in r["id"].replace("_", "-").split("-") if w]
    return "HodgeConjecture." + ".".join(w.capitalize() for w in words)


def brief(r, by_id):
    mod = module_for(r)
    path = mod.replace(".", "/") + ".lean"
    deps = ", ".join(r.get("depends_on", [])) or "none"
    sketch = ROOT / "docs" / "sketches" / f"{r['id']}.md"
    lines = [
        f"RUNG {r['id']}",
        f"title:      {r['title']}",
        f"status:     {r['status']}" + ("" if ready(r, by_id) else "  (not ready: a dependency is still open)"),
        f"kind:       {r.get('kind', 'unspecified')}",
        f"depends on: {deps}",
        f"file:       {path}",
        f"module:     {mod}",
        f"sketch:     {'docs/sketches/' + sketch.name if sketch.exists() else 'none; ask the thinker or write the statement from the note'}",
        f"note:       {r.get('note') or '(none)'}",
        "",
        "Do: one file, the statement as posted, no sorry, standard axioms only, then",
        "    python3 tools/check.py; update ledger/ladder.json; import from HodgeConjecture.lean;",
        "    branch rung/" + r["id"] + "; gh pr create; handoff in docs/handoffs/.",
        "If released: write the missing lemma as a Lean statement in the issue, then stop.",
    ]
    return "\n".join(lines)


def main(argv):
    d = load()
    rungs = d["rungs"]
    by_id = {r["id"]: r for r in rungs}
    as_json = "--json" in argv
    args = [a for a in argv if not a.startswith("--")]
    if "--all" in argv:
        rows = [{"id": r["id"], "status": r["status"], "ready": ready(r, by_id), "kind": r.get("kind")} for r in rungs]
        if as_json:
            print(json.dumps(rows, indent=2))
        else:
            for x in rows:
                flag = "ready" if x["ready"] else ("" if x["status"] != "open" else "blocked")
                print(f"{x['id']:<26} {x['status']:<9} {flag}")
        return 0
    if args:
        r = by_id.get(args[0])
        if r is None:
            print(f"no rung {args[0]!r}; ids: {', '.join(by_id)}", file=sys.stderr)
            return 2
    else:
        candidates = [r for r in rungs if ready(r, by_id)]
        if not candidates:
            print("nothing ready: every open rung waits on a dependency", file=sys.stderr)
            return 1
        r = candidates[0]
    if as_json:
        out = dict(r)
        out["module"] = module_for(r)
        out["ready"] = ready(r, by_id)
        print(json.dumps(out, indent=2))
    else:
        print(brief(r, by_id))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
