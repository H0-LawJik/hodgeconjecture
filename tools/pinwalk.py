#!/usr/bin/env python3
"""Pin walk: the order and the clash candidates for a Lean, Mathlib and upstream pin bump.

Run from anywhere:
  python3 tools/pinwalk.py                  # layers, then every gaps.md declaration by category
  python3 tools/pinwalk.py --hubs [--top N] # modules by downstream count; frozen hubs flagged
  python3 tools/pinwalk.py --clash DIR      # candidate clashes in a Mathlib or upstream source tree

Layer: 0 for a module that imports only Mathlib or upstream, else 1 + the largest layer of its
local imports (the longest local import path below it). Local modules are HodgeLadder/**/*.lean
and port/**/*.lean; the two library roots are left out. Categories and rows come from
docs/gaps.md "General lemmas kept local" (one ### heading per category). A backticked name in
the first column counts as a declaration when some local module declares it; other names are
listed as unresolved. Output is sorted, so two runs on the same tree print the same text.
Standard library only.
"""
from __future__ import annotations

import argparse
import re
import signal
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GAPS = ROOT / "docs" / "gaps.md"
SOURCES = [(ROOT / "HodgeLadder", "HodgeLadder"), (ROOT / "port" / "LefschetzPort", "LefschetzPort")]
FROZEN_DEFAULT = 1 / 3  # share of its own library downstream at which a module is a frozen hub

# Key phrases per gaps.md category, matched against full declaration names in --clash DIR.
# A hit is a candidate new equivalent of a local row; read it, then keep or replace the row.
PHRASES = {
    "Homological algebra and derived categories": [
        r"quasiIso_τ₂", r"HomologicalComplex\.mapBifunctor\w*([Ss]ingle|[Ss]hortExact)",
        r"Cocycle\.comp$", r"Ext\.\w*IsoAddEquiv", r"HomologicalComplex\.\w*[Ee]xtend\w*(Mul|Tensor)",
        r"stupidTrunc\w*[Ll]ift", r"Adjunction\.mapCochainComplex", r"homologyMap_linearDual"],
    "Sheaves and sheafification": [
        r"locallyConstant\w*[Ss]heaf", r"constantSheaf\w*[Ll]ocallyConstant", r"toSheafify\w*[Tt]ensor",
        r"Sheaf\.\w*tensor\w*_exact", r"sheafCompose\w*[Ee]xact", r"IsFlasque\.\w*(acyclic|subsingleton)"],
    "Singular homology, cohomology and simplicial cochains": [
        r"universalCoefficient", r"shuffleChain", r"oneSing|singular\w*[Cc]up\w*[Uu]nit",
        r"TopPair\.ofSubsetHom", r"triadChainMap", r"affineSingularSimplex|affineSimplexMap",
        r"cochainEval", r"relativeHomologyProjection_(sur|in)jective"],
    "Topology": [r"GLPos\.\w*[Cc]onnected", r"isPathConnected\w*det", r"irreducibleSpace_of_cover"],
    "Linear algebra: Clifford and exterior algebras": [
        r"CliffordAlgebra\.\w*(basis|rank|sublist)", r"spinEquiv|cliffordDualProd", r"^AlgHom\.restrict$"],
    "Manifolds, charts and analytic functions": [
        r"analyticAt_evaluate", r"finAppendEquiv", r"prodChart\w*maximalAtlas"],
    "Algebraic geometry and commutative algebra": [
        r"IsRegularLocalRing\.\w*(isDomain|UFD|uniqueFactorization)", r"nonempty_complexPoint",
        r"codimensionCycleSubgroup_one", r"isIso_cycleComponentι"],
    "Local cohomology, orientation and the cycle class": [
        r"Support\w*OnOpen$", r"normalizedRelativeCoclass\w*relativeCohomologyMap",
        r"complexLocalOrientation\w*smul", r"chartNormalProjectionCoclass\w*ne_zero"],
    "De Rham complex and holomorphic forms": [
        r"formWedge|holomorphicWedge", r"deRham\w*[Cc]up", r"HolomorphicForm\w*[Mm]odule",
        r"holomorphicFormOfConstant\w*ne_zero"],
    "Port-specific": [
        r"[Cc]oefficientChange\w*[Aa]dd", r"constantCoefficient\w*_comp", r"isoOfSameTransitions"],
}

IMPORT_RE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*(?:--.*)?$")
DECL_RE = re.compile(
    r"^\s*(?:@\[.*?\]\s*)?(?:(?:private|protected|noncomputable|public|nonrec|partial|unsafe|"
    r"scoped|local)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|"
    r"alias|irreducible_def)\s+([^\s:({\[⦃]+)")
NS_RE = re.compile(r"^\s*namespace\s+(\S+)")
SEC_RE = re.compile(r"^\s*(?:@\[.*?\]\s*)?(?:(?:public|private|noncomputable)\s+)*(?:section|mutual)\b")
END_RE = re.compile(r"^end\b")
NAME_RE = re.compile(r"^[^\W\d][\w.'!?]*$")
HEX_RE = re.compile(r"^[0-9a-f]{7,40}$")


def imports(path: Path) -> list[str]:
    """Imports in the header: the lines before the first command that is no import."""
    out, in_comment = [], False
    for line in path.read_text().splitlines():
        s = line.strip()
        if in_comment:
            in_comment = "-/" not in s
            continue
        if not s or s.startswith("--") or s == "module":
            continue
        if s.startswith("/-") and not s.startswith("/-!"):
            in_comment = "-/" not in s[2:]
            continue
        m = IMPORT_RE.match(line)
        if not m:
            break
        out.extend(m.group(1).split())
    return out


def declarations(path: Path):
    """Yield (full name, line number) for each named declaration, tracking namespaces."""
    stack: list[str | None] = []
    for n, line in enumerate(path.read_text(errors="replace").splitlines(), 1):
        if m := NS_RE.match(line):
            stack.append(m.group(1))
        elif SEC_RE.match(line):
            stack.append(None)
        elif END_RE.match(line) and stack:
            stack.pop()
        elif m := DECL_RE.match(line):
            name = m.group(1)
            root = name.startswith("_root_.")
            yield (name[7:] if root else ".".join([s for s in stack if s] + [name])), n


def graph():
    mods = {".".join((pre,) + f.relative_to(base).with_suffix("").parts): f
            for base, pre in SOURCES for f in sorted(base.rglob("*.lean"))}
    deps = {m: sorted({i for i in imports(f) if i in mods}) for m, f in mods.items()}
    layer: dict[str, int] = {}

    def lay(m: str) -> int:
        if m not in layer:
            layer[m] = -1  # cycle guard; Lean forbids import cycles
            layer[m] = 1 + max((lay(d) for d in deps[m]), default=-1)
        return layer[m]

    for m in sorted(mods):
        lay(m)
    down: dict[str, set[str]] = {m: set() for m in mods}
    for m in sorted(mods, key=lambda x: layer[x], reverse=True):
        for d in deps[m]:
            down[d] |= down[m] | {m}
    return mods, deps, layer, down


def gaps_rows():
    """Yield (category, first column, module column) for each row of the kept-local tables."""
    cat, cols, inside = None, None, False
    for line in GAPS.read_text().splitlines():
        if line.startswith("## "):
            inside = line.strip() == "## General lemmas kept local"
        elif not inside:
            continue
        elif line.startswith("### "):
            cat, cols = line[4:].strip(), None
        elif line.startswith("|") and cat:
            cells = [c.strip() for c in line.strip().strip("|").split(" | ")]
            if cols is None:
                cols = cells
            elif not set(cells[0]) <= set("-|: "):
                row = dict(zip(cols, cells))
                yield cat, row.get("Local declaration", ""), row.get("Module", "")


def local_index(mods):
    idx: dict[str, list[tuple[str, str]]] = {}
    for m, f in mods.items():
        for full, _ in declarations(f):
            idx.setdefault(full.rsplit(".", 1)[-1], []).append((full, m))
    return idx


def resolve(cell: str, idx, mcell: str = ""):
    """Backticked names of a first column, split into locally declared and unresolved ones.
    A name declared in the row's own modules resolves there; otherwise anywhere local."""
    found, missing, own = [], [], set(re.findall(r"`([^`]+)`", mcell))
    for tok in re.findall(r"`([^`]+)`", cell):
        short = tok.rsplit(".", 1)[-1]
        if not NAME_RE.match(tok) or tok.startswith("_") or len(short) < 4 or HEX_RE.match(tok):
            continue
        hits = [h for h in idx.get(short, []) if h[0] == tok or h[0].endswith("." + tok)]
        hits = [h for h in hits if h[1] in own] or hits
        (found if hits else missing).append((tok, hits))
    return found, missing


def walk(mods, layer, idx):
    by_cat: dict[str, list] = {}
    for cat, cell, mcell in gaps_rows():
        by_cat.setdefault(cat, []).append(resolve(cell, idx, mcell) + (mcell,))
    print(f"modules {len(mods)}; layers 0..{max(layer.values())}; categories {len(by_cat)}")
    print("walk order: categories by lowest layer, then rows by layer\n")

    def low(rows):
        return min((layer[m] for f, _, _ in rows for _, hs in f for _, m in hs), default=10**6)

    order = list(by_cat)  # gaps.md order breaks ties
    for cat in sorted(order, key=lambda c: (low(by_cat[c]), order.index(c))):
        rows = by_cat[cat]
        print(f"## {cat} ({len(rows)} rows)")
        for found, missing, mcell in sorted(rows, key=lambda r: low([r])):
            if not found:
                print(f"  -   {mcell or 'no module'}: no local declaration resolved")
            for tok, hits in found:
                for full, m in sorted(set(hits)):
                    print(f"  {layer[m]:<3} {m}  {full}")
            if missing:
                print("      unresolved: " + ", ".join(sorted({t for t, _ in missing})))
        print()


def hubs(mods, layer, down, top: int, frozen: float):
    """Per library: modules by the number of modules of the same library that import them."""
    for name in ("HodgeLadder", "LefschetzPort"):
        lib = {m for m in mods if m.startswith(name + ".")}
        cut = frozen * len(lib)
        print(f"## {name}: {len(lib)} modules; FROZEN at >= {cut:.0f} downstream ({frozen:.2f} of the library)")
        print("downstream  layer  module")
        for m in sorted(lib, key=lambda m: (-len(down[m] & lib), m))[:top]:
            d = len(down[m] & lib)
            print(f"{d:>10}  {layer[m]:>5}  {m}{'  FROZEN' if d >= cut else ''}")
        print()


def clash(tree: Path, mods, idx):
    local = {}
    for cat, cell, mcell in gaps_rows():
        for tok, hits in resolve(cell, idx, mcell)[0]:
            for full, m in hits:
                local.setdefault(full.rsplit(".", 1)[-1], set()).add((full, m, cat))
    pats = {cat: [re.compile(p) for p in ps] for cat, ps in PHRASES.items()}
    names, phrase = [], {}
    for f in sorted(tree.rglob("*.lean")):
        if ".lake" in f.relative_to(tree).parts:
            continue
        for full, n in declarations(f):
            where = f"{f.relative_to(tree)}:{n}"
            short = full.rsplit(".", 1)[-1]
            for lfull, m, cat in sorted(local.get(short, ())):
                names.append((lfull == full, lfull, m, full, where))
            for cat, ps in pats.items():
                for p in ps:
                    if p.search(full):
                        phrase.setdefault((cat, p.pattern), []).append((full, where))
    print(f"local names {len(local)}; name candidates {len(names)}\n")
    print("## name candidates (local short name declared in the tree; SAME = same full name)")
    for same, lfull, m, full, where in sorted(names, key=lambda t: (not t[0], t[1], t[4])):
        print(f"  {'SAME' if same else 'name'}  {lfull} ({m})  <->  {full}  {where}")
    missing = sorted({c for c, _, _ in gaps_rows()} - set(PHRASES))
    print("\n## phrase candidates (by category; at most 6 shown per phrase)")
    for cat in sorted(PHRASES):
        for p in PHRASES[cat]:
            hits = phrase.get((cat, p), [])
            if hits:
                print(f"  [{cat}] /{p}/ {len(hits)} hit(s)")
                for full, where in hits[:6]:
                    print(f"      {full}  {where}")
    if missing:
        print("\ncategories with no phrase list: " + ", ".join(missing))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--hubs", action="store_true", help="list modules by downstream count")
    ap.add_argument("--top", type=int, default=25, help="rows shown by --hubs")
    ap.add_argument("--frozen", type=float, default=FROZEN_DEFAULT, help="frozen-hub share")
    ap.add_argument("--clash", type=Path, metavar="DIR", help="Mathlib or upstream source tree")
    args = ap.parse_args()
    mods, _, layer, down = graph()
    if args.hubs:
        hubs(mods, layer, down, args.top, args.frozen)
        return 0
    idx = local_index(mods)
    if args.clash:
        if not args.clash.is_dir():
            print(f"no such directory: {args.clash}")
            return 2
        clash(args.clash, mods, idx)
        return 0
    walk(mods, layer, idx)
    return 0


if __name__ == "__main__":
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)  # quiet exit when piped into head
    sys.exit(main())
