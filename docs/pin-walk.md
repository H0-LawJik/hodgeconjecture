# Pin walk

A pin bump moves Lean, Mathlib and upstream `Paul-Lez/HodgeConjecture` together (`CLAUDE.md`, change propagation map). This file is the order in which to read the tree when one lands. The library has 907 local modules on 49 import layers (181 in `HodgeLadder`, 726 in the port) and 61 rows of general lemmas kept local (decision 0011). The steps below read them by category and by layer.

1. Before editing any pin, run `python3 tools/pinwalk.py` on the old tree and keep the output: it lists every declaration named in `docs/gaps.md` "General lemmas kept local" with its module and layer, categories in walk order.
2. Red-team drift check. Diff, between the old and the new upstream commit, every definition named in the "Fixed where" column of the register in `docs/conventions.md` (section "Register"; the last rule of section "Rules" asks for this diff and its result in the handoff).
3. Bump `lakefile.toml` and `lean-toolchain`, run `lake update` and `lake exe cache get`.
4. Build the pin modules first: `lake build HodgeLadder.CycleClass.Pins HodgeLadder.Cup.TriadCapPins`. Their `rfl` pins stop compiling when upstream respells a pinned step; read each break against the register before going on.
5. Walk the categories of `docs/gaps.md` in the order printed in step 1. For each category, diff the directories its "Diff at a bump" line names (`git -C .lake/packages/mathlib diff <old>..<new> --stat -- <dir>`, the same in `.lake/packages/HodgeConjecture`), run `python3 tools/pinwalk.py --clash <new source dir>` and settle each name and phrase candidate: keep the row, rename the local declaration, or replace it by the new one and close the row with the date and commit.
6. Repair build breaks in layer order, lowest first: a break at layer k often explains breaks above it.
7. Run `python3 tools/check.py`; its import-clash step fails on any full name the new Mathlib also declares.
8. Finish the propagation map: ledger `toolchain` block, `README.md` version line, and a handoff with the drift result.

**Frozen hubs.** `python3 tools/pinwalk.py --hubs` lists modules by the number of modules of their own library downstream; at one third of the library or more a module is FROZEN. Do not edit a checked frozen hub to add a lemma: put the lemma in a new leaf module that imports it, so a bump rebuilds and re-reads one file. A bump may repair a hub that no longer compiles; keep that repair to the lines that broke.

| Step | Files | Command |
|---|---|---|
| Walk order and layers | `docs/gaps.md`, `HodgeLadder/`, `port/` | `python3 tools/pinwalk.py` |
| Upstream drift | `docs/conventions.md` (Register, Rules) | `git -C .lake/packages/HodgeConjecture diff <old>..<new> -- <file>` |
| Bump | `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | `lake update`, `lake exe cache get` |
| Pins | `HodgeLadder/CycleClass/Pins.lean`, `HodgeLadder/Cup/TriadCapPins.lean` | `lake build HodgeLadder.CycleClass.Pins HodgeLadder.Cup.TriadCapPins` |
| Clash candidates | the "Diff at a bump" directories per category | `python3 tools/pinwalk.py --clash .lake/packages/mathlib/Mathlib`, then `--clash .lake/packages/HodgeConjecture` |
| Port re-read | `port/LefschetzPort/`, `docs/port-lefschetz.md`, `docs/port-tauceti.md` | category "Port-specific" in `docs/gaps.md` |
| Frozen hubs | the modules flagged FROZEN | `python3 tools/pinwalk.py --hubs` |
| Full check | everything | `python3 tools/check.py` |
