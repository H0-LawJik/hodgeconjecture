# hodgeconjecture

A public ladder of machine-checked Lean 4 proofs about the Hodge conjecture, worked on by people and coding agents together. The conjecture itself is stated in [Paul-Lez/HodgeConjecture](https://github.com/Paul-Lez/HodgeConjecture), which this repository imports at a pinned commit. Site: [hodgeconjecture.com](https://hodgeconjecture.com).

A statement counts here only when the checker accepts a proof of it against the pinned Lean toolchain and the pinned Mathlib. Nothing in this repository claims more than that. The conjecture is open; the ledger says exactly which steps are checked, which are stated, and which are open.

## Status

| | |
|---|---|
| Verdict | open |
| Statement of record | `Paul-Lez/HodgeConjecture` at `2ead713` |
| Lean / Mathlib | `v4.35.0-rc4` / `v4.35.0-rc4` (following upstream) |
| Checkpoint | Lefschetz (1,1) as an equality, `Hdg^1(X; ℚ) = algebraicCycleClassSpan X 1`, checked (`HodgeLadder.lefschetzOneOneEquality_holds`); on ℙ¹ both sides are one-dimensional (`HodgeLadder.Tests.projectiveLine_test`) |
| Current target | milestone M2: the Markman inventory is written ([`docs/notes/2026-11-25-markman-inventory.md`](docs/notes/2026-11-25-markman-inventory.md)) and `markman-statement` is open; first comes front `cup`, a ring structure on upstream's rational cohomology ([decision 0008](docs/decisions/0008-cup-product-front.md)) |

The ladder of rungs is in [`docs/roadmap.md`](docs/roadmap.md); the machine-readable copy is [`ledger/ladder.json`](ledger/ladder.json). Why the project is shaped this way: [`docs/decisions/0003-rebase-on-upstream-statement.md`](docs/decisions/0003-rebase-on-upstream-statement.md).

## Layout

| Path | What it is |
|---|---|
| `HodgeLadder/` | The Lean library: proofs about the upstream statements, consistency checks, non-vacuity tests |
| `ledger/ladder.json` | Status of every rung; the website reads it |
| `tools/check.py` | The checker: build, sorry scan, axiom check, ledger validation |
| `docs/` | The literature map (`problem.md`), strategy, harness, roadmap, conventions register, audits, gaps, decision records |
| `AGENTS.md` | How a coding agent picks a step, proves it and submits it |
| `CONTRIBUTING.md` | What a pull request has to satisfy |

## Setup

Install elan once:

```sh
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
source ~/.elan/env
```

Then, from this directory:

```sh
lake exe cache get          # prebuilt Mathlib, several GB
lake build                  # also compiles the upstream statement's import closure
python3 tools/check.py      # ACCEPTED: all checks passed
```

## What the checker requires

- Builds with the pinned toolchain and Mathlib.
- No `sorry` under `HodgeLadder/` or `port/`.
- `HodgeLadder` and `LefschetzPort` import together with all of Mathlib (no clashing declaration names).
- Only the axioms `propext`, `Classical.choice` and `Quot.sound` in any declaration the ledger names.
- Every `checked` or `stated` rung names declarations that exist.
- The ledger is well-formed: known statuses and kinds, known dependencies, no duplicate ids.

Output is one line per check, `ACCEPTED (...)` or `REJECTED (...)`, so a CI log and a person read it the same way.

## Joining

Point an agent at [`AGENTS.md`](AGENTS.md), or read it yourself. Open issues labeled `rung` are the posted steps. One rung per pull request; credit goes to the GitHub handle on the merged pull request and into the ledger.

## License

Apache 2.0, matching Mathlib, so anything useful here can move upstream.
