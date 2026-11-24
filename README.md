# hodgeconjecture

A public, machine-checked attempt to formalize the Hodge conjecture in Lean 4, worked on by people and coding agents together. Site: [hodgeconjecture.com](https://hodgeconjecture.com).

A statement counts here only when the checker accepts a proof of it against the pinned Lean toolchain and the pinned Mathlib. Nothing in this repository claims more than that. The conjecture is open; the ledger says exactly which steps are checked, which are stated, and which are open.

## Status

| | |
|---|---|
| Verdict | open |
| Lean / Mathlib | `v4.36.0` / `v4.36.0` |
| Rungs checked | 1 of 7 |
| Latest | `Z-cycles`: cycles of pure codimension `p` and the group `Z^p(X)`, generalizing Mathlib's Weil divisors |

The ladder of rungs, with dependencies and notes on what Mathlib already has, is in [`docs/roadmap.md`](docs/roadmap.md). The machine-readable copy is [`ledger/ladder.json`](ledger/ladder.json).

## Layout

| Path | What it is |
|---|---|
| `HodgeConjecture/` | The Lean library, one module per topic |
| `ledger/ladder.json` | Status of every rung; the website reads it |
| `tools/check.py` | The checker: build, sorry scan, axiom check, ledger validation |
| `docs/` | Statement, roadmap, acknowledged gaps, decision records |
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
lake build
python3 tools/check.py      # ACCEPTED: all checks passed
```

## What the checker requires

- Builds with the pinned toolchain and Mathlib.
- No `sorry` under `HodgeConjecture/`.
- Only the axioms `propext`, `Classical.choice` and `Quot.sound` in any declaration the ledger names.
- Every `checked` or `stated` rung names declarations that exist.

Output is one line per check, `ACCEPTED (...)` or `REJECTED (...)`, so a CI log and a person read it the same way.

## Joining

Point an agent at [`AGENTS.md`](AGENTS.md), or read it yourself. Open issues labeled `rung` are the posted steps. One rung per pull request; credit goes to the GitHub handle on the merged pull request and into the ledger.

## License

Apache 2.0, matching Mathlib, so anything useful here can move upstream.
