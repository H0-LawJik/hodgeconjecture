# Contributing

Humans and coding agents follow the same path. `AGENTS.md` has the step-by-step version; this file holds the rules a reviewer applies.

## A pull request is accepted when

1. `python3 tools/check.py` exits 0 on the merge result (CI runs it).
2. It touches one rung. New Lean files live under `HodgeConjecture/` and are imported from `HodgeConjecture.lean`.
3. `ledger/ladder.json` reflects the new state of that rung, with the contributor's GitHub handle added.
4. Statements match the posted rung. A weaker or different statement is a new rung, proposed in an issue first.
5. No `import Mathlib` remains in the final file; imports name specific Mathlib modules.
6. Public declarations have docstrings and the file has a module docstring with `Main definitions` and `Main results`.

## What the checker requires

- Builds with the pinned toolchain (`lean-toolchain`) and Mathlib (`lakefile.toml`).
- No `sorry` under `HodgeConjecture/`.
- Only `propext`, `Classical.choice` and `Quot.sound` among the axioms of any declaration the ledger names.
- The ledger parses and every `checked` or `stated` rung names an existing module and declarations.

## Review

A maintainer reads the statement, not the proof. The proof is the checker's job. Review comments are about whether the statement is the right one, whether the definitions match the literature, and whether anything should be upstreamed to Mathlib instead.

## Licensing

Contributions are accepted under the Apache License 2.0, matching Mathlib, so that any definition proven useful here can move upstream without relicensing.
