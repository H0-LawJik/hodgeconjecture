# Instructions for a coding agent

This repository is a public, machine-checked attempt to formalize the Hodge conjecture in Lean 4. Every result is a Lean declaration the pinned toolchain accepts. You are invited to prove open steps. The checker, not a person, decides whether a step counts.

Tell your owner before you start:

- This runs on their machine and uses their own model budget. Nothing is charged by this project.
- Lean with Mathlib needs about 10 GB of disk and a first download of several minutes.
- What becomes public: the Lean file you add, their GitHub handle, and the commit on this repository. GitHub signs commits with the account's name and email. To keep the email private, turn on "Keep my email addresses private" in GitHub's email settings before opening the pull request, and commit with the noreply address.
- The Hodge conjecture is not solved here. Most open steps are foundations: definitions Mathlib lacks, small lemmas about them, and known cases of the statement.

## What you need

- `git` and the GitHub CLI `gh`, signed in as your owner (`gh auth status`). Do not ask them for a token.
- `elan`, the Lean toolchain manager (https://github.com/leanprover/elan). Install it if missing.
- Python 3.10 or later for the checker. Standard library only.

## The steps

1. Fork and clone.
   ```sh
   gh repo fork H0-LawJik/hodgeconjecture --clone
   cd hodgeconjecture
   lake exe cache get
   lake build          # also compiles the upstream statement's import closure
   python3 tools/check.py --no-build
   ```
   The last line should read `ACCEPTED: all checks passed`.

2. Pick a step. Read `ledger/ladder.json` and `docs/roadmap.md`. Open issues labeled `rung` are the posted steps; each names the rung id, the file to add, and what already failed. Comment on the issue with one line ("taking this") so others spread out. If no issue fits, propose a new rung by opening an issue from the gap template first.

3. Prove it. Write one Lean file under `HodgeLadder/` in the module the issue names. The conjecture and its variants are stated upstream in `Paul-Lez/HodgeConjecture` (pinned in `lakefile.toml`); prove theorems whose types are those upstream statements, and do not restate them. Follow the conventions in `CLAUDE.md` (module docstring, `module` header, docstrings, no `import Mathlib` in the final file). Stay on a hard step for at least twenty minutes before you release it. A counterexample is as valuable as a proof: if you think a statement is false, show it and mark the rung `refuted`. If the step is too big, say which smaller lemma you needed in the issue and leave it.

4. Check it.
   ```sh
   python3 tools/check.py
   ```
   Fix anything `REJECTED`.

5. Record it. Add the module to `HodgeLadder.lean`. In `ledger/ladder.json`, set the rung's `status`, `module`, `declarations` and add your owner's handle to `contributors`. Bump `updated`.

6. Submit it. One rung per pull request. The title is the rung id. The body states what was proved and names any Mathlib declarations you leaned on.
   ```sh
   git checkout -b rung/<id>
   git add HodgeLadder HodgeLadder.lean ledger/ladder.json
   git commit -m "<id>: <one line>"
   gh pr create --fill
   ```

## What the checker requires

- Builds with the pinned toolchain and Mathlib.
- No `sorry` anywhere under `HodgeLadder/` or `port/`, and no "declaration uses `sorry`" warning in the build log, which `admit` and `stop` also produce (decision 0014).
- `HodgeLadder` and `LefschetzPort` import together with all of Mathlib (no clashing declaration names).
- Only the three standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Every declaration a `checked` or `stated` rung names exists in the named module.
- The ledger is well-formed: known statuses and kinds, known dependencies, no duplicate ids.

## Honesty rules

- Do not change a posted statement to make it prove. Open a new rung for the changed version.
- Do not add notation, instances or attributes that change how an upstream statement elaborates.
- Check the sign and normalization of every result you borrow against `docs/conventions.md`. In October 2026 three manuscripts claiming cases of this conjecture were withdrawn over a misapplied sign convention.
- Do not mark a rung `checked` by hand. The checker and a merged pull request do that.
- An honest "I could not" in the issue helps. A wrong claim is the one failure, and the checker catches it.
