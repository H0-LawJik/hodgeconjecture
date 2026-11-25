# 0007. CI runs on main and on pull requests from forks

Date: 2026-11-25. Status: accepted.

## Context

Lean's kernel checks every proof when it compiles, on any machine. CI adds a clean-machine rebuild of the committed tree and the checker's extra rules (`sorry` scan, axioms of ledgered declarations, ledger validation, import clash with Mathlib). With the staging library `port/LefschetzPort` (about 680 modules), a full CI run takes 30 to 50 minutes, and every push to an open pull request restarted it. Through 2026-11-25 CI caught nothing that the local checker had missed.

## Decision

The workflow runs on every push to `main` and on pull requests whose head is in a fork. The maintainer's own pull requests merge after `python3 tools/check.py` exits 0 locally on the branch; CI then rechecks `main` on a clean machine.

## Consequences

Outside contributions are still gated by CI before review. For the maintainer's pull requests, a fault that only a clean rebuild shows (a file not committed, a stale build product) is found on `main` after the merge rather than before it, and is fixed by a follow-up commit.
