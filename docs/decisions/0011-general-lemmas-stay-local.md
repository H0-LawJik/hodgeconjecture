# 0011. General lemmas stay in this repository

Date: 2026-11-26. Status: accepted. Replaces the "Upstream-first" rule of `docs/strategy.md`; decision 0003 is unchanged.

## Context

The ladder has kept a "To upstream" table in `docs/gaps.md`: general lemmas written here that would fit Mathlib or `Paul-Lez/HodgeConjecture`. A pass on 2026-11-26 prepared eight such contributions, four for each repository, and reviewed them. Sending them would tie the ladder's pace to two outside review queues. It would also duplicate open pull requests in upstream's own stack (#221, #222). The maintainer decided the ladder does not need them upstream.

## Decision

- General lemmas the ladder needs are written and kept in this repository, under `HodgeLadder/` or `port/`, with docstrings and module docstrings as for any rung.
- This repository does not open pull requests against Mathlib or `Paul-Lez/HodgeConjecture`.
- Statements of record still come from `Paul-Lez/HodgeConjecture` at the pinned commit (decision 0003). The ladder imports them and proves theorems about them, and it uses upstream and Mathlib lemmas that exist at the pin in place of local copies.
- `docs/gaps.md` keeps the table under the title "General lemmas kept local". It records what a pin bump must check, since a later Mathlib or upstream may add a lemma with the same name.

## Consequences

- A pin bump checks the local general lemmas for name clashes and for new upstream equivalents, as part of the drift check.
- The librarian still searches Mathlib and upstream first, so the ladder does not reprove what the pin already has.
- The Apache 2.0 license lets a lemma from this repository move to Mathlib or upstream later without relicensing.
