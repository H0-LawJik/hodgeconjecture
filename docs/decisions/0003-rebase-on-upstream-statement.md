# 0003: Rebase on the upstream statement; this repository becomes a ladder of proofs about it

**Date:** 2026-11-24. **Status:** adopted. **Supersedes:** the interface-first pattern in `docs/harness.md` (2026-11-23) and the foundation rungs it implied.

## Context

A conformance check against the 2026 literature (`docs/audits/2026-11-24-conformance.md`) found:

1. `Paul-Lez/HodgeConjecture` states the Hodge conjecture in Lean 4 on real definitions: X(ℂ) with the analytic topology, constant-sheaf rational cohomology, holomorphic de Rham hypercohomology with the Hodge filtration, and cycle classes from cohomology with support. It has 461 Lean files, about 84,000 lines, no `sorry` and no axioms at commit `2ead713`, and is being ported into `google-deepmind/formal-conjectures`. It also states the Lefschetz (1,1) case, the dimension ≤ n case and the abelian-variety case (`HodgeConjecture/Variants.lean`).
2. An interface structure like the one this repository planned was shown vacuous or false in `lean-dojo/LeanMillenniumPrizeProblems` (regression tests `Tests/Hodge/StatementIsVacuous.lean`, `Tests/Hodge/CycleClassUnconstrained.lean`). `formal-conjectures` rejects placeholder statements for this reason.
3. Upstream already carries a codimension-p cycle subgroup (`codimensionCycleSubgroup`), so this repository's one checked Lean rung duplicated it.
4. A full proof of rational Lefschetz (1,1) against those definitions exists as an unmerged stack of upstream pull requests (#217–#226, #9, #230, #228), on Lean and Mathlib v4.33.1, last updated 2026-10-01.

## Decision

- The statements of record are upstream's. This repository imports `Paul-Lez/HodgeConjecture` at a pinned commit; the conjecture and its variants are stated there and only there.
- This repository's Lean library is renamed `HodgeLadder` (upstream's library is `HodgeConjecture`; the names would collide). It holds proofs about upstream statements, consistency checks between them, and non-vacuity tests.
- Toolchain follows upstream: Lean and Mathlib `v4.35.0-rc4`, bumped together with the upstream pin.
- The interface-first rungs and the foundation rungs that upstream now covers are marked `dead` in the ledger with the reason. Rung ids stay.
- First target: the Lefschetz checkpoint. Verify the upstream proof independently, red-team its definitions and conventions, add non-vacuity tests, port it to the current pin (contributed upstream), and check `LefschetzOneOne` here. The Markman front opens only after this checkpoint, with an inventory of tools and gaps taken from it.
- Upstream-first: general mathematics goes to Mathlib; statement-level definitions and their supporting lemmas go to `Paul-Lez/HodgeConjecture`; this repository keeps what neither would take (the public ledger, the harness, the falsification records, proofs of variants on top of upstream, the literature map in `docs/problem.md`).

## What this repository keeps

| Kept | Why it is not duplicative |
|---|---|
| `docs/problem.md`, `docs/references.md` | A sourced map of the mathematical literature and its 2026 state; upstream documents the formal statement, not the field |
| Ledger, checker, `tools/next.py`, roles, red-team records, handoffs | Public coordination for outside agents; upstream has build checks but no public ledger or contributor desk |
| hodgeconjecture.com | The public view of the ledger |
| Falsification work (`docs/conventions.md`, non-vacuity tests) | Tests of upstream definitions, contributed back where upstream wants them |
| Proofs of variants and reductions on upstream definitions | Upstream states these cases; proofs beyond Lefschetz (1,1) do not exist there |

## Consequences

- Builds compile upstream's statement closure in addition to Mathlib. CI time grows.
- Two small lemmas from the retired cycle module (codimension one equals Mathlib's `weilDivisors`; distinct codimensions meet in zero) have no upstream counterpart and are offered upstream rather than kept here.
- Tau Ceti's line bundles are not on the critical path: the upstream Lefschetz stack carries its own Cartier data and an Oka GAGA port. Tau Ceti stays a fallback for line-bundle and Chow-group material.
