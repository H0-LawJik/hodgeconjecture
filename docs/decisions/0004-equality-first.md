# 0004: Equality first

**Date:** 2026-11-24. **Status:** adopted.

## Context

The upstream statement of the Hodge conjecture, and of Lefschetz (1,1), is an inclusion: every Hodge class lies in the span of cycle classes. A span is blind to signs and to nonzero rational scalars, and an inclusion into a span can hold for a degenerate reason: if the cycle-class construction were wrong in a way that made the span everything, the inclusion would be true and would say nothing. The red-team record of the upstream Lefschetz proof (`docs/sketches/lefschetz-1-1-upstream.redteam.md`) found that the proof runs on a cycle-class model that agrees with the pinned one only up to a nonzero scalar, possibly −1, and that nothing upstream proves the reverse inclusion. The October 2026 withdrawals (arXiv:2610.30976) failed on a sign inside an equality that a span-level claim depended on.

## Decision

- The ladder aims at non-vacuous equalities. An inclusion is a step, recorded and checked, and not an endpoint.
- The conjecture's target form here is Hdg^p(X; ℚ) = algebraicCycleClassSpan X p. The known half, cycle classes are Hodge classes, is a rung of its own (`cycle-classes-are-hodge`).
- Identities between classes are proved exactly, with signs and normalizations determined and recorded in `docs/conventions.md`. "Equal up to a nonzero scalar" does not discharge an identity rung.
- The Lefschetz checkpoint is done when `lefschetz-1-1-equality` is checked, not when the inclusion is. The port of the upstream proof must prove the divisor–Chern identity exactly on the pinned cycle class (`divisor-chern-exact`).
- Cases where only an inclusion is known, or where an equality fails (the integral conjecture in codimension ≥ 2), are recorded as study points in `docs/gaps.md` and `docs/problem.md`, not presented as results.

## Consequences

- New rungs: `divisor-chern-exact`, `lefschetz-1-1-equality`, `cycle-classes-are-hodge`, `lefschetz-1-1-integral`, `projective-space-test`.
- `markman-statement` waits on `lefschetz-1-1-equality`: Markman's method needs a characteristic class equal to a given Weil class with exact normalization, and the checkpoint should show that control first.
- More work before the checkpoint closes. The reverse inclusion in every codimension is a large foundation; its p = 1 case is within reach after the exact divisor–Chern identity.
