# Handoff 2026-11-25: `unit-extension-of-invertible`, `prime-divisors-cartier`, `lefschetz-1-1-equality`

- Moved: all three rungs checked (standard axioms). `HodgeLadder.lefschetzOneOneEquality_holds : LefschetzOneOneEquality`.
- Part A (`HodgeLadder.Divisor.AnalyticInvertible`): L^an is invertible, hence has holomorphic frames. The stack's unproved `AnalytificationGenerates` was not needed.
- Part B (`HodgeLadder.Line.*`): transition units of the frames (`Transitions`); the middle sheaf of pairs (n, v) as a local predicate (`MiddleSheaf`); the constant sheaf ℤ as locally constant functions (`LocallyConstant`, via Mathlib's locally-bijective criterion); short exactness by stalks (`UnitExtension`); E's lifts have degree one and transitions vʸ/vˣ, and frames with equal transitions give an isomorphism (`FrameComparison`, `OfInvertible`).
- The B3 re-gluing step was avoided: the comparison runs on the product cover (lift opens of E) × (frames of L^an).
- Convention recorded in `docs/conventions.md` ("Unit extension of a line bundle"). The iso L^an ≅ E.section is a Lean term, so no sign is chosen by hand.
- Upstream candidates logged in `docs/gaps.md`: `lcSheaf`/`constIsoLC`, `Frames.isoOfSameTransitions`.
- Next: red-team pass on `lefschetz-1-1-equality` (vacuity, sign through the divisor–Chern identity, upstream drift), then the Markman inventory.
