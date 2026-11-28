# Handoff 2026-11-28: `elliptic-coordinate-functions`

- Checked: `HodgeLadder/Tests/EllipticCurveCoordinates.lean` (rung `elliptic-coordinate-functions`, issue #292, sub-rung S4 of `elliptic-curve-holomorphic-form`), imported from `HodgeLadder.lean`; 43 ledger declarations, standard axioms only.
- Statements: `ellipticX`, `ellipticY` on z ≠ 0 and `ellipticU`, `ellipticW` on y ≠ 0, sections of upstream's `holomorphicFunctionSheaf ellipticCurve (dim ellipticCurve.left)` (`ellipticHolomorphic_eq_openHolomorphicFunctions`, `ellipticX_eq_regularToHolomorphicSheaf`, both `rfl`); values `ellipticX_apply`, ..., `ellipticW_apply` through the chart homeomorphisms; `ellipticY_sq : y² = x³ − x`, `ellipticW_eq : w = u³ − uw²`; on the overlap u·y = x, w·y = 1, x·w = u, y a unit.
- Route: the port's `regularFunctionsToHolomorphic` of the chart coordinates; the value lemma `ellipticChartHolomorphic_apply` unwinds `chartHomeomorph` with upstream's `evaluate_openEquiv`, `evaluate_eq`, `evaluate_map`, `affineSpecEquiv_apply`, then `quotAlgHomHomeomorph.left_inv`. Relations are ring identities in the chart ring.
- Tests: values at the origin, (±1, 0), (i, 1 − i), [0 : 1 : 0]; none of x, y, u, w is constant; fibre lemmas for S5 step 6 (`eq_of_ellipticX_eq_of_ellipticY_eq`, `ellipticY_eq_or_eq_neg_of_ellipticX_eq`).
- Red team: `docs/sketches/elliptic-coordinate-functions.redteam.md`, pass with changes; changes 1 to 6 applied (file moved to `Tests/`, the existential pin replaced by the `rfl` type equality, ledger, conventions row, roadmap row, fibre lemmas).
- Signs: none.
- Failed attempts: `simpa only [map_pow, map_sub]` leaves the coordinates folded and fails to match; `simp only ... at h; exact h` works. Upstream's `AlgebraicGeometry.ComplexPoint.chartSection` clashes with a bare `chartSection` under the opened namespace, so new names carry the `elliptic` prefix.
- Timing: the file elaborates in about 24 s (module build 20 s).
- Next: S5 `elliptic-omega`; the red-team verdict, finding 7, lists what it must build (opens V₂, V₃, inverse of a nowhere-vanishing section, Kähler identities, gluing, nonvanishing).
