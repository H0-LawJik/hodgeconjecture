# Handoff 2026-11-28: `elliptic-curve-points`

- Checked: `HodgeLadder/Tests/EllipticCurvePoints.lean` (rung `elliptic-curve-points`, issue #254, T1 plan node C0) and the general `HodgeLadder/General/QuotAlgHom.lean` (layer 0), both imported from `HodgeLadder.lean`; 40 ledger declarations, standard axioms only.
- Statements: `ellipticAffineHomeomorph : ellipticAffineOpen ≃ₜ affineCurve` (y² = x³ − x) and `ellipticInfinityHomeomorph : ellipticInfinityOpen ≃ₜ infinityCurve` (w = u³ − uw²), subspace topology of ℂ × ℂ against upstream's analytic topology; the cover `ellipticAffineOpen_sup_ellipticInfinityOpen`; the transition (x, y) ↦ (x/y, 1/y) (`mem_ellipticInfinityOpen_iff`, `ellipticInfinityHomeomorph_of_mem`) and its inverse; `compl_ellipticAffineOpen = {[0 : 1 : 0]}`; open embeddings `isOpenEmbedding_affinePoint`, `isOpenEmbedding_infinityPoint`.
- Route: `openHomeomorph` (inverse), `isoMapHomeomorph` of `chartOverIso` (`Hypersurface.chartIso` over Spec ℂ), `affineSpecHomeomorph`, then the local `quotAlgHomHomeomorph` and `Homeomorph.finTwoArrow`. The inverse pin `chartHomeomorph_symm_apply` holds by `rfl`.
- Transition: read in ℙ² through the port's `chart_base_evalPoint_eq`, injectivity of the closed immersion on points, and upstream's `underlying_injective_of_locallyOfFiniteType` (library `Other`, on the drift list).
- Tests: origin (0, 0), (±1, 0), (i, 1 − i) in z ≠ 0; [0 : 1 : 0] = (0, 0) in y ≠ 0; (i, 1 − i) ↦ ((−1 + i)/2, (1 + i)/2) in y ≠ 0, which rejects (x/y, y) and (y/x, 1/x).
- Red team: `docs/sketches/elliptic-curve-points.redteam.md`, pass with changes; changes 1 to 7 applied (general lemma moved to `General/QuotAlgHom`, unused `EllipticCurveSmooth` import dropped, gaps row, ledger entry, conventions row, open embeddings, note on `elliptic-curve-uniformization`).
- Signs: none.
- Failed attempts: `rfl` for `ellipticCurveOrigin = affinePoint ⟨(0, 0), _⟩` times out at 200000 heartbeats; `chartComplexPoint_congr` with `fin_cases` is instant. `MvPolynomial.coe_aeval_eq_eval` (a `RingHomClass.toRingHom` form) does not rewrite `aeval v p`; `aeval_eq_eval` does.
- Timing: the points file elaborates in about 6 s, the general file in about 2 s.
- Next: C3 `elliptic-curve-uniformization` still needs `CompactSpace (ℂ ⧸ L.lattice.toAddSubgroup)` and ℘/℘' → 0, 1/℘' → 0 at Λ (recorded in its ledger note), plus `weierstrass-two-to-one`.
