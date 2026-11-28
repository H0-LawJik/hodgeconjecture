# Handoff 2026-11-27: `plane-cubic-subscheme`

- Checked: `HodgeLadder/Tests/EllipticCurve.lean` (layer 7) on two new general modules, `HodgeLadder/General/ProjQuotient.lean` (layer 0) and `HodgeLadder/General/Hypersurface.lean` (layer 2); all three imported from `HodgeLadder.lean`, 36 declarations in the ledger, standard axioms only.
- Object: E = Proj (ℂ[x, y, z] ⧸ (y²z − x³ + xz²)) with x = X 0, y = X 1, z = X 2, as `HodgeLadder.Tests.ellipticCurve : Over (Spec ↧ℂ)`. Route: Proj of a graded quotient, chosen over gluing charts or an ideal sheaf so that a graded endomorphism of ℂ[x, y, z] preserving (F) gives an endomorphism of E by `Proj.map` (the route for `elliptic-curve-cm`).
- General pieces: the quotient grading by a homogeneous ideal (`ProjQuotient.gradedAlgebra`), and `isClosedImmersion_map`: `Proj.map` of a graded map onto every piece is a closed immersion, Spec of a surjection over each D₊(s). The pin has `Proj.map` and neither of these. `Hypersurface.chartIso`: V₊(F) ∩ D₊(Xᵢ) ≅ Spec R[Y] ⧸ (dehomogenize i F), lying over Oka's standard chart (`chartIso_inv_ι`).
- Projective: `ellipticCurveι ≫ (okaIsoSpace 2).hom`, ambient dimension 2, into `projectivePlane`. This instance holds for every homogeneous ideal; the content is in the charts and the tests.
- Charts: z ≠ 0 is Spec ℂ[x, y]/(y² − x³ + x), y ≠ 0 is Spec ℂ[u, w]/(w − u³ + uw²), each over the standard chart of ℙ²; they cover E (`ellipticCurve_chart_cover`, from x³ = y²z + xz²).
- Tests: [0 : 0 : 1], [0 : 1 : 0], the two-torsion points (±1, 0) (pin the sign of the linear term), `Nonempty (ComplexPoint ellipticCurve)`, and `compl_chartAffine`: the complement of z ≠ 0 is the single point [0 : 1 : 0].
- Signs: none in the rung. The linear term is a choice of curve, recorded in the conventions row "Plane cubic E and its charts"; it is load-bearing for `elliptic-curve-uniformization`.
- Hazard found: a `local notation` over section variables inside a `variable` binder elaborates the binder to an error placeholder with no message; recorded in `docs/gaps.md` "Known weaknesses" with the `admit`/`stop` gap and a proposed checker rule.
- Timing: ProjQuotient about 4 s, Hypersurface about 14 s, EllipticCurve about 5 s.
- Red team: `docs/sketches/plane-cubic-subscheme.redteam.md`, pass with changes, changes 1 to 6 applied; the `elliptic-curve-cm` ledger note carries its caution (define the negation by (x, −y, z); `Proj.map` is contravariant; the S/I → S/I lemma is E5's to write).
- Next: `elliptic-curve-smooth`, `elliptic-curve-integral`, `elliptic-curve-cm`, `elliptic-curve-points`.
