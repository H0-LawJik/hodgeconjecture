# Handoff 2026-11-28: `elliptic-curve-cm`

- Checked: `HodgeLadder/Tests/EllipticCurveCM.lean` (layer 8) on the new general module `HodgeLadder/General/ProjQuotientMap.lean` (layer 1); both imported from `HodgeLadder.lean`, 29 declarations in the ledger, standard axioms only.
- General piece: `ProjQuotient.quotMap`, the graded map A ⧸ I → B ⧸ J of a graded map f with f(I) ⊆ J, and `projQuotMap`, its `Proj.map`, with the square `projQuotMap_quotι` against the closed immersions and functoriality in `Proj.map`'s reversed order. The pin has neither.
- Maps: `diagHom c`, the endomorphism over `Spec ℂ` of a diagonal substitution Xⱼ ↦ cⱼXⱼ preserving (F); `ellipticI` with scalars (−1, i, 1), `ellipticNeg` with (1, −1, 1), stated by the substitution itself.
- Identities: `ellipticI ≫ ellipticI = ellipticNeg`, `ellipticNeg ≫ ellipticNeg = 𝟙`, `ellipticI⁴ = 𝟙`, exact, from `diagHom_comp` (`Proj.map_comp` and a ring identity of substitutions); no common rescaling of the variables enters. `ellipticIIso` with inverse [i]³ (`ellipticIIso_inv`), instance `IsIso ellipticI`.
- Points: `chartComplexPoint_comp_diagHom`, in the chart z ≠ 0 the point v goes to (c₀v₀, c₁v₁), so [i] is (x, y) ↦ (−x, iy). Tests: origin fixed; (±1, 0) swapped by [i], fixed by [−1]; (i, 1 − i) ↦ (−i, 1 + i) pins i against −i; [−1] moves (i, 1 − i), so [i] has order four (`ellipticNeg_ne_id`).
- Signs: none unexpected. The choice i over −i is recorded in the conventions row "Complex multiplication on E"; it is load-bearing for `elliptic-curve-uniformization` and the matrix of ellipticI^* in `elliptic-curve-cohomology`.
- Timing: ProjQuotientMap about 4 s, EllipticCurveCM about 6 s.
- Red team: `docs/sketches/elliptic-curve-cm.redteam.md`, pass with changes, changes 1 to 6 applied.
- Next: `elliptic-square-witness` (uses `ellipticIIso_inv`), `elliptic-curve-uniformization`.
