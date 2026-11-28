# Handoff 2026-11-27: `p1p1-point-class-nonzero`

- Checked: `HodgeLadder/Tests/P1p1PointClassNonzero.lean` (the rung, ledger module) and `HodgeLadder/Tests/ChartCohomology.lean` (the general lemmas, layer 10, imports only `ProjectivePlanePoint`), both imported from `HodgeLadder.lean`; 15 declarations in the ledger, standard axioms only.
- Rung: `p1p1_point_class_ne_zero : cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner_add ≠ 0` in H⁴(ℙ¹ × ℙ¹; ℚ), ∞ = [1 : 0]. Corollary `p1p1Fibres_cup_ne_zero`: the left side of `p1p1Fibres_cup_eq_p1p1Corner` is nonzero, so `cycle-class-multiplicative-p1p1` is now a non-vacuous identity.
- Route: the criterion `cycleComponentSheafClass_ne_zero_of_subsingleton_odd` at p = 1 needs H³ of the complement of (∞, ∞). The complement is {x₁ ≠ 0} × {x₀ ≠ 0} ∪ {x₁ ≠ 0} × {x₁ ≠ 0} ∪ {x₀ ≠ 0} × {x₁ ≠ 0}, three product charts onto ℂ². Two Mayer–Vietoris steps at q = 2 leave H² of {v₁ ≠ 0} and {v₀ ≠ 0} in two product charts, copies of ℂ* × ℂ.
- General H² lemma: `subsingleton_H'_two_chartPreOpen_coord_ne_zero`, any chart onto ℂⁿ with full target and any coordinate, is the ℙ² slit and half-space argument with the coordinate as a parameter. An `example` in `ChartCohomology` derives the ℙ² H² step from it.
- Duplication kept: the ℙ² chart lemmas in `ProjectivePlanePoint` (10 downstream modules) are the n = 2 cases by `rfl`; recorded in `docs/gaps.md`.
- Sign: none. The statement is a nonvanishing; no product enters the proof.
- Red team: `docs/sketches/p1p1-point-class-nonzero.redteam.md`, pass with changes; required changes 1 to 6 and recommended R1, R2 done. Deviation: the gaps row says 10 downstream modules for `ProjectivePlanePoint` (9 before `ChartCohomology` existed).
- Timing: each new module checks in about 10 s once its imports are built.
- Open: H⁴ of ℙ¹ × ℙ¹ has no degree map at the pin, so the sign + of the transversal identity on ℙ¹ × ℙ¹ is fixed only against upstream's normalization. Next: `fibre-class-pullback`, then `cup-positive-degree-test`.
