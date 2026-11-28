# Handoff 2026-11-28: `circle-cylinder-homology` and `torus-homology-bound`

- Checked: `HodgeLadder/General/CircleCylinderHomology.lean` (layer 1, 35 declarations) and `HodgeLadder/Torus/HomologyBound.lean` (layer 13, through `HodgeLadder.Torus.Winding.Duality` for `torus` and the T² test; 6 declarations), both imported from `HodgeLadder.lean`, standard axioms only.
- Cylinder: for `Y : TopCat.{0}` with `H_{k+1}(Y; ℚ)` and `H_k(Y; ℚ)` finite-dimensional, `finiteDimensional_homology_prod_circle` and `finrank_homology_prod_circle_le` (dim H_{k+1}(Y × S¹) ≤ b_{k+1}(Y) + b_k(Y)), from the exact Mayer–Vietoris count on `Y × U₀`, `Y × V₀`, the overlap split along `W₁`, `W₂` (`sliceHomeo`, inverses `rfl`) and the section `y ↦ (y, ↑(1/4))`.
- Cylinder test: `finrank_homology_one_circle`, dim H_1(S¹; ℚ) = 1; the lower bound is `finrank_range_overlap_zero_add_one_le` (red-team Lean, via upstream `TopCat.singularHomology₀ε_naturality`, new import `HodgeConjecture.Lemmas.AlgebraicTopology.Singular.HomologyZeroNaturality`).
- Torus: `homology_torus_bound n : ∀ k, FiniteDimensional ℚ H_k(Tⁿ) ∧ finrank ≤ n.choose k`, induction on n with all k at once; degree 0 by path-connectedness; step along `torusSuccHomeo n : Tⁿ⁺¹ ≃ₜ Tⁿ × S¹` and `Nat.choose_succ_succ'`. Test: `finrank_homology_two_torus_two`, dim H_2(T²; ℚ) = 1, lower bound from `torus_two_cup_ne_zero` through `cohomologyEquivDualHomology`.
- No sign enters either module; upstream's (i, −j) reads through ranks, the augmentation through its kernel.
- Degree 0 of the cylinder stays out of scope (the torus induction does not need it).
- Timing: about 5 s each to elaborate; `python3 tools/check.py` accepted, about 80 s wall.
- Red team: `docs/sketches/circle-cylinder-homology.redteam.md`, pass with changes; changes 1 to 8 applied; it also served as the review of `torus-homology-bound`, closed here in the same pull request.
- Next: `torus-singular-cohomology` (dim H^k(Tⁿ) through `cohomologyEquivDualHomology`, then span from `linearIndependent_coordCup` and the bound).
