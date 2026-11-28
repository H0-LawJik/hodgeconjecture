module

public import HodgeLadder.General.CircleCylinderHomology
public import HodgeLadder.Torus.Winding.Duality

/-!
# Betti bound for the real torus

Rung `torus-homology-bound` (sub-rung of `torus-singular-cohomology`, sketch
`docs/sketches/torus-singular-cohomology.md`, step 6). On `Tⁿ = UnitAddTorus (Fin n)` the rational
singular homology is finite-dimensional in every degree with `dim H_k(Tⁿ; ℚ) ≤ n.choose k`.

The proof is an induction on `n` that proves both clauses for all `k` at once, because the step in
degree `j + 1` reads the hypothesis in degrees `j + 1` and `j`:

* degree `0`, every `n`: `Tⁿ` is path-connected (Mathlib's instance on a product of circles, also
  at `n = 0`), so `dim H_0(Tⁿ; ℚ) = 1 = n.choose 0`;
* degree `j + 1` at `n = 0`: `T⁰` is a point, so `H_{j+1}(T⁰; ℚ) = 0`;
* degree `j + 1` at `n + 1`: `Tⁿ⁺¹ ≃ₜ Tⁿ × S¹` (`torusSuccHomeo`), the cylinder bound
  `HodgeLadder.CircleCylinder.finrank_homology_prod_circle_le` and Pascal's rule
  `Nat.choose_succ_succ'`.

Only dimensions enter, so no sign or normalization convention is used.

## Main definitions

* `HodgeLadder.Torus.torusSuccHomeo`: `Tⁿ⁺¹ ≃ₜ Tⁿ × S¹`, splitting off the last coordinate.

## Main results

* `HodgeLadder.Torus.homology_torus_bound`: `∀ k, FiniteDimensional ℚ H_k(Tⁿ; ℚ) ∧
  finrank ℚ H_k(Tⁿ; ℚ) ≤ n.choose k`.
* `HodgeLadder.Torus.finiteDimensional_homology_torus`,
  `HodgeLadder.Torus.finrank_homology_torus_le`: the two clauses separately.
* `HodgeLadder.Torus.nontrivial_homology_two_torus_two`,
  `HodgeLadder.Torus.finrank_homology_two_torus_two`: the nonvacuity test `dim H_2(T²; ℚ) = 1`,
  where the bound is `2.choose 2 = 1` and the lower bound comes from the nonzero cup
  `HodgeLadder.Torus.torus_two_cup_ne_zero` through upstream's `cohomologyEquivDualHomology`.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology.Singular Module HodgeLadder.CircleCylinder

namespace HodgeLadder.Torus

/-- `Tⁿ⁺¹ ≃ₜ Tⁿ × S¹`, splitting off the last coordinate. -/
def torusSuccHomeo (n : ℕ) :
    UnitAddTorus (Fin (n + 1)) ≃ₜ UnitAddTorus (Fin n) × UnitAddCircle :=
  (Fin.appendHomeomorph n 1).symm.trans
    ((Homeomorph.refl _).prodCongr (Homeomorph.funUnique (Fin 1) UnitAddCircle))

/-- **Betti bound for the torus.** For every `n` and `k`, `H_k(Tⁿ; ℚ)` is finite-dimensional with
`dim H_k(Tⁿ; ℚ) ≤ n.choose k`. The equality is the Künneth count; the bound is the half that
`torus-singular-cohomology` combines with linear independence of winding classes. -/
theorem homology_torus_bound (n : ℕ) : ∀ k : ℕ,
    FiniteDimensional ℚ (Homology ℚ (torus n) k) ∧
      finrank ℚ (Homology ℚ (torus n) k) ≤ n.choose k := by
  induction n with
  | zero =>
    intro k
    cases k with
    | zero =>
      exact ⟨MayerVietoris.finiteDimensional_homology_zero_of_pathConnected _,
        (MayerVietoris.finrank_homology_zero_of_pathConnected _).le⟩
    | succ j =>
      have := MayerVietoris.subsingleton_homology_succ_of_totallyDisconnected (torus 0) j
      exact ⟨inferInstance, by rw [finrank_zero_of_subsingleton]; exact Nat.zero_le _⟩
  | succ n ih =>
    intro k
    cases k with
    | zero =>
      exact ⟨MayerVietoris.finiteDimensional_homology_zero_of_pathConnected _,
        (MayerVietoris.finrank_homology_zero_of_pathConnected _).le⟩
    | succ j =>
      obtain ⟨h1, b1⟩ := ih (j + 1)
      obtain ⟨h0, b0⟩ := ih j
      let e := (homologyIsoOfHomeomorph ℚ (torusSuccHomeo n) (j + 1)).toLinearEquiv
      have hfd := finiteDimensional_homology_prod_circle (torus n) j
      have hb := finrank_homology_prod_circle_le (torus n) j
      refine ⟨e.symm.finiteDimensional, ?_⟩
      change finrank ℚ (Homology ℚ (TopCat.of (UnitAddTorus (Fin (n + 1)))) (j + 1)) ≤ _
      rw [e.finrank_eq, Nat.choose_succ_succ']
      exact hb.trans (by omega)

/-- `H_k(Tⁿ; ℚ)` is finite-dimensional, for every `n` and `k`. -/
instance finiteDimensional_homology_torus (n k : ℕ) :
    FiniteDimensional ℚ (Homology ℚ (torus n) k) :=
  (homology_torus_bound n k).1

/-- `dim H_k(Tⁿ; ℚ) ≤ n.choose k`. Read it with `finiteDimensional_homology_torus`. -/
theorem finrank_homology_torus_le (n k : ℕ) :
    finrank ℚ (Homology ℚ (torus n) k) ≤ n.choose k :=
  (homology_torus_bound n k).2

/-- `H_2(T²; ℚ) ≠ 0`: a zero `H_2` would make `H²(T²; ℚ) ≃ Dual H_2(T²; ℚ)` zero, against
`torus_two_cup_ne_zero`. -/
theorem nontrivial_homology_two_torus_two : Nontrivial (Homology ℚ (torus 2) 2) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton (Cohomology ℚ (torus 2) 2) :=
    (cohomologyEquivDualHomology ℚ (torus 2) 2).toEquiv.subsingleton
  exact torus_two_cup_ne_zero (Subsingleton.elim _ _)

/-- **Nonvacuity test.** `dim H_2(T²; ℚ) = 1`: the bound `2.choose 2 = 1` is attained. -/
theorem finrank_homology_two_torus_two : finrank ℚ (Homology ℚ (torus 2) 2) = 1 := by
  have := nontrivial_homology_two_torus_two
  have h1 := finrank_homology_torus_le 2 2
  have h0 : 0 < finrank ℚ (Homology ℚ (torus 2) 2) := finrank_pos
  simp only [Nat.choose_self] at h1
  omega

end HodgeLadder.Torus
