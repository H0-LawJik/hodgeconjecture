module

public import HodgeLadder.Torus.HomologyBound
public import HodgeLadder.Cup.SingularCupLinear

/-!
# Rational singular cohomology of the real torus in degrees one and two

Rung `torus-singular-cohomology` (issue #230, sketch `docs/sketches/torus-singular-cohomology.md`,
order 4). On `Tⁿ = UnitAddTorus (Fin n)` let `aᵢ ∈ H¹(Tⁿ; ℚ)` be the winding class of the
coordinate character `x ↦ exp (2πi xᵢ)` (`coordWinding i`). Then:

* for `n ≥ 2` the classes `aᵢ` are linearly independent and span `H¹(Tⁿ; ℚ)`, so
  `dim H¹(Tⁿ; ℚ) = n`;
* for every `n` the products `aᵢ ⌣ aⱼ` with `i < j` (`coordCup`) are linearly independent and span
  `H²(Tⁿ; ℚ)`, so `dim H²(Tⁿ; ℚ) = n.choose 2`.

Cohomology is upstream's `AlgebraicTopology.Singular.Cohomology ℚ`, the cup product is the
ladder's `HodgeLadder.Cup.cupSing` (front face times back face, no sign). The headline results
are the `LinearIndependent` and `span = ⊤` pairs; the `finrank` equalities follow from them and
from finite dimensionality, which is proved here as an instance (a bare `finrank` would read `0` on
an infinite-dimensional space).

The proof combines two checked halves. The upper bound: upstream's
`cohomologyEquivDualHomology` identifies `H^k(Tⁿ; ℚ)` with the dual of `H_k(Tⁿ; ℚ)`, which is
finite-dimensional of dimension at most `n.choose k` by rung `torus-homology-bound`. The lower
bound: independence of `n.choose 2` cups is `linearIndependent_coordCup` (rung
`torus-winding-duality`); independence of the `aᵢ` follows by cupping a relation `Σ cᵢ aᵢ = 0` on
the right with `a_m`, `m ≠ k` (here `n ≥ 2` enters), and evaluating on the coordinate torus
`T_km`, which returns `c_k`. That step needs additivity of `cupSing` in its first slot,
`HodgeLadder.Cup.cupSing_add_left` and `HodgeLadder.Cup.cupSing_smul_left` (module
`HodgeLadder.Cup.SingularCupLinear`), packaged as the linear map `HodgeLadder.Cup.cupSingRight`. Counting
`#{(i, j) : i < j} = n.choose 2` (`card_coordPairs`) closes the span.

Only dimensions and the exact duality formula enter; no sign is used beyond the formula
`⟨aᵢ ⌣ aⱼ, T_kl⟩ = [i = k][j = l] − [i = l][j = k]` of `torusEval_coordTorus_cup`. The
sheaf-singular comparison `Ψ` does not enter this file.

## Main definitions

* `HodgeLadder.Torus.coordWindingBasis`, `HodgeLadder.Torus.coordCupBasis`: the two bases as
  `Basis` values, for transport along a linear equivalence.

## Main results

* `HodgeLadder.Torus.linearIndependent_coordWinding`, `HodgeLadder.Torus.span_coordWinding`,
  `HodgeLadder.Torus.finrank_cohomology_one_torus`: `H¹(Tⁿ; ℚ)` has basis `a₀, …, a_{n−1}` for
  `n ≥ 2`.
* `HodgeLadder.Torus.span_coordCup`, `HodgeLadder.Torus.finrank_cohomology_two_torus`:
  `H²(Tⁿ; ℚ)` has basis `aᵢ ⌣ aⱼ`, `i < j` (independence is
  `HodgeLadder.Torus.linearIndependent_coordCup`).
* `HodgeLadder.Torus.finiteDimensional_cohomology_torus`,
  `HodgeLadder.Torus.finrank_cohomology_torus_eq`, `HodgeLadder.Torus.finrank_cohomology_torus_le`:
  `dim H^k(Tⁿ; ℚ) = dim H_k(Tⁿ; ℚ) ≤ n.choose k`, finite.
* `HodgeLadder.Torus.finrank_cohomology_one_torus_two`, `finrank_cohomology_two_torus_two`,
  `finrank_cohomology_one_torus_four`, `finrank_cohomology_two_torus_four`: the ledger's cases
  `n = 2, 4`, with values `2, 1, 4, 6`; `HodgeLadder.Torus.coordWinding_zero_ne_one_two`:
  `a₀ ≠ a₁` on `T²`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology.Singular Module HodgeLadder.Cup

namespace HodgeLadder.Torus

/-- `H^k(Tⁿ; ℚ)` is finite-dimensional, as the dual of the finite-dimensional `H_k(Tⁿ; ℚ)`. -/
instance finiteDimensional_cohomology_torus (n k : ℕ) :
    FiniteDimensional ℚ (Cohomology ℚ (torus n) k) :=
  (cohomologyEquivDualHomology ℚ (torus n) k).symm.finiteDimensional

/-- `dim H^k(Tⁿ; ℚ) = dim H_k(Tⁿ; ℚ)`, through upstream's `cohomologyEquivDualHomology`. -/
theorem finrank_cohomology_torus_eq (n k : ℕ) :
    finrank ℚ (Cohomology ℚ (torus n) k) = finrank ℚ (Homology ℚ (torus n) k) := by
  rw [(cohomologyEquivDualHomology ℚ (torus n) k).finrank_eq, Subspace.dual_finrank_eq]

/-- `dim H^k(Tⁿ; ℚ) ≤ n.choose k`. Read it with `finiteDimensional_cohomology_torus`. -/
theorem finrank_cohomology_torus_le (n k : ℕ) :
    finrank ℚ (Cohomology ℚ (torus n) k) ≤ n.choose k :=
  (finrank_cohomology_torus_eq n k).trans_le (finrank_homology_torus_le n k)

/-- **The winding classes `aᵢ` are linearly independent** in `H¹(Tⁿ; ℚ)` for `n ≥ 2`: cupping a
relation `Σ cᵢ aᵢ = 0` on the right with `a_m`, `m ≠ k`, and evaluating on `T_km` returns
`c_k`. -/
theorem linearIndependent_coordWinding {n : ℕ} (hn : 2 ≤ n) :
    LinearIndependent ℚ (coordWinding (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  obtain ⟨m, hm⟩ : ∃ m : Fin n, k ≠ m := by
    by_contra hc
    push Not at hc
    have h0 := hc ⟨0, by omega⟩
    have h1 := hc ⟨1, by omega⟩
    have : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := h0.symm.trans h1
    simp [Fin.ext_iff] at this
  have := congrArg (fun x => torusEval (coordTorus_one_left k m) (coordTorus_one_right k m)
    (cupSingRight (torus n) (coordWinding m) 2 (p := 1) rfl x)) hg
  simp only [map_sum, map_smul, map_zero] at this
  simp only [cupSingRight_apply, torusEval_coordTorus_cup hm, smul_eq_mul] at this
  rw [Finset.sum_eq_single k] at this
  · simpa [hm] using this
  · intro i _ hik
    simp [hik, hm.symm]
  · simp

/-- **The winding classes `aᵢ` span `H¹(Tⁿ; ℚ)`** for `n ≥ 2`. -/
theorem span_coordWinding {n : ℕ} (hn : 2 ≤ n) :
    Submodule.span ℚ (Set.range (coordWinding (n := n))) = ⊤ := by
  have hli := linearIndependent_coordWinding hn
  refine hli.span_eq_top_of_card_eq_finrank' (le_antisymm ?_ ?_)
  · simpa using hli.fintype_card_le_finrank
  · simpa using finrank_cohomology_torus_le n 1

/-- **`dim H¹(Tⁿ; ℚ) = n`** for `n ≥ 2`. -/
theorem finrank_cohomology_one_torus {n : ℕ} (hn : 2 ≤ n) :
    finrank ℚ (Cohomology ℚ (torus n) 1) = n := by
  have hli := linearIndependent_coordWinding hn
  refine le_antisymm (by simpa using finrank_cohomology_torus_le n 1) ?_
  simpa using hli.fintype_card_le_finrank

/-- The number of index pairs `i < j` in `Fin n` is `n.choose 2`. -/
theorem card_coordPairs (n : ℕ) :
    Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2 := by
  rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]

/-- **The products `aᵢ ⌣ aⱼ` with `i < j` span `H²(Tⁿ; ℚ)`**, for every `n`. -/
theorem span_coordCup (n : ℕ) :
    Submodule.span ℚ (Set.range (coordCup (n := n))) = ⊤ := by
  have hli := linearIndependent_coordCup n
  refine hli.span_eq_top_of_card_eq_finrank' (le_antisymm ?_ ?_)
  · exact hli.fintype_card_le_finrank
  · rw [card_coordPairs]; exact finrank_cohomology_torus_le n 2

/-- **`dim H²(Tⁿ; ℚ) = n.choose 2`**, for every `n`. -/
theorem finrank_cohomology_two_torus (n : ℕ) :
    finrank ℚ (Cohomology ℚ (torus n) 2) = n.choose 2 := by
  have hli := linearIndependent_coordCup n
  refine le_antisymm (finrank_cohomology_torus_le n 2) ?_
  rw [← card_coordPairs]
  exact hli.fintype_card_le_finrank

/-- **The basis `a₀, …, a_{n−1}` of `H¹(Tⁿ; ℚ)`**, for `n ≥ 2`. -/
def coordWindingBasis {n : ℕ} (hn : 2 ≤ n) : Basis (Fin n) ℚ (Cohomology ℚ (torus n) 1) :=
  Basis.mk (linearIndependent_coordWinding hn) (span_coordWinding hn).ge

/-- **The basis `aᵢ ⌣ aⱼ`, `i < j`, of `H²(Tⁿ; ℚ)`**, for every `n`. -/
def coordCupBasis (n : ℕ) :
    Basis {p : Fin n × Fin n // p.1 < p.2} ℚ (Cohomology ℚ (torus n) 2) :=
  Basis.mk (linearIndependent_coordCup n) (span_coordCup n).ge

/-- **Test, `n = 2`**: `a₀ ≠ a₁` in `H¹(T²; ℚ)`. -/
theorem coordWinding_zero_ne_one_two : coordWinding (n := 2) 0 ≠ coordWinding 1 :=
  (linearIndependent_coordWinding le_rfl).injective.ne (by decide)

/-- **Test, `n = 2`**: `dim H¹(T²; ℚ) = 2`. -/
theorem finrank_cohomology_one_torus_two : finrank ℚ (Cohomology ℚ (torus 2) 1) = 2 :=
  finrank_cohomology_one_torus le_rfl

/-- **Test, `n = 2`**: `dim H²(T²; ℚ) = 1`. -/
theorem finrank_cohomology_two_torus_two : finrank ℚ (Cohomology ℚ (torus 2) 2) = 1 :=
  finrank_cohomology_two_torus 2

/-- **Test, `n = 4`**: `dim H¹(T⁴; ℚ) = 4`. -/
theorem finrank_cohomology_one_torus_four : finrank ℚ (Cohomology ℚ (torus 4) 1) = 4 :=
  finrank_cohomology_one_torus (by norm_num)

/-- **Test, `n = 4`**: `dim H²(T⁴; ℚ) = 6`. -/
theorem finrank_cohomology_two_torus_four : finrank ℚ (Cohomology ℚ (torus 4) 2) = 6 :=
  finrank_cohomology_two_torus 4

end HodgeLadder.Torus
