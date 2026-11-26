module

public import LefschetzPort.AlgebraicGeometry.ChernWindingCochain
public import HodgeConjecture.Mathlib.Geometry.Convex.StdSimplex

/-!
# The square model of the torus as two singular simplices

Rung `torus-cycle-pairing` (with `HodgeLadder.Cup.TorusPairing`). For a continuous map
`T : ℝ × ℝ → Y`, this file builds the singular `2`-simplices `T ∘ lower` and `T ∘ upper`, where
`lower` and `upper` are the affine triangles with vertices `(0,0), (1,0), (1,1)` and
`(0,0), (0,1), (1,1)`. If `T` is periodic in both variables with period `1`
(`T (1, t) = T (0, t)` and `T (s, 1) = T (s, 0)`), their faces match as on the square model of the
torus: `δ₀ lower = δ₂ upper` (the two vertical sides), `δ₁ lower = δ₁ upper` (the diagonal) and
`δ₂ lower = δ₀ upper` (the two horizontal sides). The front edge `δ₂ lower` runs from `(0,0)` to
`(1,0)` and the back edge `δ₀ lower` from `(1,0)` to `(1,1)`.

## Main definitions

* `HodgeLadder.Cup.lowerTriangle`, `HodgeLadder.Cup.upperTriangle`,
  `HodgeLadder.Cup.lowerSimplex`, `HodgeLadder.Cup.upperSimplex`,
  `HodgeLadder.Cup.frontEdge`, `HodgeLadder.Cup.backEdge`

## Main results

* `HodgeLadder.Cup.torus_h0`, `HodgeLadder.Cup.torus_h1`, `HodgeLadder.Cup.torus_h2`,
  `HodgeLadder.Cup.lowerTriangle_single`
-/

@[expose] public noncomputable section

open CategoryTheory Simplicial ChernWinding

namespace HodgeLadder.Cup

/-- The barycentric coordinates of the standard simplex are continuous. -/
theorem continuous_weight {n : ℕ} (i : Fin n) :
    Continuous fun t : Convexity.StdSimplex ℝ (Fin n) => t.weights i :=
  (continuous_apply i).comp
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin n)).continuous

/-- The affine triangle with vertices `(0,0)`, `(1,0)`, `(1,1)`. -/
def lowerTriangle : C(Convexity.StdSimplex ℝ (Fin 3), ℝ × ℝ) :=
  ⟨fun t => (t.weights 1 + t.weights 2, t.weights 2),
    ((continuous_weight 1).add (continuous_weight 2)).prodMk (continuous_weight 2)⟩

/-- The affine triangle with vertices `(0,0)`, `(0,1)`, `(1,1)`. -/
def upperTriangle : C(Convexity.StdSimplex ℝ (Fin 3), ℝ × ℝ) :=
  ⟨fun t => (t.weights 2, t.weights 1 + t.weights 2),
    (continuous_weight 2).prodMk ((continuous_weight 1).add (continuous_weight 2))⟩

/-- Barycentric coordinates of a point on a face of the standard `2`-simplex. -/
theorem weights_map_succAbove (i : Fin 3) (t : Convexity.StdSimplex ℝ (Fin 2)) (k : Fin 3) :
    (Convexity.StdSimplex.map i.succAbove t).weights k =
      (if i.succAbove 0 = k then t.weights 0 else 0) +
      (if i.succAbove 1 = k then t.weights 1 else 0) := by
  classical
  rw [Convexity.StdSimplex.weights_map_apply, Finset.sum_filter, Fin.sum_univ_two]

/-- The vertices of `lowerTriangle`. -/
theorem lowerTriangle_single (k : Fin 3) :
    lowerTriangle (Convexity.StdSimplex.single k) =
      ((if k = 0 then 0 else 1 : ℝ), (if k = 2 then 1 else 0 : ℝ)) := by
  fin_cases k <;> simp [lowerTriangle, Convexity.StdSimplex.single]

variable {Y : TopCat.{0}} (T : C(ℝ × ℝ, Y))

/-- The singular simplex `T ∘ lowerTriangle`. -/
def lowerSimplex : (TopCat.toSSet.obj Y) _⦋2⦌ :=
  (Y.toSSetObjEquiv _).symm (T.comp lowerTriangle)

/-- The singular simplex `T ∘ upperTriangle`. -/
def upperSimplex : (TopCat.toSSet.obj Y) _⦋2⦌ :=
  (Y.toSSetObjEquiv _).symm (T.comp upperTriangle)

/-- The faces of `lowerSimplex T` as maps. -/
theorem simplexMap_δ_lower (i : Fin 3) (z : Convexity.StdSimplex ℝ (Fin 2)) :
    simplexMap ((TopCat.toSSet.obj Y).δ i (lowerSimplex T)) z =
      T (lowerTriangle (Convexity.StdSimplex.map i.succAbove z)) := by
  have := TopCat.toSSetObjEquiv_δ_apply (lowerSimplex T) i z
  rw [simplexMap, this, lowerSimplex, Equiv.apply_symm_apply]
  rfl

/-- The faces of `upperSimplex T` as maps. -/
theorem simplexMap_δ_upper (i : Fin 3) (z : Convexity.StdSimplex ℝ (Fin 2)) :
    simplexMap ((TopCat.toSSet.obj Y).δ i (upperSimplex T)) z =
      T (upperTriangle (Convexity.StdSimplex.map i.succAbove z)) := by
  have := TopCat.toSSetObjEquiv_δ_apply (upperSimplex T) i z
  rw [simplexMap, this, upperSimplex, Equiv.apply_symm_apply]
  rfl

/-- Two singular `1`-simplices with the same underlying map are equal. -/
theorem edge_ext {a b : (TopCat.toSSet.obj Y) _⦋1⦌} (h : ∀ z, simplexMap a z = simplexMap b z) :
    a = b :=
  (Y.toSSetObjEquiv _).injective (ContinuousMap.ext h)

/-- The front edge of `lowerSimplex T`, the image of the segment from `(0,0)` to `(1,0)`. -/
abbrev frontEdge : (TopCat.toSSet.obj Y) _⦋1⦌ := (TopCat.toSSet.obj Y).δ 2 (lowerSimplex T)

/-- The back edge of `lowerSimplex T`, the image of the segment from `(1,0)` to `(1,1)`. -/
abbrev backEdge : (TopCat.toSSet.obj Y) _⦋1⦌ := (TopCat.toSSet.obj Y).δ 0 (lowerSimplex T)

/-- The `i`-th face of `lowerTriangle`, as a map from the standard `1`-simplex. -/
def lowerFace (i : Fin 3) : C(Convexity.StdSimplex ℝ (Fin 2), ℝ × ℝ) :=
  lowerTriangle.comp ⟨Convexity.StdSimplex.map i.succAbove, Convexity.StdSimplex.continuous_map ℝ _⟩

/-- The vertices of a face of `lowerTriangle`. -/
theorem lowerFace_single (i : Fin 3) (j : Fin 2) :
    lowerFace i (Convexity.StdSimplex.single j) =
      lowerTriangle (Convexity.StdSimplex.single (i.succAbove j)) := by
  simp only [lowerFace, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Convexity.StdSimplex.map_single]

variable {T}

/-- The vertical sides agree when `T` has period `1` in the first variable. -/
theorem torus_h0 (hT₁ : ∀ t, T (1, t) = T (0, t)) :
    (TopCat.toSSet.obj Y).δ 0 (lowerSimplex T) = (TopCat.toSSet.obj Y).δ 2 (upperSimplex T) := by
  refine edge_ext fun z => ?_
  rw [simplexMap_δ_lower, simplexMap_δ_upper]
  simp only [lowerTriangle, upperTriangle, ContinuousMap.coe_mk, weights_map_succAbove]
  have e00 : (0 : Fin 3).succAbove 0 = 1 := by decide
  have e01 : (0 : Fin 3).succAbove 1 = 2 := by decide
  have e20 : (2 : Fin 3).succAbove 0 = 0 := by decide
  have e21 : (2 : Fin 3).succAbove 1 = 1 := by decide
  simp only [e00, e01, e20, e21]
  simp
  exact hT₁ _

/-- The two diagonals agree. -/
theorem torus_h1 :
    (TopCat.toSSet.obj Y).δ 1 (lowerSimplex T) = (TopCat.toSSet.obj Y).δ 1 (upperSimplex T) := by
  refine edge_ext fun z => ?_
  rw [simplexMap_δ_lower, simplexMap_δ_upper]
  simp only [lowerTriangle, upperTriangle, ContinuousMap.coe_mk, weights_map_succAbove]
  have e10 : (1 : Fin 3).succAbove 0 = 0 := by decide
  have e11 : (1 : Fin 3).succAbove 1 = 2 := by decide
  simp only [e10, e11]
  simp

/-- The horizontal sides agree when `T` has period `1` in the second variable. -/
theorem torus_h2 (hT₂ : ∀ s, T (s, 1) = T (s, 0)) :
    (TopCat.toSSet.obj Y).δ 2 (lowerSimplex T) = (TopCat.toSSet.obj Y).δ 0 (upperSimplex T) := by
  refine edge_ext fun z => ?_
  rw [simplexMap_δ_lower, simplexMap_δ_upper]
  simp only [lowerTriangle, upperTriangle, ContinuousMap.coe_mk, weights_map_succAbove]
  have e00 : (0 : Fin 3).succAbove 0 = 1 := by decide
  have e01 : (0 : Fin 3).succAbove 1 = 2 := by decide
  have e20 : (2 : Fin 3).succAbove 0 = 0 := by decide
  have e21 : (2 : Fin 3).succAbove 1 = 1 := by decide
  simp only [e00, e01, e20, e21]
  simp
  exact (hT₂ _).symm

end HodgeLadder.Cup
