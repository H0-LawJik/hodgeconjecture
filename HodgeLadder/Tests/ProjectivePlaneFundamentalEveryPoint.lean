module

public import HodgeLadder.General.LocalOrientation
public import HodgeLadder.Tests.ProjectivePlaneFundamentalDegree
public import Other.AlgebraicGeometry.ComplexPoint.SmoothConnected

/-!
# The fundamental class of `ℙ²(ℂ)` restricts to the complex local orientation at every point

Rung `p2-fundamental-class-every-point` (kind test). Let `μ ∈ H₄(ℙ²(ℂ); ℚ)` restrict to upstream's
`complexLocalOrientation projectivePlane 2 [0 : 0 : 1]` (rung `p2-fundamental-class`). Then for
every `y ∈ ℙ²(ℂ)` the image of `μ` in `H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ y; ℚ)` is
`complexLocalOrientation projectivePlane 2 y`, exactly. With the uniqueness of
`existsUnique_restrict_complexLocalOrientation`, exactly one class of `H₄(ℙ²(ℂ); ℚ)` restricts to
the complex local orientation at every point: the literature's definition of the fundamental
class of the complex orientation [`Hatcher2002` §3.3].

The proof is the general point independence of `HodgeLadder.General.LocalOrientation` (germs of
upstream's singular homology sheaf, a locally constant coefficient, connectedness), applied with
`ℙ²(ℂ)` connected by upstream's `ComplexPoint.connectedSpace`.

No sign or normalization enters: the coefficient against the orientation is `1` at every point,
and `complexLocalOrientation_ne_neg` separates the orientation from its negative at every point.
The orientation is upstream's complex local orientation at every point, so the literature reading
inherits row "Complex orientation of ℂ^p" of `docs/conventions.md`; nothing here can detect a
uniform fault in that row. On `ℙ²` this cannot change any sign: `H⁴(ℙ²; ℚ)` is one-dimensional
and the degree is pinned by one value.

## Main results

* `HodgeLadder.Tests.existsUnique_forall_restrict_complexLocalOrientation`: exactly one class of
  `H₄(ℙ²(ℂ); ℚ)` restricts to the complex local orientation at every point.
* `HodgeLadder.Tests.relativeHomologyProjection_eq_complexLocalOrientation_of_planeOrigin`: any
  class restricting to it at `[0 : 0 : 1]` restricts to it at every point.
* `HodgeLadder.Tests.complexLocalOrientation_ne_neg`: sign separation at every point.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology TopologicalSpace AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular


namespace HodgeLadder.Tests

/-- **The rung.** If `μ ∈ H₄(ℙ²(ℂ); ℚ)` restricts to the complex local orientation at
`[0 : 0 : 1]`, then for every `y ∈ ℙ²(ℂ)` its image in `H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ y; ℚ)` is
`complexLocalOrientation projectivePlane 2 y`, exactly. `ℙ²(ℂ)` is connected by upstream's
`ComplexPoint.connectedSpace`. -/
theorem relativeHomologyProjection_eq_complexLocalOrientation_of_planeOrigin
    (μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2))
    (hμ : (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
      complexLocalOrientation projectivePlane 2 planeOriginPoint)
    (y : ComplexPoint projectivePlane) :
    (relativeHomologyProjection ℚ (pointComplementPair y) (2 * 2)).hom μ =
      complexLocalOrientation projectivePlane 2 y := by
  let _ : QuasiSeparatedSpace projectivePlane.left :=
    quasiSeparatedSpace_of_quasiSeparated projectivePlane.hom
  let _ : ConnectedSpace (ComplexPoint projectivePlane) := ComplexPoint.connectedSpace _
  exact HodgeLadder.LocalOrientation.relativeHomologyProjection_eq_complexLocalOrientation_of_eq
    projectivePlane 2 μ planeOriginPoint hμ y

/-- **The fundamental class of ℙ²(ℂ), every point.** Exactly one `μ ∈ H₄(ℙ²(ℂ); ℚ)` restricts to
`complexLocalOrientation projectivePlane 2 y` in `H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ y; ℚ)` for every
`y ∈ ℙ²(ℂ)`: the literature's definition of the fundamental class of the complex orientation.
Existence and uniqueness come from `existsUnique_restrict_complexLocalOrientation` at
`[0 : 0 : 1]`, the other points from
`relativeHomologyProjection_eq_complexLocalOrientation_of_planeOrigin`. -/
theorem existsUnique_forall_restrict_complexLocalOrientation :
    ∃! μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2),
      ∀ y : ComplexPoint projectivePlane,
        (relativeHomologyProjection ℚ (pointComplementPair y) (2 * 2)).hom μ =
          complexLocalOrientation projectivePlane 2 y := by
  obtain ⟨μ, hμ, huniq⟩ := existsUnique_restrict_complexLocalOrientation
  exact ⟨μ, relativeHomologyProjection_eq_complexLocalOrientation_of_planeOrigin μ hμ,
    fun ν hν ↦ huniq ν (hν planeOriginPoint)⟩


/-- The complex local orientation of `ℙ²(ℂ)` at every point is not its negative, so the identity
at every point separates `μ` from `−μ`. -/
theorem complexLocalOrientation_ne_neg (y : ComplexPoint projectivePlane) :
    complexLocalOrientation projectivePlane 2 y ≠
      -complexLocalOrientation projectivePlane 2 y := by
  intro h
  have h0 := localClassOfChart_ne_zero 2 (localChart projectivePlane 2 y) y
    (mem_localChart_source _ 2 y)
  have h2 : (2 : ℚ) • complexLocalOrientation projectivePlane 2 y = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel _
  exact h0 ((smul_eq_zero.mp h2).resolve_left (by norm_num))

end HodgeLadder.Tests
