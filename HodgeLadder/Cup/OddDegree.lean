module

public import HodgeLadder.Cup.CupSingular
public import HodgeLadder.Cup.WindingTorus

/-!
# An odd-degree cup product on a variety with a torus of units

Rung `cup-odd-degree-transfer` (front `cup`, sub-rung of `cup-odd-degree-test`). Let `X` satisfy
the four hypotheses of `cup_singular_comparison` and suppose its analytification carries two
nowhere vanishing continuous functions `g₁ g₂` and a continuous map `T : ℝ × ℝ → X(ℂ)` of period
`1` in each variable with `g₁ (T (s, t)) = exp (2πi s)` and `g₂ (T (s, t)) = exp (2πi t)`. Pull
the singular winding classes back along upstream's equivalence `Ψ` to sheaf classes
`x₁ x₂ ∈ H¹(X; ℚ)`. Then, on the torus cycle,

  `⟨Ψ (x₁ ∪ x₂), T⟩ = −1` and `⟨Ψ (x₂ ∪ x₁), T⟩ = 1`.

So `x₁ ∪ x₂ ≠ 0` and `x₁ ∪ x₂ ≠ x₂ ∪ x₁`. The value `−1` is where the sign of
`cup_singular_comparison` enters: `Ψ (x ∪ y) = (−1)^{pq} · cupSing (Ψ x) (Ψ y)` with `p = q = 1`,
and `⟨cupSing (Ψ x₁) (Ψ x₂), T⟩ = 1` (`torusEval_cupSing_winding`). With the sign `+1` in place of
`(−1)^{pq}` the first value would be `1`. Conventions: rows "Cup product", "Sheaf–singular
comparison Ψ" and "Singular cup product" of `docs/conventions.md`.

The hypotheses on `X` are statements on upstream's and Mathlib's definitions; rung
`cup-odd-degree-gm2` discharges them for the algebraic torus `𝔾ₘ²`.

## Main definitions

* `HodgeLadder.Cup.sheafWindingClass`

## Main results

* `HodgeLadder.Cup.torusEval_cup_sheafWinding`, `HodgeLadder.Cup.torusEval_cup_sheafWinding_swap`,
  `HodgeLadder.Cup.cup_sheafWinding_ne_zero`, `HodgeLadder.Cup.cup_sheafWinding_swap_ne`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint ChernWinding

namespace HodgeLadder.Cup

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U]

/-- The sheaf class in `H¹(X; ℚ)` whose image under `Ψ` is the winding class of `g`. -/
def sheafWindingClass (g : C(ComplexPoint X, ℂ)) (hg : ∀ y, g y ≠ 0) : H^1(X; ℚ) :=
  (rationalCohomologyAddEquivSingularCohomology X 1).symm
    (windingClass (Y := TopCat.of (ComplexPoint X)) g hg)

variable {X} {T : C(ℝ × ℝ, ComplexPoint X)}
  (hT₁ : ∀ t, T (1, t) = T (0, t)) (hT₂ : ∀ s, T (s, 1) = T (s, 0))
  (g₁ g₂ : C(ComplexPoint X, ℂ)) (hg₁ : ∀ y, g₁ y ≠ 0) (hg₂ : ∀ y, g₂ y ≠ 0)
  (h₁ : ∀ p, g₁ (T p) = Complex.exp (twoPiI * (p.1 : ℂ)))
  (h₂ : ∀ p, g₂ (T p) = Complex.exp (twoPiI * (p.2 : ℂ)))

include h₁ h₂ in
/-- **`⟨Ψ (x₁ ∪ x₂), T⟩ = −1`**: the sign `(−1)^{1·1}` of the comparison, on a computed
instance. -/
theorem torusEval_cup_sheafWinding :
    torusEval (Y := TopCat.of (ComplexPoint X)) hT₁ hT₂
      (rationalCohomologyAddEquivSingularCohomology X 2
        (cup (sheafWindingClass X g₁ hg₁) (sheafWindingClass X g₂ hg₂) 2 rfl)) = -1 := by
  rw [cup_singular_comparison_swap X (sheafWindingClass X g₁ hg₁) (sheafWindingClass X g₂ hg₂)
    (show 1 + 1 = 2 from rfl)]
  simp only [sheafWindingClass, AddEquiv.apply_symm_apply]
  exact torusEval_cupSing_winding_swap (Y := TopCat.of (ComplexPoint X)) hT₁ hT₂ g₁ g₂ hg₁ hg₂
    h₁ h₂

include h₁ h₂ in
/-- **`⟨Ψ (x₂ ∪ x₁), T⟩ = 1`.** -/
theorem torusEval_cup_sheafWinding_swap :
    torusEval (Y := TopCat.of (ComplexPoint X)) hT₁ hT₂
      (rationalCohomologyAddEquivSingularCohomology X 2
        (cup (sheafWindingClass X g₂ hg₂) (sheafWindingClass X g₁ hg₁) 2 rfl)) = 1 := by
  rw [cup_singular_comparison_swap X (sheafWindingClass X g₂ hg₂) (sheafWindingClass X g₁ hg₁)
    (show 1 + 1 = 2 from rfl)]
  simp only [sheafWindingClass, AddEquiv.apply_symm_apply]
  exact torusEval_cupSing_winding (Y := TopCat.of (ComplexPoint X)) hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂

include hT₁ hT₂ h₁ h₂ in
/-- **A nonzero product of two classes in `H¹(X; ℚ)`.** -/
theorem cup_sheafWinding_ne_zero :
    cup (sheafWindingClass X g₁ hg₁) (sheafWindingClass X g₂ hg₂) 2 rfl ≠ 0 := by
  intro h
  have := torusEval_cup_sheafWinding hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂
  rw [h, map_zero, map_zero] at this
  norm_num at this

include hT₁ hT₂ h₁ h₂ in
/-- **The two orders differ**: `x₂ ∪ x₁ ≠ x₁ ∪ x₂`. -/
theorem cup_sheafWinding_swap_ne :
    cup (sheafWindingClass X g₂ hg₂) (sheafWindingClass X g₁ hg₁) 2 rfl ≠
      cup (sheafWindingClass X g₁ hg₁) (sheafWindingClass X g₂ hg₂) 2 rfl := by
  intro h
  have h1 := torusEval_cup_sheafWinding hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂
  have h2 := torusEval_cup_sheafWinding_swap hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂
  rw [h, h1] at h2
  norm_num at h2

end HodgeLadder.Cup
