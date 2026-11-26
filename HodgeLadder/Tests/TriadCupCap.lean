module

public import HodgeLadder.Cup.TriadCupCap
public import HodgeLadder.Tests.TriadCupTorus

/-!
# Non-vacuity of the triad cup–cap adjunction

Test for rung `triad-relative-cup-cap` (red team `docs/sketches/triad-relative-cup-cap.redteam.md`,
section 7b, Appendix C): with `A = B = ∅` and `p = q = 1`, the product `relCup2` of lifts of the two
winding classes of a torus map pairs nonzero with some class `z`, so both sides of
`HodgeLadder.Cup.relCup2_eval_eq_eval_triadCap` are nonzero there. The test is built from the
checked torus value `torusEval_relCup2_winding` (value 1) and the injectivity of upstream's
`relativeCohomologyEquivDualHomology`. It does not see nonempty `A, B`; the sign-visible test with
both subspaces nonempty is rung `local-class-cross-model` at `a = b = 1`.

## Main results

* `HodgeLadder.Tests.exists_eval_relCup2_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology.Singular ChernWinding HodgeLadder.Cup

namespace HodgeLadder.Tests

variable {Y : TopCat.{0}} {T : C(ℝ × ℝ, Y)} (hT₁ : ∀ t, T (1, t) = T (0, t))
  (hT₂ : ∀ s, T (s, 1) = T (s, 0)) (g₁ g₂ : C(Y, ℂ)) (hg₁ : ∀ y, g₁ y ≠ 0) (hg₂ : ∀ y, g₂ y ≠ 0)
  (h₁ : ∀ p, g₁ (T p) = Complex.exp (ChernWinding.twoPiI * (p.1 : ℂ)))
  (h₂ : ∀ p, g₂ (T p) = Complex.exp (ChernWinding.twoPiI * (p.2 : ℂ)))

include hT₁ hT₂ h₁ h₂ in
/-- **Non-vacuity of the adjunction** (`A = B = ∅`, `p = q = 1`): some `z` pairs nonzero with
`relCup2 a₁ a₂`, so both sides of `relCup2_eval_eq_eval_triadCap` are nonzero there. -/
theorem exists_eval_relCup2_ne_zero
    (a₁ a₂ : RelativeCohomology ℚ (TopPair.ofSubset (∅ : Set Y)) 1)
    (ha₁ : forgetRel _ 1 a₁ = windingClass g₁ hg₁) (ha₂ : forgetRel _ 1 a₂ = windingClass g₂ hg₂) :
    ∃ z, relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset ((∅ : Set Y) ∪ ∅)) (1 + 1)
      (relCup2 Y ∅ ∅ isOpen_empty isOpen_empty a₁ a₂ (1 + 1) rfl) z ≠ 0 := by
  by_contra hz
  push Not at hz
  have h0 : relCup2 Y ∅ ∅ isOpen_empty isOpen_empty a₁ a₂ (1 + 1) rfl = 0 :=
    (relativeCohomologyEquivDualHomology ℚ _ _).injective (by ext z; simpa using hz z)
  have h1 := torusEval_relCup2_winding hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂ a₁ a₂ ha₁ ha₂
  rw [h0, map_zero] at h1
  erw [map_zero] at h1
  exact zero_ne_one h1

end HodgeLadder.Tests
