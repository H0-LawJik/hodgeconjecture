module

public import HodgeLadder.Cup.TriadCup
public import HodgeLadder.Cup.WindingTorus

/-!
# Non-vacuity of the triad relative cup on the torus

Test for rung `triad-relative-cup` (red team 2026-11-26, section 2): with `A = B = ∅`, the
product `relCup2` of lifts of the two winding classes of a torus map, forgotten to `H²(Y)` and
evaluated on the torus cycle, is `1`. Swapping the factors gives `−1`
(`torusEval_cupSing_winding_swap`), so the test sees the factor order; it does not see the
relative information on nonempty `A, B` (rung `local-class-cross-model` does).

## Main results

* `HodgeLadder.Tests.torusEval_relCup2_winding`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology.Singular ChernWinding HodgeLadder.Cup

namespace HodgeLadder.Tests

variable {Y : TopCat.{0}} {T : C(ℝ × ℝ, Y)} (hT₁ : ∀ t, T (1, t) = T (0, t))
  (hT₂ : ∀ s, T (s, 1) = T (s, 0)) (g₁ g₂ : C(Y, ℂ)) (hg₁ : ∀ y, g₁ y ≠ 0) (hg₂ : ∀ y, g₂ y ≠ 0)
  (h₁ : ∀ p, g₁ (T p) = Complex.exp (ChernWinding.twoPiI * (p.1 : ℂ)))
  (h₂ : ∀ p, g₂ (T p) = Complex.exp (ChernWinding.twoPiI * (p.2 : ℂ)))

include h₁ h₂ in
/-- **Non-vacuity and factor order of `relCup2`** with `A = B = ∅`: for lifts `a₁, a₂` to
`H¹(Y, ∅)` of the winding classes of `g₁, g₂` (they exist by `forgetRel_empty_bijective`),
`⟨forgetRel (relCup2 a₁ a₂), T⟩ = 1`. -/
theorem torusEval_relCup2_winding
    (a₁ a₂ : RelativeCohomology ℚ (TopPair.ofSubset (∅ : Set Y)) 1)
    (ha₁ : forgetRel _ 1 a₁ = windingClass g₁ hg₁) (ha₂ : forgetRel _ 1 a₂ = windingClass g₂ hg₂) :
    torusEval hT₁ hT₂ (forgetRel (TopPair.ofSubset ((∅ : Set Y) ∪ ∅)) 2
      (relCup2 Y ∅ ∅ isOpen_empty isOpen_empty a₁ a₂ 2 rfl)) = 1 := by
  rw [forgetRel_relCup2, ha₁, ha₂]
  exact torusEval_cupSing_winding hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂

end HodgeLadder.Tests
