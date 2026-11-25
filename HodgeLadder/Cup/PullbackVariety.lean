module

public import HodgeLadder.Cup.Pullback
public import HodgeLadder.Cup.Product

/-!
# Pullback of rational cohomology along morphisms of complex schemes

Rung `cup-pullback`. A morphism `g : X' ⟶ X` over `Spec ℂ` is continuous on complex points
(upstream `Point.continuousMap`), so `pullbackH` gives `g^* : Hⁿ(X; ℚ) → Hⁿ(X'; ℚ)`. It is
additive, multiplicative for the cup product, and sends `1` to `1`.

## Main definitions

* `HodgeLadder.Cup.pullbackCoh`

## Main results

* `HodgeLadder.Cup.pullbackCoh_cup`, `pullbackCoh_one`, `pullbackCoh_add`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Cup

variable {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X)

/-- The continuous map of complex points induced by `g`. -/
abbrev pointMap : TopCat.of (ComplexPoint X') ⟶ TopCat.of (ComplexPoint X) :=
  TopCat.ofHom (Point.continuousMap g)

/-- **Pullback** `g^* : Hⁿ(X; ℚ) → Hⁿ(X'; ℚ)`. -/
def pullbackCoh (n : ℕ) (α : H^n(X; ℚ)) : H^n(X'; ℚ) := pullbackH (pointMap g) n α

/-- **Pullback is multiplicative.** -/
theorem pullbackCoh_cup {p q : ℕ} (α : H^p(X; ℚ)) (β : H^q(X; ℚ)) (n : ℕ) (h : p + q = n) :
    pullbackCoh g n (cup α β n h) = cup (pullbackCoh g p α) (pullbackCoh g q β) n h :=
  pullbackH_cupY (pointMap g) α β n h

/-- Pullback sends the unit to the unit. -/
theorem pullbackCoh_one : pullbackCoh g 0 (one X) = one X' := pullbackH_oneY (pointMap g)

/-- Pullback is additive. -/
theorem pullbackCoh_add (n : ℕ) (α β : H^n(X; ℚ)) :
    pullbackCoh g n (α + β) = pullbackCoh g n α + pullbackCoh g n β :=
  pullbackH_add (pointMap g) n α β

end HodgeLadder.Cup
