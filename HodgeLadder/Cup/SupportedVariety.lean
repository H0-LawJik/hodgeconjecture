module

public import HodgeLadder.Cup.Supported
public import HodgeLadder.Cup.Product
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport

/-!
# Supported classes times absolute classes on a complex variety

Rung `supported-cup`. For `X` over `Spec ℂ` and `Z ⊆ X(ℂ)` closed, `α ∪ β ∈ H_[Z]ⁿ(X; ℚ)` for
`α ∈ H_[Z]ᵖ(X; ℚ)` and `β ∈ H^q(X; ℚ)`. Forgetting the support commutes with the product, and the
unit acts trivially.

## Main results

* `HodgeLadder.Cup.forgetSupport_supCup`, `HodgeLadder.Cup.supCup_assoc`,
  `HodgeLadder.Cup.supCup_one`, `add_supCup`, `supCup_add`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLadder.Cup

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable {X : Over (Spec ↧ℂ)} {Z : Closeds (ComplexPoint X)}

/-- **The product** `H_[Z]ᵖ(X; ℚ) × H^q(X; ℚ) → H_[Z]ⁿ(X; ℚ)`. -/
def supCup {p q : ℕ} (α : H_[Z]^p(X; ℚ)) (β : H^q(X; ℚ)) (n : ℕ) (h : p + q = n) :
    H_[Z]^n(X; ℚ) :=
  supCupY (Y := TopCat.of (ComplexPoint X)) α β n h

/-- **Forgetting the support commutes with the product.** -/
theorem forgetSupport_supCup {p q : ℕ} (α : H_[Z]^p(X; ℚ)) (β : H^q(X; ℚ)) (n : ℕ)
    (h : p + q = n) :
    forgetSupport ℚ X Z n (supCup α β n h) = cup (forgetSupport ℚ X Z p α) β n h := by
  unfold supCup cup
  rw [← supCupY_eq_cupY]
  change (Abelian.Ext.mk₀ _).comp ((Abelian.Ext.mk₀ _).comp (supCupY α β n h) (zero_add n))
      (zero_add n) =
    supCupY ((Abelian.Ext.mk₀ _).comp ((Abelian.Ext.mk₀ _).comp α (zero_add p)) (zero_add p))
      β n h
  rw [comp_supCupY₀, comp_supCupY₀]

/-- Associativity with the cup product. -/
theorem supCup_assoc {p q r : ℕ} (α : H_[Z]^p(X; ℚ)) (β : H^q(X; ℚ)) (γ : H^r(X; ℚ)) (n : ℕ)
    (h : p + q + r = n) :
    supCup (supCup α β (p + q) rfl) γ n h = supCup α (cup β γ (q + r) rfl) n (by omega) :=
  supCupY_assoc (Y := TopCat.of (ComplexPoint X)) α β γ n h

/-- The unit acts trivially on supported classes. -/
theorem supCup_one {p : ℕ} (α : H_[Z]^p(X; ℚ)) : supCup α (one X) p (add_zero p) = α :=
  supCupY_oneY (Y := TopCat.of (ComplexPoint X)) α

/-- The product is additive in the supported class. -/
theorem add_supCup {p q : ℕ} (α α' : H_[Z]^p(X; ℚ)) (β : H^q(X; ℚ)) (n : ℕ) (h : p + q = n) :
    supCup (α + α') β n h = supCup α β n h + supCup α' β n h :=
  add_supCupY (Y := TopCat.of (ComplexPoint X)) α α' β n h

/-- The product is additive in the absolute class. -/
theorem supCup_add {p q : ℕ} (α : H_[Z]^p(X; ℚ)) (β β' : H^q(X; ℚ)) (n : ℕ) (h : p + q = n) :
    supCup α (β + β') n h = supCup α β n h + supCup α β' n h :=
  supCupY_add (Y := TopCat.of (ComplexPoint X)) α β β' n h

end HodgeLadder.Cup
