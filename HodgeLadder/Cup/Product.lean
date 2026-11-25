module

public import HodgeLadder.Cup.RationalExt
public import HodgeLadder.Cup.Yoneda

/-!
# The cup product on rational cohomology

Rung `cup-product` (front `cup`, decision 0008). Through `rationalCohomologyEquivExt`, the cup
product of `α ∈ Hᵖ(X; ℚ)` and `β ∈ H^q(X; ℚ)` is the Yoneda composition of `α` followed by `β` in
`Ext^*(ℚ_X, ℚ_X)` (Mathlib's `Ext.comp`, diagrammatic order); see `docs/conventions.md`, row
"Cup product". The target degree `n` comes with a proof of `p + q = n`, so associativity holds
without casts.

## Main definitions

* `HodgeLadder.Cup.cup`, `HodgeLadder.Cup.one`

## Main results

* `HodgeLadder.Cup.cup_assoc`, `one_cup`, `cup_one`, `add_cup`, `cup_add`,
  `rationalCohomologyEquivExt_cup`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Cup

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable {X : Over (Spec ↧ℂ)}

/-- **The cup product** `α ∪ β ∈ Hⁿ(X; ℚ)` for `α ∈ Hᵖ`, `β ∈ H^q` and `p + q = n`. -/
def cup {p q : ℕ} (α : H^p(X; ℚ)) (β : H^q(X; ℚ)) (n : ℕ) (h : p + q = n) : H^n(X; ℚ) :=
  cupY (Y := ↧(ComplexPoint X)) α β n h

variable (X) in
/-- The unit class in `H⁰(X; ℚ)`. -/
def one : H^0(X; ℚ) := oneY ↧(ComplexPoint X)

/-- Under `rationalCohomologyEquivExt`, the cup product is Yoneda composition. -/
theorem rationalCohomologyEquivExt_cup {p q : ℕ} (α : H^p(X; ℚ)) (β : H^q(X; ℚ)) (n : ℕ)
    (h : p + q = n) :
    rationalCohomologyEquivExt X n (cup α β n h) =
      (rationalCohomologyEquivExt X p α).comp (rationalCohomologyEquivExt X q β) h :=
  rationalExtEquiv_cupY (Y := ↧(ComplexPoint X)) α β n h

/-- **Associativity.** -/
theorem cup_assoc {p q r : ℕ} (α : H^p(X; ℚ)) (β : H^q(X; ℚ)) (γ : H^r(X; ℚ)) (n : ℕ)
    (h : p + q + r = n) :
    cup (cup α β (p + q) rfl) γ n h = cup α (cup β γ (q + r) rfl) n (by omega) :=
  cupY_assoc (Y := ↧(ComplexPoint X)) α β γ n h

/-- **The unit is a left unit.** -/
theorem one_cup {p : ℕ} (α : H^p(X; ℚ)) : cup (one X) α p (zero_add p) = α :=
  oneY_cupY (Y := ↧(ComplexPoint X)) α

/-- **The unit is a right unit.** -/
theorem cup_one {p : ℕ} (α : H^p(X; ℚ)) : cup α (one X) p (add_zero p) = α :=
  cupY_oneY (Y := ↧(ComplexPoint X)) α

/-- The cup product is additive in the first factor. -/
theorem add_cup {p q : ℕ} (α α' : H^p(X; ℚ)) (β : H^q(X; ℚ)) (n : ℕ) (h : p + q = n) :
    cup (α + α') β n h = cup α β n h + cup α' β n h :=
  add_cupY (Y := ↧(ComplexPoint X)) α α' β n h

/-- The cup product is additive in the second factor. -/
theorem cup_add {p q : ℕ} (α : H^p(X; ℚ)) (β β' : H^q(X; ℚ)) (n : ℕ) (h : p + q = n) :
    cup α (β + β') n h = cup α β n h + cup α β' n h :=
  cupY_add (Y := ↧(ComplexPoint X)) α β β' n h

end HodgeLadder.Cup
