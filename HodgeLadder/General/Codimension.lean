module

public import Other.AlgebraicGeometry.Cycle.Codimension

/-!
# Codimension-one cycles and disjointness of codimensions

Two facts about upstream's group of codimension-`p` cycles
`AlgebraicGeometry.codimensionCycleSubgroup X p` (integral cycles whose points with nonzero
coefficient all have coheight `p`):

* in codimension one it is Mathlib's group of Weil divisors `AlgebraicCycle.weilDivisors X ℤ`;
* cycles of two different codimensions have only the zero cycle in common.

The first ties upstream's definition to Mathlib's; both are sanity checks on the grading of the
cycle group used by the cycle class map.

## Main results

* `HodgeLadder.codimensionCycleSubgroup_one`
* `HodgeLadder.codimensionCycleSubgroup_inf_eq_bot`,
  `HodgeLadder.disjoint_codimensionCycleSubgroup`
-/

@[expose] public section

open AlgebraicGeometry Order

namespace HodgeLadder

universe u

/-- **The codimension-one cycles are the Weil divisors.** -/
theorem codimensionCycleSubgroup_one (X : Scheme.{u}) :
    codimensionCycleSubgroup X 1 = AlgebraicCycle.weilDivisors X ℤ := by
  ext c
  exact ⟨fun h x hx ↦ by simpa using h x hx, fun h x hx ↦ by simpa using h hx⟩

/-- **Cycles of two different codimensions have only the zero cycle in common.** -/
theorem codimensionCycleSubgroup_inf_eq_bot (X : Scheme.{u}) {p q : ℕ} (hpq : p ≠ q) :
    codimensionCycleSubgroup X p ⊓ codimensionCycleSubgroup X q = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  ext x
  by_contra hx
  exact hpq (by exact_mod_cast (hc.1 x hx).symm.trans (hc.2 x hx))

/-- The groups of cycles of two different codimensions are disjoint. -/
theorem disjoint_codimensionCycleSubgroup (X : Scheme.{u}) {p q : ℕ} (hpq : p ≠ q) :
    Disjoint (codimensionCycleSubgroup X p) (codimensionCycleSubgroup X q) :=
  disjoint_iff.2 (codimensionCycleSubgroup_inf_eq_bot X hpq)

end HodgeLadder
