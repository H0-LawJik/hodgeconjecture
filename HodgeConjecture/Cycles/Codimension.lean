module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Cycles of pure codimension

Mathlib defines `AlgebraicGeometry.AlgebraicCycle X R` (functions `X → R` with locally finite
support, points standing in for their closures) and singles out the Weil divisors as the cycles
supported in coheight one. The Hodge conjecture is a statement about cycles of every codimension,
so this file generalizes that predicate to an arbitrary codimension `p`.

## Main definitions

* `AlgebraicCycle.IsCodim p D`: the cycle `D` is supported on points of coheight `p`.
* `AlgebraicCycle.codimCycles X R p`: the subgroup `Z^p(X)` of such cycles.

## Main results

* `AlgebraicCycle.isWeilDivisor_iff_isCodim_one`: Mathlib's Weil divisors are the `p = 1` case.
* `AlgebraicCycle.codimCycles_one`: and so are the subgroups.

Rational equivalence, Chow groups and the cycle class map are not here yet; see `docs/roadmap.md`.
-/

@[expose] public section

namespace AlgebraicGeometry.AlgebraicCycle

open CategoryTheory

universe u

variable {X : Scheme.{u}} {R : Type*}

section IsCodim

/-- A cycle has pure codimension `p` when every point in its support has coheight `p`.
For `p = 1` this is `IsWeilDivisor`. -/
def IsCodim [Zero R] (p : ℕ∞) (D : AlgebraicCycle X R) : Prop :=
  D.support ⊆ {x | Order.coheight x = p}

theorem isCodim_iff [Zero R] {p : ℕ∞} {D : AlgebraicCycle X R} :
    IsCodim p D ↔ D.support ⊆ {x | Order.coheight x = p} := Iff.rfl

theorem IsCodim.coheight_eq [Zero R] {p : ℕ∞} {D : AlgebraicCycle X R} (hD : IsCodim p D)
    {x : X} (hx : D x ≠ 0) : Order.coheight x = p := hD hx

theorem isCodim_zero [Zero R] (p : ℕ∞) : IsCodim p (0 : AlgebraicCycle X R) :=
  fun _ hx => absurd rfl hx

/-- Mathlib's Weil divisors are exactly the cycles of pure codimension one. -/
theorem isWeilDivisor_iff_isCodim_one [Zero R] {D : AlgebraicCycle X R} :
    IsWeilDivisor D ↔ IsCodim 1 D := Iff.rfl

theorem IsCodim.add [AddMonoid R] {p : ℕ∞} {D E : AlgebraicCycle X R} (hD : IsCodim p D)
    (hE : IsCodim p E) : IsCodim p (D + E) :=
  (Function.support_add _ _).trans (Set.union_subset hD hE)

open Function.locallyFinsuppWithin in
theorem isCodim_single [DecidableEq X] [Zero R] {p : ℕ∞} {x : X} (hx : Order.coheight x = p) (r : R) :
    IsCodim p (single x r) := fun _ _ ↦ by simp_all

/-- A cycle of pure codimension `p` and of pure codimension `q` with `p ≠ q` is zero. -/
theorem IsCodim.eq_zero_of_ne [Zero R] {p q : ℕ∞} (hpq : p ≠ q) {D : AlgebraicCycle X R}
    (hp : IsCodim p D) (hq : IsCodim q D) : D = 0 := by
  ext x
  by_contra hx
  exact hpq ((hp.coheight_eq hx).symm.trans (hq.coheight_eq hx))

end IsCodim

section codimCycles

variable [AddGroup R]

variable (X R) in
/-- The group `Z^p(X)` of cycles of pure codimension `p`, as a subgroup of all cycles. -/
def codimCycles (p : ℕ∞) : AddSubgroup (AlgebraicCycle X R) :=
  Function.locallyFinsuppWithin.supported R Set.univ {x : X | Order.coheight x = p}

@[simp]
theorem mem_codimCycles {p : ℕ∞} {D : AlgebraicCycle X R} :
    D ∈ codimCycles X R p ↔ IsCodim p D := Iff.rfl

/-- `Z^1(X)` is the group of Weil divisors. -/
theorem codimCycles_one : codimCycles X R 1 = weilDivisors X R := rfl

@[simp]
theorem isCodim_neg {p : ℕ∞} {D : AlgebraicCycle X R} : IsCodim p (-D) ↔ IsCodim p D :=
  (codimCycles X R p).neg_mem_iff

theorem IsCodim.neg {p : ℕ∞} {D : AlgebraicCycle X R} (hD : IsCodim p D) : IsCodim p (-D) :=
  (codimCycles X R p).neg_mem hD

theorem IsCodim.sub {p : ℕ∞} {D E : AlgebraicCycle X R} (hD : IsCodim p D) (hE : IsCodim p E) :
    IsCodim p (D - E) := (codimCycles X R p).sub_mem hD hE

/-- Distinct codimensions meet only in the zero cycle. -/
theorem codimCycles_inf_eq_bot {p q : ℕ∞} (hpq : p ≠ q) :
    codimCycles X R p ⊓ codimCycles X R q = ⊥ := by
  rw [eq_bot_iff]
  intro D hD
  exact IsCodim.eq_zero_of_ne hpq hD.1 hD.2

end codimCycles

end AlgebraicGeometry.AlgebraicCycle
