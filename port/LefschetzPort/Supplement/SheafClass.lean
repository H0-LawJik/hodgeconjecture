/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cycle.SheafClass

/-!
# Port supplement to `Other.AlgebraicGeometry.Cycle.SheafClass`

The upstream stack (final part, PR #228) adds these two declarations to a file that exists on
upstream main: the integral and rational cycle-class maps land in `algebraicCycleClassSpan`. The
port stages them here, so that upstream's file at the pin is not edited.

## Main results

* `AlgebraicGeometry.ComplexPoint.sheafCycleClassOnCycles_mem_algebraicCycleClassSpan`
* `AlgebraicGeometry.ComplexPoint.rationalSheafCycleClassOnCycles_mem_algebraicCycleClassSpan`
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

/-- The class of every integral codimension-`p` cycle belongs to the algebraic cycle-class
span. -/
theorem sheafCycleClassOnCycles_mem_algebraicCycleClassSpan
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (p : ℕ) (c : codimensionCycleSubgroup X.left p) :
    sheafCycleClassOnCycles
        { scheme := X.left, structureMap := X.hom } p c ∈
      algebraicCycleClassSpan X p := by
  rw [sheafCycleClassOnCycles_apply]
  apply Submodule.sum_mem
  intro x _
  dsimp only
  split_ifs with hx
  · rw [← Int.cast_smul_eq_zsmul ℚ]
    exact (algebraicCycleClassSpan X p).smul_mem _
        (cycleComponentSheafClass_mem_algebraicCycleClassSpan X p x hx)
  · simp

/-- The rational cycle-class map lands in the algebraic cycle-class span. -/
theorem rationalSheafCycleClassOnCycles_mem_algebraicCycleClassSpan
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (p : ℕ) (D : TensorProduct ℤ ℚ (codimensionCycleSubgroup X.left p)) :
    rationalSheafCycleClassOnCycles
        { scheme := X.left, structureMap := X.hom } p D ∈
      algebraicCycleClassSpan X p := by
  induction D using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul q c =>
      rw [rationalSheafCycleClassOnCycles_tmul]
      exact Submodule.smul_mem _ q
        (sheafCycleClassOnCycles_mem_algebraicCycleClassSpan X p c)
  | add D E hD hE =>
      rw [map_add]
      exact Submodule.add_mem _ hD hE

end AlgebraicGeometry.ComplexPoint
