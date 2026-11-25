/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.ShiftedExact
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Port supplement to `Other.Algebra.Homology.ShiftedExact`

Upstream stack part 4/11 (PR #220) adds `Triangle.shifted_coyoneda_exact₁` to an existing upstream
file. The port stages it here, unchanged, so that upstream's file at the pin is not edited.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Pretriangulated.Triangle

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C]
  [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the first object of a distinguished triangle in an arbitrary shifted degree. -/
lemma shifted_coyoneda_exact₁ (T : Triangle C) (hT : T ∈ distTriang C)
    (I : C) (n : ℤ) (α : ShiftedHom I T.obj₁ n)
    (hα : α.comp (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₁)
      (show (0 : ℤ) + n = n by lia) = 0) :
    ∃ β : ShiftedHom I T.obj₃ (n - 1),
      β.comp T.mor₃ (show (1 : ℤ) + (n - 1) = n by lia) = α := by
  let F := preadditiveCoyoneda.obj (Opposite.op I)
  have hexact := F.homologySequence_exact₁ T hT (n - 1) n (by lia)
  rw [ShortComplex.ab_exact_iff] at hexact
  have hkernel : ((F.shift n).map T.mor₁) α = 0 := by
    change α ≫ T.mor₁⟦n⟧' = 0
    simpa only [ShiftedHom.comp_mk₀] using hα
  obtain ⟨β, hβ⟩ := hexact α hkernel
  refine ⟨β, ?_⟩
  change F.homologySequenceδ T (n - 1) n (by lia) β = α at hβ
  rwa [preadditiveCoyoneda_homologySequenceδ_apply] at hβ

end CategoryTheory.Pretriangulated.Triangle
