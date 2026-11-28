module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# Shifted homs into a distinguished triangle

Exactness of `Hom(I, -)` along a distinguished triangle, read on `ShiftedHom I _ n` in an
arbitrary integer degree, the form in which upstream's `Hypercohomology` appears under
`SmallShiftedHom.equiv`.

## Main results

* `CategoryTheory.Pretriangulated.Triangle.shifted_coyoneda_injective₁`: for a distinguished
  triangle, if `Hom(I, T₂[n₀]) → Hom(I, T₃[n₀])` is onto, then `Hom(I, T₁[n₀ + 1]) →
  Hom(I, T₂[n₀ + 1])` has zero kernel.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated.Triangle

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- Exactness at the first object of a distinguished triangle, with the connecting map killed:
if every `γ : I → T₃[n₀]` factors through `T.mor₂`, then a map `β : I → T₁[n₁]` with
`n₀ + 1 = n₁` and `β ≫ T.mor₁[n₁] = 0` is zero. -/
lemma shifted_coyoneda_injective₁ (T : Triangle C) (hT : T ∈ distTriang C)
    (I : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (hsurj : ∀ γ : ShiftedHom I T.obj₃ n₀, ∃ α : ShiftedHom I T.obj₂ n₀,
      α.comp (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₂) (zero_add n₀) = γ)
    (β : ShiftedHom I T.obj₁ n₁)
    (hβ : β.comp (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₁) (zero_add n₁) = 0) :
    β = 0 := by
  let F := preadditiveCoyoneda.obj (Opposite.op I)
  have hexact := F.homologySequence_exact₁ T hT n₀ n₁ h
  rw [ShortComplex.ab_exact_iff] at hexact
  have hkernel : ((F.shift n₁).map T.mor₁) β = 0 := by
    change β ≫ T.mor₁⟦n₁⟧' = 0
    simpa only [ShiftedHom.comp_mk₀] using hβ
  obtain ⟨γ, hγ⟩ := hexact β hkernel
  obtain ⟨α, hα⟩ := hsurj γ
  have hα' : ((F.shift n₀).map T.mor₂) α = γ := by
    change α ≫ T.mor₂⟦n₀⟧' = γ
    simpa only [ShiftedHom.comp_mk₀] using hα
  rw [← hγ, ← hα']
  change ((F.shift n₀).map T.mor₂ ≫ F.homologySequenceδ T n₀ n₁ h) α = 0
  rw [F.comp_homologySequenceδ T hT n₀ n₁ h]
  rfl

end CategoryTheory.Pretriangulated.Triangle
