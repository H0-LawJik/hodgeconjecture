module

public import Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Classes of Hom-complex cocycles and composition with chain maps

Part of rung `ext-class-right-mult` (front `cup`). For a cocycle `z` of the Hom complex
`Hom(K, L)` of degree `n` and chain maps `g : L ⟶ L'` and `f : K' ⟶ K`, the class of `z`
in the localized shifted homs (Mathlib's `CohomologyClass.toSmallShiftedHom`) is compatible with
composition: postcomposing the cocycle with `g` is composing its class with `g` in degree zero,
and likewise for precomposition with `f`. These are general facts about Mathlib's Hom complex,
candidates for Mathlib.

## Main results

* `HodgeLadder.Cup.toSmallShiftedHom_postcomp`, `HodgeLadder.Cup.toSmallShiftedHom_precomp`
-/

@[expose] public noncomputable section

open CategoryTheory Localization CochainComplex HomComplex

namespace HodgeLadder.Cup

universe w

variable {C : Type*} [Category C] [Abelian C] {K L L' K' : CochainComplex C ℤ} {n : ℤ}

/-- **Postcomposing a cocycle with a chain map composes its class in degree zero.** -/
theorem toSmallShiftedHom_postcomp
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ L L']
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L']
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ L' L']
    (z : Cocycle K L n) (g : L ⟶ L') :
    (CohomologyClass.mk (z.postcomp g)).toSmallShiftedHom =
      (CohomologyClass.mk z).toSmallShiftedHom.comp
        (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl g) (zero_add n) := by
  let := HasDerivedCategory.standard C
  apply (SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  rw [SmallShiftedHom.equiv_comp, CohomologyClass.equiv_toSmallShiftedHom_mk,
    CohomologyClass.equiv_toSmallShiftedHom_mk, SmallShiftedHom.equiv_mk₀,
    Cocycle.equivHomShift_symm_postcomp, ← ShiftedHom.comp_mk₀ _ (0 : ℤ) rfl,
    ShiftedHom.map_comp, ShiftedHom.map_mk₀]

/-- **Precomposing a cocycle with a chain map composes its class in degree zero.** -/
theorem toSmallShiftedHom_precomp
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K' K]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K' L]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ L L]
    (z : Cocycle K L n) (f : K' ⟶ K) :
    (CohomologyClass.mk (z.precomp f)).toSmallShiftedHom =
      (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl f).comp
        (CohomologyClass.mk z).toSmallShiftedHom (add_zero n) := by
  let := HasDerivedCategory.standard C
  apply (SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  rw [SmallShiftedHom.equiv_comp, CohomologyClass.equiv_toSmallShiftedHom_mk,
    CohomologyClass.equiv_toSmallShiftedHom_mk, SmallShiftedHom.equiv_mk₀,
    Cocycle.equivHomShift_symm_precomp, ← ShiftedHom.mk₀_comp (0 : ℤ) rfl,
    ShiftedHom.map_comp, ShiftedHom.map_mk₀]

end HodgeLadder.Cup
