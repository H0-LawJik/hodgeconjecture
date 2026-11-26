module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import HodgeLadder.General.Ext
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Rational sheaves and sheaves of abelian groups

Let `Y` be a topological space. Forgetting the `ℚ`-linear structure is an exact functor from
sheaves of `ℚ`-vector spaces on `Y` to sheaves of abelian groups, with an exact left adjoint
`ℚ ⊗ −`. Part of rung `rational-ext-equiv` (front `cup`, decision 0008).

## Main results

* `HodgeLadder.Cup.forgetSheaf_preservesFiniteColimits`
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace HodgeLadder.Cup

variable (Y : TopCat.{0})

/-- The site of opens of `Y`. -/
abbrev J := Opens.grothendieckTopology Y

/-- Forgetting the rational structure. -/
abbrev U : ModuleCat.{0} ℚ ⥤ AddCommGrpCat.{0} := forget₂ (ModuleCat ℚ) AddCommGrpCat

/-- Forgetting the rational structure of sheaves. -/
abbrev forgetSheaf : Sheaf (J Y) (ModuleCat.{0} ℚ) ⥤ Sheaf (J Y) AddCommGrpCat.{0} :=
  sheafCompose (J Y) U

/-- `ℤ`-modules are abelian groups. -/
abbrev intEquiv : ModuleCat.{0} ℤ ≌ AddCommGrpCat.{0} :=
  (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).asEquivalence

/-- `ℚ ⊗ −` on abelian groups. -/
abbrev tensorQ : AddCommGrpCat.{0} ⥤ ModuleCat.{0} ℚ :=
  intEquiv.inverse ⋙ ModuleCat.extendScalars (Int.castRingHom ℚ)

/-- Restriction of scalars to `ℤ` followed by the identification with abelian groups is the
forgetful functor. -/
def restrictIso : ModuleCat.restrictScalars (Int.castRingHom ℚ) ⋙ intEquiv.functor ≅ U :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- `ℚ ⊗ −` is left adjoint to forgetting the rational structure. -/
def adjQ : tensorQ ⊣ U :=
  (intEquiv.symm.toAdjunction.comp (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℚ))).ofNatIsoRight
    restrictIso

instance : U.IsRightAdjoint := ⟨_, ⟨adjQ⟩⟩

instance : PreservesFiniteLimits (forgetSheaf Y) := inferInstance

/-- Forgetting the rational structure preserves epimorphisms of sheaves: epimorphisms are the
locally surjective maps, and forgetting does not change the underlying functions. -/
instance forgetSheaf_preservesEpi : (forgetSheaf Y).PreservesEpimorphisms where
  preserves {F G} φ hφ := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hφ ⊢
    change Presheaf.IsLocallySurjective (J Y) φ.hom at hφ
    change Presheaf.IsLocallySurjective (J Y) (Functor.whiskerRight φ.hom U)
    rw [Presheaf.isLocallySurjective_iff_whisker_forget] at hφ ⊢
    exact hφ

instance forgetSheaf_additive : (forgetSheaf Y).Additive where
  map_add {F G f g} := by
    apply Sheaf.hom_ext
    ext W x
    rfl

/-- **Forgetting the rational structure of sheaves is exact.** -/
instance forgetSheaf_preservesFiniteColimits : PreservesFiniteColimits (forgetSheaf Y) := by
  have h := (Functor.exact_tfae (forgetSheaf Y)).out 1 4
  refine (h.mp fun S hS => ?_).2
  have := hS.mono_f
  have := hS.epi_g
  have hk : IsLimit (KernelFork.ofι _ ((S.map (forgetSheaf Y)).zero)) :=
    isLimitForkMapOfIsLimit' (forgetSheaf Y) S.zero hS.fIsKernel
  exact { exact := ShortComplex.exact_of_f_is_kernel _ hk
          mono_f := (forgetSheaf Y).map_mono S.f
          epi_g := (forgetSheaf Y).map_epi S.g }

/-- `ℚ ⊗ −` is left exact, since `ℚ` is flat over `ℤ`. -/
instance tensorQ_preservesFiniteLimits : PreservesFiniteLimits tensorQ := by
  have hf : (Int.castRingHom ℚ).Flat := by
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact comp_preservesFiniteLimits _ _

/-- The sheafified `ℚ ⊗ −`. -/
abbrev tensorQSheaf : Sheaf (J Y) AddCommGrpCat.{0} ⥤ Sheaf (J Y) (ModuleCat.{0} ℚ) :=
  Sheaf.composeAndSheafify (J Y) tensorQ

/-- The adjunction between sheafified `ℚ ⊗ −` and forgetting the rational structure. -/
def adjQSheaf : tensorQSheaf Y ⊣ forgetSheaf Y := Sheaf.adjunction (J Y) adjQ

instance : PreservesFiniteLimits
    ((Functor.whiskeringRight (TopologicalSpace.Opens Y)ᵒᵖ AddCommGrpCat.{0}
      (ModuleCat.{0} ℚ)).obj tensorQ) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- **Sheafified `ℚ ⊗ −` is exact.** -/
instance tensorQSheaf_preservesFiniteLimits : PreservesFiniteLimits (tensorQSheaf Y) := by
  unfold tensorQSheaf Sheaf.composeAndSheafify
  infer_instance

instance : (tensorQSheaf Y).IsLeftAdjoint := ⟨_, ⟨adjQSheaf Y⟩⟩

instance tensorQSheaf_additive : (tensorQSheaf Y).Additive :=
  Functor.additive_of_preserves_binary_products _

set_option maxHeartbeats 400000 in
/-- Forgetting the rational structure commutes with sheafification. -/
instance preservesSheafification_U : (J Y).PreservesSheafification U :=
  GrothendieckTopology.instPreservesSheafification (J := J Y) U

/-- The extension groups of the rational adjunction. -/
def extEquivQ (A : Sheaf (J Y) AddCommGrpCat.{0}) (M : Sheaf (J Y) (ModuleCat.{0} ℚ)) (n : ℕ) :
    Abelian.Ext.{0} ((tensorQSheaf Y).obj A) M n ≃+ Abelian.Ext.{0} A ((forgetSheaf Y).obj M) n :=
  (adjQSheaf Y).extEquiv

/-- Precomposition with an isomorphism, on extension groups: the universe-`0` case of
`HodgeLadder.Ext.precompIsoAddEquiv`. -/
def extPrecompEquiv {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasExt.{0} 𝒞] {A B Z : 𝒞}
    (e : A ≅ B) (n : ℕ) : Abelian.Ext.{0} B Z n ≃+ Abelian.Ext.{0} A Z n :=
  HodgeLadder.Ext.precompIsoAddEquiv e Z n

/-- Postcomposition with an isomorphism, on extension groups: the universe-`0` case of
`HodgeLadder.Ext.postcompIsoAddEquiv`. -/
def extPostcompEquiv {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasExt.{0} 𝒞] {A Z Z' : 𝒞}
    (e : Z ≅ Z') (n : ℕ) : Abelian.Ext.{0} A Z n ≃+ Abelian.Ext.{0} A Z' n :=
  HodgeLadder.Ext.postcompIsoAddEquiv e A n

/-- The constant sheaf of `ℚ`-vector spaces with value `ℚ`. -/
abbrev QX : Sheaf (J Y) (ModuleCat.{0} ℚ) :=
  (constantSheaf (J Y) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- The constant sheaf of abelian groups with value `A`. -/
abbrev constAb (A : AddCommGrpCat.{0}) : Sheaf (J Y) AddCommGrpCat.{0} :=
  (constantSheaf (J Y) AddCommGrpCat.{0}).obj A

/-- Forgetting the rational structure of `ℚ_Y` gives the constant sheaf `ℚ` of abelian groups. -/
def forgetQX : (forgetSheaf Y).obj (QX Y) ≅ constAb Y (AddCommGrpCat.of ℚ) :=
  (constantCommuteCompose (J Y) U).app (ModuleCat.of ℚ ℚ)

/-- Sections over the whole space commute with forgetting the rational structure. -/
def sectionsForgetIso :
    forgetSheaf Y ⋙ (sheafSections (J Y) AddCommGrpCat.{0}).obj (Opposite.op ⊤) ≅
      (sheafSections (J Y) (ModuleCat.{0} ℚ)).obj (Opposite.op ⊤) ⋙ U :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Sheafified `ℚ ⊗ −` commutes with constant sheaves: both composites are left adjoint to taking
global sections and forgetting the rational structure. -/
def tensorQConstIso :
    constantSheaf (J Y) AddCommGrpCat.{0} ⋙ tensorQSheaf Y ≅
      tensorQ ⋙ constantSheaf (J Y) (ModuleCat.{0} ℚ) :=
  ((constantSheafAdj (J Y) AddCommGrpCat.{0} isTerminalTop).comp (adjQSheaf Y)).leftAdjointUniq
    ((adjQ.comp (constantSheafAdj (J Y) (ModuleCat.{0} ℚ) isTerminalTop)).ofNatIsoRight
      (sectionsForgetIso Y).symm)

/-- A `ℚ`-linear equivalence `ℚ ⊗_ℤ M ≅ ℚ` from a `ℤ`-linear equivalence `M ≅ ℤ`. -/
def extendScalarsEquivSelf (M : ModuleCat.{0} ℤ) (e : M ≃ₗ[ℤ] ℤ) :
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).obj M ≃ₗ[ℚ] ℚ := by
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ) e).trans
    (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ)

/-- `ℚ ⊗ ℤ ≅ ℚ`. -/
def tensorQInt : tensorQ.obj (AddCommGrpCat.of (ULift.{0} ℤ)) ≅ ModuleCat.of ℚ ℚ :=
  let M := intEquiv.inverse.obj (AddCommGrpCat.of (ULift.{0} ℤ))
  let c : intEquiv.functor.obj M ≅ AddCommGrpCat.of (ULift.{0} ℤ) :=
    intEquiv.counitIso.app _
  let eZ : M ≃ₗ[ℤ] ℤ :=
    (c.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift).toIntLinearEquiv
  (extendScalarsEquivSelf M eZ).toModuleIso

/-- Sheafified `ℚ ⊗ −` sends the constant sheaf `ℤ` to the constant sheaf `ℚ`. -/
def tensorQSheafInt : (tensorQSheaf Y).obj (constAb Y (AddCommGrpCat.of (ULift.{0} ℤ))) ≅ QX Y :=
  (tensorQConstIso Y).app _ ≪≫ (constantSheaf (J Y) (ModuleCat.{0} ℚ)).mapIso tensorQInt

/-- **Rational cohomology is `Ext` of the constant sheaf `ℚ` in sheaves of `ℚ`-vector spaces.**
`Hⁿ(Y; ℚ) = Extⁿ(ℤ_Y, ℚ_Y)` in sheaves of abelian groups is identified with `Extⁿ(ℚ_Y, ℚ_Y)` in
sheaves of `ℚ`-vector spaces, through the exact adjunction `ℚ ⊗ − ⊣ forget`. -/
def rationalExtEquiv (n : ℕ) :
    Sheaf.H.{0} (constAb Y (AddCommGrpCat.of ℚ)) n ≃+ Abelian.Ext.{0} (QX Y) (QX Y) n :=
  (extPostcompEquiv (forgetQX Y).symm n).trans
    ((extEquivQ Y (constAb Y (AddCommGrpCat.of (ULift.{0} ℤ))) (QX Y) n).symm.trans
      (extPrecompEquiv (tensorQSheafInt Y).symm n))

/-- The unit class of `Ext⁰(ℚ_Y, ℚ_Y)`. -/
def oneExt : Abelian.Ext.{0} (QX Y) (QX Y) 0 := Abelian.Ext.mk₀ (𝟙 (QX Y))

lemma oneExt_comp {n : ℕ} (x : Abelian.Ext.{0} (QX Y) (QX Y) n) :
    (oneExt Y).comp x (zero_add n) = x := Abelian.Ext.mk₀_id_comp x

lemma comp_oneExt {n : ℕ} (x : Abelian.Ext.{0} (QX Y) (QX Y) n) :
    x.comp (oneExt Y) (add_zero n) = x := Abelian.Ext.comp_mk₀_id x

end HodgeLadder.Cup
