module

public import HodgeLadder.Line.MiddleSheaf
public import LefschetzPort.AlgebraicGeometry.HolomorphicUnitExtension
import HodgeConjecture.Mathlib.Topology.Sheaves.StalkExact

/-!
# The unit extension of a holomorphic line bundle

The middle sheaf of a holomorphic trivializing cover `σ` sits in a short exact sequence
`0 → 𝒪ˣ → N → ℤ → 0`, with `ℤ` the upstream constant sheaf. This is the holomorphic unit
extension attached to `σ`. Part of rung `unit-extension-of-invertible` (step B2).

## Main definitions

* `HodgeLadder.TCover.unitExtension`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry ComplexPoint

namespace HodgeLadder

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance unitExtensionTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable {M : SheafOfModules (holomorphicRingSheaf X d)} (T : HolomorphicTrivializingCover M)

namespace TCover

instance inclusion_mono : Mono (inclusion T) := by
  have h : ∀ U, Mono ((inclusion T).hom.app U) := fun U => by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b h
    exact inclSection_injective _ (congrArg Subtype.val h)
  have : Mono (inclusion T).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ (inclusion T)

instance projection_epi : Epi (projection T) :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp (projection_isLocallySurjective T)

/-- The extension short complex. -/
abbrev extComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) :=
  ShortComplex.mk (inclusion T) (projection T ≫ (constIsoLC (TopCat.of (ComplexPoint X))).inv)
    (by rw [← Category.assoc, inclusion_projection, zero_comp])

lemma extComplex_exact : (extComplex T).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.map_comp]
  apply TopCat.Presheaf.stalkExact_of_locallyPrimitive
  intro y U hy s hs
  have hs' : (projection T).hom.app (op U) s = 0 := by
    let e := ((TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoint X))).mapIso
      (constIsoLC (TopCat.of (ComplexPoint X)))).app (op U)
    have h2 : e.inv ((projection T).hom.app (op U) s) = 0 := hs
    have h3 := ConcreteCategory.congr_hom e.inv_hom_id ((projection T).hom.app (op U) s)
    erw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply, h2, map_zero] at h3
    exact h3.symm
  have hdeg : ∀ z : U, (s.1 z).1 = 0 := fun z => congrFun (congrArg Subtype.val hs') z
  obtain ⟨a, ha⟩ := exists_incl_of_degree_eq_zero T s hdeg
  refine ⟨U, hy, 𝟙 U, a, ?_⟩
  apply Subtype.ext
  exact ha

lemma extComplex_shortExact : (extComplex T).ShortExact where
  exact := extComplex_exact T
  mono_f := inclusion_mono T
  epi_g := epi_comp _ _

/-- **The holomorphic unit extension of a trivializing cover.** -/
def unitExtension : HolomorphicUnitExtension X d where
  middle := middleSheaf T
  inclusion := inclusion T
  projection := projection T ≫ (constIsoLC (TopCat.of (ComplexPoint X))).inv
  zero := (extComplex T).zero
  shortExact := extComplex_shortExact T

end TCover

end HodgeLadder
