module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.AnalyticSheaf
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Global holomorphic functions on a compact X(ℂ) are locally constant

General half of rung `compact-holomorphic-locally-constant` (sub-rung S1 of
`elliptic-curve-holomorphic-form`); the tests on `ℙ¹` are in
`HodgeLadder.Tests.CompactHolomorphicP1`.
Let `X` be a complex scheme smooth of relative dimension `d`, with `X(ℂ)` compact (for example
`X` projective, by upstream's instance `IsProjective.complexPoint_compactSpace`). A global
section of upstream's sheaf of holomorphic functions `holomorphicFunctionSheaf X d` is a function
`⊤ → ℂ` that is `C^ω` in upstream's charts; `X(ℂ)` is a complex manifold by upstream's
`isManifold_omega`, so Mathlib's maximum modulus principle `MDifferentiable.isLocallyConstant`
applies. The section is locally constant, and constant when `X(ℂ)` is preconnected.

The form used downstream (sub-rung S2a) is `holomorphicTopToLocallyConstant`: the ring map from
global holomorphic functions to `LocallyConstant ⊤ ℂ`, the global sections of the ladder's
`locallyConstantSheaf`, with underlying function the section itself. No sign or scalar enters.

## Main definitions

* `HodgeLadder.holomorphicTopSection X d`
* `HodgeLadder.holomorphicTopToLocallyConstant X d`

## Main results

* `HodgeLadder.compactSpace_opens_top`, `HodgeLadder.preconnectedSpace_opens_top`
* `HodgeLadder.isLocallyConstant_contMDiffMap_top`
* `HodgeLadder.isLocallyConstant_holomorphicFunctionSheaf_top`, `..._of_isProjective`
* `HodgeLadder.holomorphicTopToLocallyConstant_apply`, `..._injective`
* `HodgeLadder.exists_eq_const_holomorphicFunctionSheaf_top`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry ComplexPoint
open scoped ContDiff Manifold

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- The open `⊤` of a compact space is a compact space. -/
theorem compactSpace_opens_top {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] :
    CompactSpace (⊤ : Opens Y) :=
  isCompact_iff_compactSpace.mp (by simpa using isCompact_univ)

/-- The open `⊤` of a preconnected space is a preconnected space. -/
theorem preconnectedSpace_opens_top {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] :
    PreconnectedSpace (⊤ : Opens Y) :=
  Subtype.preconnectedSpace (by simpa using isPreconnected_univ)

/-- **Holomorphic functions on a compact `X(ℂ)` are locally constant.** A function `⊤ → ℂ` that
is `C^ω` in upstream's charts on the complex points of a scheme smooth of relative dimension `d`
is locally constant once `X(ℂ)` is compact: Mathlib's `MDifferentiable.isLocallyConstant` on the
complex manifold `X(ℂ)` (upstream's `isManifold_omega`). -/
theorem isLocallyConstant_contMDiffMap_top [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)]
    (f : C^ω⟮𝓘(ℂ, Fin d → ℂ), (⊤ : Opens (ComplexPoint X)); ℂ⟯) :
    IsLocallyConstant f := by
  have : CompactSpace (⊤ : Opens (ComplexPoint X)) := compactSpace_opens_top
  exact (f.contMDiff.mdifferentiable (by simp)).isLocallyConstant

/-- A global section of upstream's sheaf of holomorphic functions, read as the `C^ω` map
`⊤ → ℂ` it is by definition. -/
abbrev holomorphicTopSection [SmoothOfRelativeDimension d X.hom]
    (s : (holomorphicFunctionSheaf X d).presheaf.obj (Opposite.op ⊤)) :
    C^ω⟮𝓘(ℂ, Fin d → ℂ), (⊤ : Opens (ComplexPoint X)); ℂ⟯ := s

/-- **The rung, sheaf form.** On a compact `X(ℂ)`, every global section of upstream's
`holomorphicFunctionSheaf X d` is a locally constant function on `⊤`. -/
theorem isLocallyConstant_holomorphicFunctionSheaf_top [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)]
    (s : (holomorphicFunctionSheaf X d).presheaf.obj (Opposite.op ⊤)) :
    IsLocallyConstant (holomorphicTopSection X d s) :=
  isLocallyConstant_contMDiffMap_top X d s

/-- The projective case of `isLocallyConstant_holomorphicFunctionSheaf_top`: compactness of
`X(ℂ)` comes from upstream's `IsProjective.complexPoint_compactSpace`. -/
theorem isLocallyConstant_holomorphicFunctionSheaf_top_of_isProjective
    [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom]
    (s : (holomorphicFunctionSheaf X d).presheaf.obj (Opposite.op ⊤)) :
    IsLocallyConstant (holomorphicTopSection X d s) :=
  isLocallyConstant_holomorphicFunctionSheaf_top X d s

/-- On a compact `X(ℂ)`, global holomorphic functions as locally constant functions on `⊤`: a
ring map into the global sections `LocallyConstant ⊤ ℂ` of the ladder's `locallyConstantSheaf`.
Its underlying function is the section (`holomorphicTopToLocallyConstant_apply`). -/
def holomorphicTopToLocallyConstant [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)] :
    (holomorphicFunctionSheaf X d).presheaf.obj (Opposite.op ⊤) →+*
      LocallyConstant (⊤ : Opens (ComplexPoint X)) ℂ where
  toFun s := ⟨holomorphicTopSection X d s, isLocallyConstant_holomorphicFunctionSheaf_top X d s⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `holomorphicTopToLocallyConstant` evaluates as the section itself. -/
@[simp]
theorem holomorphicTopToLocallyConstant_apply [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)]
    (s : (holomorphicFunctionSheaf X d).presheaf.obj (Opposite.op ⊤))
    (z : (⊤ : Opens (ComplexPoint X))) :
    holomorphicTopToLocallyConstant X d s z = holomorphicTopSection X d s z :=
  rfl

/-- `holomorphicTopToLocallyConstant` is injective: a section is determined by its values. -/
theorem holomorphicTopToLocallyConstant_injective [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)] :
    Function.Injective (holomorphicTopToLocallyConstant X d) := by
  intro s t h
  have : holomorphicTopSection X d s = holomorphicTopSection X d t :=
    ContMDiffMap.ext fun z ↦ DFunLike.congr_fun h z
  exact this

/-- **Constant on a connected `X(ℂ)`.** If `X(ℂ)` is compact and preconnected, every global
holomorphic function is constant. -/
theorem exists_eq_const_holomorphicFunctionSheaf_top [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)] [PreconnectedSpace (ComplexPoint X)]
    (s : (holomorphicFunctionSheaf X d).presheaf.obj (Opposite.op ⊤)) :
    ∃ c : ℂ, ∀ z, holomorphicTopSection X d s z = c := by
  have : PreconnectedSpace (⊤ : Opens (ComplexPoint X)) := preconnectedSpace_opens_top
  obtain ⟨c, hc⟩ := (isLocallyConstant_holomorphicFunctionSheaf_top X d s).exists_eq_const
  exact ⟨c, fun z ↦ congr_fun hc z⟩

end HodgeLadder
