module

public import HodgeLadder.Cup.SupportedPair
public import HodgeLadder.Cup.SupportedForgetFinal
public import HodgeLadder.Cup.SupportedAgreement

/-!
# The supported comparison on `(X, X ∖ Z)`: forgetting the support, and upstream's transport

Rung `supported-pair-forget` (front `cup`). The checked statements `supported_forget_compat` and
`transport_eq_flasqueModel` are stated on the pair of opens `(⊤, ⊤ ⊓ (X ∖ Z))` and on upstream's
`neighborhoodSupportComplementPair ⊤ Z`. This file moves both to `TopPair.ofSubset (X ∖ Z)`, the
pair of `supportedEquivPair` and of `triad-relative-cup`, through isomorphisms of pairs that are
the identity on points, so no sign enters:

* `forgetRel (supportedEquivPair α) = Ψ (forgetSupport α)`;
* `supportedEquivPair α` is upstream's transport `complexSupportInjectiveSectionCohomologyEquiv X Z ⊤`
  of upstream's injective model of `α`, pulled back along `ofSubsetIsoNeighborhoodTop`.

The helper isomorphism `ofSubsetIsoNeighborhoodTop` has both endpoints spelled as the declarations
it connects (`Z.compl` and `(⊤ : Opens Y)`), so rewrites across it typecheck without unfolding
`Closeds.compl` (red team, finding 2; `docs/conventions.md`, "Pair spellings of (X, X ∖ Z)").
`ofSubsetIsoNeighborhoodUniv` is the same identity for consumers spelled with `S : Set Y`.

## Main definitions

* `HodgeLadder.Cup.ofSubsetIsoNeighborhoodTop`, `HodgeLadder.Cup.ofSubsetIsoNeighborhoodUniv`

## Main results

* `HodgeLadder.Cup.ofSubsetIsoNeighborhoodTop_fst_apply`,
  `HodgeLadder.Cup.ofSubsetIsoNeighborhoodTop_hom_comp_inv`,
  `HodgeLadder.Cup.ofSubsetIsoNeighborhoodUniv_fst_apply` (identity on points)
* `HodgeLadder.Cup.relativeCohomologyMap_inv_hom_apply`
* `HodgeLadder.Cup.forgetRel_relativeCohomologyMap` (naturality of `forgetRel`)
* `HodgeLadder.Cup.forgetRel_supportedEquivPair`
* `HodgeLadder.Cup.supportedEquivPair_eq_transport`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology.Singular

namespace HodgeLadder.Cup

section Pairs

/-- The isomorphism of pairs `(Y, Y ∖ S) ≅ (univ, univ ∖ S)` given by the identity of `Y`; the
second pair is upstream's `neighborhoodSupportComplementPair univ S`. -/
def ofSubsetIsoNeighborhoodUniv {Y : Type} [TopologicalSpace Y] (S : Set Y) :
    TopPair.ofSubset (X := TopCat.of Y) (Sᶜ : Set Y) ≅
      neighborhoodSupportComplementPair (Set.univ : Set Y) S :=
  TopPair.isoOfSubset (Homeomorph.Set.univ Y).symm (fun _ => Iff.rfl)

/-- `ofSubsetIsoNeighborhoodUniv` is the identity on points. -/
theorem ofSubsetIsoNeighborhoodUniv_fst_apply {Y : Type} [TopologicalSpace Y] (S : Set Y)
    (y : Y) : (TopPair.Hom.fst (ofSubsetIsoNeighborhoodUniv S).hom y).1 = y :=
  rfl

/-- The isomorphism of pairs `(Y, Y ∖ Z) ≅ (⊤, ⊤ ∖ Z)` given by the identity of `Y`. The domain is
spelled as the codomain of `supportedEquivPair`, the codomain as upstream's
`neighborhoodSupportComplementPair` at `V = ⊤`, the target of
`complexSupportInjectiveSectionCohomologyEquiv X Z ⊤`. -/
def ofSubsetIsoNeighborhoodTop {Y : Type} [TopologicalSpace Y] (Z : Closeds Y) :
    TopPair.ofSubset (X := TopCat.of Y) (Z.compl : Set Y) ≅
      neighborhoodSupportComplementPair ((⊤ : Opens Y) : Set Y) (Z : Set Y) :=
  TopPair.isoOfSubset (Homeomorph.Set.univ Y).symm (fun _ => Iff.rfl)

/-- `ofSubsetIsoNeighborhoodTop` is the identity on points. -/
theorem ofSubsetIsoNeighborhoodTop_fst_apply {Y : Type} [TopologicalSpace Y] (Z : Closeds Y)
    (y : Y) : (TopPair.Hom.fst (ofSubsetIsoNeighborhoodTop Z).hom y).1 = y :=
  rfl

/-- `ofSubsetIsoNeighborhoodTop` followed by the inverse of upstream's
`openIntersectionPairIsoSupportComplement` at `V = ⊤` is `topPairIso`: all three are the identity
on points. -/
theorem ofSubsetIsoNeighborhoodTop_hom_comp_inv {Y : Type} [TopologicalSpace Y] (Z : Closeds Y) :
    (ofSubsetIsoNeighborhoodTop Z).hom ≫
        (openIntersectionPairIsoSupportComplement (TopCat.of Y) Z Z.isClosed ⊤).inv =
      (topPairIso (TopCat.of Y) Z.compl).hom := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl

/-- Pulling back along an isomorphism of pairs and then along its inverse is the identity. -/
theorem relativeCohomologyMap_inv_hom_apply {P Q : TopPair.{0}} (e : P ≅ Q) (n : ℕ)
    (x : RelativeCohomology ℚ Q n) :
    relativeCohomologyMap ℚ n e.inv (relativeCohomologyMap ℚ n e.hom x) = x := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, e.inv_hom_id, relativeCohomologyMap_id]
  rfl

end Pairs

section Naturality

variable {P P' : TopPair.{0}} (f : P ⟶ P')

/-- **Forgetting the subspace is natural** for maps of pairs. -/
theorem forgetRel_relativeCohomologyMap (n : ℕ) (x : RelativeCohomology ℚ P' n) :
    forgetRel P n (relativeCohomologyMap ℚ n f x) =
      HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap (fstChainMap f)) n
        (forgetRel P' n x) := by
  have h : HomologicalComplex.linearDualMap ((relativeChainFunctor ℚ).map f) ≫
      HomologicalComplex.linearDualMap (relativeChainProjection ℚ P) =
      HomologicalComplex.linearDualMap (relativeChainProjection ℚ P') ≫
        HomologicalComplex.linearDualMap (fstChainMap f) := by
    rw [← HomologicalComplex.linearDualMap_comp, ← HomologicalComplex.linearDualMap_comp,
      TopPair.Homotopy.relativeChainProjection_naturality]
  have h' := congrArg (fun g => HomologicalComplex.homologyMap g n) h
  simp only [HomologicalComplex.homologyMap_comp] at h'
  exact ConcreteCategory.congr_hom h' x

end Naturality

section Variety

open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (Z : Closeds (ComplexPoint X))

set_option backward.isDefEq.respectTransparency false in
/-- **Forgetting the support on `(X, X ∖ Z)`**, with no sign: `forgetRel ∘ supportedEquivPair` is
upstream's sheaf–singular comparison `Ψ` after `forgetSupport`. -/
theorem forgetRel_supportedEquivPair [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    forgetRel (TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (Z.compl : Set (ComplexPoint X)))
        n (supportedEquivPair X Z n α) =
      rationalCohomologyAddEquivSingularCohomology X n (forgetSupport ℚ X Z n α) := by
  refine (forgetRel_relativeCohomologyMap (topPairIso (TopCat.of (ComplexPoint X)) Z.compl).hom n
    (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤ n
      (flasqueModel X Z n α))).trans ?_
  rw [supported_forget_compat X Z n α]
  exact fst_topOpen _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- **`supportedEquivPair` is upstream's transport**, with no sign: upstream's injective model of
`α`, then upstream's `complexSupportInjectiveSectionCohomologyEquiv X Z ⊤` into
`H^n(⊤, ⊤ ∖ Z; ℚ)`, then the pullback along `ofSubsetIsoNeighborhoodTop` (the identity on
points) is `supportedEquivPair X Z n α`. -/
theorem supportedEquivPair_eq_transport [IsProjective X.hom]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    supportedEquivPair X Z n α =
      relativeCohomologyMap ℚ n (ofSubsetIsoNeighborhoodTop Z).hom
        (complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ n
          (rationalSupportAddEquivSupportedInjectiveHomology X Z n α)) := by
  rw [transport_eq_flasqueModel]
  have e := congrArg (fun f => relativeCohomologyMap ℚ n f) (ofSubsetIsoNeighborhoodTop_hom_comp_inv Z)
  simp only [relativeCohomologyMap_comp] at e
  exact (LinearMap.congr_fun e _).symm

end Variety

end HodgeLadder.Cup
