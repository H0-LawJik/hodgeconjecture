module

public import HodgeLadder.Cup.SupportedFinal
public import HodgeLadder.Cup.RelCupNaturality

/-!
# The supported comparison on the pair `(X, X ∖ Z)`

Rung `cup-comparison-supported-pair` (front `cup`). The supported comparison
`cup_singular_comparison_supported` lands in the cohomology of the pair `(⊤, ⊤ ⊓ (X ∖ Z))` of
opens, with `Ψ β` read on `⊤`. The identity of `X` is an isomorphism of pairs from `(X, X ∖ Z)`
(upstream's `TopPair.ofSubset`, the pair of `CohomologyWithSupport`) to that pair. Transporting
along it, with `relCupSing_naturality`, states the comparison on `H^n(X, X ∖ Z; ℚ)` with `Ψ β` on
`X` itself.

## Main definitions

* `HodgeLadder.Cup.topPairIso`, `HodgeLadder.Cup.supportedEquivPair`

## Main results

* `HodgeLadder.Cup.cup_singular_comparison_supported_pair`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology.Singular TopCat.Sheaf

namespace HodgeLadder.Cup

variable (Y : TopCat.{0}) (U : Opens Y)

/-- The isomorphism of pairs `(Y, U) ≅ (⊤, ⊤ ⊓ U)` given by the identity of `Y`. -/
def topPairIso : TopPair.ofSubset (U : Set Y) ≅ pairVU Y U ⊤ where
  hom := TopPair.ofHom (Opens.inclusionTopIso Y).inv
    (TopCat.ofHom ⟨fun y => ⟨y.1, ⟨trivial, y.2⟩⟩, continuous_subtype_val.subtype_mk _⟩) rfl
  inv := TopPair.ofHom (Opens.inclusionTopIso Y).hom
    (TopCat.ofHom ⟨fun y => ⟨y.1, y.2.2⟩, continuous_subtype_val.subtype_mk _⟩) rfl
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl

/-- Relative cohomology along `topPairIso`. -/
def pairCohIso (n : ℕ) :
    RelativeCohomology ℚ (pairVU Y U ⊤) n ≅ RelativeCohomology ℚ (TopPair.ofSubset (U : Set Y)) n :=
  HomologicalComplex.homologyMapIso
    (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso (topPairIso Y U))) n

lemma pairCohIso_hom_apply (n : ℕ) (x : RelativeCohomology ℚ (pairVU Y U ⊤) n) :
    (pairCohIso Y U n).hom x = relativeCohomologyMap ℚ n (topPairIso Y U).hom x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Reading a class of `Y` on the open `⊤` and pulling it back along `topPairIso` gives it back. -/
lemma fst_topOpen (q : ℕ) (γ : Cohomology ℚ Y q) :
    HomologicalComplex.homologyMap
        (HomologicalComplex.linearDualMap (fstChainMap (topPairIso Y U).hom)) q
        (HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ Y).hom q γ) = γ := by
  have h : (singularCochainComplexIsoTopOpen ℚ Y).hom ≫
      HomologicalComplex.linearDualMap (fstChainMap (topPairIso Y U).hom) = 𝟙 _ := by
    change HomologicalComplex.linearDualMap (topOpenSingularChainComplexIso ℚ Y).hom ≫ _ = _
    rw [← HomologicalComplex.linearDualMap_comp]
    have e : fstChainMap (topPairIso Y U).hom ≫ (topOpenSingularChainComplexIso ℚ Y).hom = 𝟙 _ := by
      change ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ ℚ)).map (Opens.inclusionTopIso Y).inv ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ ℚ)).map (Opens.inclusionTopIso Y).hom = _
      rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
      rfl
    rw [e, HomologicalComplex.linearDualMap_id]
    rfl
  erw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp, h,
    HomologicalComplex.homologyMap_id]
  rfl

section Variety

open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (Z : Closeds (ComplexPoint X))

/-- **The supported comparison on `(X, X ∖ Z)`**: upstream's flasque supported-sections model,
then `supportedRationalSingularSectionCohomologyEquivRelative` at `V = ⊤`, `U = X ∖ Z`, then the
isomorphism of pairs `(X, X ∖ Z) ≅ (⊤, ⊤ ⊓ (X ∖ Z))`. -/
def supportedEquivPair (n : ℕ) :
    H_[Z]^n(X; ℚ) ≃+ RelativeCohomology ℚ
      (TopPair.ofSubset (Z.compl : Set (TopCat.of (ComplexPoint X)))) n :=
  (flasqueModel X Z n).trans
    ((supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤
      n).trans (pairCohIso (TopCat.of (ComplexPoint X)) Z.compl n).toLinearEquiv.toAddEquiv)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The supported cup product against the relative singular cup product on `(X, X ∖ Z)`**:
`Φ (α ∪ β) = (−1)^{pq} · relCupSing (Φ α) (Ψ β)`, with `Ψ` upstream's sheaf–singular
equivalence. -/
theorem cup_singular_comparison_supported_pair {p q : ℕ} (α : H_[Z]^p(X; ℚ)) (β : H^q(X; ℚ)) :
    supportedEquivPair X Z (p + q) (supCup α β (p + q) rfl) =
      (((p : ℤ) * q).negOnePow : ℤ) • relCupSing
        (TopPair.ofSubset (Z.compl : Set (TopCat.of (ComplexPoint X))))
        (supportedEquivPair X Z p α) (rationalCohomologyAddEquivSingularCohomology X q β)
        (p + q) rfl := by
  change (pairCohIso (TopCat.of (ComplexPoint X)) Z.compl (p + q)).hom
      (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤
        (p + q) (flasqueModel X Z (p + q) (supCup α β (p + q) rfl))) = _
  rw [cup_singular_comparison_supported]
  refine (map_zsmul (pairCohIso (TopCat.of (ComplexPoint X)) Z.compl (p + q)).hom.hom _ _).trans ?_
  refine congrArg (_ • ·) ?_
  rw [pairCohIso_hom_apply, relCupSing_naturality, fst_topOpen]
  rfl

end Variety

end HodgeLadder.Cup
