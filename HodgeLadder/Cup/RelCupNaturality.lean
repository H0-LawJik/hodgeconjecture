module

public import HodgeLadder.Cup.RelativeCup
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-!
# Naturality of the relative singular cup product

Part of rung `cup-comparison-supported-pair` (front `cup`). For a map of pairs `f : P → P'`,
the relative diagonal commutes with the chain maps of `f`, so pulling back along `f` carries the
relative cup product of `P'` to that of `P`.

## Main results

* `HodgeLadder.Cup.relDiagonal_naturality`, `HodgeLadder.Cup.relCohIso_map`,
  `HodgeLadder.Cup.cohIso_map`, `HodgeLadder.Cup.relCupSing_naturality`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology.Singular

namespace HodgeLadder.Cup

variable {P P' : TopPair.{0}} (f : P ⟶ P')

/-- The singular chain map of the ambient map of a map of pairs. -/
abbrev fstChainMap : SingularChainComplex ℚ P.fst ⟶ SingularChainComplex ℚ P'.fst :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map (TopPair.Hom.fst f)

set_option backward.isDefEq.respectTransparency false in
/-- **The relative diagonal is natural for maps of pairs.** -/
lemma relDiagonal_naturality :
    (relativeChainFunctor ℚ).map f ≫ relDiagonal P' =
      relDiagonal P ≫ ((relativeChainFunctor ℚ).map f ⊗ₘ fstChainMap f) := by
  haveI : Epi (relativeChainProjection ℚ P) := by
    unfold relativeChainProjection
    infer_instance
  rw [← cancel_epi (relativeChainProjection ℚ P), ← Category.assoc,
    TopPair.Homotopy.relativeChainProjection_naturality, Category.assoc, relProj_relDiagonal]
  erw [← Category.assoc (relativeChainProjection ℚ P) (relDiagonal P), relProj_relDiagonal P]
  have hn := TopCat.alexanderWhitneyDiagonal_naturality (TopPair.Hom.fst f)
    (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc, Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  erw [TopPair.Homotopy.relativeChainProjection_naturality]
  rfl

/-- The Tau Ceti form of a pullback along a chain map. -/
lemma linearDualMap_dualIsoYoneda {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) :
    HomologicalComplex.linearDualMap φ ≫ (dualIsoYoneda K).hom =
      (dualIsoYoneda L).hom ≫
        (TauCeti.ChainComplex.linearYonedaFunctor ℚ (ModuleCat.of ℚ ℚ)).map φ.op := by
  ext n ψ
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma homologyMap_dualIsoYoneda_apply {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (n : ℕ)
    (γ : L.linearDualCochainComplex.homology n) :
    HomologicalComplex.homologyMap (dualIsoYoneda K).hom n
        (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap φ) n γ) =
      HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor ℚ
        (ModuleCat.of ℚ ℚ)).map φ.op) n (HomologicalComplex.homologyMap (dualIsoYoneda L).hom n γ) := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n) (linearDualMap_dualIsoYoneda φ)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h γ

set_option backward.isDefEq.respectTransparency false in
lemma relCohIso_map (n : ℕ) (γ : RelativeCohomology ℚ P' n) :
    (relCohIso P n).hom (relativeCohomologyMap ℚ n f γ) =
      HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor ℚ
        (ModuleCat.of ℚ ℚ)).map ((relativeChainFunctor ℚ).map f).op) n ((relCohIso P' n).hom γ) :=
  homologyMap_dualIsoYoneda_apply _ n γ

set_option backward.isDefEq.respectTransparency false in
lemma cohIso_map (q : ℕ) (β : Cohomology ℚ P'.fst q) :
    (cohIso P.fst q).hom
        (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap (fstChainMap f)) q β) =
      HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor ℚ
        (ModuleCat.of ℚ ℚ)).map (fstChainMap f).op) q ((cohIso P'.fst q).hom β) :=
  homologyMap_dualIsoYoneda_apply _ q β

set_option backward.isDefEq.respectTransparency false in
/-- **Pulling back along a map of pairs carries the relative cup product to the relative cup
product.** -/
theorem relCupSing_naturality {p q : ℕ} (α : RelativeCohomology ℚ P' p)
    (β : Cohomology ℚ P'.fst q) (n : ℕ) (h : p + q = n) :
    relativeCohomologyMap ℚ n f (relCupSing P' α β n h) =
      relCupSing P (relativeCohomologyMap ℚ p f α)
        (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap (fstChainMap f)) q β) n h := by
  apply (relCohIso P n).toLinearEquiv.injective
  change (relCohIso P n).hom _ = (relCohIso P n).hom _
  rw [relCohIso_map, relCupSing, Iso.inv_hom_id_apply, relCupSing, Iso.inv_hom_id_apply,
    relCohIso_map, cohIso_map]
  exact (TauCeti.ChainComplex.cup_naturality (k := ℚ) (D := relDiagonal P')
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (relDiagonal P) ((relativeChainFunctor ℚ).map f)
    ((relativeChainFunctor ℚ).map f) (fstChainMap f) (relDiagonal_naturality f) p q n h
    ((relCohIso P' p).hom α) ((cohIso P'.fst q).hom β)).symm

end HodgeLadder.Cup
