module

public import HodgeLadder.Cup.SingularCup

/-!
# The relative singular cup product

Rung `relative-singular-cup` (front `cup`, part of the supported comparison). The
Alexander–Whitney diagonal of `X` sends chains of `A` into `C(A) ⊗ C(A)`, so it descends to a
diagonal `C(X, A) → C(X, A) ⊗ C(X)` on upstream's relative chains (the cokernel of
`C(A) → C(X)`). Tau Ceti's cup product along this diagonal is the relative cup product
`H^p(X, A) × H^q(X) → H^{p+q}(X, A)`, and by naturality it is compatible with forgetting `A`.

## Main definitions

* `HodgeLadder.Cup.relDiagonal`, `HodgeLadder.Cup.relCupSing`, `HodgeLadder.Cup.forgetRel`

## Main results

* `HodgeLadder.Cup.relProj_relDiagonal`, `HodgeLadder.Cup.forgetRel_relCupSing`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology.Singular

namespace HodgeLadder.Cup

variable (P : TopPair.{0})

/-- The Alexander–Whitney diagonal of `X` with unit coefficients. -/
abbrev awX (Y : TopCat.{0}) :=
  Y.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv

set_option backward.isDefEq.respectTransparency false in
/-- **The relative diagonal** `C(X, A) → C(X, A) ⊗ C(X)`. -/
def relDiagonal :
    (relativeChainFunctor ℚ).obj P ⟶ (relativeChainFunctor ℚ).obj P ⊗ SingularChainComplex ℚ P.fst :=
  cokernel.desc ((chainPairFunctor ℚ).obj P).hom
    (awX P.fst ≫ (relativeChainProjection ℚ P ⊗ₘ 𝟙 _)) (by
      have hn := TopCat.alexanderWhitneyDiagonal_naturality P.map (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
      change SSet.chainComplexMap (TopCat.toSSet.map P.map) _ ≫ awX P.fst ≫ _ = 0
      rw [← Category.assoc]
      erw [hn]
      rw [Category.assoc, tensorHom_comp_tensorHom]
      have hc : SSet.chainComplexMap (TopCat.toSSet.map P.map) (𝟙_ (ModuleCat.{0} ℚ)) ≫
          relativeChainProjection ℚ P = 0 := cokernel.condition _
      rw [hc]
      simp)

/-- The relative diagonal lifts the diagonal of `X`. -/
lemma relProj_relDiagonal :
    relativeChainProjection ℚ P ≫ relDiagonal P =
      awX P.fst ≫ (relativeChainProjection ℚ P ⊗ₘ 𝟙 _) :=
  cokernel.π_desc _ _ _

/-- Upstream's relative cohomology as Tau Ceti cohomology of the relative chains. -/
def relCohIso (n : ℕ) :
    RelativeCohomology ℚ P n ≅
      (((relativeChainFunctor ℚ).obj P).linearYonedaObj ℚ (ModuleCat.of ℚ ℚ)).homology n :=
  HomologicalComplex.homologyMapIso (dualIsoYoneda ((relativeChainFunctor ℚ).obj P)) n

/-- **The relative singular cup product** `H^p(X, A) × H^q(X) → H^{p+q}(X, A)`. -/
def relCupSing {p q : ℕ} (α : RelativeCohomology ℚ P p) (β : Cohomology ℚ P.fst q) (n : ℕ)
    (h : p + q = n) : RelativeCohomology ℚ P n :=
  (relCohIso P n).inv (TauCeti.ChainComplex.cup ℚ (relDiagonal P) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
    p q n h ((relCohIso P p).hom α) ((cohIso P.fst q).hom β))

/-- Forgetting the subspace: `H^n(X, A) → H^n(X)`. -/
def forgetRel (n : ℕ) : RelativeCohomology ℚ P n ⟶ Cohomology ℚ P.fst n :=
  HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (relativeChainProjection ℚ P)) n

set_option backward.isDefEq.respectTransparency false in
/-- Tau Ceti's singular cup is its generic cup along the Alexander–Whitney diagonal. -/
lemma tcCup_eq (Y : TopCat.{0}) (p q n : ℕ) (h : p + q = n) :
    tcCup Y p q n h = TauCeti.ChainComplex.cup ℚ (awX Y) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h := by
  ext a b
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  erw [TopCat.singularCup_homologyπ, TauCeti.ChainComplex.cup_homologyπ]

lemma linearDualMap_proj_dualIsoYoneda :
    HomologicalComplex.linearDualMap (relativeChainProjection ℚ P) ≫
        (dualIsoYoneda (SingularChainComplex ℚ P.fst)).hom =
      (dualIsoYoneda ((relativeChainFunctor ℚ).obj P)).hom ≫
        (TauCeti.ChainComplex.linearYonedaFunctor ℚ (ModuleCat.of ℚ ℚ)).map
          (relativeChainProjection ℚ P).op := by
  ext n φ
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma cohIso_forgetRel (n : ℕ) (α : RelativeCohomology ℚ P n) :
    (cohIso P.fst n).hom (forgetRel P n α) =
      HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor ℚ
        (ModuleCat.of ℚ ℚ)).map (relativeChainProjection ℚ P).op) n ((relCohIso P n).hom α) := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (linearDualMap_proj_dualIsoYoneda P)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact (ConcreteCategory.congr_hom h α).trans rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Forgetting the subspace carries the relative cup product to the singular cup product.** -/
theorem forgetRel_relCupSing {p q : ℕ} (α : RelativeCohomology ℚ P p)
    (β : Cohomology ℚ P.fst q) (n : ℕ) (h : p + q = n) :
    forgetRel P n (relCupSing P α β n h) = cupSing P.fst (forgetRel P p α) β n h := by
  apply (cohIso P.fst n).toLinearEquiv.injective
  change (cohIso P.fst n).hom _ = (cohIso P.fst n).hom _
  rw [cohIso_forgetRel, relCupSing, Iso.inv_hom_id_apply, cupSing, Iso.inv_hom_id_apply,
    cohIso_forgetRel]
  have hn := TauCeti.ChainComplex.cup_naturality (k := ℚ) (D := relDiagonal P)
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (awX P.fst) (relativeChainProjection ℚ P) (relativeChainProjection ℚ P) (𝟙 _)
    (relProj_relDiagonal P) p q n h ((relCohIso P p).hom α) ((cohIso P.fst q).hom β)
  rw [CategoryTheory.op_id] at hn
  erw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id,
    ConcreteCategory.id_apply] at hn
  rw [tcCup_eq]
  exact hn.symm

end HodgeLadder.Cup
