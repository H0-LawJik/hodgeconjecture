module

public import HodgeLadder.Cup.RightMultCocycle

/-!
# Right multiplication on the constant cochains

Rung `right-mult-unit` (front `cup`, sub-rung 4 of `cup-singular-comparison`). Upstream's map
`ℚ_X → S⁰` is the sheafification of `r ↦ r · ε`, where `ε` is the zero-cochain with value `1`
on every point. Right multiplication by a global `q`-cocycle `b` sends `r · ε` to `r · b|_U`
(the unit law of the cochain cup product). So upstream's map followed by right multiplication is
the sheafification of `r ↦ r · b|_U`.

## Main definitions

* `HodgeLadder.Cup.constTimes`

## Main results

* `HodgeLadder.Cup.openZeroAugmentation_eq_constCochain`, `HodgeLadder.Cup.constTimes_sheafify_one`,
  `HodgeLadder.Cup.rightMulApp_const`, `HodgeLadder.Cup.constantsToZero_rightMul`,
  `HodgeLadder.Cup.constantsToZeroSheaf_rightMulSheaf`
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite AlgebraicTopology.Singular

namespace HodgeLadder.Cup

variable {X : TopCat.{0}}

/-- Upstream's zero-chain augmentation is Tau Ceti's constant cochain with value `1`. -/
lemma openZeroAugmentation_eq_constCochain (U : (Opens X)ᵒᵖ) :
    openZeroAugmentation ℚ X U =
      (TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).constCochain (𝟙 (ModuleCat.of ℚ ℚ)) := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [SSet.ιChainComplex_constCochain]
  exact ιChainComplex_comp_simplicialZeroAugmentation ℚ _ σ

/-- **Right multiplication sends the constant cochain `r` to `r · b|_U`.** -/
theorem rightMulApp_const {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) (U : (Opens X)ᵒᵖ) (r : ℚ) :
    rightMulApp b U 0 q (zero_add q) (constantSingularZeroCochain ℚ X U r) = r • resQ b U := by
  apply (toHomQ X).injective
  simp only [rightMulApp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.apply_symm_apply,
    map_smul]
  change TauCeti.ChainComplex.cupCochain ℚ (awOpen X U) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom 0 q q
      (zero_add q) (r • openZeroAugmentation ℚ X U) (toHomQ X (resQ b U)) =
    r • toHomQ X (resQ b U)
  rw [LinearMap.map_smul₂, openZeroAugmentation_eq_constCochain]
  congr 1
  exact TopCat.cupCochain_constCochain_left (η := 𝟙 (𝟙_ (ModuleCat.{0} ℚ))) _ (by simp; rfl)
    (by simp) (zero_add q) _

lemma map_smul_cochain {q : ℕ} {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (r : ℚ)
    (c : OpenCochains ℚ X U q) :
    (singularCochainPresheaf ℚ X q).map i (r • c : OpenCochains ℚ X U q) =
      r • (show OpenCochains ℚ X V q from (singularCochainPresheaf ℚ X q).map i c) :=
  (((openSingularChainComplexFunctor ℚ X).map i.unop).f q).hom.dualMap.map_smul r c

/-- The presheaf map `r ↦ r · b|_U` from the constant presheaf `ℚ`. -/
def constTimes {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) :
    𝓒ᵖ(X; ℚ) ⟶ singularCochainPresheaf ℚ X q where
  app U := AddCommGrpCat.ofHom
    { toFun r := ((show ℚ from r) • resQ b U : OpenCochains ℚ X U q)
      map_zero' := zero_smul ℚ (resQ b U)
      map_add' r s := add_smul (show ℚ from r) (show ℚ from s) (resQ b U) }
  naturality U V i := by
    ext r
    change ((show ℚ from r) • resQ b V : OpenCochains ℚ X V q) =
      (singularCochainPresheaf ℚ X q).map i ((show ℚ from r) • resQ b U : OpenCochains ℚ X U q)
    rw [map_smul_cochain, ← resQ_map]

/-- **Upstream's constant map followed by right multiplication is `r ↦ r · b|_U`.** -/
theorem constantsToZero_rightMul {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) :
    constantsToSingularCochainZero ℚ X ≫ rightMul b 0 q (zero_add q) = constTimes b := by
  ext U r
  exact rightMulApp_const b _ (show ℚ from r)

/-- The same after sheafification. -/
theorem constantsToZeroSheaf_rightMulSheaf {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) :
    constantsToSingularCochainZeroSheaf ℚ X ≫ rightMulSheaf b 0 q (zero_add q) =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map (constTimes b) := by
  change (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      (constantsToSingularCochainZero ℚ X) ≫
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      (rightMul b 0 q (zero_add q)) = _
  rw [← Functor.map_comp, constantsToZero_rightMul]

/-- **On global sections**: the sheafified map sends the constant section `1` to the sheafified
global cochain `b`. -/
theorem constTimes_sheafify_one {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) :
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map (constTimes b)).hom.app
        (op ⊤) ((toSheafify (Opens.grothendieckTopology X) 𝓒ᵖ(X; ℚ)).app (op ⊤) (1 : ℚ)) =
      (toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf ℚ X q)).app (op ⊤) b := by
  have h := congrArg (fun f => f.app (op ⊤))
    (toSheafify_naturality (Opens.grothendieckTopology X) (constTimes b))
  have h' := ConcreteCategory.congr_hom h (1 : ℚ)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h'
  rw [← h']
  congr 1
  change ((1 : ℚ) • resQ b (op ⊤) : OpenCochains ℚ X (op ⊤) q) = b
  rw [one_smul]
  change (singularCochainPresheaf ℚ X q).map (𝟙 _) b = b
  rw [CategoryTheory.Functor.map_id]
  rfl

end HodgeLadder.Cup
