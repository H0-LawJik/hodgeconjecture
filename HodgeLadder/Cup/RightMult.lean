module

public import HodgeLadder.Cup.SingularCup
public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.Cochain

/-!
# Right multiplication by a global singular cocycle

Rung `cochain-sheaf-right-mult` (front `cup`, sub-rung 3 of `cup-singular-comparison`). For a
global singular `q`-cocycle `b` on a space `X`, right multiplication `c ↦ c ∪ b|_U` on singular
cochains of each open `U` is natural under restriction and commutes with the coboundary
(Leibniz rule, `δb = 0`). It is a family of morphisms of presheaves on upstream's singular cochain
presheaves, and passes to the sheafification.

## Main definitions

* `HodgeLadder.Cup.rightMulApp`, `HodgeLadder.Cup.rightMul`, `HodgeLadder.Cup.rightMulSheaf`

## Main results

* `HodgeLadder.Cup.rightMulApp_naturality`, `HodgeLadder.Cup.rightMul_comp_coboundary`,
  `HodgeLadder.Cup.rightMulSheaf_comp_coboundary`
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite AlgebraicTopology.Singular

namespace HodgeLadder.Cup

variable (X : TopCat.{0})

/-- The singular chain complex of an open subset, with rational coefficients. -/
abbrev opChains (U : (Opens X)ᵒᵖ) : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  (openSingularChainComplexFunctor ℚ X).obj U.unop

/-- Linear dual cochains as morphisms into `ℚ`. -/
abbrev toHomQ {U : (Opens X)ᵒᵖ} {n : ℕ} :
    OpenCochains ℚ X U n ≃ₗ[ℚ] ((opChains X U).X n ⟶ ModuleCat.of ℚ ℚ) :=
  (ModuleCat.homLinearEquiv (R := ℚ) (S := ℚ) (M := (opChains X U).X n)
    (N := ModuleCat.of ℚ ℚ)).symm

/-- The Alexander–Whitney diagonal of an open subset. -/
abbrev awOpen (U : (Opens X)ᵒᵖ) :
    opChains X U ⟶ HomologicalComplex.tensorObj (opChains X U) (opChains X U) :=
  (Opens.toTopCat X |>.obj U.unop).alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv

variable {X}

/-- Restriction of a global cochain to an open subset. -/
abbrev resQ {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) (U : (Opens X)ᵒᵖ) : OpenCochains ℚ X U q :=
  (singularCochainPresheaf ℚ X q).map (homOfLE (le_top : U.unop ≤ ⊤)).op b

/-- Right multiplication by `b` on cochains of `U`, in degree `n`, landing in degree `m = n + q`. -/
def rightMulApp {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) (U : (Opens X)ᵒᵖ) (n m : ℕ)
    (h : n + q = m) : OpenCochains ℚ X U n →+ OpenCochains ℚ X U m where
  toFun c := (toHomQ X).symm (TauCeti.ChainComplex.cupCochain ℚ (awOpen X U)
    (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom n q m h (toHomQ X c) (toHomQ X (resQ b U)))
  map_zero' := by simp
  map_add' c c' := by simp

lemma toHomQ_map {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) {n : ℕ} (c : OpenCochains ℚ X U n) :
    toHomQ X ((singularCochainPresheaf ℚ X n).map i c) =
      ((openSingularChainComplexFunctor ℚ X).map i.unop).f n ≫ toHomQ X c := rfl

lemma resQ_map {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    resQ b V = (singularCochainPresheaf ℚ X q).map i (resQ b U) := by
  unfold resQ
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **Right multiplication is natural under restriction.** -/
theorem rightMulApp_naturality {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) {U V : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (n m : ℕ) (h : n + q = m) (c : OpenCochains ℚ X U n) :
    (singularCochainPresheaf ℚ X m).map i (rightMulApp b U n m h c) =
      rightMulApp b V n m h ((singularCochainPresheaf ℚ X n).map i c) := by
  apply (toHomQ X).injective
  rw [toHomQ_map]
  simp only [rightMulApp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.apply_symm_apply]
  rw [resQ_map b i, toHomQ_map, toHomQ_map]
  exact (TauCeti.ChainComplex.cupCochain_naturality (k := ℚ) (D := awOpen X U)
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (D' := awOpen X V)
    (e := (openSingularChainComplexFunctor ℚ X).map i.unop)
    (f := (openSingularChainComplexFunctor ℚ X).map i.unop)
    (g := (openSingularChainComplexFunctor ℚ X).map i.unop)
    (TopCat.alexanderWhitneyDiagonal_naturality _ _) n q m h _ _).symm

lemma toHomQ_coboundary {U : (Opens X)ᵒᵖ} {n : ℕ} (c : OpenCochains ℚ X U n) :
    toHomQ X ((singularCochainCoboundary ℚ X n).app U c) =
      (opChains X U).d (n + 1) n ≫ toHomQ X c := rfl

/-- Restriction commutes with the coboundary. -/
lemma resQ_coboundary {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) (U : (Opens X)ᵒᵖ) :
    (singularCochainCoboundary ℚ X q).app U (resQ b U) =
      resQ ((singularCochainCoboundary ℚ X q).app (op ⊤) b) U := by
  apply (toHomQ X).injective
  change (opChains X U).d (q + 1) q ≫ ((openSingularChainComplexFunctor ℚ X).map
      (homOfLE (le_top : U.unop ≤ ⊤))).f q ≫ toHomQ X b =
    ((openSingularChainComplexFunctor ℚ X).map (homOfLE (le_top : U.unop ≤ ⊤))).f (q + 1) ≫
      ((opChains X (op ⊤)).d (q + 1) q ≫ toHomQ X b)
  rw [← Category.assoc, ← Category.assoc,
    ((openSingularChainComplexFunctor ℚ X).map (homOfLE (le_top : U.unop ≤ ⊤))).comm (q + 1) q]

/-- **Right multiplication by a cocycle commutes with the coboundary.** -/
theorem rightMulApp_coboundary {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ X q).app (op ⊤) b = 0) (U : (Opens X)ᵒᵖ) (n m : ℕ)
    (h : n + q = m) (c : OpenCochains ℚ X U n) :
    (singularCochainCoboundary ℚ X m).app U (rightMulApp b U n m h c) =
      rightMulApp b U (n + 1) (m + 1) (by omega) ((singularCochainCoboundary ℚ X n).app U c) := by
  apply (toHomQ X).injective
  rw [toHomQ_coboundary]
  simp only [rightMulApp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.apply_symm_apply]
  rw [TauCeti.ChainComplex.d_comp_cupCochain, toHomQ_coboundary]
  have hres : (opChains X U).d (q + 1) q ≫ toHomQ X (resQ b U) = 0 := by
    rw [← toHomQ_coboundary, resQ_coboundary, hb]
    erw [map_zero]
  rw [hres, map_zero, smul_zero, add_zero]

/-- **Right multiplication by `b`** as a morphism of presheaves, from degree `n` to `m = n + q`. -/
def rightMul {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) (n m : ℕ) (h : n + q = m) :
    singularCochainPresheaf ℚ X n ⟶ singularCochainPresheaf ℚ X m where
  app U := AddCommGrpCat.ofHom (rightMulApp b U n m h)
  naturality U V i := by
    ext c
    exact (rightMulApp_naturality b i n m h c).symm

/-- Right multiplication by a cocycle commutes with the coboundary, as morphisms of presheaves. -/
theorem rightMul_comp_coboundary {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ X q).app (op ⊤) b = 0) (n m : ℕ) (h : n + q = m) :
    rightMul b n m h ≫ singularCochainCoboundary ℚ X m =
      singularCochainCoboundary ℚ X n ≫ rightMul b (n + 1) (m + 1) (by omega) := by
  ext U c
  exact rightMulApp_coboundary b hb (op U) n m h c

/-- **Right multiplication by `b` on the singular cochain sheaves.** -/
def rightMulSheaf {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) (n m : ℕ) (h : n + q = m) :
    singularCochainSheaf ℚ X n ⟶ singularCochainSheaf ℚ X m :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map (rightMul b n m h)

/-- Right multiplication by a cocycle commutes with the sheaf coboundary. -/
theorem rightMulSheaf_comp_coboundary {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ X q).app (op ⊤) b = 0) (n m : ℕ) (h : n + q = m) :
    rightMulSheaf b n m h ≫ singularCochainSheafCoboundary ℚ X m =
      singularCochainSheafCoboundary ℚ X n ≫ rightMulSheaf b (n + 1) (m + 1) (by omega) := by
  change (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map (rightMul b n m h) ≫
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
        (singularCochainCoboundary ℚ X m) =
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
        (singularCochainCoboundary ℚ X n) ≫
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
        (rightMul b (n + 1) (m + 1) (by omega))
  rw [← Functor.map_comp, ← Functor.map_comp, rightMul_comp_coboundary b hb]

end HodgeLadder.Cup
