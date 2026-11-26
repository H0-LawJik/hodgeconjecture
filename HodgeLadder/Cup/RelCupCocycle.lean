module

public import HodgeLadder.Cup.RelativeCup

/-!
# The relative cup product on cocycles

Rung `relative-cup-cocycle`, part of `supported-relative-cup` (front `cup`, supported comparison). The relative cup product
`relCupSing` of the classes of a relative cocycle `c` and an absolute cocycle `b` is the class of
their cup product along the relative diagonal, and that relative cocycle, forgotten to a cochain of
`X`, is the Alexander–Whitney cup product of `c` (forgotten) and `b`.

## Main definitions

* `HodgeLadder.Cup.relCupCycles`

## Main results

* `HodgeLadder.Cup.relCupSing_homologyπ`, `HodgeLadder.Cup.relProj_cupCochain`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology.Singular

namespace HodgeLadder.Cup

variable (P : TopPair.{0})

/-- The relative cup product of a relative cocycle and an absolute cocycle, along the relative
diagonal. -/
def relCupCycles {p q : ℕ} (c : (RelativeCochainComplex ℚ P).cycles p)
    (b : (SingularChainComplex ℚ P.fst).linearDualCochainComplex.cycles q) (n : ℕ) (h : p + q = n) :
    (RelativeCochainComplex ℚ P).cycles n :=
  HomologicalComplex.cyclesMap (dualIsoYoneda ((relativeChainFunctor ℚ).obj P)).inv n
    (TauCeti.ChainComplex.cupCycles ℚ (relDiagonal P) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
      (HomologicalComplex.cyclesMap (dualIsoYoneda ((relativeChainFunctor ℚ).obj P)).hom p c)
      (HomologicalComplex.cyclesMap (dualIsoYoneda (SingularChainComplex ℚ P.fst)).hom q b))

set_option backward.isDefEq.respectTransparency false in
/-- **The relative cup product of cocycle classes is the class of the relative cup of cocycles.** -/
theorem relCupSing_homologyπ {p q : ℕ} (c : (RelativeCochainComplex ℚ P).cycles p)
    (b : (SingularChainComplex ℚ P.fst).linearDualCochainComplex.cycles q) (n : ℕ) (h : p + q = n) :
    relCupSing P ((RelativeCochainComplex ℚ P).homologyπ p c)
        ((SingularChainComplex ℚ P.fst).linearDualCochainComplex.homologyπ q b) n h =
      (RelativeCochainComplex ℚ P).homologyπ n (relCupCycles P c b n h) := by
  unfold relCupSing relCohIso cohIso relCupCycles
  simp only [HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_inv]
  have hπ : ∀ {K L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (m : ℕ) (x : K.cycles m),
      HomologicalComplex.homologyMap φ m (K.homologyπ m x) =
        L.homologyπ m (HomologicalComplex.cyclesMap φ m x) := by
    intro K L φ m x
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
  erw [hπ, hπ]
  erw [TauCeti.ChainComplex.cup_homologyπ, hπ]

/-- **Forgetting the subspace sends the relative cup to the Alexander–Whitney cup.** -/
lemma relProj_cupCochain {p q : ℕ}
    (φ : ((relativeChainFunctor ℚ).obj P).X p ⟶ ModuleCat.of ℚ ℚ)
    (ψ : (SingularChainComplex ℚ P.fst).X q ⟶ ModuleCat.of ℚ ℚ) (n : ℕ) (h : p + q = n) :
    TauCeti.ChainComplex.cupCochain ℚ (awX P.fst) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
        ((relativeChainProjection ℚ P).f p ≫ φ) ψ =
      (relativeChainProjection ℚ P).f n ≫
        TauCeti.ChainComplex.cupCochain ℚ (relDiagonal P) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h φ ψ := by
  have := TauCeti.ChainComplex.cupCochain_naturality (k := ℚ) (D := relDiagonal P)
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (awX P.fst) (relativeChainProjection ℚ P)
    (relativeChainProjection ℚ P) (𝟙 _) (relProj_relDiagonal P) p q n h φ ψ
  rw [HomologicalComplex.id_f] at this
  refine Eq.trans ?_ this
  congr 1

end HodgeLadder.Cup
