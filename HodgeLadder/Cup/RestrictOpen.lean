module

public import HodgeLadder.Cup.TopOpenCup

/-!
# The singular class of a global cocycle, pulled back to an open

Rung `singular-restrict-open` (front `cup`, supported comparison on a general open). For a global
singular cocycle `b` of `Y` and an open `V ⊆ Y`, upstream's pullback `cohomologyMap` along the
inclusion `V ⟶ Y` sends the singular class of `b` (`singClass`) to the class of the restriction of
`b` to `V`. No sign: both sides are precomposition with chain maps of continuous maps.

## Main results

* `HodgeLadder.Cup.isoTopOpen_inv_comp_inclusion`, `HodgeLadder.Cup.cohomologyMap_inclusion_singClass`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology.Singular

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}} (V : Opens Y)

/-- Upstream's transport `C(⊤) → C(Y)` followed by restriction to `V` is restriction from `⊤` to
`V`. -/
lemma isoTopOpen_inv_comp_inclusion :
    (singularCochainComplexIsoTopOpen ℚ Y).inv ≫ singularCochainComplexMap ℚ (Opens.inclusion' V) =
      HomologicalComplex.linearDualMap
        ((openSingularChainComplexFunctor ℚ Y).map (homOfLE (le_top : V ≤ ⊤))) := by
  have h : Opens.inclusion' V ≫ (Opens.inclusionTopIso Y).inv =
      (Opens.toTopCat Y).map (homOfLE (le_top : V ≤ ⊤)) := by
    ext x
    rfl
  change HomologicalComplex.linearDualMap (topOpenSingularChainComplexIso ℚ Y).inv ≫
      HomologicalComplex.linearDualMap (singularChainComplexMap ℚ (Opens.inclusion' V)) = _
  rw [← HomologicalComplex.linearDualMap_comp]
  congr 1
  change ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ ≫
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ = _
  rw [← Functor.map_comp, h]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The pullback of the singular class of `b` to `V` is the class of `b` restricted to `V`.** -/
theorem cohomologyMap_inclusion_singClass {q : ℕ} (b : OpenCochains ℚ Y (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ Y q).app (op ⊤) b = 0)
    (hbV : (SingularChainComplex ℚ ((Opens.toTopCat Y).obj V)).linearDualCochainComplex.d q (q + 1)
      (resQ b (op V)) = 0) :
    cohomologyMap ℚ q (Opens.inclusion' V) (singClass b hb) =
      (SingularChainComplex ℚ ((Opens.toTopCat Y).obj V)).linearDualCochainComplex.homologyπ q
        ((SingularChainComplex ℚ ((Opens.toTopCat Y).obj V)).linearDualCochainComplex.cyclesMk
          (resQ b (op V)) (q + 1) (by simp) hbV) := by
  rw [singClass_eq, singClassM, cohomologyMap]
  change (HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ Y).inv q ≫
      HomologicalComplex.homologyMap (singularCochainComplexMap ℚ (Opens.inclusion' V)) q) _ = _
  rw [← HomologicalComplex.homologyMap_comp, isoTopOpen_inv_comp_inclusion,
    ← ConcreteCategory.comp_apply]
  erw [HomologicalComplex.homologyπ_naturality]
  rw [ConcreteCategory.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective
    ((SingularChainComplex ℚ ((Opens.toTopCat Y).obj V)).linearDualCochainComplex.iCycles q)).mp
    inferInstance
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  have e1 := HomologicalComplex.i_cyclesMk
    (SingularChainComplex ℚ ((Opens.toTopCat Y).obj V)).linearDualCochainComplex
    (resQ b (op V)) (q + 1) (by simp) hbV
  have e2 := HomologicalComplex.i_cyclesMk (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex
    b (q + 1) (by simp) hb
  erw [e1, e2]
  rfl

end HodgeLadder.Cup
