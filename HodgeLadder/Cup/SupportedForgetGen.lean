module

public import HodgeLadder.Cup.SupportedFinal
public import HodgeLadder.Cup.ConstantGenerator

/-!
# The forgotten representative names the relative cocycle

Part of rung `supported-forget-compat` (front `cup`), stated for a general space. Let `x` be a
relative cocycle of `(⊤, ⊤ ⊓ U)` and `z` the Hom-complex cocycle out of the pair sheaf named by the
supported cocycle `Θ₁ x`. Precomposed with `ℤ_Y → ℤ[Y, U]` (upstream's map for forgetting the
support), `z` is the cocycle named by `x` read as a global cochain.

## Main results

* `HodgeLadder.Cup.gen_forget_named_cocycle`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology.Singular
  CochainComplex.HomComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

variable (Y : TopCat.{0}) [T2Space Y] [∀ W : Opens Y, ParacompactSpace W] (U : Opens Y)

/-- The map `ℤ_Y → ℤ[Y, U]` along which upstream forgets the support. -/
abbrev genForgetMap :
    (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ)) ⟶
      TopCat.Sheaf.pairSheaf' Y U ⊤ U (top_inf_eq _) :=
  (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso Limits.isTerminalTop).inv ≫
    Limits.cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf _).map (homOfLE (le_top : U ≤ ⊤)))

/-- The Hom-complex cocycle out of the pair sheaf named by a supported cocycle. -/
def genCocycle {n : ℕ} (s : (supSeq Y U ⊤).X₁.X (n : ℤ))
    (hs : (supSeq Y U ⊤).X₁.d (n : ℤ) ((n : ℤ) + 1) s = 0) :
    Cocycle ((CochainComplex.singleFunctor (CategoryTheory.Sheaf
      (Opens.grothendieckTopology Y) AddCommGrpCat) 0).obj
      (TopCat.Sheaf.pairSheaf' Y U ⊤ U (top_inf_eq _))) (sInt Y) n :=
  Cocycle.mk ((TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq _)
    (sInt Y)).inv.f n s) ((n : ℤ) + 1) rfl
    (map_d_eq_zero (TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq _)
      (sInt Y)).inv s hs)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The forgotten representative names the relative cocycle.** -/
lemma gen_forget_named_cocycle {n : ℕ} (x : (relSeq Y U ⊤).X₁.X (n : ℤ))
    (hx : (relSeq Y U ⊤).X₁.d (n : ℤ) ((n : ℤ) + 1) x = 0)
    (c : OpenCochains ℚ Y (op ⊤) n)
    (hcx : c = ((relativeDualCochainShortComplexNat ℚ (pairVU Y U ⊤)).X₂.extendXIso
        ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n)).hom
        ((relSeq Y U ⊤).f.f n x)) :
    ((TopCat.Sheaf.constantFunctor Y).map (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso.inv ≫
        genForgetMap Y U) ≫
      Cochain.fromSingleEquiv (zero_add (n : ℤ))
        (genCocycle Y U ((rawMap Y U ⊤).τ₁.f n x) (map_d_eq_zero _ x hx)).1 =
      globalMap c := by
  let s₀ := (rawMap Y U ⊤).τ₁.f n x
  let z := genCocycle Y U s₀ (map_d_eq_zero _ x hx)
  let u : (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶
      (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of (ULift ℤ)) :=
    (TopCat.Sheaf.constantFunctor Y).map (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso.inv
  let iT := CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
    (J := Opens.grothendieckTopology Y) isTerminalTop
  let t1 := (toSheafify (Opens.grothendieckTopology Y)
    ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op ⊤) (1 : ℤ)
  have hgen : iT.inv.hom.app (op ⊤) (u.hom.app (op ⊤) t1) =
      CategoryTheory.Sheaf.freeAbelianSheafGenerator ⊤ := by
    rw [← terminalIso_generator]
    exact ConcreteCategory.congr_hom (congrArg (fun g => g.hom.app (op ⊤)) iT.hom_inv_id) _
  have hes : (TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq _)
      (sInt Y)).hom.f (n : ℤ) z.1 = s₀ := by
    have h1 := congrArg (fun φ => HomologicalComplex.Hom.f φ (n : ℤ))
      (TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq _) (sInt Y)).inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h1
    exact ConcreteCategory.congr_hom h1 s₀
  have h1 := supportedSection_eq_pairEval' U ⊤ U (top_inf_eq _) (rfl : (n : ℤ) = n) z.1
  have h2 : (sInt_XIso (X := Y) (rfl : (n : ℤ) = n)).hom.hom.app (op ⊤)
      ((supSeq Y U ⊤).f.f (n : ℤ) s₀) =
      (toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf ℚ Y n)).app (op ⊤) c := by
    rw [rawMap_comm₁₂_apply, hcx]
    exact rawMapMid_apply Y U ⊤ n _
  have hsec : pairEval U ⊤ U (top_inf_eq _) (rfl : (n : ℤ) = n) z.1 =
      (toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf ℚ Y n)).app (op ⊤) c := by
    rw [← h1, hes]
    exact h2
  rw [globalMap, Iso.eq_comp_inv, AddEquiv.eq_symm_apply, integerConstantHomAddEquivGlobalSections_apply,
    ← hsec]
  change (sInt_XIso (X := Y) (rfl : (n : ℤ) = n)).hom.hom.app (op ⊤)
      ((Limits.cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf _).map (homOfLE (le_top : U ≤ ⊤))) ≫
        Cochain.fromSingleEquiv (zero_add (n : ℤ)) z.1).hom.app (op ⊤)
        (iT.inv.hom.app (op ⊤) (u.hom.app (op ⊤) t1))) = _
  rw [hgen]
  rfl

end HodgeLadder.Cup
