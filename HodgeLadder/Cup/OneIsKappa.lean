module

public import HodgeLadder.Cup.KappaCancel
public import HodgeLadder.Cup.AbYoneda

/-!
# The unit class of rational cohomology is `ℤ_Y → ℚ_Y`

Rung `one-is-kappa` (front `cup`, part of `end-class-right-mult`). The unit `oneY` of
`H⁰(Y; ℚ) = Ext⁰(ℤ_Y, ℚ_Y)` is the class of the map of constant sheaves `κ : ℤ_Y → ℚ_Y`. So every
class `β` is `κ` followed by its endomorphism class `forgetEnd (e β)` (`ab-ext-yoneda`).

## Main results

* `HodgeLadder.Cup.adj_tensorQSheafInt_comp_forgetQX`, `HodgeLadder.Cup.rationalExtEquiv_kappa`,
  `HodgeLadder.Cup.oneY_eq_kappa`, `HodgeLadder.Cup.eq_kappa_comp_forgetEnd`
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace HodgeLadder.Cup

variable (Y : TopCat.{0})

/-- **The adjoint of `ℚ ⊗ ℤ_Y ≅ ℚ_Y`, followed by `forgetQX`, is `κ`.** -/
theorem adj_tensorQSheafInt_comp_forgetQX :
    (adjQSheaf Y).homEquiv _ _ (tensorQSheafInt Y).hom ≫ (forgetQX Y).hom = kappaSheaf Y := by
  let adjC := constantSheafAdj (J Y) AddCommGrpCat.{0} isTerminalTop
  apply (adjC.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  have hc : adjC.homEquiv _ _ ((adjQSheaf Y).homEquiv _ _ (tensorQSheafInt Y).hom) =
      (adjC.comp (adjQSheaf Y)).homEquiv _ _ (tensorQSheafInt Y).hom := by
    rw [Adjunction.comp_homEquiv]; rfl
  rw [hc, tensorQSheafInt, Iso.trans_hom, Adjunction.homEquiv_naturality_right, tensorQConstIso,
    Iso.app_hom]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [kappaSheaf, ← Category.comp_id ((constantSheaf (J Y) AddCommGrpCat.{0}).map kappaAb),
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_id]
  let adjCQ := constantSheafAdj (J Y) (ModuleCat.{0} ℚ) isTerminalTop
  have F1 : adjQ.unit.app (AddCommGrpCat.of (ULift.{0} ℤ)) ≫ U.map tensorQInt.hom = kappaAb := by
    ext ⟨n⟩
    simp [adjQ, tensorQInt, extendScalarsEquivSelf, kappaAb, Adjunction.comp_unit_app,
      Adjunction.ofNatIsoRight]
    erw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
    have hc := Iso.inv_hom_id_apply (intEquiv.counitIso.app (AddCommGrpCat.of (ULift.{0} ℤ)))
      (ULift.up n)
    calc _ = ((AddEquiv.ulift ((intEquiv.counitIso.app (AddCommGrpCat.of (ULift.{0} ℤ))).hom
            ((intEquiv.counitIso.app (AddCommGrpCat.of (ULift.{0} ℤ))).inv (ULift.up n))) : ℤ) •
            (1 : ℚ)) := rfl
      _ = _ := by rw [hc]; simp
  have F2 : U.map (adjCQ.unit.app (ModuleCat.of ℚ ℚ)) ≫
      ((sheafSections (J Y) AddCommGrpCat.{0}).obj (Opposite.op ⊤)).map (forgetQX Y).hom =
      adjC.unit.app (AddCommGrpCat.of ℚ) := by
    let P := (Functor.const (TopologicalSpace.Opens Y)ᵒᵖ).obj (ModuleCat.of ℚ ℚ)
    have h1 := congrArg (fun f => f.app (Opposite.op ⊤)) (sheafComposeIso_inv_fac (J Y) U P)
    have h2 := congrArg (fun f => f.app (Opposite.op ⊤))
      (toSheafify_naturality (J Y) (Functor.constComp (TopologicalSpace.Opens Y)ᵒᵖ (ModuleCat.of ℚ ℚ) U).hom)
    ext q
    have e1 := ConcreteCategory.congr_hom h1 q
    have e2 := ConcreteCategory.congr_hom h2 q
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, ConcreteCategory.comp_apply] at e1 e2
    simp only [adjCQ, adjC, constantSheafAdj, Adjunction.comp_unit_app]
    erw [ConcreteCategory.comp_apply]
    change ConcreteCategory.hom (((constantCommuteCompose (J Y) U).hom.app
      (ModuleCat.of ℚ ℚ)).hom.app (Opposite.op ⊤)) _ = _
    rw [constantCommuteCompose_hom_app_hom]
    erw [NatTrans.comp_app, ConcreteCategory.comp_apply]
    erw [e1]
    erw [← e2]
    rfl
  simp only [Adjunction.ofNatIsoRight, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc]
  erw [Adjunction.comp_unit_app]
  simp only [Category.assoc]
  have hnat := adjCQ.unit.naturality tensorQInt.hom
  ext x
  have e1 := ConcreteCategory.congr_hom hnat ((adjQ.unit.app (AddCommGrpCat.of (ULift.{0} ℤ))) x)
  have e2 := ConcreteCategory.congr_hom F1 x
  have e3 := ConcreteCategory.congr_hom F2 (kappaAb x)
  simp only [ConcreteCategory.comp_apply] at e1 e2 e3 ⊢
  erw [← e1]
  erw [e2]
  exact e3

/-- **`e` sends the class of `κ` to the unit of `Ext⁰(ℚ_Y, ℚ_Y)`.** -/
theorem rationalExtEquiv_kappa :
    rationalExtEquiv Y 0 (Abelian.Ext.mk₀ (kappaSheaf Y)) = oneExt Y := by
  simp only [rationalExtEquiv, AddEquiv.trans_apply, extPostcompEquiv, extPrecompEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, extEquivQ, Iso.symm_hom, oneExt]
  rw [Abelian.Ext.mk₀_comp_mk₀, Adjunction.extEquiv_symm_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  congr 1
  rw [Iso.inv_comp_eq, Category.comp_id, Equiv.symm_apply_eq, ← adj_tensorQSheafInt_comp_forgetQX,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The unit of `H⁰(Y; ℚ)` is the class of `κ : ℤ_Y → ℚ_Y`.** -/
theorem oneY_eq_kappa : oneY Y = Abelian.Ext.mk₀ (kappaSheaf Y) := by
  rw [oneY, ← rationalExtEquiv_kappa, AddEquiv.symm_apply_apply]

/-- **Every class is `κ` followed by its endomorphism class.** -/
theorem eq_kappa_comp_forgetEnd {q : ℕ} (β : HQ Y q) :
    β = (Abelian.Ext.mk₀ (kappaSheaf Y)).comp (forgetEnd Y (rationalExtEquiv Y q β)) (zero_add q) := by
  rw [← oneY_eq_kappa]
  exact eq_oneY_comp_forgetEnd β

end HodgeLadder.Cup
