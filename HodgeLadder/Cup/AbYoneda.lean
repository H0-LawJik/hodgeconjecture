module

public import HodgeLadder.Cup.Yoneda

/-!
# The Yoneda cup product read in sheaves of abelian groups

Part of rung `ab-ext-yoneda` (front `cup`). `Hⁿ(Y; ℚ)` is `Extⁿ(ℤ_Y, ℚ_Y)` in sheaves of
abelian groups, while the cup product `cupY` is Yoneda composition in `Ext^*(ℚ_Y, ℚ_Y)` over
sheaves of `ℚ`-vector spaces. Forgetting the `ℚ`-structure sends a class `y` of
`Ext^q(ℚ_Y, ℚ_Y)` to an endomorphism class `forgetEnd y` of `ℚ_Y` in abelian groups. Then
`cupY α β = α ≫ forgetEnd (e β)`: the cup product is `α` followed by `β`'s endomorphism class,
all in abelian groups. In particular `β = 1 ≫ forgetEnd (e β)`.

## Main definitions

* `HodgeLadder.Cup.forgetEnd`

## Main results

* `HodgeLadder.Cup.rationalExtEquiv_comp_forgetEnd`, `HodgeLadder.Cup.cupY_eq_comp_forgetEnd`,
  `HodgeLadder.Cup.eq_oneY_comp_forgetEnd`
-/

@[expose] public noncomputable section

open CategoryTheory

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}}

variable (Y) in
/-- The endomorphism class of `ℚ_Y`, in sheaves of abelian groups, of a class of
`Ext^q(ℚ_Y, ℚ_Y)` over `ℚ`-vector spaces: forget the `ℚ`-structure and conjugate by
`forgetQX`. -/
def forgetEnd {q : ℕ} (y : Abelian.Ext.{0} (QX Y) (QX Y) q) :
    Abelian.Ext.{0} (constAb Y (AddCommGrpCat.of ℚ)) (constAb Y (AddCommGrpCat.of ℚ)) q :=
  (Abelian.Ext.mk₀ (forgetQX Y).inv).comp
    ((y.mapExactFunctor (forgetSheaf Y)).comp (Abelian.Ext.mk₀ (forgetQX Y).hom) (add_zero q))
    (zero_add q)

/-- **`e` of `α` followed by `forgetEnd y` is `e α` followed by `y`.** -/
theorem rationalExtEquiv_comp_forgetEnd {p q : ℕ} (α : HQ Y p)
    (y : Abelian.Ext.{0} (QX Y) (QX Y) q) (n : ℕ) (h : p + q = n) :
    rationalExtEquiv Y n (α.comp (forgetEnd Y y) h) = (rationalExtEquiv Y p α).comp y h := by
  have hU : ((forgetEnd Y y).comp (Abelian.Ext.mk₀ (forgetQX Y).inv) (add_zero q)) =
      (Abelian.Ext.mk₀ (forgetQX Y).inv).comp (y.mapExactFunctor (forgetSheaf Y)) (zero_add q) := by
    rw [forgetEnd, Abelian.Ext.comp_assoc_of_third_deg_zero,
      Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Abelian.Ext.comp_mk₀_id]
  have hA : (α.comp (forgetEnd Y y) h).comp (Abelian.Ext.mk₀ (forgetQX Y).inv) (add_zero n) =
      (α.comp (Abelian.Ext.mk₀ (forgetQX Y).inv) (add_zero p)).comp
        (y.mapExactFunctor (forgetSheaf Y)) h := by
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, hU, Abelian.Ext.comp_assoc_of_second_deg_zero]
  simp only [rationalExtEquiv, AddEquiv.trans_apply, extPostcompEquiv, extPrecompEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, extEquivQ, Iso.symm_hom]
  rw [hA, Adjunction.extEquiv_symm_naturality_right,
    ← Abelian.Ext.comp_assoc _ _ _ (zero_add p) h (by omega)]

/-- **The cup product in sheaves of abelian groups**: `α ∪ β` is `α` followed by the
endomorphism class of `β`. -/
theorem cupY_eq_comp_forgetEnd {p q : ℕ} (α : HQ Y p) (β : HQ Y q) (n : ℕ) (h : p + q = n) :
    cupY α β n h = α.comp (forgetEnd Y (rationalExtEquiv Y q β)) h := by
  apply (rationalExtEquiv Y n).injective
  rw [rationalExtEquiv_cupY, rationalExtEquiv_comp_forgetEnd]

/-- Every class is the unit followed by its endomorphism class. -/
theorem eq_oneY_comp_forgetEnd {q : ℕ} (β : HQ Y q) :
    β = (oneY Y).comp (forgetEnd Y (rationalExtEquiv Y q β)) (zero_add q) := by
  rw [← cupY_eq_comp_forgetEnd, oneY_cupY]

end HodgeLadder.Cup
