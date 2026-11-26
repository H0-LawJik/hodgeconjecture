module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Transport of `Ext` groups along isomorphisms

For an abelian category `C` with `Ext` groups, an isomorphism `X ≅ Y` of sources or `Y ≅ Z` of
targets induces an additive bijection of `Ext` groups in every degree, by composition with the
degree-zero class of the isomorphism. The names follow Mathlib's `ShiftedHom.precompIsoEquiv`
and `ShiftedHom.postcompIsoEquiv`. Used for `Ext` groups of sheaves on the front `cup`
(`HodgeLadder.Cup.extPrecompEquiv`, `HodgeLadder.Cup.extPostcompEquiv` are the universe-`0`
cases).

## Main definitions

* `HodgeLadder.Ext.precompIsoAddEquiv`, `HodgeLadder.Ext.postcompIsoAddEquiv`
-/

@[expose] public noncomputable section

open CategoryTheory Abelian

namespace HodgeLadder.Ext

universe w

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]

/-- The additive bijection `Ext Y Z n ≃+ Ext X Z n` induced by an isomorphism `X ≅ Y`:
precomposition with the degree-zero class of `e.hom`. -/
@[simps]
def precompIsoAddEquiv {X Y : C} (e : X ≅ Y) (Z : C) (n : ℕ) :
    Abelian.Ext.{w} Y Z n ≃+ Abelian.Ext.{w} X Z n where
  toFun α := (Abelian.Ext.mk₀ e.hom).comp α (zero_add n)
  invFun α := (Abelian.Ext.mk₀ e.inv).comp α (zero_add n)
  left_inv α := by
    simp only
    rw [← Abelian.Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega),
      Abelian.Ext.mk₀_comp_mk₀, e.inv_hom_id, Abelian.Ext.mk₀_id_comp]
  right_inv α := by
    simp only
    rw [← Abelian.Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega),
      Abelian.Ext.mk₀_comp_mk₀, e.hom_inv_id, Abelian.Ext.mk₀_id_comp]
  map_add' α β := Abelian.Ext.comp_add _ _ _ _

/-- The additive bijection `Ext X Y n ≃+ Ext X Z n` induced by an isomorphism `Y ≅ Z`:
postcomposition with the degree-zero class of `e.hom`. -/
@[simps]
def postcompIsoAddEquiv {Y Z : C} (e : Y ≅ Z) (X : C) (n : ℕ) :
    Abelian.Ext.{w} X Y n ≃+ Abelian.Ext.{w} X Z n where
  toFun α := α.comp (Abelian.Ext.mk₀ e.hom) (add_zero n)
  invFun α := α.comp (Abelian.Ext.mk₀ e.inv) (add_zero n)
  left_inv α := by
    simp only
    rw [Abelian.Ext.comp_assoc _ _ _ (add_zero n) (add_zero 0) (by omega),
      Abelian.Ext.mk₀_comp_mk₀, e.hom_inv_id, Abelian.Ext.comp_mk₀_id]
  right_inv α := by
    simp only
    rw [Abelian.Ext.comp_assoc _ _ _ (add_zero n) (add_zero 0) (by omega),
      Abelian.Ext.mk₀_comp_mk₀, e.inv_hom_id, Abelian.Ext.comp_mk₀_id]
  map_add' α β := Abelian.Ext.add_comp _ _ _ _

/-- The inverse of `precompIsoAddEquiv e` is `precompIsoAddEquiv e.symm`. -/
lemma precompIsoAddEquiv_symm {X Y : C} (e : X ≅ Y) (Z : C) (n : ℕ) :
    (precompIsoAddEquiv.{w} e Z n).symm = precompIsoAddEquiv.{w} e.symm Z n :=
  rfl

/-- The inverse of `postcompIsoAddEquiv e` is `postcompIsoAddEquiv e.symm`. -/
lemma postcompIsoAddEquiv_symm {Y Z : C} (e : Y ≅ Z) (X : C) (n : ℕ) :
    (postcompIsoAddEquiv.{w} e X n).symm = postcompIsoAddEquiv.{w} e.symm X n :=
  rfl

end HodgeLadder.Ext
