module

public import HodgeLadder.Cup.Yoneda
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Functors

/-!
# Pullback of rational cohomology is multiplicative

Rung `cup-pullback` (front `cup`, decisions 0008 and 0009). For a continuous map `f : Y ⟶ X`, the
inverse image `f⁻¹` of sheaves of `ℚ`-vector spaces is exact and sends `ℚ_X` to `ℚ_Y`, so it
induces a map `Hⁿ(X; ℚ) → Hⁿ(Y; ℚ)` on `Ext^*(ℚ, ℚ)`, transported through `rationalExtEquiv`.
Exact functors are multiplicative on `Ext` (`Ext.mapExactFunctor_comp`), so the pullback respects
cup products and units.

## Main definitions

* `HodgeLadder.Cup.conjExt`, `HodgeLadder.Cup.pullbackQ`, `HodgeLadder.Cup.pullbackH`

## Main results

* `HodgeLadder.Cup.pullbackH_cupY`, `HodgeLadder.Cup.pullbackH_oneY`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace HodgeLadder.Cup

section Conj

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Abelian 𝒞] [Abelian 𝒟]
  [HasExt.{0} 𝒞] [HasExt.{0} 𝒟]
  (Φ : 𝒞 ⥤ 𝒟) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  {A : 𝒞} {B : 𝒟} (c : Φ.obj A ≅ B)

/-- An exact functor with `Φ A ≅ B` maps `Ext(A, A)` to `Ext(B, B)`. -/
def conjExt {n : ℕ} (x : Abelian.Ext.{0} A A n) : Abelian.Ext.{0} B B n :=
  (Abelian.Ext.mk₀ c.inv).comp ((x.mapExactFunctor Φ).comp (Abelian.Ext.mk₀ c.hom) (add_zero n))
    (zero_add n)

/-- **Conjugation by an exact functor is multiplicative.** -/
theorem conjExt_comp {p q n : ℕ} (x : Abelian.Ext.{0} A A p) (y : Abelian.Ext.{0} A A q)
    (h : p + q = n) :
    conjExt Φ c (x.comp y h) = (conjExt Φ c x).comp (conjExt Φ c y) h := by
  unfold conjExt
  rw [Abelian.Ext.mapExactFunctor_comp]
  rw [Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ c.inv) _ _ (zero_add p) (by omega) (by omega)]
  congr 1
  rw [Abelian.Ext.comp_assoc (x.mapExactFunctor Φ) (Abelian.Ext.mk₀ c.hom) _ (add_zero p)
    (zero_add q) (by omega)]
  rw [← Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ c.hom) (Abelian.Ext.mk₀ c.inv) _ (zero_add 0)
    (zero_add q) (by omega)]
  rw [Abelian.Ext.mk₀_comp_mk₀, c.hom_inv_id, Abelian.Ext.mk₀_id_comp]
  exact Abelian.Ext.comp_assoc _ _ _ h (add_zero q) (by omega)

/-- Conjugation sends the unit to the unit. -/
theorem conjExt_id : conjExt Φ c (Abelian.Ext.mk₀ (𝟙 A)) = Abelian.Ext.mk₀ (𝟙 B) := by
  unfold conjExt
  rw [Abelian.Ext.mapExactFunctor_mk₀, Φ.map_id, Abelian.Ext.mk₀_id_comp,
    Abelian.Ext.mk₀_comp_mk₀, c.inv_hom_id]

/-- Conjugation is additive. -/
theorem conjExt_add {n : ℕ} (x y : Abelian.Ext.{0} A A n) :
    conjExt Φ c (x + y) = conjExt Φ c x + conjExt Φ c y := by
  unfold conjExt
  rw [Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

end Conj

section Pullback

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

/-- The inverse image `f⁻¹` on sheaves of `ℚ`-vector spaces. -/
abbrev pullbackQ : Sheaf (J X) (ModuleCat.{0} ℚ) ⥤ Sheaf (J Y) (ModuleCat.{0} ℚ) :=
  TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f

instance : PreservesFiniteLimits (pullbackQ f) :=
  Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat _ _ _ _

instance : PreservesColimits (pullbackQ f) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).leftAdjoint_preservesColimits

instance : PreservesFiniteColimits (pullbackQ f) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

instance : (pullbackQ f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `f⁻¹ ℚ_X ≅ ℚ_Y`: both are left adjoint to global sections composed with constants. -/
def pullbackQX : (pullbackQ f).obj (QX X) ≅ QX Y :=
  (((constantSheafAdj (J X) (ModuleCat.{0} ℚ) isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)).leftAdjointUniq
      (constantSheafAdj (J Y) (ModuleCat.{0} ℚ) isTerminalTop)).app _

/-- **Pullback of rational cohomology** along a continuous map `f : Y ⟶ X`. -/
def pullbackH (n : ℕ) (α : HQ X n) : HQ Y n :=
  (rationalExtEquiv Y n).symm (conjExt (pullbackQ f) (pullbackQX f) (rationalExtEquiv X n α))

lemma rationalExtEquiv_pullbackH (n : ℕ) (α : HQ X n) :
    rationalExtEquiv Y n (pullbackH f n α) =
      conjExt (pullbackQ f) (pullbackQX f) (rationalExtEquiv X n α) :=
  AddEquiv.apply_symm_apply _ _

/-- **Pullback is multiplicative.** -/
theorem pullbackH_cupY {p q : ℕ} (α : HQ X p) (β : HQ X q) (n : ℕ) (h : p + q = n) :
    pullbackH f n (cupY α β n h) = cupY (pullbackH f p α) (pullbackH f q β) n h := by
  apply (rationalExtEquiv Y n).injective
  rw [rationalExtEquiv_pullbackH, rationalExtEquiv_cupY, rationalExtEquiv_cupY,
    rationalExtEquiv_pullbackH, rationalExtEquiv_pullbackH]
  exact conjExt_comp _ _ _ _ h

/-- Pullback sends the unit to the unit. -/
theorem pullbackH_oneY : pullbackH f 0 (oneY X) = oneY Y := by
  apply (rationalExtEquiv Y 0).injective
  rw [rationalExtEquiv_pullbackH, oneY, oneY, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  exact conjExt_id _ _

/-- Pullback is additive. -/
theorem pullbackH_add (n : ℕ) (α β : HQ X n) :
    pullbackH f n (α + β) = pullbackH f n α + pullbackH f n β := by
  apply (rationalExtEquiv Y n).injective
  rw [map_add, rationalExtEquiv_pullbackH, rationalExtEquiv_pullbackH, rationalExtEquiv_pullbackH,
    map_add]
  exact conjExt_add _ _ _ _

end Pullback

end HodgeLadder.Cup
