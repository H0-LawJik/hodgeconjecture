module

public import HodgeLadder.Cup.Pullback

/-!
# Products of supported classes with absolute classes

Rung `supported-cup` (front `cup`, decision 0009). Upstream's cohomology with support in `Z` is
`Extᵖ(ℤ[Y, Y ∖ Z], ℚ_Y)` in sheaves of abelian groups. An absolute class `β ∈ H^q(Y; ℚ)` gives,
through `rationalExtEquiv` and the exact forgetful functor, a class `lift β ∈ Ext^q(ℚ_Y, ℚ_Y)` of
abelian sheaves, and `α ∪ β := α ≫ lift β`. Composition with `lift` matches the cup product
(`rationalExtEquiv_comp_lift`, from `extEquiv_symm_naturality_right`), so the product is
associative with the cup product, unital, biadditive, and natural in the source object. In
particular forgetting the support is compatible with the product.

## Main definitions

* `HodgeLadder.Cup.liftAb`, `HodgeLadder.Cup.supCupY`

## Main results

* `HodgeLadder.Cup.rationalExtEquiv_comp_lift`, `supCupY_assoc`, `supCupY_oneY`,
  `comp_supCupY`, `supCupY_eq_cupY`
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}}

/-- A rational `Ext` class seen in sheaves of abelian groups. -/
def liftAb {q : ℕ} (b : Abelian.Ext.{0} (QX Y) (QX Y) q) :
    Abelian.Ext.{0} (constAb Y (AddCommGrpCat.of ℚ)) (constAb Y (AddCommGrpCat.of ℚ)) q :=
  conjExt (forgetSheaf Y) (forgetQX Y) b

lemma liftAb_comp {p q n : ℕ} (b : Abelian.Ext.{0} (QX Y) (QX Y) p)
    (b' : Abelian.Ext.{0} (QX Y) (QX Y) q) (h : p + q = n) :
    liftAb (b.comp b' h) = (liftAb b).comp (liftAb b') h := conjExt_comp _ _ _ _ h

lemma liftAb_one : liftAb (oneExt Y) = Abelian.Ext.mk₀ (𝟙 _) := conjExt_id _ _

/-- **Composing with a lifted class is the cup product**, on the `ℚ` side. -/
theorem rationalExtEquiv_comp_lift {p q n : ℕ} (a : HQ Y p)
    (b : Abelian.Ext.{0} (QX Y) (QX Y) q) (h : p + q = n) :
    rationalExtEquiv Y n (a.comp (liftAb b) h) = (rationalExtEquiv Y p a).comp b h := by
  have key : (a.comp (liftAb b) h).comp (Abelian.Ext.mk₀ (forgetQX Y).inv) (add_zero n) =
      (a.comp (Abelian.Ext.mk₀ (forgetQX Y).inv) (add_zero p)).comp
        (b.mapExactFunctor (forgetSheaf Y)) h := by
    unfold liftAb conjExt
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
      ← Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (forgetQX Y).inv) _ _ (zero_add q) (add_zero q)
        (by omega),
      Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Abelian.Ext.comp_mk₀_id]
    exact (Abelian.Ext.comp_assoc _ _ _ (add_zero p) (zero_add q) (by omega)).symm
  show (Abelian.Ext.mk₀ (tensorQSheafInt Y).inv).comp ((extEquivQ Y _ (QX Y) n).symm
      ((a.comp (liftAb b) h).comp (Abelian.Ext.mk₀ (forgetQX Y).inv) (add_zero n))) (zero_add n) =
    ((Abelian.Ext.mk₀ (tensorQSheafInt Y).inv).comp ((extEquivQ Y _ (QX Y) p).symm
      (a.comp (Abelian.Ext.mk₀ (forgetQX Y).inv) (add_zero p))) (zero_add p)).comp b h
  rw [key, extEquivQ, (adjQSheaf Y).extEquiv_symm_naturality_right]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add p) h (by omega)).symm

/-- The lift of an absolute class to `Ext^q(ℚ_Y, ℚ_Y)` in sheaves of abelian groups. -/
abbrev liftH {q : ℕ} (β : HQ Y q) :
    Abelian.Ext.{0} (constAb Y (AddCommGrpCat.of ℚ)) (constAb Y (AddCommGrpCat.of ℚ)) q :=
  liftAb (rationalExtEquiv Y q β)

/-- **The product** of a class with source `P` (for instance a supported class, `P` the pair
sheaf) and an absolute class. -/
def supCupY {P : Sheaf (J Y) AddCommGrpCat.{0}} {p q : ℕ}
    (α : Abelian.Ext.{0} P (constAb Y (AddCommGrpCat.of ℚ)) p) (β : HQ Y q) (n : ℕ)
    (h : p + q = n) : Abelian.Ext.{0} P (constAb Y (AddCommGrpCat.of ℚ)) n :=
  α.comp (liftH β) h

variable {P : Sheaf (J Y) AddCommGrpCat.{0}}

/-- On absolute classes the product is the cup product. -/
theorem supCupY_eq_cupY {p q : ℕ} (a : HQ Y p) (β : HQ Y q) (n : ℕ) (h : p + q = n) :
    supCupY a β n h = cupY a β n h := by
  apply (rationalExtEquiv Y n).injective
  rw [rationalExtEquiv_cupY]
  exact rationalExtEquiv_comp_lift a _ h

/-- Associativity with the cup product. -/
theorem supCupY_assoc {p q r : ℕ} (α : Abelian.Ext.{0} P (constAb Y (AddCommGrpCat.of ℚ)) p)
    (β : HQ Y q) (γ : HQ Y r) (n : ℕ) (h : p + q + r = n) :
    supCupY (supCupY α β (p + q) rfl) γ n h = supCupY α (cupY β γ (q + r) rfl) n (by omega) := by
  unfold supCupY liftH
  rw [rationalExtEquiv_cupY, liftAb_comp]
  exact Abelian.Ext.comp_assoc _ _ _ rfl rfl (by omega)

/-- The unit acts trivially. -/
theorem supCupY_oneY {p : ℕ} (α : Abelian.Ext.{0} P (constAb Y (AddCommGrpCat.of ℚ)) p) :
    supCupY α (oneY Y) p (add_zero p) = α := by
  unfold supCupY liftH oneY
  rw [AddEquiv.apply_symm_apply, liftAb_one]
  exact Abelian.Ext.comp_mk₀_id α

/-- Naturality in the source: precomposition commutes with the product. -/
theorem comp_supCupY {P' : Sheaf (J Y) AddCommGrpCat.{0}} {k p q : ℕ}
    (u : Abelian.Ext.{0} P' P k) (α : Abelian.Ext.{0} P (constAb Y (AddCommGrpCat.of ℚ)) p)
    (β : HQ Y q) (n : ℕ) (h : k + p + q = n) :
    u.comp (supCupY α β (p + q) rfl) (by omega) = supCupY (u.comp α rfl) β n h := by
  unfold supCupY
  exact (Abelian.Ext.comp_assoc _ _ _ rfl rfl (by omega)).symm

/-- Naturality in the source, for a degree-zero map. -/
theorem comp_supCupY₀ {P' : Sheaf (J Y) AddCommGrpCat.{0}} {p q : ℕ}
    (u : Abelian.Ext.{0} P' P 0) (α : Abelian.Ext.{0} P (constAb Y (AddCommGrpCat.of ℚ)) p)
    (β : HQ Y q) (n : ℕ) (h : p + q = n) :
    u.comp (supCupY α β n h) (zero_add n) = supCupY (u.comp α (zero_add p)) β n h := by
  unfold supCupY
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add p) h (by omega)).symm

theorem add_supCupY {p q : ℕ} (α α' : Abelian.Ext.{0} P (constAb Y (AddCommGrpCat.of ℚ)) p)
    (β : HQ Y q) (n : ℕ) (h : p + q = n) :
    supCupY (α + α') β n h = supCupY α β n h + supCupY α' β n h :=
  Abelian.Ext.add_comp _ _ _ _

theorem supCupY_add {p q : ℕ} (α : Abelian.Ext.{0} P (constAb Y (AddCommGrpCat.of ℚ)) p)
    (β β' : HQ Y q) (n : ℕ) (h : p + q = n) :
    supCupY α (β + β') n h = supCupY α β n h + supCupY α β' n h := by
  unfold supCupY liftH
  rw [map_add]
  have : liftAb (rationalExtEquiv Y q β + rationalExtEquiv Y q β') =
      liftAb (rationalExtEquiv Y q β) + liftAb (rationalExtEquiv Y q β') := conjExt_add _ _ _ _
  rw [this]
  exact Abelian.Ext.comp_add _ _ _ _

end HodgeLadder.Cup
