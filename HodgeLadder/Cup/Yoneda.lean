module

public import HodgeLadder.Cup.SheafExact

/-!
# The Yoneda cup product on rational sheaf cohomology of a space

For a topological space `Y`, `Hⁿ(Y; ℚ) = Sheaf.H ℚ_Y n` carries the product transported from
Yoneda composition on `Ext^*(ℚ_Y, ℚ_Y)` in sheaves of `ℚ`-vector spaces (`rationalExtEquiv`):
`α ∪ β` is `α` followed by `β` (Mathlib's `Ext.comp`). Associative, unital, biadditive. Part of
rung `cup-product`.

## Main definitions

* `HodgeLadder.Cup.cupY`, `HodgeLadder.Cup.oneY`

## Main results

* `HodgeLadder.Cup.cupY_assoc`, `oneY_cupY`, `cupY_oneY`, `add_cupY`, `cupY_add`
-/

@[expose] public noncomputable section

open CategoryTheory

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}}

/-- Rational sheaf cohomology of `Y` in degree `n`. -/
abbrev HQ (Y : TopCat.{0}) (n : ℕ) := Sheaf.H.{0} (constAb Y (AddCommGrpCat.of ℚ)) n

/-- The cup product `α ∪ β ∈ Hⁿ` for `α ∈ Hᵖ`, `β ∈ H^q`, `p + q = n`. -/
def cupY {p q : ℕ} (α : HQ Y p) (β : HQ Y q) (n : ℕ) (h : p + q = n) : HQ Y n :=
  (rationalExtEquiv Y n).symm ((rationalExtEquiv Y p α).comp (rationalExtEquiv Y q β) h)

lemma rationalExtEquiv_cupY {p q : ℕ} (α : HQ Y p) (β : HQ Y q) (n : ℕ) (h : p + q = n) :
    rationalExtEquiv Y n (cupY α β n h) =
      (rationalExtEquiv Y p α).comp (rationalExtEquiv Y q β) h :=
  AddEquiv.apply_symm_apply _ _

variable (Y) in
/-- The unit class in `H⁰(Y; ℚ)`. -/
def oneY : HQ Y 0 := (rationalExtEquiv Y 0).symm (oneExt Y)

theorem cupY_assoc {p q r : ℕ} (α : HQ Y p) (β : HQ Y q) (γ : HQ Y r) (n : ℕ)
    (h : p + q + r = n) :
    cupY (cupY α β (p + q) rfl) γ n h = cupY α (cupY β γ (q + r) rfl) n (by omega) := by
  apply (rationalExtEquiv Y n).injective
  rw [rationalExtEquiv_cupY, rationalExtEquiv_cupY, rationalExtEquiv_cupY,
    rationalExtEquiv_cupY]
  exact Abelian.Ext.comp_assoc _ _ _ rfl rfl (by omega)

theorem oneY_cupY {p : ℕ} (α : HQ Y p) : cupY (oneY Y) α p (zero_add p) = α := by
  apply (rationalExtEquiv Y p).injective
  rw [rationalExtEquiv_cupY, oneY, AddEquiv.apply_symm_apply]
  exact oneExt_comp Y _

theorem cupY_oneY {p : ℕ} (α : HQ Y p) : cupY α (oneY Y) p (add_zero p) = α := by
  apply (rationalExtEquiv Y p).injective
  rw [rationalExtEquiv_cupY, oneY, AddEquiv.apply_symm_apply]
  exact comp_oneExt Y _

theorem add_cupY {p q : ℕ} (α α' : HQ Y p) (β : HQ Y q) (n : ℕ) (h : p + q = n) :
    cupY (α + α') β n h = cupY α β n h + cupY α' β n h := by
  apply (rationalExtEquiv Y n).injective
  rw [map_add, rationalExtEquiv_cupY, rationalExtEquiv_cupY, rationalExtEquiv_cupY, map_add]
  exact Abelian.Ext.add_comp _ _ _ _

theorem cupY_add {p q : ℕ} (α : HQ Y p) (β β' : HQ Y q) (n : ℕ) (h : p + q = n) :
    cupY α (β + β') n h = cupY α β n h + cupY α β' n h := by
  apply (rationalExtEquiv Y n).injective
  rw [map_add, rationalExtEquiv_cupY, rationalExtEquiv_cupY, rationalExtEquiv_cupY, map_add]
  exact Abelian.Ext.comp_add _ _ _ _

end HodgeLadder.Cup
