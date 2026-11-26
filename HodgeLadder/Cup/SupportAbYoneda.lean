module

public import HodgeLadder.Cup.Supported
public import HodgeLadder.Cup.AbYoneda

/-!
# The supported cup product read in sheaves of abelian groups

Rung `support-ab-yoneda` (front `cup`, part of the supported comparison). The product of a class
with source `P` (a supported class, `P` the pair sheaf) and an absolute class `β` is the class
followed by `forgetEnd (e β)`, the endomorphism class of `β` in sheaves of abelian groups
(`ab-ext-yoneda`): `liftAb` and `forgetEnd` are the same conjugation.

## Main results

* `HodgeLadder.Cup.liftAb_eq_forgetEnd`, `HodgeLadder.Cup.supCupY_eq_comp_forgetEnd`
-/

@[expose] public noncomputable section

open CategoryTheory

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}}

lemma liftAb_eq_forgetEnd {q : ℕ} (b : Abelian.Ext.{0} (QX Y) (QX Y) q) :
    liftAb b = forgetEnd Y b := rfl

/-- **The supported cup product in sheaves of abelian groups.** -/
theorem supCupY_eq_comp_forgetEnd {P : Sheaf (J Y) AddCommGrpCat.{0}} {p q : ℕ}
    (α : Abelian.Ext.{0} P (constAb Y (AddCommGrpCat.of ℚ)) p) (β : HQ Y q) (n : ℕ)
    (h : p + q = n) :
    supCupY α β n h = α.comp (forgetEnd Y (rationalExtEquiv Y q β)) h := rfl

end HodgeLadder.Cup
