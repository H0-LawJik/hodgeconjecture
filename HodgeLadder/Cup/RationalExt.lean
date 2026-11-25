module

public import HodgeLadder.Cup.SheafExact
public import HodgeConjecture.Statement

/-!
# Rational cohomology as `Ext` of a rational constant sheaf

Rung `rational-ext-equiv` (front `cup`, decision 0008). For a complex scheme `X`, upstream's
`H^n(X; ℚ)` is `Extⁿ(ℤ_X, ℚ_X)` in sheaves of abelian groups on `X(ℂ)`. It is identified with
`Extⁿ(ℚ_X, ℚ_X)` in sheaves of `ℚ`-vector spaces, where Yoneda composition is associative, unital
and bilinear.

## Main results

* `HodgeLadder.Cup.rationalCohomologyEquivExt`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Cup

variable (X : Over (Spec ↧ℂ))

/-- The constant sheaf `ℚ` of `ℚ`-vector spaces on `X(ℂ)`. -/
abbrev rationalSheaf : Sheaf (J ↧(ComplexPoint X)) (ModuleCat.{0} ℚ) := QX ↧(ComplexPoint X)

/-- **`H^n(X; ℚ) ≅ Extⁿ(ℚ_X, ℚ_X)`** in sheaves of `ℚ`-vector spaces on `X(ℂ)`. -/
def rationalCohomologyEquivExt (n : ℕ) :
    H^n(X; ℚ) ≃+ Abelian.Ext.{0} (rationalSheaf X) (rationalSheaf X) n :=
  rationalExtEquiv ↧(ComplexPoint X) n

end HodgeLadder.Cup
