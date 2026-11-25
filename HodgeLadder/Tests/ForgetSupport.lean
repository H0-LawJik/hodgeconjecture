module

public import HodgeConjecture.Statement

/-!
# Forgetting support is controlled by the cohomology of the open complement

Let `X` be a scheme over `ℂ`, `Z ⊆ X(ℂ)` closed and `U = X(ℂ) ∖ Z`. Upstream defines rational
cohomology with support, `H_[Z]^n(X; ℚ)`, as the cohomology of the pair `(X(ℂ), U)` (an `Ext`
group out of the pair sheaf `ℤ[X, U]`), and `forgetSupport` as the map of the long exact sequence
of that pair into `H^n(X; ℚ)`. The neighbouring terms of the sequence are `H^{n-1}(U; ℚ_X)` and
`H^n(U; ℚ_X)`, the cohomology of the open `U` in Mathlib's sense (`Sheaf.H'`). This file reads off
the two consequences used to compute cycle classes in positive codimension:

* if `H^n(U; ℚ_X) = 0`, then `forgetSupport` is injective in degree `n + 1`;
* if `H^n(U; ℚ_X) = 0`, then `forgetSupport` is surjective in degree `n`.

The class of a codimension-`p` subvariety is `forgetSupport` of its supported class
(`cycleComponentSheafClass_eq_forgetSupport` upstream), so the first statement turns nonvanishing
of the supported class, which upstream proves for every component, into nonvanishing of the cycle
class, once the complement has no cohomology in degree `2p - 1`. This is step (c) of the plan in
`docs/sketches/projective-space-test.md`: on `ℙ¹` with `Z` a point, `U ≅ ℂ`.

## Main results

* `HodgeLadder.Tests.forgetSupport_injective_of_subsingleton`
* `HodgeLadder.Tests.forgetSupport_surjective_of_subsingleton`
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry ComplexPoint TopologicalSpace Abelian

set_option linter.auxLemma false

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Tests

variable (X : Over (Spec ↧ℂ)) (Z : Closeds (ComplexPoint X))

/-- If the rational cohomology of the open complement `X(ℂ) ∖ Z` vanishes in degree `n`, then
forgetting the support `Z` is injective on `H_[Z]^{n+1}(X; ℚ)`. Exactness of the pair sequence
`H^n(X(ℂ) ∖ Z) → H_[Z]^{n+1}(X) → H^{n+1}(X)` at the middle term. -/
theorem forgetSupport_injective_of_subsingleton (n : ℕ)
    (h : Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) n Z.compl)) :
    Function.Injective (forgetSupport ℚ X Z (n + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  unfold forgetSupport at hx
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.map_eq_zero_iff] at hx
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ (Sheaf.pairShortComplex_shortExact _) _ x hx
    (add_comm 1 n)
  have hy0 : y = 0 := @Subsingleton.elim _ h y 0
  rw [← hy, hy0, Ext.comp_zero]

/-- If the rational cohomology of the open complement `X(ℂ) ∖ Z` vanishes in degree `n`, then
every class in `H^n(X; ℚ)` comes from `H_[Z]^n(X; ℚ)`. Exactness of the pair sequence
`H_[Z]^n(X) → H^n(X) → H^n(X(ℂ) ∖ Z)` at the middle term. -/
theorem forgetSupport_surjective_of_subsingleton (n : ℕ)
    (h : Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) n Z.compl)) :
    Function.Surjective (forgetSupport ℚ X Z n) := by
  intro x
  obtain ⟨x', rfl⟩ := (Sheaf.H'.addEquivTerminal isTerminalTop _ n).surjective x
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₂ (Sheaf.pairShortComplex_shortExact
    (homOfLE (le_top : Z.compl ≤ ⊤))) _ x' (@Subsingleton.elim _ h _ 0)
  refine ⟨y, ?_⟩
  unfold forgetSupport
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  congr 1

end HodgeLadder.Tests
