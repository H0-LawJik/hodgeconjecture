module

public import HodgeLadder.Divisor.UnitExtensionOfInvertible
public import HodgeLadder.Divisor.PrimeDivisorSmooth
public import HodgeLadder.Hodge.ChernClasses
public import HodgeLadder.Lefschetz.OneOne
public import HodgeLadder.CycleClass.Statements
public import Other.AlgebraicGeometry.Cycle.SheafClass

/-!
# Lefschetz (1,1) as an equality

Rung `prime-divisors-cartier`, closing `lefschetz-1-1-equality`. For a prime divisor `D` with
generic point `ξ` on a smooth projective complex variety `X`, the ideal sheaf `𝓘_D` is invertible
and represented by Cartier data with divisor `−D` (`prime-divisor-ideal-sheaf`); its
analytification is the section sheaf of a holomorphic unit extension
(`unit-extension-of-invertible`); so the class of `−D` is a Hodge class
(`chern-classes-are-hodge`), hence so is the class of `D`. The classes of prime divisors span
`algebraicCycleClassSpan X 1`, which gives the known half in codimension one, and with
`lefschetzOneOne_holds` the equality `Hdg^1(X; ℚ) = algebraicCycleClassSpan X 1`.

## Main results

* `HodgeLadder.cycleComponentSheafClass_mem_hodgeClasses_one`
* `HodgeLadder.cycleClassesAreHodgeOne_holds`
* `HodgeLadder.lefschetzOneOneEquality_holds`
-/

@[expose] public noncomputable section

open CategoryTheory Order AlgebraicGeometry ComplexPoint

namespace HodgeLadder

/-- The class of a prime divisor is a rational Hodge class. -/
theorem cycleComponentSheafClass_mem_hodgeClasses_one (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (ξ : X.left) (hξ : coheight ξ = 1) :
    cycleComponentSheafClass X ξ hξ ∈ Hdg^1(X; ℚ) := by
  obtain ⟨hL, c, hc, hdiv⟩ := exists_primeDivisor_cartierData_of_smoothProjective X hξ
  obtain ⟨E, ⟨e⟩⟩ := exists_unitExtension_of_isInvertible X
    (vanishingIdealSheaf (closure ({ξ} : Set X.left)))
  have h := sheafCycleClassOnCycles_divisor_mem_hodgeClasses X E _ hL e c hc
  rw [hdiv] at h
  erw [sheafCycleClassOnCycles_single] at h
  have h' := neg_mem h
  rw [neg_smul, neg_neg, one_smul] at h'
  exact h'

/-- **The known half in codimension one**: classes of divisors are Hodge classes. -/
theorem cycleClassesAreHodgeOne_holds : CycleClassesAreHodgeOne := by
  intro X _ _ _
  apply sSup_le
  rintro _ ⟨x, hx, rfl⟩
  exact Submodule.span_le.mpr
    (Set.singleton_subset_iff.mpr (cycleComponentSheafClass_mem_hodgeClasses_one X x hx))

/-- **Lefschetz (1,1) as an equality**: the rational Hodge classes of degree two are exactly the
ℚ-span of the classes of prime divisors. -/
theorem lefschetzOneOneEquality_holds : LefschetzOneOneEquality :=
  lefschetzOneOneEquality_iff.mpr ⟨lefschetzOneOne_holds, cycleClassesAreHodgeOne_holds⟩

end HodgeLadder
