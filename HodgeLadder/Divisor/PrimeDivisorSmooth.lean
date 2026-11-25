module

public import HodgeLadder.Divisor.PrimeDivisorCartier
public import HodgeLadder.Divisor.LocalFactoriality
public import LefschetzPort.AlgebraicGeometry.ComplexPointClosedPointEquiv

/-!
# Prime divisors on smooth projective complex varieties are Cartier

The ideal sheaf of every prime divisor `D` on a smooth projective integral complex scheme is
invertible and is represented by Cartier data with divisor `-D`. This specializes
`HodgeLadder.exists_primeDivisor_cartierData`: the scheme is Noetherian and Jacobson, and its
local rings at closed points (the images of complex points) are UFDs by `local-factoriality`.
Rung `prime-divisor-ideal-sheaf`.

## Main results

* `HodgeLadder.exists_primeDivisor_cartierData_of_smoothProjective`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint Order

namespace HodgeLadder

attribute [local instance] isNoetherian_of_isProjective

/-- **Prime divisors are Cartier.** On a smooth projective integral complex scheme, the vanishing
ideal sheaf of `D = closure {ξ}` (`coheight ξ = 1`) is invertible and is represented by Cartier
data with divisor `-D`. -/
theorem exists_primeDivisor_cartierData_of_smoothProjective (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {ξ : X.left} (hξ : coheight ξ = 1) :
    TauCeti.SheafOfModules.IsInvertible.{0} (vanishingIdealSheaf (closure ({ξ} : Set X.left))) ∧
      ∃ c : X.left.CartierData, c.Represents (vanishingIdealSheaf (closure ({ξ} : Set X.left))) ∧
        c.divisor = codimensionCycleSubgroup.single ξ hξ (-1) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  refine exists_primeDivisor_cartierData hξ fun q hq => ?_
  obtain ⟨z, hz⟩ := (complexPointEquivClosedPoint X).surjective ⟨q, hq⟩
  have h := uniqueFactorizationMonoid_stalk_complexPoint X z
  have hzq : (analytificationToPresheafedSpace X (TopologicalSpace.dim X.left)).base z = q :=
    congrArg Subtype.val hz
  rw [hzq] at h
  exact h

end HodgeLadder
