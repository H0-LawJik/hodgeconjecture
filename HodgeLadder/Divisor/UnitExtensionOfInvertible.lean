module

public import HodgeLadder.Divisor.AnalyticInvertible
public import HodgeLadder.Line.OfInvertible

/-!
# Every invertible sheaf comes from a holomorphic unit extension

Rung `unit-extension-of-invertible`. For an invertible sheaf `L` on a smooth projective integral
complex scheme `X`, the analytification `L^an` is invertible (part A), so it has a holomorphic
trivializing cover; the unit extension `E` of that cover has section sheaf `L^an` (part B).

## Main results

* `HodgeLadder.exists_unitExtension_of_isInvertible`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- **The analytification of an invertible sheaf is the section sheaf of a holomorphic unit
extension.** -/
theorem exists_unitExtension_of_isInvertible (L : X.left.Modules)
    [TauCeti.SheafOfModules.IsInvertible.{0} L] :
    ∃ E : HolomorphicUnitExtension X (TopologicalSpace.dim X.left),
      Nonempty ((moduleAnalytification X (TopologicalSpace.dim X.left)).obj L ≅
        E.sectionSheafOfModules) := by
  obtain ⟨T⟩ := nonempty_holomorphicTrivializingCover_moduleAnalytification X L
  exact ⟨TCover.unitExtension T, ⟨TCover.sectionIso T⟩⟩

end HodgeLadder
