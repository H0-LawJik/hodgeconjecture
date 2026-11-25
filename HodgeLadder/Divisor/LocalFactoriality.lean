module

public import HodgeLadder.Algebra.UFDDescent
public import HodgeLadder.Divisor.AnalyticStalk
public import LefschetzPort.AlgebraicGeometry.HolomorphicAnalytificationComparison
public import LefschetzPort.AlgebraicGeometry.HolomorphicAnalytificationLocalIso

/-!
# Local rings of a smooth projective complex variety are UFDs

At the image of a complex point `z`, the local ring `𝒪_{X,z}` maps faithfully flatly to the
stalk of holomorphic functions at `z` (`faithfullyFlat_stalkMap_holomorphicAnalytificationπ`,
from the stack, through Oka's local GAGA). That stalk is a UFD (`HodgeLadder.Divisor.AnalyticStalk`),
so `𝒪_{X,z}` is a UFD by `HodgeLadder.uniqueFactorizationMonoid_of_faithfullyFlat`. Rung
`local-factoriality` (`docs/sketches/prime-divisors-cartier.md`).

## Main results

* `HodgeLadder.uniqueFactorizationMonoid_stalk_complexPoint`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

/-- **Local factoriality at complex points.** The local ring of `X` at the image of a complex
point is a UFD. -/
theorem uniqueFactorizationMonoid_stalk_complexPoint (z : ComplexPoint X) :
    UniqueFactorizationMonoid
      (X.left.presheaf.stalk ((analytificationToPresheafedSpace X (TopologicalSpace.dim X.left)).base z)) := by
  let f : X.left.presheaf.stalk ((analytificationToPresheafedSpace X (TopologicalSpace.dim X.left)).base z) →+*
      (holomorphicLocallyRingedSpace X (TopologicalSpace.dim X.left)).presheaf.stalk z :=
    CommRingCat.Hom.hom ((analytificationToPresheafedSpace X (TopologicalSpace.dim X.left)).stalkMap z)
  have hff : f.FaithfullyFlat := faithfullyFlat_stalkMap_holomorphicAnalytificationπ X _ z
  algebraize [f]
  have : Module.FaithfullyFlat _ _ := hff
  have := isDomain_holomorphicStalk X (TopologicalSpace.dim X.left) z
  have : IsLocalRing ((holomorphicLocallyRingedSpace X (TopologicalSpace.dim X.left)).presheaf.stalk z) :=
    (holomorphicLocallyRingedSpace X (TopologicalSpace.dim X.left)).isLocalRing z
  have := uniqueFactorizationMonoid_holomorphicStalk X (TopologicalSpace.dim X.left) z
  exact uniqueFactorizationMonoid_of_faithfullyFlat
    (B := (holomorphicLocallyRingedSpace X (TopologicalSpace.dim X.left)).presheaf.stalk z)

end HodgeLadder
