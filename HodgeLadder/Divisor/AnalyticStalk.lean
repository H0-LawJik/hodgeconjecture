module

public import LefschetzPort.AlgebraicGeometry.HolomorphicAnalyticSpace
public import LefschetzPort.Oka.StalkEquiv
public import LefschetzPort.Oka.UFD

/-!
# Analytic stalks of a smooth complex variety are UFDs

For a smooth complex scheme `X` of dimension `d`, the stalk of holomorphic functions on `X(ℂ)` at
any point is isomorphic to `LocalOkaRing (Fin d)`, the ring of convergent power series in `d`
variables, which Oka's library proves is a UFD (`LocalOkaRing.instUniqueFactorizationMonoid`).
The isomorphism is the chosen analytic chart (`localChartLocallyRingedSpaceIsoFin`, from the
stack), followed by Oka's Taylor-expansion equivalence (`okaStalkEquiv`). Rung
`analytic-stalk-ufd` (`docs/sketches/prime-divisors-cartier.md`).

## Main results

* `HodgeLadder.holomorphicStalkRingEquiv`: the stalk at `z` is `LocalOkaRing (Fin d)`.
* `HodgeLadder.uniqueFactorizationMonoid_holomorphicStalk`, `HodgeLadder.isDomain_holomorphicStalk`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The stalk of holomorphic functions on `X(ℂ)` at `z` is the ring of convergent power series
in `d` variables. -/
def holomorphicStalkRingEquiv (z : ComplexPoint X) :
    (holomorphicLocallyRingedSpace X d).presheaf.stalk z ≃+* LocalOkaRing (Fin d) := by
  let U := localChartSource X d z
  let z' : (Opens.toTopCat (holomorphicLocallyRingedSpace X d).toTopCat).obj U :=
    ⟨z, mem_localChart_source X d z⟩
  let e := localChartLocallyRingedSpaceIsoFin X d z
  let eP := (LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).mapIso e
  let i1 := LocallyRingedSpace.restrictStalkIso (holomorphicLocallyRingedSpace X d)
    U.isOpenEmbedding z'
  let i2 := PresheafedSpace.stalkMap.stalkIso eP z'
  let i3 := LocallyRingedSpace.restrictStalkIso (complexSpace (Fin d))
    (localChartTarget X d z).isOpenEmbedding (eP.hom.base z')
  exact (i1.symm ≪≫ i2.symm ≪≫ i3).commRingCatIsoToRingEquiv.trans (okaStalkEquiv _)

/-- The stalks of holomorphic functions on `X(ℂ)` are UFDs. -/
theorem uniqueFactorizationMonoid_holomorphicStalk (z : ComplexPoint X) :
    UniqueFactorizationMonoid ((holomorphicLocallyRingedSpace X d).presheaf.stalk z) :=
  (holomorphicStalkRingEquiv X d z).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

/-- The stalks of holomorphic functions on `X(ℂ)` are domains. -/
theorem isDomain_holomorphicStalk (z : ComplexPoint X) :
    IsDomain ((holomorphicLocallyRingedSpace X d).presheaf.stalk z) :=
  (holomorphicStalkRingEquiv X d z).toMulEquiv.isDomain

end HodgeLadder
