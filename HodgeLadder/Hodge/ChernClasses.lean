module

public import HodgeLadder.Hodge.Conjugation
public import HodgeLadder.Hodge.FirstFiltration
public import LefschetzPort.AlgebraicGeometry.HolomorphicFirstChernClassExactness
public import LefschetzPort.AlgebraicGeometry.HolomorphicIntegralHodgeClass
public import LefschetzPort.AlgebraicGeometry.ChernRelativeFinalAssembly

/-!
# First Chern classes and Cartier divisor classes are Hodge classes

The converse of the stack's `integralHodgeClass_integerToHolomorphicSecondCohomology_eq_zero`:
an integral class of degree two that vanishes in `H²(𝒪)` has a rational image of Hodge type
`(1,1)`. Its de Rham image vanishes in `ℍ²(𝒪[0])` by the comparison of coefficient maps, so it
lies in `F¹` (`HodgeLadder.mem_hodgeFiltration_one_iff`), and conjugation fixes it
(`HodgeLadder.deRhamConj_fieldToDeRhamCohomology`). By exactness of the exponential sequence,
every holomorphic first Chern class vanishes in `H²(𝒪)`; by the divisor–Chern identity, so does
the class of the divisor of a Cartier datum.

## Main results

* `HodgeLadder.integralToRational_mem_hodgeClasses_iff`: for `α ∈ H²(X; ℤ)`, the rational image
  of `α` is a Hodge class exactly when `α` vanishes in `H²(𝒪)`.
* `HodgeLadder.holomorphicFirstChernClass_mem_hodgeClasses`: rational first Chern classes of
  holomorphic line bundles are Hodge classes.
* `HodgeLadder.sheafCycleClassOnCycles_divisor_mem_hodgeClasses`: the class of the divisor of a
  Cartier datum is a Hodge class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

attribute [local instance] isNoetherian_of_isProjective

set_option linter.auxLemma false
/- Sheaves on a space are sheaves on its site of opens; the category instance is looked up under
that spelling by Mathlib's sheaf cohomology (as in upstream's `Hodge/Filtration.lean`). -/
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

set_option backward.isDefEq.respectTransparency false in
/-- An integral degree-two class that vanishes in `H²(𝒪)` has a rational Hodge class as image. -/
theorem integralToRational_mem_hodgeClasses_of_toHolomorphic_eq_zero (α : H^2(X; ℤ))
    (h : integerToHolomorphicSecondCohomology X (dim X.left) α = 0) :
    integralToRationalCohomology X 2 α ∈ Hdg^1(X; ℚ) := by
  apply mem_hodgeClasses_of_mem_hodgeFiltration X 1
  refine (mem_hodgeFiltration_one_iff X ((2 * 1 : ℕ) : ℤ) _).2 ?_
  let β : Hypercohomology X (analyticSheafComplexInt X (𝓒(↧(ComplexPoint X); ℤ))) 2 :=
    (analyticSheafHypercohomologyAddEquiv X (𝓒(↧(ComplexPoint X); ℤ)) 2).symm α
  have hβ0 : hypercohomologyMap X
      (analyticSheafComplexIntMap X (integerConstantsToHolomorphicSheaf X (dim X.left))) 2 β =
        0 := by
    apply (analyticSheafHypercohomologyAddEquiv X (holomorphicAdditiveSheaf X (dim X.left))
      2).injective
    refine (analyticSheafHypercohomologyAddEquiv_naturality X _ 2 β).trans ?_
    rw [map_zero]
    erw [AddEquiv.apply_symm_apply]
    exact h
  have hα : α = analyticSheafHypercohomologyAddEquiv X (𝓒(↧(ComplexPoint X); ℤ)) 2 β :=
    (AddEquiv.apply_symm_apply _ α).symm
  rw [hα, integralToRationalCohomology_analyticSheafHypercohomologyAddEquiv]
  dsimp only [deRhamToHolomorphicFunctionCohomology, fieldToDeRhamCohomology,
    AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
  erw [AddEquiv.symm_apply_apply]
  erw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply,
    integerToRationalDeRhamToFunctions, hypercohomologyMap_comp_apply, hβ0, map_zero]

/-- **Integral classes of type `(1,1)`**: the rational image of an integral degree-two class is a
Hodge class exactly when the class vanishes in `H²(𝒪)`. -/
theorem integralToRational_mem_hodgeClasses_iff (α : H^2(X; ℤ)) :
    integralToRationalCohomology X 2 α ∈ Hdg^1(X; ℚ) ↔
      integerToHolomorphicSecondCohomology X (dim X.left) α =
        (0 : Sheaf.H.{0} (holomorphicAdditiveSheaf X (dim X.left)) 2) :=
  ⟨integralHodgeClass_integerToHolomorphicSecondCohomology_eq_zero X α,
    integralToRational_mem_hodgeClasses_of_toHolomorphic_eq_zero X α⟩

/-- **Rational first Chern classes are Hodge classes.** -/
theorem holomorphicFirstChernClass_mem_hodgeClasses
    (β : Sheaf.H.{0} (holomorphicUnitSheaf X (dim X.left)) 1) :
    integralToRationalCohomology X 2 (holomorphicFirstChernClass X (dim X.left) β) ∈
      Hdg^1(X; ℚ) :=
  integralToRational_mem_hodgeClasses_of_toHolomorphic_eq_zero X _
    ((exists_holomorphicFirstChernClass_iff X (dim X.left) _).mp ⟨β, rfl⟩)

/-- The rational first Chern class of a holomorphic unit extension is a Hodge class. -/
theorem firstChernClass_mem_hodgeClasses (E : HolomorphicUnitExtension X (dim X.left)) :
    integralToRationalCohomology X 2 E.firstChernClass ∈ Hdg^1(X; ℚ) :=
  holomorphicFirstChernClass_mem_hodgeClasses X _

/-- **The class of a Cartier divisor is a Hodge class.** For a Cartier datum `c` representing an
invertible sheaf `L` whose analytification is the section sheaf of a unit extension `E`, the
cycle class of `c.divisor` equals the rational first Chern class of `E` (divisor–Chern, sign `+`),
which is a Hodge class. -/
theorem sheafCycleClassOnCycles_divisor_mem_hodgeClasses [IsProjective X.hom]
    (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules)
    (hL : TauCeti.SheafOfModules.IsInvertible L)
    (e : (moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)
    (c : Scheme.CartierData X.left) (hc : c.Represents L) :
    sheafCycleClassOnCycles { scheme := X.left, structureMap := X.hom } 1 c.divisor ∈
      Hdg^1(X; ℚ) := by
  rw [hasDivisorClassOfCartierData (X := X) E L hL e c hc]
  exact firstChernClass_mem_hodgeClasses X E

end HodgeLadder
