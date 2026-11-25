module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration

/-!
# Conjugation fixes rational classes

Upstream defines conjugation on de Rham cohomology (`deRhamConj`) by conjugating constant complex
coefficients and transporting through `H^n(X(ℂ); ℂ) ≃ H_dR^n(X)`. This file proves that it fixes
the de Rham image of every rational class. With it, a rational class whose de Rham image lies in
`F^p` also lies in the conjugate filtration, so it is a Hodge class.

## Main results

* `HodgeLadder.fieldToComplexConstantSheaf_comp_conj`: `ℚ → ℂ` followed by conjugation is `ℚ → ℂ`,
  on constant sheaves.
* `HodgeLadder.deRhamConj_fieldToDeRhamCohomology`: `deRhamConj` fixes the de Rham image of a
  rational class.
* `HodgeLadder.mem_hodgeClasses_of_mem_hodgeFiltration`: a rational class of degree `2p` whose
  de Rham image lies in `F^p` is a Hodge class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ))

/-- On constant sheaves, the inclusion `ℚ → ℂ` followed by complex conjugation is the inclusion. -/
theorem fieldToComplexConstantSheaf_comp_conj :
    fieldToComplexConstantSheaf ℚ X ≫ conjConstantComplexSheaf X =
      fieldToComplexConstantSheaf ℚ X := by
  change (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map _ = (presheafToSheaf _ _).map _
  rw [← Functor.map_comp]
  congr 1
  ext U x
  exact map_ratCast (starRingEnd ℂ) (show ℚ from x)

/-- The same identity on the integer-indexed complexes in degree zero. -/
theorem fieldToComplexConstantSheafComplexInt_comp_conj :
    fieldToComplexConstantSheafComplexInt ℚ X ≫ conjConstantComplexSheafComplexInt X =
      fieldToComplexConstantSheafComplexInt ℚ X := by
  unfold fieldToComplexConstantSheafComplexInt conjConstantComplexSheafComplexInt
    conjConstantComplexComplex
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    fieldToComplexConstantSheaf_comp_conj]

/-- Conjugation on de Rham cohomology fixes the de Rham image of every rational class. -/
theorem deRhamConj_fieldToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (α : H^n(X; ℚ)) :
    deRhamConj X n (fieldToDeRhamCohomology ℚ X n α) = fieldToDeRhamCohomology ℚ X n α := by
  set β := (hypercohomologyAddEquivConstantCohomology ℚ X n).symm α
  have hβ : fieldToDeRhamCohomology ℚ X n α =
      complexConstantCohomologyDeRhamAddEquiv X n
        (hypercohomologyMap X (fieldToComplexConstantSheafComplexInt ℚ X) n β) := by
    change hypercohomologyMap X (fieldToHolomorphicDeRhamComplexInt ℚ X) n β =
      hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n
        (hypercohomologyMap X (fieldToComplexConstantSheafComplexInt ℚ X) n β)
    rw [← hypercohomologyMap_comp_apply]
    rfl
  rw [hβ, deRhamConj_apply, AddEquiv.symm_apply_apply, ← hypercohomologyMap_comp_apply,
    fieldToComplexConstantSheafComplexInt_comp_conj]

/-- A rational class of degree `2p` whose de Rham image lies in `F^p` is a Hodge class. -/
theorem mem_hodgeClasses_of_mem_hodgeFiltration [IsIntegral X.left] [Smooth X.hom] (p : ℕ)
    (α : H^(2 * p)(X; ℚ))
    (hα : fieldToDeRhamCohomology ℚ X (2 * p) α ∈ hodgeFiltration X p (2 * p : ℕ)) :
    α ∈ Hdg^p(X; ℚ) := by
  refine ⟨hα, ?_⟩
  change deRhamConj X (2 * p : ℕ) (fieldToDeRhamCohomology ℚ X (2 * p) α) ∈
    hodgeFiltration X p (2 * p : ℕ)
  rw [deRhamConj_fieldToDeRhamCohomology]
  exact hα

end HodgeLadder
