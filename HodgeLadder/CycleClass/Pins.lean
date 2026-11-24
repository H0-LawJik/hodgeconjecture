module

public import HodgeConjecture.Statement
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ComplexClassDifferentiableInvariance

/-!
# Pins: the cycle-class and Hodge-class constructions at the upstream commit

Each theorem below states, by definitional unfolding (`rfl`), how one step of the upstream
construction is built at the pinned commit of `Paul-Lez/HodgeConjecture`. If upstream changes a
step, the matching theorem stops compiling, and the change is reviewed before any result here is
read against the new definition (`docs/conventions.md`, pin drift).

The cycle class of a codimension-`p` integral subvariety `Z` with generic point `x`:

1. a local class on complex normal coordinates, normalized to pair to `1` with the complex
   orientation class of the normal space (`normalizedRelativeCoclass`, pinned by
   `normalizedRelativeCoclass_pairing_self` upstream);
2. glued along the smooth locus of `Z` (`cycleComponentSmoothSupportCoclassSection`);
3. extended uniquely across the singular locus by purity
   (`cycleComponentSupportedClassNormalizationIso`, `cycleComponentSupportedInjectiveClass`);
4. pushed to ordinary rational cohomology by forgetting the support (`forgetSupport`), giving
   `cycleComponentSheafClass`;
5. `algebraicCycleClassSpan X p` is the ℚ-span of these classes over points of coheight `p`.

The complex orientation orders real coordinates as `(Re z₀, Im z₀, Re z₁, Im z₁, …)`
(`complexRealHomeomorph`); upstream proves that holomorphic germs with invertible derivative fix
the oriented local class (`relativeHomologyMap_complexDifferentiable_standardComplexLocalClass`),
so the normalization does not depend on the chart.

## Main results

* `HodgeLadder.Pins.algebraicCycleClassSpan_eq`, `cycleComponentSheafClass_eq`,
  `cycleComponentSupportedInjectiveClass_eq`: the cycle side, steps 3 to 5.
* `HodgeLadder.Pins.hodgeClasses_eq`, `hodgePiece_eq`: the Hodge side.
* `HodgeLadder.Pins.complexRealHomeomorph_eq`: the orientation convention.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint AlgebraicTopology.Singular

namespace HodgeLadder.Pins

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Step 5: the algebraic span is the ℚ-span of the cycle classes of points of coheight `p`. -/
theorem algebraicCycleClassSpan_eq (p : ℕ) :
    algebraicCycleClassSpan X p =
      sSup {Submodule.span ℚ {cycleComponentSheafClass X x hx} |
        (x : X.left) (hx : Order.coheight x = p)} :=
  rfl

/-- Step 4: the cycle class forgets the support of the supported class. -/
theorem cycleComponentSheafClass_eq (x : X.left) {p : ℕ} (hx : Order.coheight x = p) :
    cycleComponentSheafClass X x hx =
      forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) (2 * p)
        (cycleComponentSupportedInjectiveClass X x hx) :=
  rfl

/-- Step 3: the supported class is the unique extension of the normalized coclass section on the
complement of the singular locus. -/
theorem cycleComponentSupportedInjectiveClass_eq (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) :
    cycleComponentSupportedInjectiveClass X x hx =
      (cycleComponentSupportedClassNormalizationIso X x hx).symm.toAddMonoidHom
        (cycleComponentSmoothSupportCoclassSection X x hx) :=
  rfl

/-- The Hodge side: classes whose de Rham image lies in `F^p ∩ conj F^p`. -/
theorem hodgeClasses_eq (p : ℕ) :
    hodgeClasses ℚ X p =
      ((hodgePiece X p p (2 * p : ℕ)).restrictScalars ℚ).comap
        (fieldToDeRhamCohomologyLinear ℚ X (2 * p)) :=
  rfl

/-- The Hodge piece of type `(p, q)` in degree `n` is `F^p ∩ conj F^q`. -/
theorem hodgePiece_eq (p q n : ℤ) :
    hodgePiece X p q n =
      hodgeFiltrationComplexSubmodule X p n ⊓ conjHodgeFiltrationComplexSubmodule X q n :=
  rfl

/-- The orientation convention: complex coordinates split into consecutive real and imaginary
parts through Mathlib's `Complex.piCoordCLE`. -/
theorem complexRealHomeomorph_eq (p : ℕ) :
    complexRealHomeomorph p = (Complex.piCoordCLE p).toHomeomorph :=
  rfl

end HodgeLadder.Pins
