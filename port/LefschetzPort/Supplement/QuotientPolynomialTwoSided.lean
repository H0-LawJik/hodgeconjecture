/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Port supplement: two-sided ideals of polynomial rings over a quotient

At the current Mathlib, `R ⧸ I` carries its own `Semiring` instance (`Ideal.Quotient.semiring`,
there for quotients of noncommutative rings by two-sided ideals). Instance search does not unify
it with the semiring obtained through `Ideal.Quotient.commRing`, so the instance "every ideal of a
commutative semiring is two-sided" is not found for ideals of `(R ⧸ I)[X]` or `(R ⧸ I)[X][Y]` as
they elaborate. These instances supply it; each is Mathlib's `Ideal.instIsTwoSided`, unified at
default transparency.

## Main results

* `LefschetzPort.polynomialQuotientIdealIsTwoSided`
* `LefschetzPort.polynomialPolynomialQuotientIdealIsTwoSided`
-/

@[expose] public section

namespace LefschetzPort

/-- Ideals of `(R ⧸ I)[X]` are two-sided. -/
instance polynomialQuotientIdealIsTwoSided {R : Type*} [CommRing R] (I : Ideal R)
    (J : Ideal (Polynomial (R ⧸ I))) : J.IsTwoSided :=
  @Ideal.instIsTwoSided _ (Polynomial.commSemiring (R := R ⧸ I)) J

/-- Ideals of `(R ⧸ I)[X][Y]` are two-sided. -/
instance polynomialPolynomialQuotientIdealIsTwoSided {R : Type*} [CommRing R] (I : Ideal R)
    (J : Ideal (Polynomial (Polynomial (R ⧸ I)))) : J.IsTwoSided :=
  @Ideal.instIsTwoSided _ (Polynomial.commSemiring (R := Polynomial (R ⧸ I))) J

end LefschetzPort
