/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone

/-!
# Port supplement to `HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone`

On upstream main `relativeDualCochainShortComplexNat_shortExact` is `private`; the upstream stack
makes it public and uses it from other modules. The port restates it here, with upstream's proof,
so that upstream's file at the pin is not edited.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [CommRing R]

/-- Dualizing the singular-chain sequence of a pair gives a short exact sequence of
nonnegative cochain complexes. -/
lemma relativeDualCochainShortComplexNat_shortExact (X : TopPair.{u}) :
    (relativeDualCochainShortComplexNat R X).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => (relativeDualCochainShortComplexNatDegreewiseSplitting R X n).shortExact

end AlgebraicTopology.Singular
