module

public import HodgeLadder.Cup.CapCrossEvaluation
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean

/-!
# Tests: cap–cross evaluation

Rung `cap-cross-evaluation-test`, the non-vacuity tests of rung `cap-cross-evaluation` (red team
2026-11-26, change C1, text verbatim).

## Main results

* `HodgeLadder.Tests.capCross_real_one_one`: on `ℝ¹ × ℝ¹`, in the odd degrees `m = n = 1`, the left
  side of `cap_cross_evaluation` with upstream's local class and its normalized coclass is `1`. A
  Koszul sign `(-1)^{mn}` would give `-1`, so the test separates the two conventions.
* `HodgeLadder.Tests.capCross_complex_model`: the product form of `local-class-cross-model`: on
  `ℂ^a × ℂ^b` the value is `1` for every `a`, `b`.
-/

@[expose] public noncomputable section

namespace HodgeLadder.Tests

open CategoryTheory MonoidalCategory AlgebraicTopology.Singular HodgeLadder.Relative
  HodgeLadder.CapCross

/-- `ℂ^a` as an object of `TopCat`. -/
abbrev capCrossCx (a : ℕ) : TopCat.{0} := TopCat.of (Fin a → ℂ)

/-- `ℂ^a ∖ {0}`. -/
abbrev capCrossCxPunct (a : ℕ) : Set (capCrossCx a) := ({0}ᶜ : Set (Fin a → ℂ))

/-- `ℝ^d` as an object of `TopCat`. -/
abbrev capCrossRe (d : ℕ) : TopCat.{0} := TopCat.of (Fin d → ℝ)

/-- `ℝ^d ∖ {0}`. -/
abbrev capCrossRePunct (d : ℕ) : Set (capCrossRe d) := ({0}ᶜ : Set (Fin d → ℝ))

/-- Sign-visible instance of `cap_cross_evaluation` in odd degrees `m = n = 1`: the left side is
`1`, where a Koszul sign `(-1)^{mn}` would give `-1`. -/
theorem capCross_real_one_one :
    relativeCohomologyEquivDualHomology ℚ
        (TopPair.ofSubset (X := capCrossRe 1 ⊗ capCrossRe 1)
          (rightProdSet (capCrossRe 1) (capCrossRePunct 1))) 1
      (relativeCohomologyMap ℚ 1 (prSndPair (capCrossRe 1) (capCrossRePunct 1))
        (normalizedRelativeCoclass (X := puncturedPair ℝ 1) (standardLocalClass ℚ 1)
          (standardLocalClass_ne_zero_of_pos 1 one_pos)))
      (unionRelativeTriadCapCohomologyLinear ℚ (capCrossRe 1 ⊗ capCrossRe 1)
        (leftProdSet (capCrossRePunct 1) (capCrossRe 1))
        (rightProdSet (capCrossRe 1) (capCrossRePunct 1)) 1 1
        (quasiIso_triadToUnion_prod_of_isOpen (A := capCrossRePunct 1) (B := capCrossRePunct 1)
          isOpen_compl_singleton isOpen_compl_singleton)
        (relativeCohomologyMap ℚ 1 (prFstPair (capCrossRePunct 1) (capCrossRe 1))
          (normalizedRelativeCoclass (X := puncturedPair ℝ 1) (standardLocalClass ℚ 1)
            (standardLocalClass_ne_zero_of_pos 1 one_pos)))
        (relCrossUnion (capCrossRePunct 1) (capCrossRePunct 1) 1 1
          (standardLocalClass ℚ 1) (standardLocalClass ℚ 1))) = 1 := by
  rw [cap_cross_evaluation, normalizedRelativeCoclass_pairing_self, mul_one]

/-- The product form of `local-class-cross-model`: on `ℂ^a × ℂ^b`, the triad cap of the pulled-back
normalized local class of `ℂ^a` with the cross product of the complex orientation classes, paired
with the pulled-back normalized local class of `ℂ^b`, is `1`, for every `a`, `b`. -/
theorem capCross_complex_model (a b : ℕ) :
    relativeCohomologyEquivDualHomology ℚ
        (TopPair.ofSubset (X := capCrossCx a ⊗ capCrossCx b)
          (rightProdSet (capCrossCx a) (capCrossCxPunct b))) (2 * b)
      (relativeCohomologyMap ℚ (2 * b) (prSndPair (capCrossCx a) (capCrossCxPunct b))
        (normalizedRelativeCoclass (X := puncturedPair ℂ b) (standardComplexLocalClass ℚ b)
          (standardComplexLocalClass_ne_zero b)))
      (unionRelativeTriadCapCohomologyLinear ℚ (capCrossCx a ⊗ capCrossCx b)
        (leftProdSet (capCrossCxPunct a) (capCrossCx b))
        (rightProdSet (capCrossCx a) (capCrossCxPunct b)) (2 * a) (2 * b)
        (quasiIso_triadToUnion_prod_of_isOpen (A := capCrossCxPunct a) (B := capCrossCxPunct b)
          isOpen_compl_singleton isOpen_compl_singleton)
        (relativeCohomologyMap ℚ (2 * a) (prFstPair (capCrossCxPunct a) (capCrossCx b))
          (normalizedRelativeCoclass (X := puncturedPair ℂ a) (standardComplexLocalClass ℚ a)
            (standardComplexLocalClass_ne_zero a)))
        (relCrossUnion (capCrossCxPunct a) (capCrossCxPunct b) (2 * a) (2 * b)
          (standardComplexLocalClass ℚ a) (standardComplexLocalClass ℚ b))) = 1 := by
  rw [cap_cross_evaluation, normalizedRelativeCoclass_pairing_self,
    normalizedRelativeCoclass_pairing_self, mul_one]

end HodgeLadder.Tests
