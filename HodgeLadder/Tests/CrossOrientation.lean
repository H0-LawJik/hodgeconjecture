module

public import HodgeLadder.Local.CrossOrientation
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity

/-!
# Non-vacuity of the cross product of orientations

The two identities of rung `cross-orientation` are sign-visible. Their right sides are nonzero and
are not their own negatives, so a proof with the wrong sign, or of the zero map, would contradict
them.

## Main results

* `HodgeLadder.Tests.standardLocalClass_ne_neg_of_pos`: over `ℚ`, `standardLocalClass ℚ d` is not
  its own negative for `0 < d`, so `cross_orientation_real` separates `+` from `-` whenever
  `0 < m + n`.
* `HodgeLadder.Tests.cast_standardComplexLocalClass_ne_zero`: the right side of
  `cross_orientation_complex` is nonzero for every `a, b`.
-/

@[expose] public section

open AlgebraicTopology AlgebraicTopology.Singular

namespace HodgeLadder.Tests

/-- Over `ℚ` the local class is not its own negative in positive dimension, so
`cross_orientation_real` separates `+` from `-`. -/
theorem standardLocalClass_ne_neg_of_pos (d : ℕ) (hd : 0 < d) :
    standardLocalClass ℚ d ≠ -standardLocalClass ℚ d := by
  intro e
  have h2 : (2 : ℚ) • standardLocalClass ℚ d = 0 := by rw [two_smul]; nth_rw 2 [e]; simp
  exact standardLocalClass_ne_zero_of_pos _ hd ((smul_eq_zero.1 h2).resolve_left (by norm_num))

/-- The right side of `cross_orientation_complex` is nonzero for every `a, b`. -/
theorem cast_standardComplexLocalClass_ne_zero (a b : ℕ) :
    ((Nat.mul_add 2 a b) ▸ standardComplexLocalClass ℚ (a + b) :
      RelativeHomology ℚ (puncturedPair ℂ (a + b)) (2 * a + 2 * b)) ≠ 0 := by
  have key : ∀ {d d' : ℕ} (h : d = d') (x : RelativeHomology ℚ (puncturedPair ℂ (a + b)) d),
      x ≠ 0 → (h ▸ x : RelativeHomology ℚ (puncturedPair ℂ (a + b)) d') ≠ 0 := by
    intro d d' h x hx; subst h; exact hx
  exact key _ _ (standardComplexLocalClass_ne_zero (a + b))

end HodgeLadder.Tests
