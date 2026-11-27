module

public import HodgeLadder.Hodge.DeRhamRationalIndependent

/-!
# The base-change identity `ℂ ⊗_ℚ H^n(X(ℂ); ℚ) ≅ H_dR^n(X)`

Rung `de-rham-rational-base-change` (red team of `de-rham-rational-independent`, finding 7). For a
smooth projective integral scheme `X` over `ℂ` and upstream's
`ι = fieldToDeRhamCohomologyLinear ℚ X n : H^n(X(ℂ); ℚ) →ₗ[ℚ] H_dR^n(X)`, the `ℂ`-linear
extension `LinearMap.liftBaseChange ℂ ι : ℂ ⊗_ℚ H^n(X(ℂ); ℚ) → H_dR^n(X)`,
`c ⊗ m ↦ c • ι m`, is bijective, and `finrank_ℂ H_dR^n(X) = finrank_ℚ H^n(X(ℂ); ℚ)`.

The proofs apply the conditional forms of `HodgeLadder.Hodge.DeRhamRationalIndependent`
(injectivity from `de-rham-rational-independent`, surjectivity from the span of
`de-rham-rational-span`) to `simplicialComplexSpan` (rung `simplicial-complex-span`). The
`ℂ`-module structure on `H_dR^n(X)` is upstream's.

The rank equality is an identity of natural numbers under Mathlib's convention that `finrank` is
`0` on an infinite-dimensional space; finiteness of either side is not proved here.

## Main definitions

* `HodgeLadder.deRhamBaseChangeEquiv`: the `ℂ`-linear equivalence
  `ℂ ⊗_ℚ H^n(X(ℂ); ℚ) ≃ₗ[ℂ] H_dR^n(X)`.

## Main results

* `HodgeLadder.bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat`: the base-change map
  is bijective.
* `HodgeLadder.finrank_deRham_eq_finrank_rat`:
  `Module.finrank ℂ H_dR^n(X) = Module.finrank ℚ H^n(X(ℂ); ℚ)`.
* `HodgeLadder.deRhamBaseChangeEquiv_tmul`: the equivalence sends `c ⊗ m` to `c • ι m`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ))

/-- **Rung `de-rham-rational-base-change`, bijectivity.** For a smooth projective integral `X`
over `ℂ`, the `ℂ`-linear extension `ℂ ⊗_ℚ H^n(X(ℂ); ℚ) → H_dR^n(X)`, `c ⊗ m ↦ c • ι m`, of
upstream's `ι = fieldToDeRhamCohomologyLinear ℚ X n` is bijective. -/
theorem bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    Function.Bijective (LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)) :=
  bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_simplicialComplexSpan
    X simplicialComplexSpan n

/-- **Rung `de-rham-rational-base-change`, ranks.** For a smooth projective integral `X` over `ℂ`,
`finrank_ℂ H_dR^n(X) = finrank_ℚ H^n(X(ℂ); ℚ)`, with upstream's `ℂ`-module structure on
`H_dR^n(X)`. -/
theorem finrank_deRham_eq_finrank_rat [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) : Module.finrank ℂ H_dR^n(X) = Module.finrank ℚ H^n(X; ℚ) :=
  finrank_deRham_eq_finrank_rat_of_simplicialComplexSpan X simplicialComplexSpan n

/-- The base-change identity as a `ℂ`-linear equivalence
`ℂ ⊗_ℚ H^n(X(ℂ); ℚ) ≃ₗ[ℂ] H_dR^n(X)`, the bijective map
`LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)`. -/
def deRhamBaseChangeEquiv [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    ℂ ⊗[ℚ] H^n(X; ℚ) ≃ₗ[ℂ] H_dR^n(X) :=
  LinearEquiv.ofBijective _ (bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat X n)

/-- The equivalence sends `c ⊗ m` to `c • ι m`, with `ι = fieldToDeRhamCohomology ℚ X n`. -/
theorem deRhamBaseChangeEquiv_tmul [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) (c : ℂ) (m : H^n(X; ℚ)) :
    deRhamBaseChangeEquiv X n (c ⊗ₜ m) = c • fieldToDeRhamCohomology ℚ X n m := by
  simp only [deRhamBaseChangeEquiv, LinearEquiv.ofBijective_apply,
    LinearMap.liftBaseChange_tmul]
  rfl

end HodgeLadder
