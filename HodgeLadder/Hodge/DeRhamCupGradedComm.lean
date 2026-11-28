module

public import HodgeLadder.Hodge.DeRhamCupBilinear
public import HodgeLadder.Hodge.DeRhamRationalSpan
public import HodgeLadder.Cup.CupSingular

/-!
# The de Rham cup product on smooth projective `X`: uniqueness and graded commutativity

Rungs `de-rham-cup-unique` and `de-rham-cup-antisymm-h1` (front `cup`). On a smooth projective
integral `X` over `ℂ` the classes `ι α`, `ι = fieldToDeRhamCohomology ℚ X`, span every
`H_dR^n(X)` over `ℂ` (rung `de-rham-rational-span`). A `ℂ`-bilinear map out of
`H_dR^a(X) × H_dR^b(X)` is therefore fixed by its values on pairs `(ι α, ι β)`
(`LinearMap.ext_on`, once per factor). Two consequences follow.

* **Uniqueness.** The identity `ι (α ∪ β) = deRhamCup (ι α) (ι β)` of rung `de-rham-cup-exact`
  characterizes `deRhamCupBilinear`: any `ℂ`-bilinear `P` satisfying it equals
  `deRhamCupBilinear X a b n _`. The product, its sign and its factor order on cohomology are
  fixed by the rational cup product `HodgeLadder.Cup.cup`; the dependence of
  `fieldToDeRhamCohomology_cup` on the wedge through its unit law only (`docs/gaps.md`, Known
  weaknesses) has no effect on cohomology here.
* **Graded commutativity.** `Cup.cup_gradedComm` (rung `cup-graded-commutative`),
  `cup x y = (-1 : ℤ) ^ (p * q) • cup y x`, carries over through `ι`:
  `deRhamCup y x n _ = (-1 : ℤ) ^ (a * b) • deRhamCup x y n _` for `x : H_dR^a(X)`,
  `y : H_dR^b(X)`, `a b n : ℕ`, `a + b = n`. The sign is the graded-commutativity sign
  `(-1)^{ab}` acting as a `ℤ`-scalar; Mathlib's Koszul sign `(-1)^p` inside `deRhamWedge` enters
  only through `fieldToDeRhamCohomology_cup`, which carries no sign. In degrees `(1, 1)` the sign
  is `-1`: `deRhamCup` is antisymmetric on `H¹_dR(X)`.

## Non-vacuity

`deRhamCupBilinear_eq_iff` shows that `deRhamCupBilinear` itself satisfies the hypothesis of
`deRhamCupBilinear_unique`; `P = 0` and `P = -deRhamCupBilinear` fail it at `a = b = n = 0` by
`deRhamCup_one_one_ne_zero` and `deRhamCup_one_one_ne_neg`. For the antisymmetry, every smooth projective `X` the ladder has at the pin (`Tests.point`,
`Tests.projectiveLine`, `Tests.projectiveSpace n`, `Tests.p1p1`) has first Betti number zero, so
`deRhamCup_antisymm_one` has no instance with a nonzero product yet (no Lean statement of the
vanishing); a projective instance waits on rung `cup-odd-degree-test`. The same identity on
rational classes of the affine `𝔾ₘ²` is `HodgeLadder.Tests.gm2_deRhamCup_antisymm`, proved there
from `Cup.cup_gradedComm` without the span: the product of the two generators is nonzero
(`HodgeLadder.Tests.gm2_deRhamCup_ne_zero`) and the sign `+1` fails
(`HodgeLadder.Tests.gm2_deRhamCup_swap_ne`). It is a separate theorem and no instance of
`deRhamCup_antisymm_one`.

## Instances

`Cup.cup_gradedComm` needs every open of `X(ℂ)` paracompact; upstream's `openParacompactSpace X`
supplies it for projective `X` as a local `let` inside `deRhamCupBilinear_flip`. No statement in
this file mentions it.

## Main results

* `HodgeLadder.deRhamCupBilinear_unique`: a `ℂ`-bilinear `P` with
  `P (ι α) (ι β) = ι (α ∪ β)` equals `deRhamCupBilinear X a b n _`
* `HodgeLadder.deRhamCupBilinear_eq_iff`: the same as an `iff`
* `HodgeLadder.deRhamCupBilinear_flip`:
  `(deRhamCupBilinear X b a n _).flip = (-1 : ℤ) ^ (a * b) • deRhamCupBilinear X a b n _`
* `HodgeLadder.deRhamCup_gradedComm`:
  `deRhamCup y x n _ = (-1 : ℤ) ^ (a * b) • deRhamCup x y n _`
* `HodgeLadder.deRhamCup_antisymm_one`: `deRhamCup y x 2 _ = -deRhamCup x y 2 _` on `H¹_dR(X)`
* `HodgeLadder.deRhamCup_self_of_odd`: `deRhamCup x x n _ = 0` for `x : H_dR^a(X)`, `a` odd
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- **Uniqueness of the de Rham cup product.** On a smooth projective integral `X` over `ℂ`, a
`ℂ`-bilinear `P : H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X)` with
`P (ι α) (ι β) = ι (α ∪ β)` for all rational classes `α`, `β` (`ι = fieldToDeRhamCohomology ℚ X`,
`∪ = HodgeLadder.Cup.cup`) equals `deRhamCupBilinear X a b n _`. The classes `ι α` span each
`H_dR^k(X)` (`span_range_fieldToDeRhamCohomology_rat`), and `deRhamCupBilinear` satisfies the same
identity (`fieldToDeRhamCohomology_cup`). -/
theorem deRhamCupBilinear_unique {a b n : ℕ} (h : a + b = n)
    (P : H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X))
    (hP : ∀ (α : H^a(X; ℚ)) (β : H^b(X; ℚ)),
      P (fieldToDeRhamCohomology ℚ X a α) (fieldToDeRhamCohomology ℚ X b β) =
        fieldToDeRhamCohomology ℚ X n (Cup.cup α β n h)) :
    P = deRhamCupBilinear X a b n (by lia) := by
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat X a) ?_
  rintro _ ⟨α, rfl⟩
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat X b) ?_
  rintro _ ⟨β, rfl⟩
  rw [hP, deRhamCupBilinear_apply, fieldToDeRhamCohomology_cup]

/-- **Characterization of the de Rham cup product.** On a smooth projective integral `X` over
`ℂ`, a `ℂ`-bilinear `P` equals `deRhamCupBilinear X a b n _` if and only if
`P (ι α) (ι β) = ι (α ∪ β)` for all rational classes `α`, `β`. The forward direction is
`fieldToDeRhamCohomology_cup`, the reverse `deRhamCupBilinear_unique`; in particular the
hypothesis of `deRhamCupBilinear_unique` is satisfiable. -/
theorem deRhamCupBilinear_eq_iff {a b n : ℕ} (h : a + b = n)
    (P : H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X)) :
    P = deRhamCupBilinear X a b n (by lia) ↔
      ∀ (α : H^a(X; ℚ)) (β : H^b(X; ℚ)),
        P (fieldToDeRhamCohomology ℚ X a α) (fieldToDeRhamCohomology ℚ X b β) =
          fieldToDeRhamCohomology ℚ X n (Cup.cup α β n h) := by
  refine ⟨?_, deRhamCupBilinear_unique X h P⟩
  rintro rfl α β
  rw [deRhamCupBilinear_apply, fieldToDeRhamCohomology_cup]

/-- **Graded commutativity, bundled.** On a smooth projective integral `X` over `ℂ`, for
`a + b = n` in `ℕ`, `(deRhamCupBilinear X b a n _).flip = (-1 : ℤ) ^ (a * b) • deRhamCupBilinear
X a b n _`, the `ℤ`-scalar acting on `ℂ`-bilinear maps. From `Cup.cup_gradedComm` on rational
classes, `fieldToDeRhamCohomology_cup` (no sign) and the span of rational classes. -/
theorem deRhamCupBilinear_flip {a b n : ℕ} (h : a + b = n) :
    (deRhamCupBilinear X b a n (by lia)).flip =
      ((-1 : ℤ) ^ (a * b)) • deRhamCupBilinear X a b n (by lia) := by
  let : ∀ U : Opens (ComplexPoint X), ParacompactSpace U := openParacompactSpace X
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat X a) ?_
  rintro _ ⟨α, rfl⟩
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat X b) ?_
  rintro _ ⟨β, rfl⟩
  simp only [LinearMap.flip_apply, LinearMap.smul_apply, deRhamCupBilinear_apply]
  rw [← fieldToDeRhamCohomology_cup X ((add_comm b a).trans h) β α,
    ← fieldToDeRhamCohomology_cup X h α β, Cup.cup_gradedComm X β α, map_zsmul, mul_comm]

/-- **Graded commutativity of the de Rham cup product.** On a smooth projective integral `X`
over `ℂ`, for `x : H_dR^a(X)`, `y : H_dR^b(X)` and `a + b = n` in `ℕ`,
`deRhamCup y x n _ = (-1 : ℤ) ^ (a * b) • deRhamCup x y n _` in `H_dR^n(X)`, the sign as a
`ℤ`-scalar, the same form as `Cup.cup_gradedComm`. -/
theorem deRhamCup_gradedComm {a b n : ℕ} (h : a + b = n) (x : H_dR^a(X)) (y : H_dR^b(X)) :
    deRhamCup y x n (by lia) = ((-1 : ℤ) ^ (a * b)) • deRhamCup x y n (by lia) := by
  have := congrArg (fun B => B x y) (deRhamCupBilinear_flip X h)
  simpa [deRhamCupBilinear_apply] using this

/-- **Antisymmetry on `H¹_dR`.** On a smooth projective integral `X` over `ℂ`, for
`x y : H_dR^1(X)`, `deRhamCup y x 2 _ = -deRhamCup x y 2 _`: `deRhamCup_gradedComm` at
`a = b = 1`, where `(-1 : ℤ) ^ (1 * 1) = -1`. -/
theorem deRhamCup_antisymm_one (x y : H_dR^1(X)) :
    deRhamCup y x 2 (by norm_num) = -deRhamCup x y 2 (by norm_num) := by
  have := deRhamCup_gradedComm X (a := 1) (b := 1) (n := 2) rfl x y
  simpa using this

/-- **Alternating in odd degree.** On a smooth projective integral `X` over `ℂ`, for `a` odd and
`x : H_dR^a(X)`, `deRhamCup x x n _ = 0`: `deRhamCup_gradedComm` with `(-1 : ℤ) ^ (a * a) = -1`,
and `2 • v = 0 → v = 0` in a `ℂ`-vector space. -/
theorem deRhamCup_self_of_odd {a n : ℕ} (ha : Odd a) (h : a + a = n) (x : H_dR^a(X)) :
    deRhamCup x x n (by lia) = 0 := by
  have hg := deRhamCup_gradedComm X h x x
  rw [(ha.mul ha).neg_one_pow, neg_one_zsmul, eq_neg_iff_add_eq_zero, ← two_smul ℂ] at hg
  exact (smul_eq_zero.mp hg).resolve_left two_ne_zero

end HodgeLadder
