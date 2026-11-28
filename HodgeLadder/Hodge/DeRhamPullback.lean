module

public import HodgeLadder.Hodge.DeRhamRationalBaseChange
public import HodgeLadder.Hodge.DeRhamCupGradedComm
public import HodgeLadder.Hodge.Conjugation
public import HodgeLadder.Pullback.Functorial

/-!
# Pullback on de Rham cohomology of smooth projective varieties

Rung `de-rham-pullback` (plan `docs/notes/2026-11-27-t1-plan.md`, node A5). For a morphism
`g : X ⟶ Y` over `Spec ℂ` between smooth projective integral schemes, the `ℂ`-linear map
`deRhamPullback g n : H_dR^n(Y) →ₗ[ℂ] H_dR^n(X)` is the `ℂ`-linear extension of the rational
pullback `g^* = Pullback.pullbackCohLinear g n` (rung `pullback-functorial`) through the
base-change identities `e : ℂ ⊗_ℚ H^n(-; ℚ) ≃ₗ[ℂ] H_dR^n(-)` (`deRhamBaseChangeEquiv`, rung
`de-rham-rational-base-change`): `deRhamPullback g n = e_X ∘ (ℂ ⊗ g^*) ∘ e_Y⁻¹`.

The map is defined from rational classes and carries no information about differential forms.
Its agreement with a pullback of forms on hypercohomology is the separate rung
`de-rham-hypercohomology-pullback`, and preservation of `F^p` is `hodge-filtration-pullback`.

## Laws

Every law is exact, with no sign and no scalar.

* `deRhamPullback g n (ι α) = ι (g^* α)` for `α ∈ H^n(Y; ℚ)`, `ι = fieldToDeRhamCohomology ℚ`:
  from `deRhamBaseChangeEquiv_tmul` at `1 ⊗ α`.
* Composition, identity, cup product and conjugation hold on the classes `ι α`, which span
  `H_dR^n` over `ℂ` (`span_range_fieldToDeRhamCohomology_rat`, rung `de-rham-rational-span`), so
  they hold everywhere by `LinearMap.ext_on`. On `ι`-images they are `pullbackCoh_comp`,
  `pullbackCoh_id`, `Cup.pullbackCoh_cup` with `fieldToDeRhamCohomology_cup` (no sign), and
  `deRhamConj_fieldToDeRhamCohomology` (conjugation fixes rational classes). For conjugation both
  sides are `starRingEnd ℂ`-semilinear (upstream's `deRhamConjSemilinear`), and `ext_on` applies
  to semilinear maps.

## Degrees

The degrees are natural numbers, as for `pullbackCohLinear` and `deRhamBaseChangeEquiv`;
`H_dR^n` reads `n` through the cast `ℕ → ℤ`. The cup law takes `a + b = n` in `ℕ` and passes the
cast equation `(a : ℤ) + b = n` to `deRhamCup` and `deRhamCupBilinear`, the same convention as
`fieldToDeRhamCohomology_cup` and `deRhamCupBilinear_unique`.

## Main definitions

* `HodgeLadder.deRhamPullback g n : H_dR^n(Y) →ₗ[ℂ] H_dR^n(X)`

## Main results

* `HodgeLadder.deRhamPullback_fieldToDeRhamCohomology`: `g^* (ι α) = ι (g^* α)`
* `HodgeLadder.deRhamPullback_unique`: a `ℂ`-linear map agreeing with `ι ∘ g^*` on rational
  classes is `deRhamPullback g n`
* `HodgeLadder.deRhamPullback_comp`: `(g ≫ h)^* = g^* ∘ h^*`
* `HodgeLadder.deRhamPullback_id`: `(𝟙 X)^* = id`
* `HodgeLadder.deRhamPullback_injective_of_section`: `p^*` is injective when `s ≫ p = 𝟙`
* `HodgeLadder.deRhamPullback_cupBilinear`: the cup law as an identity of `ℂ`-bilinear maps,
  `deRhamCupBilinear Y a b n _` followed by `g^*` equals `deRhamCupBilinear X a b n _` precomposed
  with `g^*` in each factor
* `HodgeLadder.deRhamPullback_cup`: `g^* (deRhamCup x y n _) = deRhamCup (g^* x) (g^* y) n _`
* `HodgeLadder.deRhamPullback_conj`: `deRhamConj X n (g^* x) = g^* (deRhamConj Y n x)`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct

namespace HodgeLadder

variable {X Y Z : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- **Pullback on de Rham cohomology**, `g^* : H_dR^n(Y) →ₗ[ℂ] H_dR^n(X)` for `g : X ⟶ Y`
between smooth projective integral schemes over `ℂ`: the composite
`e_X ∘ (ℂ ⊗_ℚ pullbackCohLinear g n) ∘ e_Y⁻¹`, with `e = deRhamBaseChangeEquiv`. It is defined
from rational classes; it carries no information about pullback of forms. -/
def deRhamPullback (g : X ⟶ Y) (n : ℕ) : H_dR^n(Y) →ₗ[ℂ] H_dR^n(X) :=
  (deRhamBaseChangeEquiv X n).toLinearMap ∘ₗ (Pullback.pullbackCohLinear g n).baseChange ℂ ∘ₗ
    (deRhamBaseChangeEquiv Y n).symm.toLinearMap

/-- **Compatibility with `ι`, exact.** For `α ∈ H^n(Y; ℚ)`,
`deRhamPullback g n (ι α) = ι (g^* α)` with `ι = fieldToDeRhamCohomology ℚ` and
`g^* = Cup.pullbackCoh g n`. No scalar. -/
theorem deRhamPullback_fieldToDeRhamCohomology (g : X ⟶ Y) (n : ℕ) (α : H^n(Y; ℚ)) :
    deRhamPullback g n (fieldToDeRhamCohomology ℚ Y n α) =
      fieldToDeRhamCohomology ℚ X n (Cup.pullbackCoh g n α) := by
  have h1 : (deRhamBaseChangeEquiv Y n).symm (fieldToDeRhamCohomology ℚ Y n α) = 1 ⊗ₜ α := by
    rw [LinearEquiv.symm_apply_eq, deRhamBaseChangeEquiv_tmul, one_smul]
  have h2 : deRhamPullback g n (fieldToDeRhamCohomology ℚ Y n α) =
      deRhamBaseChangeEquiv X n ((Pullback.pullbackCohLinear g n).baseChange ℂ (1 ⊗ₜ α)) := by
    rw [← h1]; rfl
  rw [h2, LinearMap.baseChange_tmul, deRhamBaseChangeEquiv_tmul, one_smul,
    Pullback.pullbackCohLinear_apply]

/-- **Uniqueness.** A `ℂ`-linear map `H_dR^n(Y) →ₗ[ℂ] H_dR^n(X)` that sends `ι α` to
`ι (g^* α)` for every `α ∈ H^n(Y; ℚ)` is `deRhamPullback g n`: the classes `ι α` span
`H_dR^n(Y)` over `ℂ`. This is the step "hence everywhere" of `de-rham-hypercohomology-pullback`. -/
theorem deRhamPullback_unique (g : X ⟶ Y) (n : ℕ) (φ : H_dR^n(Y) →ₗ[ℂ] H_dR^n(X))
    (hφ : ∀ α : H^n(Y; ℚ), φ (fieldToDeRhamCohomology ℚ Y n α) =
      fieldToDeRhamCohomology ℚ X n (Cup.pullbackCoh g n α)) :
    φ = deRhamPullback g n := by
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat Y n) ?_
  rintro _ ⟨α, rfl⟩
  rw [hφ, deRhamPullback_fieldToDeRhamCohomology]

/-- **Pullback along a composite.** For `g : X ⟶ Y` and `h : Y ⟶ Z`,
`deRhamPullback (g ≫ h) n = deRhamPullback g n ∘ₗ deRhamPullback h n`, the order the types
force. -/
theorem deRhamPullback_comp [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ) :
    deRhamPullback (g ≫ h) n = deRhamPullback g n ∘ₗ deRhamPullback h n := by
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat Z n) ?_
  rintro _ ⟨α, rfl⟩
  rw [LinearMap.comp_apply, deRhamPullback_fieldToDeRhamCohomology,
    deRhamPullback_fieldToDeRhamCohomology, deRhamPullback_fieldToDeRhamCohomology,
    Pullback.pullbackCoh_comp]

/-- **Pullback along the identity** is the identity of `H_dR^n(X)`. -/
theorem deRhamPullback_id (n : ℕ) : deRhamPullback (𝟙 X) n = LinearMap.id := by
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat X n) ?_
  rintro _ ⟨α, rfl⟩
  rw [deRhamPullback_fieldToDeRhamCohomology, Pullback.pullbackCoh_id, LinearMap.id_apply]

/-- **Injectivity along a morphism with a section.** If `s ≫ p = 𝟙 Y`, then
`deRhamPullback s n ∘ₗ deRhamPullback p n = id`, so `deRhamPullback p n` is injective in every
degree: `deRhamPullback_comp` and `deRhamPullback_id`. -/
theorem deRhamPullback_injective_of_section (p : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (n : ℕ) : Function.Injective (deRhamPullback p n) := by
  have key : ∀ x, deRhamPullback s n (deRhamPullback p n x) = x := fun x => by
    rw [← LinearMap.comp_apply, ← deRhamPullback_comp, hs, deRhamPullback_id,
      LinearMap.id_apply]
  exact Function.LeftInverse.injective key

/-- **Pullback is multiplicative, bundled.** For `a + b = n` in `ℕ`, the `ℂ`-bilinear maps
`(x, y) ↦ g^* (deRhamCup x y n _)` and `(x, y) ↦ deRhamCup (g^* x) (g^* y) n _` agree:
`(deRhamCupBilinear Y a b n _).compr₂ (deRhamPullback g n) =
(deRhamCupBilinear X a b n _).compl₁₂ (deRhamPullback g a) (deRhamPullback g b)`. Exact, no
sign: on rational classes it is `Cup.pullbackCoh_cup` read through `fieldToDeRhamCohomology_cup`. -/
theorem deRhamPullback_cupBilinear (g : X ⟶ Y) {a b n : ℕ} (h : a + b = n) :
    (deRhamCupBilinear Y a b n (by lia)).compr₂ (deRhamPullback g n) =
      (deRhamCupBilinear X a b n (by lia)).compl₁₂ (deRhamPullback g a) (deRhamPullback g b) := by
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat Y a) ?_
  rintro _ ⟨α, rfl⟩
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat Y b) ?_
  rintro _ ⟨β, rfl⟩
  rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, deRhamCupBilinear_apply,
    deRhamCupBilinear_apply, ← fieldToDeRhamCohomology_cup Y h,
    deRhamPullback_fieldToDeRhamCohomology, deRhamPullback_fieldToDeRhamCohomology,
    deRhamPullback_fieldToDeRhamCohomology, Cup.pullbackCoh_cup, fieldToDeRhamCohomology_cup X h]

/-- **Pullback is multiplicative.** For `x : H_dR^a(Y)`, `y : H_dR^b(Y)` and `a + b = n` in
`ℕ`, `g^* (deRhamCup x y n _) = deRhamCup (g^* x) (g^* y) n _`, with `g^* = deRhamPullback g`
in each degree. Exact, no sign, the factor order of `deRhamCup` on both sides. With literal `ℤ`
degrees (`deRhamCup x y 2 _`) `rw` and `simp` with this lemma fail on `↑2` against `2` in a
dependent position; use `exact`, or `LinearMap.congr_fun₂` of `deRhamPullback_cupBilinear` (the
form `weil-eigen-algebra`'s `hS` takes). -/
theorem deRhamPullback_cup (g : X ⟶ Y) {a b n : ℕ} (h : a + b = n) (x : H_dR^a(Y))
    (y : H_dR^b(Y)) :
    deRhamPullback g n (deRhamCup x y n (by lia)) =
      deRhamCup (deRhamPullback g a x) (deRhamPullback g b y) n (by lia) :=
  congrArg (fun B => B x y) (deRhamPullback_cupBilinear g h)

/-- **Pullback commutes with conjugation.** `deRhamConj X n (g^* x) = g^* (deRhamConj Y n x)`
for `x : H_dR^n(Y)`, with upstream's conjugation `deRhamConj`. Both sides are conjugate-linear in
`x` and agree on rational classes, which conjugation fixes. -/
theorem deRhamPullback_conj (g : X ⟶ Y) (n : ℕ) (x : H_dR^n(Y)) :
    deRhamConj X n (deRhamPullback g n x) = deRhamPullback g n (deRhamConj Y n x) := by
  have key : (deRhamConjSemilinear X n).comp (deRhamPullback g n) =
      (deRhamPullback g n).comp (deRhamConjSemilinear Y n) := by
    refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat Y n) ?_
    rintro _ ⟨α, rfl⟩
    simp only [LinearMap.comp_apply, deRhamConjSemilinear_apply]
    rw [deRhamConj_fieldToDeRhamCohomology, deRhamPullback_fieldToDeRhamCohomology,
      deRhamConj_fieldToDeRhamCohomology]
  exact congrArg (fun f => f x) key

end HodgeLadder
