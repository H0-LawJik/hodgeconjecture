module

public import HodgeLadder.Hodge.DeRhamCup
public import HodgeLadder.Hodge.DeRhamScalarSheaf

/-!
# The de Rham cup product is `ℂ`-bilinear

Rung `de-rham-cup` (front `cup`). The product `deRhamCup x y n h = e⁻¹ (pairProductShQ μ (e y) (e x))`
of rung `de-rham-cup-exact` (`e = deRhamShiftedHomEquiv X`, `μ = deRhamWedge X`) is additive in
each factor there; this file adds `deRhamCup (c • x) y = c • deRhamCup x y` and
`deRhamCup x (c • y) = c • deRhamCup x y` for `c : ℂ`, and bundles the product as a `ℂ`-bilinear
map.

## Which `ℂ`-action

The action is upstream's `deRhamHypercohomologyComplexModule`: `c • α` is upstream's
hypercohomology map of `scalarHolomorphicDeRhamComplexInt X c` (`deRham_complex_smul_eq`). It is
the instance elaboration selects for `Module ℂ H_dR^n(X)` in this file; no other action enters.
Rung `de-rham-scalar-sheaf` carries it to `S_c = rationalDeRhamScalar X c` on `Ω•_ℚ`:
`e (c • z) = e z ≫ (Q.map S_c)⟦k⟧'` (`rationalHypercohomologyEquiv_smul`, restated here as
`deRhamShiftedHomEquiv_smul`).

## Proof

Both laws are `pairProductShQ_naturality` of rung `pairing-product`, with `m = m' = μ`. For the
first factor `x` (the right tensor factor of `μ`): `f = 𝟙`, `g = k = S_c` and hypothesis the
second-factor scalar law `(𝟙 ⊗ S_c) ≫ μ = μ ≫ S_c`. For the second factor `y` (the left tensor
factor): `f = k = S_c`, `g = 𝟙` and the first-factor scalar law `(S_c ⊗ 𝟙) ≫ μ = μ ≫ S_c`. No sign
enters: `S_c` has degree zero, and the naturality is exact. The proofs are chained with
`Eq.trans` and `congrArg` through the named equations `deRhamShiftedHomEquiv_deRhamCup` and
`deRhamShiftedHomEquiv_comp_map_id`, since `rw` on these goals exceeds the default heartbeats.

## Instances

The local instances listed in the docstring of `HodgeLadder.Hodge.DeRhamCup` (the `rh*` of
`HodgeLadder.Hodge.RationalHypercohomology`; `Cup.sheafMonoidal`, `analyticShQMonoidal` and the
`wsm*` of `HodgeLadder.Hodge.WedgeSheafMap` for the scalar laws). The statements of
`deRhamCup_smul_left`, `deRhamCup_smul_right` and `deRhamCupBilinear` mention none of them.

## Main definitions

* `HodgeLadder.deRhamCupBilinear X a b n h : H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X)`, with
  `deRhamCupBilinear X a b n h x y = deRhamCup x y n h` by `rfl` (`deRhamCupBilinear_apply`)

## Main results

* `HodgeLadder.deRhamCup_smul_left`, `HodgeLadder.deRhamCup_smul_right`: `ℂ`-linearity in each
  factor, exact
* `HodgeLadder.deRhamShiftedHomEquiv_smul`, `HodgeLadder.deRhamShiftedHomEquiv_deRhamCup`,
  `HodgeLadder.deRhamShiftedHomEquiv_comp_map_id`: the named steps
* `HodgeLadder.deRhamCup_smul_one_one`: `deRhamCup (c • ι 1) (ι 1) = c • ι 1`;
  `HodgeLadder.deRhamCup_smul_one_one_ne`: for `c ≠ c'` the right side `c' • ι 1` fails, on every
  smooth integral `X` (so the trivial and the conjugate-linear actions fail the law)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry ComplexPoint TopologicalSpace DerivedCategory

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

attribute [local instance] HodgeLadder.rhHasDerivedCategory HodgeLadder.rhSiteHasDerivedCategory
  HodgeLadder.rhHasExt HodgeLadder.rhQHasDerivedCategory HodgeLadder.rhTensorAdditive
  HodgeLadder.rhForgetAdditive HodgeLadder.rhTensorPFL HodgeLadder.rhTensorPFC
  HodgeLadder.rhForgetPFL HodgeLadder.rhForgetPFC

attribute [local instance] HodgeLadder.Cup.sheafMonoidal HodgeLadder.analyticShQMonoidal
  HodgeLadder.wsmCurriedTensorAdditive HodgeLadder.wsmTensorLeftAdditive
  HodgeLadder.wsmTensorRightPreservesEmpty

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- **Scalars through the bridge.** `e (c • z) = e z ≫ (Q.map S_c)⟦k⟧'` with
`e = deRhamShiftedHomEquiv X k` and `S_c = rationalDeRhamScalar X c`: the statement
`rationalHypercohomologyEquiv_smul` read through the definition of `e`. -/
theorem deRhamShiftedHomEquiv_smul (k : ℤ) (c : ℂ) (z : H_dR^k(X)) :
    deRhamShiftedHomEquiv X k (c • z) =
      deRhamShiftedHomEquiv X k z ≫ (Q.map (rationalDeRhamScalar X c))⟦k⟧' :=
  rationalHypercohomologyEquiv_smul X k c z

/-- `e z = e z ≫ (Q.map 𝟙)⟦k⟧'`, the identity of `Ω•_ℚ` postcomposed, in the form
`pairProductShQ_naturality` takes. -/
theorem deRhamShiftedHomEquiv_comp_map_id (k : ℤ) (z : H_dR^k(X)) :
    deRhamShiftedHomEquiv X k z = deRhamShiftedHomEquiv X k z ≫
      (Q.map (𝟙 (rationalDeRhamComplex X)))⟦k⟧' :=
  (Category.comp_id _).symm.trans (congrArg (deRhamShiftedHomEquiv X k z ≫ ·)
    (((shiftFunctor (DerivedCategory (Cup.ShQ (TopCat.of (ComplexPoint X)))) k).map_id
        (Q.obj (rationalDeRhamComplex X))).symm.trans
      (congrArg (shiftFunctor (DerivedCategory (Cup.ShQ (TopCat.of (ComplexPoint X)))) k).map
        ((DerivedCategory.Q (C := Cup.ShQ (TopCat.of (ComplexPoint X)))).map_id
          (rationalDeRhamComplex X)).symm)))

variable {X}

/-- `e (deRhamCup x y n h) = pairProductShQ μ (e y) (e x)`, the definition of `deRhamCup` read
through `e = deRhamShiftedHomEquiv X`. -/
theorem deRhamShiftedHomEquiv_deRhamCup {a b : ℤ} (x : H_dR^a(X)) (y : H_dR^b(X)) (n : ℤ)
    (h : a + b = n) :
    deRhamShiftedHomEquiv X n (deRhamCup x y n h) =
      pairProductShQ (TopCat.of (ComplexPoint X)) 0 (dim X.left) (deRhamWedge X)
        ((add_comm b a).trans h) (deRhamShiftedHomEquiv X b y) (deRhamShiftedHomEquiv X a x) :=
  AddEquiv.apply_symm_apply _ _

/-- **`ℂ`-linearity in the first factor.** `deRhamCup (c • x) y n h = c • deRhamCup x y n h`. -/
theorem deRhamCup_smul_left (c : ℂ) {a b : ℤ} (x : H_dR^a(X)) (y : H_dR^b(X)) (n : ℤ)
    (h : a + b = n) : deRhamCup (c • x) y n h = c • deRhamCup x y n h := by
  apply (deRhamShiftedHomEquiv X n).injective
  refine (deRhamShiftedHomEquiv_deRhamCup (c • x) y n h).trans ?_
  refine Eq.trans ?_ (deRhamShiftedHomEquiv_smul X n c (deRhamCup x y n h)).symm
  refine Eq.trans ?_ (congrArg (· ≫ (Q.map (rationalDeRhamScalar X c))⟦n⟧')
    (deRhamShiftedHomEquiv_deRhamCup x y n h).symm)
  refine Eq.trans (congrArg (pairProductShQ (TopCat.of (ComplexPoint X)) 0 (dim X.left)
    (deRhamWedge X) ((add_comm b a).trans h) (deRhamShiftedHomEquiv X b y))
    (deRhamShiftedHomEquiv_smul X a c x)) ?_
  refine Eq.trans (congrArg (pairProductShQ (TopCat.of (ComplexPoint X)) 0 (dim X.left)
    (deRhamWedge X) ((add_comm b a).trans h) · _)
    (deRhamShiftedHomEquiv_comp_map_id X b y)) ?_
  exact pairProductShQ_naturality (TopCat.of (ComplexPoint X)) 0 (dim X.left) 0
    (dim X.left) (𝟙 (rationalDeRhamComplex X)) (rationalDeRhamScalar X c)
    (rationalDeRhamScalar X c) (deRhamWedge X) (deRhamWedge X)
    (rationalDeRhamScalar_id_tensorHom_comp_deRhamWedge X c).symm ((add_comm b a).trans h) _ _

/-- **`ℂ`-linearity in the second factor.** `deRhamCup x (c • y) n h = c • deRhamCup x y n h`. -/
theorem deRhamCup_smul_right (c : ℂ) {a b : ℤ} (x : H_dR^a(X)) (y : H_dR^b(X)) (n : ℤ)
    (h : a + b = n) : deRhamCup x (c • y) n h = c • deRhamCup x y n h := by
  apply (deRhamShiftedHomEquiv X n).injective
  refine (deRhamShiftedHomEquiv_deRhamCup x (c • y) n h).trans ?_
  refine Eq.trans ?_ (deRhamShiftedHomEquiv_smul X n c (deRhamCup x y n h)).symm
  refine Eq.trans ?_ (congrArg (· ≫ (Q.map (rationalDeRhamScalar X c))⟦n⟧')
    (deRhamShiftedHomEquiv_deRhamCup x y n h).symm)
  refine Eq.trans (congrArg (pairProductShQ (TopCat.of (ComplexPoint X)) 0 (dim X.left)
    (deRhamWedge X) ((add_comm b a).trans h) · (deRhamShiftedHomEquiv X a x))
    (deRhamShiftedHomEquiv_smul X b c y)) ?_
  refine Eq.trans (congrArg (pairProductShQ (TopCat.of (ComplexPoint X)) 0 (dim X.left)
    (deRhamWedge X) ((add_comm b a).trans h) _)
    (deRhamShiftedHomEquiv_comp_map_id X a x)) ?_
  exact pairProductShQ_naturality (TopCat.of (ComplexPoint X)) 0 (dim X.left) 0
    (dim X.left) (rationalDeRhamScalar X c) (𝟙 (rationalDeRhamComplex X))
    (rationalDeRhamScalar X c) (deRhamWedge X) (deRhamWedge X)
    (rationalDeRhamScalar_tensorHom_id_comp_deRhamWedge X c).symm ((add_comm b a).trans h) _ _

variable (X) in
/-- **The de Rham cup product as a `ℂ`-bilinear map**
`H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X)`, `x ↦ y ↦ deRhamCup x y n h`, for upstream's
`ℂ`-module structure `deRhamHypercohomologyComplexModule` on each `H_dR^k(X)`. -/
def deRhamCupBilinear (a b n : ℤ) (h : a + b = n) :
    H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X) :=
  LinearMap.mk₂ ℂ (fun x y => deRhamCup x y n h)
    (fun x x' y => deRhamCup_add_left X x x' y n h)
    (fun c x y => deRhamCup_smul_left c x y n h)
    (fun x y y' => deRhamCup_add_right X x y y' n h)
    (fun c x y => deRhamCup_smul_right c x y n h)

/-- `deRhamCupBilinear X a b n h x y = deRhamCup x y n h`, by `rfl`. -/
theorem deRhamCupBilinear_apply {a b : ℤ} (n : ℤ) (h : a + b = n) (x : H_dR^a(X))
    (y : H_dR^b(X)) : deRhamCupBilinear X a b n h x y = deRhamCup x y n h :=
  rfl

variable (X) in
/-- **Scalars on the unit.** `deRhamCup (c • ι 1) (ι 1) = c • ι 1` in `H_dR^0(X)`, with
`ι = fieldToDeRhamCohomology ℚ X 0` and `1 = Cup.one X`: `deRhamCup_smul_left` and
`deRhamCup_one_one`. -/
theorem deRhamCup_smul_one_one (c : ℂ) :
    deRhamCup (c • fieldToDeRhamCohomology ℚ X 0 (Cup.one X))
        (fieldToDeRhamCohomology ℚ X 0 (Cup.one X)) ((0 : ℕ) : ℤ) (by lia) =
      c • fieldToDeRhamCohomology ℚ X 0 (Cup.one X) :=
  (deRhamCup_smul_left c _ _ _ _).trans (congrArg (c • ·) (deRhamCup_one_one X))

variable (X) in
/-- **Nonvacuity of the scalar law.** On every smooth integral `X`, for `c ≠ c'`,
`deRhamCup (c • ι 1) (ι 1) ≠ c' • ι 1`. So the first-factor law holds with no scalar other than
`c` on the right; in particular a conjugate-linear law (`c' = conj c`, `c = I`) and the trivial
action (`c' = 1`) fail. From `deRhamCup_smul_one_one` and `ι 1 ≠ 0`
(`deRhamCup_one_one_ne_zero`). -/
theorem deRhamCup_smul_one_one_ne {c c' : ℂ} (hc : c ≠ c') :
    deRhamCup (c • fieldToDeRhamCohomology ℚ X 0 (Cup.one X))
        (fieldToDeRhamCohomology ℚ X 0 (Cup.one X)) ((0 : ℕ) : ℤ) (by lia) ≠
      c' • fieldToDeRhamCohomology ℚ X 0 (Cup.one X) := by
  rw [deRhamCup_smul_one_one]
  intro h
  have h0 := deRhamCup_one_one_ne_zero X
  rw [deRhamCup_one_one] at h0
  exact hc (smul_left_injective ℂ h0 h)

end HodgeLadder
