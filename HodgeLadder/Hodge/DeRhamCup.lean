module

public import HodgeLadder.Hodge.WedgeSheafMap
public import HodgeLadder.Hodge.RationalHypercohomology
public import HodgeLadder.Hodge.DeRhamInjective
public import HodgeLadder.Cup.SingularUnit
public import HodgeLadder.General.ComplexPoint
public import Other.AlgebraicGeometry.Cohomology.RationalDegreeZero

/-!
# The de Rham cup product and its exact identity with the rational cup product

Rung `de-rham-cup-exact` (front `cup`, split from `de-rham-cup`; red team
`docs/sketches/de-rham-cup-exact.redteam.md`). Upstream has no product on
holomorphic de Rham hypercohomology `H_dR^*(X) = ℍ^*(X; Ω•(X))`. This file defines one from the
pairing product of rung `pairing-product` and the wedge `μ = deRhamWedge X : Ω•_ℚ ⊗ Ω•_ℚ ⟶ Ω•_ℚ`
of rung `wedge-sheaf-map`, and pins it to the ladder's rational cup product `HodgeLadder.Cup.cup`
through upstream's `ι = fieldToDeRhamCohomology ℚ X`: `ι (α ∪ β) = deRhamCup (ι α) (ι β)`,
exact, with no sign and no scalar.

## Construction

`deRhamShiftedHomEquiv X n : H_dR^n(X) ≃+ Hom(ℚ_X[0], Ω•_ℚ[n])` is upstream's hypercohomology
along `forgetRationalDeRhamIso X : forget(Ω•_ℚ) ≅ Ω•(X)` (inverse direction), followed by
`rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n` (rung
`rational-hypercohomology-equiv`). On it,

`deRhamCup x y n h := e⁻¹ (pairProductShQ μ (e y) (e x))`, for `x ∈ H_dR^a`, `y ∈ H_dR^b`,
`h : a + b = n`,

that is `pairProduct μ y x` (red team of `cup-hodge-filtration`, finding 5). The primitive is
`pairProduct m x' y' = y' ≫ (x' ⊗ B)⟦b⟧ ≫ m`, so `deRhamCup x y = e x ≫ (e y ⊗ Ω•_ℚ)⟦a⟧ ≫ μ`:
the class `x` is applied first, as in the diagrammatic order of `HodgeLadder.Cup.cup`
(`α ∪ β = α.comp β`, row "Cup product" of `docs/conventions.md`), and the factor `y` is the left
tensor factor of `μ`. The degree proof `b + a = n` that `pairProductShQ` takes is
`(add_comm b a).trans h`; the user-facing degree bookkeeping is `h : a + b = n`.

## Proof of the identity

`deRhamShiftedHomEquiv_fieldToDeRhamCohomology`: `e (ι γ) = γ̂ ≫ (Q u)⟦n⟧`, where `γ̂` is
`(Cup.rationalExtEquiv _ n γ).hom` (`rationalUnitShiftedHom`) and `u = deRhamUnitShQ X`. It
combines `forget_rationalDeRhamUnit` (the unit lies over upstream's
`fieldToHolomorphicDeRhamComplexInt ℚ X`), `rationalHypercohomologyEquiv_map` and
`rationalHypercohomologyEquiv_rationalUnitComplex` (agreement with `rationalExtEquiv`, no scalar).
Then `pairProductShQ_naturality` at `f = g = k = u`, `m = unitComplexMul`, `m' = μ`, with
hypothesis `deRhamWedge_unit_unit`, and `pairProductShQ_unit` reduce the right side to
`(α̂.comp β̂) ≫ (Q u)⟦n⟧`, which is the left side by `rationalCohomologyEquivExt_cup` and
Mathlib's `Ext.comp_hom`. No sign enters: the naturality, the unit clause and the unit law are
exact, and the shift in the first variable of the tensor (`mapBifunctorShift₁Iso`) has none.

## Instances for consumers

Statements about `deRhamCup` at a variable `X` that go through `deRhamShiftedHomEquiv` or
`pairProductShQ` activate the local instances of `HodgeLadder.Hodge.RationalHypercohomology`,
with upstream's `implicit_reducible` attributes as at the top of this file:

```
attribute [local instance] HodgeLadder.rhHasDerivedCategory HodgeLadder.rhSiteHasDerivedCategory
  HodgeLadder.rhHasExt HodgeLadder.rhQHasDerivedCategory HodgeLadder.rhTensorAdditive
  HodgeLadder.rhForgetAdditive HodgeLadder.rhTensorPFL HodgeLadder.rhTensorPFC
  HodgeLadder.rhForgetPFL HodgeLadder.rhForgetPFC
```

For scalar laws, or anything stated with `HomologicalComplex.tensorHom` or the left unitor at
`TopCat.of (ComplexPoint X)`, add `HodgeLadder.Cup.sheafMonoidal`,
`HodgeLadder.analyticShQMonoidal` and the three `wsm*` instances of
`HodgeLadder.Hodge.WedgeSheafMap` (`wsmCurriedTensorAdditive`, `wsmTensorLeftAdditive`,
`wsmTensorRightPreservesEmpty`). Statements at a concrete space that only apply
`fieldToDeRhamCohomology_cup` (the tests on `gm2` and `projectivePlane`) needed none.

## Main definitions

* `HodgeLadder.deRhamShiftedHomEquiv X n`: `H_dR^n(X) ≃+ Hom(ℚ_X[0], Ω•_ℚ[n])`
* `HodgeLadder.deRhamCup x y n h : H_dR^n(X)` for `x : H_dR^a(X)`, `y : H_dR^b(X)`, `a + b = n`
* `HodgeLadder.rationalUnitShiftedHom γ`: the `Ext` class of `γ ∈ H^n(X; ℚ)` as a morphism
  `ℚ_X[0] ⟶ ℚ_X[0][n]`, typed from `unitComplex`

## Main results

* `HodgeLadder.deRhamCup_add_left`, `HodgeLadder.deRhamCup_add_right`: biadditivity
* `HodgeLadder.rationalUnitShiftedHom_cup`: the cup product as composition of shifted morphisms
* `HodgeLadder.deRhamShiftedHomEquiv_fieldToDeRhamCohomology`: `e (ι γ) = γ̂ ≫ (Q u)⟦n⟧`
* `HodgeLadder.fieldToDeRhamCohomology_cup`: `ι (α ∪ β) = deRhamCup (ι α) (ι β)`, exact, no sign
* `HodgeLadder.deRhamCup_one_one`: `deRhamCup (ι 1) (ι 1) = ι 1`;
  `HodgeLadder.deRhamCup_one_one_ne_zero`, `HodgeLadder.deRhamCup_one_one_ne_neg`: the product
  is nonzero and differs from its negative there, on every smooth integral `X`
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

section Rational

variable {X : Over (Spec ↧ℂ)}

/-- The `Ext` class `(Cup.rationalExtEquiv _ n γ).hom` of `γ ∈ H^n(X; ℚ)`, a morphism
`ℚ_X[0] ⟶ ℚ_X[0][n]` in the derived category of sheaves of `ℚ`-vector spaces, typed with source
and target `unitComplex (TopCat.of (ComplexPoint X))` as `pairProductShQ` asks. By definition. -/
def rationalUnitShiftedHom {n : ℕ} (γ : H^n(X; ℚ)) :
    ShiftedHom (Q.obj (unitComplex (TopCat.of (ComplexPoint X))))
      (Q.obj (unitComplex (TopCat.of (ComplexPoint X)))) (n : ℤ) :=
  (Cup.rationalExtEquiv (TopCat.of (ComplexPoint X)) n γ).hom

/-- **The rational cup product as composition.** `(α ∪ β)^ = α̂.comp β̂`, Mathlib's composition of
shifted morphisms, from `rationalCohomologyEquivExt_cup` and `Ext.comp_hom`. Exact, no sign. -/
theorem rationalUnitShiftedHom_cup {a b n : ℕ} (h : a + b = n) (α : H^a(X; ℚ))
    (β : H^b(X; ℚ)) :
    rationalUnitShiftedHom (Cup.cup α β n h) =
      (rationalUnitShiftedHom α).comp (rationalUnitShiftedHom β) (by lia) := by
  change (Cup.rationalCohomologyEquivExt X n (Cup.cup α β n h)).hom = _
  rw [Cup.rationalCohomologyEquivExt_cup, Abelian.Ext.comp_hom]
  rfl

end Rational

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- **De Rham classes as morphisms in the derived category of rational sheaves.**
`H_dR^n(X) = ℍ^n(X; Ω•(X)) ≃+ Hom(ℚ_X[0], Ω•_ℚ[n])`: upstream's hypercohomology along the inverse
of `forgetRationalDeRhamIso X : forget(Ω•_ℚ) ≅ Ω•(X)`, then `rationalHypercohomologyEquiv`. -/
def deRhamShiftedHomEquiv (n : ℤ) :
    H_dR^n(X) ≃+ ShiftedHom (Q.obj (unitComplex (TopCat.of (ComplexPoint X))))
      (Q.obj (rationalDeRhamComplex X)) n :=
  (hypercohomologyMapIso X (forgetRationalDeRhamIso X) n).symm.trans
    (rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n)

variable {X} in
/-- **The de Rham cup product** `deRhamCup x y n h ∈ H_dR^n(X)` of `x ∈ H_dR^a(X)` and
`y ∈ H_dR^b(X)`, `h : a + b = n`: the pairing product `pairProduct μ y x` of rung
`pairing-product` with `μ = deRhamWedge X`, read through `deRhamShiftedHomEquiv`. In the
diagrammatic order of `HodgeLadder.Cup.cup` (the class `x` is applied first;
`fieldToDeRhamCohomology_cup`); `y` is the left tensor factor of `μ`. Convention: row
"de Rham cup order" of `docs/conventions.md`. -/
def deRhamCup {a b : ℤ} (x : H_dR^a(X)) (y : H_dR^b(X)) (n : ℤ) (h : a + b = n) : H_dR^n(X) :=
  (deRhamShiftedHomEquiv X n).symm
    (pairProductShQ (TopCat.of (ComplexPoint X)) 0 (dim X.left) (deRhamWedge X)
      ((add_comm b a).trans h) (deRhamShiftedHomEquiv X b y) (deRhamShiftedHomEquiv X a x))

/-- **Additivity in the first factor**, from `pairProductShQ_add_right`. -/
theorem deRhamCup_add_left {a b : ℤ} (x x' : H_dR^a(X)) (y : H_dR^b(X)) (n : ℤ)
    (h : a + b = n) : deRhamCup (x + x') y n h = deRhamCup x y n h + deRhamCup x' y n h := by
  unfold deRhamCup
  rw [map_add (deRhamShiftedHomEquiv X a), pairProductShQ_add_right, map_add]

/-- **Additivity in the second factor**, from `pairProductShQ_add_left`. -/
theorem deRhamCup_add_right {a b : ℤ} (x : H_dR^a(X)) (y y' : H_dR^b(X)) (n : ℤ)
    (h : a + b = n) : deRhamCup x (y + y') n h = deRhamCup x y n h + deRhamCup x y' n h := by
  unfold deRhamCup
  rw [map_add (deRhamShiftedHomEquiv X b), pairProductShQ_add_left, map_add]

/-- **The image of a rational class.** `e (ι γ) = γ̂ ≫ (Q u)⟦n⟧` for `γ ∈ H^n(X; ℚ)`, with
`e = deRhamShiftedHomEquiv X n`, `ι = fieldToDeRhamCohomology ℚ X n`, `γ̂ = rationalUnitShiftedHom γ`
and `u = deRhamUnitShQ X`. Exact, no scalar: from `forget_rationalDeRhamUnit`,
`rationalHypercohomologyEquiv_map` and `rationalHypercohomologyEquiv_rationalUnitComplex`. -/
theorem deRhamShiftedHomEquiv_fieldToDeRhamCohomology (n : ℕ) (γ : H^n(X; ℚ)) :
    deRhamShiftedHomEquiv X n (fieldToDeRhamCohomology ℚ X n γ) =
      rationalUnitShiftedHom γ ≫ (Q.map (deRhamUnitShQ X))⟦(n : ℤ)⟧' := by
  set z := (unitHypercohomologyEquiv X n).symm γ with hz
  have hγ : γ = unitHypercohomologyEquiv X n z := (AddEquiv.apply_symm_apply _ _).symm
  have h1 : (hypercohomologyAddEquivConstantCohomology ℚ X n).symm γ =
      hypercohomologyMap X (forgetUnitComplexIso X).hom n z := by
    rw [hγ]
    exact AddEquiv.symm_apply_apply _ _
  have h2 : fieldToDeRhamCohomology ℚ X n γ = hypercohomologyMap X
      ((forgetComplex X).map (rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom) n z := by
    rw [forget_rationalDeRhamUnit, hypercohomologyMap_comp_apply, ← h1]
    rfl
  have h3 : deRhamShiftedHomEquiv X n (fieldToDeRhamCohomology ℚ X n γ) =
      rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n
        (hypercohomologyMap X ((forgetComplex X).map (rationalDeRhamUnit X)) n z) := by
    refine (congrArg (deRhamShiftedHomEquiv X n) h2).trans ?_
    change rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n
      (hypercohomologyMap X (forgetRationalDeRhamIso X).inv n _) = _
    have e : ((forgetComplex X).map (rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom) ≫
        (forgetRationalDeRhamIso X).inv = (forgetComplex X).map (rationalDeRhamUnit X) := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact congrArg (rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n)
      ((hypercohomologyMap_comp_apply X _ (forgetRationalDeRhamIso X).inv n z).symm.trans
        (congrArg (fun f => hypercohomologyMap X f n z) e))
  refine h3.trans ?_
  refine (rationalHypercohomologyEquiv_map X (rationalDeRhamUnit X) n z).trans ?_
  have h4 : rationalHypercohomologyEquiv X (rationalUnitComplex X) n z =
      (Cup.rationalExtEquiv (TopCat.of (ComplexPoint X)) n γ).hom :=
    (rationalHypercohomologyEquiv_rationalUnitComplex X n z).trans
      (congrArg (fun t => (Cup.rationalExtEquiv (TopCat.of (ComplexPoint X)) n t).hom) hγ.symm)
  exact congrArg (· ≫ (Q.map (deRhamUnitShQ X))⟦(n : ℤ)⟧') h4

/-- **The de Rham cup product extends the rational cup product, exactly.** For `α ∈ H^a(X; ℚ)`,
`β ∈ H^b(X; ℚ)` and `a + b = n`, `ι (α ∪ β) = deRhamCup (ι α) (ι β)`, with
`ι = fieldToDeRhamCohomology ℚ X` and `∪` the ladder's Yoneda cup product `HodgeLadder.Cup.cup`.
No sign and no scalar. The degree proof of `deRhamCup` is `(a : ℤ) + b = n`, from `h`. -/
theorem fieldToDeRhamCohomology_cup {a b n : ℕ} (h : a + b = n) (α : H^a(X; ℚ))
    (β : H^b(X; ℚ)) :
    fieldToDeRhamCohomology ℚ X n (Cup.cup α β n h) =
      deRhamCup (fieldToDeRhamCohomology ℚ X a α) (fieldToDeRhamCohomology ℚ X b β) n
        (by lia) := by
  refine (AddEquiv.eq_symm_apply (deRhamShiftedHomEquiv X n)).mpr ?_
  rw [deRhamShiftedHomEquiv_fieldToDeRhamCohomology, deRhamShiftedHomEquiv_fieldToDeRhamCohomology,
    deRhamShiftedHomEquiv_fieldToDeRhamCohomology]
  rw [pairProductShQ_naturality (TopCat.of (ComplexPoint X)) 0 0 0 (dim X.left)
    (deRhamUnitShQ X) (deRhamUnitShQ X) (deRhamUnitShQ X)
    (unitComplexMul (TopCat.of (ComplexPoint X))) (deRhamWedge X) (deRhamWedge_unit_unit X)]
  rw [pairProductShQ_unit, rationalUnitShiftedHom_cup]


/-- **The unit squares to itself.** `deRhamCup (ι 1) (ι 1) = ι 1` in `H_dR^0(X)`, with
`1 = HodgeLadder.Cup.one X`: `fieldToDeRhamCohomology_cup` and `Cup.one_cup`. -/
theorem deRhamCup_one_one :
    deRhamCup (fieldToDeRhamCohomology ℚ X 0 (Cup.one X))
        (fieldToDeRhamCohomology ℚ X 0 (Cup.one X)) ((0 : ℕ) : ℤ) (by lia) =
      fieldToDeRhamCohomology ℚ X 0 (Cup.one X) :=
  (fieldToDeRhamCohomology_cup X (zero_add 0) _ _).symm.trans
    (congrArg (fieldToDeRhamCohomology ℚ X 0) (Cup.one_cup _))

/-- **Nonvacuity.** On every smooth integral `X`, `deRhamCup (ι 1) (ι 1) ≠ 0`: by
`deRhamCup_one_one` it is `ι 1`; `ι` is injective (`fieldToDeRhamCohomology_rat_injective`),
`1` is upstream's `fieldCohomologyUnit ℚ X` (`Cup.one_eq_fieldCohomologyUnit`), which is nonzero
on a space with a point (`rationalCohomologyUnit_ne_zero`, `nonempty_complexPoint`). So the zero
product does not satisfy `fieldToDeRhamCohomology_cup`. -/
theorem deRhamCup_one_one_ne_zero :
    deRhamCup (fieldToDeRhamCohomology ℚ X 0 (Cup.one X))
        (fieldToDeRhamCohomology ℚ X 0 (Cup.one X)) ((0 : ℕ) : ℤ) (by lia) ≠ 0 := by
  have := nonempty_complexPoint X
  rw [deRhamCup_one_one]
  intro h
  apply rationalCohomologyUnit_ne_zero X
  rw [← Cup.one_eq_fieldCohomologyUnit]
  exact fieldToDeRhamCohomology_rat_injective X 0 (h.trans (map_zero _).symm)

/-- **Sign separation.** On every smooth integral `X`, `deRhamCup (ι 1) (ι 1) ≠ −ι 1`: the left
side is `ι 1 ≠ 0` (`deRhamCup_one_one_ne_zero`), and `x = −x` forces `x = 0` in the `ℂ`-vector
space `H_dR^0(X)`. So the product `pairProduct (−μ) y x` does not satisfy
`fieldToDeRhamCohomology_cup`. -/
theorem deRhamCup_one_one_ne_neg :
    deRhamCup (fieldToDeRhamCohomology ℚ X 0 (Cup.one X))
        (fieldToDeRhamCohomology ℚ X 0 (Cup.one X)) ((0 : ℕ) : ℤ) (by lia) ≠
      -fieldToDeRhamCohomology ℚ X 0 (Cup.one X) := by
  have h0 := deRhamCup_one_one_ne_zero X
  rw [deRhamCup_one_one] at h0 ⊢
  intro h
  apply h0
  have h2 : (2 : ℂ) • fieldToDeRhamCohomology ℚ X 0 (Cup.one X) = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end HodgeLadder
