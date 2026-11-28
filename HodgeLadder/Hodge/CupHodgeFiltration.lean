module

public import HodgeLadder.Hodge.DeRhamCupBilinear
public import HodgeLadder.Hodge.CupFiltration

/-!
# The de Rham cup product respects the Hodge filtration

Rung `cup-hodge-filtration` (front `cup`), statement (a) of
`docs/sketches/cup-hodge-filtration.md`: for `x ∈ F^p H_dR^a(X)` and `y ∈ F^q H_dR^b(X)`,
`deRhamCup x y n h ∈ F^{p+q} H_dR^n(X)`, with `F^p` upstream's `hodgeFiltration X p` and
`deRhamCup` the checked product of rung `de-rham-cup-exact`. Degrees and filtration indices are
integers, as in upstream's `hodgeFiltration X p n`.

## Proof

Write `e = deRhamShiftedHomEquiv X : H_dR^n(X) ≃+ Hom(ℚ_X[0], Ω•_ℚ[n])` and
`i_p = rationalHodgeFilteredInclusion X p : F^p Ω•_ℚ ⟶ Ω•_ℚ`.

1. `mem_hodgeFiltration_iff_exists_shiftedHom`: `x ∈ F^p H_dR^n(X)` if and only if
   `e x = x' ≫ (Q i_p)⟦n⟧'` for some `x' : ℚ_X[0] ⟶ F^p Ω•_ℚ[n]`. Upstream defines `F^p` as the
   range of `ℍ^n(X; F^p Ω•) → ℍ^n(X; Ω•)`; `hodgeFiltration_eq_range_rational` (rung
   `rational-de-rham-complex`) rewrites it through the forgotten rational truncation, and
   `rationalHypercohomologyEquiv_map` (rung `rational-hypercohomology-equiv`) turns upstream's
   `hypercohomologyMap` of the forgotten inclusion into postcomposition with `(Q i_p)⟦n⟧'`.
2. `deRhamCup x y = e⁻¹ (pairProductShQ μ (e y) (e x))` with `μ = deRhamWedge X`, so `y` sits in
   the left tensor factor. `pairProductShQ_naturality` at `f = i_q`, `g = i_p`, `k = i_{q+p}`,
   `m = deRhamWedgeFiltered X q p`, `m' = μ`, with hypothesis
   `deRhamWedgeFiltered_comp_inclusion X q p`, gives
   `e (deRhamCup x y) = pairProductShQ μ_{q,p} y' x' ≫ (Q i_{q+p})⟦n⟧'`, and step 1 applies.
   The index `q + p` is turned into `p + q` by `add_comm` on the membership.

No sign or scalar enters: membership in an additive subgroup is insensitive to both, and every
identity used is exact. The bound instances of `F^p Ω•_ℚ` (strictly in `[p, dim X]`) come from
`HodgeLadder.Hodge.WedgeSheafMap`.

## Non-vacuity

The zero product satisfies the statement. What ties it to the cup product is the pin
`fieldToDeRhamCohomology_cup` and the test file `HodgeLadder.Tests.CupHodgeFiltrationP2`: on
ℙ², the line classes lie in `F^1 H_dR^2`, their product is nonzero and lies in `F^2 H_dR^4`, and
the point class `[pt]` lies in `Hdg^2(ℙ²; ℚ)`. `Tests.planeLine_not_mem_hodgeFiltration_two` shows
the index `p + q` is sharp and both hypotheses carry content.

## Main results

* `HodgeLadder.mem_hodgeFiltration_iff_exists_shiftedHom`: upstream's `F^p H_dR^n(X)` read in
  `D(ShQ)` through `deRhamShiftedHomEquiv`
* `HodgeLadder.hodgeFiltration_eq_bot_of_degree_lt`: `F^p H_dR^n(X) = 0` for `n < p`
* `HodgeLadder.deRhamCup_mem_hodgeFiltration`: statement (a), elementwise
* `HodgeLadder.map₂_deRhamCupBilinear_le`: statement (a) for upstream's `ℂ`-submodules,
  `Submodule.map₂ (deRhamCupBilinear X a b n h) F^p F^q ≤ F^{p+q}`
* `HodgeLadder.cupRespectsHodgeFiltrationRational_holds`: statement (a_ℚ),
  `CupRespectsHodgeFiltrationRational X`, from (a) and `fieldToDeRhamCohomology_cup`
* `HodgeLadder.cupPreservesHodgeClasses_holds`: statement (b), `CupPreservesHodgeClasses X`,
  through `cupPreservesHodgeClasses_of_rational` (rung `cup-hodge-reduction`)
-/

@[expose] public section

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

/-- **Filtered classes through the bridge.** For `w ∈ ℍ^n(X; forget(F^p Ω•_ℚ))`, the class
`hypercohomologyMap (forget(i_p) ≫ forgetRationalDeRhamIso X) w ∈ H_dR^n(X)` goes under
`deRhamShiftedHomEquiv X n` to `rationalHypercohomologyEquiv X (F^p Ω•_ℚ) n w ≫ (Q i_p)⟦n⟧'`,
with `i_p = rationalHodgeFilteredInclusion X p`. From `rationalHypercohomologyEquiv_map`. -/
theorem deRhamShiftedHomEquiv_filtered (p n : ℤ)
    (w : ℍ^n(X; (forgetComplex X).obj (rationalHodgeFilteredComplex X p))) :
    deRhamShiftedHomEquiv X n (hypercohomologyMap X ((forgetComplex X).map
        (rationalHodgeFilteredInclusion X p) ≫ (forgetRationalDeRhamIso X).hom) n w) =
      rationalHypercohomologyEquiv X (rationalHodgeFilteredComplex X p) n w ≫
        (Q.map (rationalHodgeFilteredInclusion X p))⟦n⟧' := by
  have e : ((forgetComplex X).map (rationalHodgeFilteredInclusion X p) ≫
      (forgetRationalDeRhamIso X).hom) ≫ (forgetRationalDeRhamIso X).inv =
      (forgetComplex X).map (rationalHodgeFilteredInclusion X p) := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n
    (hypercohomologyMap X (forgetRationalDeRhamIso X).inv n _) = _
  refine Eq.trans (congrArg (rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n)
    ((hypercohomologyMap_comp_apply X _ (forgetRationalDeRhamIso X).inv n w).symm.trans
      (congrArg (fun f => hypercohomologyMap X f n w) e))) ?_
  exact rationalHypercohomologyEquiv_map X (rationalHodgeFilteredInclusion X p) n w

/-- **Upstream's Hodge filtration in the derived category of rational sheaves.**
`x ∈ hodgeFiltration X p n` if and only if `deRhamShiftedHomEquiv X n x` factors as
`x' ≫ (Q i_p)⟦n⟧'` through the rational truncation `F^p Ω•_ℚ`, with
`i_p = rationalHodgeFilteredInclusion X p`. From `hodgeFiltration_eq_range_rational` and
`deRhamShiftedHomEquiv_filtered`. -/
theorem mem_hodgeFiltration_iff_exists_shiftedHom (p n : ℤ) (x : H_dR^n(X)) :
    x ∈ hodgeFiltration X p n ↔
      ∃ x' : ShiftedHom (Q.obj (unitComplex (TopCat.of (ComplexPoint X))))
        (Q.obj (rationalHodgeFilteredComplex X p)) n,
        deRhamShiftedHomEquiv X n x = x' ≫ (Q.map (rationalHodgeFilteredInclusion X p))⟦n⟧' := by
  rw [hodgeFiltration_eq_range_rational]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, deRhamShiftedHomEquiv_filtered X p n w⟩
  · rintro ⟨x', hx'⟩
    refine ⟨(rationalHypercohomologyEquiv X (rationalHodgeFilteredComplex X p) n).symm x', ?_⟩
    apply (deRhamShiftedHomEquiv X n).injective
    refine (deRhamShiftedHomEquiv_filtered X p n _).trans (Eq.trans ?_ hx'.symm)
    exact congrArg (· ≫ (Q.map (rationalHodgeFilteredInclusion X p))⟦n⟧')
      (AddEquiv.apply_symm_apply (rationalHypercohomologyEquiv X (rationalHodgeFilteredComplex X p) n) x')

/-- **The Hodge filtration vanishes above the degree.** For `n < p`, `hodgeFiltration X p n = ⊥`:
`ℚ_X[0]` is `≤ 0` and `(F^p Ω•_ℚ)[n]` is `≥ p − n ≥ 1` for Mathlib's t-structure on the derived
category, so every `x'` of `mem_hodgeFiltration_iff_exists_shiftedHom` is zero. Above the
dimension, upstream's `AlgebraicGeometry.ComplexPoint.hodgeFiltration_eq_bot_of_lt` applies. -/
theorem hodgeFiltration_eq_bot_of_degree_lt (p n : ℤ) (hn : n < p) :
    hodgeFiltration X p n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨x', hx'⟩ := (mem_hodgeFiltration_iff_exists_shiftedHom X p n x).mp hx
  have h1 : (Q.obj (unitComplex (TopCat.of (ComplexPoint X)))).IsLE 0 := inferInstance
  have h3 : ((Q.obj (rationalHodgeFilteredComplex X p))⟦n⟧).IsGE (p - n) :=
    TStructure.t.isGE_shift _ p n (p - n) (by lia)
  rw [TStructure.t.zero_of_isLE_of_isGE x' 0 (p - n) (by lia) h1 h3, Limits.zero_comp] at hx'
  exact (AddSubgroup.mem_bot).mpr ((deRhamShiftedHomEquiv X n).map_eq_zero_iff.mp hx')

variable {X} in
/-- **The de Rham cup product respects the Hodge filtration** (statement (a)). For
`x ∈ F^p H_dR^a(X)`, `y ∈ F^q H_dR^b(X)` and `h : a + b = n`,
`deRhamCup x y n h ∈ F^{p+q} H_dR^n(X)`, with upstream's `hodgeFiltration`. Naturality of the
pairing product along the inclusions of the truncations and the filtered wedge
`deRhamWedgeFiltered X q p`. -/
theorem deRhamCup_mem_hodgeFiltration {a b n : ℤ} (h : a + b = n) {p q : ℤ}
    {x : H_dR^a(X)} {y : H_dR^b(X)}
    (hx : x ∈ hodgeFiltration X p a) (hy : y ∈ hodgeFiltration X q b) :
    deRhamCup x y n h ∈ hodgeFiltration X (p + q) n := by
  obtain ⟨x', hx'⟩ := (mem_hodgeFiltration_iff_exists_shiftedHom X p a x).mp hx
  obtain ⟨y', hy'⟩ := (mem_hodgeFiltration_iff_exists_shiftedHom X q b y).mp hy
  rw [add_comm p q]
  refine (mem_hodgeFiltration_iff_exists_shiftedHom X (q + p) n _).mpr
    ⟨pairProductShQ (TopCat.of (ComplexPoint X)) p (dim X.left) (deRhamWedgeFiltered X q p)
      ((add_comm b a).trans h) y' x', ?_⟩
  refine (deRhamShiftedHomEquiv_deRhamCup x y n h).trans ?_
  refine Eq.trans (congrArg (pairProductShQ (TopCat.of (ComplexPoint X)) 0 (dim X.left)
    (deRhamWedge X) ((add_comm b a).trans h) · _) hy') ?_
  refine Eq.trans (congrArg (pairProductShQ (TopCat.of (ComplexPoint X)) 0 (dim X.left)
    (deRhamWedge X) ((add_comm b a).trans h) _ ·) hx') ?_
  exact pairProductShQ_naturality (TopCat.of (ComplexPoint X)) p (dim X.left) 0 (dim X.left)
    (rationalHodgeFilteredInclusion X q) (rationalHodgeFilteredInclusion X p)
    (rationalHodgeFilteredInclusion X (q + p)) (deRhamWedgeFiltered X q p) (deRhamWedge X)
    (deRhamWedgeFiltered_comp_inclusion X q p) ((add_comm b a).trans h) y' x'

/-- **Statement (a) for submodules.** `Submodule.map₂ (deRhamCupBilinear X a b n h) F^p F^q`
lies in `F^{p+q}`, for upstream's `hodgeFiltrationComplexSubmodule`. From
`deRhamCup_mem_hodgeFiltration` by `Submodule.map₂_le`. -/
theorem map₂_deRhamCupBilinear_le (a b n : ℤ) (h : a + b = n) (p q : ℤ) :
    Submodule.map₂ (deRhamCupBilinear X a b n h) (hodgeFiltrationComplexSubmodule X p a)
      (hodgeFiltrationComplexSubmodule X q b) ≤ hodgeFiltrationComplexSubmodule X (p + q) n :=
  Submodule.map₂_le.mpr fun _ hx _ hy => deRhamCup_mem_hodgeFiltration h hx hy

/-- **Statement (a_ℚ).** `CupRespectsHodgeFiltrationRational X` holds: for rational classes with
`ι α ∈ F^p` and `ι β ∈ F^q`, `ι (α ∪ β) ∈ F^{p+q}`. From `fieldToDeRhamCohomology_cup` and
`deRhamCup_mem_hodgeFiltration`. -/
theorem cupRespectsHodgeFiltrationRational_holds : CupRespectsHodgeFiltrationRational X := by
  intro a b n h p q α β hα hβ
  rw [fieldToDeRhamCohomology_cup X h α β]
  exact deRhamCup_mem_hodgeFiltration _ hα hβ

/-- **Statement (b).** `CupPreservesHodgeClasses X` holds: the cup product of Hodge classes
`α ∈ Hdg^p(X; ℚ)` and `β ∈ Hdg^q(X; ℚ)` lies in `Hdg^{p+q}(X; ℚ)`. From
`cupRespectsHodgeFiltrationRational_holds` and `cupPreservesHodgeClasses_of_rational`. -/
theorem cupPreservesHodgeClasses_holds : CupPreservesHodgeClasses X :=
  cupPreservesHodgeClasses_of_rational X (cupRespectsHodgeFiltrationRational_holds X)

end HodgeLadder
