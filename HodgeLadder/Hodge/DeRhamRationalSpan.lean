module

public import HodgeLadder.General.SimplicialCochainSpan
public import LefschetzPort.AlgebraicGeometry.ProjectiveFiniteHomology
public import LefschetzPort.AlgebraicGeometry.BettiScalarNaturality
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact

/-!
# The de Rham images of rational classes span de Rham cohomology

Rung `de-rham-rational-span` (stated), an input of target T1 of the Markman inventory
(`docs/sketches/cup-hodge-filtration.md`, section "de-rham-rational-span: statement"; red team
`docs/sketches/de-rham-rational-span.redteam.md`). For a smooth projective integral scheme `X`
over `ℂ`, the complex span of the image of upstream's
`ι = fieldToDeRhamCohomology ℚ X n : H^n(X(ℂ); ℚ) →+ H_dR^n(X)` is all of `H_dR^n(X)`.

The route goes through singular cohomology. A complex class `γ` is written as a finite sum of
classes pushed along the additive maps `ratScaled z : q ↦ z q`; the de Rham image of such a class
is `z • ι β`.

1. Sheaf side (`smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt`,
   `span_range_fieldToDeRhamCohomology_rat_of_mem_closure`): the de Rham image of the class
   pushed along `ratScaled z` is `z • ι β`, exactly, so additive generation by these classes
   gives the span.
2. Comparison (rung `betti-additive-naturality`, checked): the port's
   `scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange`, natural in additive maps
   of coefficients since the port's generalization from ring maps.
3. Cochains (rung `simplicial-complex-span`, stated): `HodgeLadder.SimplicialComplexSpan`.
4. Finiteness: the port's `module_finite_singularHomology` (the analytic space of a smooth
   projective variety is a compact manifold).

`mem_closure_ratScaled` assembles 2 and 3 under explicit Hausdorff, paracompactness and
finite-homology hypotheses; `deRhamRationalSpan_of_simplicialComplexSpan` supplies them from
`IsProjective` with 4 and applies 1.

## Main definitions

* `HodgeLadder.DeRhamRationalSpan`: the statement of the rung, for all smooth projective
  integral `X` and all degrees.

## Main results

* `HodgeLadder.span_range_fieldToDeRhamCohomology_rat_of_mem_closure`: the sheaf-side reduction.
* `HodgeLadder.mem_closure_ratScaled`: the assembly, conditional on `SimplicialComplexSpan`.
* `HodgeLadder.span_range_fieldToDeRhamCohomology_rat_of_simplicialComplexSpan`: the span for one
  `X` with the topological inputs as hypotheses (no projectivity).
* `HodgeLadder.deRhamRationalSpan_of_simplicialComplexSpan`:
  `SimplicialComplexSpan → DeRhamRationalSpan`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry ComplexPoint

namespace HodgeLadder

/-- **Rung `de-rham-rational-span`** (stated). For every smooth projective integral scheme `X`
over `ℂ` and every degree `n`, the complex span of the image of
`ι : H^n(X(ℂ); ℚ) → H_dR^n(X)` is all of `H_dR^n(X)`. -/
def DeRhamRationalSpan : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ),
    Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤

variable (X : Over (Spec ↧ℂ))

/-- The inclusion of rational constants followed by multiplication by `z` on the complex
constant sheaf is change of coefficients along `ratScaled z`. -/
lemma fieldToComplexConstantSheaf_comp_complexScalarSheaf (z : ℂ) :
    fieldToComplexConstantSheaf ℚ X ≫ complexScalarSheaf X z =
      AlgebraicTopology.Singular.constantCoefficientSheafMap (ratScaled z)
        (TopCat.of (ComplexPoint X)) := by
  change (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map _ = (presheafToSheaf _ _).map _
  rw [← Functor.map_comp]
  congr 1

/-- The same identity on integer-indexed complexes. -/
lemma fieldToComplexConstantSheafComplexInt_comp_complexScalarComplexInt (z : ℂ) :
    fieldToComplexConstantSheafComplexInt ℚ X ≫ complexScalarComplexInt X z =
      constantCoefficientSheafComplexIntMap X (ratScaled z) := by
  unfold fieldToComplexConstantSheafComplexInt complexScalarComplexInt complexScalarComplex
    constantCoefficientSheafComplexIntMap
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    fieldToComplexConstantSheaf_comp_complexScalarSheaf]

/-- A complex multiple of the de Rham image of a rational class is the de Rham image of the
class pushed along `ratScaled z`: `z • ι' β = e ((ratScaled z)_* β)`, exactly. -/
lemma smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt [IsIntegral X.left]
    [Smooth X.hom] (n : ℤ) (z : ℂ) (β : ℍ^n(X; constantFieldSheafComplexInt ℚ X)) :
    z • hypercohomologyMap X (fieldToHolomorphicDeRhamComplexInt ℚ X) n β =
      hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n
        (hypercohomologyMap X (constantCoefficientSheafComplexIntMap X (ratScaled z)) n β) := by
  have h1 : fieldToHolomorphicDeRhamComplexInt ℚ X ≫ scalarHolomorphicDeRhamComplexInt X z =
      constantCoefficientSheafComplexIntMap X (ratScaled z) ≫
        constantsToHolomorphicDeRhamComplexInt X := by
    rw [fieldToHolomorphicDeRhamComplexInt, Category.assoc,
      constantsToHolomorphicDeRhamComplexInt_scalar, ← Category.assoc,
      fieldToComplexConstantSheafComplexInt_comp_complexScalarComplexInt]
    rfl
  rw [deRham_complex_smul_eq]
  exact (hypercohomologyMap_comp_apply X _ _ n β).symm.trans
    ((congrArg (fun f ↦ hypercohomologyMap X f n β) h1).trans
      (hypercohomologyMap_comp_apply X _ _ n β))

/-- Reduction: if complex constant-sheaf cohomology is additively generated by the classes
pushed along `ratScaled z` from rational classes, the de Rham images of rational classes
span. -/
theorem span_range_fieldToDeRhamCohomology_rat_of_mem_closure [IsIntegral X.left]
    [Smooth X.hom] (n : ℕ)
    (h : ∀ γ : ScalarCohomology X ℂ n, γ ∈ AddSubgroup.closure (⋃ z : ℂ, Set.range
      (hypercohomologyMap X (constantCoefficientSheafComplexIntMap X (ratScaled z)) n))) :
    Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤ := by
  let P := (Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n))).toAddSubgroup
  let e : ScalarCohomology X ℂ n →+ H_dR^n(X) :=
    hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n
  have hle : AddSubgroup.closure (⋃ z : ℂ, Set.range
      (hypercohomologyMap X (constantCoefficientSheafComplexIntMap X (ratScaled z)) n)) ≤
      P.comap e := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨_, ⟨z, rfl⟩, β, rfl⟩
    change e _ ∈ Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n))
    have hz := smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt X n z β
    change _ = e _ at hz
    rw [← hz]
    refine Submodule.smul_mem _ z
      (Submodule.subset_span ⟨hypercohomologyAddEquivConstantCohomology ℚ X n β, ?_⟩)
    exact congrArg (hypercohomologyMap X (fieldToHolomorphicDeRhamComplexInt ℚ X) n)
      ((hypercohomologyAddEquivConstantCohomology ℚ X n).symm_apply_apply β)
  rw [eq_top_iff]
  intro y _
  obtain ⟨γ, rfl⟩ := (complexConstantCohomologyDeRhamAddEquiv X n).surjective y
  exact hle (h γ)

set_option backward.isDefEq.respectTransparency false in
/-- Assembly: if `SimplicialComplexSpan` holds, `X(ℂ)` is Hausdorff with paracompact opens and
its integral singular homology is finitely generated in degree `n`, then complex
constant-sheaf cohomology of degree `n` is additively generated by the classes pushed along
`ratScaled z` from rational classes. Uses the port's comparison with singular cohomology and its
naturality in additive maps of coefficients. -/
theorem mem_closure_ratScaled [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℕ)
    [Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ
      (TopCat.of (ComplexPoint X))).homology n)]
    (hS : SimplicialComplexSpan) (γ : ScalarCohomology X ℂ n) :
    γ ∈ AddSubgroup.closure (⋃ z : ℂ, Set.range
      (hypercohomologyMap X (constantCoefficientSheafComplexIntMap X (ratScaled z)) n)) := by
  let Y := TopCat.of (ComplexPoint X)
  let Eℂ := scalarCohomologyAddEquivOrdinarySingularCohomology X ℂ n
  let Eℚ := scalarCohomologyAddEquivOrdinarySingularCohomology X ℚ n
  let Fℂ := (AlgebraicTopology.Singular.ordinaryForgottenSingularCochainHomologyIso ℂ Y n)
    |>.addCommGroupIsoToAddEquiv
  let Fℚ := (AlgebraicTopology.Singular.ordinaryForgottenSingularCochainHomologyIso ℚ Y n)
    |>.addCommGroupIsoToAddEquiv
  let : Module.Finite ℤ (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)).homology n) :=
    inferInstanceAs (Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ
      (TopCat.of (ComplexPoint X))).homology n))
  let Φ := (Fℂ.trans Eℂ.symm).toAddMonoidHom
  have hα := hS (TopCat.toSSet.obj Y) n (Fℂ.symm (Eℂ γ))
  have hγ : Φ (Fℂ.symm (Eℂ γ)) = γ := by
    simp only [Φ, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, AddEquiv.trans_apply,
      AddEquiv.apply_symm_apply]
    exact Eℂ.symm_apply_apply γ
  have key : AddSubgroup.closure (⋃ z : ℂ, Set.range
      (HomologicalComplex.homologyMap (SSet.linearDualCoefficientChange (ratScaled z)
        (TopCat.toSSet.obj Y)) n).hom) ≤
      (AddSubgroup.closure (⋃ z : ℂ, Set.range
        (hypercohomologyMap X (constantCoefficientSheafComplexIntMap X (ratScaled z))
          n))).comap Φ := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨_, ⟨z, rfl⟩, x, rfl⟩
    refine AddSubgroup.subset_closure (Set.mem_iUnion.mpr ⟨z, Eℚ.symm (Fℚ x), ?_⟩)
    apply Eℂ.injective
    have h1 : Eℂ (Φ ((HomologicalComplex.homologyMap (SSet.linearDualCoefficientChange
        (ratScaled z) (TopCat.toSSet.obj Y)) n).hom x)) = Fℂ ((HomologicalComplex.homologyMap
          (SSet.linearDualCoefficientChange (ratScaled z) (TopCat.toSSet.obj Y)) n).hom x) := by
      simp only [Φ, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
        AddEquiv.trans_apply]
      exact Eℂ.apply_symm_apply _
    rw [h1]
    change scalarCohomologyEquivOrdinarySingularCohomology X ℂ n _ = _
    rw [scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange]
    have h2 : scalarCohomologyEquivOrdinarySingularCohomology X ℚ n (Eℚ.symm (Fℚ x)) = Fℚ x :=
      Eℚ.apply_symm_apply _
    rw [h2]
    change Fℂ ((HomologicalComplex.homologyMap (SSet.linearDualCoefficientChange (ratScaled z)
      (TopCat.toSSet.obj Y)) n).hom (Fℚ.symm (Fℚ x))) = _
    rw [AddEquiv.symm_apply_apply]
  rw [← hγ]
  exact key hα

/-- The span for one `X`, with the topological inputs as hypotheses: Hausdorffness,
paracompact opens and finitely generated integral singular homology of `X(ℂ)` in degree `n`.
No projectivity is assumed; this is the hook for a later rung that drops it. -/
theorem span_range_fieldToDeRhamCohomology_rat_of_simplicialComplexSpan [IsIntegral X.left]
    [Smooth X.hom] [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) [Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ
      (TopCat.of (ComplexPoint X))).homology n)]
    (hS : SimplicialComplexSpan) :
    Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤ :=
  span_range_fieldToDeRhamCohomology_rat_of_mem_closure X n (mem_closure_ratScaled X n hS)

/-- `SimplicialComplexSpan` implies the rung: on a smooth projective integral `X`, `X(ℂ)` is
Hausdorff (`IsProjective.complexPoint_t2Space`), its opens are paracompact
(`openParacompactSpace`) and its integral singular homology is finitely generated
(`module_finite_singularHomology`). -/
theorem deRhamRationalSpan_of_simplicialComplexSpan (hS : SimplicialComplexSpan) :
    DeRhamRationalSpan := by
  intro X _ _ _ n
  let : ∀ U : Opens (ComplexPoint X), ParacompactSpace U := openParacompactSpace X
  let : Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ
      (TopCat.of (ComplexPoint X))).homology n) := module_finite_singularHomology X n
  exact span_range_fieldToDeRhamCohomology_rat_of_simplicialComplexSpan X n hS

end HodgeLadder
