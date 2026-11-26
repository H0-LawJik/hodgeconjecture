module

public import HodgeLadder.Cup.SupportedAgreement
public import HodgeLadder.Cup.SupportedOpen
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf

/-!
# The flasque model on an open against upstream's injective model and transport

Rung `supported-model-agreement-open` (front `cup`, supported comparison on a general open).
`supported-model-agreement` with `⊤` replaced by an open `V`. Upstream identifies
`H^n(V, V ⊓ (X ∖ Z); ℚ)` (its `relH` on the pair) with the cohomology of supported sections over
`V` both of its ambient injective resolution (`relHAddEquivSupportedSectionsHomology`, here
`injectiveModelOpen`) and of the singular cochain sheaves (the flasque model,
`flasqueModelOpen`). Through upstream's comparison `complexSupportedSingularInjectiveHomologyIso`
at `V` the two agree (`flasqueModelOpen_agreement`, from `relHSupported_eq_flasque`, which is
stated for any `(U, V, W, hW)`). Hence upstream's cycle-class transport
`complexSupportInjectiveSectionCohomologyEquiv X Z V`, applied after the injective model, is
`Φ_V` followed by upstream's pair isomorphism `openIntersectionPairIsoSupportComplement` from
`(V, V ⊓ (X ∖ Z))` to `(V, V ∖ Z)`, which is the identity on points. No sign enters.

## Main definitions

* `HodgeLadder.Cup.injectiveModelOpen`

## Main results

* `HodgeLadder.Cup.flasqueModelOpen_agreement`, `HodgeLadder.Cup.transport_eq_flasqueModelOpen`,
  `HodgeLadder.Cup.transport_eq_comparisonOpen`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TopCat.Sheaf CochainComplex.HomComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

section Variety

open AlgebraicGeometry ComplexPoint AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (Z : Closeds (ComplexPoint X))
  (V : Opens (ComplexPoint X))

/-- Upstream's K-injective supported-sections model of `H^n(V, V ⊓ (X ∖ Z); ℚ)`, for upstream's
ambient injective resolution of `ℚ`, the same construction as upstream's
`rationalSupportAddEquivSupportedInjectiveHomology` with `⊤` replaced by `V` and the second open
spelled `V ⊓ (X ∖ Z)`. -/
abbrev injectiveModelOpen (n : ℕ) :=
  @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology (TopCat.of (ComplexPoint X)) Z.compl V
    (V ⊓ Z.compl) rfl inferInstance _ (ambientRationalInjectiveComplex X)
    (ambientRationalInjectiveComplex_isKInjective X)
    (ambientRationalInjectiveSingleAugmentation X)
    (ambientRationalInjectiveSingleAugmentation_quasiIso X) n

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The flasque model on `V` agrees with upstream's injective model on `V`** through upstream's
comparison of supported singular and supported injective sections over `V`. -/
theorem flasqueModelOpen_agreement (n : ℕ)
    (α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) n (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))) :
    (complexSupportedSingularInjectiveHomologyIso X Z.compl V (n : ℤ)).hom
        (flasqueModelOpen X Z V n α) = injectiveModelOpen X Z V n α := by
  have := rationalToSingularCochainComplexInt_mono X
  exact (relHSupported_eq_flasque (TopCat.of (ComplexPoint X)) Z.compl V (V ⊓ Z.compl) rfl
    𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X)
    (singularCochainSheafComplexInt_isFlasque X) (ambientRationalInjectiveComplex X)
    (ambientRationalInjectiveSingleAugmentation X)
    (singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X)) (exists_contractibleOpen_le X))
    (iotaQ_comp_singularToConstantInjective X) n α).symm

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Upstream's cycle-class transport on `V` factors through the flasque model on `V`**:
`complexSupportInjectiveSectionCohomologyEquiv X Z V` after the injective model is upstream's
`supportedRationalSingularSectionCohomologyEquivSupportComplement` at `V` after the flasque
model. -/
theorem transport_eq_flasqueModelOpen (n : ℕ)
    (α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) n (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))) :
    complexSupportInjectiveSectionCohomologyEquiv X Z V n (injectiveModelOpen X Z V n α) =
      supportedRationalSingularSectionCohomologyEquivSupportComplement (TopCat.of (ComplexPoint X))
        Z Z.isClosed V n (flasqueModelOpen X Z V n α) := by
  rw [← flasqueModelOpen_agreement X Z V n α]
  unfold complexSupportInjectiveSectionCohomologyEquiv
  rw [AddEquiv.trans_apply]
  congr 1
  exact Iso.hom_inv_id_apply (complexSupportedSingularInjectiveHomologyIso X Z.compl V (n : ℤ)) _

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **`Φ_V` is upstream's cycle-class transport on `V`**, up to upstream's pair isomorphism:
the transport after the injective model is `Φ_V` followed by `relativeCohomologyMap` along the
inverse of `openIntersectionPairIsoSupportComplement` (identity on points). -/
theorem transport_eq_comparisonOpen (n : ℕ)
    (α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) n (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))) :
    complexSupportInjectiveSectionCohomologyEquiv X Z V n (injectiveModelOpen X Z V n α) =
      relativeCohomologyMap ℚ n
        (openIntersectionPairIsoSupportComplement (TopCat.of (ComplexPoint X)) Z Z.isClosed V).inv
        (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
          Z.compl V n (flasqueModelOpen X Z V n α)) :=
  transport_eq_flasqueModelOpen X Z V n α

end Variety

end HodgeLadder.Cup
