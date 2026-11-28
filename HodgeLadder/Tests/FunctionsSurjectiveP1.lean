module

public import HodgeLadder.Hodge.FunctionsSurjectiveZero
public import HodgeLadder.Tests.CompactHolomorphicP1

/-!
# `H_dR^0 → ℍ⁰(𝒪[0])` is onto on `ℙ¹`, and its target is nonzero

Tests of rung `de-rham-functions-surjective-zero`, whose general results are in
`HodgeLadder.Hodge.FunctionsSurjectiveZero`. `ℙ¹(ℂ)` is compact (upstream's
`IsProjective.complexPoint_compactSpace`), so `H_dR^0(ℙ¹) → ℍ⁰(ℙ¹; 𝒪[0])` is onto and
`ℍ¹(ℙ¹; F¹Ω^•) → H_dR^1(ℙ¹)` is injective. `ℙ¹(ℂ)` is nonempty (upstream's
`ComplexPoint.connectedSpace`), so `ℍ⁰(ℙ¹; 𝒪[0])` has two distinct classes and the surjectivity
holds onto a nonzero group, unlike the point test of `filtered-one-injective`, where the
projection is an isomorphism of complexes. Compactness is load-bearing for the general result:
`projectiveLine_exists_nonconstant_section` gives a nonconstant holomorphic function on a
non-compact open of `ℙ¹`.

## Main results

* `HodgeLadder.Tests.complexPoint_projectiveLine_nonempty`
* `HodgeLadder.Tests.deRhamToHolomorphicFunctionCohomology_projectiveLine_surjective`
* `HodgeLadder.Tests.filteredToDeRhamCohomology_projectiveLine_injective`
* `HodgeLadder.Tests.nontrivial_holomorphicFunctionCohomology_projectiveLine`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Tests

/-- `ℙ¹(ℂ)` is nonempty, from upstream's `ComplexPoint.connectedSpace`. -/
instance complexPoint_projectiveLine_nonempty : Nonempty (ComplexPoint projectiveLine) := by
  have : QuasiSeparatedSpace projectiveLine.left :=
    quasiSeparatedSpace_of_quasiSeparated projectiveLine.hom
  have : ConnectedSpace (ComplexPoint projectiveLine) := ComplexPoint.connectedSpace _
  infer_instance

/-- `H_dR^0(ℙ¹) → ℍ⁰(ℙ¹; 𝒪[0])` is onto. -/
theorem deRhamToHolomorphicFunctionCohomology_projectiveLine_surjective :
    Function.Surjective (deRhamToHolomorphicFunctionCohomology projectiveLine 0) :=
  deRhamToHolomorphicFunctionCohomology_zero_surjective projectiveLine

/-- `ℍ¹(ℙ¹; F¹Ω^•) → H_dR^1(ℙ¹)` is injective. -/
theorem filteredToDeRhamCohomology_projectiveLine_injective :
    Function.Injective (filteredToDeRhamCohomology projectiveLine 1 1) :=
  filteredToDeRhamCohomology_one_one_injective_of_compact projectiveLine

/-- `ℍ⁰(ℙ¹; 𝒪[0])` has two distinct classes. -/
theorem nontrivial_holomorphicFunctionCohomology_projectiveLine :
    Nontrivial (Hypercohomology projectiveLine
      (holomorphicFunctionComplexInt projectiveLine (TopologicalSpace.dim projectiveLine.left)) 0) :=
  nontrivial_holomorphicFunctionCohomology_zero projectiveLine

end HodgeLadder.Tests
