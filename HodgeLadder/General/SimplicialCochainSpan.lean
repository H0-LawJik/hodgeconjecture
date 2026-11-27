module

public import LefschetzPort.AlgebraicTopology.SimplicialCochainCoefficientChange

/-!
# Complex simplicial cohomology spanned by rational classes

A general statement kept local (decision 0011), used by rung `de-rham-rational-span`. For a
simplicial set `Y` whose integral homology is finitely generated in degree `n`, every degree-`n`
cohomology class of the algebraic-dual complex cochain complex should be a finite sum of
rational classes pushed along the additive maps `q ↦ z q`, `z ∈ ℂ`. Change of coefficients along
an additive map is the port's `SSet.linearDualCoefficientChange` (generalized from ring maps to
additive maps in the port, see `docs/port-lefschetz.md`).

The statement is recorded as a `Prop` (rung `simplicial-complex-span`, checked). The proof,
`HodgeLadder.simplicialComplexSpan`, is in `HodgeLadder.General.SimplicialCochainSpanProof`: the
evaluation of a complex cocycle on integral cycles has values in a finite-dimensional ℚ-subspace
`W ⊆ ℂ`; a map `P : ℂ →+ ℂ` that is the identity on `W` and a sum of `ratScaled wᵢ ∘ λᵢ` with
additive `λᵢ : ℂ → ℚ` fixes the class, by Baer's criterion for the divisible group `ℂ`.

## Main definitions

* `HodgeLadder.ratScaled z : ℚ →+ ℂ`, the map `q ↦ z q`.
* `HodgeLadder.SimplicialComplexSpan`: the statement of rung `simplicial-complex-span`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace HodgeLadder

/-- Multiplication by `z` after the inclusion `ℚ → ℂ`: the additive map `q ↦ z q`. It is a ring
map only for `z = 1`. -/
def ratScaled (z : ℂ) : ℚ →+ ℂ :=
  (AddMonoidHom.mulLeft z).comp (algebraMap ℚ ℂ).toAddMonoidHom

/-- `ratScaled z q = z * q`. -/
@[simp] lemma ratScaled_apply (z : ℂ) (q : ℚ) : ratScaled z q = z * (q : ℂ) := rfl

/-- **Sub-rung `simplicial-complex-span`** (checked, `simplicialComplexSpan`). If the integral
homology of a simplicial set is finitely generated in degree `n`, every degree-`n` complex
cohomology class of its algebraic-dual cochain complex is a finite sum of classes pushed along
`ratScaled z`. -/
def SimplicialComplexSpan : Prop :=
  ∀ (Y : SSet.{0}) (n : ℕ) [Module.Finite ℤ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).homology n)]
    (α : (((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (Y.chainComplex (ModuleCat.of ℂ ℂ)).linearDualCochainComplex).homology n),
    α ∈ AddSubgroup.closure (⋃ z : ℂ, Set.range
      (HomologicalComplex.homologyMap (SSet.linearDualCoefficientChange (ratScaled z) Y) n).hom)

end HodgeLadder
