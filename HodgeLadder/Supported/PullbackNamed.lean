module

public import HodgeLadder.Supported.Pullback
public import HodgeLadder.Supported.SingularCochainPullback
public import HodgeLadder.General.ExtMapCocycle
public import HodgeLadder.Cup.SupportedFinal

/-!
# Supported pullback of cocycle-named classes

Rung `supported-pullback-named` (sub-rung R3 of `supported-pullback-transport`). A supported class
`α ∈ H^n_Z(X; ℚ) = Extⁿ(ℤ[X, X ∖ Z], ℚ_X)` is *named* by a Hom-complex cocycle
`z : PairCocycle X Z n` (degree `n`, from `ℤ[X, X ∖ Z]` in degree zero to the integer-indexed
singular cochain sheaves `𝒮_X`) when `α` followed by the resolution `iotaQ X : ℚ_X[0] ⟶ 𝒮_X`
is the derived class of `z`:
`α.hom ≫ (Q.map (iotaQ X))⟦n⟧' = ShiftedHom.map (equivHomShift.symm z) Q`.
This is the form in which `HodgeLadder.Cup.exists_supported_rep` produces a cocycle for every
supported class.

The supported pullback `g^*` of rung `supported-class-pullback` along `g : X' ⟶ X` over `Spec ℂ`
applies the exact functor `g⁻¹` (the port's `pullbackAb`), postcomposes with
`g⁻¹ ℚ_X ≅ ℚ_{X'}` and precomposes with the pair map `ℤ[X', X' ∖ Z'] ⟶ g⁻¹ ℤ[X, X ∖ Z]`.
`pullbackCocycle g Z Z' hZ z` is `z` mapped degreewise by `g⁻¹`, precomposed with the pair map
and Mathlib's comparison `g⁻¹ (A[0]) ≅ (g⁻¹ A)[0]`, and postcomposed with the cochain pullback
`singularPullbackInt g` of rung `singular-cochain-pullback`. Then `supportedPullback_named`:
if `z` names `α`, then `pullbackCocycle g Z Z' hZ z` names `g^* α`. Exact, with no sign and no
scalar; the only shift convention is the one of `Cocycle.equivHomShift`, on both sides.

Proof: `mapExactFunctor_hom_named` (rung `ext-map-cocycle`) for `g⁻¹`; the constants square
`iotaQ_square`, a reassociation of `iotaQ_comp_singularPullbackInt`; and two general facts on
named classes from `HodgeLadder.General.ExtMapCocycle`, `comp_mk₀_named` (postcomposition by
`mk₀ c` along a commuting square) and `mk₀_comp_named` (precomposition by `mk₀ s`).

Instances: the named local instances `pointPullbackAdditive`,
`pointPullbackPreservesFiniteLimits`, `pointPullbackPreservesFiniteColimits` of
`HodgeLadder.Supported.SingularCochainPullback`, and the derived-category instances
`finSiteHasDerivedCategory`, `finHasDerivedCategory` of `HodgeLadder.Cup.SupportedFinal`, so the
statement uses the same `HasDerivedCategory` terms as `exists_supported_rep`.
`set_option backward.isDefEq.respectTransparency false` is set on `iotaQ_square` only (the
`TopCat.Sheaf` and `AbSheaf` spellings of one category; the `rw` fails without it). Kernel time
at the pin (`lake env lean -Dprofiler=true`), about 163 s for the file on a lightly loaded
machine: 6.6 s for `pullbackCocycle`, 32 s for `iotaQ_square` (it unfolds `iotaQ`, as
`iotaQ_comp_singularPullbackInt` does), 96 s for `supportedPullback_named`, 28 s for
`exists_named_supportedPullback`; a run under load after the general lemmas moved gave 240 s
(10.5, 50, 134, 46 s).

## Main definitions

* `HodgeLadder.Supported.pullbackCocycle`

## Main results

* `HodgeLadder.Supported.supportedPullback_named`
* `HodgeLadder.Supported.exists_named_supportedPullback`: every `g^* α` with `X` integral and
  smooth (the hypotheses of `exists_supported_rep`) is named by some `pullbackCocycle`
* `HodgeLadder.Supported.iotaQ_square`
* General lemmas used here, in `HodgeLadder.General.ExtMapCocycle`:
  `HodgeLadder.ExtMapCocycle.mk₀_comp_named`, `comp_mk₀_named`, `precomp_postcomp_precomp`
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits TopologicalSpace Opposite Abelian CochainComplex HomComplex
  HodgeLadder.ExtMapCocycle

namespace HodgeLadder.Supported

section Variety

open AlgebraicGeometry ComplexPoint HodgeLadder.Cup

variable {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X)

attribute [local instance] pointPullbackAdditive pointPullbackPreservesFiniteLimits
  pointPullbackPreservesFiniteColimits finHasDerivedCategory finSiteHasDerivedCategory

/-- **The pullback of a pair cocycle** along `g : X' ⟶ X`: `z` mapped degreewise by `g⁻¹`
(`cocycleMap`), precomposed with the pair map `ℤ[X', X' ∖ Z'] ⟶ g⁻¹ ℤ[X, X ∖ Z]`
(`supportPairMap`) and Mathlib's `(g⁻¹ A)[0] ≅ g⁻¹ (A[0])`, then postcomposed with the cochain
pullback `singularPullbackInt g : g⁻¹ 𝒮_X ⟶ 𝒮_{X'}`. -/
def pullbackCocycle (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') {n : ℕ}
    (z : PairCocycle X Z n) : PairCocycle X' Z' n :=
  ((cocycleMap (TopCat.Sheaf.pullbackAb (pointMap g)) z).precomp
    ((CochainComplex.singleFunctor _ 0).map (supportPairMap (pointMap g) Z Z'
      (compl_le_of_preimage_subset g Z Z' hZ)) ≫
      ((TopCat.Sheaf.pullbackAb (pointMap g)).mapCochainComplexSingleFunctor 0).inv.app _)).postcomp
    (singularPullbackInt g)

set_option backward.isDefEq.respectTransparency false in
/-- The constants square for `comp_mk₀_named`: `g⁻¹ ℚ_X ≅ ℚ_{X'}` followed by `iotaQ X'` is the
pullback of `iotaQ X` followed by the cochain pullback, read through
`(g⁻¹ ℚ_X)[0] ≅ g⁻¹ (ℚ_X[0])`. A reassociation of `iotaQ_comp_singularPullbackInt`; exact. -/
theorem iotaQ_square :
    (CochainComplex.singleFunctor _ 0).map
      ((TopCat.Sheaf.pullbackConstantSheafIso (pointMap g)).hom.app (AddCommGrpCat.of ℚ)) ≫
        iotaQ X' =
      (((TopCat.Sheaf.pullbackAb (pointMap g)).mapCochainComplexSingleFunctor 0).inv.app _ ≫
        ((TopCat.Sheaf.pullbackAb (pointMap g)).mapHomologicalComplex _).map (iotaQ X)) ≫
          singularPullbackInt g := by
  rw [assoc, iotaQ_comp_singularPullbackInt, Iso.inv_hom_id_app_assoc]

/-- **Named classes pull back to named classes.** If the supported class `α ∈ H^n_Z(X; ℚ)`,
followed by the resolution `iotaQ X`, is the derived class of the pair cocycle `z`, then its
supported pullback `g^* α ∈ H^n_{Z'}(X'; ℚ)`, followed by `iotaQ X'`, is the derived class of
`pullbackCocycle g Z Z' hZ z`. Exact: no sign, no scalar. -/
theorem supportedPullback_named (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') {n : ℕ}
    (α : H_[Z]^n(X; ℚ)) (z : PairCocycle X Z n)
    (hα : α.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q) :
    (supportedPullback g Z Z' hZ n α).hom ≫ (DerivedCategory.Q.map (iotaQ X'))⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm (pullbackCocycle g Z Z' hZ z))
        DerivedCategory.Q := by
  have h1 := mapExactFunctor_hom_named (TopCat.Sheaf.pullbackAb (pointMap g)) α (iotaQ X) z hα
  have h2 := comp_mk₀_named _ _ _ h1
    ((TopCat.Sheaf.pullbackConstantSheafIso (pointMap g)).hom.app (AddCommGrpCat.of ℚ))
    (iotaQ X') (singularPullbackInt g) (iotaQ_square g)
  have h3 := mk₀_comp_named _ _ _ h2
    (supportPairMap (pointMap g) Z Z' (compl_le_of_preimage_subset g Z Z' hZ))
  refine h3.trans ?_
  congr 2
  exact precomp_postcomp_precomp _ _ _ _

/-- **Non-vacuity of the hypothesis of `supportedPullback_named`.** On `X` integral and smooth
with `X(ℂ)` Hausdorff and every open paracompact, every supported class `α` is named by a cocycle
(`exists_supported_rep`), so every supported pullback `g^* α` is named by a pulled-back
cocycle. -/
theorem exists_named_supportedPullback [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') {n : ℕ}
    (α : H_[Z]^n(X; ℚ)) :
    ∃ z : PairCocycle X Z n,
      (supportedPullback g Z Z' hZ n α).hom ≫ (DerivedCategory.Q.map (iotaQ X'))⟦(n : ℤ)⟧' =
        ShiftedHom.map (Cocycle.equivHomShift.symm (pullbackCocycle g Z Z' hZ z))
          DerivedCategory.Q := by
  obtain ⟨x, hx, -, h⟩ := exists_supported_rep X Z α
  exact ⟨_, supportedPullback_named g Z Z' hZ α _ h⟩

end Variety

end HodgeLadder.Supported
