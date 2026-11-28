module

public import HodgeLadder.Cup.SupportedPair
public import HodgeLadder.Supported.SingularCochainPullback

/-!
# A named supported class on the pair `(X, X ∖ Z)`

Rung `supported-pair-named` (sub-rung R5 of `supported-pullback-transport`). Let `y` be a
relative singular cocycle of degree `p` on the pair `(X(ℂ), X(ℂ) ∖ Z)`, in abelian groups
(`RelCochain X Z p`), and let `β ∈ H_[Z]^p(X; ℚ)` be named by the Hom-complex cocycle
`supCocycle (rawMap y)` out of the pair sheaf `ℤ[X, X ∖ Z]`, after the resolution
`iotaQ X : ℚ_X[0] ⟶ 𝒮_X`. Then `supportedEquivPair X Z p β` is the relative singular class of `y`
on `(X, X ∖ Z)`: the class of `y` on the pair of opens `(⊤, ⊤ ⊓ (X ∖ Z))`, read in `ℚ`-modules by
upstream's `relativeDualCochainCohomologyEquiv` and moved to `(X, X ∖ Z)` along `topPairIso`.

Exact, with no sign and no scalar. The proof is the second half of `exists_supported_rep`:
`relHSupportedOfFlasque_mk` computes upstream's flasque model on the named class, and
`supported_singular_class` (checked, no sign) passes through upstream's cone identifications.
`shortExactHomologyIsoCone` enters twice inside `supported_singular_class`, for the
supported-sections sequence and inside upstream's `relativeDualCochainHomologyIsoCone`; its
naturality along `rawMap` and along `forget₂` matches the two, so any sign it carries cancels,
and the statement here contains no cone. No other step can introduce a factor.

`exists_named` checks the hypothesis on `β` is satisfiable for every relative cocycle `y`;
`exists_supportedEquivPair_eq` combines the two. `exists_named_ne_zero` gives a nonzero instance
for every nonzero supported class.

## Main results

* `HodgeLadder.Supported.supportedEquivPair_of_named`
* `HodgeLadder.Supported.exists_named`, `HodgeLadder.Supported.exists_supportedEquivPair_eq`,
  `HodgeLadder.Supported.exists_named_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology.Singular TopCat.Sheaf
  CochainComplex.HomComplex

namespace HodgeLadder.Supported

open AlgebraicGeometry ComplexPoint HodgeLadder.Cup

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (Z : Closeds (ComplexPoint X))

attribute [local instance] HodgeLadder.Cup.finHasDerivedCategory
  HodgeLadder.Cup.finSiteHasDerivedCategory

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **A named supported class has the singular class of its cocycle.** If `β` is named by
`supCocycle (rawMap y)` through `iotaQ X`, then `supportedEquivPair X Z p β` is the relative
singular class of `y` on `(X, X ∖ Z)`. Exact: no sign, no scalar. -/
theorem supportedEquivPair_of_named {p : ℕ} (β : H_[Z]^p(X; ℚ)) (y : RelCochain X Z p)
    (hy : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) y = 0)
    (hβ : β.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (supCocycle X Z ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p y)
          (map_d_eq_zero _ y hy))) DerivedCategory.Q) :
    supportedEquivPair X Z p β =
      relativeCohomologyMap ℚ p (topPairIso (TopCat.of (ComplexPoint X)) Z.compl).hom
        (relativeDualCochainCohomologyEquiv ℚ
          (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl)) p
          ((ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
            (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl))).X₁.sc p)
            (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
            (cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) y hy))) := by
  set s₀ := (rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p y
  set z := supCocycle X Z s₀ (map_d_eq_zero _ y hy)
  have hF := relHSupportedOfFlasque_mk (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
    (top_inf_eq _) 𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X)
    (singularCochainSheafComplexInt_isFlasque X) p β z hβ
  set e := homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
    (top_inf_eq _) (singularCochainSheafComplexInt X ℚ)
  have hcls : HomologicalComplex.homologyMap e.hom p
      ((homologyAddEquiv _ _ p).symm (CohomologyClass.mk z)) =
      cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁ (p : ℤ) ((p : ℤ) + 1) (by simp) s₀
        (map_d_eq_zero _ y hy) := by
    rw [← homologyAddEquiv_cls z, AddEquiv.symm_apply_apply, homologyMap_cls]
    apply cls_eq
    have h1 := congrArg (fun φ => HomologicalComplex.Hom.f φ (p : ℤ)) e.inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h1
    exact ConcreteCategory.congr_hom h1 s₀
  have hM : flasqueModel X Z p β = HomologicalComplex.homologyMap
      (rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁ p
      (cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) y hy) := by
    rw [homologyMap_cls]
    exact hF.trans hcls
  change (pairCohIso (TopCat.of (ComplexPoint X)) Z.compl p).hom
      (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤
        p (flasqueModel X Z p β)) = _
  rw [hM, supported_singular_class, pairCohIso_hom_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **Every relative cocycle names a supported class**: the hypothesis of
`supportedEquivPair_of_named` holds for some `β`, whatever the relative cocycle `y`. -/
theorem exists_named {p : ℕ} (y : RelCochain X Z p)
    (hy : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) y = 0) :
    ∃ β : H_[Z]^p(X; ℚ), β.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (supCocycle X Z ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p y)
          (map_d_eq_zero _ y hy))) DerivedCategory.Q := by
  refine ⟨Abelian.Ext.homAddEquiv.symm
    (ShiftedHom.map (Cocycle.equivHomShift.symm (supCocycle X Z
      ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p y) (map_d_eq_zero _ y hy)))
      DerivedCategory.Q ≫ inv ((DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧')), ?_⟩
  rw [← Abelian.Ext.homAddEquiv_apply, AddEquiv.apply_symm_apply, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

/-- The class of every relative cocycle on `(X, X ∖ Z)` is `supportedEquivPair` of a supported
class named by it. -/
theorem exists_supportedEquivPair_eq {p : ℕ} (y : RelCochain X Z p)
    (hy : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) y = 0) :
    ∃ β : H_[Z]^p(X; ℚ), supportedEquivPair X Z p β =
      relativeCohomologyMap ℚ p (topPairIso (TopCat.of (ComplexPoint X)) Z.compl).hom
        (relativeDualCochainCohomologyEquiv ℚ
          (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl)) p
          ((ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
            (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl))).X₁.sc p)
            (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
            (cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) y hy))) :=
  (exists_named X Z y hy).imp fun β hβ => supportedEquivPair_of_named X Z β y hy hβ

/-- **A nonzero instance**: every nonzero supported class is named by a relative cocycle whose
relative class on `(X, X ∖ Z)` is nonzero, so `supportedEquivPair_of_named` holds with both sides
nonzero. With `HodgeLadder.Tests.supportedEquivPair_supportedClass_ne_zero` this applies to
upstream's supported cycle class of every scheme point of a smooth projective `X`. -/
theorem exists_named_ne_zero {p : ℕ} (β : H_[Z]^p(X; ℚ)) (h0 : β ≠ 0) :
    ∃ (y : RelCochain X Z p)
      (hy : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) y = 0),
      β.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (supCocycle X Z ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p y)
            (map_d_eq_zero _ y hy))) DerivedCategory.Q ∧
      relativeCohomologyMap ℚ p (topPairIso (TopCat.of (ComplexPoint X)) Z.compl).hom
        (relativeDualCochainCohomologyEquiv ℚ
          (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl)) p
          ((ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
            (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl))).X₁.sc p)
            (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
            (cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) y hy))) ≠ 0 := by
  obtain ⟨y, hy, -, hβ⟩ := exists_supported_rep X Z β
  refine ⟨y, hy, hβ, ?_⟩
  rw [← supportedEquivPair_of_named X Z β y hy hβ]
  intro h
  exact h0 ((supportedEquivPair X Z p).injective (h.trans (map_zero _).symm))

end HodgeLadder.Supported
