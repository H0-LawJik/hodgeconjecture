module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularSectionCohomology

/-!
# Raw relative cochains into supported sections

Rung `supported-raw-map` (front `cup`, supported comparison). Let `U`, `V` be opens of `X` and
`W = V ⊓ U`. The relative dual-cochain sequence `C(V, W) → C(V) → C(W)` of the pair `(V, W)`,
forgotten to abelian groups, maps to upstream's supported-sections sequence
`Γ_{X ∖ U}(V, S) → S(V) → S(V ⊓ U)` of the singular cochain sheaves `S`. The middle and last
components are the sheafification units of raw cochains (`openRawToSingularCochainSheafComplex`);
the first is the induced map of kernels.

## Main definitions

* `HodgeLadder.Cup.relSeq`, `HodgeLadder.Cup.supSeq`, `HodgeLadder.Cup.rawMapMid`,
  `HodgeLadder.Cup.rawMapEnd`, `HodgeLadder.Cup.rawMapStart'`, `HodgeLadder.Cup.rawMap`

## Main results

* `HodgeLadder.Cup.rawMap_comm`, `HodgeLadder.Cup.supSeq_shortExact`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular TopCat.Sheaf

namespace HodgeLadder.Cup

variable (X : TopCat.{0}) (U V : Opens X)

/-- The relative dual-cochain sequence of `(V, V ⊓ U)`, in abelian groups. -/
abbrev relSeq : ShortComplex (CochainComplex AddCommGrpCat.{0} ℤ) :=
  ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).mapShortComplex.obj
    (relativeDualCochainShortComplexInt ℚ (openInclusionPair X (Opens.infLELeft V U)))

/-- Upstream's supported-sections sequence of the singular cochain sheaves over `V`. -/
abbrev supSeq : ShortComplex (CochainComplex AddCommGrpCat.{0} ℤ) :=
  supportRestrictionSectionsComplexShortComplex X U V (rationalSingularCochainComplex X)

/-- The middle component: raw cochains on `V` to sections of `S` over `V`. -/
def rawMapMid : (relSeq X U V).X₂ ⟶ (supSeq X U V).X₂ :=
  (openRawSingularCochainComplexIntIsoDual ℚ X V).inv ≫
    HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X V)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V)
      (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).inv

/-- The last component: raw cochains on `V ⊓ U` to sections of `S` over `V ⊓ U`, read in
`Γ(V, j_*(S|_U))`. -/
def rawMapEnd : (relSeq X U V).X₃ ⟶ (supSeq X U V).X₃ :=
  (openRawSingularCochainComplexIntIsoDual ℚ X (V ⊓ U)).inv ≫
    HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X (V ⊓ U))
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X (V ⊓ U))
      (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).inv ≫
    (supportRestrictionSectionsIntersectionIso X U V (rationalSingularCochainComplex X)).inv

set_option backward.isDefEq.respectTransparency false in
/-- **The sheafification units commute with restriction.** -/
theorem rawMap_comm : (relSeq X U V).g ≫ rawMapEnd X U V = rawMapMid X U V ≫ (supSeq X U V).g := by
  rw [← cancel_mono (supportRestrictionSectionsIntersectionIso X U V
    (rationalSingularCochainComplex X)).hom]
  simp only [rawMapEnd, rawMapMid, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [supportRestrictionSectionsIntersectionIso_restriction]
  have h1 := sectionComplexRestriction_extend X (singularCochainSheafComplex ℚ X) (V.infLELeft U)
  have h1' : (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V)
      (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).inv ≫
      sectionComplexRestriction X (ComplexShape.up ℤ) (rationalSingularCochainComplex X)
        (V.infLELeft U) =
      HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ)
        (singularCochainSheafComplex ℚ X) (V.infLELeft U)) ComplexShape.embeddingUpNat ≫
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X (V ⊓ U))
        (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact h1
  have h2 := openSingularSheafRestrictionInt_naturality ℚ X (V.infLELeft U)
  have h3 : (openRawSingularCochainComplexIntIsoDual ℚ X V).inv ≫
      HomologicalComplex.extendMap (openRawSingularRestriction ℚ X (V.infLELeft U))
        ComplexShape.embeddingUpNat =
      (relSeq X U V).g ≫ (openRawSingularCochainComplexIntIsoDual ℚ X (V ⊓ U)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact openRawSingularRestrictionInt_transport ℚ X (V.infLELeft U)
  erw [h1']
  rw [← Category.assoc (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X V)
    ComplexShape.embeddingUpNat)]
  erw [← h2]
  simp only [Category.assoc]
  rw [← Category.assoc (openRawSingularCochainComplexIntIsoDual ℚ X V).inv, h3, Category.assoc]

section Paracompact

variable [T2Space X] [∀ W : Opens X, ParacompactSpace W]

/-- Upstream's supported-sections sequence is short exact (the singular cochain sheaves are
flasque). -/
lemma supSeq_shortExact : (supSeq X U V).ShortExact :=
  supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V
    (rationalSingularCochainComplex X) (fun _ => inferInstance)

/-- The first component and its defining property: relative cochains to supported sections, the
map induced on kernels. -/
def rawMapStart' : { φ : (relSeq X U V).X₁ ⟶ (supSeq X U V).X₁ //
    φ ≫ (supSeq X U V).f = (relSeq X U V).f ≫ rawMapMid X U V } :=
  KernelFork.IsLimit.lift' (supSeq_shortExact X U V).fIsKernel ((relSeq X U V).f ≫ rawMapMid X U V)
    (by rw [Category.assoc, ← rawMap_comm, ← Category.assoc, (relSeq X U V).zero,
      Limits.zero_comp])

/-- **The map `Θ` of short complexes** from the relative dual-cochain sequence of `(V, V ⊓ U)` to
upstream's supported-sections sequence. -/
def rawMap : relSeq X U V ⟶ supSeq X U V where
  τ₁ := (rawMapStart' X U V).1
  τ₂ := rawMapMid X U V
  τ₃ := rawMapEnd X U V
  comm₁₂ := (rawMapStart' X U V).2
  comm₂₃ := (rawMap_comm X U V).symm

end Paracompact

end HodgeLadder.Cup
