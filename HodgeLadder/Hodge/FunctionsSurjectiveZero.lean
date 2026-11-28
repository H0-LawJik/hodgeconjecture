module

public import HodgeLadder.Hodge.CompactHolomorphic
public import HodgeLadder.Hodge.FilteredOneInjective
public import HodgeLadder.General.LocallyConstantSheaf
public import LefschetzPort.AlgebraicGeometry.HolomorphicHodgeProjection
public import LefschetzPort.AlgebraicGeometry.AnalyticSheafCohomologyExt
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections

/-!
# `H_dR^0(X) → ℍ⁰(X; 𝒪[0])` is onto when `X(ℂ)` is compact

Sub-rung S2a of `elliptic-curve-holomorphic-form` (rung `de-rham-functions-surjective-zero`).
Let `X` be a smooth integral complex scheme with `X(ℂ)` compact. The port's projection
`deRhamToHolomorphicFunctionCohomology X 0 : H_dR^0(X) → ℍ⁰(X; 𝒪[0])` is surjective.

The proof has three steps.

1. **`ℍ⁰` of a sheaf in degree zero is its global sections.** For a sheaf `F` of abelian groups on
   `X(ℂ)`, `hypercohomologyZeroEquivGlobalSections X F : ℍ⁰(X; F[0]) ≃ Γ(X(ℂ), F)` is the port's
   `ℍⁿ(F[0]) ≃ Extⁿ(ℤ, F)` (`analyticSheafCohomologyEquivExt`), then Mathlib's
   `Ext⁰ ≃ Hom` (`Abelian.Ext.homEquiv₀`), then upstream's evaluation at the constant section `1`
   (`TopCat.Sheaf.integerConstantHomAddEquivGlobalSections`). It is natural in `F`
   (`hypercohomologyZeroEquivGlobalSections_naturality`), so a sheaf map onto on global sections
   gives a map onto on `ℍ⁰`.
2. **Constants are onto global holomorphic functions.** The port's map `ℂ_X → 𝒪`
   (`complexConstantsToHolomorphicSheaf`) factors through the ladder's sheaf of locally constant
   functions (`complexConstantsToHolomorphicSheaf_eq`), and a global holomorphic function on a
   compact `X(ℂ)` is locally constant (`holomorphicTopToLocallyConstant`, sub-rung S1), so the map
   is onto on `⊤`. This is optional change O1 of the S1 red team.
3. **The square.** `ℂ[0] → Ω^• → 𝒪[0]` is the map `ℂ_X → 𝒪` in degree zero
   (`constantsToHolomorphicDeRhamComplexInt_comp_toFunctionsComplexInt`, from the port's
   `constantsToHolomorphicDeRhamComplex_comp_toFunctions`). A preimage of `γ ∈ ℍ⁰(𝒪[0])` is the
   image in `H_dR^0` of a class of `ℍ⁰(ℂ[0])` found in step 1.

With `filtered-one-injective` this gives `filteredToDeRhamCohomology X 1 1` injective on every
compact `X(ℂ)`. No sign or scalar enters: every map is a composite of the upstream and port
maps, and the identification of step 1 is used only through its naturality.

## Main definitions

* `HodgeLadder.hypercohomologyZeroEquivGlobalSections X F`
* `HodgeLadder.locallyConstantToHolomorphicSheaf X d`

## Main results

* `HodgeLadder.hypercohomologyZeroEquivGlobalSections_naturality`
* `HodgeLadder.hypercohomologyMap_analyticSheafComplexIntMap_zero_surjective`
* `HodgeLadder.complexConstantsToHolomorphicSheaf_eq`,
  `HodgeLadder.complexConstantsToHolomorphicSheaf_app_top_surjective`
* `HodgeLadder.constantsToHolomorphicDeRhamComplexInt_comp_toFunctionsComplexInt`
* `HodgeLadder.deRhamToHolomorphicFunctionCohomology_zero_surjective`
* `HodgeLadder.filteredToDeRhamCohomology_one_one_injective_of_compact`
* `HodgeLadder.nontrivial_holomorphicAdditiveSheaf_top`,
  `HodgeLadder.nontrivial_holomorphicFunctionCohomology_zero`: the target `ℍ⁰(X; 𝒪[0])` is
  nonzero when `X(ℂ)` is nonempty
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry ComplexPoint Opposite
open scoped ContDiff Manifold

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ))

/-- **`ℍ⁰` of a sheaf in degree zero is its global sections.** For a sheaf `F` of abelian groups
on `X(ℂ)`, `ℍ⁰(X; F[0]) ≃ Γ(X(ℂ), F)`: the port's `ℍ⁰(F[0]) ≃ Ext⁰(ℤ, F)`, Mathlib's
`Ext⁰ ≃ Hom`, and upstream's evaluation of `ℤ_X → F` at the constant section `1`. -/
def hypercohomologyZeroEquivGlobalSections (F : AnalyticAdditiveSheaf X) :
    Hypercohomology X (analyticSheafComplexInt X F) 0 ≃ F.presheaf.obj (op ⊤) :=
  letI : AddCommGroup ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).obj
      (AddCommGrpCat.of ℤ) ⟶ F) :=
    (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat ↧(ComplexPoint X))).homGroup _ _
  (analyticSheafCohomologyEquivExt X F 0).trans <| Abelian.Ext.homEquiv₀.trans
    (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F).toEquiv

/-- The equivalence `ℍ⁰(X; F[0]) ≃ Γ(X(ℂ), F)` unfolded: evaluation at `1` of the sheaf map
`ℤ_X → F` that the class gives in `Ext⁰`. -/
theorem hypercohomologyZeroEquivGlobalSections_apply (F : AnalyticAdditiveSheaf X)
    (α : Hypercohomology X (analyticSheafComplexInt X F) 0) :
    hypercohomologyZeroEquivGlobalSections X F α =
      TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F
        (Abelian.Ext.homEquiv₀.{0} (C := AnalyticAdditiveSheaf X)
          (analyticSheafCohomologyEquivExt X F 0 α)) := rfl

/-- In degree zero, the port's `ℍ⁰(F[0]) ≃ Ext⁰(ℤ, F)` sends the image of `α` under `c : F ⟶ G`
to `mk₀ (φ ≫ c)`, where `φ : ℤ_X ⟶ F` is the sheaf map of `α`. -/
theorem analyticSheafCohomologyEquivExt_zero_naturality {F G : AnalyticAdditiveSheaf X}
    (c : F ⟶ G) (α : Hypercohomology X (analyticSheafComplexInt X F) 0) :
    analyticSheafCohomologyEquivExt X G 0
        (hypercohomologyMap X (analyticSheafComplexIntMap X c) 0 α) =
      Abelian.Ext.mk₀.{0} (C := AnalyticAdditiveSheaf X)
        (Abelian.Ext.homEquiv₀.{0} (C := AnalyticAdditiveSheaf X)
          (analyticSheafCohomologyEquivExt X F 0 α) ≫ c) := by
  refine (analyticSheafCohomologyEquivExt_naturality X c 0 α).trans ?_
  conv_lhs => rw [← Abelian.Ext.mk₀_homEquiv₀_apply (analyticSheafCohomologyEquivExt X F 0 α)]
  exact Abelian.Ext.mk₀_comp_mk₀ _ _

/-- **Naturality.** Under `ℍ⁰(X; F[0]) ≃ Γ(X(ℂ), F)`, the map on `ℍ⁰` induced by a sheaf map
`c : F ⟶ G` is `c` on global sections. -/
theorem hypercohomologyZeroEquivGlobalSections_naturality {F G : AnalyticAdditiveSheaf X}
    (c : F ⟶ G) (α : Hypercohomology X (analyticSheafComplexInt X F) 0) :
    hypercohomologyZeroEquivGlobalSections X G
        (hypercohomologyMap X (analyticSheafComplexIntMap X c) 0 α) =
      c.hom.app (op ⊤) (hypercohomologyZeroEquivGlobalSections X F α) := by
  rw [hypercohomologyZeroEquivGlobalSections_apply, hypercohomologyZeroEquivGlobalSections_apply,
    analyticSheafCohomologyEquivExt_zero_naturality, ← Abelian.Ext.homEquiv₀_symm_apply,
    Equiv.apply_symm_apply]
  rfl

/-- A sheaf map `c : F ⟶ G` that is onto on global sections induces a map onto
`ℍ⁰(X; F[0]) → ℍ⁰(X; G[0])`. -/
theorem hypercohomologyMap_analyticSheafComplexIntMap_zero_surjective
    {F G : AnalyticAdditiveSheaf X} (c : F ⟶ G)
    (hc : Function.Surjective (c.hom.app (op ⊤))) :
    Function.Surjective (hypercohomologyMap X (analyticSheafComplexIntMap X c) 0) := by
  intro γ
  obtain ⟨t, ht⟩ := hc (hypercohomologyZeroEquivGlobalSections X G γ)
  refine ⟨(hypercohomologyZeroEquivGlobalSections X F).symm t, ?_⟩
  apply (hypercohomologyZeroEquivGlobalSections X G).injective
  rw [hypercohomologyZeroEquivGlobalSections_naturality, Equiv.apply_symm_apply, ht]

/-- **The square.** The composite `ℂ[0] → Ω^• → 𝒪[0]` of the upstream inclusion of constants
and the port's projection to functions is the map `ℂ_X → 𝒪` in degree zero, followed by the
identification of the extended complex `𝒪[0]` with the single complex. -/
theorem constantsToHolomorphicDeRhamComplexInt_comp_toFunctionsComplexInt
    [IsIntegral X.left] [Smooth X.hom] :
    constantsToHolomorphicDeRhamComplexInt X ≫ holomorphicDeRhamToFunctionsComplexInt X =
      analyticSheafComplexIntMap X (complexConstantsToHolomorphicSheaf X (dim X.left)) ≫
        (analyticSheafComplexIntIsoSingle X (holomorphicAdditiveSheaf X (dim X.left))).hom := by
  have h := congrArg (fun f ↦ HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)
    (constantsToHolomorphicDeRhamComplex_comp_toFunctions X (dim X.left))
  simp only [HomologicalComplex.extendMap_comp] at h
  exact (reassoc_of% h) (analyticSheafComplexIntIsoSingle X _).hom


variable (d : ℕ)

/-- Locally constant functions are holomorphic: the sheaf map from the ladder's sheaf of locally
constant `ℂ`-valued functions on `X(ℂ)` to upstream's holomorphic functions, the identity on
underlying functions. -/
def locallyConstantToHolomorphicSheaf [SmoothOfRelativeDimension d X.hom] :
    HodgeLadder.locallyConstantSheaf (TopCat.of (ComplexPoint X)) ℂ ⟶
      holomorphicAdditiveSheaf X d :=
  ⟨{ app U := AddCommGrpCat.ofHom
      { toFun f := show C^ω⟮𝓘(ℂ, Fin d → ℂ), U.unop; ℂ⟯ from
          ⟨(f : LocallyConstant U.unop ℂ), fun x ↦
            (contMDiffAt_const (c := (f : LocallyConstant U.unop ℂ) x)).congr_of_eventuallyEq
              ((f : LocallyConstant U.unop ℂ).isLocallyConstant.eventually_eq x)⟩
        map_zero' := rfl
        map_add' _ _ := rfl }
     naturality _ _ _ := rfl }⟩

set_option backward.isDefEq.respectTransparency false in
/-- The port's map `ℂ_X → 𝒪` is the ladder's isomorphism of the constant sheaf with locally
constant functions, followed by `locallyConstantToHolomorphicSheaf`. -/
theorem complexConstantsToHolomorphicSheaf_eq [SmoothOfRelativeDimension d X.hom] :
    complexConstantsToHolomorphicSheaf X d =
      (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).hom ≫
        locallyConstantToHolomorphicSheaf X d := by
  apply Sheaf.hom_ext
  apply (sheafifyLift_unique _ _ _ _ _).symm
  rw [HodgeLadder.constantSheafIsoLocallyConstantSheaf_hom]
  change toSheafify _ _ ≫ (HodgeLadder.constantSheafToLocallyConstantSheaf _ ℂ).hom ≫
    (locallyConstantToHolomorphicSheaf X d).hom = _
  erw [← Category.assoc, HodgeLadder.toSheafify_constantSheafToLocallyConstantSheaf_hom]
  rfl

/-- On a compact `X(ℂ)`, every global holomorphic function is the image of a global section of
`ℂ_X`: it is locally constant (`holomorphicTopToLocallyConstant`, sub-rung S1). -/
theorem complexConstantsToHolomorphicSheaf_app_top_surjective [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)] :
    Function.Surjective ((complexConstantsToHolomorphicSheaf X d).hom.app (op ⊤)) := by
  intro s
  refine ⟨(HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).inv.hom.app (op ⊤)
    (HodgeLadder.holomorphicTopToLocallyConstant X d s), ?_⟩
  rw [complexConstantsToHolomorphicSheaf_eq]
  change ((HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).inv ≫
    (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).hom ≫
      locallyConstantToHolomorphicSheaf X d).hom.app (op ⊤) _ = s
  rw [show (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).inv ≫
    (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).hom ≫
      locallyConstantToHolomorphicSheaf X d = locallyConstantToHolomorphicSheaf X d from
        Iso.inv_hom_id_assoc _ _]
  rfl

/-- **`H_dR^0(X) → ℍ⁰(X; 𝒪[0])` is onto when `X(ℂ)` is compact** (sub-rung S2a of
`elliptic-curve-holomorphic-form`). A class of `ℍ⁰(𝒪[0])` is a global holomorphic function,
locally constant by compactness, hence the image of a class of `ℍ⁰(ℂ[0])`, whose image in
`H_dR^0` maps to it by the square. -/
theorem deRhamToHolomorphicFunctionCohomology_zero_surjective [IsIntegral X.left] [Smooth X.hom]
    [CompactSpace (ComplexPoint X)] :
    Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0) := by
  intro γ
  let e := analyticSheafComplexIntIsoSingle X (holomorphicAdditiveSheaf X (dim X.left))
  obtain ⟨β, hβ⟩ := hypercohomologyMap_analyticSheafComplexIntMap_zero_surjective X _
    (complexConstantsToHolomorphicSheaf_app_top_surjective X (dim X.left))
    (hypercohomologyMap X e.inv 0 γ)
  refine ⟨hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) 0 β, ?_⟩
  change hypercohomologyMap X (holomorphicDeRhamToFunctionsComplexInt X) 0
    (hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) 0 β) = γ
  rw [← hypercohomologyMap_comp_apply,
    constantsToHolomorphicDeRhamComplexInt_comp_toFunctionsComplexInt]
  refine (hypercohomologyMap_comp_apply X
    (analyticSheafComplexIntMap X (complexConstantsToHolomorphicSheaf X (dim X.left))) e.hom 0
      β).trans ?_
  rw [hβ]
  refine (hypercohomologyMap_comp_apply X e.inv e.hom 0 γ).symm.trans ?_
  rw [e.inv_hom_id, hypercohomologyMap_id]
  rfl

/-- `ℍ¹(X; F¹Ω^•) → H_dR^1(X)` is injective when `X(ℂ)` is compact: `filtered-one-injective` with
its hypothesis supplied by `deRhamToHolomorphicFunctionCohomology_zero_surjective`. -/
theorem filteredToDeRhamCohomology_one_one_injective_of_compact [IsIntegral X.left]
    [Smooth X.hom] [CompactSpace (ComplexPoint X)] :
    Function.Injective (filteredToDeRhamCohomology X 1 1) :=
  filteredToDeRhamCohomology_one_one_injective X
    (deRhamToHolomorphicFunctionCohomology_zero_surjective X)

/-- On a nonempty `X(ℂ)`, upstream's holomorphic functions have two distinct global sections, the
constants `0` and `1`. -/
theorem nontrivial_holomorphicAdditiveSheaf_top [SmoothOfRelativeDimension d X.hom]
    [Nonempty (ComplexPoint X)] :
    Nontrivial ((holomorphicAdditiveSheaf X d).presheaf.obj (op ⊤)) := by
  obtain ⟨x⟩ := ‹Nonempty (ComplexPoint X)›
  refine ⟨⟨show C^ω⟮𝓘(ℂ, Fin d → ℂ), (⊤ : Opens (ComplexPoint X)); ℂ⟯ from ContMDiffMap.const 0,
    show C^ω⟮𝓘(ℂ, Fin d → ℂ), (⊤ : Opens (ComplexPoint X)); ℂ⟯ from ContMDiffMap.const 1,
    fun h ↦ ?_⟩⟩
  have := congrArg
    (fun f : C^ω⟮𝓘(ℂ, Fin d → ℂ), (⊤ : Opens (ComplexPoint X)); ℂ⟯ ↦ f ⟨x, trivial⟩) h
  exact zero_ne_one (α := ℂ) this

/-- **The target is nonzero.** On a nonempty `X(ℂ)`, `ℍ⁰(X; 𝒪[0])` has two distinct classes, so
`deRhamToHolomorphicFunctionCohomology_zero_surjective` is not a statement about a zero group. -/
theorem nontrivial_holomorphicFunctionCohomology_zero [IsIntegral X.left] [Smooth X.hom]
    [Nonempty (ComplexPoint X)] :
    Nontrivial (Hypercohomology X (holomorphicFunctionComplexInt X (dim X.left)) 0) := by
  have := nontrivial_holomorphicAdditiveSheaf_top X (dim X.left)
  have := (hypercohomologyZeroEquivGlobalSections X
    (holomorphicAdditiveSheaf X (dim X.left))).nontrivial
  exact (hypercohomologyMap_injective_of_isIso X
    (analyticSheafComplexIntIsoSingle X (holomorphicAdditiveSheaf X (dim X.left))).hom 0).nontrivial

end HodgeLadder
