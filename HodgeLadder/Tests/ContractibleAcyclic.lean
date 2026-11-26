module

public import LefschetzPort.Oka.Topology.Sheaves.Cohomology.MayerVietoris
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainResolution
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Contractible
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
public import Other.AlgebraicGeometry.Cohomology.GlobalSections
public import Other.AlgebraicTopology.Sheaf.FlasqueGlobalSections

/-!
# Contractible opens have no rational cohomology in positive degrees

Let `X` be a smooth projective integral scheme over `ℂ` and `U ⊆ X(ℂ)` a contractible open in the
analytic topology. This file proves `Hᵠ(U; ℚ_X) = 0` for `q > 0`, for Mathlib's cohomology of an
open (`Sheaf.H'`), the group that `forgetSupport_injective_of_subsingleton` and
`forgetSupport_surjective_of_subsingleton` (rung `forget-support-exact`) take as hypothesis.

The proof is the classical one, through a flasque resolution:

1. `Hᵠ(U; F) ≅ Hᵠ(U, F|_U)` (`TopCat.Sheaf.H'AddEquiv`, from the Oka port), and `ℚ_X|_U ≅ ℚ_U`
   (restriction to an open is the inverse image, which commutes with constant sheaves).
2. On a space `Y` with a basis of contractible opens, `ℚ_Y` is resolved by the sheafified singular
   cochains `𝒞^•` (upstream `constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis`);
   on a Hausdorff space whose opens are paracompact the `𝒞ⁿ` are flasque and the global sections of
   `𝒞^•` compute singular cohomology (upstream `singularCochainSheaf_isFlasque_of_opens_paracompact`,
   `topOpenToGlobalSingularCochainSheafComplex_quasiIso`).
3. Flasque sheaves are acyclic (upstream `TopCat.Sheaf.IsFlasque.subsingleton_cohomology_succ`,
   by dimension shifting into an injective sheaf). Dimension shifting
   along the cycle sheaves `Zⁱ → 𝒞ⁱ → Zⁱ⁺¹` then gives `Hᵠ⁺¹(Y; Zⁱ) = 0` for all `i` as soon as the
   global sections of `𝒞^•` are exact in positive degrees, which holds when `Y` is contractible
   (upstream `singularCochainComplex_exactAt_of_contractible`). Finally `ℚ_Y ≅ Z⁰`.
4. For `U ⊆ X(ℂ)` the hypotheses of step 2 come from upstream: `X(ℂ)` is Hausdorff
   (`IsProjective.complexPoint_t2Space`), its opens are paracompact (`openParacompactSpace`), and it
   has a basis of contractible opens (`exists_contractibleOpen_le`), which passes to `U`
   (`contractibleOpenBasis_of_isOpenEmbedding`).

The general statement for a topological space is
`HodgeLadder.Tests.Acyclic.subsingleton_H_const_of_contractible`; it uses no algebraic geometry.

## Main results

* `HodgeLadder.Tests.contractibleOpen_subsingleton_H'`: for smooth projective integral `X` and a
  contractible open `U ⊆ X(ℂ)`, `Subsingleton (Sheaf.H' ℚ_X q U)` for `q > 0`.
* `HodgeLadder.Tests.Acyclic.subsingleton_H_const_of_contractible`: a contractible Hausdorff space
  with paracompact opens and a basis of contractible opens has `Hᵠ⁺¹(Y; ℚ) = 0`.
* `HodgeLadder.Tests.Acyclic.subsingleton_H_of_isFlasque`: flasque sheaves are acyclic (a
  restatement of upstream's `TopCat.Sheaf.IsFlasque.subsingleton_cohomology_succ`).
* `HodgeLadder.Tests.Acyclic.subsingleton_H_cycles`: the cycle sheaves of a flasque resolution with
  exact global sections are acyclic. The cycle sheaves need not be flasque (`Z⁰` is the
  resolved sheaf), so upstream's `cycles_isFlasque_of_exact_le` does not apply; the exactness of
  global sections carries the induction.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry ComplexPoint TopologicalSpace Abelian

set_option linter.auxLemma false

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Tests

namespace Acyclic

universe u

variable {Y : TopCat.{u}}

open TopCat.Sheaf Opposite

/-- Dimension shifting in degree one. -/
theorem subsingleton_H_one_X₁ {S : ShortComplex (TopCat.AbSheaf Y)} (hS : S.ShortExact)
    [Subsingleton (H S.X₂ 1)] (hg : Function.Surjective (S.g.hom.app (op ⊤))) :
    Subsingleton (H S.X₁ 1) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := (H.exact₁ hS 0 1 rfl x).1 (Subsingleton.elim _ _)
  obtain ⟨s, rfl⟩ := (H.equiv₀ S.X₃).symm.surjective y
  obtain ⟨t, rfl⟩ := hg s
  rw [← H.map_equiv₀_symm, H.δ_map_g]

/-- Dimension shifting in higher degrees. -/
theorem subsingleton_H_succ_X₁ {S : ShortComplex (TopCat.AbSheaf Y)} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (H S.X₃ n)] [Subsingleton (H S.X₂ (n + 1))] :
    Subsingleton (H S.X₁ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := (H.exact₁ hS n (n + 1) rfl x).1 (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero]

/-- A flasque sheaf has no cohomology in positive degrees: upstream's
`TopCat.Sheaf.IsFlasque.subsingleton_cohomology_succ`, in the notation of this file. -/
theorem subsingleton_H_of_isFlasque (n : ℕ) :
    ∀ (F : TopCat.AbSheaf Y) [TopCat.Presheaf.IsFlasque F.obj], Subsingleton (H F (n + 1)) :=
  fun F _ => TopCat.Sheaf.IsFlasque.subsingleton_cohomology_succ F n

/-- Sections of a composite of sheaf morphisms. -/
theorem app_comp_apply {F G E : TopCat.AbSheaf Y} (f : F ⟶ G) (g : G ⟶ E) (V : (Opens Y)ᵒᵖ)
    (x : F.obj.obj V) : (f ≫ g).hom.app V x = g.hom.app V (f.hom.app V x) := rfl

/-- A monomorphism of sheaves is injective on sections. -/
theorem app_injective_of_mono {F G : TopCat.AbSheaf Y} (f : F ⟶ G) [Mono f] (V : (Opens Y)ᵒᵖ) :
    Function.Injective (f.hom.app V) := by
  have : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have : Mono (f.hom.app V) := (NatTrans.mono_iff_mono_app f.hom).1 inferInstance V
  exact (AddCommGrpCat.mono_iff_injective _).1 this

variable (K : CochainComplex (TopCat.AbSheaf Y) ℕ)

/-- The short complex `Zⁱ → Kⁱ → Zⁱ⁺¹` of cycle sheaves. -/
noncomputable def cyclesSC (i : ℕ) : ShortComplex (TopCat.AbSheaf Y) :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) (by
    rw [← cancel_mono (K.iCycles (i + 1))]
    simp)

/-- `Zⁱ → Kⁱ → Zⁱ⁺¹` is short exact when `K` is exact at `i + 1`. -/
theorem cyclesSC_shortExact (i : ℕ) (hK : K.ExactAt (i + 1)) : (cyclesSC K i).ShortExact := by
  let S := cyclesSC K i
  have hkerD := K.cyclesIsKernel i (i + 1) (by simp)
  have hker : IsLimit (KernelFork.ofι S.f S.zero) :=
    Limits.isKernelOfComp (K.iCycles (i + 1)) (K.d i (i + 1)) hkerD
      S.zero (K.toCycles_i i (i + 1))
  have hepi : Epi S.g := by
    dsimp [S, cyclesSC]
    have hnext : (ComplexShape.up ℕ).next (i + 1) = i + 2 := by simp
    have hsc' : (K.sc' i (i + 1) (i + 2)).Exact :=
      (K.exactAt_iff' (i := i) (j := i + 1) (k := i + 2) (by simp) hnext).mp hK
    have hepi' : Epi ((K.sc' i (i + 1) (i + 2)).toCycles) :=
      hsc'.epi_toCycles
    rw [← K.toCycles_cyclesIsoSc'_hom i (i + 1) (i + 2) (by simp) hnext] at hepi'
    let e := K.cyclesIsoSc' i (i + 1) (i + 2) (by simp) hnext
    have hfac : K.toCycles i (i + 1) =
        (K.toCycles i (i + 1) ≫ e.hom) ≫ e.inv := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    let : Epi (K.toCycles i (i + 1) ≫ e.hom) := hepi'
    rw [hfac]
    infer_instance
  have hmono : Mono S.f := by
    dsimp [S, cyclesSC]
    infer_instance
  exact
    { exact := S.exact_of_f_is_kernel hker
      mono_f := hmono
      epi_g := hepi }

/-- If the global sections of `K` are exact at `i + 1`, then `Kⁱ(⊤) → Zⁱ⁺¹(⊤)` is surjective. -/
theorem toCycles_app_surjective (i : ℕ)
    (hΓ : ∀ t : (K.X (i + 1)).obj.obj (op ⊤), (K.d (i + 1) (i + 2)).hom.app (op ⊤) t = 0 →
      ∃ u, (K.d i (i + 1)).hom.app (op ⊤) u = t) :
    Function.Surjective ((K.toCycles i (i + 1)).hom.app (op ⊤)) := by
  intro s
  obtain ⟨u, hu⟩ := hΓ ((K.iCycles (i + 1)).hom.app (op ⊤) s) (by
    rw [← app_comp_apply, K.iCycles_d]
    rfl)
  refine ⟨u, app_injective_of_mono (K.iCycles (i + 1)) (op ⊤) ?_⟩
  rw [← app_comp_apply, K.toCycles_i, hu]

/-- A resolution by flasque sheaves whose global sections are exact in positive degrees has
acyclic cycle sheaves. -/
theorem subsingleton_H_cycles
    (hflasque : ∀ i, TopCat.Presheaf.IsFlasque (K.X i).obj)
    (hK : ∀ i, K.ExactAt (i + 1))
    (hΓ : ∀ i, ∀ t : (K.X (i + 1)).obj.obj (op ⊤), (K.d (i + 1) (i + 2)).hom.app (op ⊤) t = 0 →
      ∃ u, (K.d i (i + 1)).hom.app (op ⊤) u = t) (q : ℕ) :
    ∀ i, Subsingleton (H (K.cycles i) (q + 1)) := by
  induction q with
  | zero =>
    intro i
    have : Subsingleton (H (cyclesSC K i).X₂ 1) := subsingleton_H_of_isFlasque 0 (K.X i)
    exact subsingleton_H_one_X₁ (S := cyclesSC K i) (cyclesSC_shortExact K i (hK i))
      (toCycles_app_surjective K i (hΓ i))
  | succ q ih =>
    intro i
    have : Subsingleton (H (cyclesSC K i).X₂ (q + 1 + 1)) :=
      subsingleton_H_of_isFlasque (q + 1) (K.X i)
    have : Subsingleton (H (cyclesSC K i).X₃ (q + 1)) := ih (i + 1)
    exact subsingleton_H_succ_X₁ (S := cyclesSC K i) (cyclesSC_shortExact K i (hK i)) (q + 1)

end Acyclic

namespace Acyclic

open TopCat.Sheaf Opposite AlgebraicTopology AlgebraicTopology.Singular HomologicalComplex

variable (Y : TopCat.{0})

/-- Singular cochains of a contractible space are exact in positive degrees, in the
top-open presentation. -/
theorem globalRaw_exactAt [ContractibleSpace Y] (n : ℕ) :
    (globalRawSingularCochainComplex ℚ Y).ExactAt (n + 1) := by
  have h := singularCochainComplex_exactAt_of_contractible ℚ Y n
  rw [exactAt_iff_isZero_homology] at h ⊢
  have h₁ : IsZero (((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex).homology
      (n + 1)) :=
    h.of_iso (homologyMapIso (singularCochainComplexIsoTopOpen ℚ Y) (n + 1)).symm
  have h₂ := (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat).map_isZero h₁
  exact (h₂.of_iso (topOpenForgottenSingularCochainHomologyIso ℚ Y (n + 1))).of_iso
    (homologyMapIso (globalRawSingularCochainComplexIso ℚ Y) (n + 1))

/-- Global sections of the sheafified singular cochains of a contractible paracompact Hausdorff
space are exact in positive degrees. -/
theorem globalSheaf_exactAt [ContractibleSpace Y] [ParacompactSpace Y] [T2Space Y] (n : ℕ) :
    (globalSingularCochainSheafComplex ℚ Y).ExactAt (n + 1) := by
  have := topOpenToGlobalSingularCochainSheafComplex_quasiIso (Y := Y)
  exact (exactAt_iff_of_quasiIsoAt (topOpenToGlobalSingularCochainSheafComplex ℚ Y) (n + 1)).1
    (globalRaw_exactAt Y n)

/-- On a contractible Hausdorff space with paracompact opens and a basis of contractible open
sets, the constant sheaf `ℚ` has no cohomology in positive degrees. -/
theorem subsingleton_H_const_of_contractible [ContractibleSpace Y] [T2Space Y]
    [∀ V : Opens Y, ParacompactSpace V] [ParacompactSpace Y]
    (hY : ∀ (x : Y) (V : Opens Y), x ∈ V →
      ∃ W : Opens Y, x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)
    (q : ℕ) : Subsingleton (H ((constantFunctor Y).obj (AddCommGrpCat.of ℚ)) (q + 1)) := by
  let K := singularCochainSheafComplex ℚ Y
  let ι := constantsToSingularCochainSheafComplex ℚ Y
  have hι : QuasiIso ι :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hY
  have hK : ∀ i, K.ExactAt (i + 1) := fun i =>
    (quasiIsoAt_iff_exactAt ι (i + 1) (CochainComplex.exactAt_succ_single_obj _ _)).1
      inferInstance
  have hflasque : ∀ i, TopCat.Presheaf.IsFlasque (K.X i).obj := fun i =>
    singularCochainSheaf_isFlasque_of_opens_paracompact (R := ℚ) (X := Y) i
  have hΓ : ∀ i, ∀ t : (K.X (i + 1)).obj.obj (op ⊤), (K.d (i + 1) (i + 2)).hom.app (op ⊤) t = 0 →
      ∃ u, (K.d i (i + 1)).hom.app (op ⊤) u = t := by
    intro i t ht
    have h := globalSheaf_exactAt Y i
    rw [exactAt_iff' _ i (i + 1) (i + 2) (by simp) (by simp)] at h
    exact (ShortComplex.ab_exact_iff _).1 h t ht
  let e : (constantFunctor Y).obj (AddCommGrpCat.of ℚ) ≅ K.cycles 0 :=
    (singleObjHomologySelfIso _ _ _).symm ≪≫ isoOfQuasiIsoAt ι 0 ≪≫ K.isoHomologyπ₀.symm
  have := subsingleton_H_cycles K hflasque hK hΓ q 0
  exact @Equiv.subsingleton _ _ (H.addEquivOfIso e (q + 1)).toEquiv this

end Acyclic

open TopCat.Sheaf Opposite AlgebraicTopology.Singular in
/-- **Contractible opens are acyclic.** Let `X` be a smooth projective integral scheme over `ℂ`
and `U ⊆ X(ℂ)` an analytic open that is contractible. Then `Hᵠ(U; ℚ_X) = 0` for `q > 0`, where
`Hᵠ(U; -)` is Mathlib's cohomology of an open (`Sheaf.H'`), the group appearing in the long exact
sequence of the pair `(X(ℂ), U)` used by `forgetSupport_injective_of_subsingleton`. -/
theorem contractibleOpen_subsingleton_H' (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (U : Opens (ComplexPoint X)) [ContractibleSpace U] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) q U) := by
  obtain ⟨q, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  let Xt := TopCat.of (ComplexPoint X)
  let Y := (Opens.toTopCat Xt).obj U
  have hj := Opens.isOpenEmbedding (X := Xt) U
  have hpara : ∀ V : Opens Y, ParacompactSpace V := fun V => by
    let Vi : Opens Xt := ⟨_ '' (V : Set Y), (hj.isOpen_iff_image_isOpen).mp V.2⟩
    have : ParacompactSpace Vi := openParacompactSpace X Vi
    exact (hj.toIsEmbedding.homeomorphImage (V : Set Y)).paracompactSpace_iff.mpr this
  have : ParacompactSpace Y := openParacompactSpace X U
  have : ContractibleSpace Y := inferInstanceAs (ContractibleSpace U)
  have : T2Space Y := inferInstanceAs (T2Space U)
  have hbasis := contractibleOpenBasis_of_isOpenEmbedding _ hj
    (fun x V hxV => exists_contractibleOpen_le X x V hxV)
  have hY := Acyclic.subsingleton_H_const_of_contractible Y hbasis q
  let C := (TopCat.Sheaf.constantFunctor Xt).obj (AddCommGrpCat.of ℚ)
  let e : (restrictOpen U).obj C ≅ (constantFunctor Y).obj (AddCommGrpCat.of ℚ) :=
    ((pullbackAbIsoRestrictAb U.isOpenEmbedding).app C).symm ≪≫
      (pullbackConstantSheafIso _).app (AddCommGrpCat.of ℚ)
  exact @Equiv.subsingleton _ _ ((H'AddEquiv U C (q + 1)).trans (H.addEquivOfIso e (q + 1))).toEquiv hY

end HodgeLadder.Tests
