module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Geometric integrality from two charts

General lemmas kept local (decision 0011) for rung `elliptic-square-witness`. Mathlib at the pin
has `GeometricallyIntegral` and the instance making `X ×_S Y` integral when one factor is
geometrically integral, flat and universally open over an integral locally noetherian other
factor; it has no criterion for a concrete scheme to be geometrically integral beyond affine space.
This file gives two.

* Two charts. If `X = U ∪ V` with `U ⟶ S` and `V ⟶ S` geometrically integral and `U ∩ V ⟶ S`
  surjective, then `X ⟶ S` is geometrically integral. For a base change `Z = X ×_S Spec K` the
  preimages of `U` and `V` are base changes of the charts (`isPullback_restrict`, pasting Mathlib's
  `isPullback_morphismRestrict`), hence integral; the preimage of `U ∩ V` maps onto `Spec K`, so
  it is nonempty; and an integral scheme is reduced and irreducible, which the cover passes to `Z`
  (`irreducibleSpace_of_two_opens`, the two-open case of
  `HodgeLadder.Tests.irreducibleSpace_of_cover`, kept here so that this module imports Mathlib
  only).
* Affine charts. `Spec A ⟶ Spec R` is geometrically integral when `A ⊗[R] K` is a domain for
  every field `K` over `R` (`geometricallyIntegral_spec`, through Mathlib's `pullbackSpecIso`),
  and `(R[σ] ⧸ (g)) ⊗[R] K ≃ K[σ] ⧸ (g)` (Mathlib's `quotientTensorEquiv` and
  `algebraTensorAlgEquiv`), so a principal quotient is geometrically a domain when `(g)` stays
  prime over every field (`isDomain_quotient_tensor`).

## Main results

* `HodgeLadder.GeometricallyIntegralCover.irreducibleSpace_of_two_opens`
* `HodgeLadder.GeometricallyIntegralCover.isPullback_restrict`
* `HodgeLadder.GeometricallyIntegralCover.geometricallyIntegral_of_cover`
* `HodgeLadder.GeometricallyIntegralCover.geometricallyIntegral_iso_comp`
* `HodgeLadder.GeometricallyIntegralCover.geometricallyIntegral_spec`
* `HodgeLadder.GeometricallyIntegralCover.isDomain_quotient_tensor`
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace HodgeLadder.GeometricallyIntegralCover

variable {X S : Scheme} (f : X ⟶ S)

/-- The preimage of an open `U` under the first projection of a pullback square is a pullback
of `U.ι ≫ f`. -/
theorem isPullback_restrict {K : Scheme} {y : K ⟶ S} {Z : Scheme} {fst : Z ⟶ X} {snd : Z ⟶ K}
    (h : IsPullback fst snd f y) (U : X.Opens) :
    IsPullback (fst ∣_ U) ((fst ⁻¹ᵁ U).ι ≫ snd) (U.ι ≫ f) y :=
  (isPullback_morphismRestrict fst U).paste_vert h

/-- A space covered by two irreducible opens that meet is irreducible. -/
theorem irreducibleSpace_of_two_opens {Z : Type*} [TopologicalSpace Z] {U V : Set Z}
    (hU : IsOpen U) (hUi : IsIrreducible U) (hVi : IsIrreducible V)
    (hcov : U ∪ V = Set.univ) (hUV : (U ∩ V).Nonempty) : IrreducibleSpace Z := by
  have h1 : V ⊆ closure U :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hVi.2 hU
      (by rw [Set.inter_comm]; exact hUV)).trans (closure_mono Set.inter_subset_right)
  have h2 : closure U = Set.univ :=
    Set.eq_univ_of_univ_subset (hcov ▸ Set.union_subset subset_closure h1)
  have h3 := hUi.closure
  rw [h2] at h3
  exact (irreducibleSpace_def Z).mpr h3

/-- **Geometric integrality from two charts.** If the opens `U` and `V` cover `X`, both charts are
geometrically integral over `S`, and their overlap maps onto `S`, then `X` is geometrically
integral over `S`. -/
theorem geometricallyIntegral_of_cover (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    [GeometricallyIntegral (U.ι ≫ f)] [GeometricallyIntegral (V.ι ≫ f)]
    [Surjective ((U ⊓ V).ι ≫ f)] : GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have hU : IsIntegral (fst ⁻¹ᵁ U).toScheme :=
    GeometricallyIntegral.geometrically_isIntegral (f := U.ι ≫ f) y _ _ (isPullback_restrict f h U)
  have hV : IsIntegral (fst ⁻¹ᵁ V).toScheme :=
    GeometricallyIntegral.geometrically_isIntegral (f := V.ι ≫ f) y _ _ (isPullback_restrict f h V)
  have hW : Surjective ((fst ⁻¹ᵁ (U ⊓ V)).ι ≫ snd) :=
    MorphismProperty.of_isPullback (isPullback_restrict f h (U ⊓ V)) inferInstance
  obtain ⟨w, -⟩ := hW.surj (Classical.arbitrary _)
  have hcov : fst ⁻¹ᵁ U ⊔ fst ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
  have hw : (fst ⁻¹ᵁ (U ⊓ V)).ι w ∈ fst ⁻¹ᵁ U ⊓ fst ⁻¹ᵁ V := by
    rw [← Scheme.Hom.preimage_inf]; exact w.2
  have : Nonempty Z := ⟨(fst ⁻¹ᵁ (U ⊓ V)).ι w⟩
  have hred : IsReduced Z := by
    have hc : TopologicalSpace.IsOpenCover
        (fun b : Bool => if b then fst ⁻¹ᵁ U else fst ⁻¹ᵁ V) := by
      rw [TopologicalSpace.IsOpenCover, iSup_bool_eq]
      exact hcov
    let 𝒰 := Z.openCoverOfIsOpenCover _ hc
    have : ∀ i, IsReduced (𝒰.X i) := by
      intro i; cases i
      · exact inferInstanceAs (IsReduced (fst ⁻¹ᵁ V).toScheme)
      · exact inferInstanceAs (IsReduced (fst ⁻¹ᵁ U).toScheme)
    exact IsReduced.of_openCover (𝒰 := 𝒰)
  have hirr : IrreducibleSpace Z := by
    refine irreducibleSpace_of_two_opens (fst ⁻¹ᵁ U).isOpen
      (isIrreducible_iff_irreducibleSpace.mpr
        (inferInstanceAs (IrreducibleSpace (fst ⁻¹ᵁ U).toScheme)))
      (isIrreducible_iff_irreducibleSpace.mpr
        (inferInstanceAs (IrreducibleSpace (fst ⁻¹ᵁ V).toScheme))) ?_
      ⟨(fst ⁻¹ᵁ (U ⊓ V)).ι w, hw.1, hw.2⟩
    have := congrArg (fun W : Z.Opens => (W : Set Z)) hcov
    simpa using this
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

/-- Geometric integrality is invariant under precomposition with an isomorphism. -/
theorem geometricallyIntegral_iso_comp {Y : Scheme} (e : Y ≅ X) [GeometricallyIntegral f] :
    GeometricallyIntegral (e.hom ≫ f) :=
  MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
    (IsPullback.of_horiz_isIso (fst := e.hom) (snd := e.hom ≫ f) (f := f) (g := 𝟙 S)
      ⟨by simp⟩) ‹_›

universe u

/-- `Spec A ⟶ Spec R` is geometrically integral when `A ⊗[R] K` is a domain for every field `K`
over `R`. -/
theorem geometricallyIntegral_spec (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (A ⊗[R] K)) :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  refine ⟨geometrically_iff_of_commRing.mpr fun K _ _ Y fst snd hpb => ?_⟩
  have := h K
  let e := hpb.isoPullback ≪≫ pullbackSpecIso R A K
  have : Nonempty Y := ⟨e.inv (Classical.arbitrary _)⟩
  exact isIntegral_of_isOpenImmersion e.hom

open MvPolynomial in
/-- Base change of a principal quotient of a polynomial ring: `(R[σ] ⧸ (g)) ⊗[R] K` is a domain
when `(g)` stays prime in `K[σ]`. -/
theorem isDomain_quotient_tensor {R K σ : Type u} [CommRing R] [Field K] [Algebra R K]
    (g : MvPolynomial σ R) (hg : (Ideal.span {map (algebraMap R K) g}).IsPrime) :
    IsDomain ((MvPolynomial σ R ⧸ Ideal.span {g}) ⊗[R] K) := by
  let φ : MvPolynomial σ R ⊗[R] K ≃ₐ[R] MvPolynomial σ K :=
    (Algebra.TensorProduct.comm R _ K).trans ((algebraTensorAlgEquiv R K).restrictScalars R)
  have hφ : ((Ideal.span {g}).map (algebraMap (MvPolynomial σ R) (MvPolynomial σ R ⊗[R] K))).map
      φ = Ideal.span {map (algebraMap R K) g} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    congr 2
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
  have : IsDomain (MvPolynomial σ K ⧸ Ideal.span {map (algebraMap R K) g}) :=
    Ideal.Quotient.isDomain _
  let e := (Algebra.TensorProduct.quotientTensorEquiv (R := R) R K (MvPolynomial σ R)
    (Ideal.span {g})).toRingEquiv.trans
      (Ideal.quotientEquiv _ (Ideal.span {map (algebraMap R K) g}) φ.toRingEquiv
        (by rw [← hφ]; rfl))
  exact e.toMulEquiv.isDomain

end HodgeLadder.GeometricallyIntegralCover
