module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Graded quotients and closed immersions of `Proj`

For a graded algebra `𝒜` over `R` and a homogeneous ideal `I`, the images of the pieces `𝒜 i`
grade `A ⧸ I` (`ProjQuotient.gradedAlgebra`), and the quotient map is a graded ring map
(`mkGraded`). A graded ring map `f : 𝒜 →+*ᵍ ℬ` onto every piece meets the hypothesis of Mathlib's
`Proj.map` (`irrelevant_le_map`), and `Proj.map f : Proj ℬ ⟶ Proj 𝒜` is a closed immersion
(`isClosedImmersion_map`): over `D₊(s)` it is `Spec` of the surjection `A_(s) → B_(f s)`
(`away_map_surjective`), the local-on-target argument of `HodgeLadder.General.Segre`. In particular
`Proj (A ⧸ I) ⟶ Proj A` is a closed immersion (`quotι`), and the preimage of `D₊(s)` is
`D₊(s mod I)` by definition.

## Main definitions

* `HodgeLadder.ProjQuotient.grading`, `mkGraded`, `quotι`

## Main results

* instance `HodgeLadder.ProjQuotient.gradedAlgebra`
* `HodgeLadder.ProjQuotient.irrelevant_le_map`, `away_map_surjective`, `isClosedImmersion_map`
* instance `HodgeLadder.ProjQuotient.isClosedImmersion_quotι`, `quotι_preimage_basicOpen`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization DirectSum

namespace HodgeLadder.ProjQuotient

section Grading

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing R] [CommRing A]
  [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

/-- The quotient grading on `A ⧸ I`: the `i`-th piece is the image of `𝒜 i`. -/
def grading (i : ι) : Submodule R (A ⧸ I.toIdeal) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

/-- The pieces of the quotient grading are the images of the pieces of `𝒜`. -/
theorem mem_grading_iff {i : ι} {b : A ⧸ I.toIdeal} :
    b ∈ grading 𝒜 I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I.toIdeal a = b := by
  simp [grading]

/-- The class of an element of `𝒜 i` lies in the `i`-th piece of the quotient grading. -/
theorem mk_mem_grading {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk I.toIdeal a ∈ grading 𝒜 I i :=
  (mem_grading_iff 𝒜 I).mpr ⟨a, ha, rfl⟩

/-- The quotient grading is multiplicative. -/
instance gradedMonoid : SetLike.GradedMonoid (grading 𝒜 I) where
  one_mem := by
    rw [← map_one (Ideal.Quotient.mk I.toIdeal)]
    exact mk_mem_grading 𝒜 I SetLike.GradedOne.one_mem
  mul_mem := by
    intro i j p q hp hq
    obtain ⟨a, ha, rfl⟩ := (mem_grading_iff 𝒜 I).mp hp
    obtain ⟨b, hb, rfl⟩ := (mem_grading_iff 𝒜 I).mp hq
    rw [← map_mul]
    exact mk_mem_grading 𝒜 I (SetLike.GradedMul.mul_mem ha hb)

/-- The quotient map on the `i`-th piece. -/
def pieceMap (i : ι) : 𝒜 i →+ grading 𝒜 I i where
  toFun x := ⟨Ideal.Quotient.mk I.toIdeal x, mk_mem_grading 𝒜 I x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The decomposition of `A` followed by the quotient map on each piece. -/
def decomposeAux : A →+ ⨁ i, grading 𝒜 I i :=
  (DirectSum.map (pieceMap 𝒜 I)).comp (decomposeAddEquiv 𝒜).toAddMonoidHom

/-- A homogeneous ideal has its homogeneous components in the ideal, so `decomposeAux` kills it. -/
theorem decomposeAux_eq_zero {a : A} (ha : a ∈ I.toIdeal) : decomposeAux 𝒜 I a = 0 := by
  ext i
  simp only [decomposeAux, AddMonoidHom.coe_comp, Function.comp_apply, map_apply,
    DirectSum.zero_apply]
  change Ideal.Quotient.mk I.toIdeal (decompose 𝒜 a i : A) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact I.isHomogeneous i ha

/-- The decomposition of `A ⧸ I`. -/
def decomposeQuot (q : A ⧸ I.toIdeal) : ⨁ i, grading 𝒜 I i :=
  Quotient.liftOn' q (decomposeAux 𝒜 I) fun a b h => by
    rw [Submodule.quotientRel_def] at h
    have := decomposeAux_eq_zero 𝒜 I h
    rwa [map_sub, sub_eq_zero] at this

/-- `decomposeQuot` on the class of `a` is the decomposition of `a`, read in the quotient. -/
theorem decomposeQuot_mk (a : A) :
    decomposeQuot 𝒜 I (Ideal.Quotient.mk I.toIdeal a) = decomposeAux 𝒜 I a := rfl

/-- `decomposeQuot` is additive. -/
theorem decomposeQuot_add (p q : A ⧸ I.toIdeal) :
    decomposeQuot 𝒜 I (p + q) = decomposeQuot 𝒜 I p + decomposeQuot 𝒜 I q := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective p
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_add, decomposeQuot_mk, decomposeQuot_mk, decomposeQuot_mk, map_add]

/-- Summing the components after the quotient map is the quotient map of the sum. -/
theorem coeAddMonoidHom_map_pieceMap (x : ⨁ i, 𝒜 i) :
    DirectSum.coeAddMonoidHom (grading 𝒜 I) (DirectSum.map (pieceMap 𝒜 I) x) =
      Ideal.Quotient.mk I.toIdeal (DirectSum.coeAddMonoidHom 𝒜 x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y => simp [pieceMap]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The quotient grading.** For a homogeneous ideal `I`, the images of the pieces of `𝒜` grade
`A ⧸ I`. -/
instance gradedAlgebra : GradedAlgebra (grading 𝒜 I) where
  decompose' := decomposeQuot 𝒜 I
  left_inv q := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [decomposeQuot_mk, decomposeAux, AddMonoidHom.comp_apply,
      coeAddMonoidHom_map_pieceMap]
    congr 1
    exact (decomposeAddEquiv 𝒜).symm_apply_apply a
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
      rw [map_zero, ← map_zero (Ideal.Quotient.mk I.toIdeal), decomposeQuot_mk, map_zero]
    | of i y =>
      obtain ⟨a, ha, hy⟩ := (mem_grading_iff 𝒜 I).mp y.2
      rw [coeAddMonoidHom_of, ← hy, decomposeQuot_mk, decomposeAux, AddMonoidHom.comp_apply]
      change DirectSum.map (pieceMap 𝒜 I) (decompose 𝒜 a) = _
      rw [decompose_of_mem 𝒜 ha, map_of]
      congr 1
      exact Subtype.ext hy
    | add x y hx hy => rw [map_add, decomposeQuot_add, hx, hy]

end Grading

section ClosedImmersion

universe u

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)

/-- A graded ring map onto every piece maps the irrelevant ideal onto the irrelevant ideal. -/
theorem irrelevant_le_map (hsurj : ∀ n, ∀ b ∈ ℬ n, ∃ a ∈ 𝒜 n, f a = b) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  change (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤ _
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi b hb
  obtain ⟨a, ha, rfl⟩ := hsurj i b hb
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi ha)

/-- A graded ring map onto every piece induces surjections of degree-zero localizations. -/
theorem away_map_surjective (hsurj : ∀ n, ∀ b ∈ ℬ n, ∃ a ∈ 𝒜 n, f a = b) {d : ℕ} {s : A}
    (hs : s ∈ 𝒜 d) : Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (Graded.map_mem f hs) z
  obtain ⟨a, ha, rfl⟩ := hsurj _ b hb
  exact ⟨Away.mk 𝒜 hs n a ha, Away.map_mk f s hs n a ha⟩

/-- **`Proj` of a graded surjection is a closed immersion.** For a graded ring map `f` onto every
piece, `Proj.map f : Proj ℬ ⟶ Proj 𝒜` is a closed immersion: over `D₊(s)` it is `Spec` of the
surjection `A_(s) → B_(f s)`. -/
theorem isClosedImmersion_map (hsurj : ∀ n, ∀ b ∈ ℬ n, ∃ a ∈ 𝒜 n, f a = b) :
    IsClosedImmersion (Proj.map f (irrelevant_le_map f hsurj)) := by
  set φ := Proj.map f (irrelevant_le_map f hsurj)
  have hcov : ⨆ t : Σ i : PNat, 𝒜 i, Proj.basicOpen 𝒜 (t.2 : A) = ⊤ := by
    refine top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr
      ⟨(Proj.affineOpenCover 𝒜).idx x, ?_⟩
    have := (Proj.affineOpenCover 𝒜).covers x
    rw [← Proj.opensRange_awayι 𝒜 _ ((Proj.affineOpenCover 𝒜).idx x).2.2
      ((Proj.affineOpenCover 𝒜).idx x).1.2]
    exact this
  apply IsZariskiLocalAtTarget.of_iSup_eq_top _ hcov
  rintro ⟨⟨i, hi⟩, s, hs⟩
  replace hs : s ∈ 𝒜 i := hs
  have : IsOpenImmersion (Proj.awayι ℬ (f s) (Graded.map_mem f hs) hi) :=
    Proj.instIsOpenImmersionAwayι ℬ (f s) (Graded.map_mem f hs) hi
  change IsClosedImmersion (φ ∣_ Proj.basicOpen 𝒜 s)
  have hrange : Set.range (Proj.awayι ℬ (f s) (Graded.map_mem f hs) hi) =
      Set.range (φ ⁻¹ᵁ Proj.basicOpen 𝒜 s).ι := by
    rw [Scheme.Opens.range_ι, Proj.map_preimage_basicOpen, ← Proj.opensRange_awayι ℬ (f s)
      (Graded.map_mem f hs) hi]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq (Proj.awayι ℬ (f s) (Graded.map_mem f hs) hi)
    (φ ⁻¹ᵁ Proj.basicOpen 𝒜 s).ι hrange
  have key : e.hom ≫ φ ∣_ Proj.basicOpen 𝒜 s =
      Spec.map (CommRingCat.ofHom (Away.map f s)) ≫
        (Proj.basicOpenIsoSpec 𝒜 s hs hi).inv := by
    refine (cancel_mono (Proj.basicOpen 𝒜 s).ι).mp ?_
    simp only [Category.assoc, morphismRestrict_ι, e]
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, Proj.awayι_comp_map f _ hi s hs,
      ← Proj.basicOpenIsoSpec_inv_ι]
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion e.hom, key]
  have h1 : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f s))) :=
    IsClosedImmersion.spec_of_surjective _ (away_map_surjective f hsurj hs)
  infer_instance

end ClosedImmersion

section Quotient

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

/-- The quotient map `A → A ⧸ I` as a graded ring map. -/
def mkGraded : 𝒜 →+*ᵍ grading 𝒜 I where
  toRingHom := Ideal.Quotient.mk I.toIdeal
  map_mem hx := mk_mem_grading 𝒜 I hx

/-- `mkGraded` is the quotient map. -/
@[simp]
theorem mkGraded_apply (a : A) : mkGraded 𝒜 I a = Ideal.Quotient.mk I.toIdeal a := rfl

/-- The quotient map is onto every piece of the quotient grading. -/
theorem mkGraded_surjOn : ∀ k, ∀ b ∈ grading 𝒜 I k, ∃ a ∈ 𝒜 k, mkGraded 𝒜 I a = b :=
  fun _ _ hb => (mem_grading_iff 𝒜 I).mp hb

/-- The closed subscheme `Proj (A ⧸ I) ⟶ Proj A` of a homogeneous ideal. -/
def quotι : Proj (grading 𝒜 I) ⟶ Proj 𝒜 :=
  Proj.map (mkGraded 𝒜 I) (irrelevant_le_map _ (mkGraded_surjOn 𝒜 I))

/-- `Proj (A ⧸ I) ⟶ Proj A` is a closed immersion. -/
instance isClosedImmersion_quotι : IsClosedImmersion (quotι 𝒜 I) :=
  isClosedImmersion_map _ (mkGraded_surjOn 𝒜 I)

/-- The preimage of `D₊(s)` in `Proj (A ⧸ I)` is `D₊(s mod I)`. -/
theorem quotι_preimage_basicOpen (s : A) :
    quotι 𝒜 I ⁻¹ᵁ Proj.basicOpen 𝒜 s =
      Proj.basicOpen (grading 𝒜 I) (Ideal.Quotient.mk I.toIdeal s) := rfl

end Quotient

end HodgeLadder.ProjQuotient
