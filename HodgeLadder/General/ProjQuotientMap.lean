module

public import HodgeLadder.General.ProjQuotient

/-!
# Graded maps of quotients and their `Proj`

A graded ring map `f : 𝒜 →+*ᵍ ℬ` with `f(I) ⊆ J` for homogeneous ideals `I` of `𝒜` and `J` of `ℬ`
induces a graded ring map `A ⧸ I → B ⧸ J` on the quotient gradings (`ProjQuotient.quotMap`),
`a mod I ↦ f a mod J`. It commutes with the quotient maps (`quotMap_comp_mkGraded`). When `f`
meets the hypothesis of `Proj.map`, so does `quotMap f` (`irrelevant_le_map_quotMap`), and the
square of schemes
```
Proj (B ⧸ J) ⟶ Proj (A ⧸ I)
     |                |
  Proj B      ⟶   Proj A
```
commutes (`projQuotMap_quotι`). For an endomorphism `f` of `𝒜` preserving `I`, this is how a
graded substitution preserving the equation of a projective hypersurface induces an endomorphism
of the hypersurface; `Proj.map` reverses the order of composition.

## Main definitions

* `HodgeLadder.ProjQuotient.quotMap`, `projQuotMap`

## Main results

* `HodgeLadder.ProjQuotient.quotMap_mk`, `quotMap_comp_mkGraded`, `quotMap_ext`, `quotMap_comp`,
  `quotMap_id`
* `HodgeLadder.ProjQuotient.irrelevant_le_comap`, `irrelevant_le_map_quotMap`
* `HodgeLadder.ProjQuotient.projQuotMap_quotι`, `projQuotMap_congr`, `projQuotMap_comp`,
  `projQuotMap_id`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HodgeLadder.ProjQuotient

universe u

section Irrelevant

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A graded ring map sends the irrelevant ideal into the irrelevant ideal. -/
theorem irrelevant_le_comap (g : 𝒜 →+*ᵍ ℬ) :
    HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).comap g := by
  change (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ _
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi a ha
  exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hi (GradedFunLike.map_mem g ha)

end Irrelevant

variable {R A B : Type u} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {I : HomogeneousIdeal 𝒜} {J : HomogeneousIdeal ℬ}

/-- **The induced map of quotients.** A graded ring map `f` with `f(I) ⊆ J` induces the graded
ring map `A ⧸ I → B ⧸ J`, `a mod I ↦ f a mod J`, on the quotient gradings. -/
def quotMap (f : 𝒜 →+*ᵍ ℬ) (hIJ : I.toIdeal ≤ J.toIdeal.comap (f : A →+* B)) :
    grading 𝒜 I →+*ᵍ grading ℬ J where
  toRingHom := Ideal.quotientMap J.toIdeal (f : A →+* B) hIJ
  map_mem {i q} hq := by
    obtain ⟨a, ha, rfl⟩ := (mem_grading_iff 𝒜 I).mp hq
    change Ideal.quotientMap J.toIdeal (f : A →+* B) hIJ (Ideal.Quotient.mk I.toIdeal a) ∈ _
    rw [Ideal.quotientMap_mk]
    exact mk_mem_grading ℬ J (GradedFunLike.map_mem f ha)

/-- `quotMap f` sends the class of `a` to the class of `f a`. -/
@[simp]
theorem quotMap_mk (f : 𝒜 →+*ᵍ ℬ) (hIJ : I.toIdeal ≤ J.toIdeal.comap (f : A →+* B)) (a : A) :
    quotMap f hIJ (Ideal.Quotient.mk I.toIdeal a) = Ideal.Quotient.mk J.toIdeal (f a) :=
  Ideal.quotientMap_mk (H := hIJ)

/-- **The quotient square of graded maps**: `quotMap f ∘ (A → A ⧸ I) = (B → B ⧸ J) ∘ f`. -/
theorem quotMap_comp_mkGraded (f : 𝒜 →+*ᵍ ℬ) (hIJ : I.toIdeal ≤ J.toIdeal.comap (f : A →+* B)) :
    (quotMap f hIJ).comp (mkGraded 𝒜 I) = (mkGraded ℬ J).comp f := by
  ext a
  exact quotMap_mk f hIJ a

/-- Two graded maps of quotients agree when they agree on classes. -/
theorem quotMap_ext {g h : grading 𝒜 I →+*ᵍ grading ℬ J}
    (hgh : ∀ a : A, g (Ideal.Quotient.mk I.toIdeal a) = h (Ideal.Quotient.mk I.toIdeal a)) :
    g = h := by
  ext q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact hgh a

/-- `quotMap` of a composite is the composite of the `quotMap`s. -/
theorem quotMap_comp {C : Type u} [CommRing C] [Algebra R C] {𝒞 : ℕ → Submodule R C}
    [GradedAlgebra 𝒞] {K : HomogeneousIdeal 𝒞} (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
    (hIJ : I.toIdeal ≤ J.toIdeal.comap (f : A →+* B))
    (hJK : J.toIdeal ≤ K.toIdeal.comap (g : B →+* C))
    (hIK : I.toIdeal ≤ K.toIdeal.comap ((g.comp f : 𝒜 →+*ᵍ 𝒞) : A →+* C)) :
    quotMap (g.comp f) hIK = (quotMap g hJK).comp (quotMap f hIJ) :=
  quotMap_ext fun a => by
    rw [GradedRingHom.comp_apply, quotMap_mk, quotMap_mk, quotMap_mk, GradedRingHom.comp_apply]

/-- `quotMap` of the identity is the identity. -/
theorem quotMap_id (hII : I.toIdeal ≤ I.toIdeal.comap ((GradedRingHom.id 𝒜 : 𝒜 →+*ᵍ 𝒜) : A →+* A)) :
    quotMap (GradedRingHom.id 𝒜) hII = GradedRingHom.id (grading 𝒜 I) :=
  quotMap_ext fun a => by rw [quotMap_mk, GradedRingHom.id_apply, GradedRingHom.id_apply]

/-- If `f` meets the hypothesis of `Proj.map`, so does `quotMap f`. -/
theorem irrelevant_le_map_quotMap (f : 𝒜 →+*ᵍ ℬ) (hIJ : I.toIdeal ≤ J.toIdeal.comap (f : A →+* B))
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    HomogeneousIdeal.irrelevant (grading ℬ J) ≤
      (HomogeneousIdeal.irrelevant (grading 𝒜 I)).map (quotMap f hIJ) := by
  calc HomogeneousIdeal.irrelevant (grading ℬ J)
      ≤ (HomogeneousIdeal.irrelevant ℬ).map (mkGraded ℬ J) :=
        irrelevant_le_map _ (mkGraded_surjOn ℬ J)
    _ ≤ ((HomogeneousIdeal.irrelevant 𝒜).map f).map (mkGraded ℬ J) :=
        HomogeneousIdeal.map_mono _ hf
    _ = ((HomogeneousIdeal.irrelevant 𝒜).map (mkGraded 𝒜 I)).map (quotMap f hIJ) := by
        rw [HomogeneousIdeal.map_map, HomogeneousIdeal.map_map, quotMap_comp_mkGraded]
    _ ≤ (HomogeneousIdeal.irrelevant (grading 𝒜 I)).map (quotMap f hIJ) :=
        HomogeneousIdeal.map_mono _
          (HomogeneousIdeal.map_le_of_le_comap _ (irrelevant_le_comap _))

/-- **The induced morphism of closed subschemes** `Proj (B ⧸ J) ⟶ Proj (A ⧸ I)`, `Proj.map` of
`quotMap f`. -/
def projQuotMap (f : 𝒜 →+*ᵍ ℬ) (hIJ : I.toIdeal ≤ J.toIdeal.comap (f : A →+* B))
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj (grading ℬ J) ⟶ Proj (grading 𝒜 I) :=
  Proj.map (quotMap f hIJ) (irrelevant_le_map_quotMap f hIJ hf)

/-- **The square against the closed immersions**:
`projQuotMap f ≫ (Proj (A ⧸ I) ⟶ Proj A) = (Proj (B ⧸ J) ⟶ Proj B) ≫ Proj.map f`. -/
@[reassoc]
theorem projQuotMap_quotι (f : 𝒜 →+*ᵍ ℬ) (hIJ : I.toIdeal ≤ J.toIdeal.comap (f : A →+* B))
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    projQuotMap f hIJ hf ≫ quotι 𝒜 I = quotι ℬ J ≫ Proj.map f hf := by
  rw [projQuotMap, quotι, quotι, ← Proj.map_comp, ← Proj.map_comp]
  congr 1

/-- `projQuotMap` depends only on the graded map. -/
theorem projQuotMap_congr {f g : 𝒜 →+*ᵍ ℬ} (hfg : f = g)
    (hIJ : I.toIdeal ≤ J.toIdeal.comap (f : A →+* B))
    (hIJ' : I.toIdeal ≤ J.toIdeal.comap (g : A →+* B))
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    projQuotMap f hIJ hf = projQuotMap g hIJ' hg := by
  subst hfg
  rfl

/-- **`projQuotMap` reverses composition**, as `Proj.map` does:
`projQuotMap (g ∘ f) = projQuotMap g ≫ projQuotMap f`. -/
theorem projQuotMap_comp {C : Type u} [CommRing C] [Algebra R C] {𝒞 : ℕ → Submodule R C}
    [GradedAlgebra 𝒞] {K : HomogeneousIdeal 𝒞} (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
    (hIJ : I.toIdeal ≤ J.toIdeal.comap (f : A →+* B))
    (hJK : J.toIdeal ≤ K.toIdeal.comap (g : B →+* C))
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map g) :
    projQuotMap (g.comp f) (hIJ.trans (Ideal.comap_mono hJK))
        (HomogeneousIdeal.irrelevant_le_map_comp hf hg) =
      projQuotMap g hJK hg ≫ projQuotMap f hIJ hf := by
  rw [projQuotMap, projQuotMap, projQuotMap, ← Proj.map_comp]
  congr 1
  exact quotMap_comp f g hIJ hJK _

/-- `projQuotMap` of the identity is the identity. -/
theorem projQuotMap_id
    (hII : I.toIdeal ≤ I.toIdeal.comap ((GradedRingHom.id 𝒜 : 𝒜 →+*ᵍ 𝒜) : A →+* A))
    (hid : HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant 𝒜).map (GradedRingHom.id 𝒜)) :
    projQuotMap (GradedRingHom.id 𝒜) hII hid = 𝟙 (Proj (grading 𝒜 I)) := by
  rw [projQuotMap, ← Proj.map_id]
  congr 1
  exact quotMap_id hII

end HodgeLadder.ProjQuotient
