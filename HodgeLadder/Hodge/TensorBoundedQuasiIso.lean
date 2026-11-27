module

public import HodgeLadder.Hodge.CupFiltration
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Tensoring with a bounded complex preserves quasi-isomorphisms

Rung `tensor-bounded-quasi-iso` (front `cup`, decision 0009, item 8): the `Prop`
`HodgeLadder.TensorBoundedQuasiIso` of `HodgeLadder.Hodge.CupFiltration` holds.

The proof works for a bifunctor `F : C₁ ⥤ C₂ ⥤ D` between abelian categories, additive in each
variable, with `F(−, X)` preserving homology for every `X` and `D` having coproducts; Mathlib's
tensor product of complexes is `mapBifunctor` for `F = curriedTensor`. Route (red team finding 7
of `docs/sketches/cup-hodge-filtration.redteam.md`):

* single case: for `M = X[−a]`, `mapBifunctor K M F ≅ F(K, X)⟦−a⟧` naturally in `K`
  (`singleComparison`), and `F(−, X)` preserves quasi-isomorphisms;
* induction on the length of `M`: the degreewise split short exact sequence
  `0 → ker → M → M^a[−a] → 0` (`bottomSES`), with `a` the lowest degree, stays degreewise
  split, hence short exact, after `mapBifunctor K − F`, naturally in `K`
  (`mapBifunctorShortComplex_shortExact`); two out of three for the middle term
  (`quasiIso_τ₂_of_shortExact`) closes the step.

For sheaves of `ℚ`-vector spaces, `F(−, X) = − ⊗ X` is exact by `HodgeLadder.Cup.tensor_exact`.

## Main definitions

* `HodgeLadder.singleComparison`, `HodgeLadder.mapBifunctorShortComplex`,
  `HodgeLadder.toSingleBottom`, `HodgeLadder.bottomSES`

## Main results

* `HodgeLadder.tensorBoundedQuasiIso_holds : HodgeLadder.TensorBoundedQuasiIso`
* `HodgeLadder.quasiIso_mapBifunctorMap_of_bounded`: the same for any bifunctor as above
* `HodgeLadder.quasiIso_τ₂_of_shortExact`: two out of three for the middle term of a morphism of
  short exact sequences of cochain complexes
-/

@[expose] public noncomputable section

open CategoryTheory Limits ComposableArrows Abelian

namespace HodgeLadder

section FiveLemma

variable {C : Type*} [Category* C] [Abelian C]

/-- **Two out of three, middle term.** A morphism of short exact sequences of `ℤ`-indexed
cochain complexes whose outer components are quasi-isomorphisms has a quasi-isomorphism as middle
component. Five lemma on the long exact homology sequences (Mathlib states the third-term case,
`HomologicalComplex.HomologySequence.quasiIso_τ₃`). -/
theorem quasiIso_τ₂_of_shortExact {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) [QuasiIso φ.τ₁] [QuasiIso φ.τ₃] :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (HomologicalComplex.homologyMap φ.τ₂ j) := by
    apply mono_of_epi_of_mono_of_mono ((δ₀Functor ⋙ δ₀Functor).map
      (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ (j - 1) j (by simp)))
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ _ _ _).δ₀.δ₀
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ _ _ _).δ₀.δ₀
    · exact (inferInstance : Epi (HomologicalComplex.homologyMap φ.τ₃ (j - 1)))
    · exact (inferInstance : Mono (HomologicalComplex.homologyMap φ.τ₁ j))
    · exact (inferInstance : Mono (HomologicalComplex.homologyMap φ.τ₃ j))
  have he : Epi (HomologicalComplex.homologyMap φ.τ₂ j) := by
    apply epi_of_epi_of_epi_of_mono ((δlastFunctor ⋙ δlastFunctor).map
      (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ j (j + 1) (by simp)))
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ _ _ _).δlast.δlast
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ _ _ _).δlast.δlast
    · exact (inferInstance : Epi (HomologicalComplex.homologyMap φ.τ₁ j))
    · exact (inferInstance : Epi (HomologicalComplex.homologyMap φ.τ₃ j))
    · exact (inferInstance : Mono (HomologicalComplex.homologyMap φ.τ₁ (j + 1)))
  exact isIso_of_mono_of_epi _

end FiveLemma

section Bifunctor

open HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Abelian C₁] [Abelian C₂] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]

/-- `mapBifunctorMap` is compatible with composition in both variables. -/
theorem mapBifunctorMap_comp' {K₁ L₁ M₁ : CochainComplex C₁ ℤ} {K₂ L₂ M₂ : CochainComplex C₂ ℤ}
    (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂)
    [HasMapBifunctor K₁ K₂ F (.up ℤ)] [HasMapBifunctor L₁ L₂ F (.up ℤ)]
    [HasMapBifunctor M₁ M₂ F (.up ℤ)] :
    mapBifunctorMap f₁ f₂ F (.up ℤ) ≫ mapBifunctorMap g₁ g₂ F (.up ℤ) =
      mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂) F (.up ℤ) := by
  ext n i j h
  simp only [HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc, ι_mapBifunctorMap,
    Functor.map_comp, NatTrans.comp_app, Category.assoc]
  simp only [NatTrans.naturality_assoc]

/-- `mapBifunctorMap` sends identities to the identity. -/
theorem mapBifunctorMap_id' (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ)
    [HasMapBifunctor K₁ K₂ F (.up ℤ)] :
    mapBifunctorMap (𝟙 K₁) (𝟙 K₂) F (.up ℤ) = 𝟙 _ := by
  ext n i j h
  simp

/-- If `M` is zero outside degree `a`, the inclusion of the summand `F(K^i, M^a)` into
`(mapBifunctor K M F).X (i + a)` is an isomorphism. -/
theorem isIso_ιMapBifunctor_of_isZero (K : CochainComplex C₁ ℤ) (M : CochainComplex C₂ ℤ)
    [HasMapBifunctor K M F (.up ℤ)] (a : ℤ) (hM : ∀ j, j ≠ a → IsZero (M.X j)) (i n : ℤ)
    (h : i + a = n) : IsIso (ιMapBifunctor K M F (.up ℤ) i a n h) := by
  classical
  refine ⟨mapBifunctorDesc (fun i' j' h' => if hj : j' = a then
      (F.map (K.XIsoOfEq (show i' = i by subst hj; simp at h'; omega)).hom).app _ ≫
        (F.obj _).map (M.XIsoOfEq hj).hom else 0), ?_, ?_⟩
  · simp
  · ext i' j' h'
    by_cases hj : j' = a
    · subst hj
      obtain rfl : i' = i := by simp at h'; omega
      simp
    · exact ((F.obj _).map_isZero (hM j' hj)).eq_of_src _ _

/-- The comparison map `(F(K, X))[−a] ⟶ mapBifunctor K (X[−a]) F`, natural in `K`, where
`F(K, X)` is `K` with `F(−, X)` applied termwise and `X[−a]` is `X` placed in degree `a`. In
degree `n` it is `(−1)^{na}` times the inclusion of the summand `F(K^{n−a}, X)`; the sign makes
it commute with the differentials, since Mathlib's shift `⟦−a⟧` multiplies the differential by
`(−1)^a` and the first differential of `mapBifunctor` carries no sign (`ComplexShape.ε₁ = 1`).
The sign plays no role in the quasi-isomorphism statements below. -/
def singleComparison (K : CochainComplex C₁ ℤ) (X : C₂) (a : ℤ)
    [HasMapBifunctor K ((single C₂ (.up ℤ) a).obj X) F (.up ℤ)] :
    (((F.flip.obj X).mapHomologicalComplex (.up ℤ)).obj K)⟦-a⟧ ⟶
      mapBifunctor K ((single C₂ (.up ℤ) a).obj X) F (.up ℤ) where
  f n := (n * a).negOnePow • ((F.obj (K.X (n + -a))).map (singleObjXSelf (.up ℤ) a X).inv ≫
      ιMapBifunctor K _ F (.up ℤ) (n + -a) a n (by simp))
  comm' n m hnm := by
    simp only [ComplexShape.up_Rel] at hnm
    subst hnm
    rw [mapBifunctor.d_eq]
    simp only [Preadditive.comp_add, Linear.units_smul_comp, Category.assoc, mapBifunctor.ι_D₁,
      mapBifunctor.ι_D₂]
    rw [mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel (n + -a) (n + 1 + -a) by
        simp; omega) _ _ (by simp),
      mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel a (a + 1) by simp) _
        (by simp)]
    simp
    rw [smul_smul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-a, by ring⟩

/-- A sign times an isomorphism is an isomorphism. -/
theorem isIso_units_smul {X Y : D} (u : ℤˣ) (g : X ⟶ Y) [IsIso g] : IsIso (u • g) :=
  ⟨u • inv g, by simp [smul_smul], by simp [smul_smul]⟩

/-- The comparison map is an isomorphism. -/
theorem isIso_singleComparison (K : CochainComplex C₁ ℤ) (X : C₂) (a : ℤ)
    [HasMapBifunctor K ((single C₂ (.up ℤ) a).obj X) F (.up ℤ)] :
    IsIso (singleComparison F K X a) := by
  have (n : ℤ) : IsIso ((singleComparison F K X a).f n) := by
    have := isIso_ιMapBifunctor_of_isZero F K ((single C₂ (.up ℤ) a).obj X) a
      (fun j hj => isZero_single_obj_X _ _ _ _ hj) (n + -a) n (by omega)
    exact isIso_units_smul _ _
  apply HomologicalComplex.Hom.isIso_of_components

/-- The comparison map is natural in `K`. -/
theorem singleComparison_naturality {K L : CochainComplex C₁ ℤ} (f : K ⟶ L) (X : C₂) (a : ℤ)
    [HasMapBifunctor K ((single C₂ (.up ℤ) a).obj X) F (.up ℤ)]
    [HasMapBifunctor L ((single C₂ (.up ℤ) a).obj X) F (.up ℤ)] :
    singleComparison F K X a ≫ mapBifunctorMap f (𝟙 _) F (.up ℤ) =
      (((F.flip.obj X).mapHomologicalComplex (.up ℤ)).map f)⟦-a⟧' ≫
        singleComparison F L X a := by
  ext n
  simp [singleComparison]

/-- **Single case.** If each `F(−, X)` preserves homology, then `F(f, 𝟙)` with a complex
concentrated in one degree preserves quasi-isomorphisms. -/
theorem quasiIso_mapBifunctorMap_single [∀ X, (F.flip.obj X).PreservesHomology]
    {K L : CochainComplex C₁ ℤ} (f : K ⟶ L) [QuasiIso f] (X : C₂) (a : ℤ)
    [HasMapBifunctor K ((single C₂ (.up ℤ) a).obj X) F (.up ℤ)]
    [HasMapBifunctor L ((single C₂ (.up ℤ) a).obj X) F (.up ℤ)] :
    QuasiIso (mapBifunctorMap f (𝟙 ((single C₂ (.up ℤ) a).obj X)) F (.up ℤ)) := by
  have := isIso_singleComparison F K X a
  have := isIso_singleComparison F L X a
  have : (F.flip.obj X).Additive := ⟨fun {_ _ g h} => by simp⟩
  have h₁ : QuasiIso (((F.flip.obj X).mapHomologicalComplex (.up ℤ)).map f) := inferInstance
  have hq : QuasiIso ((((F.flip.obj X).mapHomologicalComplex (.up ℤ)).map f)⟦-a⟧') :=
    (CochainComplex.quasiIso_shift_iff _ _).2 h₁
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (asIso (singleComparison F K X a))
    (asIso (singleComparison F L X a)) (singleComparison_naturality F f X a))).1 hq

/-- Whether `F(f, 𝟙_M)` is a quasi-isomorphism depends on `M` only up to isomorphism. -/
theorem quasiIso_mapBifunctorMap_iff_of_iso {K L : CochainComplex C₁ ℤ} (f : K ⟶ L)
    {M M' : CochainComplex C₂ ℤ} (e : M ≅ M')
    [HasMapBifunctor K M F (.up ℤ)] [HasMapBifunctor L M F (.up ℤ)]
    [HasMapBifunctor K M' F (.up ℤ)] [HasMapBifunctor L M' F (.up ℤ)] :
    QuasiIso (mapBifunctorMap f (𝟙 M) F (.up ℤ)) ↔
      QuasiIso (mapBifunctorMap f (𝟙 M') F (.up ℤ)) := by
  let eK : mapBifunctor K M F (.up ℤ) ≅ mapBifunctor K M' F (.up ℤ) :=
    { hom := mapBifunctorMap (𝟙 K) e.hom F (.up ℤ)
      inv := mapBifunctorMap (𝟙 K) e.inv F (.up ℤ)
      hom_inv_id := by simp [mapBifunctorMap_comp', mapBifunctorMap_id']
      inv_hom_id := by simp [mapBifunctorMap_comp', mapBifunctorMap_id'] }
  let eL : mapBifunctor L M F (.up ℤ) ≅ mapBifunctor L M' F (.up ℤ) :=
    { hom := mapBifunctorMap (𝟙 L) e.hom F (.up ℤ)
      inv := mapBifunctorMap (𝟙 L) e.inv F (.up ℤ)
      hom_inv_id := by simp [mapBifunctorMap_comp', mapBifunctorMap_id']
      inv_hom_id := by simp [mapBifunctorMap_comp', mapBifunctorMap_id'] }
  exact quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk eK eL
    (by
      dsimp only [eK, eL, Arrow.mk_hom]
      rw [mapBifunctorMap_comp', mapBifunctorMap_comp']
      simp
      rfl))

/-- Tensoring a short complex of complexes on the right. -/
def mapBifunctorShortComplex (K : CochainComplex C₁ ℤ) (S : ShortComplex (CochainComplex C₂ ℤ))
    [HasMapBifunctor K S.X₁ F (.up ℤ)] [HasMapBifunctor K S.X₂ F (.up ℤ)]
    [HasMapBifunctor K S.X₃ F (.up ℤ)] : ShortComplex (CochainComplex D ℤ) :=
  ShortComplex.mk (mapBifunctorMap (𝟙 K) S.f F (.up ℤ)) (mapBifunctorMap (𝟙 K) S.g F (.up ℤ))
    (by rw [mapBifunctorMap_comp', S.zero]; ext; simp)

/-- A degreewise split short exact sequence stays short exact after tensoring. -/
theorem mapBifunctorShortComplex_shortExact (K : CochainComplex C₁ ℤ)
    (S : ShortComplex (CochainComplex C₂ ℤ))
    [HasMapBifunctor K S.X₁ F (.up ℤ)] [HasMapBifunctor K S.X₂ F (.up ℤ)]
    [HasMapBifunctor K S.X₃ F (.up ℤ)]
    (σ : ∀ j, (S.map (HomologicalComplex.eval C₂ (.up ℤ) j)).Splitting) :
    (mapBifunctorShortComplex F K S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let T : ShortComplex D := ShortComplex.mk ((mapBifunctorMap (𝟙 K) S.f F (.up ℤ)).f n)
    ((mapBifunctorMap (𝟙 K) S.g F (.up ℤ)).f n)
    (by rw [← HomologicalComplex.comp_f]
        exact HomologicalComplex.congr_hom (mapBifunctorShortComplex F K S).zero n)
  let τ : T.Splitting :=
    { r := mapBifunctorDesc (fun i j h =>
        (F.obj (K.X i)).map (σ j).r ≫ ιMapBifunctor K S.X₁ F _ i j n h)
      s := mapBifunctorDesc (fun i j h =>
        (F.obj (K.X i)).map (σ j).s ≫ ιMapBifunctor K S.X₂ F _ i j n h)
      f_r := by
        refine mapBifunctor.hom_ext (fun i j h => ?_)
        have := (σ j).f_r
        dsimp at this
        simp [T, ← Functor.map_comp_assoc, this]
      s_g := by
        refine mapBifunctor.hom_ext (fun i j h => ?_)
        have := (σ j).s_g
        dsimp at this
        simp [T, ← Functor.map_comp_assoc, this]
      id := by
        refine mapBifunctor.hom_ext (fun i j h => ?_)
        have := (σ j).id
        dsimp at this
        simp only [T]
        simp
        rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Preadditive.add_comp,
          ← Functor.map_add, this, CategoryTheory.Functor.map_id, Category.id_comp] }
  exact τ.shortExact

/-- Two out of three for tensoring a degreewise split short exact sequence. -/
theorem quasiIso_mapBifunctorMap_of_splitting {K L : CochainComplex C₁ ℤ} (f : K ⟶ L)
    (S : ShortComplex (CochainComplex C₂ ℤ))
    [HasMapBifunctor K S.X₁ F (.up ℤ)] [HasMapBifunctor K S.X₂ F (.up ℤ)]
    [HasMapBifunctor K S.X₃ F (.up ℤ)]
    [HasMapBifunctor L S.X₁ F (.up ℤ)] [HasMapBifunctor L S.X₂ F (.up ℤ)]
    [HasMapBifunctor L S.X₃ F (.up ℤ)]
    (σ : ∀ j, (S.map (HomologicalComplex.eval C₂ (.up ℤ) j)).Splitting)
    (h₁ : QuasiIso (mapBifunctorMap f (𝟙 S.X₁) F (.up ℤ)))
    (h₃ : QuasiIso (mapBifunctorMap f (𝟙 S.X₃) F (.up ℤ))) :
    QuasiIso (mapBifunctorMap f (𝟙 S.X₂) F (.up ℤ)) := by
  let φ : mapBifunctorShortComplex F K S ⟶ mapBifunctorShortComplex F L S :=
    { τ₁ := mapBifunctorMap f (𝟙 S.X₁) F (.up ℤ)
      τ₂ := mapBifunctorMap f (𝟙 S.X₂) F (.up ℤ)
      τ₃ := mapBifunctorMap f (𝟙 S.X₃) F (.up ℤ)
      comm₁₂ := by
        dsimp only [mapBifunctorShortComplex]
        rw [mapBifunctorMap_comp', mapBifunctorMap_comp']
        simp
      comm₂₃ := by
        dsimp only [mapBifunctorShortComplex]
        rw [mapBifunctorMap_comp', mapBifunctorMap_comp']
        simp }
  have : QuasiIso φ.τ₁ := h₁
  have : QuasiIso φ.τ₃ := h₃
  exact quasiIso_τ₂_of_shortExact φ (mapBifunctorShortComplex_shortExact F K S σ)
    (mapBifunctorShortComplex_shortExact F L S σ)

end Bifunctor

section Bottom

open HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- A short exact sequence with zero third term splits. -/
def splittingOfIsZeroX₃ {S : ShortComplex C} (hS : S.ShortExact) (h : IsZero S.X₃) :
    S.Splitting :=
  ShortComplex.Splitting.ofIsIsoOfIsZero S (by
    have := hS.mono_f
    have := hS.exact.epi_f (h.eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _) h

/-- In a short exact sequence with invertible second map, the first term is zero. -/
theorem isZero_X₁_of_isIso_g {S : ShortComplex C} (hS : S.ShortExact) (h : IsIso S.g) :
    IsZero S.X₁ := by
  have := hS.mono_f
  have hf : S.f = 0 := by rw [← cancel_mono S.g, S.zero, zero_comp]
  exact IsZero.of_mono_eq_zero _ hf

/-- A short exact sequence with invertible second map splits. -/
def splittingOfIsIsoG {S : ShortComplex C} (hS : S.ShortExact) (h : IsIso S.g) : S.Splitting :=
  ShortComplex.Splitting.ofIsZeroOfIsIso S (isZero_X₁_of_isIso_g hS h) h

/-- The projection of a complex concentrated in degrees `≥ a` onto its degree `a` term. -/
def toSingleBottom (M : CochainComplex C ℤ) (a : ℤ) [M.IsStrictlyGE a] :
    M ⟶ (single C (.up ℤ) a).obj (M.X a) :=
  mkHomToSingle (𝟙 _) (fun i hi => by
    simp only [ComplexShape.up_Rel] at hi
    exact (M.isZero_of_isStrictlyGE a i (by omega)).eq_of_src _ _)

/-- `toSingleBottom` is an isomorphism in degree `a`. -/
theorem isIso_toSingleBottom_f_self (M : CochainComplex C ℤ) (a : ℤ) [M.IsStrictlyGE a] :
    IsIso ((toSingleBottom M a).f a) := by
  rw [toSingleBottom, mkHomToSingle_f]
  infer_instance

/-- `toSingleBottom` is an epimorphism of complexes. -/
instance toSingleBottom_epi (M : CochainComplex C ℤ) (a : ℤ) [M.IsStrictlyGE a] :
    Epi (toSingleBottom M a) := by
  apply epi_of_epi_f
  intro j
  by_cases hj : j = a
  · subst hj
    have := isIso_toSingleBottom_f_self M j
    infer_instance
  · exact (isZero_single_obj_X _ _ _ _ hj).epi _

/-- The short exact sequence `0 → ker → M → M^a[−a] → 0`. -/
abbrev bottomSES (M : CochainComplex C ℤ) (a : ℤ) [M.IsStrictlyGE a] :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (kernel.ι (toSingleBottom M a)) (toSingleBottom M a) (kernel.condition _)

/-- `bottomSES` is short exact. -/
theorem bottomSES_shortExact (M : CochainComplex C ℤ) (a : ℤ) [M.IsStrictlyGE a] :
    (bottomSES M a).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

/-- `bottomSES` is short exact in each degree. -/
theorem bottomSES_shortExact_eval (M : CochainComplex C ℤ) (a : ℤ) [M.IsStrictlyGE a] (j : ℤ) :
    ((bottomSES M a).map (eval C (.up ℤ) j)).ShortExact :=
  (shortExact_iff_degreewise_shortExact _).1 (bottomSES_shortExact M a) j

/-- The degreewise splitting of `bottomSES`. -/
def bottomSESSplitting (M : CochainComplex C ℤ) (a : ℤ) [M.IsStrictlyGE a] (j : ℤ) :
    ((bottomSES M a).map (eval C (.up ℤ) j)).Splitting := by
  by_cases hj : j = a
  · subst hj
    exact splittingOfIsIsoG (bottomSES_shortExact_eval M j j) (isIso_toSingleBottom_f_self M j)
  · exact splittingOfIsZeroX₃ (bottomSES_shortExact_eval M a j)
      (isZero_single_obj_X (.up ℤ) _ _ _ hj)

/-- The kernel of `toSingleBottom` vanishes in degree `a` and wherever `M` does. -/
theorem isZero_kernel_toSingleBottom_X (M : CochainComplex C ℤ) (a : ℤ) [M.IsStrictlyGE a]
    (j : ℤ) (hj : j = a ∨ IsZero (M.X j)) : IsZero ((kernel (toSingleBottom M a)).X j) := by
  have hS := bottomSES_shortExact_eval M a j
  rcases hj with hj | hj
  · subst hj
    exact isZero_X₁_of_isIso_g hS (isIso_toSingleBottom_f_self M j)
  · have := hS.mono_f
    exact IsZero.of_mono ((bottomSES M a).map (eval C (.up ℤ) j)).f hj

/-- The kernel of `toSingleBottom` is concentrated in degrees `≥ a + 1`. -/
instance kernel_toSingleBottom_isStrictlyGE (M : CochainComplex C ℤ) (a : ℤ) [M.IsStrictlyGE a] :
    (kernel (toSingleBottom M a)).IsStrictlyGE (a + 1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  apply isZero_kernel_toSingleBottom_X
  by_cases h : i = a
  · exact Or.inl h
  · exact Or.inr (M.isZero_of_isStrictlyGE a i (by omega))

/-- The kernel of `toSingleBottom` is concentrated in degrees `≤ b` when `M` is. -/
instance kernel_toSingleBottom_isStrictlyLE (M : CochainComplex C ℤ) (a b : ℤ)
    [M.IsStrictlyGE a] [M.IsStrictlyLE b] :
    (kernel (toSingleBottom M a)).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact isZero_kernel_toSingleBottom_X M a i (Or.inr (M.isZero_of_isStrictlyLE b i hi))

end Bottom

section Main

open HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Abelian C₁] [Abelian C₂] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ X, (F.flip.obj X).PreservesHomology] [HasCoproducts.{0} D]

/-- Induction on the length: for `M` concentrated in `[a, a + n]`, `F(f, 𝟙_M)` is a
quasi-isomorphism whenever `f` is one. -/
theorem quasiIso_mapBifunctorMap_of_length (n : ℕ) : ∀ (a : ℤ) (M : CochainComplex C₂ ℤ)
    [M.IsStrictlyGE a] [M.IsStrictlyLE (a + n)] {K L : CochainComplex C₁ ℤ} (f : K ⟶ L)
    [QuasiIso f], QuasiIso (mapBifunctorMap f (𝟙 M) F (.up ℤ)) := by
  induction n with
  | zero =>
    intro a M _ _ K L f _
    have : IsIso (toSingleBottom M a) := by
      have (j : ℤ) : IsIso ((toSingleBottom M a).f j) := by
        by_cases hj : j = a
        · subst hj
          exact isIso_toSingleBottom_f_self M j
        · have hM : IsZero (M.X j) := by
            rcases lt_or_gt_of_ne hj with h | h
            · exact M.isZero_of_isStrictlyGE a j h
            · exact M.isZero_of_isStrictlyLE (a + ((0 : ℕ) : ℤ)) j (by omega)
          exact IsZero.isIso hM (isZero_single_obj_X (.up ℤ) _ _ _ hj) _
      apply HomologicalComplex.Hom.isIso_of_components
    rw [quasiIso_mapBifunctorMap_iff_of_iso F f (asIso (toSingleBottom M a))]
    exact quasiIso_mapBifunctorMap_single F f (M.X a) a
  | succ n ih =>
    intro a M _ _ K L f _
    have : (kernel (toSingleBottom M a)).IsStrictlyLE (a + 1 + n) :=
      CochainComplex.isStrictlyLE_of_le _ (a + ((n + 1 : ℕ) : ℤ)) _ (by omega)
    exact quasiIso_mapBifunctorMap_of_splitting F f (bottomSES M a) (bottomSESSplitting M a)
      (ih (a + 1) (kernel (toSingleBottom M a)) f) (quasiIso_mapBifunctorMap_single F f (M.X a) a)

/-- **Bounded case, any bifunctor.** If `F` is additive in each variable, each `F(−, X)`
preserves homology and the target has coproducts, then `F(f, 𝟙_M)` is a quasi-isomorphism for
every quasi-isomorphism `f` and every strictly bounded complex `M`. -/
theorem quasiIso_mapBifunctorMap_of_bounded {K L : CochainComplex C₁ ℤ} (f : K ⟶ L) [QuasiIso f]
    (M : CochainComplex C₂ ℤ) (a b : ℤ) [M.IsStrictlyGE a] [M.IsStrictlyLE b]
    [HasMapBifunctor K M F (.up ℤ)] [HasMapBifunctor L M F (.up ℤ)] :
    QuasiIso (mapBifunctorMap f (𝟙 M) F (.up ℤ)) := by
  have : M.IsStrictlyLE (a + ((b - a).toNat : ℤ)) :=
    CochainComplex.isStrictlyLE_of_le M b _ (by omega)
  exact quasiIso_mapBifunctorMap_of_length F (b - a).toNat a M f

end Main

section Sheaves

open MonoidalCategory Cup

attribute [local instance] sheafMonoidal

/-- **Tensoring with a bounded complex preserves quasi-isomorphisms** (rung
`tensor-bounded-quasi-iso`). For cochain complexes of sheaves of `ℚ`-vector spaces on `Y`, with
Mathlib's tensor product of complexes, `f ⊗ 𝟙_M` is a quasi-isomorphism when `f` is one and `M`
is strictly bounded. The input from sheaves is `tensor_exact` (tensoring on the right with a sheaf
is exact) and the existence of coproducts in `ShQ Y`. -/
theorem tensorBoundedQuasiIso_holds : TensorBoundedQuasiIso := by
  intro Y K L f _ M a b _ _ _ _
  have : HasCoproducts.{0} (ShQ Y) := fun K =>
    @Sheaf.instHasColimitsOfShape _ _ (J Y) _ _ (Discrete K) _ inferInstance inferInstance
  have (X : ShQ Y) : ((curriedTensor (ShQ Y)).flip.obj X).PreservesHomology := by
    let e : tensorRight X ≅ (curriedTensor (ShQ Y)).flip.obj X := Iso.refl _
    have : PreservesFiniteLimits ((curriedTensor (ShQ Y)).flip.obj X) :=
      preservesFiniteLimits_of_natIso e
    have : PreservesFiniteColimits ((curriedTensor (ShQ Y)).flip.obj X) :=
      preservesFiniteColimits_of_natIso e
    exact Functor.preservesHomologyOfExact _
  exact quasiIso_mapBifunctorMap_of_bounded (curriedTensor (ShQ Y)) f M a b

end Sheaves

end HodgeLadder
