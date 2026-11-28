module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Complex points of a product over `Spec ℂ`

Rung `complex-points-prod`, first half (input of `p1p1-fibres-transversal`, sketch
`docs/sketches/cycle-class-multiplicative.md`); the product charts are in
`HodgeLadder.Normalization.ProductChart`. For `X Y : Over (Spec ℂ)`, the product `X ⨯ Y` is
taken in `Over (Spec ℂ)`; its underlying scheme is the fibre product over `Spec ℂ`
(`isPullback_prod`). Upstream's complex points `ComplexPoint X = Point ℂ X` carry the analytic
topology `Point.analyticTopology`, glued from the affine charts. This file shows
`pointProdHomeomorph : ComplexPoint (X ⨯ Y) ≃ₜ ComplexPoint X × ComplexPoint Y`, with no
finiteness or smoothness hypothesis. The map is the pair of projections
`z ↦ (map prod.fst z, map prod.snd z)` (`pointProdHomeomorph_apply`, by `rfl`), so the
homeomorphism is pinned; its inverse is `prod.lift` (`pointProdHomeomorph_symm_apply`).

Literature: analytification commutes with fibre products [`Serre1956` §1 to §2, `SGA1` Exp. XII
§1; numbering unverified].

## Route

The forward map is continuous by upstream's `Point.continuous_map`. For the inverse, near a pair
of points choose affine opens `U₁ ⊆ X`, `U₂ ⊆ Y`; on `U₁(ℂ) × U₂(ℂ)` the inverse factors through
the product `U₁ ⨯ U₂`, which is affine. Its global sections are generated as a ring by those of
`U₁` and `U₂`, because Mathlib's `isPushout_appTop_of_isPullback` makes the square of global
sections a pushout (`closure_range_union_eq_top`). Continuity into an affine scheme is tested on
global sections (`continuous_of_isAffine`), and evaluation is a ring homomorphism.

## Two spellings of the product

Mathlib's global `CartesianMonoidalCategory (Over S)` gives a second product `X ⊗ Y`, with
`(X ⊗ Y).left = pullback X.hom Y.hom` by `rfl`; it is not defeq to `X ⨯ Y`.
`pointTensorHomeomorph` transports the homeomorphism to it through upstream's
`Point.isoMapHomeomorph`.

## Conventions

The first factor comes first, in the homeomorphism and in the relative dimension `d + e` of
`smoothOfRelativeDimension_prod`. No sign or conjugation enters. Conventions row "Complex points of
a product and product charts" in `docs/conventions.md`.

## Main definitions

* `HodgeLadder.ComplexPointProd.pointProdEquiv`, `HodgeLadder.ComplexPointProd.pointProdHomeomorph`
* `HodgeLadder.ComplexPointProd.pointTensorHomeomorph`: the same for `X ⊗ Y`.

## Main results

* `HodgeLadder.ComplexPointProd.pointProdHomeomorph_apply`,
  `HodgeLadder.ComplexPointProd.pointProdHomeomorph_symm_apply`: the pins.
* `HodgeLadder.ComplexPointProd.isPullback_prod`: the square of underlying schemes of `X ⨯ Y` is a
  pullback.
* `HodgeLadder.ComplexPointProd.pointTensorHomeomorph_apply`: the pin for `X ⊗ Y`.
* Instances `isAffine_prod`, `smoothOfRelativeDimension_prod`
  (`SmoothOfRelativeDimension (d + e) (X ⨯ Y).hom`), `smooth_prod` (`Smooth (X ⨯ Y).hom`).
* General lemmas: `closure_range_union_eq_top`, `continuous_of_isAffine`, `evaluate_top_appTop`,
  `evaluate_top_add`, `evaluate_top_mul`, `evaluate_top_neg`, `evaluate_top_one`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory Topology AlgebraicGeometry AlgebraicGeometry.Point
open AlgebraicGeometry.ComplexPoint

namespace HodgeLadder.ComplexPointProd

section General

/-- In a pushout square of commutative rings, the images of the two legs generate the corner as
a ring. -/
theorem closure_range_union_eq_top {R A B P : CommRingCat} {f : R ⟶ A} {g : R ⟶ B}
    {inl : A ⟶ P} {inr : B ⟶ P} (h : IsPushout f g inl inr) :
    Subring.closure (Set.range inl ∪ Set.range inr) = ⊤ := by
  set S := Subring.closure (Set.range inl ∪ Set.range inr)
  let i : CommRingCat.of S ⟶ P := CommRingCat.ofHom S.subtype
  let l : A ⟶ CommRingCat.of S := CommRingCat.ofHom (inl.hom.codRestrict S
    fun a ↦ Subring.subset_closure (Or.inl ⟨a, rfl⟩))
  let r : B ⟶ CommRingCat.of S := CommRingCat.ofHom (inr.hom.codRestrict S
    fun b ↦ Subring.subset_closure (Or.inr ⟨b, rfl⟩))
  have hl : l ≫ i = inl := rfl
  have hr : r ≫ i = inr := rfl
  have hw : f ≫ l = g ≫ r := by
    ext x
    exact congrArg (fun φ : R ⟶ P ↦ φ x) h.w
  have hid : h.desc l r hw ≫ i = 𝟙 P := h.hom_ext (by simp [hl]) (by simp [hr])
  refine eq_top_iff.mpr fun p _ ↦ ?_
  have := congrArg (fun φ : P ⟶ P ↦ φ p) hid
  simp only [CommRingCat.id_apply] at this
  rw [← this]
  exact ((h.desc l r hw) p).2

/-- Continuity of a map into the complex points of an affine scheme is tested on the evaluations
of global sections. -/
theorem continuous_of_isAffine {T : Over (Spec ↧ℂ)} [IsAffine T.left] {Z : Type*}
    [TopologicalSpace Z] {g : Z → ComplexPoint T}
    (hg : ∀ s : Γ(T.left, ⊤), Continuous fun z ↦ evaluate ⊤ s (g z)) : Continuous g := by
  rw [continuous_iff_analyticSubbasis]
  rintro W ⟨U, s, V, hV, rfl⟩
  apply isOpen_iff_forall_mem_open.mpr
  rintro z ⟨hzU, hzV⟩
  obtain ⟨f, hfU, hzf⟩ :=
    (isAffineOpen_top T.left).exists_basicOpen_le ⟨(g z).underlying, hzU⟩ trivial
  let t := T.left.presheaf.map (homOfLE hfU).op s
  obtain ⟨k, a, hka⟩ := exists_evaluate_affine_basicOpen_eq_div (X := T) f t
  have hmem : ∀ y, g y ∈ overOpen (T.left.basicOpen f) ↔ evaluate ⊤ f (g y) ≠ 0 :=
    fun y ↦ mem_overOpen_basicOpen_iff_evaluate_ne_zero (U := ⊤) f (g y) trivial
  let N : Set Z := {y | evaluate ⊤ f (g y) ≠ 0} ∩
    (fun y ↦ evaluate ⊤ a (g y) / evaluate ⊤ f (g y) ^ k) ⁻¹' V
  have hNopen : IsOpen N :=
    ((hg a).continuousOn.div ((hg f).pow k).continuousOn fun y hy ↦ pow_ne_zero k hy
      ).isOpen_inter_preimage (isOpen_ne_fun (hg f) continuous_const) hV
  have heq : ∀ y, g y ∈ overOpen (T.left.basicOpen f) →
      evaluate U s (g y) = evaluate ⊤ a (g y) / evaluate ⊤ f (g y) ^ k := fun y hy ↦ by
    rw [evaluate_res hfU s _ hy]; exact hka _ hy
  refine ⟨N, ?_, hNopen, ?_⟩
  · rintro y ⟨hyf, hyV⟩
    have hy : g y ∈ overOpen (T.left.basicOpen f) := (hmem y).mpr hyf
    exact ⟨hfU hy, by
      change evaluate U s (g y) ∈ V
      rw [heq y hy]; exact hyV⟩
  · refine ⟨(hmem z).mp hzf, ?_⟩
    change evaluate ⊤ a (g z) / evaluate ⊤ f (g z) ^ k ∈ V
    rw [← heq z hzf]; exact hzV

/-- Evaluation of a pulled-back global section is evaluation at the image point. -/
theorem evaluate_top_appTop {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) (s : Γ(Y.left, ⊤))
    (z : ComplexPoint X) :
    evaluate ⊤ (f.left.appTop s) z = evaluate ⊤ s (map f z) :=
  (evaluate_map f ⊤ s z).symm

/-- Evaluation of global sections at a complex point is additive. -/
theorem evaluate_top_add {T : Over (Spec ↧ℂ)} (s t : Γ(T.left, ⊤)) (z : ComplexPoint T) :
    evaluate ⊤ (s + t) z = evaluate ⊤ s z + evaluate ⊤ t z := by
  simp only [evaluate_top_eq_appTop, map_add]

/-- Evaluation of global sections at a complex point is multiplicative. -/
theorem evaluate_top_mul {T : Over (Spec ↧ℂ)} (s t : Γ(T.left, ⊤)) (z : ComplexPoint T) :
    evaluate ⊤ (s * t) z = evaluate ⊤ s z * evaluate ⊤ t z := by
  simp only [evaluate_top_eq_appTop, map_mul]

/-- Evaluation of global sections at a complex point commutes with negation. -/
theorem evaluate_top_neg {T : Over (Spec ↧ℂ)} (s : Γ(T.left, ⊤)) (z : ComplexPoint T) :
    evaluate ⊤ (-s) z = -evaluate ⊤ s z := by
  simp only [evaluate_top_eq_appTop, map_neg]

/-- Evaluation of the unit section at a complex point is `1`. -/
theorem evaluate_top_one {T : Over (Spec ↧ℂ)} (z : ComplexPoint T) :
    evaluate ⊤ (1 : Γ(T.left, ⊤)) z = 1 := by
  simp only [evaluate_top_eq_appTop, map_one]

end General

variable (X Y : Over (Spec ↧ℂ))

/-- The product square of `X ⨯ Y` in `Over (Spec ℂ)` is a pullback square of schemes. -/
theorem isPullback_prod :
    IsPullback (prod.fst : X ⨯ Y ⟶ X).left (prod.snd : X ⨯ Y ⟶ Y).left X.hom Y.hom :=
  Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd) (prodIsProd X Y)

/-- The product of two affine schemes over `Spec ℂ` is affine. -/
instance isAffine_prod [IsAffine X.left] [IsAffine Y.left] : IsAffine (X ⨯ Y).left :=
  IsAffine.of_isPullback (isPullback_prod X Y)

/-- Complex points of `X ⨯ Y` are pairs of complex points: the map is the pair of projections, its
inverse is `prod.lift`. -/
def pointProdEquiv : ComplexPoint (X ⨯ Y) ≃ ComplexPoint X × ComplexPoint Y where
  toFun z := (map prod.fst z, map prod.snd z)
  invFun p := prod.lift p.1 p.2
  left_inv z := by ext1 <;> simp [map]
  right_inv p := by simp [map]

/-- The affine case: for `X` and `Y` affine, `prod.lift` is continuous, because the global
sections of `X ⨯ Y` are generated by those of `X` and `Y` (`isPushout_appTop_of_isPullback`). -/
theorem continuous_pointProdEquiv_symm_of_isAffine [IsAffine X.left] [IsAffine Y.left] :
    Continuous (pointProdEquiv X Y).symm := by
  have hpush := isPushout_appTop_of_isPullback (isPullback_prod X Y)
  have hclos := closure_range_union_eq_top hpush
  apply continuous_of_isAffine
  intro s
  have hs : s ∈ Subring.closure (Set.range (prod.fst : X ⨯ Y ⟶ X).left.appTop ∪
      Set.range (prod.snd : X ⨯ Y ⟶ Y).left.appTop) := hclos ▸ Subring.mem_top s
  induction hs using Subring.closure_induction with
  | mem s hs =>
    rcases hs with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · simp only [evaluate_top_appTop]
      exact (continuous_evaluate_top x).comp (by simpa [pointProdEquiv, map] using continuous_fst)
    · simp only [evaluate_top_appTop]
      exact (continuous_evaluate_top y).comp (by simpa [pointProdEquiv, map] using continuous_snd)
  | zero => simpa [evaluate_top_eq_appTop] using continuous_const
  | one => simpa [evaluate_top_one] using continuous_const
  | add s t _ _ hs ht => simp only [evaluate_top_add]; exact hs.add ht
  | neg s _ hs => simp only [evaluate_top_neg]; exact hs.neg
  | mul s t _ _ hs ht => simp only [evaluate_top_mul]; exact hs.mul ht

/-- `prod.lift` is continuous on complex points: near a pair of points it factors through the
product of two affine opens. -/
theorem continuous_pointProdEquiv_symm : Continuous (pointProdEquiv X Y).symm := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a, b⟩
  obtain ⟨U₁, hU₁, ha, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := a.underlying) (U := ⊤) trivial
  obtain ⟨U₂, hU₂, hb, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := b.underlying) (U := ⊤) trivial
  let N : Set (ComplexPoint X × ComplexPoint Y) := overOpen U₁ ×ˢ overOpen U₂
  have hN : IsOpen N := (isOpen_overOpen U₁).prod (isOpen_overOpen U₂)
  refine ContinuousOn.continuousAt ?_ (hN.mem_nhds ⟨ha, hb⟩)
  rw [continuousOn_iff_continuous_domRestrict]
  have : IsAffine (openScheme X U₁).left := hU₁
  have : IsAffine (openScheme Y U₂).left := hU₂
  let φ : N → ComplexPoint (openScheme X U₁) × ComplexPoint (openScheme Y U₂) := fun q ↦
    ((openEquiv X U₁).symm ⟨q.1.1, q.2.1⟩, (openEquiv Y U₂).symm ⟨q.1.2, q.2.2⟩)
  have hφ : Continuous φ :=
    ((continuous_openEquiv_symm X U₁).comp
        ((continuous_fst.comp continuous_subtype_val).subtype_mk _)).prodMk
      ((continuous_openEquiv_symm Y U₂).comp
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  have key : N.domRestrict (pointProdEquiv X Y).symm =
      map (prod.map (openInclusion X U₁) (openInclusion Y U₂)) ∘
        (pointProdEquiv (openScheme X U₁) (openScheme Y U₂)).symm ∘ φ := by
    funext q
    have h1 := congrArg Subtype.val ((openEquiv X U₁).apply_symm_apply ⟨q.1.1, q.2.1⟩)
    have h2 := congrArg Subtype.val ((openEquiv Y U₂).apply_symm_apply ⟨q.1.2, q.2.2⟩)
    simp only [openEquiv_coe] at h1 h2
    apply prod.hom_ext
    · simp [pointProdEquiv, map, φ, Set.domRestrict] at h1 ⊢
      exact h1.symm
    · simp [pointProdEquiv, map, φ, Set.domRestrict] at h2 ⊢
      exact h2.symm
  rw [key]
  exact (continuous_map _).comp
    ((continuous_pointProdEquiv_symm_of_isAffine _ _).comp hφ)

/-- **Rung `complex-points-prod`, the homeomorphism.** Complex points of `X ⨯ Y` with the
analytic topology are homeomorphic to the product of the complex points of `X` and `Y`. The map is
the pair of projections (`pointProdHomeomorph_apply`); the inverse is `prod.lift`. No finiteness
hypothesis enters. -/
def pointProdHomeomorph : ComplexPoint (X ⨯ Y) ≃ₜ ComplexPoint X × ComplexPoint Y where
  toEquiv := pointProdEquiv X Y
  continuous_toFun := (continuous_map _).prodMk (continuous_map _)
  continuous_invFun := continuous_pointProdEquiv_symm X Y

/-- The homeomorphism is the pair of projections. -/
@[simp]
theorem pointProdHomeomorph_apply (z : ComplexPoint (X ⨯ Y)) :
    pointProdHomeomorph X Y z = (map prod.fst z, map prod.snd z) :=
  rfl

/-- The inverse homeomorphism is `prod.lift`. -/
@[simp]
theorem pointProdHomeomorph_symm_apply (p : ComplexPoint X × ComplexPoint Y) :
    (pointProdHomeomorph X Y).symm p = prod.lift p.1 p.2 :=
  rfl

/-- Smooth of relative dimensions `d` and `e` gives smooth of relative dimension `d + e` for the
product: `X ⨯ Y → Y` is a base change of `X → Spec ℂ`, of relative dimension `d`, followed by
`Y → Spec ℂ`. This is the instance behind the charted space of dimension `d + e` on
`(X ⨯ Y)(ℂ)`.

The instance matches a dimension written as a sum: it is found for
`SmoothOfRelativeDimension (1 + 1) (X ⨯ Y).hom` and not for
`SmoothOfRelativeDimension 2 (X ⨯ Y).hom`, since `?d + ?e =?= 2` is not solved. Use
`inferInstanceAs (SmoothOfRelativeDimension (1 + 1) _)` for the literal form; the charted spaces on
`Fin 2 → ℂ` and `Fin (1 + 1) → ℂ` agree by defeq. Mathlib's `smoothOfRelativeDimension_comp` has
the same shape. -/
instance smoothOfRelativeDimension_prod {d e : ℕ} [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] :
    SmoothOfRelativeDimension (d + e) (X ⨯ Y).hom := by
  have : SmoothOfRelativeDimension d (prod.snd : X ⨯ Y ⟶ Y).left :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) (isPullback_prod X Y) ‹_›
  rw [← Over.w (prod.snd : X ⨯ Y ⟶ Y)]
  infer_instance

/-- The product of two smooth schemes over `Spec ℂ` is smooth: `X ⨯ Y → Y` is a base change of
`X → Spec ℂ`, followed by `Y → Spec ℂ`. -/
instance smooth_prod [Smooth X.hom] [Smooth Y.hom] : Smooth (X ⨯ Y).hom := by
  have : Smooth (prod.snd : X ⨯ Y ⟶ Y).left :=
    MorphismProperty.of_isPullback (P := @Smooth) (isPullback_prod X Y) ‹_›
  rw [← Over.w (prod.snd : X ⨯ Y ⟶ Y)]
  infer_instance

/-- The homeomorphism for Mathlib's other spelling `X ⊗ Y` of the product in `Over (Spec ℂ)`
(from the global `CartesianMonoidalCategory (Over S)`): transport of `pointProdHomeomorph` along
the canonical isomorphism `X ⊗ Y ≅ X ⨯ Y`. -/
def pointTensorHomeomorph : ComplexPoint (X ⊗ Y) ≃ₜ ComplexPoint X × ComplexPoint Y :=
  (isoMapHomeomorph (IsLimit.conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _))).trans (pointProdHomeomorph X Y)

/-- The homeomorphism for `X ⊗ Y` is the pair of Mathlib's projections. -/
theorem pointTensorHomeomorph_apply (z : ComplexPoint (X ⊗ Y)) :
    pointTensorHomeomorph X Y z =
      (map (CartesianMonoidalCategory.fst X Y) z, map (CartesianMonoidalCategory.snd X Y) z) := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) (limit.isLimit (pair X Y))
  refine Prod.ext ?_ ?_
  · change map _ (map _ z) = _
    rw [← map_comp_apply]
    exact congrArg (fun f ↦ map f z) (h ⟨.left⟩)
  · change map _ (map _ z) = _
    rw [← map_comp_apply]
    exact congrArg (fun f ↦ map f z) (h ⟨.right⟩)

end HodgeLadder.ComplexPointProd
