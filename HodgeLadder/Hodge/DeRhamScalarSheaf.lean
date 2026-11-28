module

public import HodgeLadder.Hodge.WedgeSheafMap
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicDeRham
public import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend
public import HodgeLadder.Tests.ComplexPointNonempty

/-!
# The `ℂ`-scalars `S_c` on `Ω•_ℚ` and the scalar laws of the wedge

Rung `de-rham-scalar-sheaf` (front `cup`, split from `de-rham-cup` by the red team of
`wedge-sheaf-map`, finding 8). The rational de Rham complex `Ω•_ℚ = rationalDeRhamComplex X` is a
complex of sheaves of `ℚ`-vector spaces, so multiplication by `c : ℂ` is extra structure. On the
presheaf of holomorphic `p`-forms it is the `ℂ`-linear map `θ ↦ c • θ`, read `ℚ`-linearly
(`rationalScalarPresheaf`); it commutes with restriction and with upstream's exterior derivative,
so its sheafification `rationalScalarSheaf` assembles into a chain endomorphism
`rationalDeRhamScalar X c` of `Ω•_ℚ`, written `S_c` below.

## Results

* The forgotten `S_c` is upstream's `scalarHolomorphicDeRhamComplexInt X c`, through the comparison
  `forgetRationalDeRhamIso X` (`forget_rationalDeRhamScalar`, a commuting square, exact). Upstream
  defines its `ℂ`-module structure on `H_dR^n(X)` through that endomorphism
  (`deRham_complex_smul_eq`), so `S_c` induces `c •` on de Rham cohomology: through
  `rationalHypercohomologyEquiv`, `c • α` is postcomposition with `(Q.map S_c)⟦n⟧'`
  (`rationalHypercohomologyEquiv_smul`). The square determines `S_c`
  (`eq_rationalDeRhamScalar_of_forget`). Degreewise the
  forgotten presheaf map is upstream's `scalarHolomorphicDeRhamPresheaf X d p c` by `rfl`
  (`whiskerRight_rationalScalarPresheaf`), and `S_c` is pinned on `Ω^p_ℚ` by the sheafification
  square `toSheafify_comp_rationalScalarSheaf`.
* Scalar laws of the wedge: `(S_c ⊗ 𝟙) ≫ deRhamWedge X = deRhamWedge X ≫ S_c` and
  `(𝟙 ⊗ S_c) ≫ deRhamWedge X = deRhamWedge X ≫ S_c`. Degreewise they are `(c a) ∧ b = c (a ∧ b)`
  and `a ∧ (c b) = c (a ∧ b)` (`map_smul` of `holomorphicWedge` in each argument), carried
  through sheafification by naturality of Mathlib's tensorator `μ` and to complexes by a
  component check on the summands `Ω^p_ℚ ⊗ Ω^q_ℚ`. No sign enters: `S_c` has degree zero, so the
  Koszul sign of Mathlib's tensor product of complexes plays no role.
* `S_1 = 𝟙`, `S_0 = 0`, `S_{a b} = S_b ≫ S_a` (the order of upstream's
  `scalarHolomorphicDeRhamComplexInt_mul`; the scalars commute, so the other order holds too),
  `S_{a + b} = S_a + S_b`, `S_{-1} = -𝟙`.
* Tests on every smooth integral `X` (a complex point exists by rung `complex-point-nonempty`):
  `S_{-1} ≠ 𝟙`, `S_c ≠ 0` for `c ≠ 0`, and `c ↦ S_c` is injective; the first-factor scalar law
  holds with `S_{c'}` on the target only for `c' = c` (`eq_of_tensorHom_id_comp_deRhamWedge`).

## Spelling and kernel cost

The scalar laws are proved once for an abstract `ℕ`-indexed complex `K` with a product `μ`
satisfying `ExtendMulLeibniz` and a chain endomorphism `s` (`tensorHom_extendMap_id_comp_extendMul`,
`tensorHom_id_extendMap_comp_extendMul`), then instantiated with the explicit `HasTensor`
instance `hasTensor_shQ` and the named `tensorHomShQ`, as in `HodgeLadder.Hodge.WedgeSheafMap`.
Each instantiation costs about 11 s of kernel time (`docs/gaps.md`, Known weaknesses). The
comparison square combines upstream's `mapExtendCanonicalIso_naturality` with the `ℕ`-indexed
square by `Eq.trans`, since `rw` does not cross the two spellings of sheaves of abelian groups.

## Main definitions

* `HodgeLadder.rationalScalarPresheaf X d p c`: `c •` on `rationalHolomorphicFormPresheaf X d p`
* `HodgeLadder.rationalScalarSheaf X d p c`: its sheafification, an endomorphism of `Ω^p_ℚ`
* `HodgeLadder.rationalScalarComplexNat X d c`: the `ℕ`-indexed chain endomorphism
* `HodgeLadder.rationalDeRhamScalar X c`: `S_c`, a chain endomorphism of `Ω•_ℚ`

## Main results

* `HodgeLadder.forget_rationalDeRhamScalar`:
  `forget(S_c) ≫ e = e ≫ scalarHolomorphicDeRhamComplexInt X c`; its inverse form
  `HodgeLadder.forgetRationalDeRhamIso_inv_comp_forget_rationalDeRhamScalar`; uniqueness
  `HodgeLadder.eq_rationalDeRhamScalar_of_forget`
* `HodgeLadder.rationalHypercohomologyEquiv_smul`: upstream's `c •` on `H_dR^n(X)` is
  postcomposition with `(Q.map S_c)⟦n⟧'` through the bridge
* `HodgeLadder.rationalDeRhamScalar_tensorHom_id_comp_deRhamWedge`,
  `HodgeLadder.rationalDeRhamScalar_id_tensorHom_comp_deRhamWedge`: the scalar laws
* `HodgeLadder.rationalScalarSheaf_whiskerRight_wedgeSheaf`,
  `HodgeLadder.rationalScalarSheaf_whiskerLeft_wedgeSheaf`: the sheaf-level scalar laws
* `HodgeLadder.rationalDeRhamScalar_one`, `_zero`, `_mul`, `_add`, `_neg_one`
* `HodgeLadder.rationalDeRhamScalar_neg_one_ne_id`, `HodgeLadder.rationalDeRhamScalar_ne_zero`,
  `HodgeLadder.rationalDeRhamScalar_injective`, `HodgeLadder.eq_of_tensorHom_id_comp_deRhamWedge`:
  sign separation and nonvacuity
* generic: `HodgeLadder.extendTensor_hom_ext`, `HodgeLadder.sheafify_whiskerRight_comp_μ_map`,
  `HodgeLadder.sheafify_whiskerLeft_comp_μ_map`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex AlgebraicGeometry ComplexPoint
  TopologicalSpace

namespace HodgeLadder

section GenericExtend

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  (K : CochainComplex C ℕ) (μ : ∀ p q : ℕ, K.X p ⊗ K.X q ⟶ K.X (p + q))
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [hTK : HasTensor (K.extend ComplexShape.embeddingUpNat)
    (K.extend ComplexShape.embeddingUpNat)]

/-- Maps out of `K^ℤ ⊗ K^ℤ`, `K^ℤ = K.extend embeddingUpNat`, are determined on the summands
`(p, q)` with `p q : ℕ`: the summands with a negative index are zero. -/
theorem extendTensor_hom_ext {L : CochainComplex C ℤ}
    {φ ψ : tensorObj (K.extend ComplexShape.embeddingUpNat)
      (K.extend ComplexShape.embeddingUpNat) ⟶ L}
    (h : ∀ p q : ℕ, ιTensorObj (K.extend ComplexShape.embeddingUpNat)
        (K.extend ComplexShape.embeddingUpNat) (p : ℤ) (q : ℤ) ((p : ℤ) + q) rfl ≫
          φ.f ((p : ℤ) + q) =
        ιTensorObj (K.extend ComplexShape.embeddingUpNat)
        (K.extend ComplexShape.embeddingUpNat) (p : ℤ) (q : ℤ) ((p : ℤ) + q) rfl ≫
          ψ.f ((p : ℤ) + q)) :
    φ = ψ := by
  ext n i₁ i₂ hh
  have h' : i₁ + i₂ = n := hh
  by_cases h₁ : 0 ≤ i₁
  swap
  · exact (isZero_tensor_left (isZero_extend_X_of_neg K (by lia)) _).eq_of_src _ _
  by_cases h₂ : 0 ≤ i₂
  swap
  · exact (isZero_tensor_right _ (isZero_extend_X_of_neg K (by lia))).eq_of_src _ _
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le h₁
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le h₂
  subst h'
  exact h p q

/-- `e.f (p + q) = p + q` for `e = embeddingUpNat`. -/
theorem embeddingUpNat_f_add (p q : ℕ) :
    ComplexShape.embeddingUpNat.f (p + q) = (p : ℤ) + q := by
  simp

/-- **Scalar law in the first factor, generic.** If a chain endomorphism `s` of `K` satisfies
`(s ▷ K^q) ≫ μ p q = μ p q ≫ s` in every bidegree, then `(s^ℤ ⊗ 𝟙) ≫ extendMul = extendMul ≫ s^ℤ`
on the extension `K^ℤ`. -/
theorem tensorHom_extendMap_id_comp_extendMul (hμ : ExtendMulLeibniz K μ) (s : K ⟶ K)
    (hs : ∀ p q : ℕ, (s.f p ▷ K.X q) ≫ μ p q = μ p q ≫ s.f (p + q)) :
    tensorHom (extendMap s ComplexShape.embeddingUpNat)
        (𝟙 (K.extend ComplexShape.embeddingUpNat)) ≫ extendMul K μ hμ =
      extendMul K μ hμ ≫ extendMap s ComplexShape.embeddingUpNat := by
  refine extendTensor_hom_ext K (fun p q => ?_)
  rw [comp_f, comp_f, ← Category.assoc, ← Category.assoc, ιTensorObj_extendMul_f]
  erw [ι_mapBifunctorMap]
  rw [Category.assoc, Category.assoc, ιTensorObj_extendMul_f,
    extendMulComponent_eq K μ p q (ComplexShape.embeddingUpNat_f p)
      (ComplexShape.embeddingUpNat_f q) (embeddingUpNat_f_add p q),
    extendMap_f s _ (ComplexShape.embeddingUpNat_f p),
    extendMap_f s _ (embeddingUpNat_f_add p q)]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, id_f, MonoidalCategory.whiskerLeft_id,
    comp_whiskerRight, Category.assoc, Iso.inv_hom_id_assoc]
  erw [Category.id_comp]
  simp only [tensorHom_def, Category.assoc, inv_hom_whiskerRight_assoc]
  rw [← whisker_exchange_assoc, reassoc_of% (hs p q)]

/-- **Scalar law in the second factor, generic.** If `(K^p ◁ s) ≫ μ p q = μ p q ≫ s` in every
bidegree, then `(𝟙 ⊗ s^ℤ) ≫ extendMul = extendMul ≫ s^ℤ`. -/
theorem tensorHom_id_extendMap_comp_extendMul (hμ : ExtendMulLeibniz K μ) (s : K ⟶ K)
    (hs : ∀ p q : ℕ, (K.X p ◁ s.f q) ≫ μ p q = μ p q ≫ s.f (p + q)) :
    tensorHom (𝟙 (K.extend ComplexShape.embeddingUpNat))
        (extendMap s ComplexShape.embeddingUpNat) ≫ extendMul K μ hμ =
      extendMul K μ hμ ≫ extendMap s ComplexShape.embeddingUpNat := by
  refine extendTensor_hom_ext K (fun p q => ?_)
  rw [comp_f, comp_f, ← Category.assoc, ← Category.assoc, ιTensorObj_extendMul_f]
  erw [ι_mapBifunctorMap]
  rw [Category.assoc, Category.assoc, ιTensorObj_extendMul_f,
    extendMulComponent_eq K μ p q (ComplexShape.embeddingUpNat_f p)
      (ComplexShape.embeddingUpNat_f q) (embeddingUpNat_f_add p q),
    extendMap_f s _ (ComplexShape.embeddingUpNat_f q),
    extendMap_f s _ (embeddingUpNat_f_add p q)]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, id_f, MonoidalCategory.id_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc]
  erw [Category.id_comp]
  simp only [tensorHom_def', Category.assoc, whiskerLeft_inv_hom_assoc]
  rw [whisker_exchange_assoc, reassoc_of% (hs p q)]

end GenericExtend

section Sheaves

attribute [local instance] Cup.sheafMonoidal analyticShQMonoidal

section GenericSheaf

variable {Y : TopCat.{0}}

/-- **A presheaf scalar law survives sheafification, first factor.** If
`(s ▷ Q) ≫ w = w ≫ t`, then `(sheafify s ▷ sheafify Q) ≫ (μ ≫ sheafify w) =
(μ ≫ sheafify w) ≫ sheafify t`. -/
theorem sheafify_whiskerRight_comp_μ_map {P P' Q R R' : Cup.PreQ Y} (s : P ⟶ P')
    (w : P ⊗ Q ⟶ R) (w' : P' ⊗ Q ⟶ R') (t : R ⟶ R') (h : (s ▷ Q) ≫ w' = w ≫ t) :
    ((Cup.sheafifyQ Y).map s ▷ (Cup.sheafifyQ Y).obj Q) ≫
        (Functor.LaxMonoidal.μ (Cup.sheafifyQ Y) P' Q ≫ (Cup.sheafifyQ Y).map w') =
      (Functor.LaxMonoidal.μ (Cup.sheafifyQ Y) P Q ≫ (Cup.sheafifyQ Y).map w) ≫
        (Cup.sheafifyQ Y).map t := by
  rw [← Category.assoc, Functor.LaxMonoidal.μ_natural_left, Category.assoc, Category.assoc,
    ← Functor.map_comp, h, Functor.map_comp]

/-- **A presheaf scalar law survives sheafification, second factor.** If
`(P ◁ s) ≫ w' = w ≫ t`, then `(sheafify P ◁ sheafify s) ≫ (μ ≫ sheafify w') =
(μ ≫ sheafify w) ≫ sheafify t`. -/
theorem sheafify_whiskerLeft_comp_μ_map {P Q Q' R R' : Cup.PreQ Y} (s : Q ⟶ Q')
    (w : P ⊗ Q ⟶ R) (w' : P ⊗ Q' ⟶ R') (t : R ⟶ R') (h : (P ◁ s) ≫ w' = w ≫ t) :
    ((Cup.sheafifyQ Y).obj P ◁ (Cup.sheafifyQ Y).map s) ≫
        (Functor.LaxMonoidal.μ (Cup.sheafifyQ Y) P Q' ≫ (Cup.sheafifyQ Y).map w') =
      (Functor.LaxMonoidal.μ (Cup.sheafifyQ Y) P Q ≫ (Cup.sheafifyQ Y).map w) ≫
        (Cup.sheafifyQ Y).map t := by
  rw [← Category.assoc, Functor.LaxMonoidal.μ_natural_right, Category.assoc, Category.assoc,
    ← Functor.map_comp, h, Functor.map_comp]

end GenericSheaf

section Forms

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Multiplication by `c : ℂ` on `rationalHolomorphicFormPresheaf X d p`: on an open `U`, the
`ℂ`-linear map `c • id` of `HolomorphicForm X d U p`, read `ℚ`-linearly. -/
def rationalScalarPresheaf (p : ℕ) (c : ℂ) :
    rationalHolomorphicFormPresheaf X d p ⟶ rationalHolomorphicFormPresheaf X d p where
  app U := ModuleCat.ofHom
    ((c • LinearMap.id : HolomorphicForm X d U p →ₗ[ℂ] _).restrictScalars ℚ)
  naturality U V i := ModuleCat.hom_ext <| LinearMap.ext fun (x : HolomorphicForm X d U p) => by
    change c • holomorphicFormRestriction X d i p x = holomorphicFormRestriction X d i p (c • x)
    exact ((holomorphicFormRestriction X d i p).map_smul c x).symm

/-- Forgetting the `ℚ`-structure of `rationalScalarPresheaf` gives upstream's
`scalarHolomorphicDeRhamPresheaf`, by `rfl`. -/
theorem whiskerRight_rationalScalarPresheaf (p : ℕ) (c : ℂ) :
    Functor.whiskerRight (rationalScalarPresheaf X d p c) Cup.U =
      scalarHolomorphicDeRhamPresheaf X d p c := rfl

/-- Scalars commute with the differential, on presheaves. -/
theorem rationalScalarPresheaf_comp_differential (p : ℕ) (c : ℂ) :
    rationalScalarPresheaf X d p c ≫ rationalHolomorphicFormDifferential X d p =
      rationalHolomorphicFormDifferential X d p ≫ rationalScalarPresheaf X d (p + 1) c :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| LinearMap.ext
    fun (x : HolomorphicForm X d U p) => (holomorphicFormDifferential X d U p).map_smul c x

/-- `S_1 = 𝟙` on presheaves. -/
theorem rationalScalarPresheaf_one (p : ℕ) :
    rationalScalarPresheaf X d p 1 = 𝟙 _ :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| LinearMap.ext
    fun (x : HolomorphicForm X d U p) => one_smul ℂ x

/-- `S_{a * b} = S_b ≫ S_a` on presheaves. -/
theorem rationalScalarPresheaf_mul (p : ℕ) (a b : ℂ) :
    rationalScalarPresheaf X d p (a * b) =
      rationalScalarPresheaf X d p b ≫ rationalScalarPresheaf X d p a :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| LinearMap.ext
    fun (x : HolomorphicForm X d U p) => mul_smul a b x

/-- `S_0 = 0` on presheaves. -/
theorem rationalScalarPresheaf_zero (p : ℕ) :
    rationalScalarPresheaf X d p 0 = 0 :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| LinearMap.ext
    fun (x : HolomorphicForm X d U p) => zero_smul ℂ x

/-- `S_{a + b} = S_a + S_b` on presheaves. -/
theorem rationalScalarPresheaf_add (p : ℕ) (a b : ℂ) :
    rationalScalarPresheaf X d p (a + b) =
      rationalScalarPresheaf X d p a + rationalScalarPresheaf X d p b :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| LinearMap.ext
    fun (x : HolomorphicForm X d U p) => add_smul a b x

/-- **Scalar law of the presheaf wedge, first factor**: `(c a) ∧ b = c (a ∧ b)`. -/
theorem rationalScalarPresheaf_whiskerRight_wedge (p q : ℕ) (c : ℂ) :
    (rationalScalarPresheaf X d p c ▷ rationalHolomorphicFormPresheaf X d q) ≫
        rationalWedgePresheaf X d p q =
      rationalWedgePresheaf X d p q ≫ rationalScalarPresheaf X d (p + q) c :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| TensorProduct.ext'
    fun (a : HolomorphicForm X d U p) (b : HolomorphicForm X d U q) =>
      LinearMap.map_smul₂ (holomorphicWedge X d U p q) c a b

/-- **Scalar law of the presheaf wedge, second factor**: `a ∧ (c b) = c (a ∧ b)`. -/
theorem rationalScalarPresheaf_whiskerLeft_wedge (p q : ℕ) (c : ℂ) :
    (rationalHolomorphicFormPresheaf X d p ◁ rationalScalarPresheaf X d q c) ≫
        rationalWedgePresheaf X d p q =
      rationalWedgePresheaf X d p q ≫ rationalScalarPresheaf X d (p + q) c :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| TensorProduct.ext'
    fun (a : HolomorphicForm X d U p) (b : HolomorphicForm X d U q) =>
      (holomorphicWedge X d U p q a).map_smul c b

/-- `S_c` on `Ω^p_ℚ`: the sheafification of `rationalScalarPresheaf X d p c`. -/
def rationalScalarSheaf (p : ℕ) (c : ℂ) :
    rationalHolomorphicFormSheaf X d p ⟶ rationalHolomorphicFormSheaf X d p :=
  (Cup.sheafifyQ (TopCat.of (ComplexPoint X))).map (rationalScalarPresheaf X d p c)

/-- **The defining square of `S_c`** on `Ω^p_ℚ`: the rational sheafification map followed by
`S_c` is `c •` followed by the sheafification map (Mathlib's `toSheafify_naturality`). -/
theorem toSheafify_comp_rationalScalarSheaf (p : ℕ) (c : ℂ) :
    toSheafify (Cup.J (TopCat.of (ComplexPoint X))) (rationalHolomorphicFormPresheaf X d p) ≫
        (Cup.presheafQ _).map (rationalScalarSheaf X d p c) =
      rationalScalarPresheaf X d p c ≫
        toSheafify (Cup.J (TopCat.of (ComplexPoint X))) (rationalHolomorphicFormPresheaf X d p) :=
  (toSheafify_naturality _ _).symm

/-- Scalars commute with the sheafified differential. -/
theorem rationalScalarSheaf_comp_differential (p : ℕ) (c : ℂ) :
    rationalScalarSheaf X d p c ≫ rationalHolomorphicFormSheafDifferential X d p =
      rationalHolomorphicFormSheafDifferential X d p ≫ rationalScalarSheaf X d (p + 1) c := by
  change (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map _ =
    (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map _
  rw [← Functor.map_comp, ← Functor.map_comp, rationalScalarPresheaf_comp_differential]

/-- **Scalar law of the sheafified wedge, first factor.** -/
theorem rationalScalarSheaf_whiskerRight_wedgeSheaf (p q : ℕ) (c : ℂ) :
    (rationalScalarSheaf X d p c ▷ rationalHolomorphicFormSheaf X d q) ≫ wedgeSheaf X d p q =
      wedgeSheaf X d p q ≫ rationalScalarSheaf X d (p + q) c :=
  sheafify_whiskerRight_comp_μ_map _ _ _ _ (rationalScalarPresheaf_whiskerRight_wedge X d p q c)

/-- **Scalar law of the sheafified wedge, second factor.** -/
theorem rationalScalarSheaf_whiskerLeft_wedgeSheaf (p q : ℕ) (c : ℂ) :
    (rationalHolomorphicFormSheaf X d p ◁ rationalScalarSheaf X d q c) ≫ wedgeSheaf X d p q =
      wedgeSheaf X d p q ≫ rationalScalarSheaf X d (p + q) c :=
  sheafify_whiskerLeft_comp_μ_map _ _ _ _ (rationalScalarPresheaf_whiskerLeft_wedge X d p q c)

/-- `S_c` on the `ℕ`-indexed complex `Ω•_ℚ`, degreewise `rationalScalarSheaf`. -/
def rationalScalarComplexNat (c : ℂ) :
    rationalHolomorphicDeRhamComplexNat X d ⟶ rationalHolomorphicDeRhamComplexNat X d :=
  CochainComplex.ofHom (fun p => rationalScalarSheaf X d p c) (fun p => by
    rw [rationalHolomorphicDeRhamComplexNat_d]
    exact rationalScalarSheaf_comp_differential X d p c)

/-- The degree-`p` component of `rationalScalarComplexNat`. -/
@[simp] theorem rationalScalarComplexNat_f (c : ℂ) (p : ℕ) :
    (rationalScalarComplexNat X d c).f p = rationalScalarSheaf X d p c := rfl

/-- `S_1 = 𝟙` on the `ℕ`-indexed complex. -/
theorem rationalScalarComplexNat_one : rationalScalarComplexNat X d 1 = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  rw [rationalScalarComplexNat_f, rationalScalarSheaf, rationalScalarPresheaf_one]
  exact (Cup.sheafifyQ (TopCat.of (ComplexPoint X))).map_id _

/-- `S_0 = 0` on the `ℕ`-indexed complex. -/
theorem rationalScalarComplexNat_zero : rationalScalarComplexNat X d 0 = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  rw [rationalScalarComplexNat_f, rationalScalarSheaf, rationalScalarPresheaf_zero]
  exact (Cup.sheafifyQ (TopCat.of (ComplexPoint X))).map_zero _ _

/-- `S_{a * b} = S_b ≫ S_a` on the `ℕ`-indexed complex. -/
theorem rationalScalarComplexNat_mul (a b : ℂ) :
    rationalScalarComplexNat X d (a * b) =
      rationalScalarComplexNat X d b ≫ rationalScalarComplexNat X d a := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  rw [rationalScalarComplexNat_f, rationalScalarSheaf, rationalScalarPresheaf_mul,
    Functor.map_comp]
  rfl

/-- `S_{a + b} = S_a + S_b` on the `ℕ`-indexed complex. -/
theorem rationalScalarComplexNat_add (a b : ℂ) :
    rationalScalarComplexNat X d (a + b) =
      rationalScalarComplexNat X d a + rationalScalarComplexNat X d b := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  rw [rationalScalarComplexNat_f, rationalScalarSheaf, rationalScalarPresheaf_add,
    Functor.map_add]
  rfl

/-- **The forgotten scalar is upstream's, on `ℕ`-indexed complexes**, through
`forgetRationalHolomorphicDeRhamComplexNatIso`. -/
theorem forget_rationalScalarComplexNat (c : ℂ) :
    ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapHomologicalComplex _).map
        (rationalScalarComplexNat X d c) ≫ (forgetRationalHolomorphicDeRhamComplexNatIso X d).hom =
      (forgetRationalHolomorphicDeRhamComplexNatIso X d).hom ≫
        scalarHolomorphicDeRhamComplex X d c := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  exact (forgetSheafifyNatIso X).inv.naturality (rationalScalarPresheaf X d p c)

end Forms

section Complex

attribute [local instance] wsmCurriedTensorAdditive wsmTensorLeftAdditive
  wsmTensorRightPreservesEmpty rdrForgetAdditive

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- **`S_c` on `Ω•_ℚ`**: the extension to integer degrees of `rationalScalarComplexNat`. -/
def rationalDeRhamScalar (c : ℂ) : rationalDeRhamComplex X ⟶ rationalDeRhamComplex X :=
  extendMap (rationalScalarComplexNat X (dim X.left) c) ComplexShape.embeddingUpNat

/-- In degree `n = p`, `S_c` is `rationalScalarSheaf` conjugated by `extendXIso`. -/
theorem rationalDeRhamScalar_f (c : ℂ) {p : ℕ} {n : ℤ}
    (h : ComplexShape.embeddingUpNat.f p = n) :
    (rationalDeRhamScalar X c).f n =
      ((rationalHolomorphicDeRhamComplexNat X (dim X.left)).extendXIso
          ComplexShape.embeddingUpNat h).hom ≫ rationalScalarSheaf X (dim X.left) p c ≫
        ((rationalHolomorphicDeRhamComplexNat X (dim X.left)).extendXIso
          ComplexShape.embeddingUpNat h).inv :=
  extendMap_f _ _ h

/-- **The forgotten scalar is upstream's** `scalarHolomorphicDeRhamComplexInt X c`: forgetting the
`ℚ`-structure of `S_c` and applying the comparison `forgetRationalDeRhamIso X` gives upstream's
multiplication by `c` on `Ω•(X)`. A commuting square, exact, no sign; upstream's `ℂ`-module
structure on `H_dR^n(X)` is the hypercohomology of the right side (`deRham_complex_smul_eq`). -/
theorem forget_rationalDeRhamScalar (c : ℂ) :
    (forgetComplex X).map (rationalDeRhamScalar X c) ≫ (forgetRationalDeRhamIso X).hom =
      (forgetRationalDeRhamIso X).hom ≫ scalarHolomorphicDeRhamComplexInt X c := by
  have h1 := mapExtendCanonicalIso_naturality (Cup.forgetSheaf (TopCat.of (ComplexPoint X)))
    (rationalHolomorphicDeRhamComplexNat X (dim X.left)) ComplexShape.embeddingUpNat
    (rationalScalarComplexNat X (dim X.left) c)
  have h2 : extendMap (((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        _).map (rationalScalarComplexNat X (dim X.left) c)) ComplexShape.embeddingUpNat ≫
      extendMap (forgetRationalHolomorphicDeRhamComplexNatIso X (dim X.left)).hom
        ComplexShape.embeddingUpNat =
      extendMap (forgetRationalHolomorphicDeRhamComplexNatIso X (dim X.left)).hom
        ComplexShape.embeddingUpNat ≫ scalarHolomorphicDeRhamComplexInt X c :=
    (extendMap_comp _ _ _).symm.trans ((congrArg (extendMap · ComplexShape.embeddingUpNat)
      (forget_rationalScalarComplexNat X (dim X.left) c)).trans (extendMap_comp _ _ _))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

/-- **Scalar law in the first factor**: `(S_c ⊗ 𝟙) ≫ deRhamWedge X = deRhamWedge X ≫ S_c`. -/
theorem rationalDeRhamScalar_tensorHom_id_comp_deRhamWedge (c : ℂ) :
    tensorHomShQ (rationalDeRhamScalar X c) (𝟙 (rationalDeRhamComplex X)) ≫ deRhamWedge X =
      deRhamWedge X ≫ rationalDeRhamScalar X c :=
  tensorHom_extendMap_id_comp_extendMul (hTK := hasTensor_shQ (TopCat.of (ComplexPoint X))
      (rationalDeRhamComplex X) (rationalDeRhamComplex X))
    (rationalHolomorphicDeRhamComplexNat X (dim X.left)) (wedgeSheaf X (dim X.left))
    (wedgeSheaf_extendMulLeibniz X (dim X.left)) (rationalScalarComplexNat X (dim X.left) c)
    (fun p q => rationalScalarSheaf_whiskerRight_wedgeSheaf X (dim X.left) p q c)

/-- **Scalar law in the second factor**: `(𝟙 ⊗ S_c) ≫ deRhamWedge X = deRhamWedge X ≫ S_c`. -/
theorem rationalDeRhamScalar_id_tensorHom_comp_deRhamWedge (c : ℂ) :
    tensorHomShQ (𝟙 (rationalDeRhamComplex X)) (rationalDeRhamScalar X c) ≫ deRhamWedge X =
      deRhamWedge X ≫ rationalDeRhamScalar X c :=
  tensorHom_id_extendMap_comp_extendMul (hTK := hasTensor_shQ (TopCat.of (ComplexPoint X))
      (rationalDeRhamComplex X) (rationalDeRhamComplex X))
    (rationalHolomorphicDeRhamComplexNat X (dim X.left)) (wedgeSheaf X (dim X.left))
    (wedgeSheaf_extendMulLeibniz X (dim X.left)) (rationalScalarComplexNat X (dim X.left) c)
    (fun p q => rationalScalarSheaf_whiskerLeft_wedgeSheaf X (dim X.left) p q c)

/-- `S_1 = 𝟙`. -/
theorem rationalDeRhamScalar_one : rationalDeRhamScalar X 1 = 𝟙 _ := by
  rw [rationalDeRhamScalar, rationalScalarComplexNat_one, extendMap_id]
  rfl

/-- `S_0 = 0`. -/
theorem rationalDeRhamScalar_zero : rationalDeRhamScalar X 0 = 0 := by
  rw [rationalDeRhamScalar, rationalScalarComplexNat_zero, extendMap_zero]
  rfl

/-- `S_{a * b} = S_b ≫ S_a`, the order of upstream's `scalarHolomorphicDeRhamComplexInt_mul`. -/
theorem rationalDeRhamScalar_mul (a b : ℂ) :
    rationalDeRhamScalar X (a * b) = rationalDeRhamScalar X b ≫ rationalDeRhamScalar X a := by
  rw [rationalDeRhamScalar, rationalScalarComplexNat_mul, extendMap_comp]
  rfl

/-- `S_{a + b} = S_a + S_b`. -/
theorem rationalDeRhamScalar_add (a b : ℂ) :
    rationalDeRhamScalar X (a + b) = rationalDeRhamScalar X a + rationalDeRhamScalar X b := by
  rw [rationalDeRhamScalar, rationalScalarComplexNat_add, extendMap_add]
  rfl

/-- `S_{-1} = -𝟙`. -/
theorem rationalDeRhamScalar_neg_one : rationalDeRhamScalar X (-1) = -𝟙 _ := by
  have h := rationalDeRhamScalar_add X (-1) 1
  rw [neg_add_cancel, rationalDeRhamScalar_one, rationalDeRhamScalar_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- **Sign separation.** `S_{-1} ≠ 𝟙` on every smooth integral `X`: otherwise `𝟙 = -𝟙` on
`Ω•_ℚ`, so `rationalDeRhamUnit X = -rationalDeRhamUnit X`, against
`Tests.rationalDeRhamUnit_ne_neg'`. -/
theorem rationalDeRhamScalar_neg_one_ne_id : rationalDeRhamScalar X (-1) ≠ 𝟙 _ := by
  intro h
  rw [rationalDeRhamScalar_neg_one] at h
  apply Tests.rationalDeRhamUnit_ne_neg' X
  calc rationalDeRhamUnit X = rationalDeRhamUnit X ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = rationalDeRhamUnit X ≫ (-𝟙 _) := by rw [h]
    _ = -rationalDeRhamUnit X := by rw [Preadditive.comp_neg, Category.comp_id]

/-- **Nonvacuity.** `S_c ≠ 0` for `c ≠ 0` on every smooth integral `X`: `S_c ≫ S_{c⁻¹} = S_1 = 𝟙`,
and `𝟙 ≠ 0` on `Ω•_ℚ` since `rationalDeRhamUnit X ≠ 0` (`Tests.rationalDeRhamUnit_ne_zero'`). -/
theorem rationalDeRhamScalar_ne_zero {c : ℂ} (hc : c ≠ 0) : rationalDeRhamScalar X c ≠ 0 := by
  intro h
  have h1 : 𝟙 (rationalDeRhamComplex X) = 0 := by
    rw [← rationalDeRhamScalar_one X, ← mul_inv_cancel₀ hc, rationalDeRhamScalar_mul, h,
      comp_zero]
  apply Tests.rationalDeRhamUnit_ne_zero' X
  rw [← Category.comp_id (rationalDeRhamUnit X), h1, comp_zero]

/-- **The scalars are separated**: `S_a = S_b` only for `a = b`, on every smooth integral `X`. -/
theorem rationalDeRhamScalar_injective : Function.Injective (rationalDeRhamScalar X) := by
  intro a b h
  by_contra hab
  apply rationalDeRhamScalar_ne_zero X (sub_ne_zero.2 hab)
  have h2 := rationalDeRhamScalar_add X (a - b) b
  rw [sub_add_cancel, h] at h2
  exact (add_eq_right.1 h2.symm)

/-- **The forget square pins `S_c`**: a chain endomorphism of `Ω•_ℚ` whose forgotten image is
upstream's `scalarHolomorphicDeRhamComplexInt X c` through `forgetRationalDeRhamIso` is `S_c`. -/
theorem eq_rationalDeRhamScalar_of_forget (c : ℂ)
    (φ : rationalDeRhamComplex X ⟶ rationalDeRhamComplex X)
    (h : (forgetComplex X).map φ ≫ (forgetRationalDeRhamIso X).hom =
      (forgetRationalDeRhamIso X).hom ≫ scalarHolomorphicDeRhamComplexInt X c) :
    φ = rationalDeRhamScalar X c := by
  have h2 : (forgetComplex X).map φ = (forgetComplex X).map (rationalDeRhamScalar X c) := by
    rw [← cancel_mono (forgetRationalDeRhamIso X).hom, h, forget_rationalDeRhamScalar X c]
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).map_injective
    (congrArg (fun f => HomologicalComplex.Hom.f f n) h2)

/-- **The first-factor scalar law pins its target scalar**:
`(S_c ⊗ 𝟙) ≫ deRhamWedge X = deRhamWedge X ≫ S_{c'}` only for `c' = c`; with `S_{conj c}` or
`S_{−c}` on the right it fails on every smooth integral `X`. -/
theorem eq_of_tensorHom_id_comp_deRhamWedge (c c' : ℂ)
    (h : tensorHomShQ (rationalDeRhamScalar X c) (𝟙 (rationalDeRhamComplex X)) ≫
        deRhamWedge X = deRhamWedge X ≫ rationalDeRhamScalar X c') : c = c' := by
  have e : shQLeftUnitor (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X) ≫
        rationalDeRhamScalar X c =
      shQLeftUnitor (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X) ≫
        rationalDeRhamScalar X c' := by
    rw [← deRhamWedge_unit X, Category.assoc, Category.assoc,
      ← rationalDeRhamScalar_tensorHom_id_comp_deRhamWedge X c, h]
  apply rationalDeRhamScalar_injective X
  rw [shQLeftUnitor_eq] at e
  exact (Iso.cancel_iso_hom_left _ _ _).1 e

end Complex

end Sheaves

section Bridge

set_option linter.auxLemma false

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

attribute [local instance] rhHasDerivedCategory rhSiteHasDerivedCategory rhHasExt
  rhQHasDerivedCategory rhTensorAdditive rhForgetAdditive rhTensorPFL rhTensorPFC rhForgetPFL
  rhForgetPFC

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The forget square of `S_c`, read through the inverse comparison:
`e⁻¹ ≫ forget(S_c) = scalarHolomorphicDeRhamComplexInt X c ≫ e⁻¹`. -/
theorem forgetRationalDeRhamIso_inv_comp_forget_rationalDeRhamScalar (c : ℂ) :
    (forgetRationalDeRhamIso X).inv ≫ (forgetComplex X).map (rationalDeRhamScalar X c) =
      scalarHolomorphicDeRhamComplexInt X c ≫ (forgetRationalDeRhamIso X).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← forget_rationalDeRhamScalar X c, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **`S_c` induces upstream's `c •` on `H_dR^n(X)`.** Through `forgetRationalDeRhamIso` and
`rationalHypercohomologyEquiv`, upstream's action `c • α` (`deRham_complex_smul_eq`) is
postcomposition with `(Q.map S_c)⟦n⟧'`. Exact, no conjugation. -/
theorem rationalHypercohomologyEquiv_smul (n : ℤ) (c : ℂ) (α : H_dR^n(X)) :
    rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n
        (hypercohomologyMap X (forgetRationalDeRhamIso X).inv n (c • α)) =
      rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n
          (hypercohomologyMap X (forgetRationalDeRhamIso X).inv n α) ≫
        (DerivedCategory.Q.map (rationalDeRhamScalar X c))⟦n⟧' := by
  have h1 : hypercohomologyMap X (forgetRationalDeRhamIso X).inv n (c • α) =
      hypercohomologyMap X ((forgetComplex X).map (rationalDeRhamScalar X c)) n
        (hypercohomologyMap X (forgetRationalDeRhamIso X).inv n α) := by
    rw [deRham_complex_smul_eq]
    exact ((hypercohomologyMap_comp_apply X _ _ n α).symm.trans
      (congrArg (fun f => hypercohomologyMap X f n α)
        (forgetRationalDeRhamIso_inv_comp_forget_rationalDeRhamScalar X c).symm)).trans
      (hypercohomologyMap_comp_apply X _ _ n α)
  rw [h1]
  exact rationalHypercohomologyEquiv_map X _ n _

end Bridge

end HodgeLadder
