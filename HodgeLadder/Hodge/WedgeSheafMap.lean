module

public import HodgeLadder.Hodge.WedgeSheafify
public import HodgeLadder.Hodge.PairingProduct

/-!
# The wedge as a morphism of complexes `Ω•_ℚ ⊗ Ω•_ℚ ⟶ Ω•_ℚ`

Rung `wedge-sheaf-map` (front `cup`), the complex-level part of the original `wedge-sheaf-map`;
`wedge-presheaf` and `wedge-sheafify` were split off it. The sheafified
wedge `wedgeSheaf X d p q : Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ` of rung `wedge-sheafify` assembles into a
morphism of complexes `deRhamWedge X` in Mathlib's tensor product of integer-indexed complexes,
typed as the `m` of `pairProductShQ` (rung `pairing-product`), so that rung `de-rham-cup` can
take `deRhamCup x y := pairProductShQ μ y x`.

## Construction

Generic layer, for an abelian monoidal `C`, an `ℕ`-indexed complex `K` and maps
`μ p q : K^p ⊗ K^q ⟶ K^{p+q}`: on the summand `(i₁, i₂)` of `K^ℤ ⊗ K^ℤ`, `K^ℤ = K.extend e`,
the component is `μ p q` conjugated by `extendXIso` when `i₁ = p ≥ 0`, `i₂ = q ≥ 0`, and zero
otherwise (`extendMulComponent`). It is a chain map (`extendMul`) as soon as `μ` satisfies the
Leibniz rule `ExtendMulLeibniz`, with the sign `(−1)^p`. That is Mathlib's Koszul sign: the
differential of `K ⊗ L` is `d₁ + d₂` with `ε₁ = 1` and `ε₂(p, q) = p.negOnePow`
(`TensorSigns (up ℤ)`), and the proof of `extendMul` reads `ε₂(p, q)` as `(−1)^p` through
`Int.coe_negOnePow_natCast`. No other sign is needed, and the factor order is the one of `μ`.
The degree casts are `eqToHom` along `p + 1 + q = p + q + 1`, handled by `extendXIso_inv_congr`
(by `subst`); `p + (q + 1) = p + q + 1` holds by `rfl`.

Truncations: `F^p L ⊗ F^q L` is zero below `p + q`, and the inclusion `F^{p+q} L ⟶ L` is an
isomorphism from `p + q` on, so `(i_p ⊗ i_q) ≫ m` lifts through it (`liftOfIsIsoGE`,
`truncMul`). The unit law is generic too (`extendMul_unit`): a degreewise unit law of `μ` gives
`(u[0] ⊗ 𝟙) ≫ extendMul = λ` for Mathlib's left unitor of complexes.

Sheaf layer: the presheaf Leibniz rule is `holomorphicFormDifferential_holomorphicWedge` on pure
tensors; the sheaf rule follows through `toSheafifyTensor_hom_ext`, its naturality, the square
`toSheafifyTensor_comp_wedgeSheaf` and the cast transport `toSheafify_comp_eqToHom`, with the
sum and the sign handled once at a variable space (`toSheafifyTensor_hom_ext_add_zsmul`).

## Spelling and kernel cost

Complexes of sheaves of record (`rationalDeRhamComplex X`, the truncations, the unit) carry the
zero morphisms found by instance search on `Cup.ShQ`, while Mathlib's tensor product of complexes
and `tensorRightComplex` carry those of the preadditive structure; every statement that mixes them
costs kernel time (`docs/gaps.md`, Known weaknesses). The statements therefore name every sheaf
level map: `tensorHomShQ` (Mathlib's `tensorHom` with the `hasTensor_shQ` instances, elaborated
once at a variable space, the spelling of the hypothesis of `pairProductShQ_naturality`),
`shQLeftUnitor` (Mathlib's left unitor of complexes) and `deRhamUnitShQ` (the unit, typed from
`unitComplex`). Instance search misses the additivity of the tensor product and the preservation
of the empty colimit at `TopCat.of (ComplexPoint X)`; they are supplied as local instances. A
consumer that states anything with `HomologicalComplex.tensorHom` or the left unitor at
`TopCat.of (ComplexPoint X)` activates them with `attribute [local instance]
HodgeLadder.wsmCurriedTensorAdditive HodgeLadder.wsmTensorLeftAdditive
HodgeLadder.wsmTensorRightPreservesEmpty`, together with `Cup.sheafMonoidal` and
`analyticShQMonoidal`.

## Main definitions

* `HodgeLadder.extendMulComponent`, `HodgeLadder.ExtendMulLeibniz`, `HodgeLadder.extendMul`
  (generic)
* `HodgeLadder.liftOfIsIsoGE`, `HodgeLadder.truncMul` (generic)
* `HodgeLadder.tensorHomShQ`, `HodgeLadder.shQLeftUnitor` (any space)
* `HodgeLadder.deRhamWedge X`: `Ω•_ℚ ⊗ Ω•_ℚ ⟶ Ω•_ℚ`
* `HodgeLadder.deRhamUnitShQ X`: the unit `ℚ_X[0] ⟶ Ω•_ℚ` from `unitComplex`
* `HodgeLadder.deRhamWedgeFiltered X p q`: `F^p Ω•_ℚ ⊗ F^q Ω•_ℚ ⟶ F^{p+q} Ω•_ℚ`

## Main results

* `HodgeLadder.ιTensorObj_extendMul_f`, `HodgeLadder.extendMulComponent_eq`: the components
* `HodgeLadder.extendMul_unit`, `HodgeLadder.truncMul_comp_inclusion` (generic)
* `HodgeLadder.rationalWedgePresheaf_leibniz`, `HodgeLadder.wedgeSheaf_leibniz`,
  `HodgeLadder.wedgeSheaf_extendMulLeibniz`: the Leibniz rule, sign `(−1)^p`
* `HodgeLadder.ιTensorObj_deRhamWedge_f`: on `Ω^p_ℚ ⊗ Ω^q_ℚ`, `deRhamWedge X` is `wedgeSheaf p q`
* `HodgeLadder.deRhamWedge_unit`: `(u ⊗ 𝟙) ≫ deRhamWedge X = λ_{Ω•_ℚ}`;
  `HodgeLadder.deRhamWedge_unit_unit`: `λ_{ℚ[0]} ≫ u = (u ⊗ u) ≫ deRhamWedge X`, from the generic
  `HodgeLadder.unitComplexMul_comp_of_unit`
* `HodgeLadder.deRhamWedgeFiltered_comp_inclusion`: `μ_{p,q} ≫ i_{p+q} = (i_p ⊗ i_q) ≫ deRhamWedge`
* `HodgeLadder.deRhamWedge_ne_zero`: nonvacuity on every `X` with a complex point;
  `HodgeLadder.deRhamWedge_unit_neg`: the unit law fails for `−deRhamWedge X`
* `HodgeLadder.eq_extendMul_of_components`, `HodgeLadder.eq_truncMul_iff`: uniqueness (generic)
* instances `rationalHodgeFilteredComplex_isStrictlyGE`, `_isStrictlyLE`: `F^p Ω•_ℚ` lies in
  degrees `[p, dim X]`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex AlgebraicGeometry ComplexPoint
  TopologicalSpace

namespace HodgeLadder

section GenericExtend

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  (K : CochainComplex C ℕ) (μ : ∀ p q : ℕ, K.X p ⊗ K.X q ⟶ K.X (p + q))

/-- The component `(K.extend e).X i₁ ⊗ (K.extend e).X i₂ ⟶ (K.extend e).X n` of the product on
the integer-indexed extension: on `i₁ = p ≥ 0`, `i₂ = q ≥ 0`, `n = p + q` it is `μ p q`
conjugated by `extendXIso`; it is zero otherwise. -/
def extendMulComponent (i₁ i₂ n : ℤ) :
    (K.extend ComplexShape.embeddingUpNat).X i₁ ⊗ (K.extend ComplexShape.embeddingUpNat).X i₂ ⟶
      (K.extend ComplexShape.embeddingUpNat).X n :=
  if h : 0 ≤ i₁ ∧ 0 ≤ i₂ ∧ i₁ + i₂ = n then
    ((K.extendXIso ComplexShape.embeddingUpNat (i := i₁.toNat)
        (Int.toNat_of_nonneg h.1)).hom ⊗ₘ
      (K.extendXIso ComplexShape.embeddingUpNat (i := i₂.toNat)
        (Int.toNat_of_nonneg h.2.1)).hom) ≫
      μ i₁.toNat i₂.toNat ≫
      (K.extendXIso ComplexShape.embeddingUpNat (i := i₁.toNat + i₂.toNat) (by
        change ((i₁.toNat + i₂.toNat : ℕ) : ℤ) = n
        rw [Nat.cast_add, Int.toNat_of_nonneg h.1, Int.toNat_of_nonneg h.2.1, h.2.2])).inv
  else 0

/-- The component on `(p, q)` with `p, q : ℕ`: `μ p q` conjugated by `extendXIso`, for any
proofs of the degree equalities. -/
theorem extendMulComponent_eq {i₁ i₂ n : ℤ} (a b : ℕ)
    (ha : ComplexShape.embeddingUpNat.f a = i₁) (hb : ComplexShape.embeddingUpNat.f b = i₂)
    (hn : ComplexShape.embeddingUpNat.f (a + b) = n) :
    extendMulComponent K μ i₁ i₂ n =
      ((K.extendXIso ComplexShape.embeddingUpNat ha).hom ⊗ₘ
        (K.extendXIso ComplexShape.embeddingUpNat hb).hom) ≫ μ a b ≫
        (K.extendXIso ComplexShape.embeddingUpNat hn).inv := by
  have ha' : (a : ℤ) = i₁ := ha
  have hb' : (b : ℤ) = i₂ := hb
  have hn' : ((a + b : ℕ) : ℤ) = n := hn
  have h : 0 ≤ i₁ ∧ 0 ≤ i₂ ∧ i₁ + i₂ = n := ⟨by lia, by lia, by lia⟩
  obtain rfl : a = i₁.toNat := by lia
  obtain rfl : b = i₂.toNat := by lia
  rw [extendMulComponent, dite_eq_left h]

/-- The component vanishes off the quadrant `i₁, i₂ ≥ 0`, `i₁ + i₂ = n`. -/
theorem extendMulComponent_eq_zero {i₁ i₂ n : ℤ} (h : ¬ (0 ≤ i₁ ∧ 0 ≤ i₂ ∧ i₁ + i₂ = n)) :
    extendMulComponent K μ i₁ i₂ n = 0 := by
  rw [extendMulComponent, dite_eq_right h]

omit [MonoidalCategory C] in
/-- Two `extendXIso` onto the same integer degree differ by the transport along `a = b`. -/
theorem extendXIso_inv_congr {a b : ℕ} (h : a = b) {n : ℤ}
    (ha : ComplexShape.embeddingUpNat.f a = n) (hb : ComplexShape.embeddingUpNat.f b = n) :
    eqToHom (congrArg K.X h) ≫ (K.extendXIso ComplexShape.embeddingUpNat hb).inv =
      (K.extendXIso ComplexShape.embeddingUpNat ha).inv := by
  subst h
  simp

omit [MonoidalCategory C] in
/-- The extension along `embeddingUpNat` is zero in negative degrees. -/
theorem isZero_extend_X_of_neg {i : ℤ} (hi : i < 0) :
    IsZero ((K.extend ComplexShape.embeddingUpNat).X i) :=
  K.isZero_extend_X _ i (fun j hj => by
    change (j : ℤ) = i at hj
    lia)

variable [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]

omit [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive] in
/-- `0 ⊗ B` is zero when tensoring is additive in the first variable. -/
theorem isZero_tensor_left {A : C} (hA : IsZero A) (B : C) : IsZero (A ⊗ B) := by
  rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, hA.eq_of_src (𝟙 A) 0]
  change ((curriedTensor C).map 0).app B = 0
  rw [Functor.map_zero]
  rfl

omit [(curriedTensor C).Additive] in
/-- `A ⊗ 0` is zero when tensoring is additive in the second variable. -/
theorem isZero_tensor_right (A : C) {B : C} (hB : IsZero B) : IsZero (A ⊗ B) := by
  rw [IsZero.iff_id_eq_zero, ← whiskerLeft_id, hB.eq_of_src (𝟙 B) 0]
  change ((curriedTensor C).obj A).map 0 = 0
  rw [Functor.map_zero]

/-- **The Leibniz hypothesis** on `μ : K^p ⊗ K^q ⟶ K^{p+q}`:
`μ ≫ d = (d ▷ K^q) ≫ μ ≫ cast + (−1)^p (K^p ◁ d) ≫ μ`, with the transport along
`p + 1 + q = p + q + 1` and Mathlib's Koszul sign `ε₂(p, q) = (−1)^p` of `TensorSigns (up ℤ)`. -/
def ExtendMulLeibniz : Prop :=
  ∀ p q : ℕ, μ p q ≫ K.d (p + q) (p + q + 1) =
    (K.d p (p + 1) ▷ K.X q) ≫ μ (p + 1) q ≫ eqToHom (congrArg K.X (Nat.add_right_comm p 1 q)) +
      ((-1 : ℤ) ^ p) • ((K.X p ◁ K.d q (q + 1)) ≫ μ p (q + 1))

variable [hTK : HasTensor (K.extend ComplexShape.embeddingUpNat)
  (K.extend ComplexShape.embeddingUpNat)]

/-- **The product as a chain map** `K^ℤ ⊗ K^ℤ ⟶ K^ℤ` on the extension `K^ℤ = K.extend e` along
`embeddingUpNat`, for `μ` satisfying `ExtendMulLeibniz`. On the summand `(i₁, i₂)` of degree `n`
it is `extendMulComponent K μ i₁ i₂ n`. The chain-map identity is checked against Mathlib's
differential of the tensor product, `d = d₁ + d₂` with `ε₁ = 1` and `ε₂(i₁, i₂) = (−1)^{i₁}`;
no further sign enters. -/
def extendMul (hμ : ExtendMulLeibniz K μ) :
    tensorObj (K.extend ComplexShape.embeddingUpNat) (K.extend ComplexShape.embeddingUpNat) ⟶
      K.extend ComplexShape.embeddingUpNat where
  f n := mapBifunctorDesc (fun i₁ i₂ _ => extendMulComponent K μ i₁ i₂ n)
  comm' n n' hnn' := by
    ext i₁ i₂ h
    have hn' : n' = n + 1 := hnn'.symm
    have h' : i₁ + i₂ = n := h
    subst hn'
    rw [ι_mapBifunctorDesc_assoc, mapBifunctor.d_eq, Preadditive.add_comp,
      Preadditive.comp_add, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc,
      mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel i₁ (i₁ + 1) from rfl) _ _
        (by dsimp; lia),
      mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel i₂ (i₂ + 1) from rfl) _
        (by dsimp; lia)]
    simp only [Linear.units_smul_comp, Category.assoc, ι_mapBifunctorDesc]
    by_cases h₁ : 0 ≤ i₁
    swap
    · exact (isZero_tensor_left (isZero_extend_X_of_neg K (by lia)) _).eq_of_src _ _
    by_cases h₂ : 0 ≤ i₂
    swap
    · exact (isZero_tensor_right _ (isZero_extend_X_of_neg K (by lia))).eq_of_src _ _
    obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le h₁
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le h₂
    subst h'
    have e₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        ((p : ℤ), (q : ℤ)) = 1 := rfl
    have e₂ : (ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        ((p : ℤ), (q : ℤ)) : ℤ) = (-1 : ℤ) ^ p := Int.coe_negOnePow_natCast p
    rw [e₁, one_smul, Units.smul_def, e₂,
      extendMulComponent_eq K μ (i₁ := p) (i₂ := q) p q rfl rfl (Nat.cast_add p q),
      extendMulComponent_eq K μ (i₁ := p + 1) (i₂ := q) (p + 1) q (by
        simp only [ComplexShape.embeddingUpNat_f]; push_cast; ring) rfl (by
        simp only [ComplexShape.embeddingUpNat_f]; push_cast; ring),
      extendMulComponent_eq K μ (i₁ := p) (i₂ := q + 1) p (q + 1) rfl (by
        simp only [ComplexShape.embeddingUpNat_f]; push_cast; ring) (by
        simp only [ComplexShape.embeddingUpNat_f]; push_cast; ring),
      K.extend_d_eq ComplexShape.embeddingUpNat (Nat.cast_add p q)
        (show ComplexShape.embeddingUpNat.f (p + q + 1) = ↑p + ↑q + 1 by
          simp only [ComplexShape.embeddingUpNat_f]; push_cast; ring),
      K.extend_d_eq ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f p = ↑p from rfl)
        (show ComplexShape.embeddingUpNat.f (p + 1) = ↑p + 1 by
          simp only [ComplexShape.embeddingUpNat_f]; push_cast; ring),
      K.extend_d_eq ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f q = ↑q from rfl)
        (show ComplexShape.embeddingUpNat.f (q + 1) = ↑q + 1 by
          simp only [ComplexShape.embeddingUpNat_f]; push_cast; ring)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (hμ p q), Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp,
      Preadditive.comp_zsmul]
    refine congrArg₂ (· + ·) ?_ (congrArg _ ?_)
    · simp only [Category.assoc, curriedTensor_map_app, tensorHom_def,
        comp_whiskerRight, whisker_exchange_assoc, inv_hom_whiskerRight_assoc]
      rw [extendXIso_inv_congr K (Nat.add_right_comm p 1 q)
        (by simp only [ComplexShape.embeddingUpNat_f]; push_cast; ring)]
    · simp only [Category.assoc, curriedTensor_obj_map, tensorHom_def, whiskerLeft_comp,
        whisker_exchange_assoc, whiskerLeft_inv_hom_assoc]

/-- On the summand `(i₁, i₂)`, `extendMul` is `extendMulComponent`. -/
theorem ιTensorObj_extendMul_f (hμ : ExtendMulLeibniz K μ) (i₁ i₂ n : ℤ) (h : i₁ + i₂ = n) :
    ιTensorObj (K.extend ComplexShape.embeddingUpNat) (K.extend ComplexShape.embeddingUpNat)
        i₁ i₂ n h ≫ (extendMul K μ hμ).f n = extendMulComponent K μ i₁ i₂ n :=
  by dsimp only [extendMul]; exact ι_mapBifunctorDesc _ _ _ _

/-- **Uniqueness from the components.** A chain map `K^ℤ ⊗ K^ℤ ⟶ K^ℤ` that agrees with
`extendMulComponent` on every summand `(p, q)`, `p q : ℕ`, is `extendMul K μ hμ`: the summands
with a negative index are zero. -/
theorem eq_extendMul_of_components (hμ : ExtendMulLeibniz K μ)
    (φ : tensorObj (K.extend ComplexShape.embeddingUpNat) (K.extend ComplexShape.embeddingUpNat) ⟶
      K.extend ComplexShape.embeddingUpNat)
    (hφ : ∀ p q : ℕ, ιTensorObj (K.extend ComplexShape.embeddingUpNat)
        (K.extend ComplexShape.embeddingUpNat) (p : ℤ) (q : ℤ) ((p : ℤ) + q) rfl ≫
          φ.f ((p : ℤ) + q) = extendMulComponent K μ p q ((p : ℤ) + q)) :
    φ = extendMul K μ hμ := by
  ext n i₁ i₂ h
  have h' : i₁ + i₂ = n := h
  rw [ιTensorObj_extendMul_f]
  by_cases h₁ : 0 ≤ i₁
  swap
  · exact (isZero_tensor_left (isZero_extend_X_of_neg K (by lia)) _).eq_of_src _ _
  by_cases h₂ : 0 ≤ i₂
  swap
  · exact (isZero_tensor_right _ (isZero_extend_X_of_neg K (by lia))).eq_of_src _ _
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le h₁
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le h₂
  subst h'
  exact hφ p q
section Unit

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

omit hTK in
/-- The left unitor of complexes on the summand `𝟙[0]^0 ⊗ L^i`. -/
theorem ιTensorObj_leftUnitor_hom_f (L : CochainComplex C ℤ) (i : ℤ) :
    ιTensorObj (tensorUnit C (.up ℤ)) L 0 i i (zero_add i) ≫ (leftUnitor L).hom.f i =
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom ▷ L.X i) ≫ (λ_ (L.X i)).hom := by
  have h : ιTensorObj (tensorUnit C (.up ℤ)) L 0 i i (zero_add i) =
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom ▷ L.X i) ≫ (λ_ (L.X i)).hom ≫
        (leftUnitor L).inv.f i := by
    simp only [HomologicalComplex.leftUnitor, Iso.symm_inv, Hom.isoOfComponents_hom_f,
      Functor.mapIso_hom, Iso.symm_hom, GradedObject.eval_map, leftUnitor'_inv,
      Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc]
  rw [h, Category.assoc, Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f, Category.comp_id]

/-- **Unit law, generic.** If `u : 𝟙 ⟶ K⁰` with `u ≫ d = 0` satisfies
`(u ▷ K^q) ≫ μ 0 q ≫ cast = λ` in every degree `q`, then `(u[0] ⊗ 𝟙) ≫ extendMul = λ` for Mathlib's
left unitor of complexes, with `u[0] = homFromSingleExtend K u hu`. Exact. -/
theorem extendMul_unit (hμ : ExtendMulLeibniz K μ) (u : 𝟙_ C ⟶ K.X 0) (hu : u ≫ K.d 0 1 = 0)
    (hunit : ∀ q : ℕ, (u ▷ K.X q) ≫ μ 0 q ≫ eqToHom (congrArg K.X (Nat.zero_add q)) =
      (λ_ (K.X q)).hom) :
    tensorHom (homFromSingleExtend K u hu) (𝟙 (K.extend ComplexShape.embeddingUpNat)) ≫
        extendMul K μ hμ = (leftUnitor (K.extend ComplexShape.embeddingUpNat)).hom := by
  ext n i₁ i₂ h
  have h' : i₁ + i₂ = n := h
  rw [HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc]
  by_cases h₁ : i₁ = 0
  swap
  · exact (isZero_tensor_left (isZero_single_obj_X (.up ℤ) 0 (𝟙_ C) i₁ h₁) _).eq_of_src _ _
  subst h₁
  obtain rfl : i₂ = n := by simpa using h'
  by_cases h₂ : 0 ≤ i₂
  swap
  · exact (isZero_tensor_right _ (isZero_extend_X_of_neg K (by lia))).eq_of_src _ _
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le h₂
  have hf0 : (homFromSingleExtend K u hu).f 0 = (singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom ≫ u ≫
      (K.extendXIso ComplexShape.embeddingUpNat embeddingUpNat_f_zero).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact homFromSingleExtend_f_zero K u hu
  have hq : ComplexShape.embeddingUpNat.f q = (q : ℤ) := rfl
  have h0q : ComplexShape.embeddingUpNat.f (0 + q) = (q : ℤ) := by
    simp only [ComplexShape.embeddingUpNat_f, zero_add]
  refine Eq.trans ?_ (ιTensorObj_leftUnitor_hom_f _ _).symm
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp,
    curriedTensor_map_app]
  rw [ιTensorObj_extendMul_f, extendMulComponent_eq K μ 0 q embeddingUpNat_f_zero hq h0q, hf0,
    ← extendXIso_inv_congr K (Nat.zero_add q) h0q hq]
  simp only [Category.assoc, comp_whiskerRight, tensorHom_def,
    inv_hom_whiskerRight_assoc]
  rw [← whisker_exchange_assoc, reassoc_of% (hunit q), leftUnitor_naturality_assoc,
    Iso.hom_inv_id, Category.comp_id]

end Unit

end GenericExtend

section GenericLift

variable {C : Type*} [Category* C] [Abelian C]

/-- A chain map `g : A ⟶ D'` that vanishes below `r` lifts through `i : D ⟶ D'` when `i` is an
isomorphism in degrees `≥ r` and `D` is zero below `r`. -/
def liftOfIsIsoGE {A D D' : CochainComplex C ℤ} (i : D ⟶ D') (g : A ⟶ D') (r : ℤ)
    (hi : ∀ n, r ≤ n → IsIso (i.f n)) (hD : ∀ n, n < r → IsZero (D.X n))
    (hg : ∀ n, n < r → g.f n = 0) : A ⟶ D where
  f n := if h : r ≤ n then haveI := hi n h; g.f n ≫ inv (i.f n) else 0
  comm' n n' hnn' := by
    by_cases h' : r ≤ n'
    · have := hi n' h'
      rw [← cancel_mono (i.f n'), Category.assoc, Category.assoc, dite_eq_left h',
        Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← i.comm, ← g.comm]
      by_cases h : r ≤ n
      · have := hi n h
        rw [dite_eq_left h, Category.assoc, IsIso.inv_hom_id_assoc]
      · rw [dite_eq_right h, zero_comp, hg n (by lia), zero_comp]
    · exact (hD n' (by lia)).eq_of_tgt _ _

/-- The lift factors `g` through `i`. -/
theorem liftOfIsIsoGE_comp {A D D' : CochainComplex C ℤ} (i : D ⟶ D') (g : A ⟶ D') (r : ℤ)
    (hi : ∀ n, r ≤ n → IsIso (i.f n)) (hD : ∀ n, n < r → IsZero (D.X n))
    (hg : ∀ n, n < r → g.f n = 0) : liftOfIsIsoGE i g r hi hD hg ≫ i = g := by
  ext n
  rw [HomologicalComplex.comp_f]
  change (if h : r ≤ n then haveI := hi n h; g.f n ≫ inv (i.f n) else 0) ≫ i.f n = g.f n
  by_cases h : r ≤ n
  · have := hi n h
    rw [dite_eq_left h, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · rw [dite_eq_right h, zero_comp, hg n (by lia)]

end GenericLift

section GenericTrunc

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  (L : CochainComplex C ℤ)

omit [MonoidalCategory C] [(curriedTensor C).Additive]
  [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive] in
/-- `F^p L` is zero below `p`. -/
theorem isZero_stupidTrunc_X_of_lt {p n : ℤ} (h : n < p) :
    IsZero ((L.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X n) :=
  L.isZero_stupidTrunc_X _ n ((ComplexShape.notMem_range_embeddingUpIntGE_iff p n).2 h)

omit [MonoidalCategory C] [(curriedTensor C).Additive]
  [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive] in
/-- The inclusion `F^p L ⟶ L` is an isomorphism in degrees `≥ p`. -/
theorem isIso_stupidTruncInclusion_f {p n : ℤ} (h : p ≤ n) :
    IsIso ((stupidTruncInclusion L (ComplexShape.embeddingUpIntGE p)).f n) := by
  rw [stupidTruncInclusion_f L _ (i := (n - p).toNat)
    (by simp only [ComplexShape.embeddingUpIntGE_f]; lia)]
  infer_instance

variable [hTL : HasTensor L L] (m : tensorObj L L ⟶ L) (p q : ℤ)
  [hTF : HasTensor (L.stupidTrunc (ComplexShape.embeddingUpIntGE p))
    (L.stupidTrunc (ComplexShape.embeddingUpIntGE q))]

/-- **The restriction of `m` to the stupid truncations** `F^p L ⊗ F^q L ⟶ F^{p+q} L`: the lift
of `(i_p ⊗ i_q) ≫ m` through `i_{p+q}` (`liftOfIsIsoGE`), which exists because `F^p L ⊗ F^q L`
is zero below `p + q`. -/
def truncMul :
    tensorObj (L.stupidTrunc (ComplexShape.embeddingUpIntGE p))
        (L.stupidTrunc (ComplexShape.embeddingUpIntGE q)) ⟶
      L.stupidTrunc (ComplexShape.embeddingUpIntGE (p + q)) :=
  liftOfIsIsoGE (stupidTruncInclusion L (ComplexShape.embeddingUpIntGE (p + q)))
    (tensorHom (stupidTruncInclusion L (ComplexShape.embeddingUpIntGE p))
      (stupidTruncInclusion L (ComplexShape.embeddingUpIntGE q)) ≫ m) (p + q)
    (fun _ h => isIso_stupidTruncInclusion_f L h) (fun _ h => isZero_stupidTrunc_X_of_lt L h)
    (fun n h => by
      ext i₁ i₂ hh
      have hh' : i₁ + i₂ = n := hh
      rw [comp_zero]
      by_cases h₁ : i₁ < p
      · exact (isZero_tensor_left (isZero_stupidTrunc_X_of_lt L h₁) _).eq_of_src _ _
      · exact (isZero_tensor_right _ (isZero_stupidTrunc_X_of_lt L (by lia))).eq_of_src _ _)

/-- `truncMul` is compatible with the inclusions; it is the unique such map, `i_{p+q}` being a
monomorphism in each degree. -/
theorem truncMul_comp_inclusion :
    truncMul L m p q ≫ stupidTruncInclusion L (ComplexShape.embeddingUpIntGE (p + q)) =
      tensorHom (stupidTruncInclusion L (ComplexShape.embeddingUpIntGE p))
        (stupidTruncInclusion L (ComplexShape.embeddingUpIntGE q)) ≫ m :=
  liftOfIsIsoGE_comp _ _ _ _ _ _

/-- **Uniqueness of the restriction.** A map `F^p L ⊗ F^q L ⟶ F^{p+q} L` is `truncMul L m p q`
if and only if it is compatible with the inclusions. -/
theorem eq_truncMul_iff (φ : tensorObj (L.stupidTrunc (ComplexShape.embeddingUpIntGE p))
        (L.stupidTrunc (ComplexShape.embeddingUpIntGE q)) ⟶
      L.stupidTrunc (ComplexShape.embeddingUpIntGE (p + q))) :
    φ = truncMul L m p q ↔
      φ ≫ stupidTruncInclusion L (ComplexShape.embeddingUpIntGE (p + q)) =
        tensorHom (stupidTruncInclusion L (ComplexShape.embeddingUpIntGE p))
          (stupidTruncInclusion L (ComplexShape.embeddingUpIntGE q)) ≫ m := by
  constructor
  · rintro rfl
    exact truncMul_comp_inclusion L m p q
  · intro hφ
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    by_cases h : p + q ≤ n
    · have := isIso_stupidTruncInclusion_f L h
      rw [← cancel_mono ((stupidTruncInclusion L (ComplexShape.embeddingUpIntGE (p + q))).f n),
        ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, hφ, truncMul_comp_inclusion]
    · exact (isZero_stupidTrunc_X_of_lt L (by lia)).eq_of_tgt _ _
end GenericTrunc

section Sheaves

attribute [local instance] Cup.sheafMonoidal analyticShQMonoidal

section GenericSheaf

variable {Y : TopCat.{0}}

/-- `toSheafifyTensor ≫ (presheafQ Y).map _` on `a + n • b`. -/
theorem toSheafifyTensor_comp_map_add_zsmul {P Q : Cup.PreQ Y} {S : Cup.ShQ Y}
    (a b : (Cup.sheafifyQ Y).obj P ⊗ (Cup.sheafifyQ Y).obj Q ⟶ S) (n : ℤ) :
    toSheafifyTensor P Q ≫ (Cup.presheafQ Y).map (a + n • b) =
      toSheafifyTensor P Q ≫ (Cup.presheafQ Y).map a +
        n • (toSheafifyTensor P Q ≫ (Cup.presheafQ Y).map b) := by
  rw [Functor.map_add, Functor.map_zsmul, Preadditive.comp_add, Preadditive.comp_zsmul]

/-- **Maps out of a sheafified tensor product, on a sum.** If `f`, `a`, `b` are read on presheaf
tensors as `f'`, `a'`, `b'` followed by the sheafification map, and `f' = a' + n • b'`, then
`f = a + n • b`. -/
theorem toSheafifyTensor_hom_ext_add_zsmul {P Q R : Cup.PreQ Y}
    (f a b : (Cup.sheafifyQ Y).obj P ⊗ (Cup.sheafifyQ Y).obj Q ⟶ (Cup.sheafifyQ Y).obj R)
    (f' a' b' : P ⊗ Q ⟶ R) (n : ℤ)
    (hf : toSheafifyTensor P Q ≫ (Cup.presheafQ Y).map f = f' ≫ toSheafify (Cup.J Y) R)
    (ha : toSheafifyTensor P Q ≫ (Cup.presheafQ Y).map a = a' ≫ toSheafify (Cup.J Y) R)
    (hb : toSheafifyTensor P Q ≫ (Cup.presheafQ Y).map b = b' ≫ toSheafify (Cup.J Y) R)
    (h : f' = a' + n • b') : f = a + n • b := by
  refine toSheafifyTensor_hom_ext ?_
  rw [toSheafifyTensor_comp_map_add_zsmul, hf, ha, hb, h, Preadditive.add_comp,
    Preadditive.zsmul_comp]

/-- `f ⊗ g` for chain maps of complexes of sheaves of `ℚ`-vector spaces, with the instances
`hasTensor_shQ`, typed through `tensorRightComplex`. Elaborated once at a variable space. -/
abbrev tensorHomShQ {K₁ K₂ L₁ L₂ : CochainComplex (Cup.ShQ Y) ℤ} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) :
    (tensorRightComplex Y K₂).obj K₁ ⟶ (tensorRightComplex Y L₂).obj L₁ :=
  haveI := hasTensor_shQ Y K₁ K₂
  haveI := hasTensor_shQ Y L₁ L₂
  HomologicalComplex.tensorHom f g

variable (Y) in
/-- The left unitor `ℚ_Y[0] ⊗ K ≅ K` of complexes (`hom`), typed through
`tensorRightComplex`. -/
def shQLeftUnitor (K : CochainComplex (Cup.ShQ Y) ℤ) :
    (tensorRightComplex Y K).obj (unitComplex Y) ⟶ K :=
  (HomologicalComplex.leftUnitor K).hom

variable (Y) in
/-- `shQLeftUnitor` is Mathlib's left unitor of complexes, by definition. -/
theorem shQLeftUnitor_eq (K : CochainComplex (Cup.ShQ Y) ℤ) :
    shQLeftUnitor Y K = (HomologicalComplex.leftUnitor K).hom := rfl

variable (Y) in
/-- `unitComplexMul` is `shQLeftUnitor` on the unit complex, by definition. -/
theorem unitComplexMul_eq_shQLeftUnitor : unitComplexMul Y = shQLeftUnitor Y (unitComplex Y) :=
  rfl

/-- **From the unit law to the unit on both factors.** If `(u ⊗ 𝟙) ≫ m = λ_L`, then
`λ_𝟙 ≫ u = (u ⊗ u) ≫ m`: the form of the hypothesis of `pairProductShQ_naturality` at
`m = unitComplexMul`, `f = g = k = u`. -/
theorem unitComplexMul_comp_of_unit {L : CochainComplex (Cup.ShQ Y) ℤ}
    (u : unitComplex Y ⟶ L) (m : (tensorRightComplex Y L).obj L ⟶ L)
    (h : tensorHomShQ u (𝟙 L) ≫ m = shQLeftUnitor Y L) :
    unitComplexMul Y ≫ u = tensorHomShQ u u ≫ m := by
  have := hasTensor_shQ Y (unitComplex Y) (unitComplex Y)
  have := hasTensor_shQ Y (unitComplex Y) L
  have := hasTensor_shQ Y L L
  have hc := mapBifunctorMap_comp' (curriedTensor (Cup.ShQ Y)) (𝟙 (unitComplex Y)) u u (𝟙 L)
  rw [Category.id_comp, Category.comp_id] at hc
  refine Eq.trans ?_ (congrArg (· ≫ m) hc)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) h).symm
  exact (complexLeftUnitor_hom_naturality u).symm

end GenericSheaf

section Forms

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- **Leibniz rule of the presheaf wedge**, from `holomorphicFormDifferential_holomorphicWedge`:
`wedge ≫ d = (d ▷ P_q) ≫ wedge ≫ cast + (−1)^p (P_p ◁ d) ≫ wedge`. -/
theorem rationalWedgePresheaf_leibniz (p q : ℕ) :
    rationalWedgePresheaf X d p q ≫ rationalHolomorphicFormDifferential X d (p + q) =
      (rationalHolomorphicFormDifferential X d p ▷ rationalHolomorphicFormPresheaf X d q) ≫
          rationalWedgePresheaf X d (p + 1) q ≫
            eqToHom (congrArg (rationalHolomorphicFormPresheaf X d) (Nat.add_right_comm p 1 q)) +
        ((-1 : ℤ) ^ p) • ((rationalHolomorphicFormPresheaf X d p ◁
          rationalHolomorphicFormDifferential X d q) ≫ rationalWedgePresheaf X d p (q + 1)) := by
  refine NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| TensorProduct.ext'
    fun (a : HolomorphicForm X d U p) (b : HolomorphicForm X d U q) => ?_
  have key := holomorphicFormDifferential_holomorphicWedge (X := X) (d := d) (U := U) a b
  rw [← eqToHom_app_rationalHolomorphicFormPresheaf X d U (Nat.add_right_comm p 1 q)] at key
  exact key

/-- **Leibniz rule of the sheafified wedge** `Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ`, with the Koszul sign
`(−1)^p` and the transport along `p + 1 + q = p + q + 1`; from the presheaf rule through
`toSheafifyTensor_hom_ext_add_zsmul`. -/
theorem wedgeSheaf_leibniz (p q : ℕ) :
    wedgeSheaf X d p q ≫ rationalHolomorphicFormSheafDifferential X d (p + q) =
      (rationalHolomorphicFormSheafDifferential X d p ▷ rationalHolomorphicFormSheaf X d q) ≫
          wedgeSheaf X d (p + 1) q ≫
            eqToHom (congrArg (rationalHolomorphicFormSheaf X d) (Nat.add_right_comm p 1 q)) +
        ((-1 : ℤ) ^ p) • ((rationalHolomorphicFormSheaf X d p ◁
          rationalHolomorphicFormSheafDifferential X d q) ≫ wedgeSheaf X d p (q + 1)) := by
  have hL : toSheafifyTensor (rationalHolomorphicFormPresheaf X d p)
        (rationalHolomorphicFormPresheaf X d q) ≫ (Cup.presheafQ _).map
          (wedgeSheaf X d p q ≫ rationalHolomorphicFormSheafDifferential X d (p + q)) =
      (rationalWedgePresheaf X d p q ≫ rationalHolomorphicFormDifferential X d (p + q)) ≫
        toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
          (rationalHolomorphicFormPresheaf X d (p + q + 1)) := by
    refine (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (toSheafifyTensor_comp_wedgeSheaf X d p q)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (toSheafify_naturality _ _).symm).trans ?_
    exact (Category.assoc _ _ _).symm
  have h1 : toSheafifyTensor (rationalHolomorphicFormPresheaf X d p)
        (rationalHolomorphicFormPresheaf X d q) ≫ (Cup.presheafQ _).map
          ((rationalHolomorphicFormSheafDifferential X d p ▷ rationalHolomorphicFormSheaf X d q) ≫
            wedgeSheaf X d (p + 1) q ≫
              eqToHom (congrArg (rationalHolomorphicFormSheaf X d) (Nat.add_right_comm p 1 q))) =
      ((rationalHolomorphicFormDifferential X d p ▷ rationalHolomorphicFormPresheaf X d q) ≫
          rationalWedgePresheaf X d (p + 1) q ≫
            eqToHom (congrArg (rationalHolomorphicFormPresheaf X d) (Nat.add_right_comm p 1 q))) ≫
        toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
          (rationalHolomorphicFormPresheaf X d (p + q + 1)) := by
    refine (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (toSheafifyTensor_naturality_left
      (rationalHolomorphicFormDifferential X d p) (rationalHolomorphicFormPresheaf X d q))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (Functor.map_comp _ _ _))).trans ?_
    refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (_ ≫ ·) (congrArg (· ≫ _)
      (toSheafifyTensor_comp_wedgeSheaf X d (p + 1) q))).trans ?_
    refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (toSheafify_comp_eqToHom
      (rationalHolomorphicFormPresheaf X d) (Nat.add_right_comm p 1 q)))).trans ?_
    simp only [Category.assoc]
  have h2 : toSheafifyTensor (rationalHolomorphicFormPresheaf X d p)
        (rationalHolomorphicFormPresheaf X d q) ≫ (Cup.presheafQ _).map
          ((rationalHolomorphicFormSheaf X d p ◁ rationalHolomorphicFormSheafDifferential X d q) ≫
            wedgeSheaf X d p (q + 1)) =
      ((rationalHolomorphicFormPresheaf X d p ◁ rationalHolomorphicFormDifferential X d q) ≫
          rationalWedgePresheaf X d p (q + 1)) ≫
        toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
          (rationalHolomorphicFormPresheaf X d (p + q + 1)) := by
    refine (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (toSheafifyTensor_naturality_right
      (rationalHolomorphicFormPresheaf X d p) (rationalHolomorphicFormDifferential X d q))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (toSheafifyTensor_comp_wedgeSheaf X d p (q + 1))).trans ?_
    exact (Category.assoc _ _ _).symm
  exact toSheafifyTensor_hom_ext_add_zsmul _ _ _ _ _ _ _ hL h1 h2
    (rationalWedgePresheaf_leibniz X d p q)

/-- The Leibniz rule of the sheafified wedge in the form `ExtendMulLeibniz` asks for. -/
theorem wedgeSheaf_extendMulLeibniz :
    ExtendMulLeibniz (rationalHolomorphicDeRhamComplexNat X d) (wedgeSheaf X d) := fun p q => by
  simp only [rationalHolomorphicDeRhamComplexNat_d]
  exact wedgeSheaf_leibniz X d p q

end Forms

section Complex

/-- `curriedTensor_additive` at the analytic space (instance search misses it there). -/
local instance wsmCurriedTensorAdditive (X : Over (Spec ↧ℂ)) :
    (curriedTensor (Cup.ShQ (TopCat.of (ComplexPoint X)))).Additive :=
  curriedTensor_additive (Y := TopCat.of (ComplexPoint X))

/-- `Cup.tensorLeft_additive` at the analytic space. -/
local instance wsmTensorLeftAdditive (X : Over (Spec ↧ℂ)) :
    ∀ X₁ : Cup.ShQ (TopCat.of (ComplexPoint X)),
      ((curriedTensor (Cup.ShQ (TopCat.of (ComplexPoint X)))).obj X₁).Additive :=
  Cup.tensorLeft_additive _

/-- Tensoring on the right preserves the empty colimit, at the analytic space. -/
local instance wsmTensorRightPreservesEmpty (X : Over (Spec ↧ℂ)) :
    ∀ X₂ : Cup.ShQ (TopCat.of (ComplexPoint X)), PreservesColimit
      (Functor.empty.{0} (Cup.ShQ (TopCat.of (ComplexPoint X))))
      ((curriedTensor (Cup.ShQ (TopCat.of (ComplexPoint X)))).flip.obj X₂) :=
  fun X₂ => haveI := Cup.tensorRight_preservesColimits (TopCat.of (ComplexPoint X)) X₂
    PreservesColimitsOfShape.preservesColimit

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- `F^p Ω•_ℚ` is strictly concentrated in degrees `≥ p` (Mathlib's instance for a stupid
truncation; instance search does not unfold the `def`). -/
instance rationalHodgeFilteredComplex_isStrictlyGE (p : ℤ) :
    (rationalHodgeFilteredComplex X p).IsStrictlyGE p := by
  unfold rationalHodgeFilteredComplex
  infer_instance

/-- `F^p Ω•_ℚ` is strictly concentrated in degrees `≤ dim X`, as `Ω•_ℚ` is. -/
instance rationalHodgeFilteredComplex_isStrictlyLE (p : ℤ) :
    (rationalHodgeFilteredComplex X p).IsStrictlyLE (dim X.left) where
  isZero n hn := by
    rw [ComplexShape.notMem_range_embeddingUpIntLE_iff] at hn
    by_cases h : p ≤ n
    · have := isIso_stupidTruncInclusion_f (rationalDeRhamComplex X) h
      exact ((rationalDeRhamComplex X).isZero_of_isStrictlyLE (dim X.left) n hn).of_iso
        (@asIso _ _ _ _ _ this)
    · exact isZero_stupidTrunc_X_of_lt _ (by lia)

/-- **The wedge as a morphism of complexes** `Ω•_ℚ ⊗ Ω•_ℚ ⟶ Ω•_ℚ`, typed as the `m` of
`pairProductShQ` (left factor `A = Ω•_ℚ`, right factor `B = Ω•_ℚ`): `extendMul` of the sheafified
wedge `wedgeSheaf X (dim X.left)` on the `ℕ`-indexed complex whose extension is
`rationalDeRhamComplex X`. On the summand `Ω^p_ℚ ⊗ Ω^q_ℚ` it is `wedgeSheaf p q`
(`ιTensorObj_deRhamWedge_f`), factor order `a ∧ b`, no sign. -/
def deRhamWedge :
    (tensorRightComplex (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X)).obj
        (rationalDeRhamComplex X) ⟶ rationalDeRhamComplex X :=
  extendMul (hTK := hasTensor_shQ (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X)
    (rationalDeRhamComplex X))
    (rationalHolomorphicDeRhamComplexNat X (dim X.left)) (wedgeSheaf X (dim X.left))
    (wedgeSheaf_extendMulLeibniz X (dim X.left))

/-- The unit `ℚ_X[0] ⟶ Ω•_ℚ`, `rationalDeRhamUnit X` by definition, typed with source
`unitComplex (TopCat.of (ComplexPoint X))` (Mathlib's tensor unit of complexes) as
`pairProductShQ_naturality` and the left unitor ask. -/
def deRhamUnitShQ : unitComplex (TopCat.of (ComplexPoint X)) ⟶ rationalDeRhamComplex X :=
  rationalDeRhamUnit X

/-- **The unit law of the wedge on complexes.** `(u ⊗ 𝟙) ≫ deRhamWedge X = λ_{Ω•_ℚ}`, with
`u = rationalDeRhamUnit X` and `λ` Mathlib's left unitor of complexes
(`shQLeftUnitor_eq`). Assembled from the bidegree-`(0, q)` law `wedgeSheaf_unit_left`. Exact, no
scalar. -/
theorem deRhamWedge_unit :
    tensorHomShQ (deRhamUnitShQ X) (𝟙 (rationalDeRhamComplex X)) ≫ deRhamWedge X =
      shQLeftUnitor (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X) :=
  extendMul_unit (hTK := hasTensor_shQ (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X)
    (rationalDeRhamComplex X)) (rationalHolomorphicDeRhamComplexNat X (dim X.left))
    (wedgeSheaf X (dim X.left)) (wedgeSheaf_extendMulLeibniz X (dim X.left))
    (rationalConstantsToFormsSheaf X (dim X.left)) (by
      rw [rationalHolomorphicDeRhamComplexNat_d]
      exact rationalConstantsToFormsSheaf_comp_differential X _)
    (wedgeSheaf_unit_left X (dim X.left))

/-- **The unit law in the form `pairProductShQ_naturality` asks** at `m = unitComplexMul`,
`f = g = k = u`, `m' = deRhamWedge X`: `λ_{ℚ[0]} ≫ u = (u ⊗ u) ≫ deRhamWedge X`. -/
theorem deRhamWedge_unit_unit :
    unitComplexMul (TopCat.of (ComplexPoint X)) ≫ deRhamUnitShQ X =
      tensorHomShQ (deRhamUnitShQ X) (deRhamUnitShQ X) ≫ deRhamWedge X :=
  unitComplexMul_comp_of_unit _ _ (deRhamWedge_unit X)

/-- **The component lemma.** On the summand `Ω^p_ℚ ⊗ Ω^q_ℚ` of degree `n = p + q`,
`deRhamWedge X` is `wedgeSheaf X (dim X.left) p q`, conjugated by `extendXIso`. These components
determine `deRhamWedge X`: it is `extendMul K (wedgeSheaf X (dim X.left)) _` by definition, so
`eq_extendMul_of_components` at those arguments says that any chain map with these components is
`deRhamWedge X`. -/
theorem ιTensorObj_deRhamWedge_f (p q : ℕ) {i₁ i₂ n : ℤ}
    (h₁ : ComplexShape.embeddingUpNat.f p = i₁) (h₂ : ComplexShape.embeddingUpNat.f q = i₂)
    (hn : ComplexShape.embeddingUpNat.f (p + q) = n) (h : i₁ + i₂ = n) :
    (haveI := hasTensor_shQ (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X)
        (rationalDeRhamComplex X);
      ιTensorObj (rationalDeRhamComplex X) (rationalDeRhamComplex X) i₁ i₂ n h) ≫
        (deRhamWedge X).f n =
      (((rationalHolomorphicDeRhamComplexNat X (dim X.left)).extendXIso
          ComplexShape.embeddingUpNat h₁).hom ⊗ₘ
        ((rationalHolomorphicDeRhamComplexNat X (dim X.left)).extendXIso
          ComplexShape.embeddingUpNat h₂).hom) ≫ wedgeSheaf X (dim X.left) p q ≫
        ((rationalHolomorphicDeRhamComplexNat X (dim X.left)).extendXIso
          ComplexShape.embeddingUpNat hn).inv :=
  (ιTensorObj_extendMul_f (hTK := hasTensor_shQ (TopCat.of (ComplexPoint X))
    (rationalDeRhamComplex X) (rationalDeRhamComplex X))
    (rationalHolomorphicDeRhamComplexNat X (dim X.left)) (wedgeSheaf X (dim X.left))
    (wedgeSheaf_extendMulLeibniz X (dim X.left)) i₁ i₂ n h).trans
    (extendMulComponent_eq _ _ p q h₁ h₂ hn)

/-- **Nonvacuity.** On a variety with a complex point, `deRhamWedge X ≠ 0`: a zero wedge would
make the left unitor of `Ω•_ℚ` zero by `deRhamWedge_unit`, so `Ω•_ℚ` would be a zero complex and
`rationalDeRhamUnit X = 0`, against `Tests.rationalDeRhamUnit_ne_zero`. -/
theorem deRhamWedge_ne_zero [Nonempty (ComplexPoint X)] : deRhamWedge X ≠ 0 := by
  intro h
  have hu := deRhamWedge_unit X
  rw [h, comp_zero, shQLeftUnitor_eq] at hu
  have hZ : IsZero (rationalDeRhamComplex X) := by
    rw [IsZero.iff_id_eq_zero]
    exact (Iso.inv_hom_id _).symm.trans ((congrArg (_ ≫ ·) hu.symm).trans comp_zero)
  exact Tests.rationalDeRhamUnit_ne_zero X (hZ.eq_of_tgt _ _)

/-- **Sign separation.** On a variety with a complex point, the unit law fails for
`−deRhamWedge X`: it would give `λ = −λ`, so `𝟙 = −𝟙` on `Ω•_ℚ` and
`rationalDeRhamUnit X = −rationalDeRhamUnit X`, against `Tests.rationalDeRhamUnit_ne_neg`. -/
theorem deRhamWedge_unit_neg [Nonempty (ComplexPoint X)] :
    tensorHomShQ (deRhamUnitShQ X) (𝟙 (rationalDeRhamComplex X)) ≫ (-deRhamWedge X) ≠
      shQLeftUnitor (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X) := by
  intro h
  rw [Preadditive.comp_neg, deRhamWedge_unit, shQLeftUnitor_eq] at h
  have h1 : 𝟙 (rationalDeRhamComplex X) = -𝟙 (rationalDeRhamComplex X) := by
    have e := Iso.inv_hom_id (HomologicalComplex.leftUnitor (rationalDeRhamComplex X))
    exact e.symm.trans ((congrArg (_ ≫ ·) h.symm).trans
      ((Preadditive.comp_neg _ _).trans (congrArg Neg.neg e)))
  apply Tests.rationalDeRhamUnit_ne_neg X
  calc rationalDeRhamUnit X = rationalDeRhamUnit X ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = rationalDeRhamUnit X ≫ (-𝟙 _) := by rw [← h1]
    _ = -rationalDeRhamUnit X := by rw [Preadditive.comp_neg, Category.comp_id]

/-- **The restriction to the Hodge filtration** `F^p Ω•_ℚ ⊗ F^q Ω•_ℚ ⟶ F^{p+q} Ω•_ℚ`
(`truncMul`), typed as the `m` of `pairProductShQ` with left factor `F^p`. -/
def deRhamWedgeFiltered (p q : ℤ) :
    (tensorRightComplex (TopCat.of (ComplexPoint X)) (rationalHodgeFilteredComplex X q)).obj
        (rationalHodgeFilteredComplex X p) ⟶ rationalHodgeFilteredComplex X (p + q) :=
  truncMul (hTL := hasTensor_shQ (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X)
      (rationalDeRhamComplex X))
    (hTF := hasTensor_shQ (TopCat.of (ComplexPoint X)) (rationalHodgeFilteredComplex X p)
      (rationalHodgeFilteredComplex X q))
    (rationalDeRhamComplex X) (deRhamWedge X) p q

/-- **The restriction is compatible with the inclusions** `rationalHodgeFilteredInclusion`:
`μ_{p,q} ≫ i_{p+q} = (i_p ⊗ i_q) ≫ deRhamWedge X`, the form of the hypothesis of
`pairProductShQ_naturality`. -/
theorem deRhamWedgeFiltered_comp_inclusion (p q : ℤ) :
    deRhamWedgeFiltered X p q ≫ rationalHodgeFilteredInclusion X (p + q) =
      tensorHomShQ (rationalHodgeFilteredInclusion X p) (rationalHodgeFilteredInclusion X q) ≫
        deRhamWedge X :=
  truncMul_comp_inclusion (hTL := hasTensor_shQ (TopCat.of (ComplexPoint X))
      (rationalDeRhamComplex X) (rationalDeRhamComplex X))
    (hTF := hasTensor_shQ (TopCat.of (ComplexPoint X)) (rationalHodgeFilteredComplex X p)
      (rationalHodgeFilteredComplex X q))
    (rationalDeRhamComplex X) (deRhamWedge X) p q

end Complex

end Sheaves

end HodgeLadder
