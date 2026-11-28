module

public import HodgeLadder.General.ProjQuotient
public import LefschetzPort.Oka.AlgebraicGeometry.ProjectiveSpace.Basic

/-!
# Hypersurfaces in projective space

For a homogeneous polynomial `F ∈ R[X₀, …, Xₙ]` of degree `d`, the hypersurface
`V₊(F) = Proj (R[X₀, …, Xₙ] ⧸ (F))` (`Hypersurface.scheme`) comes with the closed immersion
`ι : V₊(F) ⟶ ℙₒ(n; R)` into Oka's projective space (`HodgeLadder.ProjQuotient.quotι`). Its open
subscheme over the standard open `U i = D₊(Xᵢ)` is `Spec (R[Y₀, …, Yₙ₋₁] ⧸ (dehomogenize i F))`
(`chartIso`), and this chart lies over Oka's standard chart `ProjectiveSpace.chart i` through the
quotient map (`chartIso_inv_ι`). The ring isomorphism behind it is `awayEquiv`:
`(a mod F) / (Xᵢ mod F)ᵐ ↦ dehomogenize i a mod (dehomogenize i F)`, inverse to
`Yⱼ ↦ X_{i.succAbove j} / Xᵢ`.

## Main definitions

* `HodgeLadder.Hypersurface.ideal`, `grading`, `scheme`, `ι`, `π`
* `HodgeLadder.Hypersurface.chartIdeal`, `ChartRing`, `awayπ`, `fromAway`, `toAway`, `awayEquiv`
* `HodgeLadder.Hypersurface.chartIso`, `chartPoint`

## Main results

* `HodgeLadder.Hypersurface.awayπ_surjective`, `fromAway_awayπ`, `ι_preimage_U`
* `HodgeLadder.Hypersurface.chartIso_inv_ι`, `chartPoint_ι`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open scoped AlgebraicGeometry.ProjectiveSpace

namespace HodgeLadder.Hypersurface

universe u

variable {n : ℕ} {R : Type u} [CommRing R] {d : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R

/-- The homogeneous ideal `(F)` of a homogeneous polynomial `F`. -/
def ideal (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ 𝒜 d) : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.span {F}, Ideal.homogeneous_span 𝒜 _ (by
    rintro x rfl
    exact ⟨d, hF⟩)⟩

/-- The underlying ideal of `ideal F hF` is `(F)`. -/
theorem ideal_toIdeal (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ 𝒜 d) :
    (ideal F hF).toIdeal = Ideal.span {F} := rfl

/-- The quotient grading on `R[X₀, …, Xₙ] ⧸ (F)`. -/
abbrev grading (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ 𝒜 d) :
    ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R ⧸ (ideal F hF).toIdeal) :=
  ProjQuotient.grading 𝒜 (ideal F hF)

/-- The hypersurface `V₊(F) = Proj (R[X₀, …, Xₙ] ⧸ (F))`. -/
abbrev scheme (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ 𝒜 d) : Scheme.{u} := Proj (grading F hF)

/-- The closed immersion `V₊(F) ⟶ ℙₒ(n; R)`. -/
abbrev ι (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ 𝒜 d) : scheme F hF ⟶ ℙₒ(n; R) :=
  ProjQuotient.quotι 𝒜 (ideal F hF)

/-- The class of a polynomial modulo `F`. -/
abbrev π (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ 𝒜 d) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin (n + 1)) R ⧸ (ideal F hF).toIdeal :=
  Ideal.Quotient.mk _

/-- The class of `Xᵢ` has degree one in the quotient grading. -/
theorem π_X_mem (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ 𝒜 d) (i : Fin (n + 1)) :
    π F hF (X i) ∈ grading F hF 1 :=
  ProjQuotient.mk_mem_grading 𝒜 _ (X_mem_homogeneousSubmodule_one i)

section Chart

variable (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) R d)
  (i : Fin (n + 1))

/-- The ideal of the chart `Xᵢ ≠ 0`: the dehomogenization of `F` at `Xᵢ`. -/
abbrev chartIdeal (F : MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)) :
    Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span {dehomogenize R i F}

/-- The coordinate ring `R[Y₀, …, Yₙ₋₁] ⧸ (dehomogenize i F)` of the chart `Xᵢ ≠ 0`. -/
abbrev ChartRing (F : MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)) : Type u :=
  MvPolynomial (Fin n) R ⧸ chartIdeal F i

/-- Dehomogenization at `Xᵢ` maps `(F)` into `(dehomogenize i F)`. -/
theorem dehomogenize_mem_chartIdeal {a : MvPolynomial (Fin (n + 1)) R}
    (ha : a ∈ (ideal F hF).toIdeal) : dehomogenize R i a ∈ chartIdeal F i := by
  rw [ideal_toIdeal, Ideal.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- Dehomogenization at `Xᵢ`, on the quotient by `F`. -/
def dehomQ : (MvPolynomial (Fin (n + 1)) R ⧸ (ideal F hF).toIdeal) →+* ChartRing F i :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (dehomogenize R i).toRingHom)
    fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr (dehomogenize_mem_chartIdeal F hF i ha)

/-- `dehomQ` on the class of `a` is the class of `dehomogenize i a`. -/
theorem dehomQ_π (a : MvPolynomial (Fin (n + 1)) R) :
    dehomQ F hF i (π F hF a) = Ideal.Quotient.mk _ (dehomogenize R i a) := rfl

/-- `dehomQ` sends the class of `Xᵢ` to `1`. -/
theorem dehomQ_π_X_self : dehomQ F hF i (π F hF (X i)) = 1 := by
  rw [dehomQ_π, dehomogenize_X_self, map_one]

/-- The degree-zero localization map `A_(Xᵢ) → (A ⧸ F)_(Xᵢ)`. -/
def awayπ : Away 𝒜 (X i) →+* Away (grading F hF) (π F hF (X i)) :=
  Away.map (ProjQuotient.mkGraded 𝒜 (ideal F hF)) (X i)

/-- `awayπ` on `a / Xᵢᵐ` is `(a mod F) / (Xᵢ mod F)ᵐ`. -/
theorem awayπ_mk (m : ℕ) (a : MvPolynomial (Fin (n + 1)) R) (ha : a ∈ 𝒜 (m • 1)) :
    awayπ F hF i (Away.mk 𝒜 (X_mem_homogeneousSubmodule_one i) m a ha) =
      Away.mk (grading F hF) (π_X_mem F hF i) m (π F hF a)
        (ProjQuotient.mk_mem_grading 𝒜 _ ha) :=
  Away.map_mk _ _ _ _ _ _

/-- `awayπ` is surjective: every homogeneous class lifts to a homogeneous polynomial of the same
degree. -/
theorem awayπ_surjective : Function.Surjective (awayπ F hF i) :=
  ProjQuotient.away_map_surjective _ (ProjQuotient.mkGraded_surjOn 𝒜 _)
    (X_mem_homogeneousSubmodule_one i)

/-- The chart map `(A ⧸ F)_(Xᵢ) → R[Y] ⧸ (dehomogenize i F)`: `a / Xᵢᵐ ↦ dehomogenize i a`. -/
def fromAway : Away (grading F hF) (π F hF (X i)) →+* ChartRing F i :=
  (Localization.awayLift (dehomQ F hF i) (π F hF (X i))
    (isUnit_iff_exists_inv.mpr ⟨1, by rw [dehomQ_π_X_self, one_mul]⟩)).comp
      (algebraMap _ (Localization.Away (π F hF (X i))))

/-- `fromAway` on `(a mod F) / (Xᵢ mod F)ᵐ` is the class of `dehomogenize i a`. -/
theorem fromAway_awayπ_mk (m : ℕ) (a : MvPolynomial (Fin (n + 1)) R) (ha : a ∈ 𝒜 (m • 1)) :
    fromAway F hF i (awayπ F hF i (Away.mk 𝒜 (X_mem_homogeneousSubmodule_one i) m a ha)) =
      Ideal.Quotient.mk _ (dehomogenize R i a) := by
  rw [awayπ_mk]
  simp only [fromAway, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  rw [Localization.awayLift_mk (v := 1) (hv := by rw [dehomQ_π_X_self, one_mul])]
  rw [one_pow, mul_one, dehomQ_π]

/-- The degree-zero localization of `F` at `Xᵢ` vanishes in `(A ⧸ F)_(Xᵢ)`. -/
theorem awayπ_toAwayX_dehomogenize :
    awayπ F hF i (toAwayX R i (dehomogenize R i F)) = 0 := by
  have hF' : F ∈ 𝒜 (d • 1) := by rwa [smul_eq_mul, mul_one]
  rw [← fromAwayX_mk i d F hF', toAwayX_fromAwayX, awayπ_mk]
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.val_zero]
  have : π F hF F = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [this, Localization.mk_zero]

/-- The inverse chart map `R[Y] ⧸ (dehomogenize i F) → (A ⧸ F)_(Xᵢ)`,
`Yⱼ ↦ X_{i.succAbove j} / Xᵢ`. -/
def toAway : ChartRing F i →+* Away (grading F hF) (π F hF (X i)) :=
  Ideal.Quotient.lift _ ((awayπ F hF i).comp (toAwayX R i)) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [RingHom.comp_apply, map_mul, map_mul, awayπ_toAwayX_dehomogenize, zero_mul]

/-- `toAway` on the class of `p` is `awayπ (toAwayX i p)`. -/
theorem toAway_mk (p : MvPolynomial (Fin n) R) :
    toAway F hF i (Ideal.Quotient.mk _ p) = awayπ F hF i (toAwayX R i p) := rfl

/-- `fromAway` is a left inverse of `toAway`. -/
theorem fromAway_toAway (q : ChartRing F i) : fromAway F hF i (toAway F hF i q) = q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨m, a, ha, hz⟩ := Away.mk_surjective 𝒜 (X_mem_homogeneousSubmodule_one i)
    (toAwayX R i p)
  rw [toAway_mk, ← hz, fromAway_awayπ_mk]
  congr 1
  rw [← fromAwayX_mk i m a ha, hz, fromAwayX_toAwayX]

/-- `fromAway` is a right inverse of `toAway`. -/
theorem toAway_fromAway (w : Away (grading F hF) (π F hF (X i))) :
    toAway F hF i (fromAway F hF i w) = w := by
  obtain ⟨z, rfl⟩ := awayπ_surjective F hF i w
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (X_mem_homogeneousSubmodule_one i) z
  rw [fromAway_awayπ_mk, toAway_mk, ← fromAwayX_mk i m a ha, toAwayX_fromAwayX]

/-- **The chart ring of a hypersurface.** `(R[X₀, …, Xₙ] ⧸ (F))_(Xᵢ) ≃ R[Y] ⧸ (dehomogenize i F)`,
with `X_{i.succAbove j} / Xᵢ ↦ Yⱼ`. -/
def awayEquiv : Away (grading F hF) (π F hF (X i)) ≃+* ChartRing F i where
  toFun := fromAway F hF i
  invFun := toAway F hF i
  left_inv := toAway_fromAway F hF i
  right_inv := fromAway_toAway F hF i
  map_mul' := map_mul _
  map_add' := map_add _

/-- `fromAway ∘ awayπ` is the quotient map after Oka's dehomogenization `fromAwayX i`. -/
theorem fromAway_awayπ (z : Away 𝒜 (X i)) :
    fromAway F hF i (awayπ F hF i z) = Ideal.Quotient.mk _ (fromAwayX R i z) := by
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (X_mem_homogeneousSubmodule_one i) z
  rw [fromAway_awayπ_mk, fromAwayX_mk]

/-- The open `Xᵢ ≠ 0` of the hypersurface is `D₊(Xᵢ mod F)`. -/
theorem ι_preimage_U :
    ι F hF ⁻¹ᵁ ProjectiveSpace.U n R i = Proj.basicOpen (grading F hF) (π F hF (X i)) := rfl

/-- **The chart `Xᵢ ≠ 0` of the hypersurface** `V₊(F)`: the open subscheme over the standard open
`U i` of `ℙₒ(n; R)` is `Spec (R[Y₀, …, Yₙ₋₁] ⧸ (dehomogenize i F))`. -/
def chartIso :
    (ι F hF ⁻¹ᵁ ProjectiveSpace.U n R i).toScheme ≅ Spec (.of (ChartRing F i)) :=
  Proj.basicOpenIsoSpec (grading F hF) (π F hF (X i)) (π_X_mem F hF i) Nat.one_pos ≪≫
    Scheme.Spec.mapIso (awayEquiv F hF i).toCommRingCatIso.symm.op

/-- The chart of the hypersurface lies over the standard chart of `ℙₒ(n; R)` through the quotient
map `R[Y] → R[Y] ⧸ (dehomogenize i F)`. -/
theorem chartIso_inv_ι :
    (chartIso F hF i).inv ≫ (ι F hF ⁻¹ᵁ ProjectiveSpace.U n R i).ι ≫ ι F hF =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal F i))) ≫
        ProjectiveSpace.chart i := by
  have h1 : (chartIso F hF i).inv = Spec.map (CommRingCat.ofHom (fromAway F hF i)) ≫
      (Proj.basicOpenIsoSpec (grading F hF) (π F hF (X i)) (π_X_mem F hF i) Nat.one_pos).inv :=
    rfl
  rw [h1]
  change Spec.map (CommRingCat.ofHom (fromAway F hF i)) ≫
      ((Proj.basicOpenIsoSpec (grading F hF) (π F hF (X i)) (π_X_mem F hF i) Nat.one_pos).inv ≫
        (Proj.basicOpen (grading F hF) (π F hF (X i))).ι) ≫
          Proj.map (ProjQuotient.mkGraded 𝒜 (ideal F hF)) _ = _
  rw [Proj.basicOpenIsoSpec_inv_ι]
  erw [Proj.awayι_comp_map (ProjQuotient.mkGraded 𝒜 (ideal F hF)) _ Nat.one_pos (X i)
    (X_mem_homogeneousSubmodule_one i)]
  change Spec.map (CommRingCat.ofHom (fromAway F hF i)) ≫
      Spec.map (CommRingCat.ofHom (awayπ F hF i)) ≫ _ = _
  rw [ProjectiveSpace.chart, ← Spec.map_comp_assoc, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext z
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, awayXEquiv_symm_apply]
  exact fromAway_awayπ F hF i z

/-- The `S`-point of the hypersurface in the chart `Xᵢ ≠ 0` with affine coordinates `φ`. -/
def chartPoint {S : Type u} [CommRing S] (φ : ChartRing F i →+* S) :
    Spec (.of S) ⟶ scheme F hF :=
  Spec.map (CommRingCat.ofHom φ) ≫ (chartIso F hF i).inv ≫
    (ι F hF ⁻¹ᵁ ProjectiveSpace.U n R i).ι

/-- A chart point of the hypersurface, in `ℙₒ(n; R)`: the point of the standard chart with the
same affine coordinates. -/
theorem chartPoint_ι {S : Type u} [CommRing S] (φ : ChartRing F i →+* S) :
    chartPoint F hF i φ ≫ ι F hF =
      Spec.map (CommRingCat.ofHom (φ.comp (Ideal.Quotient.mk _))) ≫ ProjectiveSpace.chart i := by
  rw [chartPoint, Category.assoc, Category.assoc, chartIso_inv_ι, ← Spec.map_comp_assoc]
  rfl

end Chart

end HodgeLadder.Hypersurface
