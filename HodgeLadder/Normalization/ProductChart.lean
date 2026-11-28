module

public import HodgeLadder.General.ComplexPointProd
public import HodgeLadder.Normalization.ChartStep
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap

/-!
# Product charts on the complex points of a product over `Spec ℂ`

Rung `complex-points-prod`, second half (input of `p1p1-fibres-transversal`, sketch
`docs/sketches/cycle-class-multiplicative.md`); the homeomorphism
`pointProdHomeomorph : ComplexPoint (X ⨯ Y) ≃ₜ ComplexPoint X × ComplexPoint Y` is in
`HodgeLadder.General.ComplexPointProd`. For `X`, `Y` smooth of relative dimensions `d`, `e`, the
product of a chart of the maximal analytic atlas of `X(ℂ)` and one of `Y(ℂ)` lies in the maximal
analytic atlas of `(X ⨯ Y)(ℂ)` for upstream's charted space of dimension `d + e`
(`prodChart_mem_maximalAtlas`), and the product of upstream's own charts at `a` and `b` is such a
chart around `prod.lift a b` (`prodChart_localChart_mem_maximalAtlas`).

Literature: analytification commutes with fibre products, and products of holomorphic charts are
holomorphic charts of the product [`Serre1956` §1 to §2, `SGA1` Exp. XII §1; numbering
unverified].

## Route

Every regular function on `X ⨯ Y` is, near a point, a quotient of polynomials in pullbacks of
regular functions on affine opens of `X` and `Y` (`analyticAt_evaluate_prodLift`, from
`closure_range_union_eq_top`). With upstream's `analyticAt_localChart_symm_evaluate` and
`analyticAt_localChart_symm_map`, Mathlib's `OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn`
concludes.

## Conventions

Coordinate order: the coordinates of the first factor come first,
`prodChart X Y φ ψ z = Fin.append (φ (map prod.fst z)) (ψ (map prod.snd z))`
(`prodChart_apply`), through `finAppendEquiv d e : ℂ^d × ℂ^e ≃L[ℂ] ℂ^(d + e)`. The relative
dimension of `X ⨯ Y` is `d + e` (`smoothOfRelativeDimension_prod`). No sign or conjugation enters;
conventions row "Complex points of a product and product charts" in `docs/conventions.md`.

## Main definitions

* `HodgeLadder.ComplexPointProd.finAppendEquiv`, `HodgeLadder.ComplexPointProd.prodChart`

## Main results

* `HodgeLadder.ComplexPointProd.prodChart_mem_maximalAtlas`: product charts are analytic charts.
* `HodgeLadder.ComplexPointProd.prodChart_localChart_mem_maximalAtlas`: the product of upstream's
  charts at `a` and `b` is in the maximal atlas, and its source contains `prod.lift a b`.
* `HodgeLadder.ComplexPointProd.finAppendEquiv_apply`, `prodChart_apply`, `prodChart_symm_apply`,
  `prodChart_source`, `prodChart_target`.
* General lemmas: `analyticAt_evaluate_symm_of_mem_maximalAtlas`,
  `analyticAt_chart_map_localChart_symm`, `analyticAt_evaluate_prodLift`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology AlgebraicGeometry AlgebraicGeometry.Point
open AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff

namespace HodgeLadder.ComplexPointProd

variable (X Y : Over (Spec ↧ℂ))

/-- The linear identification `ℂ^d × ℂ^e ≃ ℂ^(d + e)` that puts the first block first
(`finAppendEquiv_apply`). -/
def finAppendEquiv (d e : ℕ) : ((Fin d → ℂ) × (Fin e → ℂ)) ≃L[ℂ] (Fin (d + e) → ℂ) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin e) ℂ ℂ).symm.trans
    (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)).toContinuousLinearEquiv

/-- `finAppendEquiv` is `Fin.append`. -/
theorem finAppendEquiv_apply {d e : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ) :
    finAppendEquiv d e (u, v) = Fin.append u v := by
  ext i
  simp only [finAppendEquiv, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.trans_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]
  · simp [LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

/-- Evaluation of a regular function is analytic in every chart of the maximal analytic atlas, read
through the inverse chart. -/
theorem analyticAt_evaluate_symm_of_mem_maximalAtlas {Z : Over (Spec ↧ℂ)} {d : ℕ}
    [SmoothOfRelativeDimension d Z.hom] {φ : OpenPartialHomeomorph (ComplexPoint Z) (Fin d → ℂ)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint Z))
    {u : Fin d → ℂ} (hu : u ∈ φ.target) (V : Z.left.Opens) (s : Γ(Z.left, V))
    (hV : φ.symm u ∈ overOpen V) :
    AnalyticAt ℂ (fun u ↦ evaluate V s (φ.symm u)) u := by
  set a := φ.symm u
  set c := localChart Z d a
  have ha : a ∈ c.source := mem_localChart_source Z d a
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint Z) :=
    IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) a
  have hT : φ.symm.trans c ∈ contDiffGroupoid ω 𝓘(ℂ, Fin d → ℂ) :=
    IsManifold.compatible_of_mem_maximalAtlas hφ hc
  have h1 := Normalization.analyticAt_of_mem_contDiffGroupoid hT (v := u) ⟨hu, ha⟩
  have h2 := analyticAt_localChart_symm_evaluate Z d a (w := c a) (c.map_source ha) V s
    (by rw [c.left_inv ha]; exact hV)
  have h3 : AnalyticAt ℂ (fun v ↦ evaluate V s (c.symm (c (φ.symm v)))) u := h2.comp_of_eq h1 rfl
  apply h3.congr
  filter_upwards [φ.continuousAt_symm hu (c.open_source.mem_nhds ha)] with v hv
  exact congrArg (evaluate V s) (c.left_inv hv)

/-- A morphism of smooth complex schemes, read from upstream's chart at a point into a chart of the
maximal analytic atlas of the target, is analytic at the point. -/
theorem analyticAt_chart_map_localChart_symm {P Z : Over (Spec ↧ℂ)} {n d : ℕ}
    [SmoothOfRelativeDimension n P.hom] [SmoothOfRelativeDimension d Z.hom] (f : P ⟶ Z)
    {φ : OpenPartialHomeomorph (ComplexPoint Z) (Fin d → ℂ)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint Z))
    (w : ComplexPoint P) (hw : map f w ∈ φ.source) :
    AnalyticAt ℂ (fun v ↦ φ (map f ((localChart P n w).symm v))) (localChart P n w w) := by
  set c := localChart P n w
  set cZ := localChart Z d (map f w)
  have hw' : w ∈ c.source := mem_localChart_source P n w
  have hcw : c w ∈ c.target := c.map_source hw'
  have hfw : map f w ∈ cZ.source := mem_localChart_source Z d _
  have h1 := analyticAt_localChart_symm_map P Z f n d w hcw (by rw [c.left_inv hw']; exact hfw)
  have hcZ : cZ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint Z) :=
    IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) (map f w)
  have hT : cZ.symm.trans φ ∈ contDiffGroupoid ω 𝓘(ℂ, Fin d → ℂ) :=
    IsManifold.compatible_of_mem_maximalAtlas hcZ hφ
  have h2 := Normalization.analyticAt_of_mem_contDiffGroupoid hT (v := cZ (map f w))
    ⟨cZ.map_source hfw, by simpa [cZ.left_inv hfw] using hw⟩
  have h3 : AnalyticAt ℂ (fun v ↦ φ (cZ.symm (cZ (map f (c.symm v))))) (c w) :=
    h2.comp_of_eq h1 (by simp only [c.left_inv hw'])
  apply h3.congr
  have hcont : ContinuousAt (fun v ↦ map f (c.symm v)) (c w) :=
    (continuous_map f).continuousAt.comp (c.continuousAt_symm hcw)
  have hnhds : (fun v ↦ map f (c.symm v)) ⁻¹' cZ.source ∈ 𝓝 (c w) :=
    hcont (by simpa only [c.left_inv hw'] using cZ.open_source.mem_nhds hfw)
  filter_upwards [hnhds] with v hv
  exact congrArg φ (cZ.left_inv hv)

/-- **The analytic core.** Let `α` and `β` be maps from a complex normed space to the complex points
of `X` and `Y`, continuous at `x₀`, along which every regular function evaluates analytically at
`x₀`. Then every regular function on `X ⨯ Y` evaluates analytically at `x₀` along
`prod.lift α β`. Near `x₀` the section is a quotient of global sections of a product of affine
opens, and these are generated by the sections of the factors. -/
theorem analyticAt_evaluate_prodLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {α : E → ComplexPoint X} {β : E → ComplexPoint Y} {x₀ : E}
    (hαc : ContinuousAt α x₀) (hβc : ContinuousAt β x₀)
    (hα : ∀ (V : X.left.Opens) (s : Γ(X.left, V)), α x₀ ∈ overOpen V →
      AnalyticAt ℂ (fun x ↦ evaluate V s (α x)) x₀)
    (hβ : ∀ (V : Y.left.Opens) (s : Γ(Y.left, V)), β x₀ ∈ overOpen V →
      AnalyticAt ℂ (fun x ↦ evaluate V s (β x)) x₀)
    (V : (X ⨯ Y).left.Opens) (t : Γ((X ⨯ Y).left, V))
    (hV : (prod.lift (α x₀) (β x₀) : ComplexPoint (X ⨯ Y)) ∈ overOpen V) :
    AnalyticAt ℂ (fun x ↦ evaluate V t (prod.lift (α x) (β x) : ComplexPoint (X ⨯ Y))) x₀ := by
  classical
  obtain ⟨U₁, hU₁, ha, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := (α x₀).underlying) (U := ⊤) trivial
  obtain ⟨U₂, hU₂, hb, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := (β x₀).underlying) (U := ⊤) trivial
  have : IsAffine (openScheme X U₁).left := hU₁
  have : IsAffine (openScheme Y U₂).left := hU₂
  have hαU : ∀ᶠ x in 𝓝 x₀, α x ∈ overOpen U₁ := hαc ((isOpen_overOpen U₁).mem_nhds ha)
  have hβU : ∀ᶠ x in 𝓝 x₀, β x ∈ overOpen U₂ := hβc ((isOpen_overOpen U₂).mem_nhds hb)
  let α' : E → ComplexPoint (openScheme X U₁) := fun x ↦
    if h : α x ∈ overOpen U₁ then (openEquiv X U₁).symm ⟨α x, h⟩
    else (openEquiv X U₁).symm ⟨α x₀, ha⟩
  let β' : E → ComplexPoint (openScheme Y U₂) := fun x ↦
    if h : β x ∈ overOpen U₂ then (openEquiv Y U₂).symm ⟨β x, h⟩
    else (openEquiv Y U₂).symm ⟨β x₀, hb⟩
  have hα' : ∀ x, α x ∈ overOpen U₁ → map (openInclusion X U₁) (α' x) = α x := fun x h ↦ by
    simp only [α', h, ↓reduceDIte]
    exact congrArg Subtype.val ((openEquiv X U₁).apply_symm_apply ⟨α x, h⟩)
  have hβ' : ∀ x, β x ∈ overOpen U₂ → map (openInclusion Y U₂) (β' x) = β x := fun x h ↦ by
    simp only [β', h, ↓reduceDIte]
    exact congrArg Subtype.val ((openEquiv Y U₂).apply_symm_apply ⟨β x, h⟩)
  let m := prod.map (openInclusion X U₁) (openInclusion Y U₂)
  let q : E → ComplexPoint (openScheme X U₁ ⨯ openScheme Y U₂) := fun x ↦ prod.lift (α' x) (β' x)
  have hq : ∀ x, α x ∈ overOpen U₁ → β x ∈ overOpen U₂ → map m (q x) = prod.lift (α x) (β x) := by
    intro x h1 h2
    apply prod.hom_ext
    · simpa [m, q, map] using hα' x h1
    · simpa [m, q, map] using hβ' x h2
  have hglob : ∀ g : Γ((openScheme X U₁ ⨯ openScheme Y U₂).left, ⊤),
      AnalyticAt ℂ (fun x ↦ evaluate ⊤ g (q x)) x₀ := by
    intro g
    have hg : g ∈ Subring.closure
        (Set.range (prod.fst : openScheme X U₁ ⨯ openScheme Y U₂ ⟶ _).left.appTop ∪
          Set.range (prod.snd : openScheme X U₁ ⨯ openScheme Y U₂ ⟶ _).left.appTop) :=
      (closure_range_union_eq_top (isPushout_appTop_of_isPullback
        (isPullback_prod (openScheme X U₁) (openScheme Y U₂)))) ▸ Subring.mem_top g
    induction hg using Subring.closure_induction with
    | mem g hg =>
      rcases hg with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · have h := hα (U₁.ι ''ᵁ ⊤) ((U₁.ι.appIso ⊤).inv y) (by simpa [overOpen] using ha)
        apply h.congr
        filter_upwards [hαU] with x hx
        rw [evaluate_top_appTop, ← hα' x hx, evaluate_openEquiv]
        simp [q, map]
      · have h := hβ (U₂.ι ''ᵁ ⊤) ((U₂.ι.appIso ⊤).inv y) (by simpa [overOpen] using hb)
        apply h.congr
        filter_upwards [hβU] with x hx
        rw [evaluate_top_appTop, ← hβ' x hx, evaluate_openEquiv]
        simp [q, map]
    | zero => simpa [evaluate_top_eq_appTop] using analyticAt_const
    | one => simpa [evaluate_top_one] using analyticAt_const
    | add s t _ _ hs ht => simp only [evaluate_top_add]; exact hs.add ht
    | neg s _ hs => simp only [evaluate_top_neg]; exact hs.neg
    | mul s t _ _ hs ht => simp only [evaluate_top_mul]; exact hs.mul ht
  have hq0V : q x₀ ∈ overOpen (m.left ⁻¹ᵁ V) :=
    (mem_overOpen_map_iff m (q x₀) V).mp (by rw [hq x₀ ha hb]; exact hV)
  obtain ⟨f, hfV, hf0⟩ := (isAffineOpen_top (openScheme X U₁ ⨯ openScheme Y U₂).left
    ).exists_basicOpen_le (V := m.left ⁻¹ᵁ V) ⟨(q x₀).underlying, hq0V⟩ trivial
  obtain ⟨k, a, hka⟩ := exists_evaluate_affine_basicOpen_eq_div
    (X := openScheme X U₁ ⨯ openScheme Y U₂) f
    ((openScheme X U₁ ⨯ openScheme Y U₂).left.presheaf.map (homOfLE hfV).op (m.left.app V t))
  have hmem : ∀ x, q x ∈ overOpen ((openScheme X U₁ ⨯ openScheme Y U₂).left.basicOpen f) ↔
      evaluate ⊤ f (q x) ≠ 0 :=
    fun x ↦ mem_overOpen_basicOpen_iff_evaluate_ne_zero (U := ⊤) f (q x) trivial
  have hf0' : evaluate ⊤ f (q x₀) ≠ 0 := (hmem x₀).mp hf0
  have hrat : AnalyticAt ℂ (fun x ↦ evaluate ⊤ a (q x) / evaluate ⊤ f (q x) ^ k) x₀ :=
    (hglob a).div ((hglob f).pow k) (pow_ne_zero k hf0')
  apply hrat.congr
  filter_upwards [hαU, hβU, (hglob f).continuousAt.eventually_ne hf0'] with x h1 h2 h3
  have hxf := (hmem x).mpr h3
  rw [← hq x h1 h2, evaluate_map, evaluate_res hfV _ _ hxf, hka _ hxf]

variable {d e : ℕ}

/-- The product chart: `φ` on the first factor, `ψ` on the second, the coordinates of `φ` first
(`prodChart_apply`). -/
def prodChart (φ : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
    (ψ : OpenPartialHomeomorph (ComplexPoint Y) (Fin e → ℂ)) :
    OpenPartialHomeomorph (ComplexPoint (X ⨯ Y)) (Fin (d + e) → ℂ) :=
  ((pointProdHomeomorph X Y).toOpenPartialHomeomorph.trans (φ.prod ψ)).trans
    (finAppendEquiv d e).toHomeomorph.toOpenPartialHomeomorph

variable {X Y}

/-- The product chart appends the coordinates of `φ` at the first projection and those of `ψ` at
the second. -/
theorem prodChart_apply (φ : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
    (ψ : OpenPartialHomeomorph (ComplexPoint Y) (Fin e → ℂ)) (z : ComplexPoint (X ⨯ Y)) :
    prodChart X Y φ ψ z = Fin.append (φ (map prod.fst z)) (ψ (map prod.snd z)) := by
  simp [prodChart, ← finAppendEquiv_apply]

/-- The inverse of the product chart is `prod.lift` of the two inverse charts. -/
theorem prodChart_symm_apply (φ : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
    (ψ : OpenPartialHomeomorph (ComplexPoint Y) (Fin e → ℂ)) (v : Fin (d + e) → ℂ) :
    (prodChart X Y φ ψ).symm v =
      prod.lift (φ.symm ((finAppendEquiv d e).symm v).1) (ψ.symm ((finAppendEquiv d e).symm v).2) :=
  rfl

/-- The source of the product chart: both projections in the sources of the factor charts. -/
theorem prodChart_source (φ : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
    (ψ : OpenPartialHomeomorph (ComplexPoint Y) (Fin e → ℂ)) :
    (prodChart X Y φ ψ).source = {z | map prod.fst z ∈ φ.source ∧ map prod.snd z ∈ ψ.source} := by
  ext z; simp [prodChart]

/-- The target of the product chart. -/
theorem prodChart_target (φ : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
    (ψ : OpenPartialHomeomorph (ComplexPoint Y) (Fin e → ℂ)) :
    (prodChart X Y φ ψ).target = (finAppendEquiv d e).symm ⁻¹' (φ.target ×ˢ ψ.target) := by
  ext v; simp [prodChart]

/-- **Rung `complex-points-prod`, the atlas.** For `X` and `Y` smooth of relative dimensions `d`
and `e` over `ℂ`, the product of a chart of the maximal analytic atlas of `X(ℂ)` and one of
`Y(ℂ)`, read through `pointProdHomeomorph` and with the coordinates of the first factor first, lies
in the maximal analytic atlas of `(X ⨯ Y)(ℂ)` for upstream's charted space of dimension `d + e`. -/
theorem prodChart_mem_maximalAtlas [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom]
    {φ : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)}
    {ψ : OpenPartialHomeomorph (ComplexPoint Y) (Fin e → ℂ)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X))
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin e → ℂ) ω (ComplexPoint Y)) :
    prodChart X Y φ ψ ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (d + e) → ℂ) ω (ComplexPoint (X ⨯ Y)) := by
  set p := prodChart X Y φ ψ
  set L := finAppendEquiv d e
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · intro w hw
    have hw' : map prod.fst w ∈ φ.source ∧ map prod.snd w ∈ ψ.source := by
      simpa [p, prodChart_source] using hw
    refine (Normalization.contMDiffAt_of_analyticAt_chart (p.continuousAt hw) ?_
      ).contMDiffWithinAt
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id]
    change AnalyticAt ℂ (fun v ↦ p ((localChart (X ⨯ Y) (d + e) w).symm v))
      (localChart (X ⨯ Y) (d + e) w w)
    have h1 := analyticAt_chart_map_localChart_symm (n := d + e) prod.fst hφ w hw'.1
    have h2 := analyticAt_chart_map_localChart_symm (n := d + e) prod.snd hψ w hw'.2
    have h := (L.toContinuousLinearMap.analyticAt _).comp (h1.prod h2)
    refine h.congr (Filter.Eventually.of_forall fun v ↦ ?_)
    simp [p, prodChart, L]
  · intro v hv
    have hv' : ((L.symm v).1 ∈ φ.target) ∧ (L.symm v).2 ∈ ψ.target := by
      simpa [p, L, prodChart_target] using hv
    refine (Normalization.contMDiffAt_of_analyticAt_chart (p.continuousAt_symm hv) ?_
      ).contMDiffWithinAt
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      id]
    set c := localChart (X ⨯ Y) (d + e) (p.symm v)
    change AnalyticAt ℂ (fun u ↦ c (p.symm u)) v
    have hs : p.symm v ∈ c.source := mem_localChart_source _ _ _
    refine AnalyticAt.pi fun i ↦ ?_
    let D := localEtaleCoordinates (X ⨯ Y) (d + e) (p.symm v)
    have hV : p.symm v ∈ overOpen D.ambientCoordinateOpen := by
      have hmem := mem_coordinateNeighborhood_of_mem_localChart_source _ (d + e) (p.symm v) _ hs
      simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top]
        using hmem
    let ℓ₁ : (Fin (d + e) → ℂ) →L[ℂ] (Fin d → ℂ) :=
      (ContinuousLinearMap.fst ℂ _ _).comp L.symm.toContinuousLinearMap
    let ℓ₂ : (Fin (d + e) → ℂ) →L[ℂ] (Fin e → ℂ) :=
      (ContinuousLinearMap.snd ℂ _ _).comp L.symm.toContinuousLinearMap
    have hK := analyticAt_evaluate_prodLift X Y (α := fun u ↦ φ.symm (ℓ₁ u))
      (β := fun u ↦ ψ.symm (ℓ₂ u)) (x₀ := v)
      ((φ.continuousAt_symm hv'.1).comp (f := fun u ↦ ℓ₁ u) ℓ₁.continuous.continuousAt)
      ((ψ.continuousAt_symm hv'.2).comp (f := fun u ↦ ℓ₂ u) ℓ₂.continuous.continuousAt)
      (fun V s hs ↦ (analyticAt_evaluate_symm_of_mem_maximalAtlas hφ hv'.1 V s hs).comp
        (f := fun u ↦ ℓ₁ u) (ℓ₁.analyticAt v))
      (fun V s hs ↦ (analyticAt_evaluate_symm_of_mem_maximalAtlas hψ hv'.2 V s hs).comp
        (f := fun u ↦ ℓ₂ u) (ℓ₂.analyticAt v))
      _ (D.ambientCoordinateSection i) hV
    apply hK.congr
    filter_upwards [p.continuousAt_symm hv (c.open_source.mem_nhds hs)] with u hu
    exact (localChart_apply_component_eq_evaluate _ (d + e) (p.symm v) _ hu i).symm

/-- Non-vacuity: the product of upstream's own charts at `a` and `b` lies in the maximal analytic
atlas of `(X ⨯ Y)(ℂ)`, and its source contains `prod.lift a b`. -/
theorem prodChart_localChart_mem_maximalAtlas [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] (a : ComplexPoint X) (b : ComplexPoint Y) :
    prodChart X Y (localChart X d a) (localChart Y e b) ∈
        IsManifold.maximalAtlas 𝓘(ℂ, Fin (d + e) → ℂ) ω (ComplexPoint (X ⨯ Y)) ∧
      (prod.lift a b : ComplexPoint (X ⨯ Y)) ∈
        (prodChart X Y (localChart X d a) (localChart Y e b)).source := by
  refine ⟨prodChart_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) a)
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, Fin e → ℂ)) (n := ω) b), ?_⟩
  rw [prodChart_source]
  exact ⟨by simpa [map] using mem_localChart_source X d a,
    by simpa [map] using mem_localChart_source Y e b⟩


end HodgeLadder.ComplexPointProd
