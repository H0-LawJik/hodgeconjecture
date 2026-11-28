module

public import HodgeLadder.Rect.Winding
public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# The argument principle on a rectangle

For `f` meromorphic on `ℂ` with finite order at every point, analytic and nonzero on the
boundary `[[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)` of the rectangle
with lower-left corner `z` and upper-right corner `w`, the counterclockwise boundary integral of
`logDeriv f` is `2πi` times the sum of the orders of `f` over the open rectangle: zeros count with
their multiplicity, poles with minus their order (Mathlib's `MeromorphicOn.divisor`).

## Main results

* `HodgeLadder.Rect.rectIntegral_logDeriv`: the argument principle on a rectangle.
* `HodgeLadder.Rect.rectIntegral_const_mul`, `rectIntegral_add`: linearity of `rectIntegral`.
* `HodgeLadder.Rect.rectIntegral_sub_inv_of_notMem`: `(p − u)⁻¹` has boundary integral `0` for
  `u` outside the closed rectangle.
* `HodgeLadder.Rect.rect_subset_ball`: the closed rectangle lies in an open ball around `z`.
* `HodgeLadder.Rect.rectIntegral_logDeriv_id`, `rectIntegral_logDeriv_inv`: tests on the square
  with corners `−1 − I`, `1 + I`; a simple zero at `0` gives `2πi`, a simple pole gives `−2πi`.

## Proof

Take the open ball `U` around `z` of radius `|w.re − z.re| + |w.im − z.im| + 1`, which contains
the closed rectangle. The divisor of `f` on `U` has finite support (its closure is compact), so
`MeromorphicOn.extract_zeros_poles` writes `f = (∏ᶠ u, (· − u) ^ d u) • g` on a codiscrete subset
of `U`, with `g` analytic and zero-free on `U`. At a boundary point `p` the order of `f` is `0`, so
both sides are analytic at `p` and agree on a neighbourhood of `p`; there
`logDeriv f p = ∑ u ∈ S, d u * (p − u)⁻¹ + logDeriv g p` for the finite support `S`. Integrate by
`rectIntegral_congr` and linearity: `logDeriv g` is holomorphic on the closed rectangle (Cauchy),
a point `u ∈ S` inside contributes `2πi · d u` (`rectIntegral_sub_inv`) and a point outside the
closed rectangle contributes `0`; no point of `S` lies on the boundary.
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory intervalIntegral Filter Topology MeromorphicOn Metric

open scoped Real Interval

namespace HodgeLadder.Rect

/-- `rectIntegral` commutes with multiplication by a constant. -/
theorem rectIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectIntegral (fun p ↦ c * f p) z w = c * rectIntegral f z w := by
  simp only [rectIntegral, smul_eq_mul, intervalIntegral.integral_const_mul]
  ring

/-- `rectIntegral` of a sum of two functions continuous on the boundary is the sum. -/
theorem rectIntegral_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F G : ℂ → E}
    {z w : ℂ}
    (hF : ContinuousOn F ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)))
    (hG : ContinuousOn G ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
    rectIntegral (fun p ↦ F p + G p) z w = rectIntegral F z w + rectIntegral G z w := by
  have h := rectIntegral_finsetSum (s := Finset.univ) (f := ![F, G]) (z := z) (w := w)
    (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

/-- For `u` outside the closed rectangle the boundary integral of `p ↦ (p − u)⁻¹` is `0`, by
Cauchy's theorem for rectangles. -/
theorem rectIntegral_sub_inv_of_notMem {z w u : ℂ} (hu : u ∉ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) :
    rectIntegral (fun p ↦ (p - u)⁻¹) z w = 0 := by
  apply rectIntegral_eq_zero_of_differentiableOn
  intro p hp
  have : p - u ≠ 0 := sub_ne_zero.mpr fun h ↦ hu (h ▸ hp)
  exact ((differentiableAt_id.sub_const u).inv this).differentiableWithinAt

/-- The closed rectangle with corners `z`, `w` lies in the open ball around `z` of radius
`|w.re − z.re| + |w.im − z.im| + 1`. -/
theorem rect_subset_ball (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ ball z (|w.re - z.re| + |w.im - z.im| + 1) := by
  intro p hp
  rw [mem_reProdIm] at hp
  rw [mem_ball, dist_eq]
  calc ‖p - z‖ ≤ |(p - z).re| + |(p - z).im| := norm_le_abs_re_add_abs_im _
    _ ≤ |w.re - z.re| + |w.im - z.im| := by
        simp only [sub_re, sub_im]
        exact add_le_add (abs_sub_left_of_mem_uIcc hp.1) (abs_sub_left_of_mem_uIcc hp.2)
    _ < _ := by linarith

set_option linter.unusedVariables false in
/-- The argument principle on a rectangle. Let `f` be meromorphic on `ℂ` with finite order at
every point, analytic and nonzero on the boundary of the rectangle with lower-left corner `z` and
upper-right corner `w`. Then the counterclockwise boundary integral of `logDeriv f` is `2πi` times
the sum, over the open rectangle, of the divisor of `f` (order of a zero positive, order of a pole
negative). Orientation and sign: row "Rectangle boundary orientation" of `docs/conventions.md`.

The corner-order hypotheses `hre`, `him` fix the orientation reading and are kept from the
posted statement; the proof does not need them, because when either fails the open rectangle is
empty, `hbd` covers the whole closed rectangle, and both sides are `0`. -/
theorem rectIntegral_logDeriv {f : ℂ → ℂ} (hf : Meromorphic f)
    (hord : ∀ u, meromorphicOrderAt f u ≠ ⊤) {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hbd : ∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im),
      AnalyticAt ℂ f p ∧ f p ≠ 0) :
    rectIntegral (logDeriv f) z w =
      2 * π * I * ∑ᶠ u ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im, ((divisor f univ u : ℤ) : ℂ) := by
  set R := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hR
  set O := Ioo z.re w.re ×ℂ Ioo z.im w.im with hO
  set U := ball z (|w.re - z.re| + |w.im - z.im| + 1) with hU
  have hRU : R ⊆ U := rect_subset_ball z w
  have hOR : O ⊆ R := fun p hp ↦ by
    rw [hO, mem_reProdIm] at hp
    rw [hR, mem_reProdIm]
    exact ⟨Icc_subset_uIcc (Ioo_subset_Icc_self hp.1), Icc_subset_uIcc (Ioo_subset_Icc_self hp.2)⟩
  have hfU : MeromorphicOn f U := fun x _ ↦ hf x
  have hfin : (divisor f U).support.Finite := divisor_ball_support_finite fun x _ ↦ hf x
  obtain ⟨g, hg, hg0, hfg⟩ := hfU.extract_zeros_poles (fun u ↦ hord u) hfin
  set d : ℂ → ℤ := ⇑(divisor f U) with hd
  set S := hfin.toFinset with hS
  have hmemS : ∀ u, u ∈ S ↔ d u ≠ 0 := fun u ↦ by simp [S, d]
  have hdd : ∀ u ∈ U, divisor f univ u = d u := fun u hu ↦ by
    rw [hd, divisor_apply (fun x _ ↦ hf x) (mem_univ u), divisor_apply hfU hu]
  have hdB : ∀ p ∈ R \ O, d p = 0 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hbd p hp
    rw [hd, divisor_apply hfU (hRU hp.1), h1.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 h2]
    rfl
  have hSB : ∀ u ∈ S, u ∉ R \ O := fun u hu hB ↦ (hmemS u).1 hu (hdB u hB)
  have hgl : ∀ p ∈ U, AnalyticAt ℂ (logDeriv g) p := fun p hp ↦
    (hg p hp).deriv.div (hg p hp) (hg0 ⟨p, hp⟩)
  have key : EqOn (logDeriv f) (fun p ↦ ∑ u ∈ S, (d u : ℂ) * (p - u)⁻¹ + logDeriv g p)
      (R \ O) := by
    intro p hp
    obtain ⟨hfa, hfp⟩ := hbd p hp
    have hpU : p ∈ U := hRU hp.1
    have hdp : d p = 0 := hdB p hp
    set φ : ℂ → ℂ := ∏ᶠ u, (· - u) ^ d u with hφ
    have hφa : AnalyticAt ℂ φ p := Function.FactorizedRational.analyticAt (by rw [hdp])
    have hφp : φ p ≠ 0 := Function.FactorizedRational.ne_zero hdp
    have hne : f =ᶠ[𝓝[≠] p] φ • g := by
      have h1 := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.1 hfg) p hpU
      filter_upwards [h1, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hpU)] with y hy hyU
      exact hy hyU
    have hn : f =ᶠ[𝓝 p] φ • g :=
      (hfa.meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
        (hφa.smul (hg p hpU)).meromorphicNFAt).1 hne
    rw [(logDeriv_congr_nhds hn).eq_of_nhds]
    change logDeriv (φ * g) p = _
    rw [logDeriv_mul p hφp (hg0 ⟨p, hpU⟩) hφa.differentiableAt (hg p hpU).differentiableAt]
    congr 1
    have hφe : φ = fun x ↦ ∏ u ∈ S, (x - u) ^ d u := by
      rw [hφ, Function.FactorizedRational.finprod_eq_fun hfin]
      funext x
      apply finprod_eq_prod_of_mulSupport_subset
      intro u hu
      rw [Finset.mem_coe, hmemS]
      intro h0
      apply hu
      change (x - u) ^ d u = 1
      rw [h0, zpow_zero]
    have hpu : ∀ u ∈ S, p - u ≠ 0 := fun u hu ↦
      sub_ne_zero.2 fun h ↦ (hmemS u).1 hu (h ▸ hdp)
    rw [hφe, logDeriv_fun_prod]
    · refine Finset.sum_congr rfl fun u hu ↦ ?_
      rw [logDeriv_fun_zpow (f := fun x ↦ x - u) (by fun_prop)]
      simp [logDeriv_apply, div_eq_mul_inv]
    · intro u hu
      exact zpow_ne_zero _ (hpu u hu)
    · intro u hu
      exact (differentiableAt_fun_id.sub_const u).zpow (Or.inl (hpu u hu))
  have hcont : ∀ u ∈ S, ContinuousOn (fun p ↦ (d u : ℂ) * (p - u)⁻¹) (R \ O) := fun u hu ↦
    continuousOn_const.mul (ContinuousOn.inv₀ (f := fun p ↦ p - u) (by fun_prop) fun p hp h ↦
      hSB u hu (by rw [sub_eq_zero] at h; exact h ▸ hp))
  have hgc : ContinuousOn (logDeriv g) (R \ O) := fun p hp ↦
    (hgl p (hRU hp.1)).continuousAt.continuousWithinAt
  rw [rectIntegral_congr key, rectIntegral_add (continuousOn_finsetSum S hcont) hgc,
    rectIntegral_finsetSum hcont, rectIntegral_eq_zero_of_differentiableOn _ _ _
      (fun p hp ↦ (hgl p (hRU hp)).differentiableAt.differentiableWithinAt), add_zero]
  have hterm : ∀ u ∈ S, rectIntegral (fun p ↦ (d u : ℂ) * (p - u)⁻¹) z w =
      2 * π * I * O.indicator (fun u ↦ ((divisor f univ u : ℤ) : ℂ)) u := by
    intro u hu
    rw [rectIntegral_const_mul]
    by_cases huO : u ∈ O
    · rw [indicator_of_mem huO]
      have h4 := huO
      rw [hO, mem_reProdIm] at h4
      rw [rectIntegral_sub_inv h4.1.1 h4.1.2 h4.2.1 h4.2.2, hdd u (hRU (hOR huO))]
      ring
    · have huR : u ∉ R := fun h ↦ hSB u hu ⟨h, huO⟩
      rw [indicator_of_notMem huO, rectIntegral_sub_inv_of_notMem huR]
      ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, finsum_mem_def,
    finsum_eq_sum_of_support_subset _ ?_]
  intro u hu
  rw [Function.mem_support] at hu
  have huO : u ∈ O := by
    by_contra h
    exact hu (indicator_of_notMem h _)
  rw [indicator_of_mem huO, hdd u (hRU (hOR huO))] at hu
  rw [Finset.mem_coe, hmemS]
  exact_mod_cast hu


/-- The order of the identity of `ℂ` is `1` at `0` and `0` elsewhere. -/
theorem meromorphicOrderAt_id_eq (u : ℂ) :
    meromorphicOrderAt (fun p : ℂ ↦ p) u = if u = 0 then 1 else 0 := by
  split_ifs with hu
  · subst hu; exact meromorphicOrderAt_id
  · exact analyticAt_id.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 hu

/-- `0` lies in the open square with corners `−1 − I` and `1 + I`. -/
theorem rect_test_mem : (0 : ℂ) ∈ Ioo (-1 - I).re (1 + I).re ×ℂ Ioo (-1 - I).im (1 + I).im := by
  simp [mem_reProdIm]

/-- Test of the zero sign: `p ↦ p` has a simple zero at `0`, and `rectIntegral_logDeriv` gives
`2πi` on the square with corners `−1 − I`, `1 + I` (the value of `rectIntegral_inv_square`, since
`logDeriv` of the identity is `p ↦ p⁻¹`). -/
theorem rectIntegral_logDeriv_id :
    rectIntegral (logDeriv fun p : ℂ ↦ p) (-1 - I) (1 + I) = 2 * π * I := by
  have hm : Meromorphic fun p : ℂ ↦ p := fun x ↦ analyticAt_id.meromorphicAt
  rw [rectIntegral_logDeriv hm (fun u ↦ by rw [meromorphicOrderAt_id_eq]; split_ifs <;> simp)
    (by norm_num) (by norm_num) (fun p hp ↦ ⟨analyticAt_id, fun h ↦ hp.2 (h ▸ rect_test_mem)⟩),
    finsum_mem_def, finsum_eq_single _ (0 : ℂ), indicator_of_mem rect_test_mem]
  · rw [divisor_apply (fun x _ ↦ hm x) (mem_univ _), meromorphicOrderAt_id_eq]
    simp
  · intro u hu
    refine indicator_apply_eq_zero.2 fun _ ↦ ?_
    rw [divisor_apply (fun x _ ↦ hm x) (mem_univ _), meromorphicOrderAt_id_eq]
    simp [hu]

/-- Test of the pole sign: `p ↦ p⁻¹` has a simple pole at `0`, and `rectIntegral_logDeriv` gives
`−2πi` on the same square. -/
theorem rectIntegral_logDeriv_inv :
    rectIntegral (logDeriv fun p : ℂ ↦ p⁻¹) (-1 - I) (1 + I) = -(2 * π * I) := by
  have hm : Meromorphic fun p : ℂ ↦ p⁻¹ := fun x ↦ analyticAt_id.meromorphicAt.inv
  have ho : ∀ u, meromorphicOrderAt (fun p : ℂ ↦ p⁻¹) u = -(if u = 0 then 1 else 0) := fun u ↦ by
    change meromorphicOrderAt ((fun p : ℂ ↦ p)⁻¹) u = _
    rw [meromorphicOrderAt_inv, meromorphicOrderAt_id_eq]
  rw [rectIntegral_logDeriv hm (fun u ↦ by rw [ho]; split_ifs <;> simp)
    (by norm_num) (by norm_num)
    (fun p hp ↦ ⟨analyticAt_inv fun h ↦ hp.2 (h ▸ rect_test_mem),
      inv_ne_zero fun h ↦ hp.2 (h ▸ rect_test_mem)⟩),
    finsum_mem_def, finsum_eq_single _ (0 : ℂ), indicator_of_mem rect_test_mem]
  · rw [divisor_apply (fun x _ ↦ hm x) (mem_univ _), ho]
    simp
  · intro u hu
    refine indicator_apply_eq_zero.2 fun _ ↦ ?_
    rw [divisor_apply (fun x _ ↦ hm x) (mem_univ _), ho]
    simp [hu]

end HodgeLadder.Rect
