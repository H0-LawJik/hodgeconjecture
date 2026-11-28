module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Winding of a rectangle around an interior point

Mathlib's Cauchy theorem for rectangles,
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, is stated for the boundary
expression `∫ bottom − ∫ top + I • ∫ right − I • ∫ left`, which is the counterclockwise
boundary integral of the rectangle with corners `z`, `w` when `z.re < w.re` and `z.im < w.im`.
`rectIntegral f z w` names that expression. For `a` strictly inside the rectangle the value
at `p ↦ (p − a)⁻¹` is `2πi`.

## Main definitions

* `HodgeLadder.Rect.rectIntegral`: the left side of
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

## Main results

* `HodgeLadder.Rect.integral_horizontal_sub_inv`, `integral_vertical_right_sub_inv`,
  `integral_vertical_left_sub_inv`: the integral of `(p − a)⁻¹` along one side as a difference
  of logarithms.
* `HodgeLadder.Rect.log_neg_sub_log_of_im_neg`, `log_sub_log_neg_of_im_pos`: the jump `πI` of
  the principal logarithm between `q` and `−q` off the real axis.
* `HodgeLadder.Rect.rectIntegral_eq_zero_of_differentiableOn`: Mathlib's theorem, read through
  `rectIntegral`.
* `HodgeLadder.Rect.rectIntegral_sub_inv`: `rectIntegral (fun p ↦ (p − a)⁻¹) z w = 2πi` for
  `z.re < a.re < w.re` and `z.im < a.im < w.im`.
* `HodgeLadder.Rect.rectIntegral_sub_inv_ne_neg`: the value is not `−2πi`, so the value of
  `rectIntegral_sub_inv` separates the two orientations.
* `HodgeLadder.Rect.rectIntegral_inv_square`: the instance `a = 0`, `z = −1 − I`, `w = 1 + I`.
* `HodgeLadder.Rect.rectIntegral_bottom_square_im`: an orientation test with no logarithm, the
  bottom side of that square has imaginary part `π / 2` by `arctan`.
* `HodgeLadder.Rect.rectIntegral_swap`: swapping both corners leaves `rectIntegral` unchanged.
* `HodgeLadder.Rect.rectIntegral_congr`, `rectIntegral_finsetSum`: `rectIntegral` depends only on
  boundary values and is additive over finite sums of boundary-continuous functions.

## Proof

Each side is a difference of values of a branch of the logarithm by the fundamental theorem of
calculus: `log (p − a)` on the bottom, top and right sides, which stay in the slit plane, and
`log (a − p)` on the left side. With `q₀₀ = z − a` in the lower half-plane and
`q₀₁ = z.re + w.im I − a` in the upper one, the four terms add up to
`(log (−q₀₀) − log q₀₀) + (log q₀₁ − log (−q₀₁)) = πI + πI`.
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory intervalIntegral

open scoped Real Interval

namespace HodgeLadder.Rect

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The counterclockwise boundary integral of `f` over the rectangle with corners `z` and `w`
(for `z.re < w.re`, `z.im < w.im`): bottom minus top plus `I` times right minus `I` times left,
exactly the left side of `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. -/
def rectIntegral (f : ℂ → E) (z w : ℂ) : E :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
    I • (∫ y : ℝ in z.im..w.im, f (re z + y * I))

/-- Mathlib's Cauchy theorem for rectangles, read through `rectIntegral`. -/
theorem rectIntegral_eq_zero_of_differentiableOn (f : ℂ → E) (z w : ℂ)
    (H : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) : rectIntegral f z w = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w H

/-- For `q` in the lower half-plane, `log (−q) − log q = πI`. -/
theorem log_neg_sub_log_of_im_neg {q : ℂ} (hq : q.im < 0) : log (-q) - log q = π * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_add_pi_of_im_neg hq]

/-- For `q` in the upper half-plane, `log q − log (−q) = πI`. -/
theorem log_sub_log_neg_of_im_pos {q : ℂ} (hq : 0 < q.im) : log q - log (-q) = π * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_sub_pi_of_im_pos hq]

/-- A horizontal segment at height `t ≠ a.im`: the integral of `(p − a)⁻¹` is a difference of
values of `log (p − a)`. -/
theorem integral_horizontal_sub_inv {a : ℂ} {t : ℝ} (ht : t ≠ a.im) (x₀ x₁ : ℝ) :
    ∫ x : ℝ in x₀..x₁, ((x : ℂ) + t * I - a)⁻¹ =
      log (x₁ + t * I - a) - log (x₀ + t * I - a) := by
  have hslit : ∀ x : ℝ, (x : ℂ) + t * I - a ∈ slitPlane := fun x ↦ by
    rw [mem_slitPlane_iff]; right; simp [sub_ne_zero.mpr ht]
  have hne : ∀ x : ℝ, (x : ℂ) + t * I - a ≠ 0 := fun x ↦ slitPlane_ne_zero (hslit x)
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ ↦ log ((x : ℂ) + t * I - a))
      ((x : ℂ) + t * I - a)⁻¹ x := fun x ↦ by
    have := ((((hasDerivAt_id x).ofReal_comp).add_const (t * I)).sub_const a).clog_real (hslit x)
    simpa [one_div] using this
  refine integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x) ?_
  refine Continuous.intervalIntegrable ?_ _ _
  exact Continuous.inv₀ (by fun_prop) hne

/-- A vertical segment at abscissa `s > a.re`: the integral of `I (p − a)⁻¹` is a difference of
values of `log (p − a)`. -/
theorem integral_vertical_right_sub_inv {a : ℂ} {s : ℝ} (hs : a.re < s) (y₀ y₁ : ℝ) :
    ∫ y : ℝ in y₀..y₁, I * ((s : ℂ) + y * I - a)⁻¹ =
      log (s + y₁ * I - a) - log (s + y₀ * I - a) := by
  have hslit : ∀ y : ℝ, (s : ℂ) + y * I - a ∈ slitPlane := fun y ↦ by
    rw [mem_slitPlane_iff]; left; simpa using hs
  have hne : ∀ y : ℝ, (s : ℂ) + y * I - a ≠ 0 := fun y ↦ slitPlane_ne_zero (hslit y)
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ ↦ log ((s : ℂ) + y * I - a))
      (I * ((s : ℂ) + y * I - a)⁻¹) y := fun y ↦ by
    have := (((((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (s : ℂ)).sub_const
      a).clog_real (hslit y)
    simpa [div_eq_mul_inv] using this
  refine integral_eq_sub_of_hasDerivAt (fun y _ ↦ hd y) ?_
  refine Continuous.intervalIntegrable ?_ _ _
  exact continuous_const.mul (Continuous.inv₀ (by fun_prop) hne)

/-- A vertical segment at abscissa `s < a.re`: the integral of `I (p − a)⁻¹` is a difference of
values of `log (a − p)`. -/
theorem integral_vertical_left_sub_inv {a : ℂ} {s : ℝ} (hs : s < a.re) (y₀ y₁ : ℝ) :
    ∫ y : ℝ in y₀..y₁, I * ((s : ℂ) + y * I - a)⁻¹ =
      log (a - (s + y₁ * I)) - log (a - (s + y₀ * I)) := by
  have hslit : ∀ y : ℝ, a - ((s : ℂ) + y * I) ∈ slitPlane := fun y ↦ by
    rw [mem_slitPlane_iff]; left; simpa using hs
  have hne : ∀ y : ℝ, (s : ℂ) + y * I - a ≠ 0 := fun y ↦ by
    rw [← neg_ne_zero, neg_sub]; exact slitPlane_ne_zero (hslit y)
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ ↦ log (a - ((s : ℂ) + y * I)))
      (I * ((s : ℂ) + y * I - a)⁻¹) y := fun y ↦ by
    have := (((((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (s : ℂ)).const_sub
      a).clog_real (hslit y)
    simp only [id, Complex.ofReal_one, one_mul] at this
    convert this using 1
    rw [← neg_sub ((s : ℂ) + y * I) a, div_neg]
    simp [div_eq_mul_inv]
  refine integral_eq_sub_of_hasDerivAt (fun y _ ↦ hd y) ?_
  refine Continuous.intervalIntegrable ?_ _ _
  exact continuous_const.mul (Continuous.inv₀ (by fun_prop) hne)

/-- The boundary integral of `p ↦ (p − a)⁻¹` over a rectangle containing `a` in its interior is
`2πi`, with Mathlib's counterclockwise orientation. -/
theorem rectIntegral_sub_inv {z w a : ℂ} (h₁ : z.re < a.re) (h₂ : a.re < w.re)
    (h₃ : z.im < a.im) (h₄ : a.im < w.im) :
    rectIntegral (fun p ↦ (p - a)⁻¹) z w = 2 * π * I := by
  simp only [rectIntegral, smul_eq_mul, ← intervalIntegral.integral_const_mul]
  rw [integral_horizontal_sub_inv h₃.ne, integral_horizontal_sub_inv h₄.ne',
    integral_vertical_right_sub_inv h₂, integral_vertical_left_sub_inv h₁]
  have e₀ := log_neg_sub_log_of_im_neg (q := (z.re : ℂ) + z.im * I - a) (by simpa using h₃)
  have e₁ := log_sub_log_neg_of_im_pos (q := (z.re : ℂ) + w.im * I - a) (by simpa using h₄)
  rw [neg_sub] at e₀ e₁
  linear_combination e₀ + e₁

/-- The orientation test: the boundary integral of `p ↦ (p − a)⁻¹` is not `−2πi`. -/
theorem rectIntegral_sub_inv_ne_neg {z w a : ℂ} (h₁ : z.re < a.re) (h₂ : a.re < w.re)
    (h₃ : z.im < a.im) (h₄ : a.im < w.im) :
    rectIntegral (fun p ↦ (p - a)⁻¹) z w ≠ -(2 * π * I) := by
  rw [rectIntegral_sub_inv h₁ h₂ h₃ h₄]
  intro h
  have : (2 * π * I : ℂ) = 0 := by linear_combination h / 2
  simp [Real.pi_ne_zero] at this

/-- A numerical instance: the square with corners `−1 − I` and `1 + I` winds once
counterclockwise around `0`. -/
theorem rectIntegral_inv_square :
    rectIntegral (fun p : ℂ ↦ p⁻¹) (-1 - I) (1 + I) = 2 * π * I := by
  simpa using rectIntegral_sub_inv (z := -1 - I) (w := 1 + I) (a := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Swapping both corners leaves `rectIntegral` unchanged: the rectangle is the same and the
expression keeps its orientation. -/
theorem rectIntegral_swap (f : ℂ → E) (z w : ℂ) : rectIntegral f w z = rectIntegral f z w := by
  simp only [rectIntegral, integral_symm w.re z.re, integral_symm w.im z.im, smul_neg]
  abel

/-- Each side of the rectangle lies in its boundary
`[[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)`: the four parametrizations
used by `rectIntegral`. -/
theorem mapsTo_rect_sides (z w : ℂ) :
    MapsTo (fun x : ℝ ↦ (x : ℂ) + z.im * I) [[z.re, w.re]]
        ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) ∧
      MapsTo (fun x : ℝ ↦ (x : ℂ) + w.im * I) [[z.re, w.re]]
        ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) ∧
      MapsTo (fun y : ℝ ↦ (w.re : ℂ) + y * I) [[z.im, w.im]]
        ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) ∧
      MapsTo (fun y : ℝ ↦ (z.re : ℂ) + y * I) [[z.im, w.im]]
        ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro t ht <;>
    simp [mem_reProdIm, ht, left_mem_uIcc, right_mem_uIcc]

/-- `rectIntegral` only depends on the values on the boundary of the rectangle. -/
theorem rectIntegral_congr {f g : ℂ → E} {z w : ℂ}
    (h : EqOn f g ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
    rectIntegral f z w = rectIntegral g z w := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := mapsTo_rect_sides z w
  simp only [rectIntegral]
  rw [integral_congr fun x hx ↦ h (h₁ hx), integral_congr fun x hx ↦ h (h₂ hx),
    integral_congr fun y hy ↦ h (h₃ hy), integral_congr fun y hy ↦ h (h₄ hy)]

/-- `rectIntegral` of a finite sum of functions continuous on the boundary of the rectangle is
the sum of the `rectIntegral`s. -/
theorem rectIntegral_finsetSum {ι : Type*} {s : Finset ι} {f : ι → ℂ → E} {z w : ℂ}
    (hf : ∀ i ∈ s, ContinuousOn (f i)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
    rectIntegral (fun p ↦ ∑ i ∈ s, f i p) z w = ∑ i ∈ s, rectIntegral (f i) z w := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := mapsTo_rect_sides z w
  have hc₁ : Continuous fun x : ℝ ↦ (x : ℂ) + z.im * I := by fun_prop
  have hc₂ : Continuous fun x : ℝ ↦ (x : ℂ) + w.im * I := by fun_prop
  have hc₃ : Continuous fun y : ℝ ↦ (w.re : ℂ) + y * I := by fun_prop
  have hc₄ : Continuous fun y : ℝ ↦ (z.re : ℂ) + y * I := by fun_prop
  simp only [rectIntegral]
  rw [integral_finsetSum (f := fun i (x : ℝ) ↦ f i ((x : ℂ) + z.im * I))
      fun i hi ↦ ((hf i hi).comp hc₁.continuousOn h₁).intervalIntegrable,
    integral_finsetSum (f := fun i (x : ℝ) ↦ f i ((x : ℂ) + w.im * I))
      fun i hi ↦ ((hf i hi).comp hc₂.continuousOn h₂).intervalIntegrable,
    integral_finsetSum (f := fun i (x : ℝ) ↦ f i ((w.re : ℂ) + x * I))
      fun i hi ↦ ((hf i hi).comp hc₃.continuousOn h₃).intervalIntegrable,
    integral_finsetSum (f := fun i (x : ℝ) ↦ f i ((z.re : ℂ) + x * I))
      fun i hi ↦ ((hf i hi).comp hc₄.continuousOn h₄).intervalIntegrable,
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]

/-- An orientation test independent of `Complex.log`: on the bottom side of the square with
corners `−1 − I`, `1 + I` the imaginary part of `∫ (p − 0)⁻¹` is `π / 2`, by `arctan`. The four
sides of this square carry equal integrals (the rotation `p ↦ I p` maps each to the next), so
the total `2πi` of `rectIntegral_inv_square` is four times this side's `π / 2 · I` plus a zero
real part. -/
theorem rectIntegral_bottom_square_im :
    (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + (-1 : ℝ) * I)⁻¹).im = π / 2 := by
  have hne : ∀ x : ℝ, (x : ℂ) + (-1 : ℝ) * I ≠ 0 := fun x h ↦ by
    simpa using congrArg Complex.im h
  have hint : IntervalIntegrable (fun x : ℝ ↦ ((x : ℂ) + (-1 : ℝ) * I)⁻¹) volume (-1) 1 :=
    (Continuous.inv₀ (by fun_prop) hne).intervalIntegrable _ _
  have key := Complex.imCLM.intervalIntegral_comp_comm hint
  simp only [Complex.imCLM_apply] at key
  rw [← key]
  have him : ∀ x : ℝ, (((x : ℂ) + (-1 : ℝ) * I)⁻¹).im = (1 + x ^ 2)⁻¹ := fun x ↦ by
    simp [Complex.inv_im, Complex.normSq_apply]
    ring
  simp_rw [him]
  rw [integral_inv_one_add_sq, Real.arctan_neg, Real.arctan_one]
  ring

end HodgeLadder.Rect
