module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Complex.Basic

/-!
# The boundary integral of a doubly periodic function over a period rectangle

For `h : ℂ → E` with periods `1` and `τ`, the counterclockwise boundary integral over the
rectangle with corners `a` and `a + 1 + (Im τ) I` vanishes. The boundary integral is written out
as the left side of Mathlib's `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`
(bottom minus top plus `I` times right minus `I` times left), so the statement is, by `rfl`,
`rectIntegral h a (a + 1 + τ.im * I) = 0` for the `rectIntegral` of rung `rect-winding`.

The rectangle has width `1` and height `Im τ`; `τ` need not be purely imaginary, and no
integrability, continuity or holomorphy is assumed.

## Main results

* `HodgeLadder.Rect.rectIntegral_eq_zero_of_periodic`: the boundary integral vanishes.
* `HodgeLadder.Rect.boundary_im_ne_zero`: for `h p = Im p`, which has period `1` and lacks
  period `I`, the same expression at `a = 0`, `τ = I` is `−1`; the hypothesis on `τ` is used.
* `HodgeLadder.Rect.boundary_re_ne_zero`: for `h p = Re p`, which has period `I` and lacks
  period `1`, the same expression at `a = 0`, `τ = I` is `I`; the hypothesis on `1` is used.
* `HodgeLadder.Rect.im_periodic_one_not_I`, `re_periodic_I_not_one`: the periods of the two
  test functions.

## Proof

The two vertical sides agree pointwise by the period `1`. On the top side,
`x + (a.im + τ.im) I = (x − τ.re) + a.im I + τ`, so the period `τ` turns the top integrand into
the bottom one shifted by `τ.re`; the bottom integrand has period `1` in `x`, and
`Function.Periodic.intervalIntegral_add_eq` moves the window `[a.re − τ.re, a.re − τ.re + 1]`
back to `[a.re, a.re + 1]`.
-/

@[expose] public section

open Complex intervalIntegral

namespace HodgeLadder.Rect

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- For `h` with periods `1` and `τ`, the counterclockwise boundary integral of `h` over the
rectangle with corners `a` and `a + 1 + (Im τ) I` is zero. The left side is the left side of
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` at `z = a`,
`w = a + 1 + τ.im * I`, that is `rectIntegral h a (a + 1 + τ.im * I)` by `rfl`. -/
theorem rectIntegral_eq_zero_of_periodic {h : ℂ → E} {τ : ℂ} (h₁ : ∀ p, h (p + 1) = h p)
    (hτ : ∀ p, h (p + τ) = h p) (a : ℂ) :
    (∫ x : ℝ in a.re..(a + 1 + τ.im * I).re, h (x + a.im * I)) -
        (∫ x : ℝ in a.re..(a + 1 + τ.im * I).re, h (x + (a + 1 + τ.im * I).im * I)) +
      I • (∫ y : ℝ in a.im..(a + 1 + τ.im * I).im, h (re (a + 1 + τ.im * I) + y * I)) -
      I • (∫ y : ℝ in a.im..(a + 1 + τ.im * I).im, h (re a + y * I)) = 0 := by
  have hre : (a + 1 + τ.im * I).re = a.re + 1 := by simp
  have him : (a + 1 + τ.im * I).im = a.im + τ.im := by simp
  rw [hre, him]
  have hv : (fun y : ℝ ↦ h (((a.re + 1 : ℝ) : ℂ) + y * I)) = fun y : ℝ ↦ h (a.re + y * I) := by
    funext y
    rw [show ((a.re + 1 : ℝ) : ℂ) + y * I = (a.re + y * I) + 1 by push_cast; ring, h₁]
  have hh : (fun x : ℝ ↦ h (x + ((a.im + τ.im : ℝ) : ℂ) * I)) =
      fun x : ℝ ↦ h (((x - τ.re : ℝ) : ℂ) + a.im * I) := by
    funext x
    rw [show (x : ℂ) + ((a.im + τ.im : ℝ) : ℂ) * I = ((x - τ.re : ℝ) : ℂ) + a.im * I + τ by
      push_cast; linear_combination re_add_im τ, hτ]
  have hper : Function.Periodic (fun x : ℝ ↦ h ((x : ℂ) + a.im * I)) 1 := by
    intro x
    simp only
    rw [show ((x + 1 : ℝ) : ℂ) + a.im * I = (x + a.im * I) + 1 by push_cast; ring, h₁]
  rw [hv, hh, intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ h ((x : ℂ) + a.im * I)),
    show a.re + 1 - τ.re = (a.re - τ.re) + 1 by ring,
    hper.intervalIntegral_add_eq (a.re - τ.re) a.re]
  simp

/-- The hypothesis on `τ` is used: `h p = Im p` has period `1` and lacks period `I`, and the
boundary expression of `rectIntegral_eq_zero_of_periodic` at `a = 0`, `τ = I` is `−1`
(bottom `0`, top `1`, the vertical sides cancel). -/
theorem boundary_im_ne_zero :
    (∫ x : ℝ in (0 : ℂ).re..(0 + 1 + I.im * I).re, (((x + (0 : ℂ).im * I : ℂ).im : ℝ) : ℂ)) -
        (∫ x : ℝ in (0 : ℂ).re..(0 + 1 + I.im * I).re,
          (((x + (0 + 1 + I.im * I : ℂ).im * I : ℂ).im : ℝ) : ℂ)) +
      I • (∫ y : ℝ in (0 : ℂ).im..(0 + 1 + I.im * I).im,
          (((re (0 + 1 + I.im * I) + y * I : ℂ).im : ℝ) : ℂ)) -
      I • (∫ y : ℝ in (0 : ℂ).im..(0 + 1 + I.im * I).im,
          (((re (0 : ℂ) + y * I : ℂ).im : ℝ) : ℂ)) = -1 := by
  simp

/-- `p ↦ Im p` has period `1` and lacks period `I`, the two facts `boundary_im_ne_zero` is a test
of. -/
theorem im_periodic_one_not_I :
    (∀ p : ℂ, (((p + 1).im : ℝ) : ℂ) = ((p.im : ℝ) : ℂ)) ∧
      ¬ ∀ p : ℂ, (((p + I).im : ℝ) : ℂ) = ((p.im : ℝ) : ℂ) := by
  refine ⟨fun p ↦ by simp, fun hI ↦ ?_⟩
  simpa using hI 0

/-- The hypothesis on the period `1` is used: `h p = Re p` has period `I` and lacks period `1`,
and the boundary expression of `rectIntegral_eq_zero_of_periodic` at `a = 0`, `τ = I` is `I`
(the horizontal sides cancel, right `1`, left `0`). -/
theorem boundary_re_ne_zero :
    (∫ x : ℝ in (0 : ℂ).re..(0 + 1 + I.im * I).re, (((x + (0 : ℂ).im * I : ℂ).re : ℝ) : ℂ)) -
        (∫ x : ℝ in (0 : ℂ).re..(0 + 1 + I.im * I).re,
          (((x + (0 + 1 + I.im * I : ℂ).im * I : ℂ).re : ℝ) : ℂ)) +
      I • (∫ y : ℝ in (0 : ℂ).im..(0 + 1 + I.im * I).im,
          (((re (0 + 1 + I.im * I) + y * I : ℂ).re : ℝ) : ℂ)) -
      I • (∫ y : ℝ in (0 : ℂ).im..(0 + 1 + I.im * I).im,
          (((re (0 : ℂ) + y * I : ℂ).re : ℝ) : ℂ)) = I := by
  simp

/-- `p ↦ Re p` has period `I` and lacks period `1`, the two facts `boundary_re_ne_zero` is a test
of. -/
theorem re_periodic_I_not_one :
    (∀ p : ℂ, (((p + I).re : ℝ) : ℂ) = ((p.re : ℝ) : ℂ)) ∧
      ¬ ∀ p : ℂ, (((p + 1).re : ℝ) : ℂ) = ((p.re : ℝ) : ℂ) := by
  refine ⟨fun p ↦ by simp, fun h1 ↦ ?_⟩
  simpa using h1 0

end HodgeLadder.Rect
