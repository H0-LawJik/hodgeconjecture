module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.Real.Cardinality
public import HodgeLadder.Period.Pair.Normalize

/-!
# A fundamental rectangle for a normalized period pair

For a period pair with `ω₁ = 1` and `Im ω₂ > 0`, the lattice is `Λ = ℤ + ℤ ω₂`. For every corner
`a`, the half-open rectangle `[a.re, a.re + 1) ×ℂ [a.im, a.im + Im ω₂)` holds exactly one point of
each class of `ℂ` modulo `Λ`: the imaginary part of `z + m + n ω₂` is `z.im + n Im ω₂`, which fixes
`n` (period `Im ω₂`), and then the real part `z.re + n Re ω₂ + m` fixes `m` (period `1`). The shear
`Re ω₂` enters only through the choice of `m`. For a countable `S`, a corner `a` can be chosen so
that the boundary of the closed rectangle `[[a.re, a.re + 1]] ×ℂ [[a.im, a.im + Im ω₂]]` misses
`S + Λ`: only countably many real and imaginary parts of the corner are excluded.

The rectangle heights match `rect-periodic`'s rectangle from `a` to `a + 1 + (Im ω₂) I`.

## Main results

* `HodgeLadder.Period.exists_fundamental_rect`: rung `lattice-fundamental-rectangle`.
* `HodgeLadder.Period.existsUnique_shift_mem_Ico`: the unique shift, for every corner.
* `HodgeLadder.Period.exists_boundary_avoids`: the boundary clause alone.
* `HodgeLadder.Period.shift_mem_Ico_iff`, `HodgeLadder.Period.eq_of_sub_mem_lattice`: counting
  forms (the shifts into the rectangle are exactly one lattice point; congruent points of the
  rectangle are equal).
* `HodgeLadder.Period.mem_Ioo_of_boundary_avoids`: representatives of points of `S` lie in the
  open rectangle.
* `HodgeLadder.Period.lattice_countable`: `Λ` is countable.
* Tests: at `(1, i)` the shifts of `3/2 + 5/2 i` into `[0, 1) ×ℂ [0, 1)` are exactly `-1 - 2i`; at
  the sheared pair `(1, 1/2 + i)` the shifts of `1/4 + 3/2 i` are exactly `1/2 - i = 1 - ω₂`, and
  the vertical guess `-ω₂` misses; `(1, -i)` has an empty half-open rectangle (so `Im ω₂ > 0` is
  used); `(2, i)` has no shift of `3/2` into the unit-width rectangle (so `ω₁ = 1` is used); for
  `S = Λ` the unique lattice point of the half-open rectangle lies in the open rectangle.

No sign or normalization convention: the statements are about sets and the lattice only.
-/

@[expose] public noncomputable section

namespace HodgeLadder.Period

open Set Complex
open scoped Interval

/-- With `ω₁ = 1`, the lattice points are the `m + n ω₂` with `m n : ℤ`. -/
theorem mem_lattice_of_ω₁_eq_one {L : PeriodPair} (h₁ : L.ω₁ = 1) {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) + n * L.ω₂ = x := by
  rw [PeriodPair.mem_lattice, h₁]
  simp only [mul_one]

/-- The lattice of a period pair is countable. -/
theorem lattice_countable (L : PeriodPair) : (L.lattice : Set ℂ).Countable := by
  have : (L.lattice : Set ℂ) = range fun q : ℤ × ℤ => (q.1 : ℂ) * L.ω₁ + q.2 * L.ω₂ := by
    ext x
    simp only [SetLike.mem_coe, PeriodPair.mem_lattice, mem_range, Prod.exists]
  rw [this]
  exact countable_range _

/-- For `ω₁ = 1` and `Im ω₂ > 0`, every `z` has exactly one lattice shift into the half-open
rectangle `[a.re, a.re + 1) ×ℂ [a.im, a.im + Im ω₂)`. -/
theorem existsUnique_shift_mem_Ico (L : PeriodPair) (h₁ : L.ω₁ = 1) (h₂ : 0 < L.ω₂.im)
    (a z : ℂ) :
    ∃! l : L.lattice, z + l ∈ Ico a.re (a.re + 1) ×ℂ Ico a.im (a.im + L.ω₂.im) := by
  obtain ⟨n, hn, hn'⟩ := existsUnique_add_zsmul_mem_Ico h₂ z.im a.im
  obtain ⟨m, hm, hm'⟩ :=
    existsUnique_add_zsmul_mem_Ico one_pos (z.re + n * L.ω₂.re) a.re
  have hmem : (m : ℂ) + n * L.ω₂ ∈ L.lattice := (mem_lattice_of_ω₁_eq_one h₁).2 ⟨m, n, rfl⟩
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · show z + ((m : ℂ) + n * L.ω₂) ∈ _
    rw [mem_reProdIm]
    simp only [zsmul_eq_mul, mul_one] at hm hn
    constructor
    · convert hm using 1; simp; ring
    · convert hn using 1; simp
  · rintro ⟨l, hl⟩ hz
    obtain ⟨m', n', rfl⟩ := (mem_lattice_of_ω₁_eq_one h₁).1 hl
    rw [mem_reProdIm] at hz
    have hn'' : n' = n := hn' n' (by
      simp only [zsmul_eq_mul]; convert hz.2 using 1; simp)
    subst hn''
    have hm'' : m' = m := hm' m' (by
      simp only [zsmul_eq_mul, mul_one]; convert hz.1 using 1; simp; ring)
    subst hm''
    rfl

/-- Some real number avoids a countable set. -/
theorem exists_real_notMem {B : Set ℝ} (hB : B.Countable) : ∃ x : ℝ, x ∉ B := by
  by_contra h
  exact Cardinal.not_countable_real (hB.mono fun x _ => not_not.1 (not_exists.1 h x))

/-- For `Im ω₂ > 0` and countable `S`, some rectangle `[[a.re, a.re + 1]] ×ℂ [[a.im, a.im + Im ω₂]]`
has boundary disjoint from `S + Λ`: no boundary point `p` and lattice point `l` have `p + l ∈ S`. -/
theorem exists_boundary_avoids (L : PeriodPair) (h₂ : 0 < L.ω₂.im) {S : Set ℂ}
    (hS : S.Countable) :
    ∃ a : ℂ, ∀ p ∈ [[a.re, a.re + 1]] ×ℂ [[a.im, a.im + L.ω₂.im]] \
        (Ioo a.re (a.re + 1) ×ℂ Ioo a.im (a.im + L.ω₂.im)), ∀ l ∈ L.lattice, p + l ∉ S := by
  have hΛ := lattice_countable L
  set Bre : Set ℝ := ⋃ s ∈ S, ⋃ l ∈ (L.lattice : Set ℂ), ({(s - l).re, (s - l).re - 1} : Set ℝ)
  set Bim : Set ℝ := ⋃ s ∈ S, ⋃ l ∈ (L.lattice : Set ℂ),
    ({(s - l).im, (s - l).im - L.ω₂.im} : Set ℝ)
  have hre : Bre.Countable :=
    hS.biUnion fun _ _ => hΛ.biUnion fun _ _ => (toFinite _).countable
  have him : Bim.Countable :=
    hS.biUnion fun _ _ => hΛ.biUnion fun _ _ => (toFinite _).countable
  obtain ⟨x, hx⟩ := exists_real_notMem hre
  obtain ⟨y, hy⟩ := exists_real_notMem him
  refine ⟨⟨x, y⟩, ?_⟩
  rintro p ⟨hp, hpo⟩ l hl hpl
  simp only [mem_reProdIm] at hp hpo
  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hp
  have hsl : p + l - l = p := add_sub_cancel_right p l
  rcases not_and_or.1 hpo with h | h
  · apply hx
    simp only [Bre, mem_iUnion]
    refine ⟨p + l, hpl, l, hl, ?_⟩
    rw [hsl]
    rcases hp.1 with ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with e | e
    · exact Or.inl e
    rcases eq_or_lt_of_le h2 with e' | e'
    · right; simp only [mem_singleton_iff]; linarith
    · exact absurd ⟨e, e'⟩ h
  · apply hy
    simp only [Bim, mem_iUnion]
    refine ⟨p + l, hpl, l, hl, ?_⟩
    rw [hsl]
    rcases hp.2 with ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with e | e
    · exact Or.inl e
    rcases eq_or_lt_of_le h2 with e' | e'
    · right; simp only [mem_singleton_iff]; linarith
    · exact absurd ⟨e, e'⟩ h

/-- Rung `lattice-fundamental-rectangle`. -/
theorem exists_fundamental_rect (L : PeriodPair) (h₁ : L.ω₁ = 1) (h₂ : 0 < L.ω₂.im)
    {S : Set ℂ} (hS : S.Countable) :
    ∃ a : ℂ, (∀ p ∈ [[a.re, a.re + 1]] ×ℂ [[a.im, a.im + L.ω₂.im]] \
        (Ioo a.re (a.re + 1) ×ℂ Ioo a.im (a.im + L.ω₂.im)), ∀ l ∈ L.lattice, p + l ∉ S) ∧
      ∀ z : ℂ, ∃! l : L.lattice, z + l ∈ Ico a.re (a.re + 1) ×ℂ Ico a.im (a.im + L.ω₂.im) := by
  obtain ⟨a, ha⟩ := exists_boundary_avoids L h₂ hS
  exact ⟨a, ha, existsUnique_shift_mem_Ico L h₁ h₂ a⟩

/-- Counting form: once `z + w` lies in the half-open rectangle for a lattice point `w`, the shifts
`l` of `z` into it are exactly `l = w`. -/
theorem shift_mem_Ico_iff (L : PeriodPair) (h₁ : L.ω₁ = 1) (h₂ : 0 < L.ω₂.im) {a z w : ℂ}
    (hw : w ∈ L.lattice) (hzw : z + w ∈ Ico a.re (a.re + 1) ×ℂ Ico a.im (a.im + L.ω₂.im))
    (l : L.lattice) :
    z + l ∈ Ico a.re (a.re + 1) ×ℂ Ico a.im (a.im + L.ω₂.im) ↔ (l : ℂ) = w := by
  obtain ⟨l₀, -, hu⟩ := existsUnique_shift_mem_Ico L h₁ h₂ a z
  refine ⟨fun hl => ?_, fun hl => hl ▸ hzw⟩
  have e₁ := hu l hl
  have e₂ := hu ⟨w, hw⟩ hzw
  rw [e₁, ← e₂]

/-- Two points of the half-open rectangle that differ by a lattice point are equal. -/
theorem eq_of_sub_mem_lattice (L : PeriodPair) (h₁ : L.ω₁ = 1) (h₂ : 0 < L.ω₂.im) {a u v : ℂ}
    (hu : u ∈ Ico a.re (a.re + 1) ×ℂ Ico a.im (a.im + L.ω₂.im))
    (hv : v ∈ Ico a.re (a.re + 1) ×ℂ Ico a.im (a.im + L.ω₂.im)) (huv : u - v ∈ L.lattice) :
    u = v := by
  have h0 : v + (0 : ℂ) ∈ Ico a.re (a.re + 1) ×ℂ Ico a.im (a.im + L.ω₂.im) := by
    rwa [add_zero]
  have := (shift_mem_Ico_iff L h₁ h₂ L.lattice.zero_mem h0 ⟨u - v, huv⟩).1
    (by simpa using hu)
  simpa [sub_eq_zero] using this

/-- If the boundary of the rectangle misses `S + Λ`, then every point of the half-open rectangle
congruent to a point of `S` lies in the open rectangle. -/
theorem mem_Ioo_of_boundary_avoids {L : PeriodPair} (h₂ : 0 < L.ω₂.im) {S : Set ℂ} {a : ℂ}
    (ha : ∀ p ∈ [[a.re, a.re + 1]] ×ℂ [[a.im, a.im + L.ω₂.im]] \
        (Ioo a.re (a.re + 1) ×ℂ Ioo a.im (a.im + L.ω₂.im)), ∀ l ∈ L.lattice, p + l ∉ S)
    {u : ℂ} (hu : u ∈ Ico a.re (a.re + 1) ×ℂ Ico a.im (a.im + L.ω₂.im)) {l : ℂ}
    (hl : l ∈ L.lattice) (hS : u + l ∈ S) :
    u ∈ Ioo a.re (a.re + 1) ×ℂ Ioo a.im (a.im + L.ω₂.im) := by
  by_contra h
  refine ha u ⟨?_, h⟩ l hl hS
  rw [mem_reProdIm] at hu ⊢
  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
  exact ⟨Ico_subset_Icc_self hu.1, Ico_subset_Icc_self hu.2⟩

/-! ### Tests -/

/-- Test: the sheared period pair `(1, 1/2 + i)`. -/
def shearPair : PeriodPair where
  ω₁ := 1
  ω₂ := 1 / 2 + Complex.I
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    subst h2
    simpa using h1

/-- Test: the period pair `(2, i)`, with `ω₁ ≠ 1`. -/
def twoIPair : PeriodPair where
  ω₁ := 2
  ω₂ := Complex.I
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact ⟨h1, h2⟩

/-- Test at the Gaussian pair `(1, i)` and `a = 0`: the shifts of `3/2 + 5/2 i` into
`[0, 1) ×ℂ [0, 1)` are exactly `-1 - 2 i`, with representative `1/2 + 1/2 i`. -/
theorem gaussianPair_shift_iff (l : gaussianPair.lattice) :
    (3 / 2 + 5 / 2 * I : ℂ) + l ∈ Ico (0 : ℂ).re ((0 : ℂ).re + 1) ×ℂ
      Ico (0 : ℂ).im ((0 : ℂ).im + gaussianPair.ω₂.im) ↔ (l : ℂ) = -1 - 2 * I := by
  have h₂ : 0 < gaussianPair.ω₂.im := by simp [gaussianPair]
  refine shift_mem_Ico_iff gaussianPair rfl h₂ ?_ ?_ l
  · exact (mem_lattice_of_ω₁_eq_one rfl).2 ⟨-1, -2, by simp [gaussianPair]; ring⟩
  · simp only [mem_reProdIm, gaussianPair]
    norm_num

/-- Test at the sheared pair `(1, 1/2 + i)` and `a = 0`: the shifts of `1/4 + 3/2 i` into
`[0, 1) ×ℂ [0, 1)` are exactly `1 - ω₂ = 1/2 - i`, with representative `3/4 + 1/2 i`. The purely
vertical shift `-ω₂` lands at `-1/4 + 1/2 i`, outside, so the shear moves the real coordinate. -/
theorem shearPair_shift_iff (l : shearPair.lattice) :
    (1 / 4 + 3 / 2 * I : ℂ) + l ∈ Ico (0 : ℂ).re ((0 : ℂ).re + 1) ×ℂ
      Ico (0 : ℂ).im ((0 : ℂ).im + shearPair.ω₂.im) ↔ (l : ℂ) = 1 / 2 - I := by
  have h₂ : 0 < shearPair.ω₂.im := by simp [shearPair]
  refine shift_mem_Ico_iff shearPair rfl h₂ ?_ ?_ l
  · exact (mem_lattice_of_ω₁_eq_one rfl).2 ⟨1, -1, by simp [shearPair]; ring⟩
  · simp only [mem_reProdIm, shearPair]
    norm_num

/-- Test at the sheared pair: `-ω₂` is a lattice point, and the shift of `1/4 + 3/2 i` by it
misses `[0, 1) ×ℂ [0, 1)`. -/
theorem shearPair_neg_ω₂_notMem :
    -shearPair.ω₂ ∈ shearPair.lattice ∧
      (1 / 4 + 3 / 2 * I : ℂ) + -shearPair.ω₂ ∉ Ico (0 : ℂ).re ((0 : ℂ).re + 1) ×ℂ
        Ico (0 : ℂ).im ((0 : ℂ).im + shearPair.ω₂.im) := by
  refine ⟨neg_mem shearPair.ω₂_mem_lattice, ?_⟩
  simp only [mem_reProdIm, shearPair]
  norm_num

/-- Test: `Im ω₂ > 0` is used. For `(1, -i)` the half-open rectangle is empty, so `0` has no shift
into it. -/
theorem not_existsUnique_conjGaussianPair :
    ¬ ∃! l : conjGaussianPair.lattice, (0 : ℂ) + l ∈ Ico (0 : ℂ).re ((0 : ℂ).re + 1) ×ℂ
      Ico (0 : ℂ).im ((0 : ℂ).im + conjGaussianPair.ω₂.im) := by
  rintro ⟨l, hl, -⟩
  simp only [mem_reProdIm, conjGaussianPair] at hl
  norm_num at hl

/-- Test: `ω₁ = 1` is used. For `(2, i)` no lattice shift of `3/2` has real part in `[0, 1)`. -/
theorem not_exists_twoIPair :
    ¬ ∃ l : twoIPair.lattice, (3 / 2 : ℂ) + l ∈ Ico (0 : ℂ).re ((0 : ℂ).re + 1) ×ℂ
      Ico (0 : ℂ).im ((0 : ℂ).im + twoIPair.ω₂.im) := by
  rintro ⟨⟨l, hl⟩, h⟩
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hl
  simp only [mem_reProdIm, twoIPair] at h
  norm_num at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  have k1 : (-1 : ℝ) < m := by linarith
  have k2 : (m : ℝ) < 0 := by linarith
  have k1' : -1 < m := by exact_mod_cast k1
  have k2' : m < 0 := by exact_mod_cast k2
  omega

/-- Test: the boundary clause holds non-vacuously for `S = Λ`; the shift of `0` into the half-open
rectangle (the unique lattice point there) lies in the open rectangle. -/
theorem lattice_point_mem_Ioo (L : PeriodPair) (h₁ : L.ω₁ = 1) (h₂ : 0 < L.ω₂.im) :
    ∃ a : ℂ, ∃! l : L.lattice,
      (l : ℂ) ∈ Ico a.re (a.re + 1) ×ℂ Ico a.im (a.im + L.ω₂.im) ∧
        (l : ℂ) ∈ Ioo a.re (a.re + 1) ×ℂ Ioo a.im (a.im + L.ω₂.im) := by
  obtain ⟨a, ha, hu⟩ := exists_fundamental_rect L h₁ h₂ (lattice_countable L)
  obtain ⟨l, hl, hl'⟩ := hu 0
  rw [zero_add] at hl
  refine ⟨a, l, ⟨hl, mem_Ioo_of_boundary_avoids h₂ ha hl (neg_mem l.2) (by simp)⟩,
    fun l' hl'' => hl' l' (by simpa using hl''.1)⟩

end HodgeLadder.Period
