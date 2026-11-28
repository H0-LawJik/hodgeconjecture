module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Normalizing a period pair

Every period pair `(ω₁, ω₂)` can be brought to the form `(1, τ)` with `Im τ > 0` by two moves
that keep track of `℘`:

1. **Orientation.** If `Im(ω₂/ω₁) < 0`, swap to `(ω₂, ω₁)`. The lattice and `℘` are unchanged.
   If `Im(ω₂/ω₁) > 0`, keep the basis. The value `0` does not occur. This is the only basis
   choice made here; downstream rungs inherit `τ = ω₂/ω₁` of the oriented basis, recorded in
   `normalize_of_pos` and `normalize_of_neg`.
2. **Scaling.** Multiply by `μ = ω₁⁻¹` of the oriented basis. The lattice becomes `μ Λ`, and
   `℘` is homogeneous of weight `-2`: `℘_{μΛ}(μ z) = μ⁻² ℘_Λ(z)`.

Mathlib has `℘` at the pin, but no scaling of period pairs and no homogeneity.

## Main definitions

* `HodgeLadder.Period.swap`, `HodgeLadder.Period.smul`: the pairs `(ω₂, ω₁)` and `(μ ω₁, μ ω₂)`.
* `HodgeLadder.Period.oriented`: the basis with `Im(ω₂/ω₁) > 0`.
* `HodgeLadder.Period.normalize`, `HodgeLadder.Period.normalizeScale`: `(1, τ)` and `μ`.

## Main results

* `HodgeLadder.Period.exists_normalized`: rung `period-pair-normalize`.
* `HodgeLadder.Period.weierstrassP_smul`: `℘_{μΛ}(μ z) = μ⁻² ℘_Λ(z)` for every `μ ≠ 0`.
* `HodgeLadder.Period.derivWeierstrassP_smul`, `HodgeLadder.Period.G_smul`,
  `HodgeLadder.Period.g₂_smul`, `HodgeLadder.Period.g₃_smul`: weights `-3`, `-n`, `-4`, `-6`.
* `HodgeLadder.Period.weierstrassP_congr`: `℘` depends only on the lattice.
* Tests: `(1, i)` is normalized with scale `1`; `(1, -i)` is swapped, scale `i`, `τ = i`;
  `(c, i c)` is kept with scale `c⁻¹` and `(c, -i c)` swapped to `(-i c, c)` with scale `i c⁻¹`,
  both with `τ = i` and oriented basis `ω₂ = i ω₁`; `℘_{ℤ[i]}(i z) = -℘_{ℤ[i]}(z)` and
  `℘′_{ℤ[i]}(i z) = i ℘′_{ℤ[i]}(z)`; at `μ = 2` the weight `+2` and the reversed lattice transport
  fail on every lattice (`℘ ≢ 0`).

No sign convention beyond the orientation choice `Im τ > 0`; the exponents are exact.
-/

@[expose] public noncomputable section

namespace HodgeLadder.Period

/-- The period pair `(ω₂, ω₁)`: the same lattice and the same `℘`, with the basis order reversed. -/
def swap (L : PeriodPair) : PeriodPair where
  ω₁ := L.ω₂
  ω₂ := L.ω₁
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have := LinearIndependent.pair_iff.mp L.indep t s (by rw [add_comm]; exact h)
    exact ⟨this.2, this.1⟩

/-- The period pair `(μ ω₁, μ ω₂)` for `μ ≠ 0`, spanning the lattice `μ Λ`. -/
def smul (μ : ℂ) (hμ : μ ≠ 0) (L : PeriodPair) : PeriodPair where
  ω₁ := μ * L.ω₁
  ω₂ := μ * L.ω₂
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    refine LinearIndependent.pair_iff.mp L.indep s t ?_
    have h' : μ * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← h]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp h').resolve_left hμ

/-- Swapping the basis keeps the lattice. -/
theorem swap_lattice (L : PeriodPair) : (swap L).lattice = L.lattice := by
  simp only [PeriodPair.lattice, swap, Set.pair_comm]

/-- `℘` depends only on the lattice: two period pairs with the same lattice have the same `℘`. -/
theorem weierstrassP_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.weierstrassP = L'.weierstrassP := by
  funext z
  unfold PeriodPair.weierstrassP
  exact (Equiv.subtypeEquivProp (by rw [h])).tsum_eq _ |>.symm.trans rfl

/-- Lattice transport: `μ z ∈ μ Λ` exactly when `z ∈ Λ`. -/
theorem mem_smul_lattice (μ : ℂ) (hμ : μ ≠ 0) (L : PeriodPair) (z : ℂ) :
    μ * z ∈ (smul μ hμ L).lattice ↔ z ∈ L.lattice := by
  simp only [PeriodPair.mem_lattice, smul]
  refine exists₂_congr fun m n => ?_
  constructor
  · intro h
    apply mul_left_cancel₀ hμ
    rw [← h]; ring
  · intro h; rw [← h]; ring

/-- The bijection `Λ ≃ μ Λ`, `l ↦ μ l`, along which the lattice sums are reindexed. -/
def smulLatticeEquiv (μ : ℂ) (hμ : μ ≠ 0) (L : PeriodPair) :
    L.lattice ≃ (smul μ hμ L).lattice where
  toFun l := ⟨μ * l, (mem_smul_lattice μ hμ L l).2 l.2⟩
  invFun l := ⟨μ⁻¹ * l, (mem_smul_lattice μ hμ L _).1 (by
    rw [← mul_assoc, mul_inv_cancel₀ hμ, one_mul]; exact l.2)⟩
  left_inv l := Subtype.ext (by simp [← mul_assoc, inv_mul_cancel₀ hμ])
  right_inv l := Subtype.ext (by simp [← mul_assoc, mul_inv_cancel₀ hμ])

/-- Homogeneity of `℘` of weight `-2`: `℘_{μΛ}(μ z) = μ⁻² ℘_Λ(z)` for every `μ ≠ 0` and every `z`
(including the junk value `0` on the lattice). Reindex the `tsum` along `l ↦ μ l`. -/
theorem weierstrassP_smul (μ : ℂ) (hμ : μ ≠ 0) (L : PeriodPair) (z : ℂ) :
    (smul μ hμ L).weierstrassP (μ * z) = μ⁻¹ ^ 2 * L.weierstrassP z := by
  unfold PeriodPair.weierstrassP
  rw [← (smulLatticeEquiv μ hμ L).tsum_eq, ← tsum_mul_left]
  congr 1
  funext l
  simp only [smulLatticeEquiv, Equiv.coe_fn_mk]
  rw [← mul_sub, mul_pow, mul_pow]
  field_simp

/-- Homogeneity of `℘′` of weight `-3`: `℘′_{μΛ}(μ z) = μ⁻³ ℘′_Λ(z)`. -/
theorem derivWeierstrassP_smul (μ : ℂ) (hμ : μ ≠ 0) (L : PeriodPair) (z : ℂ) :
    (smul μ hμ L).derivWeierstrassP (μ * z) = μ⁻¹ ^ 3 * L.derivWeierstrassP z := by
  unfold PeriodPair.derivWeierstrassP
  rw [← (smulLatticeEquiv μ hμ L).tsum_eq, mul_neg, ← tsum_mul_left]
  congr 2
  funext l
  simp only [smulLatticeEquiv, Equiv.coe_fn_mk]
  rw [← mul_sub, mul_pow]
  field_simp

/-- Homogeneity of the Eisenstein sums: `G_n(μΛ) = μ⁻ⁿ G_n(Λ)`. -/
theorem G_smul (μ : ℂ) (hμ : μ ≠ 0) (L : PeriodPair) (n : ℕ) :
    (smul μ hμ L).G n = μ⁻¹ ^ n * L.G n := by
  unfold PeriodPair.G
  rw [← (smulLatticeEquiv μ hμ L).tsum_eq, ← tsum_mul_left]
  congr 1
  funext l
  simp only [smulLatticeEquiv, Equiv.coe_fn_mk]
  rw [mul_pow, mul_inv, inv_pow]

/-- `g₂(μΛ) = μ⁻⁴ g₂(Λ)`, with Mathlib's `g₂ = 60 G₄`. -/
theorem g₂_smul (μ : ℂ) (hμ : μ ≠ 0) (L : PeriodPair) :
    (smul μ hμ L).g₂ = μ⁻¹ ^ 4 * L.g₂ := by
  simp only [PeriodPair.g₂, G_smul]; ring

/-- `g₃(μΛ) = μ⁻⁶ g₃(Λ)`, with Mathlib's `g₃ = 140 G₆`. -/
theorem g₃_smul (μ : ℂ) (hμ : μ ≠ 0) (L : PeriodPair) :
    (smul μ hμ L).g₃ = μ⁻¹ ^ 6 * L.g₃ := by
  simp only [PeriodPair.g₃, G_smul]; ring

/-- The first period is nonzero. -/
theorem ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  simpa using L.indep.ne_zero 0

/-- The second period is nonzero. -/
theorem ω₂_ne_zero (L : PeriodPair) : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1

/-- `ω₂ / ω₁` is not real: `ℝ`-independence of the periods. -/
theorem im_div_ne_zero (L : PeriodPair) : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro h
  have hq : L.ω₂ / L.ω₁ = ((L.ω₂ / L.ω₁).re : ℂ) := by
    apply Complex.ext <;> simp [h]
  have h2 : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁ := by
    rw [← hq, div_mul_cancel₀ _ (ω₁_ne_zero L)]
  have := LinearIndependent.pair_iff.mp L.indep (L.ω₂ / L.ω₁).re (-1)
    (by rw [Complex.real_smul, Complex.real_smul, ← h2]; push_cast; ring)
  norm_num at this

/-- The positively oriented basis of the same lattice: `L` itself when `Im(ω₂/ω₁) > 0`, and the
swap `(ω₂, ω₁)` when `Im(ω₂/ω₁) < 0` (the value `0` does not occur, `im_div_ne_zero`). -/
def oriented (L : PeriodPair) : PeriodPair :=
  if 0 < (L.ω₂ / L.ω₁).im then L else swap L

/-- When `Im(ω₂/ω₁) > 0` the basis is kept. -/
theorem oriented_of_pos {L : PeriodPair} (h : 0 < (L.ω₂ / L.ω₁).im) : oriented L = L :=
  ite_eq_left_iff.mpr fun h' => absurd h h'

/-- When `Im(ω₂/ω₁) < 0` the basis is swapped to `(ω₂, ω₁)`. -/
theorem oriented_of_neg {L : PeriodPair} (h : (L.ω₂ / L.ω₁).im < 0) :
    oriented L = swap L :=
  ite_eq_right_iff.mpr fun h' => absurd h' (not_lt.mpr h.le)

/-- The oriented basis spans the same lattice. -/
theorem oriented_lattice (L : PeriodPair) : (oriented L).lattice = L.lattice := by
  unfold oriented; split_ifs
  · rfl
  · exact swap_lattice L

/-- The oriented basis satisfies `Im(ω₂/ω₁) > 0`. -/
theorem im_div_oriented_pos (L : PeriodPair) :
    0 < ((oriented L).ω₂ / (oriented L).ω₁).im := by
  unfold oriented; split_ifs with h
  · exact h
  · have hneg : (L.ω₂ / L.ω₁).im < 0 := lt_of_le_of_ne (not_lt.mp h) (im_div_ne_zero L)
    have hne : L.ω₂ / L.ω₁ ≠ 0 := div_ne_zero (ω₂_ne_zero L) (ω₁_ne_zero L)
    show 0 < (L.ω₁ / L.ω₂).im
    rw [← inv_div, Complex.inv_im]
    exact div_pos (neg_pos.mpr hneg) (Complex.normSq_pos.mpr hne)

/-- The normalizing scale `μ = ω₁⁻¹` of the oriented basis: `ω₁⁻¹` without the swap, `ω₂⁻¹` with it. -/
def normalizeScale (L : PeriodPair) : ℂ := (oriented L).ω₁⁻¹

/-- The normalizing scale is nonzero. -/
theorem normalizeScale_ne_zero (L : PeriodPair) : normalizeScale L ≠ 0 :=
  inv_ne_zero (ω₁_ne_zero _)

/-- The normalized period pair `μ · oriented L = (1, τ)` with `μ = normalizeScale L` and `Im τ > 0`. -/
def normalize (L : PeriodPair) : PeriodPair :=
  smul (normalizeScale L) (normalizeScale_ne_zero L) (oriented L)

/-- The normalized pair has first period `1`. -/
theorem normalize_ω₁ (L : PeriodPair) : (normalize L).ω₁ = 1 :=
  inv_mul_cancel₀ (ω₁_ne_zero _)

/-- The normalized pair has second period `τ = ω₂/ω₁` of the oriented basis. -/
theorem normalize_ω₂ (L : PeriodPair) :
    (normalize L).ω₂ = (oriented L).ω₂ / (oriented L).ω₁ := by
  show (oriented L).ω₁⁻¹ * (oriented L).ω₂ = _
  rw [div_eq_inv_mul]

/-- Without the swap (`Im(ω₂/ω₁) > 0`): `μ = ω₁⁻¹` and `τ = ω₂/ω₁`. -/
theorem normalize_of_pos {L : PeriodPair} (h : 0 < (L.ω₂ / L.ω₁).im) :
    normalizeScale L = L.ω₁⁻¹ ∧ (normalize L).ω₂ = L.ω₂ / L.ω₁ := by
  rw [normalize_ω₂, normalizeScale, oriented_of_pos h]
  exact ⟨rfl, rfl⟩

/-- With the swap (`Im(ω₂/ω₁) < 0`): `μ = ω₂⁻¹` and `τ = ω₁/ω₂`. -/
theorem normalize_of_neg {L : PeriodPair} (h : (L.ω₂ / L.ω₁).im < 0) :
    normalizeScale L = L.ω₂⁻¹ ∧ (normalize L).ω₂ = L.ω₁ / L.ω₂ := by
  rw [normalize_ω₂, normalizeScale, oriented_of_neg h]
  exact ⟨rfl, rfl⟩

/-- Rung `period-pair-normalize`: every period pair is, after the basis swap when `Im(ω₂/ω₁) < 0` and
the rescaling by `μ = ω₁⁻¹` of the oriented basis, a pair `L' = (1, τ)` with `Im τ > 0`, whose
lattice is `μ Λ` and whose `℘` satisfies `℘_{L'}(μ z) = μ⁻² ℘_L(z)`. The witnesses are
`normalize L` and `normalizeScale L`. -/
theorem exists_normalized (L : PeriodPair) :
    ∃ (L' : PeriodPair) (μ : ℂ), μ ≠ 0 ∧ L'.ω₁ = 1 ∧ 0 < L'.ω₂.im ∧
      (∀ z, μ * z ∈ L'.lattice ↔ z ∈ L.lattice) ∧
      ∀ z, L'.weierstrassP (μ * z) = μ⁻¹ ^ 2 * L.weierstrassP z := by
  refine ⟨normalize L, normalizeScale L, normalizeScale_ne_zero L, normalize_ω₁ L, ?_, ?_, ?_⟩
  · rw [normalize_ω₂]; exact im_div_oriented_pos L
  · intro z
    rw [normalize, mem_smul_lattice, oriented_lattice]
  · intro z
    rw [normalize, weierstrassP_smul, weierstrassP_congr (oriented_lattice L)]

/-- Test: the Gaussian period pair `(1, i)`, spanning `ℤ[i]`. -/
def gaussianPair : PeriodPair where
  ω₁ := 1
  ω₂ := Complex.I
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact ⟨h1, h2⟩

/-- Test: the period pair `(1, -i)`, spanning `ℤ[i]` with the negative orientation. -/
def conjGaussianPair : PeriodPair where
  ω₁ := 1
  ω₂ := -Complex.I
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact ⟨h1, h2⟩

/-- Test: `(1, i)` is positively oriented and kept. -/
theorem oriented_gaussianPair : oriented gaussianPair = gaussianPair :=
  oriented_of_pos (by simp [gaussianPair])

/-- Test: `(1, i)` is already normalized, with scale `1`. -/
theorem normalizeScale_gaussianPair : normalizeScale gaussianPair = 1 := by
  rw [normalizeScale, oriented_gaussianPair]; simp [gaussianPair]

/-- Test: the normalized `(1, i)` has `τ = i`. -/
theorem normalize_gaussianPair_ω₂ : (normalize gaussianPair).ω₂ = Complex.I := by
  rw [normalize_ω₂, oriented_gaussianPair]; simp [gaussianPair]

/-- Test: `(1, -i)` is negatively oriented and swapped to `(-i, 1)`. -/
theorem oriented_conjGaussianPair : oriented conjGaussianPair = swap conjGaussianPair :=
  oriented_of_neg (by simp [conjGaussianPair])

/-- Test: the scale for `(1, -i)` is `(-i)⁻¹ = i`. -/
theorem normalizeScale_conjGaussianPair : normalizeScale conjGaussianPair = Complex.I := by
  rw [normalizeScale, oriented_conjGaussianPair]; simp [swap, conjGaussianPair]

/-- Test: the normalized `(1, -i)` is `(1, i)`, with `τ = 1/(-i) = i`. -/
theorem normalize_conjGaussianPair_ω₂ : (normalize conjGaussianPair).ω₂ = Complex.I := by
  rw [normalize_ω₂, oriented_conjGaussianPair]; simp [swap, conjGaussianPair]

/-- Test: `i ℤ[i] = ℤ[i]`, the lattice of `(i, -1)` is that of `(1, i)`. -/
theorem smul_I_gaussianPair_lattice :
    (smul Complex.I Complex.I_ne_zero gaussianPair).lattice = gaussianPair.lattice := by
  ext z
  simp only [PeriodPair.mem_lattice, smul, gaussianPair]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨-n, m, by rw [← h]; push_cast; ring_nf; rw [Complex.I_sq]; ring⟩
  · rintro ⟨m, n, h⟩
    exact ⟨n, -m, by rw [← h]; push_cast; ring_nf; rw [Complex.I_sq]; ring⟩

/-- Test of homogeneity: `℘_{ℤ[i]}(i z) = -℘_{ℤ[i]}(z)`, since `i⁻² = -1`. -/
theorem weierstrassP_gaussianPair_I_mul (z : ℂ) :
    gaussianPair.weierstrassP (Complex.I * z) = -gaussianPair.weierstrassP z := by
  have h := weierstrassP_smul Complex.I Complex.I_ne_zero gaussianPair z
  rw [weierstrassP_congr smul_I_gaussianPair_lattice] at h
  rw [h, inv_pow, Complex.I_sq]
  ring

/-- `℘` is not identically zero: it is discontinuous at `0`. Guards the homogeneity statements
against vacuity. -/
theorem exists_weierstrassP_ne_zero (L : PeriodPair) : ∃ z, L.weierstrassP z ≠ 0 := by
  by_contra h
  push Not at h
  have : L.weierstrassP = fun _ => 0 := funext h
  exact L.not_continuousAt_weierstrassP 0 (zero_mem _) (by rw [this]; exact continuousAt_const)

/-- Test at `μ = 2`: `℘_{2Λ}(2 z) = ℘_Λ(z) / 4`. -/
theorem weierstrassP_smul_two (L : PeriodPair) (z : ℂ) :
    (smul 2 two_ne_zero L).weierstrassP (2 * z) = L.weierstrassP z / 4 := by
  rw [weierstrassP_smul]; ring

/-- Test: the weight `+2` fails at `μ = 2` on every lattice, so `weierstrassP_smul` separates
`μ⁻²` from `μ²` (the `μ = i` test cannot). -/
theorem not_weierstrassP_smul_two_sq (L : PeriodPair) :
    ¬ ∀ z, (smul 2 two_ne_zero L).weierstrassP (2 * z) = 2 ^ 2 * L.weierstrassP z := by
  intro h
  obtain ⟨z, hz⟩ := exists_weierstrassP_ne_zero L
  have h1 := h z
  rw [weierstrassP_smul] at h1
  apply hz
  have : ((2:ℂ)⁻¹ ^ 2 - 2 ^ 2) * L.weierstrassP z = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · norm_num at h0
  · exact h0

/-- Test: the reversed transport `z ∈ μΛ ↔ μ z ∈ Λ` fails at `μ = 2` on every lattice. -/
theorem not_forall_mem_smul_two_iff_two_mul_mem (L : PeriodPair) :
    ¬ ∀ z, z ∈ (smul 2 two_ne_zero L).lattice ↔ 2 * z ∈ L.lattice := by
  intro h
  have h1 : L.ω₁ ∈ (smul 2 two_ne_zero L).lattice :=
    (h L.ω₁).2 (by
      have := L.lattice.add_mem L.ω₁_mem_lattice L.ω₁_mem_lattice
      rwa [← two_mul] at this)
  have h2 : 2 * (L.ω₁ / 2) ∈ (smul 2 two_ne_zero L).lattice := by
    rwa [mul_div_cancel₀ _ two_ne_zero]
  exact L.ω₁_div_two_notMem_lattice ((mem_smul_lattice 2 two_ne_zero L _).1 h2)

/-- A basis `(c, i c)` is kept: scale `c⁻¹`, `τ = i`. -/
theorem normalize_of_eq_I_mul (L : PeriodPair) (h : L.ω₂ = Complex.I * L.ω₁) :
    oriented L = L ∧ normalizeScale L = L.ω₁⁻¹ ∧ (normalize L).ω₂ = Complex.I := by
  have hp : 0 < (L.ω₂ / L.ω₁).im := by
    rw [h, mul_div_cancel_right₀ _ (ω₁_ne_zero L)]; simp
  refine ⟨oriented_of_pos hp, (normalize_of_pos hp).1, ?_⟩
  rw [(normalize_of_pos hp).2, h, mul_div_cancel_right₀ _ (ω₁_ne_zero L)]

/-- A basis `(c, -i c)` is swapped to `(-i c, c)`: scale `i c⁻¹`, `τ = i`. -/
theorem normalize_of_eq_neg_I_mul (L : PeriodPair) (h : L.ω₂ = -Complex.I * L.ω₁) :
    oriented L = swap L ∧ normalizeScale L = Complex.I * L.ω₁⁻¹ ∧
      (normalize L).ω₂ = Complex.I := by
  have h1 := ω₁_ne_zero L
  have hn : (L.ω₂ / L.ω₁).im < 0 := by
    rw [h, mul_div_cancel_right₀ _ h1]; simp
  refine ⟨oriented_of_neg hn, ?_, ?_⟩
  · rw [(normalize_of_neg hn).1, h, mul_inv, inv_neg, Complex.inv_I, neg_neg]
  · rw [(normalize_of_neg hn).2, h]; field_simp; rw [Complex.I_sq]

/-- For `(c, ± i c)` the oriented basis satisfies `ω₂ = i ω₁`, so multiplication by `i` acts on
its coordinates as `rot` (row "Winding-class pullback and the rotation of T²"). -/
theorem oriented_ω₂_eq_I_mul (L : PeriodPair)
    (h : L.ω₂ = Complex.I * L.ω₁ ∨ L.ω₂ = -Complex.I * L.ω₁) :
    (oriented L).ω₂ = Complex.I * (oriented L).ω₁ := by
  rcases h with h | h
  · rw [(normalize_of_eq_I_mul L h).1, h]
  · rw [(normalize_of_eq_neg_I_mul L h).1]; simp only [swap]; rw [h, ← mul_assoc]; simp

/-- The oriented basis depends only on the unordered pair `{ω₁, ω₂}`. -/
theorem oriented_swap (L : PeriodPair) : oriented (swap L) = oriented L := by
  rcases lt_or_gt_of_ne (im_div_ne_zero L) with h | h
  · rw [oriented_of_neg h]
    apply oriented_of_pos
    show 0 < (L.ω₁ / L.ω₂).im
    rw [← inv_div, Complex.inv_im]
    exact div_pos (neg_pos.mpr h)
      (Complex.normSq_pos.mpr (div_ne_zero (ω₂_ne_zero L) (ω₁_ne_zero L)))
  · rw [oriented_of_pos h]
    have hn : ((swap L).ω₂ / (swap L).ω₁).im < 0 := by
      show (L.ω₁ / L.ω₂).im < 0
      rw [← inv_div, Complex.inv_im]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos h)
        (Complex.normSq_pos.mpr (div_ne_zero (ω₂_ne_zero L) (ω₁_ne_zero L)))
    rw [oriented_of_neg hn]
    rfl

/-- `℘′` depends only on the lattice. -/
theorem derivWeierstrassP_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.derivWeierstrassP = L'.derivWeierstrassP := by
  funext z
  unfold PeriodPair.derivWeierstrassP
  congr 1
  exact (Equiv.subtypeEquivProp (by rw [h])).tsum_eq _ |>.symm.trans rfl

/-- Test of the weight `-3`: `℘′_{ℤ[i]}(i z) = i ℘′_{ℤ[i]}(z)`, since `i⁻³ = i` (the weight `+3`
would give `-i`, the automorphism `[-i]`). -/
theorem derivWeierstrassP_gaussianPair_I_mul (z : ℂ) :
    gaussianPair.derivWeierstrassP (Complex.I * z) =
      Complex.I * gaussianPair.derivWeierstrassP z := by
  have h := derivWeierstrassP_smul Complex.I Complex.I_ne_zero gaussianPair z
  rw [derivWeierstrassP_congr smul_I_gaussianPair_lattice] at h
  rw [h, Complex.inv_I]
  linear_combination (-Complex.I * gaussianPair.derivWeierstrassP z) * Complex.I_sq

end HodgeLadder.Period
