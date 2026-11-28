module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Module.Submodule.Bilinear

/-!
# Eigenvalue bookkeeping for products

Let `K` be a field, `T : V →ₗ[K] V` diagonal on a family `e : ι → V` with eigenvalues
`μ : ι → K`, `B : V →ₗ[K] V →ₗ[K] W` bilinear and `S : W →ₗ[K] W` with
`S (B x y) = B (T x) (T y)`. If the products `B (e i) (e j)` span `W`, then for every `c : K`
the `c`-eigenspace `ker (S - c • id)` is the span of the products `B (e i) (e j)` with
`μ i * μ j = c`. The rung `weil-surface-reduction` uses the inclusion with `K = ℂ`,
`V = H_dR^1`, `W = H_dR^2`, `B` the de Rham cup product and `T`, `S` the de Rham pullbacks of an
endomorphism, to place the `-d`-eigenspace on `H²` inside products of eigenvectors on `H¹`.
Mathlib only; no sign conventions enter.

## Main results

* `HodgeLadder.ker_sub_smul_le_span_of_eigen`: the inclusion, as stated in the ledger.
* `HodgeLadder.span_le_ker_sub_smul_of_eigen`: the converse inclusion, without the span
  hypothesis.
* `HodgeLadder.ker_sub_smul_eq_span_of_eigen`: the equality.
* `HodgeLadder.span_range_prod_eq_top_of_span`: if `e` spans `V` and all products `B x y` span
  `W`, the products `B (e i) (e j)` span `W` (the span hypothesis in the form the theorems take).
* `HodgeLadder.isCompl_ker_sub_smul_ker_add_smul`: if `T (T x) = (s * s) • x` with `s ≠ 0` and
  `2 ≠ 0` in `K`, then `V` is the direct sum of the `s`- and `-s`-eigenspaces of `T`.
* `HodgeLadder.disjoint_ker_sub_smul_ker_add_smul`: for `s ≠ 0` and `2 ≠ 0`, the `s`- and
  `-s`-eigenspaces of any `T` are disjoint.
* `HodgeLadder.EigenProductExample.apply_zero_zero_of_mem_ker`: the inclusion applied in the
  example; `HodgeLadder.EigenProductExample.not_ker_le_span_without_hspan`: the span hypothesis
  cannot be dropped.
* `HodgeLadder.EigenProductExample.mem_ker`: a nonvacuity example over `ℚ` with
  `T = diag(1, -1)` and `B` the tensor product into `ℚ^(2 × 2)`.
-/

@[expose] public section

namespace HodgeLadder

/-- **Eigenvalue bookkeeping for products.** Let `T` act diagonally on a family `e : ι → V`
with eigenvalues `μ`, let `B` be bilinear with `S (B x y) = B (T x) (T y)`, and suppose the
products `B (e i) (e j)` span `W`. Then every `c`-eigenvector of `S` lies in the span of the
products `B (e i) (e j)` with `μ i * μ j = c`. The family `ι` is arbitrary; no finiteness is
needed. Proof: each product is a `μ i * μ j`-eigenvector of `S`; split `W` into the span of the
products with value `c` and the span of the others, which lies in the sum of the eigenspaces for
values `≠ c`; eigenspaces for distinct values are independent
(`Module.End.eigenspaces_iSupIndep`). -/
theorem ker_sub_smul_le_span_of_eigen {K V W ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (B : V →ₗ[K] V →ₗ[K] W) (T : V →ₗ[K] V)
    (S : W →ₗ[K] W) (hS : ∀ x y, S (B x y) = B (T x) (T y)) (e : ι → V) (μ : ι → K)
    (he : ∀ i, T (e i) = μ i • e i)
    (hspan : Submodule.span K (Set.range fun p : ι × ι => B (e p.1) (e p.2)) = ⊤) (c : K) :
    LinearMap.ker (S - c • LinearMap.id) ≤
      Submodule.span K ((fun p : ι × ι => B (e p.1) (e p.2)) '' {p | μ p.1 * μ p.2 = c}) := by
  set g : ι × ι → W := fun p => B (e p.1) (e p.2) with hg
  have hE : ∀ p, g p ∈ Module.End.eigenspace S (μ p.1 * μ p.2) := by
    intro p
    rw [Module.End.mem_eigenspace_iff]
    simp only [g, hS, he, map_smul, LinearMap.smul_apply, smul_smul, mul_comm]
  intro w hw
  have hwE : w ∈ Module.End.eigenspace S c := by
    rw [Module.End.mem_eigenspace_iff]
    simpa [sub_eq_zero] using hw
  have hw' : w ∈ Submodule.span K (g '' {p | μ p.1 * μ p.2 = c}) ⊔
      Submodule.span K (g '' {p | μ p.1 * μ p.2 = c}ᶜ) := by
    rw [← Submodule.span_union, ← Set.image_union, Set.union_compl_self, Set.image_univ, hspan]
    trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw'
  have hbE : b ∈ ⨆ (j) (_ : j ≠ c), Module.End.eigenspace S j := by
    refine Submodule.span_le.2 ?_ hb
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.mem_iSup_of_mem (μ p.1 * μ p.2) (Submodule.mem_iSup_of_mem hp (hE p))
  have haE : a ∈ Module.End.eigenspace S c := by
    refine Submodule.span_le.2 ?_ ha
    rintro _ ⟨p, hp, rfl⟩
    exact hp ▸ hE p
  have hbc : b ∈ Module.End.eigenspace S c := by
    simpa using sub_mem hwE haE
  have hb0 : b = 0 := Submodule.disjoint_def.1
    (iSupIndep_def.1 (Module.End.eigenspaces_iSupIndep S) c) b hbc hbE
  simpa [hb0] using ha

/-- The converse inclusion, with no span hypothesis: a product `B (e i) (e j)` with
`μ i * μ j = c` is a `c`-eigenvector of `S`. -/
theorem span_le_ker_sub_smul_of_eigen {K V W ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (B : V →ₗ[K] V →ₗ[K] W) (T : V →ₗ[K] V)
    (S : W →ₗ[K] W) (hS : ∀ x y, S (B x y) = B (T x) (T y)) (e : ι → V) (μ : ι → K)
    (he : ∀ i, T (e i) = μ i • e i) (c : K) :
    Submodule.span K ((fun p : ι × ι => B (e p.1) (e p.2)) '' {p | μ p.1 * μ p.2 = c}) ≤
      LinearMap.ker (S - c • LinearMap.id) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨p, hp, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, hS, he, map_smul, smul_smul, sub_eq_zero]
  rw [← hp, mul_comm]

/-- **The `c`-eigenspace of `S` is the span of the products with eigenvalue product `c`**,
when the products `B (e i) (e j)` span `W`: the inclusion `ker_sub_smul_le_span_of_eigen` and
its converse `span_le_ker_sub_smul_of_eigen`. -/
theorem ker_sub_smul_eq_span_of_eigen {K V W ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (B : V →ₗ[K] V →ₗ[K] W) (T : V →ₗ[K] V)
    (S : W →ₗ[K] W) (hS : ∀ x y, S (B x y) = B (T x) (T y)) (e : ι → V) (μ : ι → K)
    (he : ∀ i, T (e i) = μ i • e i)
    (hspan : Submodule.span K (Set.range fun p : ι × ι => B (e p.1) (e p.2)) = ⊤) (c : K) :
    LinearMap.ker (S - c • LinearMap.id) =
      Submodule.span K ((fun p : ι × ι => B (e p.1) (e p.2)) '' {p | μ p.1 * μ p.2 = c}) :=
  le_antisymm (ker_sub_smul_le_span_of_eigen B T S hS e μ he hspan c)
    (span_le_ker_sub_smul_of_eigen B T S hS e μ he c)

/-- If a family `e` spans `V` and the products `B x y` span `W`, then the products
`B (e i) (e j)` span `W`. -/
theorem span_range_prod_eq_top_of_span {K V W ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (B : V →ₗ[K] V →ₗ[K] W) (e : ι → V)
    (he : Submodule.span K (Set.range e) = ⊤)
    (hB : Submodule.span K (Set.image2 (fun x y => B x y) Set.univ Set.univ) = ⊤) :
    Submodule.span K (Set.range fun p : ι × ι => B (e p.1) (e p.2)) = ⊤ := by
  have h1 := Submodule.map₂_span_span K B (Set.range e) (Set.range e)
  have h2 := Submodule.map₂_span_span K B (Set.univ : Set V) (Set.univ : Set V)
  rw [Submodule.span_univ] at h2
  rw [he, h2, hB, Set.image2_range] at h1
  exact h1.symm

/-- **Splitting into `±s`-eigenspaces.** Over a field with `2 ≠ 0`, if `T (T x) = (s * s) • x`
for all `x` and `s ≠ 0`, then `ker (T - s • id)` and `ker (T + s • id)` are complementary:
`x = (2 s)⁻¹ • (T x + s • x) + (2 s)⁻¹ • (s • x - T x)`, the summands being `s`- and
`-s`-eigenvectors, and a common eigenvector satisfies `2 s • x = 0`. Over `ℂ` with
`s = i √d` this is the eigen-decomposition `H¹ = V₊ ⊕ V₋` of a pullback squaring to `-d`. -/
theorem isCompl_ker_sub_smul_ker_add_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : V →ₗ[K] V) (s : K) (hs : s ≠ 0) (h2 : (2 : K) ≠ 0)
    (hT : ∀ x, T (T x) = (s * s) • x) :
    IsCompl (LinearMap.ker (T - s • LinearMap.id)) (LinearMap.ker (T + s • LinearMap.id)) := by
  have h2s : (2 * s) ≠ 0 := mul_ne_zero h2 hs
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hx hy
    have : (2 * s) • x = 0 := by
      rw [two_mul, add_smul]
      rw [hx] at hy
      exact hy
    exact (smul_eq_zero.1 this).resolve_left h2s
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (2 * s)⁻¹ • (T x + s • x) + (2 * s)⁻¹ • (s • x - T x) := by
      rw [← smul_add, show T x + s • x + (s • x - T x) = (2 * s) • x by
        rw [mul_smul, two_smul]; abel, smul_smul, inv_mul_cancel₀ h2s, one_smul]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_smul, map_add, hT]
      rw [show (s * s) • x - s • T x + s • (T x - s • x) = 0 by
        rw [smul_sub, mul_smul]; abel, smul_zero]
    · simp only [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_smul, map_sub, hT]
      rw [show s • (T x + s • x) - ((s * s) • x + s • T x) = 0 by
        rw [smul_add, mul_smul]; abel, smul_zero]

/-- **Disjoint `±s`-eigenspaces.** Over a field with `2 ≠ 0`, for `s ≠ 0` the kernels of
`T - s • id` and `T + s • id` are disjoint: a common vector satisfies `(2 * s) • x = 0`. A
kernel-form case of Mathlib's `Module.End.disjoint_genEigenspace`, with no hypothesis on `T`;
the disjoint half of `isCompl_ker_sub_smul_ker_add_smul`. -/
theorem disjoint_ker_sub_smul_ker_add_smul {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (T : V →ₗ[K] V) {s : K} (hs : s ≠ 0) (h2 : (2 : K) ≠ 0) :
    Disjoint (LinearMap.ker (T - s • LinearMap.id)) (LinearMap.ker (T + s • LinearMap.id)) := by
  rw [Submodule.disjoint_def]
  intro x h₁ h₂
  rw [LinearMap.mem_ker] at h₁ h₂
  have h : (2 * s) • x =
      (T + s • LinearMap.id : V →ₗ[K] V) x - (T - s • LinearMap.id : V →ₗ[K] V) x := by
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, two_mul, add_smul]
    abel
  rw [h₁, h₂, sub_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (mul_ne_zero h2 hs)

namespace EigenProductExample

/-! ### A nonvacuity example over `ℚ` -/

/-- Eigenvalues `1, -1`. -/
def μ : Fin 2 → ℚ := ![1, -1]

/-- Coordinate vectors. -/
def e : Fin 2 → (Fin 2 → ℚ) := fun i => Pi.single i 1

/-- The tensor product `B x y = (x i * y j)_{i,j}`. -/
noncomputable def B : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 × Fin 2 → ℚ) :=
  LinearMap.mk₂ ℚ (fun x y p => x p.1 * y p.2)
    (fun _ _ _ => by funext p; simp [add_mul])
    (fun _ _ _ => by funext p; simp [mul_assoc])
    (fun _ _ _ => by funext p; simp [mul_add])
    (fun _ _ _ => by funext p; simp [mul_left_comm])

/-- `T = diag(1, -1)`. -/
noncomputable def T : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  LinearMap.pi fun i => μ i • LinearMap.proj i

/-- `S = T ⊗ T`, diagonal with entries `μ i * μ j`. -/
noncomputable def S : (Fin 2 × Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 × Fin 2 → ℚ) :=
  LinearMap.pi fun p => (μ p.1 * μ p.2) • LinearMap.proj p

/-- `S (B x y) = B (T x) (T y)` in the example. -/
theorem hS (x y : Fin 2 → ℚ) : S (B x y) = B (T x) (T y) := by
  funext p; simp [S, T, B]; ring

/-- The coordinate vectors are eigenvectors of `T` with eigenvalues `μ`. -/
theorem he (i : Fin 2) : T (e i) = μ i • e i := by
  funext k; by_cases h : k = i <;> simp [T, e, h]

/-- `B (e i) (e j)` is the coordinate vector at `(i, j)`. -/
theorem B_e (p : Fin 2 × Fin 2) : B (e p.1) (e p.2) = Pi.single p 1 := by
  funext q
  rcases p with ⟨i, j⟩; rcases q with ⟨k, l⟩
  by_cases hk : k = i <;> by_cases hl : l = j <;> simp [B, e, hk, hl]

/-- The products `B (e i) (e j)` span `ℚ^(2 × 2)`. -/
theorem hspan : Submodule.span ℚ (Set.range fun p : Fin 2 × Fin 2 => B (e p.1) (e p.2)) = ⊤ := by
  have : (fun p : Fin 2 × Fin 2 => B (e p.1) (e p.2)) = Pi.basisFun ℚ (Fin 2 × Fin 2) := by
    funext p; rw [B_e, Pi.basisFun_apply]
  rw [this]; exact (Pi.basisFun ℚ _).span_eq

/-- The theorem applied to the example at `c = -1`: the `-1`-eigenspace of `S` is the span of
the products `B (e i) (e j)` with `μ i * μ j = -1`. -/
theorem ker_eq : LinearMap.ker (S - (-1 : ℚ) • LinearMap.id) =
    Submodule.span ℚ ((fun p : Fin 2 × Fin 2 => B (e p.1) (e p.2)) ''
      {p | μ p.1 * μ p.2 = -1}) :=
  ker_sub_smul_eq_span_of_eigen B T S hS e μ he hspan (-1)

/-- Nonvacuity and sharpness at `c = -1`: `B (e 0) (e 1)` is a nonzero `-1`-eigenvector of `S`,
and `B (e 0) (e 0)`, whose eigenvalue product is `1`, is excluded. -/
theorem mem_ker : B (e 0) (e 1) ∈ LinearMap.ker (S - (-1 : ℚ) • LinearMap.id) ∧
    B (e 0) (e 1) ≠ 0 ∧ B (e 0) (e 0) ∉ LinearMap.ker (S - (-1 : ℚ) • LinearMap.id) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ker_eq]; exact Submodule.subset_span ⟨(0, 1), by simp [μ], rfl⟩
  · rw [B_e (0, 1)]; simp
  · intro h
    have := congrFun (LinearMap.mem_ker.1 h) (0, 0)
    rw [B_e (0, 0)] at this
    norm_num [S, μ] at this

/-- The inclusion `ker_sub_smul_le_span_of_eigen`, applied in the example: a `-1`-eigenvector
of `S` has zero `(0, 0)` coordinate. -/
theorem apply_zero_zero_of_mem_ker (w : Fin 2 × Fin 2 → ℚ)
    (hw : w ∈ LinearMap.ker (S - (-1 : ℚ) • LinearMap.id)) : w (0, 0) = 0 := by
  have hw' := ker_sub_smul_le_span_of_eigen B T S hS e μ he hspan (-1) hw
  refine Submodule.span_induction (p := fun v _ => v (0, 0) = 0) ?_ ?_ ?_ ?_ hw'
  · rintro _ ⟨⟨i, j⟩, hp, rfl⟩
    show B (e i) (e j) (0, 0) = 0
    rw [B_e (i, j)]
    simp only [Set.mem_ofPred_eq] at hp
    fin_cases i <;> fin_cases j
    all_goals (try simp [μ] at hp ⊢)
    all_goals (try norm_num at hp)
  · rfl
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro a x _ hx; simp [hx]

/-- The span hypothesis cannot be dropped: with `V = W = ℚ`, `B = 0`, `T = id`, `μ = 1`,
`S = -id` and `c = -1`, all hypotheses but the span hold, the `-1`-eigenspace of `S` is `ℚ` and
the span is `0`. -/
theorem not_ker_le_span_without_hspan :
    ∃ (B : ℚ →ₗ[ℚ] ℚ →ₗ[ℚ] ℚ) (T S : ℚ →ₗ[ℚ] ℚ) (e : Unit → ℚ) (μ : Unit → ℚ),
      (∀ x y, S (B x y) = B (T x) (T y)) ∧ (∀ i, T (e i) = μ i • e i) ∧
      ¬ LinearMap.ker (S - (-1 : ℚ) • LinearMap.id) ≤
        Submodule.span ℚ ((fun p : Unit × Unit => B (e p.1) (e p.2)) ''
          {p | μ p.1 * μ p.2 = -1}) := by
  refine ⟨0, LinearMap.id, -LinearMap.id, fun _ => 1, fun _ => 1, by simp, by simp, ?_⟩
  intro h
  have h1 : (1 : ℚ) ∈ LinearMap.ker (-LinearMap.id - (-1 : ℚ) • LinearMap.id : ℚ →ₗ[ℚ] ℚ) := by
    simp
  have := h h1
  have h0 : {p : Unit × Unit | (1 : ℚ) = -1} = ∅ := by ext; norm_num
  simp [h0] at this

end EigenProductExample

end HodgeLadder
