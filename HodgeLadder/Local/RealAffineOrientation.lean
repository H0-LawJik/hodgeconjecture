module

public import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.FundamentalClass
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClass
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
public import HodgeConjecture.Mathlib.Topology.Category.TopPair
public import Other.AlgebraicTopology.LocalHomology.EuclideanNeighborhoodOrientation
public import HodgeLadder.Glpos.PathConnected
public import Mathlib.Basic.Sign.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Real affine maps and the local orientation class of `ℝ^d`

Upstream normalizes local classes of `ℝ^d` by one ordered affine simplex: `standardLocalClass ℚ d`
in `H_d(ℝ^d, ℝ^d ∖ {0}; ℚ)` is the class of `standardAffineSimplex d`, with ordered vertices
`e₀, …, e_{d-1}, (-1, …, -1)`. Translation by `y` moves it to `H_d(ℝ^d, ℝ^d ∖ {y}; ℚ)`
(upstream's `translationPointComplementPairMap`). Write `o_y` for that transported class.

This file computes three signs, exactly.

1. The edge matrix of upstream's reference simplex (column `i` is `v_{i+1} - v_0`) has
   determinant `(-1)^d (d + 1)`. So the reference simplex is positively oriented, in the sense of
   the determinant of `ℝ^d`, exactly when `d` is even.
2. An affine automorphism `x ↦ A x + c` of `ℝ^d` (with `A` acting on column vectors by `mulVec`)
   sends `o_y` to `sign(det A) • o_{A y + c}`.
3. An affine `d`-simplex with ordered vertices `v₀, …, v_d` and `y` in its open interior
   (all barycentric coordinates of `y` positive) is a relative cycle of `(ℝ^d, ℝ^d ∖ {y})` whose
   class is `sign(det E(v)) • (-1)^d • o_y`, with `E(v)` its edge matrix.

Signs are recorded in `docs/conventions.md`, rows "Complex orientation of ℂ^p" (the sign
`(-1)^d` of the reference simplex), "Real determinant and the topology of real matrices" and
"Cross product of complex orientations"; a row "Real local orientation and affine maps" is
proposed in `docs/sketches/local-class-product.md`. The rung `cross-orientation` reads 3 at a
point in the open identity-shuffle simplex of `s_m × s_n`.

## Main definitions

* `HodgeLadder.RealAffine.edgeMatrix`: the matrix with columns `v_{i+1} - v_0`.
* `HodgeLadder.RealAffine.affineSingularSimplex`: the singular `d`-simplex `t ↦ ∑ tᵢ vᵢ` of
  `ℝ^d`.
* `HodgeLadder.RealAffine.openSimplex`: the open affine simplex (all barycentric weights
  positive).
* `HodgeLadder.RealAffine.pointPair`: the pair `(ℝ^d, ℝ^d ∖ {y})`.
* `HodgeLadder.RealAffine.realMatrixPuncturedPairMap`, `HodgeLadder.RealAffine.affinePointPairMap`:
  the maps of pairs of an invertible matrix and of `x ↦ A x + c`.
* `HodgeLadder.RealAffine.vertexSwapMatrix`: the linear map exchanging the first two vertices of
  the reference simplex and fixing the others.

## Main results

* `HodgeLadder.RealAffine.det_edgeMatrix_standardAffineSimplex`: sign 1 above, and
  `sign_det_edgeMatrix_standardAffineSimplex_mul`: the scalar of 3 at the reference simplex is
  `1`.
* `HodgeLadder.RealAffine.relativeHomologyMap_realMatrix_standardLocalClass`: an invertible real
  matrix acts on `standardLocalClass ℚ d` by `sign(det A)`.
* `HodgeLadder.RealAffine.relativeHomologyMap_affinePointPairMap`: sign 2 above.
* `HodgeLadder.RealAffine.affineSimplex_homologyπ`: sign 3 above, with
  `exists_affineSimplex_cycle` (the cycle exists), `exists_affineSimplex_openSimplex_cycle` (the
  same simplex modulo the complement of its open simplex, the form a cross product of two
  simplices needs) and `affineSimplex_openSimplex_restrict` (that class restricted to any point of
  the open simplex).
* Reference instance: `affineSingularSimplex_standardAffineSimplex`,
  `translationPointComplementPairMap_zero`, `exists_affineSimplex_cycle_standard`,
  `affineSimplex_homologyπ_standard` (scalar `1`, upstream's class itself) and
  `openSimplex_standard_restrict_zero`.
* For `cross-orientation`: `relativeHomologyMap_point_eq_translate` (moving the point inside a
  convex support) and `relativeHomologyMap_translation_injective` (cancelling the translation).
* Route: `relativeHomologyMap_vertexSwap_standardLocalClass` (the one reflection, computed on
  chains: `R ∘ s_d = s_d ∘ (0 1)` and `s_d ∘ (0 1) + s_d` is the relative boundary of `s_d` on the
  vertex sequence `0, 1, 0, 2, …, d`), `relativeHomologyMap_realMatrix_of_det_pos` (a path in
  `{det > 0}` from `glpos-path-connected`), `weights_eq_of_det_ne_zero` (affine independence),
  `affine_transport_combination` (the affine map sending the reference vertices to `v`).

The local degree of a linear automorphism of `ℝ^d` is the sign of its determinant
[`Hatcher2002` §2.2; section unverified].
-/

@[expose] public noncomputable section

open CategoryTheory Matrix Convexity
open scoped Simplicial

namespace HodgeLadder.RealAffine

open AlgebraicTopology AlgebraicTopology.Singular

/-! ## The edge determinant of the reference simplex -/

/-- The **edge matrix** of an ordered list of `d + 1` points `v₀, …, v_d` of `ℝ^d`: column `i`
is `v_{i+1} - v₀`, so entry `(j, i)` is `(v_{i+1} - v₀)_j`. Its determinant is the oriented
volume of the simplex times `d!`. -/
def edgeMatrix {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j i => v i.succ j - v 0 j

/-- The vertices of upstream's reference simplex: vertex `k` has coordinate `j` equal to
`[k = j] - [k = d]`, so `e_k` for `k < d` and `(-1, …, -1)` for `k = d`. -/
lemma standardAffineSimplex_single_apply (d : ℕ) (k : Fin (d + 1)) (j : Fin d) :
    standardAffineSimplex d (StdSimplex.single k) j =
      (if k = Fin.castSucc j then 1 else 0) - (if k = Fin.last d then 1 else 0) := by
  simp [standardAffineSimplex, Finsupp.single_apply]

/-- Entries of the edge matrix of the reference simplex in dimension `n + 1`. Column `i < n` is
`e_{i+1} - e₀`; column `n` is `(-1, …, -1) - e₀`. -/
lemma edgeMatrix_standardAffineSimplex_apply (n : ℕ) (j i : Fin (n + 1)) :
    edgeMatrix (fun k => standardAffineSimplex (n + 1) (StdSimplex.single k)) j i =
      (if i.succ = Fin.castSucc j then 1 else 0) - (if i = Fin.last n then 1 else 0)
        - (if j = 0 then 1 else 0) := by
  simp only [edgeMatrix, of_apply, standardAffineSimplex_single_apply]
  have h0 : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := (Fin.last_pos).ne
  simp only [h0, ite_false, Fin.succ_eq_last_succ]
  have : ((0 : Fin (n + 2)) = Fin.castSucc j) ↔ j = 0 := by
    rw [eq_comm, Fin.castSucc_eq_zero_iff]
  simp only [this]
  ring

/-- **The edge determinant of upstream's reference simplex** (vertices `e₀, …, e_{d-1}`,
`(-1, …, -1)`) is `(-1)^d (d + 1)`. Proof: adding all rows to row `0` leaves
`(0, …, 0, -(d + 1))` there, and the complementary minor is the identity. So the reference
simplex has the orientation of the standard basis exactly when `d` is even (register row
"Complex orientation of ℂ^p"). -/
theorem det_edgeMatrix_standardAffineSimplex (d : ℕ) :
    (edgeMatrix fun k => standardAffineSimplex d (StdSimplex.single k)).det =
      (-1) ^ d * (d + 1) := by
  cases d with
  | zero => simp
  | succ n =>
    set E := edgeMatrix fun k => standardAffineSimplex (n + 1) (StdSimplex.single k) with hE
    have h1 := det_updateRow_sum E 0 (fun _ => 1)
    simp only [one_smul] at h1
    rw [← h1, det_succ_row_zero, Fin.sum_univ_castSucc]
    have hrow : ∀ i, (∑ k, E k) i = if i = Fin.last n then -((n : ℝ) + 2) else 0 := by
      intro i
      have := Finset.sum_apply (M := fun _ : Fin (n + 1) => ℝ) i Finset.univ (fun k => E k)
      erw [this]
      simp only [hE, edgeMatrix_standardAffineSimplex_apply, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', Finset.mem_univ]
      induction i using Fin.lastCases with
      | last =>
        have hl : ∀ x : Fin (n + 1), Fin.last n.succ ≠ x.castSucc :=
          fun x h => Fin.castSucc_ne_last x h.symm
        simp only [Fin.succ_last, ↓reduceIte, hl, Finset.sum_const_zero, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        push_cast
        ring
      | cast i =>
        simp only [Fin.castSucc_ne_last, ↓reduceIte, Fin.succ_castSucc, Fin.castSucc_inj,
          Finset.sum_ite_eq, Finset.mem_univ, Finset.sum_const_zero]
        ring
    have hsub : (E.updateRow 0 (∑ k, E k)).submatrix Fin.succ (Fin.last n).succAbove = 1 := by
      ext a b
      simp only [submatrix_apply, updateRow_ne (Fin.succ_ne_zero a), hE,
        edgeMatrix_standardAffineSimplex_apply, Fin.succAbove_last, one_apply]
      simp only [← Fin.succ_castSucc, Fin.succ_inj, Fin.castSucc_inj, Fin.castSucc_ne_last,
        Fin.succ_ne_zero, ↓reduceIte, sub_zero, eq_comm]
    simp only [updateRow_self, hrow, Fin.castSucc_ne_last, ite_false, mul_zero, zero_mul,
      Finset.sum_const_zero, zero_add, ite_true, hsub, det_one, mul_one]
    simp only [Fin.val_last, pow_succ]
    push_cast
    ring

/-- The scalar of `affineSimplex_homologyπ` at the reference simplex is `1`:
`sign((-1)^d (d + 1)) · (-1)^d = 1`. So that theorem at `v` the reference vertices and `y = 0`
returns upstream's class itself, with no sign. -/
theorem sign_det_edgeMatrix_standardAffineSimplex_mul (d : ℕ) :
    (SignType.sign (edgeMatrix fun k => standardAffineSimplex d (StdSimplex.single k)).det : ℚ) *
      (-1) ^ d = 1 := by
  rw [det_edgeMatrix_standardAffineSimplex, sign_mul, sign_pow,
    sign_pos (by positivity : (0 : ℝ) < d + 1)]
  simp only [mul_one, SignType.coe_pow]
  rw [← mul_pow]
  simp

/-! ## Affine simplices -/

/-- The pair `(ℝ^d, ℝ^d ∖ {y})`, the target of upstream's `translationPointComplementPairMap`
for `E = ℝ^d`. At `y = 0` it is `puncturedPair ℝ d`. -/
abbrev pointPair (d : ℕ) (y : Fin d → ℝ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) ({y}ᶜ : Set (Fin d → ℝ))

/-- The affine map `Δ^d → ℝ^d`, `t ↦ ∑ tᵢ vᵢ`, with ordered vertices `v₀, …, v_d`. -/
def affineSimplexMap {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ)
    (t : StdSimplex ℝ (Fin (d + 1))) : Fin d → ℝ :=
  ∑ i, t.weights i • v i

/-- The affine simplex map is continuous. -/
@[fun_prop]
lemma continuous_affineSimplexMap {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ) :
    Continuous (affineSimplexMap v) := by
  unfold affineSimplexMap
  exact continuous_finsetSum _ fun i _ =>
    (StdSimplex.continuous_weights_apply ℝ i).smul continuous_const

/-- Upstream's reference simplex is the affine simplex on its own vertices. -/
lemma affineSimplexMap_standardAffineSimplex (d : ℕ) :
    affineSimplexMap (fun k => standardAffineSimplex d (StdSimplex.single k)) =
      standardAffineSimplex d := by
  funext t j
  simp only [affineSimplexMap, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    standardAffineSimplex_single_apply, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

/-- Pushing barycentric weights forward along `g` and then taking the affine combination is the
affine combination of the composite vertex list. -/
lemma affineSimplexMap_map {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ) (g : Fin (d + 1) → Fin (d + 1))
    (t : StdSimplex ℝ (Fin (d + 1))) :
    affineSimplexMap v (t.map g) = affineSimplexMap (v ∘ g) t := by
  classical
  unfold affineSimplexMap
  simp_rw [StdSimplex.weights_map_apply, Finset.sum_smul]
  rw [show (∑ i, t.weights i • (v ∘ g) i) = ∑ i, t.weights i • v (g i) from rfl,
    ← Finset.sum_fiberwise Finset.univ g (fun x => t.weights x • v (g x))]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-- The vertices of the reference simplex add up to `0`. -/
lemma sum_standardVertices (d : ℕ) :
    ∑ k, standardAffineSimplex d (StdSimplex.single k) = 0 := by
  funext j
  simp [Finset.sum_apply, standardAffineSimplex_single_apply, Finset.sum_sub_distrib]

/-- Vertex `j < d` of the reference simplex is the basis vector `e_j`. -/
lemma standardAffineSimplex_single_castSucc (d : ℕ) (j : Fin d) :
    standardAffineSimplex d (StdSimplex.single (Fin.castSucc j)) = Pi.single j 1 := by
  funext i
  simp only [standardAffineSimplex_single_apply, Fin.castSucc_inj, Fin.castSucc_ne_last,
    ↓reduceIte, sub_zero, Pi.single_apply, eq_comm]

/-- The **affine singular simplex** of `ℝ^d` with ordered vertices `v₀, …, v_d`. -/
def affineSingularSimplex {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ) :
    (TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))) _⦋d⦌ :=
  ((TopCat.of (Fin d → ℝ)).toSSetObjEquiv _).symm
    ⟨affineSimplexMap v, continuous_affineSimplexMap v⟩

/-- Upstream's reference singular simplex is the affine simplex on its own vertices. -/
theorem affineSingularSimplex_standardAffineSimplex (d : ℕ) :
    affineSingularSimplex (fun k => standardAffineSimplex d (StdSimplex.single k)) =
      standardSingularSimplex d := by
  unfold affineSingularSimplex standardSingularSimplex
  congr 1
  ext t j
  exact congrFun (congrFun (affineSimplexMap_standardAffineSimplex d) t) j

/-- The **open affine simplex** on `v₀, …, v_d`: the points `∑ wᵢ vᵢ` with every `wᵢ > 0` and
`∑ wᵢ = 1`. -/
def openSimplex {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | ∃ w : Fin (d + 1) → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • v i = x}

/-- The open affine simplex is convex. -/
theorem convex_openSimplex {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ) : Convex ℝ (openSimplex v) := by
  rintro _ ⟨w, hw, hw1, rfl⟩ _ ⟨w', hw', hw1', rfl⟩ a b ha hb hab
  refine ⟨fun i => a * w i + b * w' i, fun i => ?_, ?_, ?_⟩
  · rcases ha.eq_or_lt with rfl | ha'
    · simp only [zero_add] at hab; subst hab; simpa using hw' i
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hw i)) (mul_nonneg hb (hw' i).le)
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, hw1', mul_one, mul_one,
      hab]
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]

/-- The barycenter of upstream's reference simplex is the origin, so `0` lies in its open
simplex. -/
theorem zero_mem_openSimplex_standardAffineSimplex (d : ℕ) :
    (0 : Fin d → ℝ) ∈ openSimplex fun k => standardAffineSimplex d (StdSimplex.single k) := by
  refine ⟨fun _ => 1 / (d + 1), fun _ => by positivity, ?_, ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, standardAffineSimplex_single_apply,
      ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      sub_self, mul_zero, Pi.zero_apply]

/-- The edge matrix applied to `c` is `∑ cᵢ (v_{i+1} - v₀)`. -/
lemma edgeMatrix_mulVec {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ) (c : Fin d → ℝ) :
    edgeMatrix v *ᵥ c = ∑ i, c i • (v i.succ - v 0) := by
  funext j
  simp [mulVec, dotProduct, edgeMatrix, Finset.sum_apply, mul_comm]

/-- **Affine independence.** Two barycentric expressions of one point in a nondegenerate simplex
have the same weights. -/
lemma weights_eq_of_det_ne_zero {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ)
    (hv : (edgeMatrix v).det ≠ 0) (a b : Fin (d + 1) → ℝ) (ha : ∑ i, a i = 1)
    (hb : ∑ i, b i = 1) (h : ∑ i, a i • v i = ∑ i, b i • v i) : a = b := by
  have hc : edgeMatrix v *ᵥ (fun i => a i.succ - b i.succ) = 0 := by
    rw [edgeMatrix_mulVec]
    have h' : ∑ i, (a i - b i) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
    have hs : ∑ i, (a i - b i) = 0 := by rw [Finset.sum_sub_distrib, ha, hb, sub_self]
    rw [Fin.sum_univ_succ] at h' hs
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    have hs' : ∑ x : Fin d, a x.succ - ∑ x : Fin d, b x.succ = -(a 0 - b 0) := by
      rw [← Finset.sum_sub_distrib]; linarith
    rw [hs', neg_smul, sub_neg_eq_add, add_comm]
    exact h'
  have hc0 := mulVec_injective_of_det_ne_zero hv (hc.trans (mulVec_zero _).symm)
  have hsucc : ∀ i : Fin d, a i.succ = b i.succ := fun i =>
    sub_eq_zero.mp (congrFun hc0 i)
  funext i
  induction i using Fin.cases with
  | zero =>
    rw [Fin.sum_univ_succ] at ha hb
    simp only [hsucc] at ha
    linarith
  | succ i => exact hsucc i

/-- A point of a face (one weight zero) of a nondegenerate simplex is outside its open
simplex. -/
lemma affineSimplexMap_map_succAbove_not_mem {k : ℕ} (v : Fin (k + 2) → Fin (k + 1) → ℝ)
    (hv : (edgeMatrix v).det ≠ 0) (i : Fin (k + 2)) (t : StdSimplex ℝ (Fin (k + 1))) :
    affineSimplexMap v (t.map i.succAbove) ∉ openSimplex v := by
  classical
  rintro ⟨w, hw, hw1, hwy⟩
  have heq := weights_eq_of_det_ne_zero v hv w (fun m => (t.map i.succAbove).weights m) hw1
    (StdSimplex.total_of_fintype _) hwy
  have h0 : (t.map i.succAbove).weights i = 0 := by
    rw [StdSimplex.weights_map_apply]
    exact Finset.sum_eq_zero fun x hx => absurd (Finset.mem_filter.1 hx).2 (Fin.succAbove_ne _ _)
  have := hw i
  rw [congrFun heq i, h0] at this
  exact lt_irrefl _ this

/-! ## Chain-level helpers -/

/-- The inclusion of cycles is injective. -/
lemma iCycles_injective (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) :
    Function.Injective (K.iCycles n).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- A cycle that is a boundary has class `0`. -/
lemma homologyπ_eq_zero_of_iCycles_eq_d (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (z : K.cycles n) (b : K.X (n + 1)) (h : (K.iCycles n).hom z = (K.d (n + 1) n).hom b) :
    (K.homologyπ n).hom z = 0 := by
  have hz : z = (K.toCycles (n + 1) n).hom b := by
    apply iCycles_injective K n
    rw [h]
    exact (congrArg (fun f => f.hom b) (K.toCycles_i (n + 1) n)).symm
  rw [hz]
  exact congrArg (fun f => f.hom b) (K.toCycles_comp_homologyπ (n + 1) n)

/-- A simplex of `X` with image in `S` vanishes in `C(X, S)`. -/
lemma relProj_ι_eq_zero {X : TopCat.{0}} (S : Set X) {k : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋k⦌) (hs : ∀ t, X.toSSetObjEquiv _ s t ∈ S) :
    ((relativeChainProjection ℚ (TopPair.ofSubset S)).f k).hom
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) s).hom (1 : ℚ)) = 0 := by
  let σ' : (TopCat.toSSet.obj (TopPair.ofSubset S).snd) _⦋k⦌ :=
    ((TopPair.ofSubset S).snd.toSSetObjEquiv _).symm
      ⟨fun t => ⟨X.toSSetObjEquiv _ s t, hs t⟩,
        ((X.toSSetObjEquiv _ s).continuous).subtype_mk _⟩
  have hσ : (TopCat.toSSet.map (TopPair.ofSubset S).map).app _ σ' = s := by
    apply (X.toSSetObjEquiv _).injective
    ext t
    rfl
  have h := congrArg (fun f => f.hom (1 : ℚ))
    (iota_subspace_relativeChainProjection ℚ (TopPair.ofSubset S) σ')
  rw [hσ] at h
  exact h

/-- Pushing a relative cycle forward along a map of pairs, on representing chains. -/
lemma iCycles_cyclesMap_apply {X Y : TopPair.{0}} (g : X ⟶ Y) (n : ℕ)
    (z : ((relativeChainFunctor ℚ).obj X).cycles n) (c : (SingularChainComplex ℚ X.fst).X n)
    (hz : (((relativeChainFunctor ℚ).obj X).iCycles n).hom z =
      ((relativeChainProjection ℚ X).f n).hom c) :
    (((relativeChainFunctor ℚ).obj Y).iCycles n).hom
        ((HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map g) n).hom z) =
      ((relativeChainProjection ℚ Y).f n).hom
        ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
          (TopPair.Hom.fst g)).f n |>.hom c) := by
  have h1 := congrArg (fun f => f.hom z)
    (HomologicalComplex.cyclesMap_i ((relativeChainFunctor ℚ).map g) n)
  have h2 := congrArg (fun f => (f.f n).hom c)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) g)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, HomologicalComplex.comp_f] at h1 h2
  rw [h1, hz, h2]

/-- The chain map of a continuous map sends a simplex to its composite. -/
lemma chainMap_ι_apply {X Y : TopCat.{0}} (g : X ⟶ Y) (n : ℕ) (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map g).f n).hom
        (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) s).hom (1 : ℚ)) =
      (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℚ ℚ)
        ((TopCat.toSSet.map g).app _ s)).hom (1 : ℚ)) := by
  have := congrArg (fun f => f.hom (1 : ℚ))
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) (TopCat.toSSet.map g)
      (ModuleCat.of ℚ ℚ) s)
  exact this

/-- The relative projection commutes with the boundary, on elements. -/
lemma relProj_d_apply (X : TopPair.{0}) (i j : ℕ) (x : (SingularChainComplex ℚ X.fst).X i) :
    (((relativeChainFunctor ℚ).obj X).d i j).hom (((relativeChainProjection ℚ X).f i).hom x) =
      ((relativeChainProjection ℚ X).f j).hom (((SingularChainComplex ℚ X.fst).d i j).hom x) := by
  have := congrArg (fun φ => φ.hom x) ((relativeChainProjection ℚ X).comm i j)
  exact this

/-- The boundary of a simplex, on elements. -/
lemma d_ι_apply (X : TopCat.{0}) {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k + 1⦌) :
    (((SingularChainComplex ℚ X).d (k + 1) k).hom
        (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom (1 : ℚ))) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ i.val •
        (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ)
          ((TopCat.toSSet.obj X).δ i x)).hom (1 : ℚ)) := by
  have := congrArg (fun φ => φ.hom (1 : ℚ))
    (SSet.ιChainComplex_d (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_zsmul, LinearMap.smul_apply] at this
  exact this

/-- On classes of cycles, the map of a map of pairs is the class of the pushed cycle. -/
lemma relativeHomologyMap_homologyπ {X Y : TopPair.{0}} (g : X ⟶ Y) (n : ℕ)
    (z : ((relativeChainFunctor ℚ).obj X).cycles n) :
    relativeHomologyMap ℚ n g ((((relativeChainFunctor ℚ).obj X).homologyπ n).hom z) =
      (((relativeChainFunctor ℚ).obj Y).homologyπ n).hom
        ((HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map g) n).hom z) := by
  have h := congrArg (fun φ => φ.hom z)
    (HomologicalComplex.homologyπ_naturality ((relativeChainFunctor ℚ).map g) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simp only [relativeHomologyMap, relativeHomologyFunctor, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map]
  exact h

/-- Restricting the support, on representing chains. -/
lemma iCycles_cyclesMap_supportInclusion {d : ℕ} {Z W : Set (Fin d → ℝ)} (h : Z ⊆ W) (n : ℕ)
    (z : ((relativeChainFunctor ℚ).obj
      (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) Wᶜ)).cycles n)
    (c : (SingularChainComplex ℚ (TopCat.of (Fin d → ℝ))).X n)
    (hz : (((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) Wᶜ)).iCycles n).hom z =
      ((relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) Wᶜ)).f n).hom c) :
    (((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) Zᶜ)).iCycles n).hom
        ((HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map
          (supportInclusionPairMap (TopCat.of (Fin d → ℝ)) h)) n).hom z) =
      ((relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) Zᶜ)).f n).hom
        c := by
  have h1 := congrArg (fun f => f.hom z)
    (HomologicalComplex.cyclesMap_i ((relativeChainFunctor ℚ).map
      (supportInclusionPairMap (TopCat.of (Fin d → ℝ)) h)) n)
  have h2 := congrArg (fun f => (f.f n).hom c)
    (relativeChainProjection_supportInclusion ℚ (TopCat.of (Fin d → ℝ)) h)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, HomologicalComplex.comp_f] at h1 h2
  rw [h1, hz]
  exact h2

/-- An element killed by the differential is the inclusion of a cycle. -/
lemma exists_cycles_of_d_eq_zero (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) (x : K.X n)
    (hx : (K.d n ((ComplexShape.down ℕ).next n)).hom x = 0) :
    ∃ z : K.cycles n, (K.iCycles n).hom z = x := by
  let f : ModuleCat.of ℚ ℚ ⟶ K.X n := ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ x)
  have hf : f ≫ K.d n ((ComplexShape.down ℕ).next n) = 0 := by
    ext
    simp [f, hx]
  refine ⟨(K.liftCycles f _ rfl hf).hom 1, ?_⟩
  have := congrArg (fun φ => φ.hom (1 : ℚ)) (K.liftCycles_i f _ rfl hf)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  rw [this]
  simp [f]

/-! ## Affine simplices are relative cycles -/

/-- An affine simplex of positive dimension whose faces lie in `B` is a relative cycle of
`(ℝ^d, B)`. -/
lemma exists_affineSimplex_cycle_of_faces {k : ℕ} (v : Fin (k + 2) → Fin (k + 1) → ℝ)
    (B : Set (Fin (k + 1) → ℝ))
    (hB : ∀ (i : Fin (k + 2)) (t : StdSimplex ℝ (Fin (k + 1))),
      affineSimplexMap v (t.map i.succAbove) ∈ B) :
    ∃ z : ((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := TopCat.of (Fin (k + 1) → ℝ)) B)).cycles (k + 1),
      (((relativeChainFunctor ℚ).obj
          (TopPair.ofSubset (X := TopCat.of (Fin (k + 1) → ℝ)) B)).iCycles (k + 1)).hom z =
        ((relativeChainProjection ℚ
            (TopPair.ofSubset (X := TopCat.of (Fin (k + 1) → ℝ)) B)).f (k + 1)).hom
          (((TopCat.toSSet.obj (TopCat.of (Fin (k + 1) → ℝ))).ιChainComplex
            (R := ModuleCat.of ℚ ℚ) (affineSingularSimplex v)).hom (1 : ℚ)) := by
  apply exists_cycles_of_d_eq_zero
  rw [ChainComplex.next_nat_succ]
  refine (relProj_d_apply (TopPair.ofSubset (X := TopCat.of (Fin (k + 1) → ℝ)) B) (k + 1) k
    _).trans ?_
  refine (congrArg _ (d_ι_apply (TopCat.of (Fin (k + 1) → ℝ)) (affineSingularSimplex v))).trans ?_
  refine (map_sum _ _ _).trans (Finset.sum_eq_zero fun i _ => ?_)
  refine (map_zsmul _ _ _).trans ?_
  have hs : ∀ t, (TopCat.of (Fin (k + 1) → ℝ)).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of (Fin (k + 1) → ℝ))).δ i (affineSingularSimplex v)) t ∈ B := by
    intro t
    rw [TopCat.toSSetObjEquiv_δ_apply]
    exact hB i t
  have h0 := relProj_ι_eq_zero (X := TopCat.of (Fin (k + 1) → ℝ)) (k := k) B
    ((TopCat.toSSet.obj (TopCat.of (Fin (k + 1) → ℝ))).δ i (affineSingularSimplex v)) hs
  rw [h0, smul_zero]

/-- In dimension `0` every simplex is a relative cycle. -/
lemma exists_affineSimplex_cycle_zero (v : Fin 1 → Fin 0 → ℝ) (B : Set (Fin 0 → ℝ)) :
    ∃ z : ((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := TopCat.of (Fin 0 → ℝ)) B)).cycles 0,
      (((relativeChainFunctor ℚ).obj
          (TopPair.ofSubset (X := TopCat.of (Fin 0 → ℝ)) B)).iCycles 0).hom z =
        ((relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of (Fin 0 → ℝ)) B)).f 0).hom
          (((TopCat.toSSet.obj (TopCat.of (Fin 0 → ℝ))).ιChainComplex
            (R := ModuleCat.of ℚ ℚ) (affineSingularSimplex v)).hom (1 : ℚ)) := by
  apply exists_cycles_of_d_eq_zero
  rw [HomologicalComplex.shape _ _ _ (by simp)]
  rfl

/-- **An affine simplex is a relative cycle modulo the complement of its open simplex**: every
face lies in the boundary, which misses the open simplex when `det E(v) ≠ 0`. The cross product
of two such cycles lives on the complement of a convex product, where
`relativeHomologyMap_point_eq_translate` moves the point (rung `cross-orientation`). -/
theorem exists_affineSimplex_openSimplex_cycle {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ)
    (hv : (edgeMatrix v).det ≠ 0) :
    ∃ z : ((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).cycles d,
      (((relativeChainFunctor ℚ).obj
          (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).iCycles d).hom z =
        ((relativeChainProjection ℚ
            (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).f d).hom
          (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
            (affineSingularSimplex v)).hom (1 : ℚ)) := by
  cases d with
  | zero => exact exists_affineSimplex_cycle_zero v _
  | succ k =>
    exact exists_affineSimplex_cycle_of_faces v _
      fun i t => affineSimplexMap_map_succAbove_not_mem v hv i t

/-- An affine simplex whose interior contains `y` is a relative cycle of `(ℝ^d, ℝ^d ∖ {y})`:
every face misses `y`, since `y` has positive barycentric coordinates. -/
theorem exists_affineSimplex_cycle {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ)
    (hv : (edgeMatrix v).det ≠ 0) (y : Fin d → ℝ) (w : Fin (d + 1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hy : ∑ i, w i • v i = y) :
    ∃ z : ((relativeChainFunctor ℚ).obj (pointPair d y)).cycles d,
      (((relativeChainFunctor ℚ).obj (pointPair d y)).iCycles d).hom z =
        ((relativeChainProjection ℚ (pointPair d y)).f d).hom
          (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
            (affineSingularSimplex v)).hom (1 : ℚ)) := by
  cases d with
  | zero => exact exists_affineSimplex_cycle_zero v _
  | succ k =>
    refine exists_affineSimplex_cycle_of_faces v _ fun i t h => ?_
    exact affineSimplexMap_map_succAbove_not_mem v hv i t
      (h ▸ ⟨w, hw, hw1, hy⟩ : affineSimplexMap v (t.map i.succAbove) ∈ openSimplex v)

/-- The reference cycle: `affineSimplex_homologyπ`'s hypotheses hold at the reference simplex. -/
theorem exists_affineSimplex_cycle_standard (d : ℕ) :
    ∃ z : ((relativeChainFunctor ℚ).obj (pointPair d 0)).cycles d,
      (((relativeChainFunctor ℚ).obj (pointPair d 0)).iCycles d).hom z =
        ((relativeChainProjection ℚ (pointPair d 0)).f d).hom
          (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
            (affineSingularSimplex fun k => standardAffineSimplex d (StdSimplex.single k))).hom
              (1 : ℚ)) := by
  refine ⟨(standardLocalCycle ℚ d).hom 1, ?_⟩
  have h := congrArg (fun f => f.hom (1 : ℚ)) (standardLocalCycle_inclusion ℚ d)
  rw [affineSingularSimplex_standardAffineSimplex]
  exact h

/-! ## Maps of pairs -/

/-- An invertible real matrix as a self-map of `(ℝ^d, ℝ^d ∖ {0})`; the real counterpart of
upstream's `complexMatrixPuncturedPairMap`. -/
def realMatrixPuncturedPairMap (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0) :
    puncturedPair ℝ d ⟶ puncturedPair ℝ d :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun x => A *ᵥ x, continuous_const.matrix_mulVec continuous_id⟩)
    fun x hx h => hx (mulVec_injective_of_det_ne_zero hA (by simpa using h))

/-- Maps of pairs of matrices compose as the matrix product. -/
lemma realMatrixPuncturedPairMap_comp (d : ℕ) {A B : Matrix (Fin d) (Fin d) ℝ} (hA : A.det ≠ 0)
    (hB : B.det ≠ 0) (hAB : (A * B).det ≠ 0) :
    realMatrixPuncturedPairMap d B hB ≫ realMatrixPuncturedPairMap d A hA =
      realMatrixPuncturedPairMap d (A * B) hAB := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    exact Subtype.ext (Matrix.mulVec_mulVec x.1 A B)
  · ext x
    exact Matrix.mulVec_mulVec x A B

/-- The map of pairs of a matrix depends only on the matrix. -/
lemma realMatrixPuncturedPairMap_congr (d : ℕ) {A A' : Matrix (Fin d) (Fin d) ℝ} (h : A = A')
    (hA : A.det ≠ 0) (hA' : A'.det ≠ 0) :
    realMatrixPuncturedPairMap d A hA = realMatrixPuncturedPairMap d A' hA' := by
  subst h
  rfl

/-- An invertible affine map sends the complement of `y` into the complement of its image. -/
lemma affine_mem_compl {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0)
    (c y : Fin d → ℝ) :
    ∀ x ∈ ({y}ᶜ : Set (Fin d → ℝ)), A *ᵥ x + c ∈ ({A *ᵥ y + c}ᶜ : Set (Fin d → ℝ)) :=
  fun _ hx h => hx (mulVec_injective_of_det_ne_zero hA (add_right_cancel h))

/-- The affine map `x ↦ A x + c` (`A` invertible, acting by `mulVec`) as a map of pairs
`(ℝ^d, ℝ^d ∖ {y}) ⟶ (ℝ^d, ℝ^d ∖ {A y + c})`. -/
def affinePointPairMap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0)
    (c y : Fin d → ℝ) : pointPair d y ⟶ pointPair d (A *ᵥ y + c) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun x => A *ᵥ x + c,
      (continuous_const.matrix_mulVec continuous_id).add continuous_const⟩)
    (affine_mem_compl A hA c y)

/-- `x ↦ A x + c` as a map of pairs `(ℝ^d, ℝ^d ∖ {y}) ⟶ (ℝ^d, ℝ^d ∖ {y'})`, for `A y + c = y'`. -/
def affinePairMap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0)
    (c y y' : Fin d → ℝ) (h : A *ᵥ y + c = y') : pointPair d y ⟶ pointPair d y' :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun x => A *ᵥ x + c,
      (continuous_const.matrix_mulVec continuous_id).add continuous_const⟩)
    (h ▸ affine_mem_compl A hA c y)

/-- Translation by `0` is the identity map of pairs. -/
theorem translationPointComplementPairMap_zero (d : ℕ) :
    translationPointComplementPairMap (Fin d → ℝ) 0 = 𝟙 (puncturedPair ℝ d) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x; exact Subtype.ext (add_zero (x.1 : Fin d → ℝ))
  · ext x; exact add_zero (M := Fin d → ℝ) x

/-- Translation back: `x ↦ x - y`, from `(ℝ^d, ℝ^d ∖ {y})` to `(ℝ^d, ℝ^d ∖ {0})`. -/
def translateBackPairMap (d : ℕ) (y : Fin d → ℝ) : pointPair d y ⟶ puncturedPair ℝ d :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun x => x - y, continuous_id.sub continuous_const⟩)
    fun _ hx h => hx (sub_eq_zero.mp h)

/-- Translation by `y` followed by translation by `-y` is the identity map of pairs. -/
lemma translation_comp_translateBack (d : ℕ) (y : Fin d → ℝ) :
    translationPointComplementPairMap (Fin d → ℝ) y ≫ translateBackPairMap d y =
      𝟙 (puncturedPair ℝ d) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    exact Subtype.ext (add_sub_cancel_right (x.1 : Fin d → ℝ) y)
  · ext x
    exact add_sub_cancel_right (G := Fin d → ℝ) x y

/-- Translation by `y` is injective on relative homology. -/
theorem relativeHomologyMap_translation_injective {d : ℕ} (n : ℕ) (y : Fin d → ℝ) :
    Function.Injective
      (relativeHomologyMap ℚ n (translationPointComplementPairMap (Fin d → ℝ) y)) := by
  intro a b h
  have h' := congrArg (relativeHomologyMap ℚ n (translateBackPairMap d y)) h
  simp only [← LinearMap.comp_apply, ← relativeHomologyMap_comp,
    translation_comp_translateBack, relativeHomologyMap_id, LinearMap.id_apply] at h'
  exact h'

/-- `x ↦ A (x + y) + c` is `x ↦ A x` followed by translation by `A y + c`, as maps of pairs. -/
lemma translation_comp_affinePointPairMap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det ≠ 0) (c y : Fin d → ℝ) :
    translationPointComplementPairMap (Fin d → ℝ) y ≫ affinePointPairMap A hA c y =
      realMatrixPuncturedPairMap d A hA ≫
        translationPointComplementPairMap (Fin d → ℝ) (A *ᵥ y + c) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    apply Subtype.ext
    change A *ᵥ (x.1 + y) + c = A *ᵥ x.1 + (A *ᵥ y + c)
    rw [mulVec_add, add_assoc]
  · ext (x : Fin d → ℝ)
    change A *ᵥ (x + y) + c = A *ᵥ x + (A *ᵥ y + c)
    rw [mulVec_add, add_assoc]

/-! ## The one reflection -/

/-- The linear map of `ℝ^d` that exchanges vertices `0` and `1` of upstream's reference simplex
and fixes the others: column `j` is the image of `e_j`, the vertex `swap 0 1 j`. For `d = 1` it
is `x ↦ -x` (the two vertices are `1` and `-1`); for `d ≥ 2` it exchanges the coordinates `0`
and `1`. -/
def vertexSwapMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j =>
    standardAffineSimplex d (StdSimplex.single (Equiv.swap 0 1 (Fin.castSucc j))) i

/-- The vertex swap has determinant `-1` in every positive dimension. -/
theorem det_vertexSwapMatrix (n : ℕ) : (vertexSwapMatrix (n + 1)).det = -1 := by
  cases n with
  | zero =>
    rw [det_fin_one]
    simp [vertexSwapMatrix, standardAffineSimplex_single_apply]
  | succ m =>
    have h : vertexSwapMatrix (m + 2) =
        (Equiv.swap (0 : Fin (m + 2)) 1).permMatrix ℝ := by
      ext i j
      simp only [vertexSwapMatrix, of_apply, standardAffineSimplex_single_apply,
        PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
      have hc : Equiv.swap (0 : Fin (m + 3)) 1 (Fin.castSucc j) =
          Fin.castSucc (Equiv.swap (0 : Fin (m + 2)) 1 j) := by
        have h0 : (0 : Fin (m + 3)) = Fin.castSucc 0 := rfl
        have h1 : (1 : Fin (m + 3)) = Fin.castSucc 1 := rfl
        rw [h0, h1, Equiv.swap_apply_def, Equiv.swap_apply_def]
        simp only [Fin.castSucc_inj]
        split_ifs <;> rfl
      rw [hc]
      simp only [Fin.castSucc_ne_last, Fin.castSucc_inj, ↓reduceIte, sub_zero]
      exact if_congr (by rw [Equiv.swap_apply_eq_iff, eq_comm]) rfl rfl
    rw [h, det_permutation, Equiv.Perm.sign_swap (Fin.zero_ne_one)]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]

/-- The vertex swap permutes the vertices of the reference simplex by `swap 0 1`. -/
lemma vertexSwapMatrix_mulVec_single (n : ℕ) (k : Fin (n + 2)) :
    vertexSwapMatrix (n + 1) *ᵥ standardAffineSimplex (n + 1) (StdSimplex.single k) =
      standardAffineSimplex (n + 1) (StdSimplex.single (Equiv.swap 0 1 k)) := by
  have hcol : ∀ j : Fin (n + 1), vertexSwapMatrix (n + 1) *ᵥ
      standardAffineSimplex (n + 1) (StdSimplex.single (Fin.castSucc j)) =
        standardAffineSimplex (n + 1) (StdSimplex.single (Equiv.swap 0 1 (Fin.castSucc j))) := by
    intro j
    rw [standardAffineSimplex_single_castSucc, mulVec_single_one]
    rfl
  induction k using Fin.lastCases with
  | cast j => exact hcol j
  | last =>
    have h1 := sum_standardVertices (n + 1)
    rw [Fin.sum_univ_castSucc] at h1
    have h2 := sum_standardVertices (n + 1)
    rw [← Equiv.sum_comp (Equiv.swap (0 : Fin (n + 2)) 1), Fin.sum_univ_castSucc] at h2
    rw [eq_neg_of_add_eq_zero_right h1, mulVec_neg, mulVec_sum]
    simp_rw [hcol]
    rw [eq_neg_of_add_eq_zero_right h2]

/-- On the reference simplex, the vertex swap is precomposition with `swap 0 1`. -/
lemma vertexSwapMatrix_mulVec_standardAffineSimplex (n : ℕ)
    (t : StdSimplex ℝ (Fin (n + 2))) :
    vertexSwapMatrix (n + 1) *ᵥ standardAffineSimplex (n + 1) t =
      standardAffineSimplex (n + 1) (t.map (Equiv.swap 0 1)) := by
  rw [← affineSimplexMap_standardAffineSimplex, affineSimplexMap_map]
  unfold affineSimplexMap
  rw [mulVec_sum]
  simp_rw [mulVec_smul, vertexSwapMatrix_mulVec_single]
  rfl

/-- The value of `p.succAbove i`: `i` below `p`, `i + 1` from `p` on. -/
lemma val_succAbove_eq {m : ℕ} (p : Fin (m + 1)) (i : Fin m) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), Fin.val_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega), Fin.val_succ]

/-- The vertex sequence `0, 1, 0, 2, 3, …, n + 1` of the `(n + 2)`-simplex whose boundary relates
the reference simplex to its vertex swap. -/
def swapPrism (n : ℕ) (k : Fin (n + 3)) : Fin (n + 2) :=
  ⟨if k.val = 2 then 0 else if k.val ≤ 1 then k.val else k.val - 1, by split_ifs <;> omega⟩

/-- Face `0` of the vertex sequence `0, 1, 0, 2, …` is the swap `1, 0, 2, …`. -/
lemma swapPrism_comp_succAbove_zero (n : ℕ) :
    swapPrism n ∘ (0 : Fin (n + 3)).succAbove = Equiv.swap 0 1 := by
  funext x
  apply Fin.ext
  rw [Equiv.swap_apply_def]
  simp only [Function.comp_apply, swapPrism, Fin.succAbove_zero, Fin.val_succ]
  have e0 : ((0 : Fin (n + 2)) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin (n + 2)) : ℕ) = 1 := by simp
  have hx0 : x = 0 ↔ x.val = 0 := by rw [Fin.ext_iff, e0]
  have hx1 : x = 1 ↔ x.val = 1 := by rw [Fin.ext_iff, e1]
  by_cases a0 : x.val = 0
  · rw [ite_eq_left (hx0.2 a0), e1, ite_eq_right (by omega), ite_eq_left (by omega)]; omega
  · by_cases a1 : x.val = 1
    · rw [ite_eq_right (fun h => a0 (hx0.1 h)), ite_eq_left (hx1.2 a1), e0, ite_eq_left (by omega)]
    · rw [ite_eq_right (fun h => a0 (hx0.1 h)), ite_eq_right (fun h => a1 (hx1.1 h)),
        ite_eq_right (by omega),
        ite_eq_right (by omega)]
      omega

/-- Face `2` of the vertex sequence `0, 1, 0, 2, …` is the identity sequence. -/
lemma swapPrism_comp_succAbove_two (n : ℕ) :
    swapPrism n ∘ (2 : Fin (n + 3)).succAbove = id := by
  funext x
  apply Fin.ext
  simp only [Function.comp_apply, swapPrism, id, val_succAbove_eq]
  have h2 : ((2 : Fin (n + 3)) : ℕ) = 2 := by simp
  rw [h2]
  split_ifs <;> omega

/-- Every other face of the vertex sequence `0, 1, 0, 2, …` omits some vertex. -/
lemma swapPrism_comp_succAbove_ne (n : ℕ) (i : Fin (n + 3)) (h0 : i ≠ 0) (h2 : i ≠ 2) :
    ∃ m : Fin (n + 2), ∀ x, swapPrism n (i.succAbove x) ≠ m := by
  have h0' : i.val ≠ 0 := fun h => h0 (Fin.ext h)
  have h2v : ((2 : Fin (n + 3)) : ℕ) = 2 := by simp
  have h2' : i.val ≠ 2 := fun h => h2 (Fin.ext (by rw [h, h2v]))
  refine ⟨⟨if i.val = 1 then 1 else i.val - 1, by split_ifs <;> omega⟩, fun x hx => ?_⟩
  have hv := congrArg Fin.val hx
  simp only [swapPrism, val_succAbove_eq] at hv
  split_ifs at hv <;> omega

/-- The singular simplex `t ↦ s_{n+1}(g_* t)` of `ℝ^{n+1}`: the reference simplex on the vertex
sequence `g`. -/
noncomputable def stdMapSimplex (n : ℕ) {k : ℕ} (g : Fin (k + 1) → Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of (Fin (n + 1) → ℝ))) _⦋k⦌ :=
  ((TopCat.of (Fin (n + 1) → ℝ)).toSSetObjEquiv _).symm
    ⟨fun t => standardAffineSimplex (n + 1) (t.map g), by fun_prop⟩

/-- Faces of `stdMapSimplex` are `stdMapSimplex` of the composite vertex sequence. -/
lemma δ_stdMapSimplex (n : ℕ) {k : ℕ} (g : Fin (k + 2) → Fin (n + 2)) (i : Fin (k + 2)) :
    (TopCat.toSSet.obj (TopCat.of (Fin (n + 1) → ℝ))).δ i (stdMapSimplex n g) =
      stdMapSimplex n (g ∘ i.succAbove) := by
  apply ((TopCat.of (Fin (n + 1) → ℝ)).toSSetObjEquiv _).injective
  ext t : 1
  change standardAffineSimplex (n + 1) ((StdSimplex.map i.succAbove t).map g) =
    standardAffineSimplex (n + 1) (t.map (g ∘ i.succAbove))
  rw [StdSimplex.map_comp]

/-- On the identity vertex sequence, `stdMapSimplex` is upstream's reference simplex. -/
lemma stdMapSimplex_id (n : ℕ) :
    stdMapSimplex n (id : Fin (n + 2) → Fin (n + 2)) = standardSingularSimplex (n + 1) := by
  apply ((TopCat.of (Fin (n + 1) → ℝ)).toSSetObjEquiv _).injective
  ext t : 1
  change standardAffineSimplex (n + 1) (t.map id) = standardAffineSimplex (n + 1) t
  rw [StdSimplex.map_id]

/-- A reference simplex on a vertex sequence that misses a vertex misses the origin. -/
lemma stdMapSimplex_ne_zero (n : ℕ) {k : ℕ} (g : Fin (k + 1) → Fin (n + 2)) (m : Fin (n + 2))
    (hm : ∀ x, g x ≠ m) (t : StdSimplex ℝ (Fin (k + 1))) :
    standardAffineSimplex (n + 1) (t.map g) ≠ 0 := by
  classical
  apply standardAffineSimplex_ne_zero_of_coord_zero (n + 1) _ m
  rw [StdSimplex.weights_map_apply]
  exact Finset.sum_eq_zero fun x hx => absurd (Finset.mem_filter.1 hx).2 (hm x)

/-- The vertex swap applied to the reference simplex is the reference simplex on the vertex
sequence `swap 0 1`. -/
lemma vertexSwap_map_standardSingularSimplex (n : ℕ) (hR : (vertexSwapMatrix (n + 1)).det ≠ 0) :
    (TopCat.toSSet.map (TopPair.Hom.fst
        (realMatrixPuncturedPairMap (n + 1) (vertexSwapMatrix (n + 1)) hR))).app _
        (standardSingularSimplex (n + 1)) =
      stdMapSimplex n (Equiv.swap 0 1) := by
  apply ((TopCat.of (Fin (n + 1) → ℝ)).toSSetObjEquiv _).injective
  ext t : 1
  change vertexSwapMatrix (n + 1) *ᵥ standardAffineSimplex (n + 1) t =
    standardAffineSimplex (n + 1) (t.map (Equiv.swap 0 1))
  exact vertexSwapMatrix_mulVec_standardAffineSimplex n t

/-- **The one reflection, on chains.** The vertex swap reverses upstream's local orientation:
`R ∘ σ` is `σ` with vertices `0` and `1` exchanged, and `σ ∘ (0 1) + σ` is a relative boundary
(the boundary of `σ` on the vertex sequence `0, 1, 0, 2, …, d`, whose other faces miss the
origin). -/
theorem relativeHomologyMap_vertexSwap_standardLocalClass (n : ℕ) :
    relativeHomologyMap ℚ (n + 1)
        (realMatrixPuncturedPairMap (n + 1) (vertexSwapMatrix (n + 1))
          (by rw [det_vertexSwapMatrix]; norm_num))
        (standardLocalClass ℚ (n + 1)) =
      -standardLocalClass ℚ (n + 1) := by
  have hR : (vertexSwapMatrix (n + 1)).det ≠ 0 := by rw [det_vertexSwapMatrix]; norm_num
  set f := realMatrixPuncturedPairMap (n + 1) (vertexSwapMatrix (n + 1)) hR
  set K := (relativeChainFunctor ℚ).obj (puncturedPair ℝ (n + 1))
  set z0 := (standardLocalCycle ℚ (n + 1)).hom (1 : ℚ)
  set z1 := (HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map f) (n + 1)).hom z0
  let ι := fun {k : ℕ} (x : (TopCat.toSSet.obj (TopCat.of (Fin (n + 1) → ℝ))) _⦋k⦌) =>
    ((TopCat.toSSet.obj (TopCat.of (Fin (n + 1) → ℝ))).ιChainComplex
      (R := ModuleCat.of ℚ ℚ) x).hom (1 : ℚ)
  have hz0 : (K.iCycles (n + 1)).hom z0 =
      ((relativeChainProjection ℚ (puncturedPair ℝ (n + 1))).f (n + 1)).hom
        (ι (stdMapSimplex n id)) := by
    rw [stdMapSimplex_id]
    exact congrArg (fun f => f.hom (1 : ℚ)) (standardLocalCycle_inclusion ℚ (n + 1))
  have hz1 : (K.iCycles (n + 1)).hom z1 =
      ((relativeChainProjection ℚ (puncturedPair ℝ (n + 1))).f (n + 1)).hom
        (ι (stdMapSimplex n (Equiv.swap 0 1))) := by
    rw [iCycles_cyclesMap_apply f (n + 1) z0 _ hz0, stdMapSimplex_id]
    erw [chainMap_ι_apply]
    rw [vertexSwap_map_standardSingularSimplex n hR]
    rfl
  have hbd : (K.iCycles (n + 1)).hom (z1 + z0) =
      (K.d (n + 2) (n + 1)).hom
        (((relativeChainProjection ℚ (puncturedPair ℝ (n + 1))).f (n + 2)).hom
          (ι (stdMapSimplex n (swapPrism n)))) := by
    erw [relProj_d_apply]
    rw [map_add, hz0, hz1]
    erw [d_ι_apply]
    have h2v : ((2 : Fin (n + 3)) : ℕ) = 2 := by simp
    have h02 : (0 : Fin (n + 3)) ≠ 2 := fun h => by
      have := congrArg Fin.val h
      rw [h2v] at this
      simp at this
    erw [map_sum]
    rw [Finset.sum_eq_add (0 : Fin (n + 3)) 2 h02 ?_ (by simp) (by simp)]
    · erw [δ_stdMapSimplex, δ_stdMapSimplex]
      rw [swapPrism_comp_succAbove_zero, swapPrism_comp_succAbove_two, h2v]
      simp only [Fin.val_zero, pow_zero, one_smul, neg_one_sq]
      rfl
    · intro i _ ⟨hi0, hi2⟩
      erw [map_zsmul, δ_stdMapSimplex]
      obtain ⟨m, hm⟩ := swapPrism_comp_succAbove_ne n i hi0 hi2
      erw [relProj_ι_eq_zero _ _ fun t => stdMapSimplex_ne_zero n _ m hm t]
      rw [smul_zero]
  have h0 := homologyπ_eq_zero_of_iCycles_eq_d K (n + 1) (z1 + z0) _ hbd
  rw [map_add] at h0
  have hnat := congrArg (fun φ => φ.hom z0)
    (HomologicalComplex.homologyπ_naturality ((relativeChainFunctor ℚ).map f) (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  change (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map f) (n + 1)).hom
      ((K.homologyπ (n + 1)).hom z0) = -(K.homologyπ (n + 1)).hom z0
  rw [hnat]
  exact eq_neg_of_add_eq_zero_left h0

/-! ## The sign of an affine automorphism -/

/-- A path of invertible real matrices from `1` to `A` gives a homotopy of pairs from the identity
of `(ℝ^d, ℝ^d ∖ {0})` to the map of `A`; the real copy of upstream's
`complexMatrixPuncturedPairHomotopy`. -/
def realMatrixPuncturedPairHomotopy (d : ℕ) {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.det ≠ 0)
    (H : C(unitInterval, Matrix (Fin d) (Fin d) ℝ)) (h0 : H 0 = 1) (h1 : H 1 = A)
    (hH : ∀ t, (H t).det ≠ 0) :
    TopPair.Homotopy (𝟙 (puncturedPair ℝ d)) (realMatrixPuncturedPairMap d A hA) where
  fst :=
    { toFun := fun tx => (H tx.1).mulVec tx.2
      continuous_toFun := by fun_prop
      map_zero_left := fun x => by
        simp only [h0]
        exact Matrix.one_mulVec x
      map_one_left := fun x => by
        simp only [h1]
        rfl }
  snd :=
    { toFun := fun tx =>
        ⟨(H tx.1).mulVec tx.2.1, by
          intro hz
          apply tx.2.2
          apply (H tx.1).mulVec_injective_of_det_ne_zero (hH tx.1)
          simpa using hz⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have : Continuous (fun tx : unitInterval × (Fin d → ℝ) => (H tx.1).mulVec tx.2) := by
          fun_prop
        exact this.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      map_zero_left := fun x => by
        apply Subtype.ext
        simp only [h0]
        exact Matrix.one_mulVec x.1
      map_one_left := fun x => by
        apply Subtype.ext
        simp only [h1]
        rfl }
  w := rfl

/-- A real matrix of positive determinant acts trivially on relative homology of
`(ℝ^d, ℝ^d ∖ {0})`. -/
theorem relativeHomologyMap_realMatrix_of_det_pos (d n : ℕ) {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : 0 < A.det) (x : RelativeHomology ℚ (puncturedPair ℝ d) n) :
    relativeHomologyMap ℚ n (realMatrixPuncturedPairMap d A hA.ne') x = x := by
  have hJ := HodgeLadder.Glpos.joinedIn_one_of_det_pos hA
  have h := (realMatrixPuncturedPairHomotopy d hA.ne' hJ.somePath.toContinuousMap
    hJ.somePath.source hJ.somePath.target (fun t => ne_of_gt (hJ.somePath_mem t))
    ).relativeHomologyMap_apply_eq (R := ℚ) n x
  rw [← h, relativeHomologyMap_id]
  rfl

/-- **An invertible real matrix acts on upstream's local class of `ℝ^d` by the sign of its
determinant**: `A_* [σ_d] = sign(det A) • [σ_d]` in `H_d(ℝ^d, ℝ^d ∖ {0}; ℚ)`. For
`det A > 0` a path to `1` in `{M | 0 < det M}` (`glpos-path-connected`) gives a homotopy of
pairs to the identity; for `det A < 0`, `A = (A R) R` with `R` the vertex swap. The real
counterpart of upstream's `relativeHomologyMap_complexMatrix_standardComplexLocalClass`, where
the sign is always `+`. -/
theorem relativeHomologyMap_realMatrix_standardLocalClass (d : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0) :
    relativeHomologyMap ℚ d (realMatrixPuncturedPairMap d A hA) (standardLocalClass ℚ d) =
      (SignType.sign A.det : ℚ) • standardLocalClass ℚ d := by
  rcases hA.lt_or_gt with hneg | hpos
  · cases d with
    | zero => simp at hneg; linarith
    | succ n =>
      have hR : (vertexSwapMatrix (n + 1)).det ≠ 0 := by rw [det_vertexSwapMatrix]; norm_num
      set R := vertexSwapMatrix (n + 1)
      have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR
      have hBdet : (A * R⁻¹).det = -A.det := by
        rw [det_mul, det_nonsing_inv, det_vertexSwapMatrix]
        simp
      have hB : 0 < (A * R⁻¹).det := by rw [hBdet]; linarith
      have hBR : A * R⁻¹ * R = A := by rw [Matrix.mul_assoc, nonsing_inv_mul R hRu, Matrix.mul_one]
      rw [← realMatrixPuncturedPairMap_congr (n + 1) hBR (by rw [hBR]; exact hA) hA,
        ← realMatrixPuncturedPairMap_comp (n + 1) hB.ne' hR, relativeHomologyMap_comp,
        LinearMap.comp_apply, relativeHomologyMap_vertexSwap_standardLocalClass, map_neg,
        relativeHomologyMap_realMatrix_of_det_pos _ _ hB, sign_neg hneg]
      simp
  · rw [relativeHomologyMap_realMatrix_of_det_pos _ _ hpos, sign_pos hpos]
    simp

/-- **An affine automorphism `x ↦ A x + c` of `ℝ^d` acts on the transported local orientation
class by `sign(det A)`**, exactly: it sends `o_y`, the translate to `y` of
`standardLocalClass ℚ d`, to `sign(det A) • o_{A y + c}`. Conjugate
`relativeHomologyMap_realMatrix_standardLocalClass` by the translations by `-y` and `A y + c`. -/
theorem relativeHomologyMap_affinePointPairMap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det ≠ 0) (c y : Fin d → ℝ) :
    relativeHomologyMap ℚ d (affinePointPairMap A hA c y)
        (relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) y)
          (standardLocalClass ℚ d)) =
      (SignType.sign A.det : ℚ) •
        relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) (A *ᵥ y + c))
          (standardLocalClass ℚ d) := by
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, translation_comp_affinePointPairMap,
    relativeHomologyMap_comp, LinearMap.comp_apply,
    relativeHomologyMap_realMatrix_standardLocalClass,
    map_smul]

/-- `relativeHomologyMap_affinePointPairMap` with the image point named: for `A y + c = y'`,
`x ↦ A x + c` sends `o_y` to `sign(det A) • o_{y'}`. -/
theorem relativeHomologyMap_affinePairMap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det ≠ 0) (c y y' : Fin d → ℝ) (h : A *ᵥ y + c = y') :
    relativeHomologyMap ℚ d (affinePairMap A hA c y y' h)
        (relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) y)
          (standardLocalClass ℚ d)) =
      (SignType.sign A.det : ℚ) •
        relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) y')
          (standardLocalClass ℚ d) := by
  subst h
  exact relativeHomologyMap_affinePointPairMap A hA c y

/-! ## The class of an affine simplex around a point -/

/-- **Moving the point inside a convex support.** For a convex `U ∋ 0, y` and a class `x` of
`(ℝ^d, ℝ^d ∖ U)` in any degree, the restriction of `x` to `y` is the translate by `y` of its
restriction to `0`. Upstream's `convexSupportTranslationPairHomotopy`. -/
theorem relativeHomologyMap_point_eq_translate {d : ℕ} (n : ℕ) (U : Set (Fin d → ℝ))
    (hU : Convex ℝ U) (h0 : (0 : Fin d → ℝ) ∈ U) (y : Fin d → ℝ) (hy : y ∈ U)
    (x : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) Uᶜ) n) :
    relativeHomologyMap ℚ n
        (supportInclusionPairMap (TopCat.of (Fin d → ℝ)) (Set.singleton_subset_iff.mpr hy)) x =
      relativeHomologyMap ℚ n (translationPointComplementPairMap (Fin d → ℝ) y)
        (relativeHomologyMap ℚ n
          (supportInclusionPairMap (TopCat.of (Fin d → ℝ)) (Set.singleton_subset_iff.mpr h0))
          x) := by
  have h := (convexSupportTranslationPairHomotopy (Fin d → ℝ) U h0 hU y hy
    ).relativeHomologyMap_apply_eq (R := ℚ) n x
  simpa only [relativeHomologyMap_comp, LinearMap.comp_apply] using h

/-- The affine map sending the reference vertices to `v`: `x ↦ M x + c` with
`M = E(v) E(s_d)⁻¹`, `c = v₀ - M s₀`, applied to an affine combination. -/
lemma affine_transport_combination {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ)
    (a : Fin (d + 1) → ℝ) (ha : ∑ i, a i = 1) :
    (edgeMatrix v * (edgeMatrix fun k => standardAffineSimplex d (StdSimplex.single k))⁻¹) *ᵥ
        (∑ i, a i • standardAffineSimplex d (StdSimplex.single i)) +
      (v 0 - (edgeMatrix v * (edgeMatrix fun k => standardAffineSimplex d
        (StdSimplex.single k))⁻¹) *ᵥ standardAffineSimplex d (StdSimplex.single 0)) =
      ∑ i, a i • v i := by
  set S := fun k => standardAffineSimplex d (StdSimplex.single k)
  set M := edgeMatrix v * (edgeMatrix S)⁻¹
  have hSdet : (edgeMatrix S).det ≠ 0 := by
    rw [det_edgeMatrix_standardAffineSimplex]; positivity
  have hcol : ∀ i : Fin d, S i.succ - S 0 = edgeMatrix S *ᵥ Pi.single i 1 := by
    intro i; rw [mulVec_single_one]; rfl
  have hvert : ∀ k, M *ᵥ S k + (v 0 - M *ᵥ S 0) = v k := by
    intro k
    induction k using Fin.cases with
    | zero => abel
    | succ i =>
      have : M *ᵥ (S i.succ - S 0) = v i.succ - v 0 := by
        rw [hcol, mulVec_mulVec, Matrix.mul_assoc,
          nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hSdet), Matrix.mul_one, mulVec_single_one]
        rfl
      rw [mulVec_sub] at this
      rw [← sub_add_cancel (M *ᵥ S i.succ) (M *ᵥ S 0), this]
      abel
  rw [mulVec_sum]
  simp_rw [mulVec_smul]
  have hc : v 0 - M *ᵥ S 0 = ∑ i, a i • (v 0 - M *ᵥ S 0) := by
    rw [← Finset.sum_smul, ha, one_smul]
  rw [hc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_add, hvert]

/-- The sign of an inverse real number is its sign. -/
lemma sign_inv_real (x : ℝ) : SignType.sign x⁻¹ = SignType.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sign_neg h, sign_neg (inv_lt_zero.mpr h)]
  · rw [h, _root_.inv_zero]
  · rw [sign_pos h, sign_pos (inv_pos.mpr h)]

/-- **The class of an affine `d`-simplex around `y`.** Let `v₀, …, v_d` span a nondegenerate
affine simplex of `ℝ^d` and let `y = ∑ wᵢ vᵢ` with every `wᵢ > 0`, `∑ wᵢ = 1`. Then the
relative cycle of `(ℝ^d, ℝ^d ∖ {y})` carried by the affine singular simplex `t ↦ ∑ tᵢ vᵢ` has
class `sign(det E(v)) · (-1)^d · o_y`, where `o_y` is the translate to `y` of
`standardLocalClass ℚ d` and `E(v)` is the edge matrix. The factor `(-1)^d` is the sign of
`det_edgeMatrix_standardAffineSimplex`: the class is `o_y` exactly when `v` has the orientation
of upstream's reference simplex. -/
theorem affineSimplex_homologyπ {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ)
    (hv : (edgeMatrix v).det ≠ 0) (y : Fin d → ℝ) (w : Fin (d + 1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hy : ∑ i, w i • v i = y)
    (z : ((relativeChainFunctor ℚ).obj (pointPair d y)).cycles d)
    (hz : (((relativeChainFunctor ℚ).obj (pointPair d y)).iCycles d).hom z =
      ((relativeChainProjection ℚ (pointPair d y)).f d).hom
        (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
          (affineSingularSimplex v)).hom (1 : ℚ))) :
    (((relativeChainFunctor ℚ).obj (pointPair d y)).homologyπ d).hom z =
      ((SignType.sign (edgeMatrix v).det : ℚ) * (-1) ^ d) •
        relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) y)
          (standardLocalClass ℚ d) := by
  set S := fun k => standardAffineSimplex d (StdSimplex.single k) with hSdef
  have hSdet : (edgeMatrix S).det ≠ 0 := by
    rw [det_edgeMatrix_standardAffineSimplex]; positivity
  set M := edgeMatrix v * (edgeMatrix S)⁻¹ with hMdef
  have hM : M.det ≠ 0 := by
    rw [hMdef, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero hv (inv_ne_zero hSdet)
  set c := v 0 - M *ᵥ S 0 with hcdef
  set p := ∑ i, w i • S i with hpdef
  have hFp : M *ᵥ p + c = y := by rw [← hy]; exact affine_transport_combination v w hw1
  have h0 : (0 : Fin d → ℝ) ∈ openSimplex S := zero_mem_openSimplex_standardAffineSimplex d
  have hp : p ∈ openSimplex S := ⟨w, hw, hw1, rfl⟩
  obtain ⟨zS, hzS⟩ := exists_affineSimplex_openSimplex_cycle S hSdet
  let ι := fun (u : Fin (d + 1) → Fin d → ℝ) =>
    ((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
      (affineSingularSimplex u)).hom (1 : ℚ)
  -- restriction to `0` is upstream's class
  have hres0 : relativeHomologyMap ℚ d (supportInclusionPairMap (TopCat.of (Fin d → ℝ))
      (Set.singleton_subset_iff.mpr h0)) ((((relativeChainFunctor ℚ).obj _).homologyπ d).hom zS) =
      standardLocalClass ℚ d := by
    rw [relativeHomologyMap_homologyπ]
    have hc := iCycles_cyclesMap_supportInclusion (Set.singleton_subset_iff.mpr h0) d zS _ hzS
    have hzz : (HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map
        (supportInclusionPairMap (TopCat.of (Fin d → ℝ)) (Set.singleton_subset_iff.mpr h0))) d).hom
          zS = (standardLocalCycle ℚ d).hom 1 := by
      apply iCycles_injective
      rw [hc]
      have h := congrArg (fun f => f.hom (1 : ℚ)) (standardLocalCycle_inclusion ℚ d)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      rw [h, affineSingularSimplex_standardAffineSimplex]
      rfl
    rw [hzz]
    rfl
  -- restriction to `p` is the translate
  have hresp := relativeHomologyMap_point_eq_translate d (openSimplex S) (convex_openSimplex S) h0
    p hp ((((relativeChainFunctor ℚ).obj _).homologyπ d).hom zS)
  rw [hres0] at hresp
  -- the pushforward along `F`
  set F := affinePairMap M hM c p y hFp
  have hFσ : (TopCat.toSSet.map (TopPair.Hom.fst F)).app _ (affineSingularSimplex S) =
      affineSingularSimplex v := by
    apply ((TopCat.of (Fin d → ℝ)).toSSetObjEquiv _).injective
    ext t : 1
    change M *ᵥ affineSimplexMap S t + c = affineSimplexMap v t
    exact affine_transport_combination v _ (StdSimplex.total_of_fintype t)
  set zp := (HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map
    (supportInclusionPairMap (TopCat.of (Fin d → ℝ)) (Set.singleton_subset_iff.mpr hp))) d).hom zS
  have hzp := iCycles_cyclesMap_supportInclusion (Set.singleton_subset_iff.mpr hp) d zS _ hzS
  have hzF : z = (HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map F) d).hom zp := by
    apply iCycles_injective
    rw [hz, iCycles_cyclesMap_apply F d zp _ hzp]
    erw [chainMap_ι_apply]
    rw [hFσ]
    rfl
  rw [hzF, ← relativeHomologyMap_homologyπ, ← relativeHomologyMap_homologyπ, hresp,
    relativeHomologyMap_affinePairMap]
  congr 1
  have hs := sign_det_edgeMatrix_standardAffineSimplex_mul d
  have hS1 : (SignType.sign (edgeMatrix S).det : ℚ) = (-1) ^ d := by
    have h2 : ((-1 : ℚ) ^ d) * (-1) ^ d = 1 := by rw [← mul_pow]; simp
    calc (SignType.sign (edgeMatrix S).det : ℚ)
        = (SignType.sign (edgeMatrix S).det : ℚ) * ((-1) ^ d * (-1) ^ d) := by rw [h2, mul_one]
      _ = (-1) ^ d := by rw [← mul_assoc, hs, one_mul]
  rw [hMdef, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', sign_mul, sign_inv_real,
    SignType.coe_mul,
    hS1]

/-- **The restriction of the open-simplex class to a point.** A nondegenerate affine simplex is a
relative cycle of `(ℝ^d, ℝ^d ∖ openSimplex v)` (`exists_affineSimplex_openSimplex_cycle`); its
class restricted to any `y` in the open simplex is `sign(det E(v)) · (-1)^d · o_y`. The rung
`cross-orientation` uses it to identify a cross product of two such classes at `0`, which lies
outside the open identity-shuffle simplex. -/
theorem affineSimplex_openSimplex_restrict {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ)
    (hv : (edgeMatrix v).det ≠ 0) (y : Fin d → ℝ) (hy : y ∈ openSimplex v)
    (z : ((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).cycles d)
    (hz : (((relativeChainFunctor ℚ).obj
          (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).iCycles d).hom z =
        ((relativeChainProjection ℚ
            (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).f d).hom
          (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
            (affineSingularSimplex v)).hom (1 : ℚ))) :
    relativeHomologyMap ℚ d
        (supportInclusionPairMap (TopCat.of (Fin d → ℝ)) (Set.singleton_subset_iff.mpr hy))
        ((((relativeChainFunctor ℚ).obj
          (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).homologyπ d).hom z) =
      ((SignType.sign (edgeMatrix v).det : ℚ) * (-1) ^ d) •
        relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) y)
          (standardLocalClass ℚ d) := by
  obtain ⟨w, hw, hw1, hwy⟩ := hy
  rw [relativeHomologyMap_homologyπ]
  exact affineSimplex_homologyπ v hv y w hw hw1 hwy _
    (iCycles_cyclesMap_supportInclusion _ d z _ hz)

/-! ## The reference instance -/

/-- **The sign pin.** `affineSimplex_homologyπ` at the reference simplex and `y = 0`: scalar `1`,
class `standardLocalClass ℚ d` itself. -/
theorem affineSimplex_homologyπ_standard (d : ℕ)
    (z : ((relativeChainFunctor ℚ).obj (pointPair d 0)).cycles d)
    (hz : (((relativeChainFunctor ℚ).obj (pointPair d 0)).iCycles d).hom z =
      ((relativeChainProjection ℚ (pointPair d 0)).f d).hom
        (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
          (affineSingularSimplex fun k => standardAffineSimplex d (StdSimplex.single k))).hom
            (1 : ℚ))) :
    (((relativeChainFunctor ℚ).obj (pointPair d 0)).homologyπ d).hom z =
      ((SignType.sign (edgeMatrix fun k => standardAffineSimplex d (StdSimplex.single k)).det : ℚ)
          * (-1) ^ d) •
        relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) 0)
          (standardLocalClass ℚ d) := by
  rw [sign_det_edgeMatrix_standardAffineSimplex_mul, one_smul,
    translationPointComplementPairMap_zero, relativeHomologyMap, CategoryTheory.Functor.map_id]
  have hinj : Function.Injective
      (((relativeChainFunctor ℚ).obj (pointPair d 0)).iCycles d).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hzz : z = (standardLocalCycle ℚ d).hom 1 := by
    have h := congrArg (fun f => f.hom (1 : ℚ)) (standardLocalCycle_inclusion ℚ d)
    rw [affineSingularSimplex_standardAffineSimplex] at hz
    exact hinj (hz.trans h.symm)
  subst hzz
  rfl

/-- **The reference open-simplex class at `0` is upstream's class**: the reference simplex,
as a relative cycle of `(ℝ^d, ℝ^d ∖ openSimplex s_d)`, restricts at `0` to
`standardLocalClass ℚ d` itself, with no sign. -/
theorem openSimplex_standard_restrict_zero (d : ℕ)
    (z : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ))
        (openSimplex fun k => standardAffineSimplex d (StdSimplex.single k))ᶜ)).cycles d)
    (hz : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ))
          (openSimplex fun k => standardAffineSimplex d (StdSimplex.single k))ᶜ)).iCycles d).hom z =
        ((relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ))
            (openSimplex fun k => standardAffineSimplex d (StdSimplex.single k))ᶜ)).f d).hom
          (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
            (affineSingularSimplex fun k => standardAffineSimplex d (StdSimplex.single k))).hom
              (1 : ℚ))) :
    relativeHomologyMap ℚ d
        (supportInclusionPairMap (TopCat.of (Fin d → ℝ))
          (Set.singleton_subset_iff.mpr (zero_mem_openSimplex_standardAffineSimplex d)))
        ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ))
          (openSimplex fun k => standardAffineSimplex d (StdSimplex.single k))ᶜ)).homologyπ
            d).hom z) =
      standardLocalClass ℚ d := by
  have hdet : (edgeMatrix fun k => standardAffineSimplex d (StdSimplex.single k)).det ≠ 0 := by
    rw [det_edgeMatrix_standardAffineSimplex]; positivity
  rw [affineSimplex_openSimplex_restrict _ hdet 0 (zero_mem_openSimplex_standardAffineSimplex d)
      z hz,
    sign_det_edgeMatrix_standardAffineSimplex_mul, one_smul,
    translationPointComplementPairMap_zero, relativeHomologyMap_id]
  rfl

end HodgeLadder.RealAffine
