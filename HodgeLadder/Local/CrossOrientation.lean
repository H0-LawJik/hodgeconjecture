module

public import HodgeLadder.Relative.CrossChain
public import HodgeLadder.Local.RealAffineOrientation
public import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.ComplexClass

/-!
# The cross product of local orientation classes

Rung `cross-orientation` (front `cup`, decision 0009, sub-rung of `local-class-product`). Write
`s_d` for upstream's reference simplex (`standardAffineSimplex d`, ordered vertices
`e₀, …, e_{d-1}, (-1, …, -1)`) and `standardLocalClass ℚ d` for its class in
`H_d(ℝ^d, ℝ^d ∖ {0}; ℚ)`. The shuffle cross product of `HodgeLadder.Relative.relCrossUnion`, pushed
along `(u, v) ↦ Fin.append u v`, sends `s_m × s_n` to `s_{m+n}` with sign `+`, in every pair of
real dimensions; and the cross product of upstream's complex orientation classes of `ℂ^a` and
`ℂ^b` is the complex orientation class of `ℂ^{a+b}`, with sign `+`.

Signs, each a separate statement here or in a checked rung (register rows "Cross product of
complex orientations", "Shuffle map", "Relative homology cross product", "Real local orientation
and affine maps", "Complex orientation of ℂ^p"):

* the identity shuffle has coefficient `+1` (`shuffleChain_idShuffle_coeff`);
* the identity-shuffle simplex of `s_m × s_n` has vertices `(v_{min(i,m)}, w_{i-m})` and edge
  matrix block upper triangular, so its edge determinant is `det E(s_m) · det E(s_n)`
  (`det_edgeMatrix_shuffleVertices`), of sign `(-1)^m (-1)^n = (-1)^{m+n}`, the sign of `s_{m+n}`;
  the class scalar of `affineSimplex_homologyπ` is then `1`
  (`sign_det_edgeMatrix_shuffleVertices_standard_mul`);
* under `Fin.append` the consecutive (Re, Im) coordinates of `ℂ^a` then `ℂ^b` are those of
  `ℂ^{a+b}` in order (`complexRealHomeomorph_append`), so the complex form needs no permutation;
  with real parts first it would carry `(-1)^{ab}`.

## Main definitions

* `HodgeLadder.CrossOrientation.shuffleVertices`: the vertices of the identity-shuffle simplex of
  two affine simplices.
* `HodgeLadder.CrossOrientation.shuffleBarycenter`: the barycenter of the identity-shuffle simplex
  of `s_m × s_n`, the point where the real form is read before translating back to `0`.
* `HodgeLadder.CrossOrientation.appendMap`, `HodgeLadder.CrossOrientation.complexAppendMap`:
  `(u, v) ↦ Fin.append u v` on `ℝ^m × ℝ^n` and on `ℂ^a × ℂ^b`.
* `HodgeLadder.CrossOrientation.affineShuffleMap`: `Δ[m] ⊗ Δ[n] ⟶ Sing(ℝ^{m+n})` for two affine
  simplices.
* `HodgeLadder.CrossOrientation.openPrism`: the product of the two open reference simplices.
* `HodgeLadder.CrossOrientation.reindexPair`: reindexing `ℝ^d` along `Fin.cast`.
* `HodgeLadder.CrossOrientation.setA`, `setB`, `orient`: the pair `(ℂ^{a+b}, setA ∪ setB)` and
  upstream's complex class on it, as `local-class-cross-model` reads them.

## Main results

* `HodgeLadder.CrossOrientation.complexRealHomeomorph_append`: block compatibility of upstream's
  real coordinates of `ℂ^p` with `Fin.append`.
* `HodgeLadder.CrossOrientation.det_edgeMatrix_shuffleVertices`: the block determinant;
  `sign_det_edgeMatrix_shuffleVertices_standard_mul`: the class scalar at `s_m × s_n` is `1`.
* `HodgeLadder.CrossOrientation.appendMap_idShuffle`: Tau Ceti's identity-shuffle simplex of two
  affine simplices, pushed along `appendMap`, is the affine simplex on `shuffleVertices`.
* `HodgeLadder.CrossOrientation.eq_idShuffle_of_shuffleBarycenter`: no other simplex of
  `Δ[m] ⊗ Δ[n]`, degenerate ones included, reaches the barycenter;
  `relProj_shuffle_eq`: so at the barycenter the shuffle chain is the identity-shuffle simplex.
* `HodgeLadder.CrossOrientation.cross_orientation_real`: `s_m × s_n = s_{m+n}`, sign `+`.
* `HodgeLadder.CrossOrientation.cross_orientation_complex`: the complex form, sign `+`.
* `HodgeLadder.CrossOrientation.cross_orientation_orient`: the complex form on
  `(ℂ^{a+b}, setA ∪ setB)`, equal to `orient a b`.

## Proof of the real form

The cycles of `s_m`, `s_n` relative to the complements of their open simplices have a cross
product on the complement of the open prism `U`, which restricts at `0` to the left side
(`relCrossUnion_naturality`, `openSimplex_standard_restrict_zero`). `U` is convex and contains the
barycenter `y` of the identity-shuffle simplex, so restriction at `y` is the translate of
restriction at `0` (`relativeHomologyMap_point_eq_translate`). At `y` the cycle is the
identity-shuffle simplex alone (`relProj_shuffle_eq`), whose class is `o_y` with scalar `1`
(`affineSimplex_homologyπ`, `sign_det_edgeMatrix_shuffleVertices_standard_mul`); translation is
injective (`relativeHomologyMap_translation_injective`). The complex form moves both factors
along `complexRealHomeomorph` (`relCrossUnion_naturality`, `complexRealHomeomorph_append`) and
reads the degree casts through `HEq`, which carry no scalar.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits Matrix Convexity Finset
open scoped Simplicial
open AlgebraicTopology AlgebraicTopology.Singular

namespace HodgeLadder.CrossOrientation

open HodgeLadder.Relative HodgeLadder.RealAffine

/-! ## Block compatibility of the complex coordinates -/

/-- Upstream's real coordinates of `ℂ^p`: coordinate `finProdFinEquiv (i, j)` (value `2 i + j`)
is the `j`-th coordinate of `z i` in Mathlib's basis `(1, I)`, so `j = 0` is `Re z_i` and
`j = 1` is `Im z_i` (register row "Complex orientation of ℂ^p"). -/
theorem complexRealHomeomorph_finProdFinEquiv (p : ℕ) (z : Fin p → ℂ) (i : Fin p) (j : Fin 2) :
    complexRealHomeomorph p z (finProdFinEquiv (i, j)) = Complex.basisOneI.repr (z i) j := by
  change (Complex.piBasisOneI p).repr z (finProdFinEquiv (i, j)) = _
  rw [Complex.piBasisOneI, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.smulTower'_repr_mk]
  simp

/-- **Block compatibility.** Upstream's real coordinates of `ℂ^{a+b}` at `Fin.append u v` are the
real coordinates of `u` followed by those of `v`, in order, up to the cast
`(a + b) * 2 = a * 2 + b * 2`: no permutation of real coordinates, so no sign
(register row "Cross product of complex orientations"). -/
theorem complexRealHomeomorph_append (a b : ℕ) (u : Fin a → ℂ) (v : Fin b → ℂ) :
    complexRealHomeomorph (a + b) (Fin.append u v) = fun i =>
      Fin.append (complexRealHomeomorph a u) (complexRealHomeomorph b v)
        (Fin.cast (Nat.add_mul a b 2) i) := by
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [complexRealHomeomorph_finProdFinEquiv]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have h : Fin.cast (Nat.add_mul a b 2) (finProdFinEquiv (Fin.castAdd b i, j)) =
        Fin.castAdd (b * 2) (finProdFinEquiv (i, j)) := Fin.ext (by simp)
    rw [h, Fin.append_left, Fin.append_left, complexRealHomeomorph_finProdFinEquiv]
  · have h : Fin.cast (Nat.add_mul a b 2) (finProdFinEquiv (Fin.natAdd a i, j)) =
        Fin.natAdd (a * 2) (finProdFinEquiv (i, j)) := Fin.ext (by simp; ring)
    rw [h, Fin.append_right, Fin.append_right, complexRealHomeomorph_finProdFinEquiv]

/-! ## The identity-shuffle simplex and its edge determinant -/

/-- The vertices of the **identity-shuffle simplex** of two affine simplices with vertices
`v₀, …, v_m` in `ℝ^m` and `w₀, …, w_n` in `ℝ^n`: vertex `k` is `Fin.append v_{min(k, m)} w_{k-m}`
(truncated subtraction), the image of vertex `k` of `HodgeLadder.Relative.idShuffle m n`, whose
lattice path takes all first-factor steps first. -/
def shuffleVertices {m n : ℕ} (v : Fin (m + 1) → Fin m → ℝ) (w : Fin (n + 1) → Fin n → ℝ) :
    Fin (m + n + 1) → Fin (m + n) → ℝ :=
  fun k => Fin.append (v ⟨min k.val m, by omega⟩) (w ⟨k.val - m, by omega⟩)

/-- The edge matrix of the identity-shuffle simplex is block upper triangular: columns `i < m`
are `(v_{i+1} - v₀, 0)`, columns `m + i` are `(v_m - v₀, w_{i+1} - w₀)`. -/
theorem edgeMatrix_shuffleVertices {m n : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (w : Fin (n + 1) → Fin n → ℝ) :
    edgeMatrix (shuffleVertices v w) =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks (edgeMatrix v) (of fun j _ => v (Fin.last m) j - v 0 j) 0
          (edgeMatrix w)) := by
  ext r c
  refine Fin.addCases (fun j => ?_) (fun j => ?_) r <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) c <;>
    simp only [edgeMatrix, shuffleVertices, reindex_apply, submatrix_apply, of_apply,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Fin.append_left, Fin.append_right, Matrix.zero_apply]
  · congr 2; ext; simp
  · congr 2; ext; simp; omega
  · rw [sub_eq_zero]; congr 2; simp
  · congr 2 <;> ext <;> simp; omega

/-- **The block determinant.** The identity-shuffle simplex of two affine simplices has edge
determinant `det E(v) · det E(w)`, with no further sign: the first-factor block comes first both
in the vertex order (identity shuffle) and in the coordinates (`Fin.append`). With the second
factor first in either one, the determinant would carry `(-1)^{mn}`. -/
theorem det_edgeMatrix_shuffleVertices {m n : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (w : Fin (n + 1) → Fin n → ℝ) :
    (edgeMatrix (shuffleVertices v w)).det = (edgeMatrix v).det * (edgeMatrix w).det := by
  rw [edgeMatrix_shuffleVertices, det_reindex_self, det_fromBlocks_zero₂₁]

/-- The identity-shuffle simplex of `s_m × s_n` has edge determinant
`(-1)^m (m + 1) · (-1)^n (n + 1)`. -/
theorem det_edgeMatrix_shuffleVertices_standard (m n : ℕ) :
    (edgeMatrix (shuffleVertices (fun k => standardAffineSimplex m (StdSimplex.single k))
        (fun k => standardAffineSimplex n (StdSimplex.single k)))).det =
      ((-1) ^ m * (m + 1)) * ((-1) ^ n * (n + 1)) := by
  rw [det_edgeMatrix_shuffleVertices, det_edgeMatrix_standardAffineSimplex,
    det_edgeMatrix_standardAffineSimplex]

/-- **The sign of the identity-shuffle simplex.** The scalar `sign(det E) · (-1)^{m+n}` of
`affineSimplex_homologyπ` at the identity-shuffle simplex of `s_m × s_n` is `1`: the simplex has
the orientation of `s_{m+n}`, in every pair of real dimensions. -/
theorem sign_det_edgeMatrix_shuffleVertices_standard_mul (m n : ℕ) :
    (SignType.sign (edgeMatrix (shuffleVertices
        (fun k => standardAffineSimplex m (StdSimplex.single k))
        (fun k => standardAffineSimplex n (StdSimplex.single k)))).det : ℚ) *
      (-1) ^ (m + n) = 1 := by
  rw [det_edgeMatrix_shuffleVertices, sign_mul, SignType.coe_mul, pow_add,
    mul_mul_mul_comm, sign_det_edgeMatrix_standardAffineSimplex_mul,
    sign_det_edgeMatrix_standardAffineSimplex_mul, mul_one]

/-! ## The block maps -/

/-- `(u, v) ↦ Fin.append u v`, from `ℝ^m × ℝ^n` to `ℝ^{m+n}`: first factor first. -/
def appendMap (m n : ℕ) :
    TopCat.of (Fin m → ℝ) ⊗ TopCat.of (Fin n → ℝ) ⟶ TopCat.of (Fin (m + n) → ℝ) :=
  TopCat.ofHom ⟨fun z => Fin.append z.1 z.2, by
    refine continuous_pi fun i => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; fun_prop
    · simp only [Fin.append_right]; fun_prop⟩

/-- `appendMap` sends `(ℝ^m ∖ 0) × ℝ^n ∪ ℝ^m × (ℝ^n ∖ 0)` into `ℝ^{m+n} ∖ 0`. -/
theorem appendMap_mem (m n : ℕ) :
    ∀ z ∈ leftProdSet (P := TopCat.of (Fin m → ℝ)) ({0}ᶜ : Set (Fin m → ℝ))
        (TopCat.of (Fin n → ℝ)) ∪
      rightProdSet (TopCat.of (Fin m → ℝ)) (Q := TopCat.of (Fin n → ℝ)) ({0}ᶜ : Set (Fin n → ℝ)),
      appendMap m n z ∈ ({0}ᶜ : Set (Fin (m + n) → ℝ)) := by
  rintro z (hz | hz) h
  · have h' : Fin.append z.1 z.2 = 0 := h
    exact hz (funext fun i => (Fin.append_left z.1 z.2 i).symm.trans (congrFun h' _))
  · have h' : Fin.append z.1 z.2 = 0 := h
    exact hz (funext fun i => (Fin.append_right z.1 z.2 i).symm.trans (congrFun h' _))

/-- `(u, v) ↦ Fin.append u v`, from `ℂ^a × ℂ^b` to `ℂ^{a+b}`: first factor first. -/
def complexAppendMap (a b : ℕ) :
    TopCat.of (Fin a → ℂ) ⊗ TopCat.of (Fin b → ℂ) ⟶ TopCat.of (Fin (a + b) → ℂ) :=
  TopCat.ofHom ⟨fun z => Fin.append z.1 z.2, by
    refine continuous_pi fun i => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; fun_prop
    · simp only [Fin.append_right]; fun_prop⟩

/-- `complexAppendMap` sends `(ℂ^a ∖ 0) × ℂ^b ∪ ℂ^a × (ℂ^b ∖ 0)` into `ℂ^{a+b} ∖ 0`. -/
theorem complexAppendMap_mem (a b : ℕ) :
    ∀ z ∈ leftProdSet (P := TopCat.of (Fin a → ℂ)) ({0}ᶜ : Set (Fin a → ℂ))
        (TopCat.of (Fin b → ℂ)) ∪
      rightProdSet (TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)),
      complexAppendMap a b z ∈ ({0}ᶜ : Set (Fin (a + b) → ℂ)) := by
  rintro z (hz | hz) h
  · have h' : Fin.append z.1 z.2 = 0 := h
    exact hz (funext fun i => (Fin.append_left z.1 z.2 i).symm.trans (congrFun h' _))
  · have h' : Fin.append z.1 z.2 = 0 := h
    exact hz (funext fun i => (Fin.append_right z.1 z.2 i).symm.trans (congrFun h' _))

/-! ## The identity-shuffle simplex as an affine simplex (route lemma) -/

/-- The affine simplex on `v`, precomposed with the map of standard simplices induced by a vertex
map `g`, is the affine combination of the vertices `v (g i)`. -/
lemma affineSimplexMap_map_apply {d k : ℕ} (v : Fin (d + 1) → Fin d → ℝ)
    (g : Fin (k + 1) → Fin (d + 1)) (t : StdSimplex ℝ (Fin (k + 1))) :
    affineSimplexMap v (t.map g) = ∑ i, t.weights i • v (g i) := by
  classical
  unfold affineSimplexMap
  simp_rw [StdSimplex.weights_map_apply, Finset.sum_smul]
  rw [← Finset.sum_fiberwise Finset.univ g (fun x => t.weights x • v (g x))]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-- **The identity-shuffle simplex of two affine simplices, pushed along `appendMap`, is the
affine simplex on `shuffleVertices`**, with the same vertex order. This is the term of
`shuffleBilin_ι` that `shuffleChain_idShuffle_coeff` gives coefficient `+1`. -/
theorem appendMap_idShuffle {m n : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (w : Fin (n + 1) → Fin n → ℝ) :
    (((SSet.yonedaEquiv.symm (affineSingularSimplex v) ⊗ₘ
          SSet.yonedaEquiv.symm (affineSingularSimplex w)) ≫
        Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of (Fin m → ℝ)) (TopCat.of (Fin n → ℝ)) ≫
          TopCat.toSSet.map (appendMap m n)).app _ (idShuffle m n (m + n) rfl)) =
      affineSingularSimplex (shuffleVertices v w) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext t j
  set p := ((SSet.yonedaEquiv.symm (affineSingularSimplex v) ⊗ₘ
          SSet.yonedaEquiv.symm (affineSingularSimplex w)).app _ (idShuffle m n (m + n) rfl))
  have h1 := congrArg (fun f => TopCat.toSSetObjEquiv _ _ (f.app _ p) t)
    (Functor.Monoidal.μ_fst TopCat.toSSet (TopCat.of (Fin m → ℝ)) (TopCat.of (Fin n → ℝ)))
  have h2 := congrArg (fun f => TopCat.toSSetObjEquiv _ _ (f.app _ p) t)
    (Functor.Monoidal.μ_snd TopCat.toSSet (TopCat.of (Fin m → ℝ)) (TopCat.of (Fin n → ℝ)))
  simp only at h1 h2
  set q := (Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of (Fin m → ℝ))
    (TopCat.of (Fin n → ℝ))).app _ p
  have hq : TopCat.toSSetObjEquiv _ _ q t = (TopCat.toSSetObjEquiv _ _ p.1 t,
      TopCat.toSSetObjEquiv _ _ p.2 t) := Prod.ext h1 h2
  change appendMap m n (TopCat.toSSetObjEquiv _ _ q t) j =
    affineSimplexMap (shuffleVertices v w) t j
  rw [hq]
  -- the two factors are the affine simplices precomposed with the vertex maps of `idShuffle`
  change Fin.append
    (affineSimplexMap v
      (StdSimplex.map (SSet.stdSimplex.objEquiv (idShuffle.{0} m n (m + n) rfl).1) t))
    (affineSimplexMap w
      (StdSimplex.map (SSet.stdSimplex.objEquiv (idShuffle.{0} m n (m + n) rfl).2) t))
    j = _
  rw [affineSimplexMap_map_apply, affineSimplexMap_map_apply]
  unfold affineSimplexMap
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.append_left, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, shuffleVertices, Fin.append_left]
    rfl
  · rw [Fin.append_right, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, shuffleVertices, Fin.append_right]
    rfl

/-- The map `Δ[m] ⊗ Δ[n] ⟶ Sing(ℝ^{m+n})` classified by two affine simplices and `appendMap`, as
`shuffleBilin_ι` writes the shuffle product of two singular simplices. -/
abbrev affineShuffleMap {m n : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (w : Fin (n + 1) → Fin n → ℝ) :
    ((Δ[m] : SSet.{0}) ⊗ Δ[n]) ⟶ TopCat.toSSet.obj (TopCat.of (Fin (m + n) → ℝ)) :=
  (SSet.yonedaEquiv.symm (affineSingularSimplex v) ⊗ₘ
      SSet.yonedaEquiv.symm (affineSingularSimplex w)) ≫
    Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of (Fin m → ℝ)) (TopCat.of (Fin n → ℝ)) ≫
      TopCat.toSSet.map (appendMap m n)

/-- The singular simplex that `affineShuffleMap v w` attaches to a simplex `x` of `Δ[m] ⊗ Δ[n]` is
the affine combination of the vertices `Fin.append (v (x.1 i)) (w (x.2 i))`. -/
lemma toSSetObjEquiv_affineShuffleMap {m n k : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (w : Fin (n + 1) → Fin n → ℝ) (x : ((Δ[m] : SSet.{0}) ⊗ Δ[n]) _⦋k⦌)
    (t : StdSimplex ℝ (Fin (k + 1))) :
    TopCat.toSSetObjEquiv _ _ ((affineShuffleMap v w).app _ x) t =
      ∑ i, t.weights i • Fin.append (v (x.1 i)) (w (x.2 i)) := by
  ext j
  set p := ((SSet.yonedaEquiv.symm (affineSingularSimplex v) ⊗ₘ
          SSet.yonedaEquiv.symm (affineSingularSimplex w)).app _ x)
  have h1 := congrArg (fun f => TopCat.toSSetObjEquiv _ _ (f.app _ p) t)
    (Functor.Monoidal.μ_fst TopCat.toSSet (TopCat.of (Fin m → ℝ)) (TopCat.of (Fin n → ℝ)))
  have h2 := congrArg (fun f => TopCat.toSSetObjEquiv _ _ (f.app _ p) t)
    (Functor.Monoidal.μ_snd TopCat.toSSet (TopCat.of (Fin m → ℝ)) (TopCat.of (Fin n → ℝ)))
  simp only at h1 h2
  set q := (Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of (Fin m → ℝ))
    (TopCat.of (Fin n → ℝ))).app _ p
  have hq : TopCat.toSSetObjEquiv _ _ q t = (TopCat.toSSetObjEquiv _ _ p.1 t,
      TopCat.toSSetObjEquiv _ _ p.2 t) := Prod.ext h1 h2
  change appendMap m n (TopCat.toSSetObjEquiv _ _ q t) j = _
  rw [hq]
  change Fin.append
    (affineSimplexMap v (StdSimplex.map (SSet.stdSimplex.objEquiv x.1) t))
    (affineSimplexMap w (StdSimplex.map (SSet.stdSimplex.objEquiv x.2) t)) j = _
  rw [affineSimplexMap_map_apply, affineSimplexMap_map_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.append_left]; simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, Fin.append_left]
    rfl
  · rw [Fin.append_right]; simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, Fin.append_right]
    rfl

/-- A combination of vertices along a vertex map `f`, regrouped by vertex. -/
lemma sum_smul_comp_eq {d N : ℕ} (v : Fin (d + 1) → Fin d → ℝ) (f : Fin N → Fin (d + 1))
    (t : Fin N → ℝ) :
    ∑ k, t k • v (f k) = ∑ j, (∑ k with f k = j, t k) • v j := by
  rw [← Finset.sum_fiberwise Finset.univ f (fun k => t k • v (f k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [(Finset.mem_filter.1 hk).2]

/-- Two barycentric expressions along vertex maps `f`, `g` of one point of a nondegenerate
simplex give the same mass to every prefix `{j < i}` of the vertices. -/
lemma prefix_mass_eq {d N : ℕ} (v : Fin (d + 1) → Fin d → ℝ) (hv : (edgeMatrix v).det ≠ 0)
    (f g : Fin N → Fin (d + 1)) (t u : Fin N → ℝ) (ht1 : ∑ k, t k = 1) (hu1 : ∑ k, u k = 1)
    (h : ∑ k, t k • v (f k) = ∑ k, u k • v (g k)) (i : ℕ) :
    ∑ k with (f k).val < i, t k = ∑ k with (g k).val < i, u k := by
  rw [sum_smul_comp_eq v f t, sum_smul_comp_eq v g u] at h
  have hw := weights_eq_of_det_ne_zero v hv _ _
    (by rw [Finset.sum_fiberwise univ f t]; exact ht1)
    (by rw [Finset.sum_fiberwise univ g u]; exact hu1) h
  have key : ∀ (f : Fin N → Fin (d + 1)) (t : Fin N → ℝ),
      ∑ k with (f k).val < i, t k = ∑ j with j.val < i, ∑ k with f k = j, t k := by
    intro f t
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter fun k => (f k).val < i)
      (t := univ.filter fun j : Fin (d + 1) => j.val < i) (g := f)
      (fun k hk => by simpa using hk)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.filter_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ (Finset.mem_filter.1 hj).2, h⟩
  rw [key f t, key g u]
  exact Finset.sum_congr rfl fun j _ => congrFun hw j

/-- In `Fin N`, a downward-closed predicate is `k < card`. -/
lemma lowerSet_iff_lt_card {N : ℕ} (p : Fin N → Prop) [DecidablePred p]
    (hp : ∀ k k', k' ≤ k → p k → p k') (k : Fin N) :
    p k ↔ k.val < #{k | p k} := by
  constructor
  · intro hk
    have : Finset.Iic k ⊆ univ.filter (fun k => p k) := fun k' hk' =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hp k k' (Finset.mem_Iic.1 hk') hk⟩
    have := Finset.card_le_card this
    rw [Fin.card_Iic] at this
    omega
  · intro hk
    by_contra hn
    have : univ.filter (fun k => p k) ⊆ Finset.Iio k := fun k' hk' => by
      rw [Finset.mem_Iio]
      by_contra hle
      exact hn (hp k' k (not_lt.1 hle) (Finset.mem_filter.1 hk').2)
    have := Finset.card_le_card this
    rw [Fin.card_Iio] at this
    omega

/-- A nondecreasing prefix sum hitting `i / N` at `L i` for all `i ≤ N` forces `L i = i`. -/
lemma eq_of_prefix_values {N : ℕ} (S : ℕ → ℝ) (hS : Monotone S) (L : ℕ → ℕ)
    (hL : ∀ i, i ≤ N → L i ≤ N) (hv : ∀ i, i ≤ N → S (L i) = i / N) (hN : 0 < N) :
    ∀ i, i ≤ N → L i = i := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : ∀ i, i < N → L i < L (i + 1) := by
    intro i hi
    by_contra hle
    have := hS (not_lt.1 hle)
    rw [hv _ hi.le, hv _ hi] at this
    rw [div_le_div_iff_of_pos_right hNr] at this
    push_cast at this
    linarith
  have hge : ∀ i, i ≤ N → i ≤ L i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih => intro hi; have := hlt i (by omega); have := ih (by omega); omega
  have hle : ∀ j, j ≤ N → L (N - j) ≤ N - j := by
    intro j
    induction j with
    | zero => intro _; simpa using hL N le_rfl
    | succ j ih =>
      intro hj
      have h1 := hlt (N - (j + 1)) (by omega)
      have h2 := ih (by omega)
      have : N - (j + 1) + 1 = N - j := by omega
      rw [this] at h1
      omega
  intro i hi
  have := hle (N - i) (by omega)
  rw [Nat.sub_sub_self hi] at this
  exact le_antisymm this (hge i hi)


/-- The barycenter of the identity-shuffle simplex of `s_m × s_n`: every vertex of
`shuffleVertices` with weight `1 / (m + n + 1)`. -/
def shuffleBarycenter (m n : ℕ) : Fin (m + n) → ℝ :=
  ∑ k, (1 / (m + n + 1 : ℝ)) • shuffleVertices
    (fun k => standardAffineSimplex m (StdSimplex.single k))
    (fun k => standardAffineSimplex n (StdSimplex.single k)) k

/-- **Only the identity shuffle reaches the barycenter** (route lemma). If an `(m + n)`-simplex
`x` of `Δ[m] ⊗ Δ[n]`, degenerate or not, realized affinely through `s_m`, `s_n` and `Fin.append`,
passes through `shuffleBarycenter m n`, then `x` is the identity shuffle. So in
`C(ℝ^{m+n}, ℝ^{m+n} ∖ {y})`, `y` the barycenter, every term of the shuffle chain other than the
identity shuffle vanishes. Proof: the barycentric weights of the two components are
unique (`weights_eq_of_det_ne_zero`), so the partial sums of `t` take the `m + n + 1` values
`1/N, …, N/N` (`N = m + n + 1`) at strictly increasing indices, which forces the vertex maps of
`x` to be `k ↦ min k m` and `k ↦ k - m`. -/
theorem eq_idShuffle_of_shuffleBarycenter {m n : ℕ} (x : ((Δ[m] : SSet.{0}) ⊗ Δ[n]) _⦋m + n⦌)
    (t : Fin (m + n + 1) → ℝ) (ht : ∀ k, 0 ≤ t k) (ht1 : ∑ k, t k = 1)
    (h : ∑ k, t k • Fin.append (standardAffineSimplex m (StdSimplex.single (x.1 k)))
        (standardAffineSimplex n (StdSimplex.single (x.2 k))) = shuffleBarycenter m n) :
    x = idShuffle m n (m + n) rfl := by
  set u : Fin (m + n + 1) → ℝ := fun _ => 1 / (m + n + 1 : ℝ) with hu
  have hNr : (0 : ℝ) < (m : ℝ) + n + 1 := by positivity
  have hu1 : ∑ k, u k = 1 := by
    simp only [hu, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hdm : (edgeMatrix fun k => standardAffineSimplex m (StdSimplex.single k)).det ≠ 0 := by
    rw [det_edgeMatrix_standardAffineSimplex]; positivity
  have hdn : (edgeMatrix fun k => standardAffineSimplex n (StdSimplex.single k)).det ≠ 0 := by
    rw [det_edgeMatrix_standardAffineSimplex]; positivity
  have hA : ∑ k, t k • (fun k => standardAffineSimplex m (StdSimplex.single k)) (x.1 k) =
      ∑ k, u k • (fun k => standardAffineSimplex m (StdSimplex.single k))
        (⟨min k.val m, by omega⟩ : Fin (m + 1)) := by
    funext i
    have := congrFun h (Fin.castAdd n i)
    simp only [Finset.sum_apply, Pi.smul_apply, Fin.append_left, shuffleBarycenter,
      shuffleVertices] at this
    simpa only [Finset.sum_apply, Pi.smul_apply] using this
  have hB : ∑ k, t k • (fun k => standardAffineSimplex n (StdSimplex.single k)) (x.2 k) =
      ∑ k, u k • (fun k => standardAffineSimplex n (StdSimplex.single k))
        (⟨k.val - m, by omega⟩ : Fin (n + 1)) := by
    funext i
    have := congrFun h (Fin.natAdd m i)
    simp only [Finset.sum_apply, Pi.smul_apply, Fin.append_right, shuffleBarycenter,
      shuffleVertices] at this
    simpa only [Finset.sum_apply, Pi.smul_apply] using this
  have hcount : ∀ i, i ≤ m + n + 1 → ∑ k with k.val < i, u k = i / (m + n + 1 : ℝ) := by
    intro i hi
    rw [Finset.sum_const, Fin.card_filter_val_lt, min_eq_right hi, nsmul_eq_mul]
    field_simp
  let Q : ℕ → Fin (m + n + 1) → Prop := fun i k =>
    if i ≤ m then (x.1 k).val < i else (x.2 k).val < i - m
  have hQ : ∀ i, i ≤ m + n + 1 → ∑ k with Q i k, t k = i / (m + n + 1 : ℝ) := by
    intro i hi
    rw [← hcount i hi]
    by_cases him : i ≤ m
    · have e1 : (univ.filter fun k => Q i k) = univ.filter fun k => (x.1 k).val < i := by
        ext k; simp [Q, him]
      have e2 : (univ.filter fun k : Fin (m + n + 1) => k.val < i) =
          univ.filter fun k : Fin (m + n + 1) =>
            (⟨min k.val m, by omega⟩ : Fin (m + 1)).val < i := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [e1, e2]
      exact prefix_mass_eq _ hdm _ _ t u ht1 hu1 hA i
    · have e1 : (univ.filter fun k => Q i k) = univ.filter fun k => (x.2 k).val < i - m := by
        ext k; simp [Q, him]
      have e2 : (univ.filter fun k : Fin (m + n + 1) => k.val < i) =
          univ.filter fun k : Fin (m + n + 1) =>
            (⟨k.val - m, by omega⟩ : Fin (n + 1)).val < i - m := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [e1, e2]
      exact prefix_mass_eq _ hdn _ _ t u ht1 hu1 hB (i - m)
  have hlow : ∀ i k k', k' ≤ k → Q i k → Q i k' := by
    intro i k k' hle hk
    have h1 := SSet.stdSimplex.monotone_apply x.1 hle
    have h2 := SSet.stdSimplex.monotone_apply x.2 hle
    simp only [Q] at hk ⊢
    split_ifs at hk ⊢
    · exact lt_of_le_of_lt (Fin.le_iff_val_le_val.1 h1) hk
    · exact lt_of_le_of_lt (Fin.le_iff_val_le_val.1 h2) hk
  let L : ℕ → ℕ := fun i => #{k | Q i k}
  let S : ℕ → ℝ := fun l => ∑ k with k.val < l, t k
  have hS : Monotone S := by
    intro l l' hl
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => ht k
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    omega
  have hSL : ∀ i, S (L i) = ∑ k with Q i k, t k := by
    intro i
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (lowerSet_iff_lt_card (Q i) (hlow i) k).symm
  have hLle : ∀ i, i ≤ m + n + 1 → L i ≤ m + n + 1 := fun i _ =>
    (Finset.card_le_univ _).trans (by simp)
  have hLv : ∀ i, i ≤ m + n + 1 → S (L i) = i / ((m + n + 1 : ℕ) : ℝ) := by
    intro i hi; rw [hSL, hQ i hi]; push_cast; rfl
  have hL := eq_of_prefix_values S hS L hLle hLv (by omega)
  have hQiff : ∀ i, i ≤ m + n + 1 → ∀ k, Q i k ↔ k.val < i := by
    intro i hi k
    rw [lowerSet_iff_lt_card (Q i) (hlow i) k]
    exact iff_of_eq (congrArg (k.val < ·) (hL i hi))
  refine (eq_idShuffle_iff rfl x).2 fun k => ⟨?_, ?_⟩
  · have hm := (x.1 k).isLt
    by_cases hk : k.val < m
    · have h1 := (hQiff (k.val + 1) (by omega) k).2 (by omega)
      have h2 := (hQiff k.val (by omega) k)
      simp only [Q, show k.val + 1 ≤ m by omega, show k.val ≤ m by omega, ite_true] at h1 h2
      have : ¬ (x.1 k).val < k.val := fun h => (lt_irrefl _ (h2.1 h))
      omega
    · have h2 := hQiff m (by omega) k
      simp only [Q, le_refl, ite_true] at h2
      have : ¬ (x.1 k).val < m := fun h => hk (h2.1 h)
      omega
  · have hn := (x.2 k).isLt
    by_cases hk : k.val ≤ m
    · have h1 := (hQiff (m + 1) (by omega) k).2 (by omega)
      simp only [Q, show ¬ (m + 1 ≤ m) by omega, ite_false] at h1
      omega
    · have h1 := (hQiff (k.val + 1) (by omega) k).2 (by omega)
      have h2 := hQiff k.val (by omega) k
      simp only [Q, show ¬ (k.val + 1 ≤ m) by omega, show ¬ (k.val ≤ m) by omega,
        ite_false] at h1 h2
      have : ¬ (x.2 k).val < k.val - m := fun h => lt_irrefl _ (h2.1 h)
      omega

/-- **Only the identity shuffle survives at the barycenter.** In `C(ℝ^{m+n}, ℝ^{m+n} ∖ {y})`, `y`
the barycenter, Tau Ceti's shuffle chain of `s_m × s_n`, pushed along `appendMap`, is the
identity-shuffle simplex with coefficient `1` (`shuffleChain_idShuffle_coeff`); every other
simplex misses `y` (`eq_idShuffle_of_shuffleBarycenter`). -/
lemma relProj_shuffle_eq (m n : ℕ) :
    ((relativeChainProjection ℚ (pointPair (m + n) (shuffleBarycenter m n))).f (m + n)).hom
      ((SSet.shuffleChain (ModuleCat.of ℚ ℚ) m n (m + n) rfl ≫
        (SSet.chainComplexMap
          (affineShuffleMap (fun k => standardAffineSimplex m (StdSimplex.single k))
            (fun k => standardAffineSimplex n (StdSimplex.single k))) (ModuleCat.of ℚ ℚ)).f
              (m + n)).hom 1) =
    ((relativeChainProjection ℚ (pointPair (m + n) (shuffleBarycenter m n))).f (m + n)).hom
      (((TopCat.toSSet.obj (TopCat.of (Fin (m + n) → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
        (affineSingularSimplex (shuffleVertices
          (fun k => standardAffineSimplex m (StdSimplex.single k))
          (fun k => standardAffineSimplex n (StdSimplex.single k))))).hom 1) := by
  set F := affineShuffleMap (fun k => standardAffineSimplex m (StdSimplex.single k))
          (fun k => standardAffineSimplex n (StdSimplex.single k))
  have key : (SSet.chainComplexMap F (ModuleCat.of ℚ ℚ)).f (m + n) ≫
      (relativeChainProjection ℚ (pointPair (m + n) (shuffleBarycenter m n))).f (m + n) =
      simplexCoeff ((Δ[m] : SSet.{0}) ⊗ Δ[n]) (ModuleCat.of ℚ ℚ) (idShuffle m n (m + n) rfl) ≫
        (TopCat.toSSet.obj (TopCat.of (Fin (m + n) → ℝ))).ιChainComplex
          (R := ModuleCat.of ℚ ℚ) (affineSingularSimplex (shuffleVertices
            (fun k => standardAffineSimplex m (StdSimplex.single k))
            (fun k => standardAffineSimplex n (StdSimplex.single k)))) ≫
        (relativeChainProjection ℚ (pointPair (m + n) (shuffleBarycenter m n))).f (m + n) := by
    refine Cofan.IsColimit.hom_ext
      (((Δ[m] : SSet.{0}) ⊗ Δ[n]).isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) (m + n))
      _ _ fun x => ?_
    change ((Δ[m] : SSet.{0}) ⊗ Δ[n]).ιChainComplex x ≫ _ =
      ((Δ[m] : SSet.{0}) ⊗ Δ[n]).ιChainComplex x ≫ _
    erw [SSet.ι_chainComplexMap_f_assoc]
    by_cases hx : x = idShuffle m n (m + n) rfl
    · subst hx
      erw [ι_simplexCoeff_self_assoc]
      exact congrArg (fun s => (TopCat.toSSet.obj (TopCat.of (Fin (m + n) → ℝ))).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) s ≫
          (relativeChainProjection ℚ (pointPair (m + n) (shuffleBarycenter m n))).f (m + n))
        (appendMap_idShuffle _ _)
    · rw [← Category.assoc, ι_simplexCoeff_of_ne _ _ hx, zero_comp]
      ext1
      refine LinearMap.ext_ring ?_
      refine (relProj_ι_eq_zero _ _ fun t => ?_).trans rfl
      rw [toSSetObjEquiv_affineShuffleMap]
      intro h
      exact hx (eq_idShuffle_of_shuffleBarycenter x t.weights (fun k => t.nonneg k)
        (StdSimplex.total_of_fintype _) h)
  have h := congrArg (fun f => f.hom (1 : ℚ))
    (congrArg (SSet.shuffleChain (ModuleCat.of ℚ ℚ) m n (m + n) rfl ≫ ·) key)
  simp only [← Category.assoc, shuffleChain_idShuffle_coeff, Category.id_comp] at h
  exact h

/-- The open prism: first block in the open simplex of `s_m`, second in that of `s_n`. -/
def openPrism (m n : ℕ) : Set (Fin (m + n) → ℝ) :=
  {z | (fun i => z (Fin.castAdd n i)) ∈
      openSimplex (fun k => standardAffineSimplex m (StdSimplex.single k)) ∧
    (fun j => z (Fin.natAdd m j)) ∈
      openSimplex (fun k => standardAffineSimplex n (StdSimplex.single k))}

/-- The open prism is convex. -/
lemma convex_openPrism (m n : ℕ) : Convex ℝ (openPrism m n) :=
  ((convex_openSimplex _).linear_preimage (LinearMap.funLeft ℝ ℝ (Fin.castAdd n))).inter
    ((convex_openSimplex _).linear_preimage (LinearMap.funLeft ℝ ℝ (Fin.natAdd m)))

/-- The open prism contains `0`. -/
lemma zero_mem_openPrism (m n : ℕ) : (0 : Fin (m + n) → ℝ) ∈ openPrism m n :=
  ⟨zero_mem_openSimplex_standardAffineSimplex m, zero_mem_openSimplex_standardAffineSimplex n⟩

/-- Equal positive weights on a surjective vertex map give a point of the open simplex. -/
lemma mem_openSimplex_of_comp {d N : ℕ} (v : Fin (d + 1) → Fin d → ℝ) (f : Fin N → Fin (d + 1))
    (hf : Function.Surjective f) (u : ℝ) (hu : 0 < u) (hN : (N : ℝ) * u = 1) :
    ∑ k, u • v (f k) ∈ openSimplex v := by
  refine ⟨fun j => ∑ k with f k = j, u, fun j => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hf j
    exact Finset.sum_pos (fun _ _ => hu) ⟨k, by simp [hk]⟩
  · rw [Finset.sum_fiberwise univ f (fun _ => u)]
    simpa using hN
  · exact (sum_smul_comp_eq v f (fun _ => u)).symm

/-- The barycenter of the identity-shuffle simplex lies in the open prism. -/
lemma shuffleBarycenter_mem_openPrism (m n : ℕ) : shuffleBarycenter m n ∈ openPrism m n := by
  have hu : (0 : ℝ) < 1 / (m + n + 1 : ℝ) := by positivity
  have hN : ((m + n + 1 : ℕ) : ℝ) * (1 / (m + n + 1 : ℝ)) = 1 := by push_cast; field_simp
  constructor
  · have := mem_openSimplex_of_comp (fun k => standardAffineSimplex m (StdSimplex.single k))
      (fun k : Fin (m + n + 1) => (⟨min k.val m, by omega⟩ : Fin (m + 1)))
      (fun j => ⟨⟨j.val, by omega⟩, Fin.ext (by simp; omega)⟩) _ hu hN
    convert this using 1
    funext i
    simp only [shuffleBarycenter, shuffleVertices, Finset.sum_apply, Pi.smul_apply,
      Fin.append_left]
  · have := mem_openSimplex_of_comp (fun k => standardAffineSimplex n (StdSimplex.single k))
      (fun k : Fin (m + n + 1) => (⟨k.val - m, by omega⟩ : Fin (n + 1)))
      (fun j => ⟨⟨j.val + m, by omega⟩, Fin.ext (by simp)⟩) _ hu hN
    convert this using 1
    funext i
    simp only [shuffleBarycenter, shuffleVertices, Finset.sum_apply, Pi.smul_apply,
      Fin.append_right]

/-- `appendMap` sends the complement of the open simplex product into the complement of the open
prism. -/
lemma appendMap_mem_openPrism_compl (m n : ℕ) :
    ∀ z ∈ leftProdSet (P := TopCat.of (Fin m → ℝ))
        (openSimplex fun k => standardAffineSimplex m (StdSimplex.single k))ᶜ
        (TopCat.of (Fin n → ℝ)) ∪
      rightProdSet (TopCat.of (Fin m → ℝ)) (Q := TopCat.of (Fin n → ℝ))
        (openSimplex fun k => standardAffineSimplex n (StdSimplex.single k))ᶜ,
      appendMap m n z ∈ (openPrism m n)ᶜ := by
  rintro z (hz | hz) ⟨h1, h2⟩
  · exact hz (by convert h1 using 1; funext i; exact (Fin.append_left z.1 z.2 i).symm)
  · exact hz (by convert h2 using 1; funext i; exact (Fin.append_right z.1 z.2 i).symm)
/-- `relCrossUnion_naturality` along two support inclusions. -/
lemma relCrossUnion_supportInclusion {P Q : TopCat.{0}} {Z W : Set P} {Z' W' : Set Q}
    (h : Z ⊆ W) (h' : Z' ⊆ W') (hf : ∀ a ∈ Wᶜ, (𝟙 P : P ⟶ P) a ∈ Zᶜ)
    (hg : ∀ b ∈ W'ᶜ, (𝟙 Q : Q ⟶ Q) b ∈ Z'ᶜ) {m n : ℕ}
    (x : RelativeHomology ℚ (TopPair.ofSubset Wᶜ) m)
    (y : RelativeHomology ℚ (TopPair.ofSubset W'ᶜ) n) :
    relCrossUnion Zᶜ Z'ᶜ m n (relativeHomologyMap ℚ m (supportInclusionPairMap P h) x)
        (relativeHomologyMap ℚ n (supportInclusionPairMap Q h') y) =
      relativeHomologyMap ℚ (m + n)
        (TopPair.ofSubsetHom (𝟙 P ⊗ₘ 𝟙 Q) (tensorHom_mem_union (𝟙 P) (𝟙 Q) hf hg))
        (relCrossUnion Wᶜ W'ᶜ m n x y) :=
  relCrossUnion_naturality (𝟙 P) (𝟙 Q) hf hg x y

/-! ## The cross product of orientation classes -/

/-- **Real form: `s_m × s_n = s_{m+n}`, sign `+`.** The shuffle cross product of upstream's
local classes of `ℝ^m` and `ℝ^n`, pushed along `appendMap`, is upstream's local class of
`ℝ^{m+n}`, exactly, for every `m, n` (register row "Cross product of complex orientations").
At `m = n = 1` the right side is nonzero (`standardLocalClass_ne_zero_of_pos`), so the identity
separates `+` from `-` and from `0`. -/
theorem cross_orientation_real (m n : ℕ) :
    relativeHomologyMap ℚ (m + n) (TopPair.ofSubsetHom (appendMap m n) (appendMap_mem m n))
      (relCrossUnion (P := TopCat.of (Fin m → ℝ)) (Q := TopCat.of (Fin n → ℝ))
        ({0}ᶜ : Set (Fin m → ℝ)) ({0}ᶜ : Set (Fin n → ℝ)) m n
        (standardLocalClass ℚ m) (standardLocalClass ℚ n)) =
      standardLocalClass ℚ (m + n) := by
  set Sm := fun k => standardAffineSimplex m (StdSimplex.single k) with hSm
  set Sn := fun k => standardAffineSimplex n (StdSimplex.single k) with hSn
  have hdm : (edgeMatrix Sm).det ≠ 0 := by
    rw [det_edgeMatrix_standardAffineSimplex]; positivity
  have hdn : (edgeMatrix Sn).det ≠ 0 := by
    rw [det_edgeMatrix_standardAffineSimplex]; positivity
  obtain ⟨zx, hzx⟩ := exists_affineSimplex_openSimplex_cycle Sm hdm
  obtain ⟨zy, hzy⟩ := exists_affineSimplex_openSimplex_cycle Sn hdn
  rw [← openSimplex_standard_restrict_zero m zx hzx, ← openSimplex_standard_restrict_zero n zy hzy]
  have hf : ∀ a ∈ (openSimplex Sm)ᶜ, (𝟙 (TopCat.of (Fin m → ℝ)) : _ ⟶ _) a ∈
      ({0} : Set (Fin m → ℝ))ᶜ := fun a ha hb =>
    ha (Set.singleton_subset_iff.mpr (zero_mem_openSimplex_standardAffineSimplex m) hb)
  have hg : ∀ a ∈ (openSimplex Sn)ᶜ, (𝟙 (TopCat.of (Fin n → ℝ)) : _ ⟶ _) a ∈
      ({0} : Set (Fin n → ℝ))ᶜ := fun a ha hb =>
    ha (Set.singleton_subset_iff.mpr (zero_mem_openSimplex_standardAffineSimplex n) hb)
  refine (congrArg _ (relCrossUnion_supportInclusion (P := TopCat.of (Fin m → ℝ))
    (Q := TopCat.of (Fin n → ℝ)) _ _ hf hg _ _)).trans ?_
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  set y := shuffleBarycenter m n
  have hyU := shuffleBarycenter_mem_openPrism m n
  have hpair : TopPair.ofSubsetHom (𝟙 _ ⊗ₘ 𝟙 _) (tensorHom_mem_union _ _ hf hg) ≫
      TopPair.ofSubsetHom (appendMap m n) (appendMap_mem m n) =
      TopPair.ofSubsetHom (appendMap m n) (appendMap_mem_openPrism_compl m n) ≫
        supportInclusionPairMap (TopCat.of (Fin (m + n) → ℝ))
          (Set.singleton_subset_iff.mpr (zero_mem_openPrism m n)) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext <;> rfl
  rw [hpair, relativeHomologyMap_comp, LinearMap.comp_apply]
  apply relativeHomologyMap_translation_injective (m + n) y
  rw [← relativeHomologyMap_point_eq_translate (m + n) (openPrism m n) (convex_openPrism m n)
    (zero_mem_openPrism m n) y hyU]
  obtain ⟨z, hz⟩ := exists_unionCycle_shuffle _ _ _ _ zx hzx zy hzy
  rw [relCrossUnion_homologyπ _ _ _ _ zx zy z hzx hzy hz]
  refine (congrArg _ (relativeHomologyMap_homologyπ _ _ z)).trans
    ((relativeHomologyMap_homologyπ _ _ _).trans ?_)
  have h1 := iCycles_cyclesMap_apply
    (TopPair.ofSubsetHom (appendMap m n) (appendMap_mem_openPrism_compl m n)) (m + n) z _ hz
  have h2 := iCycles_cyclesMap_supportInclusion (Set.singleton_subset_iff.mpr hyU) (m + n) _ _ h1
  rw [shuffleBilin_ι] at h2
  have hchain : ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
      (TopPair.Hom.fst (TopPair.ofSubsetHom (appendMap m n)
        (appendMap_mem_openPrism_compl m n)))).f (m + n)).hom
      ((SSet.shuffleChain (ModuleCat.of ℚ ℚ) m n (m + n) rfl ≫
        (SSet.chainComplexMap
          ((SSet.yonedaEquiv.symm (affineSingularSimplex Sm) ⊗ₘ
            SSet.yonedaEquiv.symm (affineSingularSimplex Sn)) ≫
            Functor.LaxMonoidal.μ TopCat.toSSet _ _) (ModuleCat.of ℚ ℚ)).f (m + n)).hom 1) =
      (SSet.shuffleChain (ModuleCat.of ℚ ℚ) m n (m + n) rfl ≫
        (SSet.chainComplexMap (affineShuffleMap Sm Sn) (ModuleCat.of ℚ ℚ)).f (m + n)).hom 1 := by
    change ((SSet.shuffleChain (ModuleCat.of ℚ ℚ) m n (m + n) rfl ≫
        (SSet.chainComplexMap
          ((SSet.yonedaEquiv.symm (affineSingularSimplex Sm) ⊗ₘ
            SSet.yonedaEquiv.symm (affineSingularSimplex Sn)) ≫
            Functor.LaxMonoidal.μ TopCat.toSSet _ _) (ModuleCat.of ℚ ℚ)).f (m + n)) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (appendMap m n)) (ModuleCat.of ℚ ℚ)).f
          (m + n)).hom 1 = _
    rw [Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp, Category.assoc]
  rw [hchain, relProj_shuffle_eq] at h2
  have hdet : (edgeMatrix (shuffleVertices Sm Sn)).det ≠ 0 := by
    rw [det_edgeMatrix_shuffleVertices]; exact mul_ne_zero hdm hdn
  have hw : ∀ i : Fin (m + n + 1), 0 < (fun _ => 1 / (m + n + 1 : ℝ)) i := fun _ => by positivity
  have hw1 : ∑ i : Fin (m + n + 1), (fun _ => 1 / (m + n + 1 : ℝ)) i = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  refine (affineSimplex_homologyπ (shuffleVertices Sm Sn) hdet y _ hw hw1 rfl _ h2).trans ?_
  rw [sign_det_edgeMatrix_shuffleVertices_standard_mul, one_smul]

/-- Transport of a class along an equation of degrees changes nothing up to `HEq`. -/
lemma rel_cast_heq {P : TopPair} {n n' : ℕ} (h : n = n') (z : RelativeHomology ℚ P n) :
    HEq (h ▸ z : RelativeHomology ℚ P n') z := by
  subst h; rfl

/-- Upstream's complex class is, up to the degree cast, the real class moved by
`standardComplexRealPairIso`. -/
lemma standardComplexLocalClass_heq (k : ℕ) :
    HEq (standardComplexLocalClass ℚ k)
      (relativeHomologyMap ℚ (k * 2) (standardComplexRealPairIso k).inv
        (standardLocalClass ℚ (k * 2))) :=
  rel_cast_heq _ _

/-- The right side of `cross_orientation_complex`, up to `HEq`. -/
lemma rhs_heq (a b : ℕ) :
    HEq ((Nat.mul_add 2 a b) ▸ standardComplexLocalClass ℚ (a + b) :
      RelativeHomology ℚ (puncturedPair ℂ (a + b)) (2 * a + 2 * b))
      (relativeHomologyMap ℚ ((a + b) * 2) (standardComplexRealPairIso (a + b)).inv
        (standardLocalClass ℚ ((a + b) * 2))) :=
  (rel_cast_heq _ _).trans (standardComplexLocalClass_heq _)

/-- `relativeHomologyMap` respects `HEq` across an equation of degrees. -/
lemma relHom_heq {P Q : TopPair} (f : P ⟶ Q) {n n' : ℕ} (h : n = n')
    {z : RelativeHomology ℚ P n} {z' : RelativeHomology ℚ P n'} (hz : HEq z z') :
    HEq (relativeHomologyMap ℚ n f z) (relativeHomologyMap ℚ n' f z') := by
  subst h; cases hz; rfl

/-- `relCrossUnion` respects `HEq` across equations of degrees. -/
lemma relCrossUnion_heq {P Q : TopCat.{0}} (A : Set P) (B : Set Q) {p p' q q' : ℕ}
    (hp : p = p') (hq : q = q')
    {x : RelativeHomology ℚ (TopPair.ofSubset A) p}
    {x' : RelativeHomology ℚ (TopPair.ofSubset A) p'}
    {y : RelativeHomology ℚ (TopPair.ofSubset B) q}
    {y' : RelativeHomology ℚ (TopPair.ofSubset B) q'}
    (hx : HEq x x') (hy : HEq y y') :
    HEq (relCrossUnion A B p q x y) (relCrossUnion A B p' q' x' y') := by
  subst hp hq; cases hx; cases hy; rfl

/-- Reindexing the coordinates of `ℝ^d` along `Fin.cast`, a map of punctured pairs. -/
def reindexPair {d d' : ℕ} (h : d' = d) : puncturedPair ℝ d ⟶ puncturedPair ℝ d' :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun x i => x (Fin.cast h i), by fun_prop⟩)
    fun x hx h0 => hx (funext fun j => by
      simpa using congrFun h0 (Fin.cast h.symm j))

/-- Reindexing along `Fin.cast` sends `standardLocalClass ℚ d` to `standardLocalClass ℚ d'`,
up to the degree cast. -/
lemma reindexPair_heq {d d' : ℕ} (h : d' = d) :
    HEq (relativeHomologyMap ℚ d (reindexPair h) (standardLocalClass ℚ d))
      (standardLocalClass ℚ d') := by
  subst h
  have : reindexPair (rfl : d' = d') = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext <;> rfl
  rw [this, relativeHomologyMap_id]
  rfl

/-- **Complex form, sign `+`.** The shuffle cross product of upstream's complex orientation
classes of `ℂ^a` and `ℂ^b`, pushed along `complexAppendMap`, is upstream's complex orientation
class of `ℂ^{a+b}`, exactly, read in degree `2a + 2b` through `2 (a + b) = 2a + 2b`
(register row "Cross product of complex orientations"). The route is
`complexRealHomeomorph_append`, `relCrossUnion_naturality` and `cross_orientation_real` at
`m = 2a`, `n = 2b`. -/
theorem cross_orientation_complex (a b : ℕ) :
    relativeHomologyMap ℚ (2 * a + 2 * b)
      (TopPair.ofSubsetHom (complexAppendMap a b) (complexAppendMap_mem a b))
      (relCrossUnion (P := TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
        ({0}ᶜ : Set (Fin a → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)) (2 * a) (2 * b)
        (standardComplexLocalClass ℚ a) (standardComplexLocalClass ℚ b)) =
      (Nat.mul_add 2 a b) ▸ standardComplexLocalClass ℚ (a + b) := by
  apply eq_of_heq
  refine HEq.trans ?_ (rhs_heq a b).symm
  refine (relHom_heq _ (by ring) (relCrossUnion_heq _ _ (by ring) (by ring)
    (standardComplexLocalClass_heq a) (standardComplexLocalClass_heq b))).trans ?_
  have hfa : ∀ x ∈ ({0}ᶜ : Set (Fin (a * 2) → ℝ)),
      (TopCat.ofHom ⟨(complexRealHomeomorph a).symm, (complexRealHomeomorph a).symm.continuous⟩ :
        TopCat.of (Fin (a * 2) → ℝ) ⟶ TopCat.of (Fin a → ℂ)) x ∈ ({0}ᶜ : Set (Fin a → ℂ)) :=
    fun x hx h => hx (by
      have h0 : (complexRealHomeomorph a).symm x = 0 := h
      have h' := congrArg (complexRealHomeomorph a) h0
      rw [Homeomorph.apply_symm_apply] at h'
      rw [Set.mem_singleton_iff, h']
      exact map_zero (Complex.piCoordCLE a))
  have hfb : ∀ x ∈ ({0}ᶜ : Set (Fin (b * 2) → ℝ)),
      (TopCat.ofHom ⟨(complexRealHomeomorph b).symm, (complexRealHomeomorph b).symm.continuous⟩ :
        TopCat.of (Fin (b * 2) → ℝ) ⟶ TopCat.of (Fin b → ℂ)) x ∈ ({0}ᶜ : Set (Fin b → ℂ)) :=
    fun x hx h => hx (by
      have h0 : (complexRealHomeomorph b).symm x = 0 := h
      have h' := congrArg (complexRealHomeomorph b) h0
      rw [Homeomorph.apply_symm_apply] at h'
      rw [Set.mem_singleton_iff, h']
      exact map_zero (Complex.piCoordCLE b))
  have hnat := relCrossUnion_naturality _ _ hfa hfb (standardLocalClass ℚ (a * 2))
    (standardLocalClass ℚ (b * 2))
  refine HEq.trans (heq_of_eq (congrArg _ hnat)) ?_
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  have hpair : TopPair.ofSubsetHom (_ ⊗ₘ _) (tensorHom_mem_union _ _ hfa hfb) ≫
      TopPair.ofSubsetHom (complexAppendMap a b) (complexAppendMap_mem a b) =
      TopPair.ofSubsetHom (appendMap (a * 2) (b * 2)) (appendMap_mem _ _) ≫
        reindexPair (Nat.add_mul a b 2) ≫ (standardComplexRealPairIso (a + b)).inv := by
    have key : ∀ (p : Fin (a * 2) → ℝ) (q : Fin (b * 2) → ℝ),
        Fin.append ((complexRealHomeomorph a).symm p) ((complexRealHomeomorph b).symm q) =
          (complexRealHomeomorph (a + b)).symm
            (fun i => Fin.append p q (Fin.cast (Nat.add_mul a b 2) i)) := by
      intro p q
      rw [Homeomorph.eq_symm_apply, complexRealHomeomorph_append, Homeomorph.apply_symm_apply,
        Homeomorph.apply_symm_apply]
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      exact Subtype.ext (key z.1.1 z.1.2)
    · ext z
      exact key z.1 z.2
  rw [hpair, relativeHomologyMap_comp, LinearMap.comp_apply, cross_orientation_real,
    relativeHomologyMap_comp, LinearMap.comp_apply]
  exact relHom_heq _ (Nat.add_mul a b 2).symm (reindexPair_heq _)

/-! ## The form `local-class-cross-model` reads -/

/-- `{z ∈ ℂ^{a+b} | z' ≠ 0}`, `z'` the first `a` coordinates. -/
def setA (a b : ℕ) : Set (Fin (a + b) → ℂ) := {z | (fun i : Fin a => z (Fin.castAdd b i)) ≠ 0}

/-- `{z ∈ ℂ^{a+b} | z'' ≠ 0}`, `z''` the last `b` coordinates. -/
def setB (a b : ℕ) : Set (Fin (a + b) → ℂ) := {z | (fun j : Fin b => z (Fin.natAdd a j)) ≠ 0}

/-- `setA ∪ setB` is `ℂ^{a+b} ∖ 0`, read through the identity homeomorphism. -/
theorem union_eq (a b : ℕ) (z : Fin (a + b) → ℂ) :
    (Homeomorph.refl (Fin (a + b) → ℂ)) z ∈ setA a b ∪ setB a b ↔
      z ∈ ({0}ᶜ : Set (Fin (a + b) → ℂ)) := by
  simp only [Homeomorph.refl_apply, id_eq, Set.mem_union, setA, setB, Set.mem_ofPred_eq,
    Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h) rfl
    · exact h rfl
    · exact h rfl
  · intro hz
    by_contra hc
    push Not at hc
    refine hz (funext fun k => ?_)
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · exact congrFun hc.1 i
    · exact congrFun hc.2 j

/-- Upstream's complex orientation class of `ℂ^{a+b}` on `(ℂ^{a+b}, setA ∪ setB)`, in degree
`2a + 2b`: the identity of `ℂ^{a+b}` as a map of pairs, then the degree cast. -/
def orient (a b : ℕ) : RelativeHomology ℚ
    (TopPair.ofSubset (X := TopCat.of (Fin (a + b) → ℂ)) (setA a b ∪ setB a b)) (2 * a + 2 * b) :=
  (Nat.mul_add 2 a b) ▸ relativeHomologyMap ℚ (2 * (a + b))
    (TopPair.isoOfSubset (Homeomorph.refl _) (fun z => union_eq a b z)).hom
    (standardComplexLocalClass ℚ (a + b))

/-- `complexAppendMap` sends `(ℂ^a ∖ 0) × ℂ^b ∪ ℂ^a × (ℂ^b ∖ 0)` into `setA ∪ setB`. -/
lemma complexAppendMap_mem_union (a b : ℕ) :
    ∀ z ∈ leftProdSet (P := TopCat.of (Fin a → ℂ)) ({0}ᶜ : Set (Fin a → ℂ))
        (TopCat.of (Fin b → ℂ)) ∪
      rightProdSet (TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)),
      complexAppendMap a b z ∈ setA a b ∪ setB a b := by
  rintro z (hz | hz)
  · left
    intro h
    exact hz (funext fun i => (Fin.append_left z.1 z.2 i).symm.trans (congrFun h i))
  · right
    intro h
    exact hz (funext fun j => (Fin.append_right z.1 z.2 j).symm.trans (congrFun h j))

/-- **The complex form on `(ℂ^{a+b}, setA ∪ setB)`**, sign `+`: the cross product of upstream's
complex orientation classes of `ℂ^a` and `ℂ^b`, pushed along `complexAppendMap`, is `orient a b`
(register row "Cross product of complex orientations"). A corollary of
`cross_orientation_complex` through the identity map of pairs. -/
theorem cross_orientation_orient (a b : ℕ) :
    relativeHomologyMap ℚ (2 * a + 2 * b)
      (TopPair.ofSubsetHom (complexAppendMap a b) (complexAppendMap_mem_union a b))
      (relCrossUnion (P := TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
        ({0}ᶜ : Set (Fin a → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)) (2 * a) (2 * b)
        (standardComplexLocalClass ℚ a) (standardComplexLocalClass ℚ b)) =
      orient a b := by
  have hpair : TopPair.ofSubsetHom (complexAppendMap a b) (complexAppendMap_mem_union a b) =
      TopPair.ofSubsetHom (complexAppendMap a b) (complexAppendMap_mem a b) ≫
        (TopPair.isoOfSubset (Homeomorph.refl _) (fun z => union_eq a b z)).hom := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext <;> rfl
  rw [hpair, relativeHomologyMap_comp, LinearMap.comp_apply, cross_orientation_complex]
  apply eq_of_heq
  exact (relHom_heq _ (Nat.mul_add 2 a b).symm (rel_cast_heq _ _)).trans (rel_cast_heq _ _).symm

end HodgeLadder.CrossOrientation
