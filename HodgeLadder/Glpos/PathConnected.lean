module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Real matrices with positive determinant are joined to the identity

A real square matrix `A` with `0 < A.det` is joined to the identity matrix `1` by a continuous
path of real matrices, every member of which has positive determinant. Equivalently, the set
`{M : Matrix n n ℝ | 0 < M.det}` (the matrix form of `GL⁺ₙ(ℝ)`) is path-connected.

The path lives in `Matrix n n ℝ` with its product topology, so a consumer gets a
`Path (1 : Matrix n n ℝ) A` from `JoinedIn.somePath` and the determinant bound at every time
from `JoinedIn.somePath_mem`. This is the shape of upstream's complex isotopy
`Matrix.ComplexIsotopyToOne`, which `real-affine-orientation` follows to build a homotopy of
punctured pairs.

## Main results

* `HodgeLadder.Glpos.joinedIn_one_of_det_pos`: a real matrix with positive determinant is
  joined to `1` within `{M | 0 < M.det}`.
* `HodgeLadder.Glpos.isPathConnected_setOf_det_pos`: the set `{M | 0 < M.det}` is
  path-connected.
* Steps: `joinedIn_one_mul` (products), `joinedIn_one_transvection`,
  `joinedIn_one_diagonal_of_pos`, `quarterTurn_mul_self` (the square of the quarter turn
  `transvection i j (-1) * transvection j i 1 * transvection i j (-1)` negates the entries at
  `i` and `j`), `joinedIn_one_diagonal` (induction on the number of negative entries).
* Sanity checks: `not_joinedIn_det_ne_zero_fin_one` (the `det ≠ 0` form fails over `ℝ`) and
  `joinedIn_one_diagonal_neg_one_neg_one` (the sign-flip case at size two).

The classical statement is that `GL⁺ₙ(ℝ)` is path-connected [`Hall2015`; section number
unverified].
-/

@[expose] public section

open Matrix

namespace HodgeLadder.Glpos

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Paths to the identity inside `{M | 0 < M.det}` multiply: if `A` and `B` are joined to `1`
there, so is `A * B` (pointwise product of the two paths). -/
theorem joinedIn_one_mul {A B : Matrix n n ℝ}
    (hA : JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 A)
    (hB : JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 B) :
    JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 (A * B) := by
  have h := hA.mul hB
  rw [one_mul] at h
  refine h.mono ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  simp only [Set.mem_ofPred_eq, det_mul] at hx hy ⊢
  exact mul_pos hx hy

/-- A family of matrices continuous on `[0, 1]` with positive determinant there joins its two
endpoints inside `{M | 0 < M.det}`. -/
theorem joinedIn_of_continuousOn {f : ℝ → Matrix n n ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < (f s).det) :
    JoinedIn {M : Matrix n n ℝ | 0 < M.det} (f 0) (f 1) := by
  have h : JoinedIn (Set.Icc (0 : ℝ) 1) 0 1 :=
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩).joinedIn 0 (by simp) 1 (by simp)
  refine (h.map hf).mono ?_
  rintro _ ⟨s, hs, rfl⟩
  exact hpos s hs

/-- A real transvection is joined to `1` inside `{M | 0 < M.det}`, by scaling its off-diagonal
entry. -/
theorem joinedIn_one_transvection {i j : n} (hij : i ≠ j) (c : ℝ) :
    JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 (transvection i j c) := by
  have h := joinedIn_of_continuousOn (f := fun s : ℝ ↦ transvection i j (s * c)) ?_ ?_
  · simpa using h
  · refine Continuous.continuousOn (continuous_matrix fun a b ↦ ?_)
    simp only [transvection, Matrix.add_apply, single_apply]
    split_ifs <;> fun_prop
  · intro s _
    simp [det_transvection_of_ne _ _ hij]

/-- A real diagonal matrix with positive entries is joined to `1` inside `{M | 0 < M.det}`, by
the straight segment. -/
theorem joinedIn_one_diagonal_of_pos (D : n → ℝ) (hD : ∀ k, 0 < D k) :
    JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 (diagonal D) := by
  have h := joinedIn_of_continuousOn
    (f := fun s : ℝ ↦ diagonal fun k ↦ (1 - s) + s * D k) ?_ ?_
  · simpa using h
  · exact Continuous.continuousOn (Continuous.matrix_diagonal (continuous_pi fun k ↦ by fun_prop))
  · intro s hs
    rw [det_diagonal]
    refine Finset.prod_pos fun k _ ↦ ?_
    rcases eq_or_lt_of_le hs.2 with h | h
    · subst h
      simpa using hD k
    · nlinarith [mul_nonneg hs.1 (hD k).le]

/-- **The quarter turn squared.** For `i ≠ j`, the product of three transvections
`W = transvection i j (-1) * transvection j i 1 * transvection i j (-1)` is the rotation by a
quarter turn in the `(i, j)`-plane, and `W * W` is the diagonal matrix with `-1` at `i` and `j`
and `1` elsewhere. -/
theorem quarterTurn_mul_self {i j : n} (hij : i ≠ j) :
    (transvection i j (-1 : ℝ) * transvection j i 1 * transvection i j (-1)) *
      (transvection i j (-1 : ℝ) * transvection j i 1 * transvection i j (-1)) =
      diagonal (fun k ↦ if k = i ∨ k = j then -1 else 1) := by
  ext a b
  simp only [transvection, add_mul, mul_add, one_mul, mul_one, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij, single_mul_single_of_ne _ _ _ _ hij.symm, add_zero]
  simp only [Matrix.add_apply, single_apply, one_apply, diagonal_apply]
  split_ifs <;> subst_vars <;> simp_all <;> grind

/-- A real diagonal matrix with positive determinant is joined to `1` inside
`{M | 0 < M.det}`. Induction on the number of negative entries: two of them are flipped by the
square of a quarter turn, exactly one is excluded by the sign of the product, and none is
`joinedIn_one_diagonal_of_pos`. -/
theorem joinedIn_one_diagonal (D : n → ℝ) (hD : 0 < ∏ k, D k) :
    JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 (diagonal D) := by
  suffices h : ∀ m, ∀ D : n → ℝ, (Finset.univ.filter fun k ↦ D k < 0).card = m →
      0 < ∏ k, D k → JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 (diagonal D) from
    h _ D rfl hD
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro D hm hD
  have hne : ∀ k, D k ≠ 0 := fun k hk ↦ hD.ne' (Finset.prod_eq_zero (Finset.mem_univ k) hk)
  set N := Finset.univ.filter fun k ↦ D k < 0 with hN
  rcases Nat.lt_or_ge 1 N.card with h2 | h1
  · -- two negative entries `i ≠ j`: flip them by the square of a quarter turn
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 h2
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    set ε : n → ℝ := fun k ↦ if k = i ∨ k = j then -1 else 1 with hε
    set D' : n → ℝ := fun k ↦ if k = i ∨ k = j then -D k else D k with hD'
    set W : Matrix n n ℝ := transvection i j (-1) * transvection j i 1 * transvection i j (-1)
      with hW
    have hWW : W * W = diagonal ε := quarterTurn_mul_self hij
    have hsplit : diagonal D = diagonal D' * (W * W) := by
      rw [hWW, diagonal_mul_diagonal]
      congr 1
      funext k
      simp only [hD', hε]
      split_ifs <;> ring
    have hdetW : W.det = 1 := by
      simp [hW, det_mul, det_transvection_of_ne _ _ hij, det_transvection_of_ne _ _ hij.symm]
    have hD'pos : 0 < ∏ k, D' k := by
      have := congrArg Matrix.det hsplit
      rw [det_mul, det_mul, hdetW, det_diagonal, det_diagonal, mul_one, mul_one] at this
      rw [← this]
      exact hD
    have hsub : (Finset.univ.filter fun k ↦ D' k < 0) ⊂ N := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i, by simpa [hN] using hi, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hD', true_or, ite_true]
        linarith
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hD'] at hk
        simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs at hk with hk'
        · rcases hk' with rfl | rfl <;> linarith
        · exact hk
    have hW1 : JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 W :=
      joinedIn_one_mul (joinedIn_one_mul (joinedIn_one_transvection hij _)
        (joinedIn_one_transvection hij.symm _)) (joinedIn_one_transvection hij _)
    rw [hsplit]
    exact joinedIn_one_mul (ih _ (hm ▸ Finset.card_lt_card hsub) D' rfl hD'pos)
      (joinedIn_one_mul hW1 hW1)
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h1
    · -- no negative entry
      refine joinedIn_one_diagonal_of_pos D fun k ↦ ?_
      have hk : k ∉ N := by simp [Finset.card_eq_zero.1 h0]
      simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
      exact lt_of_le_of_ne hk (hne k).symm
    · -- exactly one negative entry: the product is negative
      exfalso
      obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
      have hDi : D i < 0 := by
        have : i ∈ N := by simp [hi]
        simpa [hN] using this
      have hrest : 0 < ∏ k ∈ Finset.univ.erase i, D k := by
        refine Finset.prod_pos fun k hk ↦ ?_
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        have : k ∉ N := by simp [hi, hki]
        simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
        exact lt_of_le_of_ne this (hne k).symm
      rw [← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)] at hD
      nlinarith

/-- **A real matrix with positive determinant is joined to the identity inside `GL⁺`.**
For a finite index type `n` and `A : Matrix n n ℝ` with `0 < A.det`, there is a continuous path
of real matrices from `1` to `A`, every member of which has positive determinant.

Proof: Mathlib's `Matrix.diagonal_transvection_induction` writes `A` from transvections and a
diagonal matrix with the determinant of `A`; transvections are joined to `1` by scaling,
products by `joinedIn_one_mul`, and the diagonal factor by `joinedIn_one_diagonal`. -/
theorem joinedIn_one_of_det_pos {A : Matrix n n ℝ} (hA : 0 < A.det) :
    JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 A := by
  have key := diagonal_transvection_induction
    (fun M ↦ 0 < M.det ∧ JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 M) A ?_ ?_ ?_
  · exact key.2
  · intro D hD
    refine ⟨hD ▸ hA, joinedIn_one_diagonal D ?_⟩
    rw [← det_diagonal, hD]
    exact hA
  · intro t
    exact ⟨by simp [t.det], joinedIn_one_transvection t.hij t.c⟩
  · intro B C hB hC
    exact ⟨by rw [det_mul]; exact mul_pos hB.1 hC.1, joinedIn_one_mul hB.2 hC.2⟩

/-- **`GL⁺ₙ(ℝ)` is path-connected**, in matrix form: the real `n × n` matrices with positive
determinant form a path-connected subset of `Matrix n n ℝ`. -/
theorem isPathConnected_setOf_det_pos :
    IsPathConnected {M : Matrix n n ℝ | 0 < M.det} :=
  ⟨1, by simp, fun _ hA ↦ joinedIn_one_of_det_pos hA⟩

/-! ### Sanity checks -/

/-- **Negative check.** The `det ≠ 0` form of the rung is false over `ℝ`: at size one, the
matrix `diagonal ![-1]` is not joined to `1` through invertible matrices, since `det` would
take the value `0` along the path (intermediate value theorem). -/
theorem not_joinedIn_det_ne_zero_fin_one :
    ¬ JoinedIn {M : Matrix (Fin 1) (Fin 1) ℝ | M.det ≠ 0} 1 (diagonal ![-1]) := by
  intro h
  have hc : Continuous fun t ↦ (h.somePath t).det := h.somePath.continuous.matrix_det
  obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hc
    (show (0 : ℝ) ∈ Set.Icc _ _ by simp)
  exact h.somePath_mem t ht

/-- **The sign-flip case.** `diagonal ![-1, -1]`, a matrix with positive determinant and two
negative entries, is joined to `1` inside `{M | 0 < M.det}`. The `det ≠ 0` form cannot tell
this matrix from `diagonal ![-1, 1]`. -/
theorem joinedIn_one_diagonal_neg_one_neg_one :
    JoinedIn {M : Matrix (Fin 2) (Fin 2) ℝ | 0 < M.det} 1 (diagonal ![-1, -1]) :=
  joinedIn_one_of_det_pos (by simp [det_diagonal, Fin.prod_univ_two])

end HodgeLadder.Glpos
