module

public import HodgeLadder.Cup.WindingTorus
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Winding classes of the coordinates of `Tⁿ` against the coordinate `2`-tori

Rung `torus-winding-duality` (sub-rung of `torus-singular-cohomology`, sketch
`docs/sketches/torus-singular-cohomology.md`, step 8).

On the real torus `Tⁿ = UnitAddTorus (Fin n)` let `aᵢ ∈ H¹(Tⁿ; ℚ)` be the winding class of the
coordinate character `x ↦ exp (2πi xᵢ)` (`coordWinding i`), and for `k l : Fin n` let
`T_kl : ℝ × ℝ → Tⁿ` be the coordinate `2`-torus `(s, t) ↦ update (update 0 k s) l t`
(`coordTorus k l`). For `k ≠ l` and all `i j`,

  `⟨aᵢ ⌣ aⱼ, T_kl⟩ = [i = k][j = l] − [i = l][j = k]`,

exactly, with no scalar. The cup product is the ladder's singular cup `HodgeLadder.Cup.cupSing`
(Tau Ceti's front face times back face) on upstream's
`AlgebraicTopology.Singular.Cohomology ℚ`, and the pairing is `HodgeLadder.Cup.torusEval`, the
evaluation on the cycle `T_kl ∘ (lower − upper)` of rung `torus-cycle-pairing`. The formula holds
in both orders: `⟨a_k ⌣ a_l, T_kl⟩ = 1`, `⟨a_l ⌣ a_k, T_kl⟩ = −1`, and swapping `k` and `l`
reverses the orientation of the cycle, so `⟨a_k ⌣ a_l, T_lk⟩ = −1`.

The sheaf-singular comparison `Ψ` does not enter this file. A consumer that reads a sheaf cup
`x ∪ y` of degree-one classes through `Ψ` picks up the sign `(−1)^{1·1} = −1` of
`cup_singular_comparison` (conventions row "Sheaf–singular comparison Ψ").

The proof generalizes the edge computations of rung `winding-torus-cup`: along `T_kl` the
character of the `i`-th coordinate is `exp (2πi π)` with `π (s, t)` equal to `t` if `i = l`, to
`s` if `i = k`, and to `0` otherwise; the front edge reads `π (1, 0) − π (0, 0)` and the back edge
`π (1, 1) − π (1, 0)`, and `torusEval_cupSing` turns these into the determinant.

## Main definitions

* `HodgeLadder.Torus.torus`, `HodgeLadder.Torus.coordChar`, `HodgeLadder.Torus.coordWinding`,
  `HodgeLadder.Torus.coordTorus`, `HodgeLadder.Torus.coordPhase`, `HodgeLadder.Torus.coordCup`

## Main results

* `HodgeLadder.Torus.torusEval_coordTorus_cup`: the duality formula, for `k ≠ l`;
  `HodgeLadder.Torus.torusEval_coordTorus_cup_all` drops `k ≠ l`
  (`HodgeLadder.Torus.torusEval_coordTorus_cup_diag`: the value `0` on `T_kk`).
* `HodgeLadder.Torus.linearIndependent_coordCup`: the products `aᵢ ⌣ aⱼ` with `i < j`
  (`HodgeLadder.Torus.coordCup`) are linearly independent in `H²(Tⁿ; ℚ)`.
* `HodgeLadder.Torus.torusEval_coordTorus_cup_kl`, `HodgeLadder.Torus.torusEval_coordTorus_cup_lk`,
  `HodgeLadder.Torus.torusEval_coordTorus_swap`: the values `1`, `−1`, `−1` in the two orders.
* `HodgeLadder.Torus.torusEval_coordTorus_cup_self`, `HodgeLadder.Torus.coordWinding_cup_ne_zero`,
  `HodgeLadder.Torus.torus_two_cup_ne_zero`, `HodgeLadder.Torus.torus_two_cup_self_eval`,
  `HodgeLadder.Torus.torus_two_cup_swap_ne`: nonvacuity on `Tⁿ` and `T²`.
-/

@[expose] public noncomputable section

open CategoryTheory HodgeLadder.Cup ChernWinding

namespace HodgeLadder.Torus

/-- The real torus `Tⁿ = UnitAddTorus (Fin n)` as a topological space in `TopCat`. -/
abbrev torus (n : ℕ) : TopCat.{0} := TopCat.of (UnitAddTorus (Fin n))

/-- The character of the `i`-th coordinate, `x ↦ exp (2πi xᵢ)`, as a continuous function
`Tⁿ → ℂ`. -/
def coordChar {n : ℕ} (i : Fin n) : C(torus n, ℂ) :=
  ⟨fun x => ((AddCircle.toCircle ((x : UnitAddTorus (Fin n)) i) : Circle) : ℂ),
    continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp (continuous_apply i))⟩

/-- The coordinate character does not vanish. -/
theorem coordChar_ne_zero {n : ℕ} (i : Fin n) (x : torus n) : coordChar i x ≠ 0 :=
  Circle.coe_ne_zero _

/-- **The winding class `aᵢ ∈ H¹(Tⁿ; ℚ)`** of the `i`-th coordinate character. -/
def coordWinding {n : ℕ} (i : Fin n) : AlgebraicTopology.Singular.Cohomology ℚ (torus n) 1 :=
  windingClass (coordChar i) (coordChar_ne_zero i)

/-- **The coordinate `2`-torus `T_kl`**, `(s, t) ↦ update (update 0 k s) l t`. -/
def coordTorus {n : ℕ} (k l : Fin n) : C(ℝ × ℝ, torus n) :=
  ⟨fun p => Function.update (Function.update (0 : UnitAddTorus (Fin n)) k (p.1 : UnitAddCircle))
      l (p.2 : UnitAddCircle),
    (continuous_const.update k (AddCircle.continuous_mk' 1 |>.comp continuous_fst)).update l
      (AddCircle.continuous_mk' 1 |>.comp continuous_snd)⟩

/-- The coordinates of `T_kl (s, t)`; for `k = l` the second update wins. -/
theorem coordTorus_apply {n : ℕ} (k l : Fin n) (p : ℝ × ℝ) (i : Fin n) :
    (coordTorus k l p : UnitAddTorus (Fin n)) i =
      ((if i = l then p.2 else if i = k then p.1 else 0 : ℝ) : UnitAddCircle) := by
  simp only [coordTorus, ContinuousMap.coe_mk]
  by_cases hl : i = l
  · subst hl; simp
  · by_cases hk : i = k
    · subst hk; simp [hl]
    · simp [hl, hk]

/-- `T_kl` has period `1` in the first variable. -/
theorem coordTorus_one_left {n : ℕ} (k l : Fin n) (t : ℝ) :
    coordTorus k l (1, t) = coordTorus k l (0, t) := by
  simp only [coordTorus, ContinuousMap.coe_mk]
  rw [AddCircle.coe_period, AddCircle.coe_zero]

/-- `T_kl` has period `1` in the second variable. -/
theorem coordTorus_one_right {n : ℕ} (k l : Fin n) (s : ℝ) :
    coordTorus k l (s, 1) = coordTorus k l (s, 0) := by
  simp only [coordTorus, ContinuousMap.coe_mk]
  rw [AddCircle.coe_period, AddCircle.coe_zero]

/-- The phase of the `i`-th coordinate along `T_kl`: `t` if `i = l`, `s` if `i = k`, else `0`. -/
def coordPhase {n : ℕ} (k l i : Fin n) (p : ℝ × ℝ) : ℝ :=
  if i = l then p.2 else if i = k then p.1 else 0

/-- The phase is continuous. -/
theorem continuous_coordPhase {n : ℕ} (k l i : Fin n) : Continuous (coordPhase k l i) :=
  continuous_if_const _ (fun _ => continuous_snd)
    (fun _ => continuous_if_const _ (fun _ => continuous_fst) (fun _ => continuous_const))

/-- Along `T_kl` the `i`-th coordinate character is `exp (2πi π)`, `π = coordPhase k l i`. -/
theorem coordChar_coordTorus {n : ℕ} (k l i : Fin n) (p : ℝ × ℝ) :
    coordChar i (coordTorus k l p) = Complex.exp (twoPiI * (coordPhase k l i p : ℂ)) := by
  change ((AddCircle.toCircle ((coordTorus k l p : UnitAddTorus (Fin n)) i) : Circle) : ℂ) = _
  rw [coordTorus_apply, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1
  simp only [coordPhase, twoPiI]
  push_cast
  ring

variable {Y : TopCat.{0}} {T : C(ℝ × ℝ, Y)}

/-- The winding value on the front edge of `T`, when `g ∘ T = exp (2πi π)`: the change
`π (1, 0) − π (0, 0)`. -/
theorem val_frontEdge_of_phase (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (π : ℝ × ℝ → ℝ)
    (hπ : Continuous π) (hgT : ∀ p, g (T p) = Complex.exp (twoPiI * (π p : ℂ))) (q : ℚ)
    (hq : π (1, 0) - π (0, 0) = q) : val (windingTC g hg) (frontEdge T) = q := by
  refine val_windingTC_of_increment _ _ _ q ?_
  rw [simplexIncrement_torus g hg π hπ hgT (lowerFace 2) _ (simplexMap_δ_lower T 2),
    lowerFace_single, lowerFace_single, lowerTriangle_single, lowerTriangle_single]
  have e0 : (2 : Fin 3).succAbove 0 = 0 := by decide
  have e1 : (2 : Fin 3).succAbove 1 = 1 := by decide
  simp only [e0, e1]
  norm_num
  rw [← Complex.ofReal_sub, hq]
  push_cast
  rfl

/-- The winding value on the back edge of `T`, when `g ∘ T = exp (2πi π)`: the change
`π (1, 1) − π (1, 0)`. -/
theorem val_backEdge_of_phase (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (π : ℝ × ℝ → ℝ)
    (hπ : Continuous π) (hgT : ∀ p, g (T p) = Complex.exp (twoPiI * (π p : ℂ))) (q : ℚ)
    (hq : π (1, 1) - π (1, 0) = q) : val (windingTC g hg) (backEdge T) = q := by
  refine val_windingTC_of_increment _ _ _ q ?_
  rw [simplexIncrement_torus g hg π hπ hgT (lowerFace 0) _ (simplexMap_δ_lower T 0),
    lowerFace_single, lowerFace_single, lowerTriangle_single, lowerTriangle_single]
  have e0 : (0 : Fin 3).succAbove 0 = 1 := by decide
  have e1 : (0 : Fin 3).succAbove 1 = 2 := by decide
  simp only [e0, e1]
  norm_num
  rw [← Complex.ofReal_sub, hq]
  push_cast
  rfl

/-- The winding value of `aᵢ` on the front edge of `T_kl`: `[i = k]`. -/
theorem val_frontEdge_coord {n : ℕ} {k l : Fin n} (hkl : k ≠ l) (i : Fin n) :
    val (windingTC (coordChar i) (coordChar_ne_zero i)) (frontEdge (coordTorus k l)) =
      if i = k then 1 else 0 := by
  refine val_frontEdge_of_phase _ _ _ (continuous_coordPhase k l i)
    (coordChar_coordTorus k l i) _ ?_
  have hlk : l ≠ k := hkl.symm
  by_cases hk : i = k
  · subst hk; simp [coordPhase, hkl]
  · by_cases hl : i = l
    · subst hl; simp [coordPhase, hlk]
    · simp [coordPhase, hk, hl]

/-- The winding value of `aᵢ` on the back edge of `T_kl`: `[i = l]`, for all `k l`. -/
theorem val_backEdge_coord {n : ℕ} (k l i : Fin n) :
    val (windingTC (coordChar i) (coordChar_ne_zero i)) (backEdge (coordTorus k l)) =
      if i = l then 1 else 0 := by
  refine val_backEdge_of_phase _ _ _ (continuous_coordPhase k l i)
    (coordChar_coordTorus k l i) _ ?_
  by_cases hl : i = l
  · simp [coordPhase, hl]
  · by_cases hk : i = k
    · subst hk; simp [coordPhase, hl]
    · simp [coordPhase, hk, hl]

/-- **The duality formula** `⟨aᵢ ⌣ aⱼ, T_kl⟩ = [i = k][j = l] − [i = l][j = k]`, exact, for
`k ≠ l`. -/
theorem torusEval_coordTorus_cup {n : ℕ} {k l : Fin n} (hkl : k ≠ l) (i j : Fin n) :
    torusEval (coordTorus_one_left k l) (coordTorus_one_right k l)
        (cupSing (torus n) (coordWinding i) (coordWinding j) 2 rfl) =
      (if i = k ∧ j = l then 1 else 0) - (if i = l ∧ j = k then 1 else 0) := by
  rw [coordWinding, coordWinding, torusEval_cupSing, val_frontEdge_coord hkl,
    val_frontEdge_coord hkl, val_backEdge_coord k l, val_backEdge_coord k l]
  by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hjk : j = k <;>
    by_cases hjl : j = l <;> simp [hik, hil, hjk, hjl, hkl, hkl.symm]

/-- On the diagonal `T_kk` (a circle) every product of two coordinate classes evaluates to
`0`: the front edge is constant. -/
theorem torusEval_coordTorus_cup_diag {n : ℕ} (k i j : Fin n) :
    torusEval (coordTorus_one_left k k) (coordTorus_one_right k k)
        (cupSing (torus n) (coordWinding i) (coordWinding j) 2 rfl) = 0 := by
  have hf : ∀ m : Fin n, val (windingTC (coordChar m) (coordChar_ne_zero m))
      (frontEdge (coordTorus k k)) = 0 := fun m =>
    val_frontEdge_of_phase _ _ _ (continuous_coordPhase k k m) (coordChar_coordTorus k k m) 0
      (by by_cases h : m = k <;> simp [coordPhase, h])
  rw [coordWinding, coordWinding, torusEval_cupSing, hf, hf]
  simp

/-- **The duality formula for all `k l`**: `⟨aᵢ ⌣ aⱼ, T_kl⟩ = [i = k][j = l] − [i = l][j = k]`.
For `k = l` both sides are `0`. -/
theorem torusEval_coordTorus_cup_all {n : ℕ} (k l i j : Fin n) :
    torusEval (coordTorus_one_left k l) (coordTorus_one_right k l)
        (cupSing (torus n) (coordWinding i) (coordWinding j) 2 rfl) =
      (if i = k ∧ j = l then 1 else 0) - (if i = l ∧ j = k then 1 else 0) := by
  by_cases hkl : k = l
  · subst hkl
    rw [torusEval_coordTorus_cup_diag]
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp [hi, hj]
  · exact torusEval_coordTorus_cup hkl i j

/-- **`⟨a_k ⌣ a_l, T_kl⟩ = 1`** for `k ≠ l`. -/
theorem torusEval_coordTorus_cup_kl {n : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    torusEval (coordTorus_one_left k l) (coordTorus_one_right k l)
        (cupSing (torus n) (coordWinding k) (coordWinding l) 2 rfl) = 1 := by
  rw [torusEval_coordTorus_cup hkl]
  simp [hkl]

/-- **`⟨a_l ⌣ a_k, T_kl⟩ = −1`** for `k ≠ l`: the other order of the factors. -/
theorem torusEval_coordTorus_cup_lk {n : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    torusEval (coordTorus_one_left k l) (coordTorus_one_right k l)
        (cupSing (torus n) (coordWinding l) (coordWinding k) 2 rfl) = -1 := by
  rw [torusEval_coordTorus_cup hkl]
  simp [hkl, hkl.symm]

/-- **`⟨a_k ⌣ a_l, T_lk⟩ = −1`** for `k ≠ l`: the other order of the torus coordinates
reverses the orientation of the cycle. -/
theorem torusEval_coordTorus_swap {n : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    torusEval (coordTorus_one_left l k) (coordTorus_one_right l k)
        (cupSing (torus n) (coordWinding k) (coordWinding l) 2 rfl) = -1 := by
  rw [torusEval_coordTorus_cup hkl.symm]
  simp [hkl, hkl.symm]

/-- **`⟨aᵢ ⌣ aᵢ, T_kl⟩ = 0`** on every coordinate `2`-torus. -/
theorem torusEval_coordTorus_cup_self {n : ℕ} {k l : Fin n} (hkl : k ≠ l) (i : Fin n) :
    torusEval (coordTorus_one_left k l) (coordTorus_one_right k l)
        (cupSing (torus n) (coordWinding i) (coordWinding i) 2 rfl) = 0 := by
  rw [torusEval_coordTorus_cup hkl]
  by_cases hk : i = k
  · subst hk; simp [hkl]
  · simp [hk]

/-- **`a_k ⌣ a_l ≠ 0`** in `H²(Tⁿ; ℚ)` for `k ≠ l`. -/
theorem coordWinding_cup_ne_zero {n : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    cupSing (torus n) (coordWinding k) (coordWinding l) 2 rfl ≠ 0 := by
  intro h
  have := torusEval_coordTorus_cup_kl hkl
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- **On `T²`, `a₀ ⌣ a₁ ≠ 0`.** -/
theorem torus_two_cup_ne_zero :
    cupSing (torus 2) (coordWinding 0) (coordWinding 1) 2 rfl ≠ 0 :=
  coordWinding_cup_ne_zero (by decide)

/-- **On `T²`, `⟨a₀ ⌣ a₀, T₀₁⟩ = 0`.** -/
theorem torus_two_cup_self_eval :
    torusEval (coordTorus_one_left (0 : Fin 2) 1) (coordTorus_one_right (0 : Fin 2) 1)
        (cupSing (torus 2) (coordWinding 0) (coordWinding 0) 2 rfl) = 0 :=
  torusEval_coordTorus_cup_self (by decide) 0

/-- **On `T²`, `a₁ ⌣ a₀ ≠ a₀ ⌣ a₁`**: the two orders differ, as the sign `(−1)^{1·1}` of
`cupSing_gradedComm` predicts. -/
theorem torus_two_cup_swap_ne :
    cupSing (torus 2) (coordWinding 1) (coordWinding 0) 2 rfl ≠
      cupSing (torus 2) (coordWinding 0) (coordWinding 1) 2 rfl := by
  intro h
  have h1 := torusEval_coordTorus_cup_kl (n := 2) (k := 0) (l := 1) (by decide)
  have h2 := torusEval_coordTorus_cup_lk (n := 2) (k := 0) (l := 1) (by decide)
  rw [h, h1] at h2
  norm_num at h2

/-- The product `aᵢ ⌣ aⱼ ∈ H²(Tⁿ; ℚ)` for an index pair `i < j`. -/
def coordCup {n : ℕ} (p : {p : Fin n × Fin n // p.1 < p.2}) :
    AlgebraicTopology.Singular.Cohomology ℚ (torus n) 2 :=
  cupSing (torus n) (coordWinding p.1.1) (coordWinding p.1.2) 2 rfl

/-- **The products `aᵢ ⌣ aⱼ` with `i < j` are linearly independent** in `H²(Tⁿ; ℚ)`, for every
`n`: evaluation on `T_kl` with `k < l` picks out the coefficient of `a_k ⌣ a_l`. -/
theorem linearIndependent_coordCup (n : ℕ) : LinearIndependent ℚ (coordCup (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have hkl : q.1.1 ≠ q.1.2 := ne_of_lt q.2
  have := congrArg (torusEval (coordTorus_one_left q.1.1 q.1.2)
    (coordTorus_one_right q.1.1 q.1.2)) hg
  rw [map_sum, map_zero] at this
  simp only [coordCup, map_smul, torusEval_coordTorus_cup hkl, smul_eq_mul] at this
  rw [Finset.sum_eq_single q] at this
  · have h2 : ¬ (q.1.1 = q.1.2 ∧ q.1.2 = q.1.1) := fun h => hkl h.1
    simpa [h2] using this
  · intro p _ hpq
    have hp := p.2
    have hq := q.2
    have h1 : ¬ (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) := fun h =>
      hpq (Subtype.ext (Prod.ext h.1 h.2))
    have h2 : ¬ (p.1.1 = q.1.2 ∧ p.1.2 = q.1.1) := by
      rintro ⟨h3, h4⟩; rw [h3, h4] at hp; exact lt_asymm hp hq
    simp [h1, h2]
  · simp

end HodgeLadder.Torus
