module

public import HodgeLadder.Local.ClassProduct
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-!
# Tests: the product of normalized local classes

Non-vacuity tests of rung `local-class-product` (`HodgeLadder.Local.ClassProduct`).

## Main results

* `HodgeLadder.Tests.relCup2_model_ne_zero`: both sides of the model form are nonzero, so the
  identity separates `+` from `-` and from `0`.
* `HodgeLadder.Tests.relCup2_model_ne_neg`: the sign test, the model product is not minus
  `u_{a+b}`.
* `HodgeLadder.Tests.coordinate_hyps`: on `M = ℂ^{a+b}` the coordinate charts `z ↦ (z'', z')`,
  `z ↦ (z', z'')`, `z ↦ (0, z)` meet every hypothesis of
  `relCup2_chartNormalProjectionCoclass` with `Z = {z' = 0}`, `W = {z'' = 0}`, `T = {0}`.
* `HodgeLadder.Tests.coordinate_chartForm_ne_zero`: on upstream's flattened neighbourhood `V` of
  `0` in that chart (so `0 ∈ T ∩ V`), the right side of the chart form is nonzero.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology.Singular HodgeLadder.Cup HodgeLadder.CrossOrientation
  HodgeLadder.LocalClassProduct

namespace HodgeLadder.Tests

/-- Both sides of the model form are nonzero: the right side pairs to `1` with upstream's
orientation class pushed along the identity of `ℂ^{a+b}`. -/
theorem relCup2_model_ne_zero (a b : ℕ) :
    relativeCohomologyMap ℚ (2 * (a + b)) (unionIso a b).inv (u (a + b)) ≠ 0 := by
  intro h
  have hinv : relativeHomologyMap ℚ (2 * (a + b)) (unionIso a b).inv
      (relativeHomologyMap ℚ (2 * (a + b)) (unionIso a b).hom
        (standardComplexLocalClass ℚ (a + b))) = standardComplexLocalClass ℚ (a + b) := by
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, Iso.hom_inv_id,
      relativeHomologyMap_id, LinearMap.id_apply]
  have h1 := congrArg (fun c => relativeCohomologyEquivDualHomology ℚ _ _ c
    (relativeHomologyMap ℚ (2 * (a + b)) (unionIso a b).hom
      (standardComplexLocalClass ℚ (a + b)))) h
  simp only [relativeCohomologyEquivDualHomology_relativeCohomologyMap, hinv, u,
    normalizedRelativeCoclass_pairing_self, map_zero, LinearMap.zero_apply] at h1
  exact one_ne_zero h1

/-- The model form separates `+` from `-`: the model product is not minus `u_{a+b}`. -/
theorem relCup2_model_ne_neg (a b : ℕ) :
    relCup2 (cx a b) (setA a b) (setB a b) (isOpen_setA a b) (isOpen_setB a b)
        (relativeCohomologyMap ℚ (2 * a) (projA a b) (u a))
        (relativeCohomologyMap ℚ (2 * b) (projB a b) (u b)) (2 * (a + b))
        (Nat.mul_add 2 a b).symm ≠
      -relativeCohomologyMap ℚ (2 * (a + b)) (unionIso a b).inv (u (a + b)) := by
  rw [relCup2_model]
  intro h
  have h2 : (2 : ℚ) • relativeCohomologyMap ℚ (2 * (a + b)) (unionIso a b).inv (u (a + b)) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact relCup2_model_ne_zero a b ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-- `ℂ^{a+b}` with its first block `z'` and second block `z''`. -/
abbrev Cab (a b : ℕ) : Type := Fin (a + b) → ℂ

/-- The chart `z ↦ (z'', z')`: tangential `ℂ^b`, normal `ℂ^a`. -/
def chartZ (a b : ℕ) : OpenPartialHomeomorph (Cab a b) ((Fin b → ℂ) × (Fin a → ℂ)) :=
  ((Fin.appendHomeomorph a b).symm.trans (Homeomorph.prodComm _ _)).toOpenPartialHomeomorph

/-- The chart `z ↦ (z', z'')`: tangential `ℂ^a`, normal `ℂ^b`. -/
def chartW (a b : ℕ) : OpenPartialHomeomorph (Cab a b) ((Fin a → ℂ) × (Fin b → ℂ)) :=
  (Fin.appendHomeomorph a b).symm.toOpenPartialHomeomorph

/-- The chart `z ↦ (0, z)`: tangential `ℂ⁰`, normal `ℂ^{a+b}`. -/
def chartT (a b : ℕ) : OpenPartialHomeomorph (Cab a b) ((Fin 0 → ℂ) × (Fin (a + b) → ℂ)) :=
  (Homeomorph.uniqueProd (Fin 0 → ℂ) (Fin (a + b) → ℂ)).symm.toOpenPartialHomeomorph

/-- `Z = {z' = 0}`. -/
def setZ (a b : ℕ) : Set (Cab a b) := {z | (fun i : Fin a => z (Fin.castAdd b i)) = 0}

/-- `W = {z'' = 0}`. -/
def setW (a b : ℕ) : Set (Cab a b) := {z | (fun j : Fin b => z (Fin.natAdd a j)) = 0}

/-- `T = {0}`. -/
def setT (a b : ℕ) : Set (Cab a b) := {0}

/-- The coordinate charts meet every hypothesis of the chart form, on `V = ℂ^{a+b}`. -/
theorem coordinate_hyps (a b : ℕ) :
    (∀ y ∈ (chartZ a b).source, y ∈ setZ a b ↔ (chartZ a b y).2 = 0) ∧
    (∀ y ∈ (chartW a b).source, y ∈ setW a b ↔ (chartW a b y).2 = 0) ∧
    (∀ y ∈ (chartT a b).source, y ∈ setT a b ↔ (chartT a b y).2 = 0) ∧
    (∀ y : Cab a b, (chartZ a b y).2 = fun i => (chartT a b y).2 (Fin.castAdd b i)) ∧
    (∀ y : Cab a b, (chartW a b y).2 = fun j => (chartT a b y).2 (Fin.natAdd a j)) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl, fun _ => rfl⟩

/-- On upstream's flattened neighbourhood `V` of `0` for the chart `z ↦ (0, z)` (it contains
`0 ∈ T`), the right side of the chart form is nonzero: through `chartUnionIso` it pairs to `1`
with upstream's normal class (`chartNormalProjectionCoclass_apply_normalClass`). -/
theorem coordinate_chartForm_ne_zero (a b : ℕ) :
    let V : Set (Cab a b) := flattenedSupportNeighborhood (Fin 0 → ℂ) (a + b) (chartT a b) 0
      (Set.mem_univ _)
    relativeCohomologyMap ℚ (2 * (a + b))
        (chartUnionIso V (chart_mem_iff (chartZ a b) (chartW a b) (chartT a b)
          (coordinate_hyps a b).1 (coordinate_hyps a b).2.1 (coordinate_hyps a b).2.2.1
          (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
          (flattenedSupportNeighborhood_subset_source _ _ _ _ _)
          (fun y _ => (coordinate_hyps a b).2.2.2.1 y)
          (fun y _ => (coordinate_hyps a b).2.2.2.2 y))).hom
        (chartNormalProjectionCoclass (Fin 0 → ℂ) (a + b) (chartT a b) (setT a b)
          (coordinate_hyps a b).2.2.1 V (flattenedSupportNeighborhood_subset_source _ _ _ _ _)) ≠
      0 := by
  intro V h
  set I := chartUnionIso V (chart_mem_iff (chartZ a b) (chartW a b) (chartT a b)
    (coordinate_hyps a b).1 (coordinate_hyps a b).2.1 (coordinate_hyps a b).2.2.1
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    (flattenedSupportNeighborhood_subset_source _ _ _ _ _)
    (fun y _ => (coordinate_hyps a b).2.2.2.1 y) (fun y _ => (coordinate_hyps a b).2.2.2.2 y))
  set N := flattenedSupportNormalClass (Fin 0 → ℂ) (a + b) (chartT a b) 0 (Set.mem_univ _)
    (setT a b) (coordinate_hyps a b).2.2.1 rfl
  have hinv : relativeHomologyMap ℚ (2 * (a + b)) I.hom
      (relativeHomologyMap ℚ (2 * (a + b)) I.inv N) = N := by
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, Iso.inv_hom_id,
      relativeHomologyMap_id, LinearMap.id_apply]
  have h1 := congrArg (fun c => relativeCohomologyEquivDualHomology ℚ _ _ c
    (relativeHomologyMap ℚ (2 * (a + b)) I.inv N)) h
  simp only [relativeCohomologyEquivDualHomology_relativeCohomologyMap, hinv, map_zero,
    LinearMap.zero_apply] at h1
  have h0 := chartNormalProjectionCoclass_apply_normalClass (Fin 0 → ℂ) (a + b) (chartT a b)
    (setT a b) (coordinate_hyps a b).2.2.1 0 (Set.mem_univ _) rfl
  exact one_ne_zero (h0.symm.trans h1)

end HodgeLadder.Tests
