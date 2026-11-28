module

public import HodgeLadder.Pullback.Functorial

/-!
# The Weil space of an endomorphism

Rung `weil-space` (plan `docs/notes/2026-11-27-t1-plan.md`, node A3). For an endomorphism
`f : X ⟶ X` over `Spec ℂ` and `d : ℚ`, the Weil space is the `−d`-eigenspace of the pullback
`f^* : H²(X; ℚ) → H²(X; ℚ)`:

  `weilSpace X f d = ker (f^* + d • id) = {w ∈ H²(X; ℚ) : f^* w = −d • w}`.

Convention (row "Weil space" in `docs/conventions.md`). The map is the pullback `f^*` of rung
`pullback-functorial` (contravariant: `f : X ⟶ X` acts on `H²(X; ℚ)` by `pullbackCoh f 2`). The
eigenvalue is `−d`, written with `+ d • id` inside the kernel; `weilSpace_eq_ker_sub` and
`weilSpace_eq_eigenspace` give the forms `ker (f^* − (−d) • id)` and
`Module.End.eigenspace f^* (−d)`. No condition on `d` is imposed: on an abelian surface A with
`(f^*)² = −d` on `H¹` and `d > 0`, the eigenvalues of `f^*` on `H¹ ⊗ ℂ` are `±i√d`, each with a
2-dimensional eigenspace `V±`, and on `H² = ∧²H¹` the `−d`-eigenspace has complexification
`∧²V₊ ⊕ ∧²V₋`, the complexification of Weil's `W_K = ∧²_K H¹` for `K = ℚ(√−d)` ([Weil1977];
[vanGeemen1994] §5, locators unverified). If `f` acts as `m√−d`, pass `m² d`. The space is the
same for `f` and for an endomorphism acting by `−f^*` on `H¹`. Positivity of `d` and the
Weil-type (balance) condition are hypotheses of the theorem (`IsWeilTypeSurface`, rung
`weil-surface-statement`), not of this definition. The eigenspace description is specific to
surfaces: on `H^{2n}` of an abelian `2n`-fold with `n ≥ 2` the `(−d)^n`-eigenspace is strictly
larger than `W_K` (dimension 38 against 2 for `n = 2`), so this definition does not serve T3 or
T4. This file uses none of the surface facts.

The comparison with algebraic classes, `weilSpace_le_algebraic_iff_le_hodge`, sits in
`HodgeLadder.Weil.Algebraic`, so that this module depends on the pullback alone.

## Main definitions

* `HodgeLadder.Weil.weilSpace`: `ker (pullbackCohLinear f 2 + d • id)` in `H²(X; ℚ)`.

## Main results

* `HodgeLadder.Weil.mem_weilSpace_iff`: `w ∈ weilSpace X f d ↔ f^* w = −d • w`.
* `HodgeLadder.Weil.weilSpace_eq_ker_sub`, `HodgeLadder.Weil.weilSpace_eq_eigenspace`: the forms
  `ker (f^* − (−d) • id)` and `Module.End.eigenspace f^* (−d)`.
* `HodgeLadder.Weil.weilSpace_id_one`: `weilSpace X (𝟙 X) 1 = ⊥`, the vacuity guard.
* `HodgeLadder.Weil.weilSpace_id_neg_one`: `weilSpace X (𝟙 X) (−1) = ⊤`, the companion guard.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder.Cup HodgeLadder.Pullback

namespace HodgeLadder.Weil

/-- **The Weil space** of `f : X ⟶ X` and `d : ℚ`: the `−d`-eigenspace
`ker (f^* + d • id)` of the pullback `f^*` on `H²(X; ℚ)`. -/
def weilSpace (X : Over (Spec ↧ℂ)) (f : X ⟶ X) (d : ℚ) : Submodule ℚ H^2(X; ℚ) :=
  LinearMap.ker (pullbackCohLinear f 2 + d • LinearMap.id)

/-- A class lies in the Weil space exactly when `f^* w = −d • w`. -/
theorem mem_weilSpace_iff (X : Over (Spec ↧ℂ)) (f : X ⟶ X) (d : ℚ) (w : H^2(X; ℚ)) :
    w ∈ weilSpace X f d ↔ pullbackCoh f 2 w = -d • w := by
  rw [neg_smul]
  exact add_eq_zero_iff_eq_neg

/-- The Weil space in the form `ker (S − c • id)` that `ker_sub_smul_le_span_of_eigen` and
`isCompl_ker_sub_smul_ker_add_smul` consume, with `c = −d`. -/
theorem weilSpace_eq_ker_sub (X : Over (Spec ↧ℂ)) (f : X ⟶ X) (d : ℚ) :
    weilSpace X f d = LinearMap.ker (pullbackCohLinear f 2 - (-d) • LinearMap.id) := by
  rw [neg_smul, sub_neg_eq_add]
  rfl

/-- The Weil space is Mathlib's eigenspace of `f^*` for the eigenvalue `−d`. -/
theorem weilSpace_eq_eigenspace (X : Over (Spec ↧ℂ)) (f : X ⟶ X) (d : ℚ) :
    weilSpace X f d = Module.End.eigenspace (pullbackCohLinear f 2) (-d) := by
  ext w
  rw [Module.End.mem_eigenspace_iff, mem_weilSpace_iff, pullbackCohLinear_apply]

/-- **Vacuity guard**: for the identity and `d = 1` the Weil space is zero, since
`(𝟙 X)^* w = w = −w` forces `w = 0` over `ℚ`. -/
theorem weilSpace_id_one (X : Over (Spec ↧ℂ)) : weilSpace X (𝟙 X) 1 = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
  rw [mem_weilSpace_iff, pullbackCoh_id, neg_smul, one_smul] at hw
  have h2 : (2 : ℚ) • w = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hw]
    exact add_neg_cancel w
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **Companion guard**: for the identity and `d = −1` the Weil space is everything, since
`(𝟙 X)^* w = w = −(−1) • w`. With `weilSpace_id_one` this pins the sign of the eigenvalue. -/
theorem weilSpace_id_neg_one (X : Over (Spec ↧ℂ)) : weilSpace X (𝟙 X) (-1) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun w => ?_
  rw [mem_weilSpace_iff, pullbackCoh_id, neg_neg, one_smul]

end HodgeLadder.Weil
