# 2026-11-27 torus-winding-duality (order 1 of torus-singular-cohomology)

- Checked: `HodgeLadder.Torus.Winding.Duality`. On Tⁿ = `UnitAddTorus (Fin n)`: `coordChar i` (x ↦ exp(2πi xᵢ)), `coordWinding i` (its winding class aᵢ ∈ H¹(Tⁿ; ℚ)), `coordTorus k l` ((s, t) ↦ update (update 0 k s) l t).
- `torusEval_coordTorus_cup`: ⟨aᵢ ⌣ aⱼ, T_kl⟩ = [i = k][j = l] − [i = l][j = k] for k ≠ l, exact, with the singular cup `cupSing` (front face times back face) on the cycle lower − upper. Ψ does not enter; a sheaf cup read through Ψ gives the negative.
- Both orders: `_cup_kl` (value 1), `_cup_lk` (−1), `torusEval_coordTorus_swap` (T_lk, value −1). `torusEval_coordTorus_cup_all` drops k ≠ l (both sides 0 on the circle T_kk, `_cup_diag`).
- Nonvacuity: `coordWinding_cup_ne_zero`, `torus_two_cup_ne_zero`, `torus_two_cup_swap_ne` (a₁ ⌣ a₀ ≠ a₀ ⌣ a₁ on T²), `torus_two_cup_self_eval` (value 0, a value lemma only).
- `linearIndependent_coordCup`: the products aᵢ ⌣ aⱼ with i < j (`coordCup`) are linearly independent in H²(Tⁿ; ℚ) for every n, from the formula alone (red-team probe P5). This is the degree-2 independence half of `torus-singular-cohomology`, so that rung uses `coordCup` from here.
- Proof: the general edge lemmas `val_frontEdge_of_phase`, `val_backEdge_of_phase` (any space, g ∘ T = exp(2πi π)) generalize the four edge lemmas of `winding-torus-cup`; then `torusEval_cupSing`. At n = 2 the values agree with `torusEval_cupSing_winding` by an independent route (red team P1).
- Red team (`docs/sketches/torus-winding-duality.redteam.md`): pass with changes, all applied. Unused k ≠ l removed from `coordTorus_apply`, `coordChar_coordTorus`, `val_backEdge_coord`; ⌣ and `cupSing` in the ledger title and roadmap row; conventions row "Coordinate tori of Tⁿ"; gaps rows at layers 11 and 12. Optional O1, O2 (as a lemma here) and O3 done.
- Cost: the file elaborates in about 5 s; `tools/check.py` exits 0.
- Next: `torus-singular-cohomology` still needs `cupSing` additivity in the first slot for the H¹ half, plus the upper bound from `torus-homology-bound`.
