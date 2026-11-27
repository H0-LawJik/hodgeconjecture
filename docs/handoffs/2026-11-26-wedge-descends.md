# Handoff 2026-11-26: `wedge-descends`

- Checked: `HodgeLadder.wedgeDescends : HodgeLadder.WedgeDescends`, both sides, in `HodgeLadder/Hodge/WedgeDescends.lean`. The statement in `HodgeLadder/Hodge/CupFiltration.lean` is unchanged.
- Route, as in the ledger note. Fix a chart at `z` with coordinate domain `D`. `ExteriorAlgebra.lift` applied to upstream's `chartDerivation` gives an `𝒪(U)`-algebra map `chartExtMap : ⋀ Ω_{𝒪(U)} → (D → ⋀_ℂ (ℂ^d)^*)`. `D → ⋀_ℂ (ℂ^d)^*` is an `𝒪(U)`-algebra through upstream's `chartFieldModule` (`Algebra.ofModule`, local only).
- Factorization: `pairingDual_chartPointForm` says that the degree-p value at `y`, paired by Mathlib's `exteriorPower.pairingDual` with `w₁ ∧ ⋯ ∧ w_p`, is upstream's `chartEvaluation θ y w`. Mathlib's determinant `det (fⱼ (wᵢ))` is the transpose of upstream's `det (Lᵢ (wⱼ))`, so the identity is exact with no sign.
- `exteriorPower.bijective_pairingDual` (ℂ^d is finite free) turns this into `mem_chartEvaluationKernel_iff_chartExtMap`: θ is in the kernel iff `chartExtMap θ` vanishes at every point of every chart. Both sides of `WedgeDescends` follow from `map_mul`. Graded commutativity is not used.
- Seven auxiliary declarations are listed in `docs/gaps.md`. They belong upstream next to `chartEvaluationKernel`.
- Next: `wedge-presheaf`. Lift `formWedge` to `HolomorphicForm X d U` with `Submodule.liftQ` twice, using the two sides, and prove naturality under `holomorphicFormRestriction` from `Algebra.DeRham.map` being multiplicative.
