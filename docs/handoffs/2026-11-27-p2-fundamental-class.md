# Handoff 2026-11-27: `p2-fundamental-class`

- Checked: `HodgeLadder.Tests.ProjectivePlaneFundamental` (the existence half; it does not import `CycleClassSignTestP2`) and `HodgeLadder.Tests.ProjectivePlaneFundamentalDegree` (the ledger module), 16 declarations, standard axioms, both imported from `HodgeLadder.lean`.
- Headline: exactly one μ ∈ H₄(ℙ²(ℂ); ℚ) restricts to `complexLocalOrientation projectivePlane 2 [0 : 0 : 1]` (`existsUnique_restrict_complexLocalOrientation`), the one-point characterization of [ℙ²]. With it `planeDegree α = ⟨Ψ α, μ⟩` unconditionally (`exists_planeDegree_eq_eval`) and ⟨Ψ [pt], μ⟩ = 1.
- Route: sheaf H³ = H⁴ = 0 of ℙ²(ℂ) ∖ pt, carried to singular homology of the open by `relH.forget_injective_of_eq_bot`, upstream's support-⊤ transport on the open, universal coefficients over ℚ and the empty-subspace iso; then the homology sequence of the pair. Only vanishing crosses each equivalence, so no sign or scalar enters.
- Reading μ as the complex-orientation [ℙ²] rests on row "Complex orientation of ℂ^p"; a real-parts-first ordering would flip μ and [pt] together and leave every statement true (red team, finding 5).
- Sign question at a = b = 1: unchanged in substance. Ψ [pt] = PD(pt) is now exact, but the line scalars still satisfy only c₀ · c₁ = 1; the coordinate swap would give c₀ = c₁ = ±1 and does not fix the sign (correction recorded in the ledger).
- Red team changes A to H implemented. E's second half waits: add `planeDegree_eq_eval_of_restrict` to the guard roots of `CycleClassSignTestP2.lean` when that file is next touched (recorded in its ledger note).
- Cost: about 9 s per module with `lake env lean`.
- Next: `p2-fundamental-class-every-point` (new, open, optional), or the evaluation of [L] on a fundamental class of a line, which is what separates c₀ from its sign.
