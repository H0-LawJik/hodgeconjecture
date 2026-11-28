# Handoff 2026-11-28: `torus-singular-cohomology`

- Checked: `HodgeLadder/Torus/Singular/Cohomology.lean` (layer 14) and the new leaf `HodgeLadder/Cup/SingularCupLinear.lean` (layer 12, through `HodgeLadder.Cup.RelCupNaturality`), both imported from `HodgeLadder.lean`, 26 declarations in the ledger, standard axioms only. Node C6 of `docs/notes/2026-11-27-t1-plan.md`.
- Results on Tⁿ = `UnitAddTorus (Fin n)`: for n ≥ 2 the winding classes aᵢ are a basis of H¹ (`linearIndependent_coordWinding`, `span_coordWinding`, `coordWindingBasis`), dim n; for every n the cups aᵢ ⌣ aⱼ with i < j are a basis of H² (`span_coordCup`, `coordCupBasis`), dim n.choose 2. Tests at n = 2, 4 (values 2, 1, 4, 6) and a₀ ≠ a₁ on T².
- Route: upper bound dim H^k = dim H_k ≤ n.choose k through upstream's `cohomologyEquivDualHomology` and `torus-homology-bound`; lower bound from `torusEval` on coordinate tori; card plus independence gives the span. No Künneth.
- H¹ independence: cup a relation on the right with a_m, m ≠ k, evaluate on T_km; n ≥ 2 enters only there. n = 1 closes after `winding-class-pullback` by pulling back along T² → T¹.
- New in the cup layer: `cupSingBilin` (apply by `rfl`), additivity and homogeneity in both slots, `cupSingRight`, and naturality `cupSing_cohomologyMap` (exact, no sign; the square `cohIso_cohomologyMap` as a separate lemma, then Tau Ceti's `singularCup_naturality`). `SingularCup` stays untouched (frozen hub).
- Signs: none enters a conclusion; aⱼ ⌣ aᵢ = −aᵢ ⌣ aⱼ, so coefficients in `coordCupBasis` name the order i < j (conventions row "Coordinate tori of Tⁿ"); new conventions row "Universal coefficients over a field".
- Timing: each module elaborates in about 5 s.
- Red team: `docs/sketches/torus-singular-cohomology.redteam.md`, pass with changes; changes 1 to 5 applied, O1, O3 and the finding-8 naturality lemma added, O2 and O4 skipped. The leaf sits at layer 12, two above the verdict's estimate, because the naturality lemma imports `RelCupNaturality`.
- Next: `winding-class-pullback` (`windingClass_comp`, then transport of `coordWindingBasis` and `coordCupBasis` along `cohomologyMap ℚ k h` for h : Y ≃ₜ Tⁿ).
