# Handoff 2026-11-27: `wedge-sheafify`

- Checked: `HodgeLadder/Hodge/WedgeSheafify.lean`, imported from `HodgeLadder.lean`, 24 declarations in the ledger, standard axioms only.
- Statement: `wedgeSheaf X d p q : Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ := μ ≫ sheafifyQ.map rationalWedgePresheaf`, the presheaf wedge being `TensorProduct.lift` of `(holomorphicWedge X d U p q).restrictScalars₁₂ ℚ ℚ`. Defining square against `toSheafifyTensor P Q := toSheafify (P ⊗ Q) ≫ δ`, uniqueness `eq_wedgeSheaf_iff`, and `forget_wedgeSheaf`, which reaches upstream's sheafification map of `holomorphicDeRhamPresheaf X d (p + q)` through `toSheafify_comp_forgetRationalHolomorphicFormSheafIso`. Exact, no sign, no scalar.
- Scale pin (red team change 5): `wedgeSheaf_unit_left`, `(u₀ ▷ Ω^q_ℚ) ≫ wedgeSheaf 0 q ≫ eqToHom = λ`, with `sheafifyQ_ε : ε = 𝟙 := rfl` so a Mathlib bump that changes the unit breaks loudly.
- Nonvacuity: `wedgeSheaf_ne_zero` on every X with a complex point, from the unit law and `Tests.rationalDeRhamUnit_ne_zero` (14 lines).
- Instance: `Cup.sheafMonoidal` is not applied at `TopCat.of (ComplexPoint X)` (discrimination-tree key `Opens _.1` against the reduced concrete spelling); workaround `analyticShQMonoidal X` as a local instance. Recorded in `docs/gaps.md`.
- Spelling: `rw` does not cross `rationalHolomorphicFormSheaf X d p` and `sheafifyQ.obj P_p`; sheaf-level proofs go by `Eq.trans` with the generic lemmas (Leibniz shape: five steps, recorded in the `wedge-sheaf-map` note).
- Timing: the module checks in about 10 s; `lake build` of it 7 s.
- Red team: `docs/sketches/wedge-sheafify.redteam.md`, pass with changes, all implemented (changes 1 to 7 as asked; change 8 lands here since `de-rham-unit-nonzero` had merged).
- Next: `wedge-sheaf-map` (chain-map check and complex unit law), then `de-rham-cup`, which owes `S_c := sheafifyQ.map (c • ·)` and its tie to `scalarHolomorphicDeRhamComplexInt`.
