# Handoff 2026-11-27: `de-rham-unit-nonzero`

- Checked: `HodgeLadder/Tests/DeRhamUnitNonzero.lean`, imported from `HodgeLadder.lean`, ten declarations in the ledger. The rung's two statements are `fieldToHolomorphicDeRhamComplexInt ℚ point ≠ 0` and `rationalDeRhamUnit point ≠ 0`, at `point = Spec ℂ` (rung `nonvacuity-tests`).
- General forms: on every smooth integral `X` with a complex point and every field `K` with `Algebra K ℂ`, upstream's unit and `rationalDeRhamUnit X` are nonzero.
- Route: degree zero through `homFromSingleExtend_f_zero`; the sheaf map `K_X ⟶ ℂ_X ⟶ Ω⁰` is a sheafification, and on the stalk at a point Mathlib's `stalkFunctor_map_unit_toSheafify_isIso` keeps the germ of `[1]`; chart evaluation of `[1]` is `1`. The rational corollary cancels `forgetUnitComplexIso` in `forget_rationalDeRhamUnit`.
- Sign (red team change 4): `n • ι ≠ 0` for `n ≠ 0` by the same proof, so `ι ≠ −ι` and `rationalDeRhamUnit X ≠ −rationalDeRhamUnit X`. With it the unit lemma is false for the negated unit; a bare `≠ 0` did not give that.
- Kept local (decision 0011): `holomorphicFormOfConstant_ne_zero` reproves half of upstream's private `holomorphicFormOfConstant_injective`; row in `docs/gaps.md`.
- Instance: `(forgetComplex X).PreservesZeroMorphisms` and `.Additive` are not found by search; supplied as terms inside the proofs.
- New open rung: `complex-point-nonempty` (`Nonempty (ComplexPoint X)` from `IsIntegral` and `Smooth`, Nullstellensatz).
- Recorded for `wedge-sheaf-map` (ledger note): two routes to `wedgeSheaf X d 0 0 ≠ 0`.
- Red team: `docs/sketches/de-rham-unit-nonzero.redteam.md`, pass with changes, all implemented.
- Next: `wedge-sheafify`.
