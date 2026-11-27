# Handoff 2026-11-27: `rational-de-rham-complex`

- Checked: `HodgeLadder.Hodge.RationalDeRhamComplex`, imported from `HodgeLadder.lean`, standard axioms. Ω•_ℚ sheafifies upstream's `HolomorphicForm X d U p` in `ModuleCat ℚ` (global instance `holomorphicFormRatModule`, unique by `subsingleton_rat_module`); its underlying presheaf is upstream's by `rfl`.
- Comparison: `forgetRationalDeRhamIso : (forgetComplex X).obj (rationalDeRhamComplex X) ≅ Ω•(X)` from Mathlib's `sheafComposeNatIso`, pinned against the two sheafification maps (`toSheafify_comp_forgetRationalHolomorphicFormSheafIso`, red team change 2), which excludes a twist by an automorphism such as −1.
- Unit: `forget_rationalDeRhamUnit` through exactly `forgetUnitComplexIso` (change 8 of the `rational-hypercohomology-equiv` red team), exact, no scalar. Truncations: `forget_rationalHodgeFilteredInclusion` lies over `hodgeFilteredDeRhamInclusion X p`; `hodgeFiltration_eq_range_rational` gives F^p H_dR^n as the range of the rational truncation.
- Red team (`docs/sketches/rational-de-rham-complex.redteam.md`): pass with changes; changes 1 to 6 implemented, the `extendSingleIso` agreement of change 7 added, change 8 posted as the open test rung `de-rham-unit-nonzero`.
- Generic layer kept local (decision 0011): `homFromSingleExtend` and its lemmas, `mapStupidTruncIso`; recorded in `docs/gaps.md` with the drift check for the `Module ℚ` instance.
- Proof technique: the site and analytic spellings of the sheaf category do not cross under `rw` or `simp`; the proofs join generic lemmas by `Eq.trans` and `exact`.
- Next: `wedge-sheafify`, whose ledger note now lists what it takes from here (the ℚ-bilinear wedge by `restrictScalars₁₂ ℚ ℚ`, `rationalHolomorphicFormPresheaf`, the change-2 pin).
