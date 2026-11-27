# 2026-11-27 de-rham-injective

- Checked: `HodgeLadder.fieldToDeRhamCohomology_rat_injective` and `ker_fieldToDeRhamCohomologyLinear_rat`, module `HodgeLadder.Hodge.DeRhamInjective`.
- Proof: the ℚ case of upstream's `fieldToDeRhamCohomology_injective` (library `Other`); upstream factors ι through constant-coefficient cohomology with ℂ, uses the holomorphic Poincaré lemma, and a ℚ-linear retraction ℂ → ℚ.
- Hypotheses: those of `fieldToDeRhamCohomology` only; no properness.
- Drift: the `Other` lemma above.
- Next: `de-rham-cup-test-p2` reads this when it shows `deRhamCup (ι [L₀]) (ι [L₁]) ≠ 0`.
