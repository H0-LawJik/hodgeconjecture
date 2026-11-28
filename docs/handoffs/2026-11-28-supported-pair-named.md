# Handoff 2026-11-28: `supported-pair-named`

- Checked: `HodgeLadder/Supported/PairNamed.lean`, imported from `HodgeLadder.lean`, four declarations in the ledger, standard axioms only. Sub-rung R5 of `supported-pullback-transport` (issue #260).
- Main result: `supportedEquivPair_of_named`. If β ∈ H_[Z]^p(X; ℚ) is named through `iotaQ X` by `supCocycle (rawMap y)`, then `supportedEquivPair X Z p β` is the relative class of `y` under upstream's `relativeDualCochainCohomologyEquiv` and `topPairIso`. Exact, no sign, no scalar; the statement is the sketch's R5 verbatim.
- Proof: the second half of `exists_supported_rep` (`relHSupportedOfFlasque_mk`, the `e.inv_hom_id` round trip, `homologyMap_cls`), then `supported_singular_class` and `pairCohIso_hom_apply`.
- Sign: `shortExactHomologyIsoCone` enters twice inside `supported_singular_class` and cancels; R5's statement contains no cone, so R6's common ε(n) is 1.
- Tests: `exists_named` (the hypothesis holds for some β, for every relative cocycle y), `exists_supportedEquivPair_eq`, `exists_named_ne_zero` (every nonzero β gives an instance with both sides nonzero).
- Instances: R3's `HodgeLadder.Cup.finHasDerivedCategory`, `finSiteHasDerivedCategory` through `attribute [local instance]`, so R6 meets one spelling.
- Timing: about 100 s wall, 76 s kernel (main theorem 31 s, `maxHeartbeats 1000000`); row in gaps "Known weaknesses".
- Red team: `docs/sketches/supported-pair-named.redteam.md`, pass with changes; changes A to G applied.
- Next: `supported-pullback-transport` (R6) once R3 and R4 land: R5 on X with `exists_supported_rep`, on X' with R3 and R4, then upstream's `relativeDualCochainCohomologyEquiv_naturality`.
