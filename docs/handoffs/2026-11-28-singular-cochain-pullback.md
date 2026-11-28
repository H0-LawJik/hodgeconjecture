# Handoff 2026-11-28: `singular-cochain-pullback`

- Checked: `HodgeLadder/Supported/SingularCochainPullback.lean` (layer 17, through `HodgeLadder.Cup.EndClass` for `iotaQ`), imported from `HodgeLadder.lean`, 19 declarations in the ledger, standard axioms only. Sub-rung R1 of `supported-pullback-transport`.
- Map: `singularPullbackSheaf f n` is the transpose under `pullbackPushforwardAdjunction` of upstream's `singularRestrictionSheaf ℚ f n`, which takes any continuous map; `unit_comp_singularPullbackSheaf` states the defining property.
- Identities, all exact with no sign and no scalar: `singularPullbackSheaf_comm` (coboundary), `constants_comp_singularPullbackSheaf` (constants through the port's `pullbackConstantSheafIso`, the iso `supportedPullback` uses), `iotaQ_comp_singularPullbackInt` (the same square in ℤ-degrees, through the general `HodgeLadder.extendMap_single_square`).
- Tests: `constants_comp_singularPullbackSheaf_ne_zero` and `singularPullbackSheaf_zero_ne_zero` on nonempty `Y`.
- Instances: `(pullbackAb (pointMap g)).Additive` and the finite (co)limit facts are missed by instance search; use the named local instances `pointPullbackAdditive`, `pointPullbackPreservesFiniteLimits`, `pointPullbackPreservesFiniteColimits` with `attribute [local instance]`.
- Transparency: `backward.isDefEq.respectTransparency false` on five declarations, each needed (`TopCat.Sheaf` against `AbSheaf` spelling).
- Timing: about 50 s wall; `iotaQ_comp_singularPullbackInt` alone takes about 37 s of kernel time (gaps "Known weaknesses"); unfolding `iotaQ` first did not help.
- Red team: `docs/sketches/singular-cochain-pullback.redteam.md`, pass with changes; changes 1 to 8 and O1, O2 applied, O3 (split the `General` section to layer 2) skipped.
- Next: `supported-pullback-named` (R3), using `mapExactFunctor_hom_named`; the red team's scratch composite (finding 3) needs `erw` across the `pairSheaf'` spelling.
