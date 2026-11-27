# Handoff 2026-11-26: `cycle-class-multiplicative`

- Checked: `HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal`, [Z] ∪ [W] = [T] in H^{2(a+b)}(X; ℚ) for upstream's cycle classes and the Yoneda cup, exact, sign +. The statement is the one elaborated in the sketch, unchanged. Module `HodgeLadder/Cycle/Multiplicative.lean`, 20 declarations, standard axioms.
- The front's kill criterion did not fire. The sign chain is (−1)^{(2a)(2b)} = 1 from `cup_singular_comparison'` (computed by `Even.neg_one_pow`) times the local + of `chartNormalProjectionCoclass_eq_relCup2`. Every other map is an identity or inclusion of points.
- Route: γ comes from surjectivity of Φ_T applied to the `unionComplIso` pullback of `relCup2 (Φ_Z [Z]) (Φ_W [W])`.
  - `cup_forgetSupport_of_product` handles the global side, with sign (−1)^{pq} for any p, q.
  - `germ_transport_eq_of_chart` handles each y ∈ T(ℂ): `cycle-class-germ` on three charts split from φ by the ℂ-linear `normalSplit`.
  - `TopCat.Presheaf.section_ext` on U_T and upstream's `cycleComponentSupportedInjectiveClass_unique` give γ = [T]_supp.
- Checked with it: `cycle-class-multiplicative-p2` (`HodgeLadder/Tests/CycleClassMultiplicativeP2.lean`): [L₀] ∪ [L₁] = [pt] on ℙ², by `exact` from `p2-lines-transversal`; ht is `coheight_planeOrigin_add`.
- Traps:
  - `(supportedEquivPair X T n).symm` inside a `def` hit maximum recursion in `apply_symm_apply`. The route uses surjectivity instead.
  - `rw` across coercions of upstream `AddEquiv`s (Φ, Ψ, including `map_zsmul`) timed out. Use `congrArg`, `Eq.trans`, `convert … using 2`.
  - `set` on cycle-component supports timed out. So did an inline `sZ ▸ hy` inside a big application. Name them with `have` first.
- Cost: the module takes about 97 s to build, mostly kernel time, 9 to 18 s per declaration whose statement applies `supportedEquivPair`. Consumers that avoid it (the ℙ² instance) take about 3 s.
- Red team: final statement and proof pass with changes A to G (`docs/sketches/cycle-class-multiplicative.final.redteam.md`), all implemented. Two rungs were dropped from `depends_on` (not in the import closure): `supported-open-naturality`, `supported-model-agreement-open`.
- New open rungs: `cycle-class-multiplicative-no-reg` (without `hxreg`, `hwreg`) and `cycle-class-multiplicative-generic` (transversality at the generic point of T). Several components is recorded in the sketch only.
- Next, the sign-visible tests: `cycle-class-multiplicative-codim-zero`, `p2-point-class-nonzero`, `cup-positive-degree-test-p2`.
