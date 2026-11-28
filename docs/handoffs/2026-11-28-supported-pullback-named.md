# Handoff 2026-11-28: `supported-pullback-named`

- Checked: `HodgeLadder/Supported/PullbackNamed.lean` (layer 22), imported from `HodgeLadder.lean`, seven declarations in the ledger, standard axioms only. Sub-rung R3 of `supported-pullback-transport`, issue #261; statement as posted in the sketch.
- Result: `supportedPullback_named`, if z names α (through `iotaQ X`, in the form `exists_supported_rep` produces), then `pullbackCocycle g Z Z' hZ z` names `supportedPullback g Z Z' hZ n α` (through `iotaQ X'`). Exact, no sign, no scalar.
- Proof: `mapExactFunctor_hom_named` along `pullbackAb (pointMap g)`, then `comp_mk₀_named` with the constants square `iotaQ_square` (a reassociation of `iotaQ_comp_singularPullbackInt`), then `mk₀_comp_named` at `supportPairMap`, then `precomp_postcomp_precomp`.
- General lemmas: `mk₀_comp_named`, `comp_mk₀_named`, `precomp_postcomp_precomp` moved into `HodgeLadder/General/ExtMapCocycle.lean` (red team change 2; that module had one downstream module); its gaps row now covers them.
- Tests: `exists_named_supportedPullback` (hypothesis satisfiable on integral smooth X) and `HodgeLadder.Tests.pullbackCocycle_prodFst_ne_zero` (on pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹ a pulled-back cocycle has nonzero derived class in degree 0), listed under `supported-class-pullback-test`.
- Instances: `SupportedFinal`'s `finHasDerivedCategory`, `finSiteHasDerivedCategory` (in that order), the same terms as `exists_supported_rep`; the three named `pointPullback*` instances of R1.
- Transparency: `respectTransparency false` on `iotaQ_square` only (tested: `rw [assoc]` fails without it). A term-mode `let ⟨…⟩` in the corollary hit a `whnf` heartbeat timeout; `obtain` works.
- Timing: see the module docstring; the file is well under the 600 s split threshold.
- Red team: `docs/sketches/supported-pullback-named.redteam.md`, pass with changes; changes 1 to 5 and R1 applied, R2 is R5's.
- Next: `supported-pullback-section` (R4), evaluating `pullbackCocycle` on `supCocycle`; then `supported-pullback-transport` (R6), whose X' side composes this rung with R5's `supportedEquivPair_of_named`.
