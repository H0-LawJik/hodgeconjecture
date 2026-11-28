# Handoff 2026-11-28: `compact-holomorphic-locally-constant`

- Checked: `HodgeLadder/Hodge/CompactHolomorphic.lean` (general, layer 0) and `HodgeLadder/Tests/CompactHolomorphicP1.lean` (ℙ¹ tests, the ledger module), rung `compact-holomorphic-locally-constant`, issue #289, sub-rung S1 of `elliptic-curve-holomorphic-form`; 13 ledger declarations, standard axioms only.
- Statement: for X smooth of relative dimension d with X(ℂ) compact (`IsProjective` suffices, upstream's `complexPoint_compactSpace`), every section over ⊤ of upstream's `holomorphicFunctionSheaf X d` is locally constant (`isLocallyConstant_holomorphicFunctionSheaf_top`), constant when X(ℂ) is preconnected.
- Route: a global section is by definition a `C^ω⟮𝓘(ℂ, Fin d → ℂ), ⊤; ℂ⟯` map; Mathlib's `MDifferentiable.isLocallyConstant` on upstream's `isManifold_omega`, after `CompactSpace ↥⊤` (local helper, no Mathlib instance).
- For S2a: `holomorphicTopToLocallyConstant X d`, a ring map into `LocallyConstant ⊤ ℂ` with underlying function the section (`rfl`), injective. S2a's ledger note names the import and the red team's compiled O1 text (the lift through `constantSheafIsoLocallyConstantSheaf`).
- Tests: on ℙ¹, c ↦ the constant section is a bijection ℂ → Γ(ℙ¹(ℂ), 𝒪) (`projectiveLine_existsUnique_const`); a chart coordinate is a section with two values on a chart domain (`projectiveLine_exists_nonconstant_section`), so compactness is load-bearing.
- Red team: `docs/sketches/compact-holomorphic-locally-constant.redteam.md`, pass with changes; required changes 1 to 5 applied (split into a general and a test module, nonconstant-section test, ledger note, roadmap row, gaps row at layer 0). Optional O1 and O2 left out of this rung.
- Signs: none.
- Failed attempts: none; the first draft compiled as written.
- Timing: each file elaborates in about 3 s.
- Next: S2a `de-rham-functions-surjective-zero`, starting from O1 in a new leaf module.
