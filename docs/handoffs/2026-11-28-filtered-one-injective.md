# Handoff 2026-11-28: `filtered-one-injective`

- Checked: `HodgeLadder/Hodge/FilteredOneInjective.lean`, `HodgeLadder/General/TriangleShiftedHom.lean` (layer 0, Mathlib only) and `HodgeLadder/Tests/PointFunctionsSurjective.lean`, all imported from `HodgeLadder.lean`, eleven declarations in the ledger, standard axioms only. Sub-rung S2b of `docs/sketches/elliptic-curve-holomorphic-form.md`, statement as posted.
- General step (in `General.TriangleShiftedHom`, gaps row added): `Triangle.shifted_coyoneda_injective₁` (distinguished T, `n₀ + 1 = n₁`: if every `I → T₃[n₀]` factors through `T.mor₂`, then `β ≫ T.mor₁[n₁] = 0` forces `β = 0`), from `Functor.homologySequence_exact₁` and `comp_homologySequenceδ` for `preadditiveCoyoneda`.
- `filteredToDeRhamCohomology_one_one_injective`: that lemma on the triangle of `firstFiltrationShortComplex_shortExact` with `I = ℤ[0]`, `n₀ = 0`, `n₁ = 1`, moved across `SmallShiftedHom.equiv`.
- Corollary: `filteredOneOneEquivHodgeFiltration` (target `hodgeFiltration X 1 1`) and `filteredOneOneEquivHodgeFiltrationComplexSubmodule` (target `F^1 H_dR^1(X)`), by `AddMonoidHom.ofInjective`, each pinned to `filteredToDeRhamCohomology X 1 1` by `rfl`.
- Sign: none; only δ = 0 is used.
- Nonvacuity: `Tests.deRhamToHolomorphicFunctionCohomology_point_surjective` proves the hypothesis at Spec ℂ (Ω• → 𝒪[0] is an iso of complexes there), and the theorem applies (`Tests.filteredToDeRhamCohomology_point_injective`); the conclusion is degenerate at the point. Positive dimension waits on S2a `de-rham-functions-surjective-zero`.
- Red team: `docs/sketches/filtered-one-injective.redteam.md`, pass with changes; required changes 1 to 4 and O1 applied (conventions row "First-filtration triangle" added); O2 (one public copy of the hypercohomology helper in `FirstFiltration`) left for the next edit of that file.
- Timing: the module elaborates in about 9 s wall, imports included.
- Next: S2a, then S6 `curve-hodge-filtration-section` (needs S2a, S2b, S3).
