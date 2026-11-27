# Handoff 2026-11-26: `tensor-bounded-quasi-iso`

- Checked: `HodgeLadder.tensorBoundedQuasiIso_holds : TensorBoundedQuasiIso`, the `Prop` stated in `HodgeLadder/Hodge/CupFiltration.lean`, left unchanged. The proof is in the new module `HodgeLadder/Hodge/TensorBoundedQuasiIso.lean`.
- General form `quasiIso_mapBifunctorMap_of_bounded`: for `F : C₁ ⥤ C₂ ⥤ D` between abelian categories, additive in each variable, with each `F(−, X)` preserving homology and coproducts in `D`, `F(f, 𝟙_M)` is a quasi-isomorphism for every quasi-isomorphism `f` and every strictly bounded `M`. For sheaves, `F = curriedTensor (ShQ Y)` and `F(−, X) = − ⊗ X` is exact by `tensor_exact`.
- Route, as in red-team finding 7 (no stalks):
  - Single case: `singleComparison` is an explicit isomorphism `F(K, X)⟦−a⟧ ≅ mapBifunctor K (X[−a]) F`, natural in `K`, with sign `(−1)^{na}` in degree `n`.
  - Step: induction on the length of `M` via the degreewise split sequence `0 → ker → M → M^a[−a] → 0` (`bottomSES`). This sequence stays degreewise split after `mapBifunctor K − F` (`mapBifunctorShortComplex_shortExact`).
  - Two out of three for the middle term (`quasiIso_τ₂_of_shortExact`): Mathlib has only the third-term case.
- Instances: `HasCoproducts.{0} (ShQ Y)` is given as an explicit term, `Sheaf.instHasColimitsOfShape` with `inferInstance` arguments. Plain `inferInstance` on `HasColimitsOfShape (Discrete J) (ShQ Y)` ran for over two minutes. The `HasTensor` hypotheses of the statement enter only through proof irrelevance.
- Build time of the module is about 20 seconds. Axioms: standard three.
- General lemmas listed in `docs/gaps.md`, "General lemmas kept local".
- Next: `derived-tensor-bounded` (`Localization.lift` of `− ⊗ B` along `Q`, additivity through the homotopy category, red-team finding 6).
