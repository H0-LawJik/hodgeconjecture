# Red team: `filtered-one-injective`

Date: 2026-11-28. Candidate: commit `6a97ba8` on `track/filtered-one-injective` (base `a509ee0`, equal to `main`), file `HodgeLadder/Hodge/FilteredOneInjective.lean` (module `HodgeLadder.Hodge.FilteredOneInjective`, six declarations), root-imported; ledger entry set `checked`. Issue #290, sub-rung S2b of `docs/sketches/elliptic-curve-holomorphic-form.md`.

Read: `python3 tools/next.py filtered-one-injective` and `curve-hodge-filtration-section` (S6, the consumer); the sketch's sub-rung table and "Signs and normalizations"; `HodgeLadder/Hodge/FirstFiltration.lean`; upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (`Hypercohomology`, `hypercohomologyAddCommGroup`, `hypercohomologyMap`, `hodgeFilteredDeRhamInclusion`, `filteredToDeRhamCohomology`, `hodgeFiltration`, `hodgeFiltrationComplexSubmodule`) and `HolomorphicDeRham.lean` (`holomorphicDeRhamSheaf_isZero_of_lt`, `holomorphicDeRhamComplexInt_isZero_X_of_lt`); the port's `HolomorphicHodgeProjection.lean` (`holomorphicDeRhamToFunctionsComplexInt`, `deRhamToHolomorphicFunctionCohomology`); Mathlib `CategoryTheory/Triangulated/{HomologicalFunctor,Pretriangulated,Yoneda}.lean`, `Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean`; `HodgeLadder/Hodge/RationalHypercohomology.lean` (`equiv_hypercohomologyMap`); `docs/gaps.md`, `docs/conventions.md`, `docs/references.md`.

Scratch: `scratch-rt-foi/` in the worktree (`Probe.lean`, `General.lean`), each run with `lake env lean` against the built `.olean`; deleted after the pass. Every Lean claim marked "scratch" below elaborated there with no error.

**Verdict: pass with changes.** The six declarations say what the rung claims, with the three standard axioms. The theorem's maps are upstream's `filteredToDeRhamCohomology X 1 1` and the port's `deRhamToHolomorphicFunctionCohomology X 0` with no intermediate identification, the triangle is Mathlib's `triangleOfSES` of the checked short exact sequence, and the general lemma has the right indices. The hypothesis holds at `Spec ℂ` (scratch, 30 lines), so the theorem has an instance at the pin today. The changes are bookkeeping: placement of the general lemma, a gaps row, a conventions row, and the nonvacuity text.

## Findings

1. **Fidelity.** Literature ([Voisin2002], degeneration of the Hodge-to-de Rham spectral sequence; F¹H¹ = H⁰(Ω¹) for compact curves; locators unverified): on a compact complex manifold the long exact sequence of 0 → F¹Ω• → Ω• → 𝒪 → 0 reads H⁰(X, Ω•) → H⁰(X, 𝒪) → ℍ¹(F¹Ω•) → H¹(X, Ω•), and since H⁰(X, 𝒪) consists of locally constant functions, the first map is onto and the third is injective. The Lean theorem isolates the formal step and keeps the analytic input as a hypothesis.

   | Field | Literature | Lean | Match |
   |---|---|---|---|
   | space | compact complex manifold | any `X : Over (Spec ↧ℂ)` with `[IsIntegral X.left] [Smooth X.hom]`; compactness enters only through the hypothesis | yes (more general) |
   | F¹Ω• | stupid truncation σ≥1 | upstream `hodgeFilteredDeRhamComplex X 1 = Ω•(X).stupidTrunc (embeddingUpIntGE 1)` | yes |
   | 𝒪 term | 𝒪 in degree 0 | `holomorphicFunctionComplexInt X (dim X.left)`, the single complex on upstream's holomorphic-function sheaf | yes |
   | hypothesis | H⁰(Ω•) → H⁰(𝒪) onto | `Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0)`, the port's `hypercohomologyMap X (holomorphicDeRhamToFunctionsComplexInt X) 0` | yes |
   | conclusion | ℍ¹(F¹Ω•) → H¹_dR injective | `Function.Injective (filteredToDeRhamCohomology X 1 1)`, upstream's `hypercohomologyMap X (hodgeFilteredDeRhamInclusion X 1) 1` | yes |
   | statement as posted | sketch row S2b: `(Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0)) → Function.Injective (filteredToDeRhamCohomology X 1 1)` | the same | yes |

   Without the hypothesis the conclusion is false in the literature: on 𝔸¹, F¹Ω• = Ω¹[−1], ℍ¹(F¹Ω•) = Γ(ℂ, Ω¹) ≠ 0 and H¹_dR(ℂ) = 0. The hypothesis is load-bearing; this is a recalled computation, unchecked in Lean.

2. **The general lemma: indices.** `Triangle.shifted_coyoneda_injective₁` takes surjectivity of postcomposition with `T.mor₂` in degree `n₀` and concludes that `β : ShiftedHom I T.obj₁ n₁`, `n₀ + 1 = n₁`, with `β ≫ T.mor₁[n₁] = 0` vanishes. The connecting map of `Functor.homologySequence_exact₁` runs `(F.shift n₀).obj T.obj₃ → (F.shift n₁).obj T.obj₁` (Mathlib, `HomologicalFunctor.lean:228`), so the surjective map sits one degree below the injective one, as stated. In the instance `n₀ = 0`, `n₁ = 1`, `I = ℤ[0]`. The proof uses `comp_homologySequenceδ` (`HomologicalFunctor.lean:192`) for δ ∘ mor₂ = 0, a vanishing statement. The lemma elaborates with Mathlib-only imports (`Triangulated.HomologicalFunctor`, `Triangulated.Yoneda`, `Shift.ShiftedHom`; scratch `General.lean`, standard axioms), so its import layer can be 0.

3. **Mathlib equivalents.** Mathlib's `Triangle.coyoneda_exact₁` (`Pretriangulated.lean:265`) is the unshifted form for `f : X ⟶ T.obj₁⟦1⟧` with a factorization conclusion; `Abelian.Ext.covariant_sequence_exact₁` (`Ext/ExactSequences.lean:157`) is the `ℕ`-graded `Ext` form under `HasExt`. Neither is stated for `ShiftedHom` in an arbitrary `ℤ` degree, which is how upstream's `Hypercohomology` is read through `SmallShiftedHom.equiv`. A local lemma is justified (decision 0011), alongside its sibling `Triangle.shifted_coyoneda_exact₂` in `FirstFiltration.lean`. Neither has a row in `docs/gaps.md`, so a pin walk would skip both (change 2).

4. **The instance: maps and identifications.** The proof's `change` steps elaborate `(triangleOfSES hS).mor₁` to `DerivedCategory.Q.map (hodgeFilteredDeRhamInclusion X 1)` and `mor₂` to `DerivedCategory.Q.map (holomorphicDeRhamToFunctionsComplexInt X)` definitionally; `firstFiltrationShortComplex` is `ShortComplex.mk` of exactly these two maps, the ones `filteredToDeRhamCohomology X 1 1` and `deRhamToHolomorphicFunctionCohomology X 0` postcompose with. The transfer `E = SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q` is a bijection and is the map that defines upstream's group structure (`hypercohomologyAddCommGroup`), with `hypercohomologyEquiv_zero` for zero; no other iso enters. The file's `local instance` `HasDerivedCategory.standard` is used only inside proofs: `Function.Injective` of a coercion does not depend on a group structure, and the corollaries' `≃+` types use upstream's `hypercohomologyAddCommGroup`, a fixed definition. Same pattern as `FirstFiltration.lean`.

5. **Nonvacuity: the hypothesis holds at `Spec ℂ`.** In scratch, at `HodgeLadder.Tests.point`: `SmoothOfRelativeDimension 0 point.hom` by `infer_instance`; `TopologicalSpace.dim point.left = 0` by upstream's `SmoothOfRelativeDimension.dim_eq`; `IsIso (holomorphicDeRhamToFunctionsComplexInt point)` by components (degree 0 is `isIso_holomorphicDeRhamToFunctionsComplexInt_f_zero`; degrees `j < 0` by `IsStrictlyGE`, `j > 0` by upstream's `holomorphicDeRhamComplexInt_isZero_X_of_lt`, target `isZero_single_obj_X`); then `Function.Surjective (deRhamToHolomorphicFunctionCohomology point 0)` from `hypercohomologyMap_comp_apply`, `IsIso.inv_hom_id`, `hypercohomologyMap_id`, and `filteredToDeRhamCohomology_one_one_injective point` applies. `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`. At the point the conclusion is degenerate (F¹Ω• is zero in every degree), so this instance shows the hypothesis consistent and the theorem applicable; content in positive dimension comes through S2a, S3 and S6 on `Tests.ellipticCurve`. The scratch file is reproduced under "Optional changes" as O1.

6. **Triviality attempts.** The conclusion has no unconditional proof at the pin to find: its truth for all smooth integral X would contradict the 𝔸¹ computation of finding 1, provided upstream's de Rham objects are faithful there. No definition in the statement unfolds to `True`, no `ℕ∞` coercion occurs, and the index types are `ℤ` degrees `0` and `1`. The hypothesis is used (it supplies `α` with `E α ≫ mor₂ = γ`).

7. **Corollaries.** `filteredOneOneEquivHodgeFiltration` is `AddMonoidHom.ofInjective`, whose target is `(filteredToDeRhamCohomology X 1 1).range`, which is `hodgeFiltration X 1 1` by definition; `_apply` is `rfl`. `filteredOneOneEquivHodgeFiltrationComplexSubmodule` retypes it to `F^1 H_dR^1(X)`, whose carrier is `hodgeFiltration X 1 1`; `_apply` is `rfl`. Both are honest equivalences onto the range, the exact identification ℍ¹(F¹Ω•) ≅ F¹H¹_dR with no scalar. Upstream gives `Module ℂ` to `H_dR^n(X)` only (`Filtration.lean:671`), so an additive equivalence is the form available; a ℂ-linear one would need a `Module ℂ` on `FilteredDeRhamHypercohomology`, which upstream lacks.

8. **The private helper.** `equiv_hypercohomologyMap'` copies `FirstFiltration`'s private `equiv_hypercohomologyMap` (nine lines). `RationalHypercohomology.lean:470` has a public `HodgeLadder.equiv_hypercohomologyMap` with the same content in the form `x ≫ (Q.map g)⟦n⟧'`, but importing it pulls in `Cup.ExtBridge` and a module of about 758 s, and its form differs. Making `FirstFiltration`'s copy public under its present name would clash with that declaration in any module importing both; it would need a new name. `FirstFiltration` has 14 downstream modules (`tools/pinwalk.py --hubs`, below the frozen threshold of 78). The copy is acceptable for this rung; O2 records the cleanup.

9. **Placement.** The general lemma names no Hodge object and compiles at layer 0 (finding 2). The #212 layout and the red teams of `weil-eigen-algebra` (item 9) and `elliptic-curve-points` (item 6) keep such lemmas under `HodgeLadder/General/` with a gaps row. In `Hodge/FilteredOneInjective.lean` it sits at layer 6. Change 1 moves it; the ledger `declarations` list is unchanged because the name stays.

10. **Equality first (decision 0004).** The theorem is an injectivity statement, a step. Its corollary is the exact identification ℍ¹(F¹Ω•) ≃+ F¹H¹_dR(X), pinned by `rfl` to upstream's map. The equality it serves is F¹H¹_dR(X) ≅ Γ(X, Ω¹) on a compact curve ([Voisin2002], unverified locator); S3 `curve-one-form-class` (open) supplies the injection Γ(Ω¹) → ℍ¹(F¹Ω•), and no rung yet states surjectivity of that map, so the full equality has no rung. S6 needs only F¹H¹ ≠ ⊥, which injectivity gives.

11. **Conventions.** The rung uses one convention: the connecting map of the triangle of `firstFiltrationShortComplex_shortExact` (Mathlib's `triangleOfSES` with its `mor₃` and `homologySequenceδ`). Only δ ∘ mor₂ = 0 and the exactness of δ against mor₁ are used, both unchanged by δ ↦ −δ or by any unit multiple. The identification through `SmallShiftedHom.equiv` is a bijection with no scalar. `docs/conventions.md` has no row for this triangle; S3 works in the same triangle and may name δ or a shift-of-`single` iso, so change 3 adds the row now. No cited result is assumed.

12. **Checker.** `python3 tools/check.py --no-build` ends `ACCEPTED: all checks passed`; the six ledger declarations each print `[Classical.choice, Quot.sound, propext]`: `CategoryTheory.Pretriangulated.Triangle.shifted_coyoneda_injective₁`, `HodgeLadder.filteredToDeRhamCohomology_one_one_injective`, `HodgeLadder.filteredOneOneEquivHodgeFiltration`, `HodgeLadder.filteredOneOneEquivHodgeFiltration_apply`, `HodgeLadder.filteredOneOneEquivHodgeFiltrationComplexSubmodule`, `HodgeLadder.filteredOneOneEquivHodgeFiltrationComplexSubmodule_apply`. Each is the declaration the ledger means.

13. **Pin drift.** Checked at upstream `2ead713179628a3c738197d5996f51c8a9c886ac`, the current pin; the branch base equals `main`. No drift to diff.

14. **Signs.** None load-bearing (finding 11).

## Required changes

1. **Move the general lemma.** Create `HodgeLadder/General/TriangleShiftedHom.lean` holding `CategoryTheory.Pretriangulated.Triangle.shifted_coyoneda_injective₁` with its docstring unchanged, header `module`, imports `public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor`, `public import Mathlib.CategoryTheory.Triangulated.Yoneda`, `public import Mathlib.CategoryTheory.Shift.ShiftedHom`, `@[expose] public section`, and a module docstring with "Main results" naming the lemma (this layout elaborated in scratch). Delete the section from `FilteredOneInjective.lean`, add `public import HodgeLadder.General.TriangleShiftedHom` there and in `HodgeLadder.lean`, and in the module docstring of `FilteredOneInjective.lean` replace the first "Main results" bullet by: "* the general step is `CategoryTheory.Pretriangulated.Triangle.shifted_coyoneda_injective₁` in `HodgeLadder.General.TriangleShiftedHom`." Leave `shifted_coyoneda_exact₂` where it is (moving it rebuilds 14 modules; see O2).

2. **Gaps row.** In `docs/gaps.md`, "Homological algebra and derived categories", insert after the row for `HodgeLadder.General.Ext`:

   `| `CategoryTheory.Pretriangulated.Triangle.shifted_coyoneda_injective₁` (in a distinguished triangle, if postcomposition with `T.mor₂` is onto on `ShiftedHom I _ n₀`, then postcomposition with `T.mor₁` is injective on `ShiftedHom I _ (n₀ + 1)`), `Triangle.shifted_coyoneda_exact₂` (exactness at `T.obj₂` in any shifted degree) | `HodgeLadder.General.TriangleShiftedHom`, `HodgeLadder.Hodge.FirstFiltration` | 0, 5 | Mathlib has `Triangle.coyoneda_exact₁`, `coyoneda_exact₂` for unshifted morphisms and `Abelian.Ext.covariant_sequence_exact₁`, `exact₂` for `ℕ`-graded `Ext`; neither for `ShiftedHom` in a `ℤ` degree, the form of upstream's `Hypercohomology` under `SmallShiftedHom.equiv` | 2026-11-28 |`

3. **Conventions row.** In `docs/conventions.md`, insert after the row "Hodge filtration":

   `| First-filtration triangle | this repository, `HodgeLadder.firstFiltrationShortComplex`, `firstFiltrationShortComplex_shortExact` (`HodgeLadder/Hodge/FirstFiltration.lean`, rung `chern-classes-are-hodge`); Mathlib `DerivedCategory.triangleOfSES`, `Functor.homologySequenceδ` | the triangle of 0 → F¹Ω• → Ω• → 𝒪[0] → 0 has `mor₁ = Q.map (hodgeFilteredDeRhamInclusion X 1)` and `mor₂ = Q.map (holomorphicDeRhamToFunctionsComplexInt X)` by definition, the maps of upstream's `filteredToDeRhamCohomology X 1 n` and the port's `deRhamToHolomorphicFunctionCohomology X n`; `mor₃` and δ are Mathlib's, sign unread | none for `mem_hodgeFiltration_one_iff` and `filtered-one-injective`: they use exactness and δ ∘ mor₂ = 0, unchanged by δ ↦ −δ. A rung that states an identity through δ or computes ℍ¹(F¹Ω•) through it (possibly S3 `curve-one-form-class`) depends on the sign and must extend this row | read from source; the identification of `mor₁`, `mor₂` checked by `change` in `HodgeLadder/Hodge/FilteredOneInjective.lean` (red team 2026-11-28, `docs/sketches/filtered-one-injective.redteam.md`) |`

4. **Nonvacuity text.** In `ledger/ladder.json`, rung `filtered-one-injective`, replace the sentence "Nonvacuity: the hypothesis is supplied on compact X(ℂ) by S2a de-rham-functions-surjective-zero (open); no instance is proved here." by: "Nonvacuity: the hypothesis holds at Spec ℂ, where Ω• → 𝒪[0] is an isomorphism of complexes (Ω^p = 0 for p > dim = 0); there the conclusion is degenerate, F¹Ω• being zero (red team scratch, docs/sketches/filtered-one-injective.redteam.md finding 5). In positive dimension S2a de-rham-functions-surjective-zero (open) supplies it on compact X(ℂ). Red team: pass with changes." In the module docstring of `FilteredOneInjective.lean`, replace "The hypothesis is satisfiable: sub-rung S2a of `elliptic-curve-holomorphic-form` (`de-rham-functions-surjective-zero`) is planned to supply it on every compact `X(ℂ)`." by: "The hypothesis holds at `Spec ℂ`, where `Ω^•` is `𝒪` in degree zero, and there the conclusion is degenerate. On a compact `X(ℂ)` of positive dimension, sub-rung S2a of `elliptic-curve-holomorphic-form` (`de-rham-functions-surjective-zero`, open) is to supply it." If O1 is taken, cite `HodgeLadder.Tests.deRhamToHolomorphicFunctionCohomology_point_surjective` in both places in place of the scratch reference.

## Optional changes

O1. **Commit the point instance as a test.** `HodgeLadder/Tests/PointFunctionsSurjective.lean`, importing `HodgeLadder.Hodge.FilteredOneInjective` and `HodgeLadder.Tests.Witness`, with the scratch body below (namespace `HodgeLadder.Tests`, the instance named `smoothOfRelativeDimension_point`, the theorems renamed `dim_point`, `isIso_holomorphicDeRhamToFunctionsComplexInt_point`, `deRhamToHolomorphicFunctionCohomology_point_surjective`, `filteredToDeRhamCohomology_point_injective`), docstrings added, ledger declarations appended. Elaborates in about 6 s with the imports built.

```lean
instance : SmoothOfRelativeDimension 0 point.hom := by dsimp [point]; infer_instance

theorem dim_point : TopologicalSpace.dim point.left = 0 :=
  SmoothOfRelativeDimension.dim_eq (f := point.hom) 0

theorem isIso_toFunctions_point : IsIso (holomorphicDeRhamToFunctionsComplexInt point) := by
  have hc : ∀ j, IsIso ((holomorphicDeRhamToFunctionsComplexInt point).f j) := by
    intro j
    by_cases hj : j = 0
    · subst hj; exact isIso_holomorphicDeRhamToFunctionsComplexInt_f_zero point
    · have hs : IsZero ((holomorphicDeRhamComplexInt point).X j) := by
        rcases lt_or_gt_of_ne hj with hneg | hpos
        · exact CochainComplex.isZero_of_isStrictlyGE (holomorphicDeRhamComplexInt point) 0 j
            (by omega)
        · exact holomorphicDeRhamComplexInt_isZero_X_of_lt point j (by
            rw [dim_point]; exact_mod_cast hpos)
      apply isIso_of_source_target_iso_zero
      · exact hs.isoZero
      · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ j hj).isoZero
  exact HomologicalComplex.Hom.isIso_of_components _

attribute [local instance] isIso_toFunctions_point

theorem surjective_point : Function.Surjective (deRhamToHolomorphicFunctionCohomology point 0) := by
  intro γ
  refine ⟨hypercohomologyMap point (inv (holomorphicDeRhamToFunctionsComplexInt point)) 0 γ, ?_⟩
  change hypercohomologyMap point (holomorphicDeRhamToFunctionsComplexInt point) 0
    (hypercohomologyMap point (inv (holomorphicDeRhamToFunctionsComplexInt point)) 0 γ) = γ
  rw [← hypercohomologyMap_comp_apply, IsIso.inv_hom_id, hypercohomologyMap_id]
  rfl

example : Function.Injective (filteredToDeRhamCohomology point 1 1) :=
  filteredToDeRhamCohomology_one_one_injective point surjective_point
```

O2. **One copy of the helper.** On the next change to `FirstFiltration.lean`, make its helper public under a name distinct from `RationalHypercohomology`'s (for example `HodgeLadder.equiv_hypercohomologyMap_comp_mk₀`), delete `equiv_hypercohomologyMap'` here, and move `shifted_coyoneda_exact₂` into `HodgeLadder/General/TriangleShiftedHom.lean`, updating the module column of the change 2 row.

## Not done

No Lean check of the 𝔸¹ computation in finding 1 (it would need an affine-line witness with Γ(Ω¹) ≠ 0). No locator check of [Voisin2002].
