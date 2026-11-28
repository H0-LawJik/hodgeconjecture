# Red team: `elliptic-coordinate-functions` (S4 of `elliptic-curve-holomorphic-form`, issue #292)

**Verdict: pass with changes.** The candidate is commit 257ee3a on `track/elliptic-coordinate-functions`, file `HodgeLadder/Elliptic/Coordinate/Functions.lean`. The four coordinates are sections of upstream's `holomorphicFunctionSheaf ellipticCurve (dim ellipticCurve.left)`, carried by upstream's ring structure, with the dimension spelling that upstream's de Rham complex uses. The values come from the checked chart homeomorphisms, the relations come from the chart ring, and the overlap identities are exact. All three local forms of S5 elaborate against these sections as elements of upstream's `HolomorphicForm` and of `holomorphicDeRhamSheaf … 1`. The required changes cover placement, one weak pin and the bookkeeping. There is no sign.

Scope: a proportionate pass. I read the candidate, the sketch (steps 4 to 6 and the sub-rung table), upstream's `AnalyticSheaf.lean`, `AnalyticDifferentialForms.lean` (`OpenHolomorphicFunctions`, `chartEvaluationKernel`, `HolomorphicForm`) and `HolomorphicDeRham.lean` (`holomorphicDeRhamPresheaf`, `holomorphicDeRhamSheaf`, `holomorphicDeRhamComplex`, the `dim X.left` spelling at line 563), the port's `RegularFunctionsHolomorphic.lean`, the conventions row "Plane cubic E and its charts", and the briefs `tools/next.py elliptic-coordinate-functions` and `tools/next.py elliptic-omega`. Probes ran in a scratch directory under the worktree (deleted). The file compiles against its built olean in about 10 s.

## Findings

1. **The coordinates are honest sections of upstream's 𝒪.** `EllipticHolomorphic U` is spelled as Mathlib's `C^ω⟮𝓘(ℂ, Fin (dim ellipticCurve.left) → ℂ), U; ℂ⟯`. The following elaborate by `rfl` in scratch:
   - `EllipticHolomorphic U = OpenHolomorphicFunctions ellipticCurve (dim ellipticCurve.left) (op U)`;
   - `EllipticHolomorphic U = ((holomorphicFunctionSheaf ellipticCurve (dim ellipticCurve.left)).presheaf.obj (op U) : Type)`.

   So the carrier is upstream's local-predicate sheaf of sections, and no independent C^ω type enters. The ring structures agree as well: `ellipticY_sq` is accepted verbatim at the type `OpenHolomorphicFunctions ellipticCurve (dim _) (op ellipticAffineOpen)`. Upstream's `holomorphicFunctionSheafToTypes.commRing` is `inferInstanceAs` of the C^ω ring. Restriction in upstream's sheaf is the candidate's `ellipticResAffine` by `rfl` (scratch) and in general by `holomorphicFunctionSheaf_map_eq` (in the file). The dimension spelling `TopologicalSpace.dim ellipticCurve.left` is the one upstream's `deRhamComplex` passes to `holomorphicDeRhamComplex X (dim X.left)`. No cast is needed, and none should be added (sketch, signs table, last row).

2. **The pin `ellipticX_eq_regularToHolomorphicSheaf` is the strong pin.** By `rfl` it identifies `ellipticX` with the component of the port's sheaf map `regularToHolomorphicSheaf ellipticCurve _` at `chartOpenScheme 2`, applied to the regular function `x`. That ties the coordinate to the algebraic structure sheaf, beyond the bare ring map. The companion `ellipticX_mem_openHolomorphicFunctions` (`∃ f : OpenHolomorphicFunctions …, f = ellipticX`) holds for any term once the types unify, so it says less than its name and docstring suggest. Required change 2 replaces it with the type equality of finding 1.

3. **The values are exact and come from the evaluation.** `ellipticChartHolomorphic_apply` unwinds `chartHomeomorph` through upstream's `evaluate_openEquiv`, `evaluate_eq`, `evaluate_map` and `affineSpecEquiv_apply`, then `quotAlgHomHomeomorph`. No definitional shortcut replaces the evaluation. `ellipticX_apply`, …, `ellipticW_apply` reduce to the checked homeomorphisms of `elliptic-curve-points`, and the point tests (origin, (±1, 0), (i, 1 − i), [0 : 1 : 0], and (u, w) = ((−1 + i)/2, (1 + i)/2) at the chart meet) go through those. By hand at the chart meet: u = x/y = i/(1 − i) = (−1 + i)/2 and w = 1/(1 − i) = (1 + i)/2. The index check: chart 1 is `dehomogenize 1`, with `X 0` = x/y and `X 1` = z/y, matching the conventions row.

4. **The relations are exact, and wrong variants are rejected.** `ellipticY_sq` and `ellipticW_eq` are images of ring identities in the chart ring (`chartRing_two_relation`, `chartRing_one_relation`, each closed by `ring` after `dehomogenize_*_cubicForm`). In scratch, `¬ (ellipticY ^ 2 = ellipticX ^ 3 + ellipticX)` is proved by evaluating at the chart meet (imaginary part: −2i against 0). The swapped transition `u = y / x` is refuted pointwise at the same point. Both overlap ring identities (`u · y = x`, `w · y = 1`) are equalities. Neither holds only up to a scalar, and `isUnit_ellipticResAffine_ellipticY` comes from `w · y = 1` with no general inverse lemma.

5. **Non-constancy is genuine.** Each `*_not_constant` uses two point values obtained through the evaluation (finding 3), so a definitional collapse (all four functions zero, or a constant) would fail them. They are the smallest non-vacuity tests for this rung.

6. **The fit with S5: the three local forms elaborate.** In scratch, against upstream's API:
   - `Algebra.DeRham.mk ℂ A₁ 1 (ellipticResInfinity ellipticW) ![ellipticResAffine ellipticX]`, with `A₁ := OpenHolomorphicFunctions ellipticCurve (dim _) (op ellipticOverlapOpen)`. This is y⁻¹ dx on V₁, using `w = y⁻¹`. It passes to `HolomorphicForm ellipticCurve (dim _) (op ellipticOverlapOpen) 1` by `Submodule.Quotient.mk`, which is definitionally `(holomorphicDeRhamPresheaf ellipticCurve (dim _) 1).obj (op ellipticOverlapOpen)`, and then to `(holomorphicDeRhamSheaf ellipticCurve (dim _) 1).presheaf.obj (op ellipticOverlapOpen)` by `((toSheafify J (holomorphicDeRhamPresheaf …)).app _).hom`.
   - V₂ is defined as `⟨Subtype.val '' {z : ellipticAffineOpen | (3 * ellipticX ^ 2 - 1) z ≠ 0}, …⟩`. Openness comes from `ellipticAffineOpen.isOpen.isOpenMap_subtype_val` and `isOpen_ne_fun (….contMDiff.continuous) continuous_const`, and the inclusion into `ellipticAffineOpen` is a two-line proof. The inverse of a nowhere-vanishing function is `⟨fun z => (f z)⁻¹, f.contMDiff.inv₀ h⟩` (Mathlib's `ContMDiff.inv₀` with the `ContMDiffInv₀ 𝓘(ℂ) ω ℂ` instance), with `inv * f = 1` by `ext`. The form `Algebra.DeRham.mk ℂ _ 1 (2 * (3x² − 1)⁻¹) ![y]` on V₂ elaborates. V₃ is the same pattern on `ellipticInfinityOpen` with `1 + 2 * ellipticU * ellipticW`.
   - The Kähler identity behind the agreement `(2 * y) • D y = (3 * x ^ 2 - 1) • D x` is proved in scratch in `Ω[OpenHolomorphicFunctions ellipticCurve (dim _) (op V)⁄ℂ]` for every `V ≤ ellipticAffineOpen`. The proof is `congrArg D` of `ellipticY_sq`, then `Derivation.leibniz_pow`, then a `Nat.cast_smul_eq_nsmul` rewrite. S4's ring identities are therefore the right shape for S5's agreement step.

7. **What S5 must still build.** These items are outside S4 and are listed so the S5 brief can carry them:
   - (a) the opens V₂ and V₃, the cover V₁ ∪ V₂ ∪ V₃ = ⊤ (using `ellipticCurveInfinity` with u = w = 0 in V₃ and `compl_ellipticAffineOpen`), and V₂ ∩ V₃ ⊆ V₁;
   - (b) the inverse of a nowhere-vanishing section (three lines, finding 6). This is general for any C^ω map to ℂ, so it goes in `HodgeLadder/General/` with a row in `docs/gaps.md` if it is kept as a lemma;
   - (c) the Kähler identities on V₁ ∩ V₂ and V₁ ∩ V₃. S4 states the overlap identities only on `ellipticOverlapOpen`, and S5 must push them to smaller opens by the ring maps `ContMDiffMap.restrictRingHom`. The du computation needs `dw = −w² dy` from `w · y = 1` and `du = w dx + x dw` from `x · w = u` (`ellipticX_mul_ellipticW`). The sign of −2(1 + 2uw)⁻¹ du is load-bearing for `ellipticOmega_res`;
   - (d) the passage from Kähler forms to the quotient by `chartEvaluationKernel` (by `mkQ`), then naturality of `toSheafify`, then `TopCat.Sheaf.existsUnique_gluing`;
   - (e) the nonvanishing (sketch step 6), the hardest part. Upstream evaluates forms in its chosen `localChart` (`chartEvaluation`), which is unrelated to x, y, u, w, so S5 needs D(x ∘ e⁻¹) ≠ 0 at some point of a chart. Non-constancy of x (finding 5) is weaker than what that argument needs, which is the two-point fibre of x. The pointwise fibre lemmas are cheap here and were proved in scratch (recommended change 6).

8. **Placement.** `HodgeLadder/Elliptic/Coordinate/Functions.lean` is `next.py`'s fallback path. Every sibling (`EllipticCurve`, `EllipticCurvePoints`, `EllipticCurveWitness`, `EllipticCurveCM`, …) lives in `HodgeLadder/Tests/` under namespace `HodgeLadder.Tests`, and the candidate already uses that namespace. Move the file to `HodgeLadder/Tests/EllipticCurveCoordinates.lean` (required change 1).

9. **General lemmas.** None. `chartEval_quotAlgHomCoord` and `analyticOpen_chartOpenScheme` are stated for the cubic's charts, and `holomorphicFunctionSheaf_map_eq` is stated for `ellipticCurve`. No row goes in `docs/gaps.md`.

10. **Signs and normalizations.** None enter S4. The coordinates are u = x/y and w = z/y (row "Plane cubic E and its charts"), and a swapped order would fail `ellipticU_apply` and `ellipticUW_chartMeet` (finding 4). Every theorem is an exact equality of functions or values, and none holds up to a scalar. The first load-bearing scalar downstream is the −2 in S5's third local form, which is S5's concern. The conventions row needs the new names (required change 4).

11. **Axioms and the checker.** `#print axioms` on `ellipticX_apply`, `ellipticU_apply`, `ellipticY_sq`, `ellipticW_eq`, `ellipticU_mul_ellipticY`, `ellipticX_mul_ellipticW`, `isUnit_ellipticResAffine_ellipticY`, `ellipticUW_chartMeet`, `ellipticW_not_constant` and `ellipticX_eq_regularToHolomorphicSheaf` gives `[propext, Classical.choice, Quot.sound]`. `python3 tools/check.py --no-build` in the worktree exits with "ACCEPTED: all checks passed", but the module is neither root-imported nor named in the ledger yet, so the checker has not covered these declarations. Rerun it after required changes 1 and 3.

12. **Pin drift.** None. The branch base `d670df6` and `main` (`a509ee0`) have identical `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` (upstream rev `2ead713…`, `v4.35.0-rc4`). `main` is one commit ahead (`weil-surface-reduction`), so rebase before the pull request. The only expected conflict is `ledger/ladder.json`.

## Required changes

1. Move `HodgeLadder/Elliptic/Coordinate/Functions.lean` to `HodgeLadder/Tests/EllipticCurveCoordinates.lean`, with module `HodgeLadder.Tests.EllipticCurveCoordinates`. Add `public import HodgeLadder.Tests.EllipticCurveCoordinates` to `HodgeLadder.lean`, and update the ledger `file`/`module` fields and the sketch's S4 row if it names a path.

2. Replace `ellipticX_mem_openHolomorphicFunctions` with:

   ```lean
   /-- **Pin to upstream's ring.** Holomorphic functions on an open of `E(ℂ)` are, by definition,
   upstream's `OpenHolomorphicFunctions` in dimension `dim E`, the coefficient ring of
   `HolomorphicForm` and `holomorphicDeRhamSheaf`. -/
   theorem ellipticHolomorphic_eq_openHolomorphicFunctions
       (U : TopologicalSpace.Opens (ComplexPoint ellipticCurve)) :
       EllipticHolomorphic U =
         OpenHolomorphicFunctions ellipticCurve (TopologicalSpace.dim ellipticCurve.left) (op U) :=
     rfl
   ```

   Update the module docstring's "Main results" to match.

3. Ledger entry `elliptic-coordinate-functions`: set `status` to `checked`, `module` to `HodgeLadder.Tests.EllipticCurveCoordinates`, and `declarations` to the docstring's Main definitions and Main results (with change 2 applied and change 6 if taken), each prefixed `HodgeLadder.Tests.`. Use this `note`:

   > Checked 2026-11-28. Sketch: docs/sketches/elliptic-curve-holomorphic-form.md (S4). x, y on z ≠ 0 and u = x/y, w = z/y on y ≠ 0 are the port's regularFunctionsToHolomorphic of the chart coordinates X 0, X 1 of dehomogenize 2 and dehomogenize 1, as sections of upstream's holomorphicFunctionSheaf ellipticCurve (dim ellipticCurve.left) (EllipticHolomorphic U = OpenHolomorphicFunctions … (op U) by rfl; pinned to regularToHolomorphicSheaf by rfl). Values through ellipticAffineHomeomorph and ellipticInfinityHomeomorph (upstream evaluate_openEquiv, evaluate_map, affineSpecEquiv_apply); y² = x³ − x and w = u³ − uw² as ring identities; on the overlap u·y = x, w·y = 1, x·w = u, y a unit. Tests at the origin, (±1, 0), (i, 1 − i), [0 : 1 : 0]; none of x, y, u, w is constant. No sign. Red team: pass with changes (docs/sketches/elliptic-coordinate-functions.redteam.md).

4. `docs/conventions.md`, row "Plane cubic E and its charts". In the first column, after `` `isOpenEmbedding_infinityPoint` `` or after the `elliptic-curve-points` group, add: `` `ellipticX`, `ellipticY`, `ellipticU`, `ellipticW`, `EllipticHolomorphic`, `ellipticOverlapOpen` (`HodgeLadder/Tests/EllipticCurveCoordinates.lean`, rung `elliptic-coordinate-functions`) ``. In the second column, append: `; as holomorphic functions (sections of upstream's holomorphicFunctionSheaf ellipticCurve (dim ellipticCurve.left)), ellipticX, ellipticY are the images of X 0, X 1 in the chart ring of z ≠ 0 and ellipticU, ellipticW those of X 0, X 1 in the chart ring of y ≠ 0, with w = y⁻¹ and u = x · w on the overlap`. In the last column, append: `; the coordinate functions' values, relations and the u = y/x rejection at (i, 1 − i) checked in scratch (red team 2026-11-28, elliptic-coordinate-functions)`.

5. Rebase onto `main` (`a509ee0`) before opening the pull request, resolve `ledger/ladder.json`, and run `python3 tools/check.py` with the build.

6. (Recommended, cheap, feeds S5 step 6.) Add the pointwise fibre lemmas, each proved in scratch at the pin exactly as written:

   ```lean
   /-- The chart relation pointwise: `y(z)² = x(z)³ − x(z)`. -/
   theorem ellipticY_sq_apply (z : ellipticAffineOpen) :
       ellipticY z ^ 2 = ellipticX z ^ 3 - ellipticX z :=
     congrArg (fun f : EllipticHolomorphic ellipticAffineOpen => f z) ellipticY_sq

   /-- The pair `(x, y)` separates the points of `z ≠ 0`. -/
   theorem eq_of_ellipticX_eq_of_ellipticY_eq {z z' : ellipticAffineOpen}
       (hx : ellipticX z = ellipticX z') (hy : ellipticY z = ellipticY z') : z = z' := by
     apply ellipticAffineHomeomorph.injective
     apply Subtype.ext
     rw [ellipticX_apply, ellipticX_apply] at hx
     rw [ellipticY_apply, ellipticY_apply] at hy
     exact Prod.ext hx hy

   /-- The fibres of `x`: two points with the same `x` have `y` equal or opposite. -/
   theorem ellipticY_eq_or_eq_neg_of_ellipticX_eq {z z' : ellipticAffineOpen}
       (hx : ellipticX z = ellipticX z') :
       ellipticY z = ellipticY z' ∨ ellipticY z = -ellipticY z' := by
     rw [← sq_eq_sq_iff_eq_or_eq_neg, ellipticY_sq_apply, ellipticY_sq_apply, hx]
   ```

   If they are omitted here, the S5 brief must list them.

## What I tried

- Type and ring identification against upstream (finding 1): `rfl` at `OpenHolomorphicFunctions`, at `(holomorphicFunctionSheaf …).presheaf.obj`, and for restriction. `ellipticY_sq` was restated at upstream's type. All succeeded.
- Elaborating S5's three local forms through `Algebra.DeRham.mk`, `HolomorphicForm` and `toSheafify` into `holomorphicDeRhamSheaf … 1` (finding 6). This succeeded after adding `noncomputable` and fixing one continuity spelling (`.contMDiff.continuous`; the `.continuous` field does not exist on the subtype). Mixing `OpenHolomorphicFunctions` and `EllipticHolomorphic` in one product with no ascription fails instance search for `HMul`. S5 should ascribe one spelling per expression.
- The Kähler identity 2y dy = (3x² − 1) dx. My first attempt misparsed `2 * r y • D (r y)` as `2 * (r y • D (r y))` and failed on `HMul ℕ Ω Ω`. With parentheses it closes with `Derivation.leibniz_pow`, `mul_smul`, `sub_smul` and `Nat.cast_smul_eq_nsmul`.
- Trivialization attempts: I looked for a reduction of any value lemma or relation to `rfl` or `True`, or one that survives a wrong relation. The wrong relation y² = x³ + x and the wrong transition u = y/x are both refuted at (i, 1 − i), so the statements carry content. The only statement that holds for a reason unrelated to the mathematics is `ellipticX_mem_openHolomorphicFunctions` (finding 2).
- The fibre lemmas of change 6 compile as written.
- `python3 tools/check.py --no-build`: accepted, with the coverage caveat in finding 11.
