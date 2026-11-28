# Red team: `elliptic-curve-smooth` (foundation, issue #252, T1 plan node E2)

Date: 2026-11-28. Worktree `elliptic-curve-smooth`, branch `track/elliptic-curve-smooth`, candidate commit `f29fd24` on base `19a4bda` (the tip of `main`). Files: `HodgeLadder/General/HypersurfaceSmooth.lean` (117 lines, namespace `HodgeLadder.HypersurfaceSmooth`), `HodgeLadder/Elliptic/Curve/Smooth.lean` (168 lines, namespace `HodgeLadder.Tests`).

**Verdict: pass with changes.**

The rung delivers what node E2 of `docs/notes/2026-11-27-t1-plan.md` asks for: `instance : SmoothOfRelativeDimension 1 HodgeLadder.Tests.ellipticCurve.hom`, with `Smooth` from it. Both instances are found by instance search at `ellipticCurve` exactly where upstream's statements ask for them, and the relative dimension 1 is pinned two independent ways (rank of Ω on a nonzero chart localization, and upstream's `dim` under a hypothetical integrality instance). No sign or scalar enters. The changes are placement, a gaps-row addition, a conventions row and the ledger note.

Read: ledger entries `elliptic-curve-smooth`, `plane-cubic-subscheme`, `elliptic-curve-integral`, `elliptic-curve-witness`; `python3 tools/next.py elliptic-curve-smooth`; `docs/notes/2026-11-27-t1-plan.md` nodes E1 to E4; `docs/sketches/plane-cubic-subscheme.redteam.md`; `HodgeLadder/Tests/EllipticCurve.lean` (`cubicForm`, `affineEquation`, `infinityEquation`, the chart isos, `ellipticCurveChart*_inv_ι`, `ellipticCurve_chart_cover`); `HodgeLadder/Tests/P1p1Witness.lean` (assembly pattern); upstream `Statement.lean`, `Variants.lean`, `Lemmas/AlgebraicGeometry/Smooth/Equidimensional.lean` (`SmoothOfRelativeDimension.of_isIntegral`, `SmoothOfRelativeDimension.dim_eq`), `Mathlib/RingTheory/SmoothKrullDimension.lean`; Mathlib `RingTheory/Extension/Presentation/{Basic,Submersive}.lean`, `RingTheory/Smooth/{StandardSmooth,StandardSmoothCotangent,Local}.lean`, `RingTheory/RingHom/StandardSmooth.lean`, `RingTheory/Etale/StandardEtale.lean`; `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`; `tools/pinwalk.py` output.

Scratch (directory `scratch-redteam-ecs/` in the worktree, deleted afterwards):

| File | What it tried | Result |
|---|---|---|
| `Before.lean` | `inferInstance` for `Smooth ellipticCurve.hom` and `SmoothOfRelativeDimension 1 ellipticCurve.hom` importing only `HodgeLadder.Tests.EllipticCurve` | both fail to synthesize: the rung adds the instances, nothing upstream or in Mathlib supplied them |
| `Probe.lean`, A | `inferInstance` for `SmoothOfRelativeDimension 1 ellipticCurve.hom`, `Smooth ellipticCurve.hom`, `LocallyOfFiniteType ellipticCurve.hom` with the rung imported | all three found |
| `Probe.lean`, B | `example [IsIntegral ellipticCurve.left] (h : HodgeConjecture) (p : ℕ) := h ellipticCurve p`; `inferInstance` for `SmoothOfRelativeDimension (TopologicalSpace.dim ellipticCurve.left) ellipticCurve.hom` under the same hypothetical `IsIntegral`; `dim ellipticCurve.left = 1` by `SmoothOfRelativeDimension.dim_eq (f := ellipticCurve.hom) 1` | all elaborate; the only hypothesis of `HodgeConjecture` still missing at `ellipticCurve` is `IsIntegral ellipticCurve.left` (rung `elliptic-curve-integral`) |
| `Probe.lean`, C | `¬ SmoothOfRelativeDimension 0 ellipticCurve.hom` under hypothetical `IsIntegral` | proved by `dim_eq` at 1 and at 0 and `omega`: the number 1 is load-bearing |
| `Probe.lean`, D | the criterion at f = 0 and f = 1 in one variable over ℂ; the point (i, 1 − i) on y² = x³ − x | f = 0: hypothesis false (`simp`); f = 1: hypothesis true in the zero ring, conclusion about the empty scheme; the chart ring of the curve is nonzero (evaluation at (i, 1 − i) is a ring map to ℂ) |
| `Probe.lean`, E | `Module.rank LocA Ω[LocA⁄ℂ] = 1` for `LocA` the localization of ℂ[x, y] ⧸ (y² − x³ + x) away from ∂_y f = 2y, with `Nontrivial LocA` from the lift of evaluation at (i, 1 − i) (2y ↦ 2 − 2i ≠ 0) | proved from `isStandardSmoothOfRelativeDimension_away` and Mathlib's `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`, no integrality used |
| `Optional.lean` | the code block of change 6, verbatim, inside `namespace HodgeLadder.Tests` | compiles, no warnings |
| `Probe.lean` | `#print axioms HodgeLadder.Tests.smoothOfRelativeDimension_ellipticCurve` | `[propext, Classical.choice, Quot.sound]` |

## 1. Is this the statement the literature makes?

The literature statement is the Jacobian criterion for a hypersurface in its standard-smooth form [`Stacks`, section "Smooth ring maps", definition of a standard smooth algebra; tag numbers unverified]: a presentation R[x₁, …, xₙ] ⧸ (f₁, …, f_c) is standard smooth of relative dimension n − c when the c × c minor of (∂f_j/∂x_i) on the first c variables is invertible in the quotient. Mathlib's `Algebra.IsStandardSmoothOfRelativeDimension` follows that definition, with `Presentation.dimension` = #variables − #relations.

Field by field against `smoothOfRelativeDimension_spec`:

| Literature | Lean | Match |
|---|---|---|
| A = R[x_σ] ⧸ (f), one equation | `MvPolynomial σ R ⧸ Ideal.span {f}`, `[Fintype σ]` | yes |
| hypothesis: V(f) has no point where all ∂ᵢf vanish, i.e. (f, ∂₁f, …, ∂ₙf) = (1) in R[x] | `Ideal.span (Set.range fun i => mk (pderiv i f)) = ⊤` in A, which is the same ideal statement read in the quotient | yes |
| A[1/∂ᵢf] = R[x_σ, T] ⧸ (f, T ∂ᵢf − 1), Jacobian on (Xᵢ, T) triangular with diagonal ∂ᵢf, ∂ᵢf | `awayPresentation f i` = `localizationAway.comp (naivePresentation f i)`, Jacobian `∂ᵢf · ∂ᵢf` by `comp_jacobian_eq_jacobian_smul_jacobian` and `localizationAway_jacobian` | yes |
| relative dimension n − 1 | `Fintype.card σ - 1` (ℕ subtraction), from `dimension_comp_eq_dimension_add_dimension` with the localization contributing 1 − 1 = 0 | yes for n ≥ 1; at n = 0 the hypothesis forces f to be a unit and A = 0, so the truncation is harmless |
| the D(∂ᵢf) cover Spec A | `RingHom.Locally` with the spanning set `range (mk ∘ pderiv · f)` | yes |
| scheme form | `HasRingHomProperty.Spec_iff` for Mathlib's `SmoothOfRelativeDimension`, whose ring-hom property is `RingHom.Locally (IsStandardSmoothOfRelativeDimension n)` | yes |

For the curve: E : y²z = x³ − xz², with charts z ≠ 0, f = y² − x³ + x, and y ≠ 0, h = w − u³ + uw² (conventions row "Plane cubic E and its charts"). By hand:

- f_x = 1 − 3x², f_y = 2y; (4 − 6x²)(1 − 3x²) − 9xy · 2y = 4 − 18x² + 18x⁴ − 18xy² = 4 − 18x(y² − x³ + x). The candidate's identity is right, and 4 is a unit over ℂ.
- h_u = w² − 3u², h_w = 1 + 2uw; u²(w² − 3u²) + (1 + uw)(1 + 2uw) = 1 + 3uw + 3u²w² − 3u⁴ = 1 + 3u(w − u³ + uw²). Right; the handoff's derivation from Euler's relation, 3h = u h_u + 2w + w h_w at y = 1, also checks.
- The `pderiv_*` lemmas agree with these derivatives, including the variable order in the chart y ≠ 0 (`dehomogenize 1` sends X 0 to u = x/y and X 2 to X 1 = w = z/y).

The cover: `IsZariskiLocalAtSource.of_iSup_eq_top` is applied to `cond b (ι ⁻¹ᵁ U 2) (ι ⁻¹ᵁ U 1)`, so `true` is the chart z ≠ 0 and `false` the chart y ≠ 0; `rintro (_ | _)` treats `false` first with `ellipticCurveChartInfinity` and `true` second with `ellipticCurveChartAffine`. The supremum is `ellipticCurve_chart_cover` after `iSup_bool_eq`. On each piece the restriction of `ellipticCurve.hom` is rewritten, through `ellipticCurveChart*_inv_ι` and `ProjectiveSpace.chart_toSpec`, to `Spec.map (algebraMap ℂ (ℂ[x, y] ⧸ (·)))`, which is literally the morphism in `smoothOfRelativeDimension_spec`; the chart iso contributes relative dimension 0 (`0 + 1`). `ellipticCurve.hom` is `ellipticCurveι ≫ ProjectiveSpace.toSpec 2 ℂ` by `rfl` (`ellipticCurve_hom`), the same structure map as in `isProjective_ellipticCurve`.

## 2. Can the hypotheses be satisfied?

The general criterion: yes, at both charts of the curve (`span_pderiv_affineEquation`, `span_pderiv_infinityEquation`), and with a nonzero quotient: the chart ring maps to ℂ at (i, 1 − i), and the curve has complex points (`nonempty_complexPoint_ellipticCurve`). The hypothesis is not automatic: the cusp fails it (`cusp_span_pderiv_ne_top`), and so does f = 0 over any nontrivial ring (scratch D). It holds degenerately when f is a unit; then A = 0 and the conclusion is about the empty scheme, which is correct and is excluded for the curve by the point above.

The instances have no hypotheses.

## 3. Trivially true?

Tried, failed:

- `inferInstance` without the rung (scratch `Before.lean`): fails for both classes.
- A degenerate reading of `SmoothOfRelativeDimension 1`: on a nonzero localization of the affine chart, Ω has rank exactly 1 (scratch E), and under a hypothetical `IsIntegral ellipticCurve.left`, `SmoothOfRelativeDimension 0` is refuted and `dim ellipticCurve.left = 1` (scratch C, B). So neither the class nor the number is vacuous.
- An unused hypothesis: `smoothOfRelativeDimension_spec` uses `h` in `locally` as the spanning set of `RingHom.Locally`; without it the f = 0 case would assign Spec R[x_σ] relative dimension #σ − 1, which Mathlib's rank lemma refutes for #σ ≥ 1.
- An empty index type: the curve uses `Fin 2`; `Fintype.card (Fin 2) - 1` reduces to `1` by `rfl` in the chart theorems.

## 4. Interface axioms

None. The rung is a foundation with no structure and no `Prop` input; decision 0003 holds.

## 5. Checker and declarations

`python3 tools/check.py --no-build` in the worktree: `ACCEPTED: all checks passed`. All 17 ledger declarations report `[Classical.choice, Quot.sound, propext]`, and they are the 17 public declarations of the two files (11 in the curve file, 6 in the general file), each the one the ledger note describes: the two instances, the two chart theorems, the two span theorems, the four `pderiv_*` lemmas, the cusp test, and the six general declarations.

## 6. Conventions

| Convention | Where | Sensitive? |
|---|---|---|
| Linear term of the curve (a₄ = −1) and chart coordinates | row "Plane cubic E and its charts" | the instances are insensitive (y² = x³ ± x are both smooth, Δ = 64 for a₄ = −1 and −64 for a₄ = 1); the two explicit combinations are specific to a₄ = −1 and are checked by `linear_combination` against the definitions `affineEquation`, `infinityEquation` |
| Relative dimension of a presentation: #variables − #relations in ℕ; naive presentation with the relation attached to Xᵢ; Jacobian of `comp` is the product | Mathlib `Presentation.dimension`, `PreSubmersivePresentation.naive`, `comp_jacobian_eq_jacobian_smul_jacobian` | no sign: the Jacobian enters only through `IsUnit`. The value #σ − 1 is load-bearing for `elliptic-curve-witness` (`dim ellipticCurve.left = 1`). Missing from the register: change 3 |
| Upstream's relative dimension | `SmoothOfRelativeDimension.of_isIntegral` gives `SmoothOfRelativeDimension (dim X.left)`; `dim_eq` identifies any certified d with `dim` | matches: scratch B and C |

No cited result carries a sign. The two `pderiv` facts are Mathlib's `pderiv_X` with `Pi.single`, evaluated by `simp`.

## 7. Equality first

The rung is neither an identity nor an inclusion; it supplies an instance for the witness `elliptic-curve-witness` (E4), which feeds the T1 identity rungs on E × E. Not applicable beyond that.

## 7b. Non-vacuity

- Hypothesis side: `HodgeLadder.Tests.cusp_span_pderiv_ne_top` exists and would fail if the hypothesis held for every f.
- Conclusion side: the smallest upstream-API test is `SmoothOfRelativeDimension.dim_eq (f := ellipticCurve.hom) 1 : TopologicalSpace.dim ellipticCurve.left = 1`, which needs `IsIntegral ellipticCurve.left` and belongs to E4 (the plan lists `dim ellipticCurve.left = 1` there). Until E3 lands, an integrality-free test is the Kähler rank lemma of scratch E; it compiled as written and is offered as optional change 6.

## 8. Placement, Mathlib overlap, gaps

- Placement. `HodgeLadder/Elliptic/Curve/Smooth.lean` is `next.py`'s fallback path from the rung id. Its namespace is `HodgeLadder.Tests`, the curve it extends is `HodgeLadder/Tests/EllipticCurve.lean`, and the red team of `plane-cubic-subscheme` (change 1) moved that rung's file from the fallback `HodgeLadder/Plane/Cubic/Subscheme.lean` into `HodgeLadder/Tests/` for the same reason. `HodgeLadder/Elliptic/` holds nothing else. Move to `HodgeLadder/Tests/EllipticCurveSmooth.lean` (change 1). The general file stays where it is.
- Mathlib at the pin (searched `RingTheory/Smooth/`, `RingTheory/Extension/`, `RingTheory/Etale/`, `RingTheory/RingHom/`, `AlgebraicGeometry/Morphisms/Smooth.lean` for `pderiv`, `span {f}` and "Jacobian"): no criterion through the ideal of partial derivatives. Neighbours: `Algebra.FormallySmooth.iff_injective_lTensor_residueField` (`RingTheory/Smooth/Local.lean`, the Jacobian criterion for local algebras through the cotangent complex); `PreSubmersivePresentation.isUnit_jacobian_of_linearIndependent_of_span_eq_top` (`Extension/Presentation/Submersive.lean`, a pointwise unit criterion for a given presentation); `StandardEtalePair` (`RingTheory/Etale/StandardEtale.lean`, the one-variable étale analogue R[X][Y] ⧸ (f, Y g − 1)). None states the candidate's result; the gaps row should name the last two for a bump (change 2). Upstream has no hypersurface smoothness lemma. `check.py`'s import-clash step passes.
- Universe. `smoothOfRelativeDimension_spec` takes `R σ : Type u` in one universe; enough for `Fin 2` over ℂ, worth knowing for a later ℙⁿ use.
- Layers (`tools/pinwalk.py`, 2026-11-28): `HodgeLadder.General.HypersurfaceSmooth` 0, matching the gaps row. An older ordering slip in the same table (the layer-2 `HodgeLadder.General.Hypersurface` row sits after layer-9 and layer-27 rows) predates this rung; no change asked here.

## 9. Drift

Base `19a4bda` is the tip of `main`; `lake-manifest.json` is identical to `main`'s (upstream `2ead713`, `v4.35.0-rc4`). No drift to diff. At a bump, the Mathlib directories in change 2 are the ones to diff, and `SmoothOfRelativeDimension.dim_eq` upstream is the consumer to recheck.

## 10. Findings

1. The general criterion is the standard one-equation Jacobian criterion with the right relative dimension; the unit-ideal hypothesis is the hypersurface smoothness condition, fails for the cusp and for f = 0, and holds degenerately only when f is a unit (empty scheme).
2. Both chart combinations are correct identities (checked by hand and by `linear_combination`), and the cover pieces are matched with the correct charts and structure maps.
3. Instance search finds `SmoothOfRelativeDimension 1`, `Smooth` and `LocallyOfFiniteType` at `ellipticCurve.hom`; `HodgeConjecture` applies to `ellipticCurve` once `IsIntegral ellipticCurve.left` exists, and upstream's `SmoothOfRelativeDimension (dim ellipticCurve.left)` and `dim = 1` then follow.
4. The relative dimension 1 is pinned (rank of Ω, `dim_eq`); no vacuity found.
5. No sign; the conventions register lacks a row for Mathlib's presentation dimension, which E4 depends on.
6. File placement disagrees with the namespace and the precedent of `plane-cubic-subscheme`.
7. The gaps row omits two Mathlib neighbours to recheck at a bump.

## 11. Required changes

1. Move `HodgeLadder/Elliptic/Curve/Smooth.lean` to `HodgeLadder/Tests/EllipticCurveSmooth.lean` (module `HodgeLadder.Tests.EllipticCurveSmooth`, namespace unchanged) and delete the empty `HodgeLadder/Elliptic/`. In `HodgeLadder.lean` replace `public import HodgeLadder.Elliptic.Curve.Smooth` by `public import HodgeLadder.Tests.EllipticCurveSmooth`. In `ledger/ladder.json`, entry `elliptic-curve-smooth`, set `"module": "HodgeLadder.Tests.EllipticCurveSmooth"`. In `docs/roadmap.md`, row `elliptic-curve-smooth`, replace `` `HodgeLadder.Elliptic.Curve.Smooth` `` by `` `HodgeLadder.Tests.EllipticCurveSmooth` ``. In `docs/handoffs/2026-11-28-elliptic-curve-smooth.md` replace `` `HodgeLadder/Elliptic/Curve/Smooth.lean` `` by `` `HodgeLadder/Tests/EllipticCurveSmooth.lean` ``. In the module docstring replace "No sign convention enters; the combinations are identities of polynomials." by: "No sign convention enters this file. The curve's linear term is recorded in `docs/conventions.md`, row \"Plane cubic E and its charts\"; smoothness holds for either sign, and the two combinations below are specific to y² = x³ − x."

2. In `docs/gaps.md`, row `HodgeLadder.HypersurfaceSmooth.naivePresentation`, replace the "Why local" cell by:

   Mathlib has the presentations (`PreSubmersivePresentation.naive`, `localizationAway`, `comp`) and no criterion through the ideal of partial derivatives; neighbours are `Algebra.FormallySmooth.iff_injective_lTensor_residueField` (`RingTheory/Smooth/Local.lean`, the local Jacobian criterion through the cotangent complex), `PreSubmersivePresentation.isUnit_jacobian_of_linearIndependent_of_span_eq_top` (`RingTheory/Extension/Presentation/Submersive.lean`) and `StandardEtalePair` (`RingTheory/Etale/StandardEtale.lean`, the one-variable étale case); at a bump check Mathlib `RingTheory/Smooth/`, `RingTheory/Extension/Presentation/`, `RingTheory/Etale/` and `AlgebraicGeometry/Morphisms/Smooth.lean` for a Jacobian criterion; rung `elliptic-curve-smooth`

3. In `docs/conventions.md`, add after the row "Plane cubic E and its charts":

   | Relative dimension of a one-equation presentation | this repository, `HodgeLadder.HypersurfaceSmooth.naivePresentation`, `naivePresentation_jacobian`, `awayPresentation`, `isStandardSmoothOfRelativeDimension_away`, `smoothOfRelativeDimension_spec` (`HodgeLadder/General/HypersurfaceSmooth.lean`), `HodgeLadder.Tests.smoothOfRelativeDimension_ellipticCurve` (`HodgeLadder/Tests/EllipticCurveSmooth.lean`, rung `elliptic-curve-smooth`); Mathlib `Presentation.dimension`, `PreSubmersivePresentation.naive`, `localizationAway`, `comp`, `dimension_comp_eq_dimension_add_dimension`, `SmoothOfRelativeDimension`; upstream `SmoothOfRelativeDimension.of_isIntegral`, `SmoothOfRelativeDimension.dim_eq` | the dimension of a presentation is #variables − #relations in ℕ (truncated); `naivePresentation f i` has variables σ and the one relation f attached to Xᵢ, Jacobian the class of ∂ᵢf; `awayPresentation f i` is `localizationAway.comp naive`, variables `Unit ⊕ σ`, relations `Unit ⊕ Unit`, Jacobian ∂ᵢf · ∂ᵢf, dimension 0 + (#σ − 1); on a nonzero localization the relative dimension is the rank of Ω (Mathlib `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`), and on an integral X it is upstream's `dim X.left` (`SmoothOfRelativeDimension.dim_eq`) | no sign: smoothness is a `Prop` and the Jacobian enters only through `IsUnit`, so signs and unit scalars are invisible. The number is load-bearing for `elliptic-curve-witness` (`dim ellipticCurve.left = 1`). At #σ = 0 the truncation gives 0, harmless because the hypothesis then forces f to be a unit and the quotient to be zero | read from source; checked in scratch: rank of Ω is 1 on the nonzero localization of ℂ[x, y] ⧸ (y² − x³ + x) away from 2y, and under a hypothetical `IsIntegral ellipticCurve.left`, `dim ellipticCurve.left = 1` and `¬ SmoothOfRelativeDimension 0 ellipticCurve.hom` (red team 2026-11-28, `elliptic-curve-smooth`) |

4. In `ledger/ladder.json`, entry `elliptic-curve-smooth`, append to `note`: " Red team: pass with changes (docs/sketches/elliptic-curve-smooth.redteam.md)."

5. After the move, run `python3 tools/check.py` (full build: the module path changed) and confirm the 17 declarations are still accepted.

6. Optional, not required for the pass: add to the test file an integrality-free test that the relative dimension is the rank of Ω. Compiled in scratch as written, appended inside `namespace HodgeLadder.Tests` of the test file (scratch `Optional.lean`):

   ```lean
   /-- The localization of the affine chart away from `∂_y f = 2y`. -/
   abbrev affineChartAway := Localization.Away
     (Ideal.Quotient.mk (Ideal.span {affineEquation}) (pderiv 1 affineEquation))

   /-- `(x, y) = (i, 1 − i)` lies on `y² = x³ − x`. -/
   theorem affineEquation_eval_I : eval ![Complex.I, 1 - Complex.I] affineEquation = 0 := by
     simp [affineEquation]; ring_nf; simp [Complex.I_sq]

   instance : Nontrivial affineChartAway := by
     let ev : MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation} →+* ℂ :=
       Ideal.Quotient.lift _ (eval ![Complex.I, 1 - Complex.I]) fun a ha => by
         obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
         simp [affineEquation_eval_I]
     have hu : IsUnit (ev (Ideal.Quotient.mk _ (pderiv 1 affineEquation))) := by
       rw [pderiv_one_affineEquation]
       refine isUnit_iff_ne_zero.mpr ?_
       simp [ev]
       intro h
       have := congrArg Complex.re h
       simp at this
     exact (IsLocalization.Away.lift _ hu : affineChartAway →+* ℂ).domain_nontrivial

   /-- **Test.** The relative dimension one is the rank of `Ω` on a nonzero chart localization. -/
   theorem rank_kaehlerDifferential_affineChartAway :
       Module.rank affineChartAway Ω[affineChartAway⁄ℂ] = 1 := by
     have := HypersurfaceSmooth.isStandardSmoothOfRelativeDimension_away affineEquation (1 : Fin 2)
     simpa using Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
       (R := ℂ) (S := affineChartAway) (Fintype.card (Fin 2) - 1)
   ```
