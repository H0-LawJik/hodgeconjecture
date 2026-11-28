# Red team: `elliptic-curve-points` (foundation, issue #254, T1 plan node C0)

Date: 2026-11-28. Worktree `elliptic-curve-points`, branch `track/elliptic-curve-points`, candidate commit `465f44b` on base `1ab3252`. File: `HodgeLadder/Tests/EllipticCurvePoints.lean` (696 lines, 84 `theorem`/`def`/`abbrev` declarations, namespace `HodgeLadder.Tests`), not yet imported from the root, ledger entry still `open`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, the same at base and candidate (the candidate touches no pin file).

**Verdict: pass with changes.**

The two chart homeomorphisms are honest composites of upstream homeomorphisms for the analytic topology and a general lemma for the subspace topology of ℂⁿ. They are pinned by their inverses (x, y) ↦ [x : y : 1] and (u, w) ↦ [u : 1 : w], and those points are pinned in ℙ² by `chartComplexPoint_ι` from `plane-cubic-subscheme`. The transition (x, y) ↦ (x/y, 1/y) has the right direction, and a test at (i, 1 − i) rejects the two nearest wrong formulas. No sign enters. The changes are about placement and records: the general lemma moves to `General/` at layer 0 with a gaps row, one unused import goes, and the ledger and conventions texts are given below.

Read: `python3 tools/next.py elliptic-curve-points`; the ledger entries `elliptic-curve-points`, `plane-cubic-subscheme`, `elliptic-curve-cm`, `elliptic-curve-integral`, `elliptic-curve-witness`, `elliptic-curve-uniformization`, `weierstrass-lattice-i`, `weierstrass-two-to-one`; `docs/notes/2026-11-27-t1-plan.md` nodes C0, C3, D5; `docs/sketches/elliptic-curve-cm.redteam.md` (item 9 on placement); `docs/conventions.md` rows "Plane cubic E and its charts" and "Complex multiplication on E"; `docs/gaps.md` "Algebraic geometry and commutative algebra"; upstream `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean` (`analyticTopology`, `isoMapHomeomorph`), `Lemmas/AlgebraicGeometry/ComplexPoint/{Open,AffineScheme,StandardEtale}.lean`, `Other/AlgebraicGeometry/ComplexPoint/ClosedImmersion.lean`; Mathlib `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`, `RingTheory/Nullstellensatz.lean`. No sketch `docs/sketches/elliptic-curve-points.md` exists; the statement was written from node C0.

Scratch (directory `rt-scratch-ecp-redteam/` in the worktree, deleted afterwards):

| File | What it tried | Result |
|---|---|---|
| `All.lean` | `#print axioms` on all 84 declarations of the file | 83 give `[propext, Classical.choice, Quot.sound]`; `succAbove_two_one` gives `[propext]` |
| `Probe.lean` | (B) the instance on `ComplexPoint ellipticCurve` is upstream's `Point.analyticTopology` by `rfl`; (C) the instance on `affineCurve` is `induced Subtype.val` by `rfl`; (D) `Homeomorph.finTwoArrow v = (v 0, v 1)` by `rfl`; (E) `zeroSet f = MvPolynomial.zeroLocus ℂ (Ideal.span {f})`; (F) at (i, 1 − i) the chart y ≠ 0 differs from (x/y, y) and from (y/x, 1/x); (G) (x, y'/2) ∈ `affineCurve` from y'² = 4x³ − 4x − 0; (H) `affinePoint (x, y) = infinityPoint (x/y, 1/y)` instantiated; (I) a point in both charts; (J) `rfl`, `simp` and `ext <;> simp` fail on `ellipticInfinityHomeomorph_of_mem`; compactness probes | (B) to (J) all check; `CompactSpace (ComplexPoint ellipticCurve)` by `infer_instance` (upstream, `IsProjective`); `CompactSpace (ℂ ⧸ L.lattice.toAddSubgroup)` is not inferred at the pin |
| `NoSmooth.lean` | the file with `public import HodgeLadder.Tests.EllipticCurveSmooth` removed | compiles with no error |
| `QuotAlgHom.lean` | the `ZeroSet` section alone as a module importing only `HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme` and `Mathlib.Topology.Algebra.MvPolynomial`, namespace `HodgeLadder.QuotAlgHom` | compiles with no error |
| `Embed.lean` | the exact text of change 6 | checks, standard axioms |

`lake build HodgeLadder.Tests.EllipticCurvePoints`: success. `python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`. The rung is not in the ledger yet, so the checker's axiom step covered none of its declarations; `All.lean` stands in for it.

## Findings

1. **Statement against the literature.** On the Weierstrass curve E : y²z = x³ − xz² ⊂ ℙ², E(ℂ) is covered by the affine curve y² = x³ − x in the chart z ≠ 0 and the chart y ≠ 0 around O = [0 : 1 : 0] (`Silverman2009`, ch. III §1 for the Weierstrass equation and O, locator unverified; the chart arithmetic is elementary and checked here by `field_simp`/`linear_combination`).

   | Literature | Lean | Match |
   |---|---|---|
   | E ⊂ ℙ², F = y²z − x³ + xz² | `ellipticCurve`, `cubicForm = X 1 ^ 2 * X 2 - X 0 ^ 3 + X 0 * X 2 ^ 2` (`plane-cubic-subscheme`) | yes |
   | E(ℂ) with the analytic topology | `ComplexPoint ellipticCurve` with upstream's `Point.analyticTopology` (probe B, `rfl`) | yes |
   | chart z ≠ 0: {(x, y) ∈ ℂ² : y² = x³ − x}, subspace topology | `ellipticAffineOpen = chartOpen 2`, `affineCurve = {p | p.2 ^ 2 = p.1 ^ 3 - p.1}` in `ℂ × ℂ` (probe C) | yes |
   | chart y ≠ 0: (u, w) = (x/y, z/y), w = u³ − uw² | `ellipticInfinityOpen = chartOpen 1`, `infinityCurve = {p | p.2 = p.1 ^ 3 - p.1 * p.2 ^ 2}` | yes: F(u, 1, w) = w − u³ + uw² |
   | the charts cover E(ℂ) | `ellipticAffineOpen_sup_ellipticInfinityOpen` from the scheme-level `ellipticCurve_chart_cover` | yes |
   | [x : y : 1] = [x/y : 1 : 1/y] for y ≠ 0 | `affinePoint_eq_infinityPoint`, `ellipticInfinityHomeomorph_of_mem` | yes |
   | [u : 1 : w] = [u/w : 1/w : 1] for w ≠ 0 | `infinityPoint_eq_affinePoint`, `ellipticAffineHomeomorph_of_mem` | yes |
   | E(ℂ) ∖ {z ≠ 0} = {O} | `compl_ellipticAffineOpen` | yes; from w = 0 the equation forces u³ = 0 |

   The ledger title promises the two homeomorphisms, the cover and the transition; the file delivers all three plus the inverse transition and the complement.

2. **The homeomorphisms are honest and pinned.** `chartHomeomorph i` is `(openHomeomorph _ _).symm`, then `isoMapHomeomorph (chartOverIso i)`, then `affineSpecHomeomorph`, then `quotAlgHomHomeomorph`. Each upstream piece is a `Homeomorph` between `analyticTopology` (or its subspace topology, `induced Subtype.val analyticTopology`) and upstream's `affineAlgebraHomTopology` (pointwise convergence, `induced` by the coercion to functions). `chartOverIso` is `Over.isoMk` of `Hypersurface.chartIso` with its square over Spec ℂ proved (`chartIso_hom_structureMap`), so the iso lies over the base. The local piece `quotAlgHomHomeomorph` is continuous in both directions by coordinate evaluation and by `MvPolynomial.continuous_eval`. The pins `ellipticAffineHomeomorph_symm_apply` and `ellipticInfinityHomeomorph_symm_apply` name the inverse as `chartComplexPoint 2 ![x, y]` and `chartComplexPoint 1 ![u, w]`, proved by `Over.OverMorphism.ext` and `rfl`; `chartComplexPoint_ι` (checked) places that point in ℙ² as Spec of evaluation followed by the port's `chart i`. A homeomorphism is determined by its inverse, so neither map can be an arbitrary homeomorphism. The coordinate order is fixed twice: `Homeomorph.finTwoArrow v = (v 0, v 1)` by `rfl` (probe D), and `affinePoint_mem_ellipticInfinityOpen_iff` reads membership in y ≠ 0 off the second coordinate through `dehomogenize_two_X_one`; the equation y² = x³ − x is not symmetric in x and y, so a swap would also fail `eval_dehomogenize_two_eq_zero_iff`.

3. **Hypotheses satisfiable; no vacuity.** The theorems take no hypotheses beyond membership. Both opens are inhabited (origin, point at infinity) and their intersection is inhabited by [i : 1 − i : 1] (probe I, from `ellipticCurveChartMeet_mem` and `ellipticCurveChartMeet_mem_ellipticInfinityOpen`). The origin and (±1, 0) lie outside y ≠ 0 and O lies outside z ≠ 0 (four tests), so neither open is the whole space.

4. **Trivial proofs fail.** On `ellipticInfinityHomeomorph_of_mem`, `rfl`, `simp` and `ext <;> simp` all fail (probe J): the identity needs the transition in ℙ², which the file proves through the port's `chart_base_evalPoint_eq` and injectivity of the closed embedding `ellipticCurveι` on points, then upstream's `underlying_injective_of_locallyOfFiniteType`. Nothing unfolds to `True`, and no `ℕ∞` or empty index type enters. Not an interface rung, so item 4 of the template does not apply.

5. **Transition direction.** u = x/y and w = z/y = 1/y at z = 1; inversely x = u/w, y = 1/w at y = 1. The chart-meet test computes i/(1 − i) = (−1 + i)/2 and 1/(1 − i) = (1 + i)/2; by hand (u, w) = ((−1 + i)/2, (1 + i)/2) has u² = −i/2, u³ = (1 + i)/4, w² = i/2, uw² = (−1 − i)/4, so u³ − uw² = (1 + i)/2 = w. The formulas (x/y, y) and (y/x, 1/x) give a different value at that point (probe F), so the test discriminates the direction.

6. **The general lemma: Mathlib and upstream neighbours, placement.** `zeroSet f` is Mathlib's `MvPolynomial.zeroLocus ℂ (Ideal.span {f})` (`RingTheory/Nullstellensatz.lean`); probe E proves the equality in eight lines. Mathlib has no topology on `AlgHom`. Upstream has `AlgebraicGeometry.ComplexPoint.mvPolynomialAlgHomHomeomorph n : (complexPolynomialRing n →ₐ[ℂ] ℂ) ≃ₜ (Fin n → ℂ)` and `standardEtalePointHomeomorph` (`Lemmas/AlgebraicGeometry/ComplexPoint/StandardEtale.lean`), the polynomial-ring and standard-étale cases; the hypersurface quotient is absent, so a local copy is justified (decision 0011). The section uses only Mathlib and upstream and compiles alone as a module at layer 0 (`QuotAlgHom.lean`). In `Tests/` it sits at layer 9 (`tools/pinwalk.py` graph: the file imports `Tests.EllipticCurveCM` at layer 8), which the #212 layout and the precedent of `elliptic-curve-cm` (its red team, item 9) both argue against. Change 1 moves it.

7. **Unused import.** `public import HodgeLadder.Tests.EllipticCurveSmooth` is not needed: the file compiles without it (`NoSmooth.lean`). `LocallyOfFiniteType ellipticCurve.hom`, which `underlying_injective_of_locallyOfFiniteType` needs, comes through the other imports. Change 2.

8. **`Other` dependency.** `underlying_injective_of_locallyOfFiniteType` lives in upstream's library `Other` (`Other/AlgebraicGeometry/ComplexPoint/ClosedImmersion.lean`), outside the statement guard. It is a two-line lemma (`Over.OverMorphism.ext` of `ext_of_apply_closedPoint_eq`, from the guarded `HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.ResidueField`). It is already on the drift list since `cycle-class-germ` (`docs/handoffs/2026-11-26-cycle-class-germ.md`), and the gaps category "Algebraic geometry and commutative algebra" already diffs `Other/AlgebraicGeometry/ComplexPoint/` at a bump. The ledger note must name it (change 4).

9. **Names.** `chartOpen`, `chartOpenScheme`, `chartOverIso`, `chartHomeomorph`, `affinePoint`, `infinityPoint` are generic names for objects specific to E in `HodgeLadder.Tests`. There is no clash at the pin: the port's `chartOpen` is `ComplexAnalytic.AnalyticSpace.chartOpen`, and `chartComplexPoint` in the same namespace is the precedent. Recorded only; no change required.

10. **Fit with `elliptic-curve-uniformization` (C3).** Mathlib states `derivWeierstrassP_sq : ℘'[L] z ^ 2 = 4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃` with `g₂ = 60 G₄`, `g₃ = 140 G₆`. With g₂ = 4, g₃ = 0, (℘'/2)² = ℘³ − ℘, so (℘ z, ℘' z / 2) lies on `affineCurve` in exactly this file's coordinates (probe G), and Φ z = `affinePoint ⟨(℘ z, ℘' z / 2), _⟩` off Λ. Near Λ, `affinePoint_eq_infinityPoint` gives Φ z = `infinityPoint (2℘/℘', 2/℘')` (probe H), and both coordinates tend to 0 = the coordinates of O (`ellipticInfinityHomeomorph_infinity`), so continuity at Λ reduces to ℘/℘' → 0 and 1/℘' → 0, facts about the poles of ℘ that this rung does not supply. What C3 still needs beyond this rung: (a) those two limits; (b) `CompactSpace (ℂ ⧸ L.lattice.toAddSubgroup)`, which Mathlib does not infer at the pin (Mathlib's `IsZLattice.isCompact_range_of_periodic` is the likely route); (c) bijectivity from `weierstrass-two-to-one`. The target side is in place: E(ℂ) is compact (upstream instance) and Hausdorff (`ellipticCurve_t2Space`), every point of z ≠ 0 is `affinePoint` of its coordinates (`eq_affinePoint`), and the only other point is O (`compl_ellipticAffineOpen`). The open-embedding forms of the chart inverses (change 6) save C3 the composition with `Subtype.val`.

11. **Fit with D5 (by hand, not checked in Lean).** In the chart y ≠ 0 the form dx/y is (w du − u dw)/w; on w = u³ − uw², (1 + 2uw) dw = (3u² − w²) du and u/w = u⁻²(1 + O(u⁴)), so dx/y = (−2 + O(u)) du, holomorphic and nonzero at O. With u = 2℘/℘' = −z + O(z³) near 0, this agrees with dx/y = 2 dz. Recorded for `elliptic-curve-holomorphic-form` route (a).

12. **Conventions.** Coordinates x = X 0, y = X 1, z = X 2; chart z ≠ 0 is `dehomogenize 2` with (X 0, X 1) ↦ (x, y) via `Fin.succAbove 2`; chart y ≠ 0 is `dehomogenize 1` with (X 0, X 1) ↦ (u, w) = (x/y, z/y) via `Fin.succAbove 1`; `Homeomorph.finTwoArrow` puts `v 0` first. All are already in row "Plane cubic E and its charts" except the point-level statements of this rung, which change 5 adds. No sign, orientation or scalar enters any statement here. The truth of every theorem in the file is an identity of points or coordinates, so a swapped coordinate order or a wrong transition would make it false (probes D, F); the CM sign of row "Complex multiplication on E" is not used.

13. **Equality first.** The chart identities, the transition and the complement are exact equalities; no inclusion or scalar is involved.

14. **Non-vacuity test.** The smallest test that fails if the transition were trivially true or the overlap empty is `HodgeLadder.Tests.ellipticInfinityHomeomorph_chartMeet` (exists, standard axioms); for the cover and complement, `HodgeLadder.Tests.ellipticCurveInfinity_not_mem_ellipticAffineOpen` with `compl_ellipticAffineOpen` (both exist).

15. **Pin drift.** Base and candidate share the pin `2ead713`; nothing to diff. At a future bump, the definitions this rung reads are upstream `Point.analyticTopology`, `chartTopology`, `isoMapHomeomorph` (`Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean`), `openScheme`, `openHomeomorph` (`Lemmas/.../ComplexPoint/Open.lean`), `affineAlgebraHomTopology`, `affineSpecHomeomorph`, `continuous_affineAlgebraHom_apply` (`Lemmas/.../ComplexPoint/AffineScheme.lean`), and `underlying_injective_of_locallyOfFiniteType` (`Other`). A change of the affine topology from pointwise convergence would break `quotAlgHomHomeomorph`'s proofs, which is the right failure; `chartHomeomorph_symm_apply` by `rfl` breaks if `affineSpecEquiv` or `openEquiv` changes its underlying map.

## Required changes

1. **Move the general lemma.** Create `HodgeLadder/General/QuotAlgHom.lean` with the `ZeroSet` section of the candidate verbatim (with `ComplexPoint.continuous_affineAlgebraHom_apply` spelled `AlgebraicGeometry.ComplexPoint.continuous_affineAlgebraHom_apply`), under this header, and close it with `end HodgeLadder.QuotAlgHom`:

   ```lean
   module

   public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
   public import Mathlib.Topology.Algebra.MvPolynomial

   /-!
   # Complex points of a hypersurface quotient

   Complex algebra homomorphisms out of `ℂ[Y₁, …, Yₙ] ⧸ (f)`, with upstream's topology of
   pointwise convergence (`AlgebraicGeometry.ComplexPoint.affineAlgebraHomTopology`), are the
   zeros of `f` with the subspace topology of `ℂⁿ`. Upstream's `mvPolynomialAlgHomHomeomorph` is
   the case `f = 0` without the quotient.

   ## Main definitions

   * `HodgeLadder.QuotAlgHom.zeroSet`: `{v ∈ ℂⁿ : f(v) = 0}`.
   * `HodgeLadder.QuotAlgHom.quotAlgHomHomeomorph`: `(ℂ[Y] ⧸ (f) →ₐ[ℂ] ℂ) ≃ₜ zeroSet f`.
   -/

   @[expose] public noncomputable section

   open MvPolynomial

   namespace HodgeLadder.QuotAlgHom
   ```

   In `HodgeLadder/Tests/EllipticCurvePoints.lean`, delete the `ZeroSet` section, add `public import HodgeLadder.General.QuotAlgHom`, add `HodgeLadder.QuotAlgHom` to the `open` line, and change the module docstring bullet to "`HodgeLadder.QuotAlgHom.zeroSet`, `quotAlgHomHomeomorph` (`HodgeLadder.General.QuotAlgHom`): zeros of `f` and algebra homomorphisms out of `ℂ[Y] ⧸ (f)`." Add `public import HodgeLadder.General.QuotAlgHom` and `public import HodgeLadder.Tests.EllipticCurvePoints` to `HodgeLadder.lean`. Do not follow `next.py`'s fallback path `HodgeLadder/Elliptic/Curve/Points.lean`.

2. **Drop the unused import** `public import HodgeLadder.Tests.EllipticCurveSmooth` from `HodgeLadder/Tests/EllipticCurvePoints.lean`.

3. **Gaps row.** In `docs/gaps.md`, category "Algebraic geometry and commutative algebra", insert after the `HodgeLadder.General.ComplexPointProd` row (layer 0) and before the `HodgeLadder.General.ProjQuotient` row:

   ```
   | `HodgeLadder.QuotAlgHom.zeroSet`, `quotAlgHomCoord`, `quotAlgHomOfZero`, `quotAlgHomOfZero_mk`, `quotAlgHomHomeomorph` (complex algebra homomorphisms out of ℂ[Y₁, …, Yₙ] ⧸ (f), with upstream's topology of pointwise convergence `affineAlgebraHomTopology`, are the zeros of f with the subspace topology of ℂⁿ) | `HodgeLadder.General.QuotAlgHom` | 0 | Mathlib has the zero set as `MvPolynomial.zeroLocus ℂ (Ideal.span {f})` (`RingTheory/Nullstellensatz.lean`, equal to `zeroSet f` in eight lines, red team) and no topology on `AlgHom`; upstream has `mvPolynomialAlgHomHomeomorph` and `standardEtalePointHomeomorph` (`Lemmas/AlgebraicGeometry/ComplexPoint/StandardEtale.lean`), the polynomial-ring and standard-étale cases, and no quotient by a hypersurface; the torus file's `gmAlgHomHomeomorph` (`HodgeLadder.Tests.AlgebraicTorusPoints`) is the same argument for a localization; at a pin bump check Mathlib `RingTheory/Nullstellensatz.lean` and upstream `Lemmas/AlgebraicGeometry/ComplexPoint/{AffineScheme,StandardEtale}.lean` for a homeomorphism of complex points of `Spec (ℂ[Y] ⧸ I)`; rung `elliptic-curve-points` | 2026-11-28 |
   ```

4. **Ledger entry** `elliptic-curve-points`: `"status": "checked"`, `"module": "HodgeLadder.Tests.EllipticCurvePoints"`, `"contributors": ["claude-code"]`, `"declarations"`:

   ```
   "HodgeLadder.QuotAlgHom.zeroSet", "HodgeLadder.QuotAlgHom.quotAlgHomOfZero_mk", "HodgeLadder.QuotAlgHom.quotAlgHomHomeomorph",
   "HodgeLadder.Tests.chartOpen", "HodgeLadder.Tests.chartOverIso", "HodgeLadder.Tests.chartHomeomorph",
   "HodgeLadder.Tests.chartHomeomorph_symm_apply", "HodgeLadder.Tests.chartComplexPoint_mem_chartOpen_iff",
   "HodgeLadder.Tests.chartOpen_two_sup_one", "HodgeLadder.Tests.chartComplexPoint_dehomogenizeVec_eq",
   "HodgeLadder.Tests.affineCurve", "HodgeLadder.Tests.infinityCurve",
   "HodgeLadder.Tests.ellipticAffineOpen", "HodgeLadder.Tests.ellipticInfinityOpen",
   "HodgeLadder.Tests.ellipticAffineHomeomorph", "HodgeLadder.Tests.ellipticInfinityHomeomorph",
   "HodgeLadder.Tests.affinePoint", "HodgeLadder.Tests.infinityPoint",
   "HodgeLadder.Tests.ellipticAffineHomeomorph_symm_apply", "HodgeLadder.Tests.ellipticInfinityHomeomorph_symm_apply",
   "HodgeLadder.Tests.eq_affinePoint", "HodgeLadder.Tests.eq_infinityPoint",
   "HodgeLadder.Tests.ellipticAffineOpen_sup_ellipticInfinityOpen",
   "HodgeLadder.Tests.affinePoint_eq_infinityPoint", "HodgeLadder.Tests.infinityPoint_eq_affinePoint",
   "HodgeLadder.Tests.mem_ellipticInfinityOpen_iff", "HodgeLadder.Tests.ellipticInfinityHomeomorph_of_mem",
   "HodgeLadder.Tests.mem_ellipticAffineOpen_iff", "HodgeLadder.Tests.ellipticAffineHomeomorph_of_mem",
   "HodgeLadder.Tests.compl_ellipticAffineOpen",
   "HodgeLadder.Tests.ellipticAffineHomeomorph_origin", "HodgeLadder.Tests.ellipticInfinityHomeomorph_infinity",
   "HodgeLadder.Tests.ellipticAffineHomeomorph_twoTorsionPos", "HodgeLadder.Tests.ellipticAffineHomeomorph_twoTorsionNeg",
   "HodgeLadder.Tests.ellipticAffineHomeomorph_chartMeet", "HodgeLadder.Tests.ellipticInfinityHomeomorph_chartMeet",
   "HodgeLadder.Tests.ellipticCurveInfinity_not_mem_ellipticAffineOpen",
   "HodgeLadder.Tests.ellipticCurveOrigin_not_mem_ellipticInfinityOpen"
   ```

   plus `isOpenEmbedding_affinePoint` and `isOpenEmbedding_infinityPoint` if change 6 is taken, and `"note"`:

   > Checked 2026-11-28. Plan: docs/notes/2026-11-27-t1-plan.md, node C0. Each chart homeomorphism is upstream's openHomeomorph (inverse), isoMapHomeomorph of chartOverIso (Hypersurface.chartIso over Spec ℂ), affineSpecHomeomorph and the general quotAlgHomHomeomorph ((ℂ[Y] ⧸ (f) →ₐ[ℂ] ℂ) ≃ₜ {v : f(v) = 0}, pointwise convergence against the subspace topology of ℂⁿ; HodgeLadder.General.QuotAlgHom), then Homeomorph.finTwoArrow; pinned by its inverse, (x, y) ↦ chartComplexPoint 2 ![x, y] = [x : y : 1] and (u, w) ↦ [u : 1 : w]. The cover from ellipticCurve_chart_cover; the transition (x, y) ↦ (x/y, 1/y) on y ≠ 0 and (u, w) ↦ (u/w, 1/w) on w ≠ 0, read in ℙ² through the port's chart_base_evalPoint_eq and upstream's underlying_injective_of_locallyOfFiniteType (library Other, Other/AlgebraicGeometry/ComplexPoint/ClosedImmersion.lean; on the drift list); the complement of z ≠ 0 is {[0 : 1 : 0]}. Tests: the origin, (±1, 0) and (i, 1 − i) in z ≠ 0, [0 : 1 : 0] = (0, 0) in y ≠ 0, (i, 1 − i) ↦ ((−1 + i)/2, (1 + i)/2). For C3: (℘, ℘'/2) lies on y² = x³ − x when g₂ = 4, g₃ = 0. No sign. Red team: pass with changes (docs/sketches/elliptic-curve-points.redteam.md).

   Add the row to `docs/roadmap.md` as the propagation map says.

5. **Conventions row** "Plane cubic E and its charts" in `docs/conventions.md`. Append to the "Fixed where" cell: `; `affineCurve`, `infinityCurve`, `ellipticAffineHomeomorph`, `ellipticInfinityHomeomorph`, `affinePoint`, `infinityPoint`, `compl_ellipticAffineOpen` (`HodgeLadder/Tests/EllipticCurvePoints.lean`, rung `elliptic-curve-points`); `HodgeLadder.QuotAlgHom.quotAlgHomHomeomorph`; upstream `openHomeomorph`, `affineSpecHomeomorph`, `Point.analyticTopology``. Append to the "Choice" cell: `; on complex points the chart z ≠ 0 is (x, y) = (v 0, v 1) ∈ {y² = x³ − x} ⊂ ℂ × ℂ (`Homeomorph.finTwoArrow`, `X 0` first) and the chart y ≠ 0 is (u, w) ∈ {w = u³ − uw²}, both with the subspace topology of ℂ × ℂ against upstream's analytic topology; the inverses are (x, y) ↦ [x : y : 1] and (u, w) ↦ [u : 1 : w]; transition (x, y) ↦ (x/y, 1/y) on y ≠ 0, inverse (u, w) ↦ (u/w, 1/w) on w ≠ 0; the complement of z ≠ 0 is {[0 : 1 : 0]}`. Replace "also C0 `elliptic-curve-points` (the chart equations)" in the "Results" cell by: `also C0 `elliptic-curve-points` (every theorem is an identity of points or coordinates: a swapped coordinate order or the transition (y/x, 1/x) makes it false); in C3, Φ z = `affinePoint (℘ z, ℘' z / 2)` off Λ and `infinityPoint (2℘/℘', 2/℘')` near Λ, tending to (0, 0) = O`. Append to the "Status" cell: `; chart homeomorphisms read from source, the analytic topology, the subspace topology and the `finTwoArrow` order by `rfl`, wrong transitions rejected at (i, 1 − i), in scratch (red team 2026-11-28, `elliptic-curve-points`)`.

6. **Optional, for C3.** Add after `ellipticInfinityHomeomorph_symm_apply` (checked in scratch, standard axioms):

   ```lean
   /-- `(x, y) ↦ [x : y : 1]` is an open embedding of the affine curve into `E(ℂ)`. -/
   theorem isOpenEmbedding_affinePoint : Topology.IsOpenEmbedding affinePoint := by
     have h : affinePoint = (Subtype.val : ellipticAffineOpen → ComplexPoint ellipticCurve) ∘
         ellipticAffineHomeomorph.symm :=
       funext fun p => (ellipticAffineHomeomorph_symm_apply p).symm
     rw [h]
     exact ellipticAffineOpen.isOpen.isOpenEmbedding_subtypeVal.comp
       ellipticAffineHomeomorph.symm.isOpenEmbedding

   /-- `(u, w) ↦ [u : 1 : w]` is an open embedding of the curve at infinity into `E(ℂ)`. -/
   theorem isOpenEmbedding_infinityPoint : Topology.IsOpenEmbedding infinityPoint := by
     have h : infinityPoint = (Subtype.val : ellipticInfinityOpen → ComplexPoint ellipticCurve) ∘
         ellipticInfinityHomeomorph.symm :=
       funext fun q => (ellipticInfinityHomeomorph_symm_apply q).symm
     rw [h]
     exact ellipticInfinityOpen.isOpen.isOpenEmbedding_subtypeVal.comp
       ellipticInfinityHomeomorph.symm.isOpenEmbedding
   ```

7. **Record for C3** (no change to this rung). Add to the note of `elliptic-curve-uniformization`: "Needs CompactSpace (ℂ ⧸ L.lattice.toAddSubgroup), not inferred at the pin (route: Mathlib's IsZLattice.isCompact_range_of_periodic), and ℘/℘' → 0, 1/℘' → 0 at Λ for continuity in the chart y ≠ 0 (red team of elliptic-curve-points, finding 10)."

After changes 1 to 5, rerun `python3 tools/check.py` (full build, since the root import changes); the new declarations then enter the checker's axiom step.
