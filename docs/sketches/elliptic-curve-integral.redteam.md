# Red team: `elliptic-curve-integral` (foundation, issue #253, T1 node E3) and `elliptic-curve-witness` (test, T1 node E4)

Date: 2026-11-28. Worktree `elliptic-curve-integral`, branch `track/elliptic-curve-integral`, candidate commit `8cc70fe` on base `0fd3685`. Upstream pin `2ead713` (unchanged on the branch and on `main`). File: `HodgeLadder/Tests/EllipticCurveIntegral.lean` (329 lines, namespace `HodgeLadder.Tests`).

**Verdict, `elliptic-curve-integral`: pass with changes.** The mathematics is right and the instance is honest: both chart rings are domains, the scheme is reduced from a genuine open cover, and irreducible from a point lying in both charts. The changes: use Mathlib's bivariate equivalence in place of a local copy, add the density statement the ledger title promises, correct one docstring sentence about where the sign enters, complete the ledger declaration list, and extend the conventions row.

**Verdict, `elliptic-curve-witness`: pass (statement and proof).** Every hypothesis of upstream's `HodgeConjecture` is found by instance search at `ellipticCurve`; the file text in change 7 compiles against the branch with the standard three axioms on all eleven declarations. Add it as `checked` in phase 2 with the ledger entry of change 8.

Read: ledger entries `plane-cubic-subscheme`, `elliptic-curve-smooth`, `elliptic-curve-cm`, `elliptic-curve-integral`, `elliptic-curve-witness`, `p2-witness`; `python3 tools/next.py` for both rungs; `docs/notes/2026-11-27-t1-plan.md` nodes E3, E4; `docs/sketches/plane-cubic-subscheme.redteam.md`, `elliptic-curve-smooth.redteam.md`, `elliptic-curve-cm.redteam.md`; `HodgeLadder/Tests/{EllipticCurve,EllipticCurveSmooth,EllipticCurveCM,P1p1Witness,ProjectivePlane,CodimensionZero}.lean`; upstream `HodgeConjecture/Statement.lean`, `Variants.lean`, `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean`, `Lemmas/AlgebraicGeometry/ComplexPoint/{ProjectiveHausdorff,ProjectiveParacompact}.lean`, `Other/AlgebraicGeometry/Hodge/CodimensionZero{Comparison,Nonvanishing}.lean`; Mathlib `Algebra/Polynomial/{SpecificDegree,Bivariate}.lean`; `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`.

Scratch (directory `.redteam-eci-probe/` in the worktree, deleted afterwards):

| File | What it tried | Result |
|---|---|---|
| `Before.lean` | `inferInstance` for `IsIntegral ellipticCurve.left` importing `EllipticCurveSmooth` and `EllipticCurveCM` only | fails to synthesize |
| `Same.lean` | `#synth` for `T2Space (ComplexPoint ellipticCurve)`, `IsIntegral ellipticCurve.left`, `Smooth`, `SmoothOfRelativeDimension 1`, `IsProjective` | found as upstream's `IsProjective.complexPoint_t2Space` and the ladder's `isIntegral_ellipticCurve`, `smooth_ellipticCurve`, `smoothOfRelativeDimension_ellipticCurve`, `isProjective_ellipticCurve` |
| `Same.lean` | `ellipticCurveChartMeet = ellipticCurvePointI := rfl` | compiles |
| `Same.lean` | the root check of `sq_ne_X_pow_three_sub_X` for y² = x³ + x, same proof text with the sign of two terms changed | compiles: the domain argument is insensitive to the sign of the linear term |
| `Same.lean` | `¬ Irreducible (X ^ 2 - C (X ^ 2) : ℂ[X][X])` (the reducible conic y² − x²) | compiles: the monic-with-no-root criterion has content |
| `Equiv2.lean` | Mathlib's `(Polynomial.Bivariate.equivMvPolynomial ℂ).symm` and its rename-swap composite against `bivariateEquivSwap`, `bivariateEquiv` | equal by `MvPolynomial.algHom_ext`; the four variable lemmas close by `simp` |
| `IntegralAlt.lean` | the candidate file with changes 1, 2 applied (Mathlib equivalence, `dense_ellipticAffineChart`) | compiles; `#print axioms` on `isIntegral_ellipticCurve`, `dense_ellipticAffineChart`, `irreducible_infinityEquation`: `[propext, Classical.choice, Quot.sound]` |
| `EllipticCurveWitness.lean`, `W3.lean` | the file of change 7 and `#print axioms` for its eleven declarations | compiles in about 22 s; all eleven `[propext, Classical.choice, Quot.sound]` |

`python3 tools/check.py --no-build` on the candidate: `ACCEPTED: all checks passed`, no sorry, the eighteen ledger declarations each `[Classical.choice, Quot.sound, propext]`.

## 1. The statement against the literature

`IsIntegral` is Mathlib's: nonempty, and every nonempty open has a domain of sections; equivalent to reduced plus irreducible (`isIntegral_of_irreducibleSpace_of_isReduced`), the definition of an integral scheme in [`Hartshorne1977`, II.3, locator unverified]. The object is `ellipticCurve.left`, which reduces to `ellipticCurveScheme = Hypersurface.scheme cubicForm`, the scheme whose structure morphism upstream's `HodgeConjecture` takes as `X.hom`. Field by field:

| Literature | Lean | Match |
|---|---|---|
| E = V₊(y²z − x³ + xz²) ⊂ ℙ²_ℂ | `ellipticCurve`, `cubicForm = X 1 ^ 2 * X 2 - X 0 ^ 3 + X 0 * X 2 ^ 2` | yes (plane-cubic-subscheme, red-teamed) |
| E integral | `instance isIntegral_ellipticCurve : IsIntegral ellipticCurve.left` | yes |
| chart z ≠ 0 ring ℂ[x, y]/(y² − x³ + x) a domain | `isDomain_affineChartRing` on `MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation}`, `affineEquation = X 1 ^ 2 - X 0 ^ 3 + X 0` | yes |
| chart y ≠ 0 ring ℂ[u, w]/(w − u³ + uw²) a domain | `isDomain_infinityChartRing`, `infinityEquation = X 1 - X 0 ^ 3 + X 0 * X 1 ^ 2` | yes |
| chart z ≠ 0 dense | proved inside `irreducibleSpace_of_cover` (`h1`, `h2` of its proof) and stated nowhere | add `dense_ellipticAffineChart` (change 2) |

The two chart rings are the rings the chart isomorphisms `ellipticCurveChartAffine`, `ellipticCurveChartInfinity` of `plane-cubic-subscheme` land on (their types name `Ideal.span {affineEquation}` and `Ideal.span {infinityEquation}` literally), so `isIntegral_of_isOpenImmersion ...hom` transports the right fact.

## 2. Hypotheses satisfiable

The rung has no hypotheses. Its instance is consumed at `ellipticCurve` by `hodgeConjecture_ellipticCurve` and `lefschetzOneOne_ellipticCurve` of change 7, which compile.

## 3. Trivial truth

`IsIntegral` carries `Nonempty`, so no empty-scheme escape exists; `nonempty_ellipticCurve` (plane-cubic-subscheme) and the chart instances `nonempty_ellipticAffineChart`, `nonempty_ellipticInfinityChart` (a point of the spectrum of a nonzero ring) supply it honestly. `inferInstance` for `IsIntegral ellipticCurve.left` with only `EllipticCurveSmooth` and `EllipticCurveCM` imported fails to synthesize (`Before.lean`): nothing in Mathlib, upstream or the earlier rungs supplies it, and the smooth red team recorded `IsIntegral` as the only instance `HodgeConjecture` still lacked at `ellipticCurve`. The integrality argument is a real one.

By hand:

- Affine chart. In ℂ[x][y], y² − (x³ − x) is monic of degree two, so it is irreducible iff it has no root in ℂ[x] (`Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`, which needs only a domain: a factorization of a monic polynomial has unit leading coefficients, so a nontrivial one has a linear factor). A root r has r² = x³ − x = x(x − 1)(x + 1), squarefree and nonconstant, impossible; the Lean proof runs it at 0 (r(0) = 0, r = xs, x(xs² − x² + 1) = 0, the second factor is 1 at 0). Correct.
- Infinity chart. w − u³ + uw² = −(u³ − w²u − w), monic cubic in u over ℂ[w] after the unit −1. A root r ∈ ℂ[w] has r(0)³ = 0, so r = ws and w(w²s³ − w²s − 1) = 0, the second factor −1 at 0. Correct. `bivariateEquiv_infinityEquation` matches the sign: −(u³ − w²u − w) = w − u³ + uw².
- The transfer MvPolynomial (Fin 2) ℂ ≃ ℂ[X][X] (`MulEquiv.irreducible_iff`) and irreducible ⇒ prime in the UFD `MvPolynomial (Fin 2) ℂ` (`UniqueFactorizationMonoid.irreducible_iff_prime`) are standard; `Ideal.span_singleton_prime` needs the element nonzero, from irreducibility.
- Reduced. `IsReduced.of_openCover` over `openCoverOfIsOpenCover` of the Bool family {z ≠ 0, y ≠ 0}; the cover is `ellipticCurve_chart_cover` (on E, x = y = 0 forces z = 0, so the two charts cover). Each chart is integral, hence reduced.
- Irreducible. `irreducibleSpace_of_cover` with U = chart z ≠ 0 open and irreducible, the two charts irreducible and covering, and each meeting U. The meeting point is (i, 1 − i): (1 − i)² = −2i = i³ − i, and y = 1 − i ≠ 0 (`ellipticCurveChartMeet_mem_infinityChart` uses the real part). In ℙ² it is [i : 1 − i : 1], with z = 1 and y ≠ 0.

## 4. Interface rung

Not an interface rung; no structure, no axioms.

## 5. Checker

`python3 tools/check.py --no-build`: accepted; axioms line for each of the eighteen named declarations is the standard three. The named declarations are the ones the ledger means. Unnamed but load-bearing: `ellipticAffineChart`, `ellipticInfinityChart`, `ellipticCurveChartMeet`, `eval_chartMeet`, `bivariateEquivSwap_affineEquation`, `bivariateEquiv_infinityEquation`, `sq_ne_X_pow_three_sub_X`, `pow_three_sub_X_sq_mul_sub_X_ne_zero`, the four `bivariateEquiv*_X_*` lemmas, `nonempty_ellipticAffineChart`, `nonempty_ellipticInfinityChart`. Change 4 adds the ones a downstream rung or a reader would cite.

## 6. Conventions

| Convention | Used how | Truth depends on it |
|---|---|---|
| Sign of the linear term of E (row "Plane cubic E and its charts") | the curve; the root checks at 0; the chart point (i, 1 − i) | no: integrality holds for y² = x³ ± x (root check recompiled for y² = x³ + x). The proof text depends on it at one place: (i, 1 − i) is on y² = x³ − x and off y² = x³ + x (there i³ + i = 0 ≠ −2i), so a flip of the sign in `cubicForm` breaks `eval_chartMeet` at build time |
| Variable order of the two `Polynomial (Polynomial ℂ)` transports (`bivariateEquiv`: X 0 outer; `bivariateEquivSwap`: X 1 outer) | which variable the polynomial is monic in | no: an internal choice, checked by the four variable lemmas; the wrong order would make `affineEquation` non-monic of degree three in x, still irreducible, and the proof would fail to typecheck |
| Chart coordinates (u, w) = (x/y, z/y) on y ≠ 0 | `infinityEquation` | no, as above |

The module docstring says "The domain proofs use the sign of the linear term only in the root checks at `0`". The root checks are sign-free; the sign enters only `eval_chartMeet`. Change 3 corrects it. Change 5 extends the conventions row. No cited input, no scalar, no orientation.

## 7. Equality first

Not an identity or an inclusion: a property instance (integrality) feeding a witness. The equalities it serves: `hodge_eq_span_zero_ellipticCurve` (codimension zero, in change 7) and, later, the T1 chain at E.

## 7b. Non-vacuity

The smallest test that would fail if `IsIntegral ellipticCurve.left` were obtained vacuously is upstream's `AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass_genericPoint_ne_zero` at `ellipticCurve` (the class of E at `genericPoint ellipticCurve.left`, which exists only for an irreducible nonempty scheme, is nonzero); it is `ellipticCurve_fundamentalClass_ne_zero` of change 7 and compiles. On the algebra side, `¬ Irreducible (X ^ 2 - C (X ^ 2))` compiled in scratch shows the criterion used is no tautology; not proposed for the tree.

## 8. Pin drift

Branch and `main` share the pin (`git diff main -- lakefile.toml lake-manifest.json lean-toolchain` is empty). `main` has moved two commits (`eb665a1`, `8e84167`) since the base `0fd3685`; they touch `HodgeLadder.lean` (tail of the import list), `ledger/ladder.json`, `docs/roadmap.md`, `docs/conventions.md`, `docs/gaps.md`, and introduce none of this rung's names. Rebase before merge and expect textual conflicts at those tails only. No definition this rung depends on changed.

## 9. Reuse of `ellipticCurvePointI`

`ellipticCurveChartMeet` and `ellipticCurvePointI` (`elliptic-curve-cm`) are the same term up to the proof of the equation (`rfl` closes the equality). Keep them independent: importing `EllipticCurveCM` into the integral file would pull `HodgeLadder.General.ProjQuotientMap` and the port's `LinearSubst` into the integrality closure, and `elliptic-curve-integral` and `elliptic-curve-cm` are siblings in the plan. Record the identity once, in the witness file, which imports both (`ellipticCurveChartMeet_eq_pointI`, change 7). `EllipticCurveSmooth.affineEquation_eval_I` is a third statement of the same point equation; leave it.

## Findings

1. Both irreducibility arguments are correct by hand and in Lean; the change of variables matches the chart equations and their signs.
2. `IsIntegral` is honest: reduced from a real two-chart open cover, irreducible from irreducible charts that cover and meet at (i, 1 − i); nonemptiness comes from points, with no vacuous instance.
3. `bivariateEquivSwap` duplicates Mathlib's `Polynomial.Bivariate.equivMvPolynomial` (inverted), at the pin in `Mathlib/Algebra/Polynomial/Bivariate.lean`; `bivariateEquiv` is that plus a variable swap. CLAUDE.md and decision 0011 ask for what Mathlib has before a local copy.
4. The ledger title promises "the chart z ≠ 0 is dense"; no declaration states it.
5. The module docstring misplaces the sign dependence (section 6).
6. The ledger declaration list omits the chart opens, the meeting point and the root lemmas.
7. No new general lemma is claimed and, after change 1, none exists: `docs/gaps.md` needs no row. The root lemmas are specific to this curve.
8. No test in this file depends on the sign of the curve for its truth; one proof step depends on it for its text (`eval_chartMeet`), a build-time pin worth recording.
9. Witness: all one-liners elaborate; upstream's `HodgeConjecture` hypotheses `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]` are met at `ellipticCurve` by the instances listed in the scratch table, exactly. `TopologicalSpace.dim ellipticCurve.left = 1` and uniqueness of the relative dimension follow from upstream's `SmoothOfRelativeDimension.dim_eq`. The ledger's derived path for the witness is `HodgeLadder/Elliptic/Curve/Witness.lean` (`next.py` fallback); the precedent of the three sibling red teams puts it in `HodgeLadder/Tests/`.
10. Placement of the integral file in `HodgeLadder/Tests/` matches its siblings and namespace.

## Required changes

1. In `HodgeLadder/Tests/EllipticCurveIntegral.lean`, add `public import Mathlib.Algebra.Polynomial.Bivariate` after the `SpecificDegree` import, and replace the body of `section Bivariate` (from the docstring of `bivariateEquiv` to the line before `end Bivariate`) by:

   ```lean
   /-- The ring isomorphism `ℂ[x, y] ≅ ℂ[x][y]`, `x = X 0 ↦ C X`, `y = X 1 ↦ Polynomial.X`: Mathlib's
   `Polynomial.Bivariate.equivMvPolynomial`, inverted. -/
   def bivariateEquivSwap : MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] Polynomial (Polynomial ℂ) :=
     (Polynomial.Bivariate.equivMvPolynomial ℂ).symm

   /-- `bivariateEquivSwap` sends `x = X 0` to the inner variable. -/
   theorem bivariateEquivSwap_X_zero : bivariateEquivSwap (X 0) = Polynomial.C Polynomial.X := by
     simp [bivariateEquivSwap]

   /-- `bivariateEquivSwap` sends `y = X 1` to the outer variable. -/
   theorem bivariateEquivSwap_X_one : bivariateEquivSwap (X 1) = Polynomial.X := by
     simp [bivariateEquivSwap]

   /-- The ring isomorphism `ℂ[u, w] ≅ ℂ[w][u]`, `u = X 0 ↦ Polynomial.X`, `w = X 1 ↦ C X`: swap
   the variables, then `bivariateEquivSwap`. -/
   def bivariateEquiv : MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] Polynomial (Polynomial ℂ) :=
     (renameEquiv ℂ (Equiv.swap 0 1)).trans bivariateEquivSwap

   /-- `bivariateEquiv` sends `u = X 0` to the outer variable. -/
   theorem bivariateEquiv_X_zero : bivariateEquiv (X 0) = Polynomial.X := by
     simp [bivariateEquiv, bivariateEquivSwap]

   /-- `bivariateEquiv` sends `w = X 1` to the inner variable. -/
   theorem bivariateEquiv_X_one : bivariateEquiv (X 1) = Polynomial.C Polynomial.X := by
     simp [bivariateEquiv, bivariateEquivSwap]
   ```

   The rest of the file is unchanged (compiled in scratch as `IntegralAlt.lean`). In the module docstring, change the first algebra bullet's "Under `ℂ[x, y] ≅ ℂ[x][y]`" to "Under `ℂ[x, y] ≅ ℂ[x][y]` (Mathlib's `Polynomial.Bivariate.equivMvPolynomial`)".

2. In the same file, between `irreducibleSpace_ellipticCurveScheme` and `isIntegral_ellipticCurveScheme`, add:

   ```lean
   /-- The chart `z ≠ 0` is dense in `E`. -/
   theorem dense_ellipticAffineChart : Dense (ellipticAffineChart : Set ellipticCurveScheme) :=
     ellipticAffineChart.isOpen.dense
       ⟨_, ellipticCurveChartMeet_mem_affineChart (Classical.arbitrary (Spec ↧ℂ))⟩
   ```

   and add `` `HodgeLadder.Tests.dense_ellipticAffineChart` `` to "Main results".

3. In the module docstring, replace the paragraph "No sign convention enters this file. The domain proofs use the sign of the linear term only in the root checks at `0` (`x³ − x` and `w² u + w` vanish there to order one); the curve is recorded in `docs/conventions.md`, row "Plane cubic E and its charts"." by:

   "No sign convention enters the truth of this file: integrality holds for y² = x³ ± x, and the root checks at `0` are the same for either sign. The sign enters one proof step: the meeting point `(i, 1 − i)` lies on y² = x³ − x and off y² = x³ + x, so `eval_chartMeet` fails to build if the linear term of `cubicForm` changes sign. The curve is recorded in `docs/conventions.md`, row "Plane cubic E and its charts"."

4. In `ledger/ladder.json`, entry `elliptic-curve-integral`, append to `declarations`: `"HodgeLadder.Tests.dense_ellipticAffineChart"`, `"HodgeLadder.Tests.ellipticAffineChart"`, `"HodgeLadder.Tests.ellipticInfinityChart"`, `"HodgeLadder.Tests.ellipticCurveChartMeet"`, `"HodgeLadder.Tests.eval_chartMeet"`, `"HodgeLadder.Tests.bivariateEquivSwap_affineEquation"`, `"HodgeLadder.Tests.bivariateEquiv_infinityEquation"`, `"HodgeLadder.Tests.sq_ne_X_pow_three_sub_X"`, `"HodgeLadder.Tests.pow_three_sub_X_sq_mul_sub_X_ne_zero"`. In `note`, replace "under ℂ[x, y] ≅ ℂ[x][y]" by "under ℂ[x, y] ≅ ℂ[x][y] (Mathlib's Polynomial.Bivariate.equivMvPolynomial)", replace "No sign convention enters." by "The chart z ≠ 0 is dense (dense_ellipticAffineChart). No sign convention enters the truth; (i, 1 − i) pins the sign of the linear term at build time.", and append " Red team: pass with changes (docs/sketches/elliptic-curve-integral.redteam.md)."

5. In `docs/conventions.md`, row "Plane cubic E and its charts": in column "Fixed where", after "(`HodgeLadder/Tests/EllipticCurve.lean`, rung `plane-cubic-subscheme`);" insert " `ellipticAffineChart`, `ellipticInfinityChart`, `ellipticCurveChartMeet` (`HodgeLadder/Tests/EllipticCurveIntegral.lean`, rung `elliptic-curve-integral`);". In column "Choice", append "; `ellipticCurveChartMeet` is [i : 1 − i : 1], the same point as `ellipticCurvePointI`, on y² = x³ − x and off y² = x³ + x (i³ + i = 0 ≠ (1 − i)² = −2i)". In column "Status", append "; E3 root checks recompiled for y² = x³ + x and the reducible y² − x² rejected by the same criterion, in scratch (red team 2026-11-28, `elliptic-curve-integral`)".

6. Rebase `track/elliptic-curve-integral` onto `main` (`8e84167` or later) before merging; resolve the tails of `HodgeLadder.lean`, `ledger/ladder.json`, `docs/roadmap.md` by keeping both sides. Rerun `python3 tools/check.py`.

7. Phase 2, rung `elliptic-curve-witness`: add `HodgeLadder/Tests/EllipticCurveWitness.lean` with exactly this text (compiled in scratch against the branch; with change 1 applied the imports are unaffected), and `public import HodgeLadder.Tests.EllipticCurveWitness` at the end of `HodgeLadder.lean`:

   ```lean
   module

   public import HodgeLadder.Tests.EllipticCurveSmooth
   public import HodgeLadder.Tests.EllipticCurveIntegral
   public import HodgeLadder.Tests.EllipticCurveCM
   public import HodgeLadder.Tests.CodimensionZero
   public import HodgeLadder.Lefschetz.OneOne
   public import HodgeConjecture.Statement

   /-!
   # The plane cubic `y²z = x³ − xz²` satisfies the hypotheses of the statements of record

   Rung `elliptic-curve-witness`. The curve `ellipticCurve` of `plane-cubic-subscheme`, an object of
   `Over (Spec ↧ℂ)`, is integral (`elliptic-curve-integral`), smooth of relative dimension one
   (`elliptic-curve-smooth`) and projective (`plane-cubic-subscheme`), so upstream's
   `HodgeConjecture` and `LefschetzOneOne` specialize to it. Its complex points are Hausdorff
   (upstream's instance for projective `X`) and nonempty (the origin `[0 : 0 : 1]`), every open subset
   of them is paracompact (upstream's `ComplexPoint.openParacompactSpace`), upstream's dimension of
   `E` is `1`, and the relative dimension is unique.

   Non-vacuity on upstream definitions: the checked Lefschetz (1,1) theorem applies at `E`, the
   codimension-zero equality `Hdg⁰ = algebraicCycleClassSpan 0` holds at `E`, and the class of `E`
   itself, `cycleComponentSheafClass` at the generic point, is nonzero (upstream's `Other` library).
   The point `(i, 1 − i)` of `elliptic-curve-integral` is the point `ellipticCurvePointI` of
   `elliptic-curve-cm`, by `rfl`.

   No sign or normalization convention enters this file.

   ## Main results

   * `HodgeLadder.Tests.ellipticCurve_witness`, `ellipticCurve_t2Space`,
     `ellipticCurve_openParacompactSpace`, `dim_ellipticCurve`,
     `relativeDimension_ellipticCurve_eq`, `ellipticCurve_complexPoint_nonempty`
   * `HodgeLadder.Tests.hodgeConjecture_ellipticCurve`, `lefschetzOneOne_ellipticCurve`,
     `hodge_eq_span_zero_ellipticCurve`, `ellipticCurve_fundamentalClass_ne_zero`
   * `HodgeLadder.Tests.ellipticCurveChartMeet_eq_pointI`
   -/

   @[expose] public section

   open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace

   namespace HodgeLadder.Tests

   /-- **Rung `elliptic-curve-witness`.** The plane cubic `E : y²z = x³ − xz²` satisfies the scheme
   hypotheses of the statements of record: integral, smooth of relative dimension one (hence smooth),
   and projective. -/
   theorem ellipticCurve_witness :
       IsIntegral ellipticCurve.left ∧ SmoothOfRelativeDimension 1 ellipticCurve.hom ∧
         Smooth ellipticCurve.hom ∧ IsProjective ellipticCurve.hom :=
     ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

   /-- The complex points of `E` are Hausdorff (upstream's `IsProjective.complexPoint_t2Space`). -/
   theorem ellipticCurve_t2Space : T2Space (ComplexPoint ellipticCurve) := inferInstance

   /-- Every open subset of the complex points of `E` is paracompact (upstream's
   `ComplexPoint.openParacompactSpace`). -/
   theorem ellipticCurve_openParacompactSpace :
       ∀ U : Opens (ComplexPoint ellipticCurve), ParacompactSpace U :=
     ComplexPoint.openParacompactSpace ellipticCurve

   /-- Upstream's dimension of `E` is `1` (upstream's `SmoothOfRelativeDimension.dim_eq`). -/
   theorem dim_ellipticCurve : TopologicalSpace.dim ellipticCurve.left = 1 :=
     SmoothOfRelativeDimension.dim_eq (f := ellipticCurve.hom) 1

   /-- The relative dimension of `E` over `ℂ` is unique: any `d` with `SmoothOfRelativeDimension d`
   is `1`. -/
   theorem relativeDimension_ellipticCurve_eq (d : ℕ)
       [SmoothOfRelativeDimension d ellipticCurve.hom] : d = 1 :=
     (SmoothOfRelativeDimension.dim_eq (f := ellipticCurve.hom) d).symm.trans dim_ellipticCurve

   /-- `E` has a complex point (the origin `[0 : 0 : 1]`, `nonempty_complexPoint_ellipticCurve`). -/
   theorem ellipticCurve_complexPoint_nonempty : Nonempty (ComplexPoint ellipticCurve) :=
     inferInstance

   /-- Upstream's `HodgeConjecture` specializes to `E`: its instance arguments elaborate at
   `ellipticCurve`. -/
   theorem hodgeConjecture_ellipticCurve (h : HodgeConjecture) (p : ℕ) :
       Hdg^p(ellipticCurve; ℚ) ≤ algebraicCycleClassSpan ellipticCurve p :=
     h ellipticCurve p

   /-- The checked Lefschetz (1,1) theorem (`lefschetz-1-1`) at `E`: every rational Hodge class of
   degree two on `E` is a rational combination of classes of points. -/
   theorem lefschetzOneOne_ellipticCurve :
       Hdg^1(ellipticCurve; ℚ) ≤ algebraicCycleClassSpan ellipticCurve 1 :=
     HodgeLadder.lefschetzOneOne_holds ellipticCurve

   /-- The codimension-zero equality (`nonvacuity-tests`) at `E`. -/
   theorem hodge_eq_span_zero_ellipticCurve :
       Hdg^0(ellipticCurve; ℚ) = algebraicCycleClassSpan ellipticCurve 0 :=
     hodge_eq_span_zero ellipticCurve

   /-- The class of `E` itself, upstream's `cycleComponentSheafClass` at the generic point, is
   nonzero (upstream's `cycleComponentSheafClass_genericPoint_ne_zero`). -/
   theorem ellipticCurve_fundamentalClass_ne_zero :
       cycleComponentSheafClass ellipticCurve (genericPoint ellipticCurve.left)
         (coheight_genericPoint_eq_zero ellipticCurve) ≠ 0 :=
     cycleComponentSheafClass_genericPoint_ne_zero ellipticCurve

   /-- The point `(i, 1 − i)` that `elliptic-curve-integral` uses to join the charts is the point
   `ellipticCurvePointI` of `elliptic-curve-cm`. -/
   theorem ellipticCurveChartMeet_eq_pointI : ellipticCurveChartMeet = ellipticCurvePointI := rfl

   end HodgeLadder.Tests
   ```

8. Phase 2, `ledger/ladder.json`, replace the entry `elliptic-curve-witness` by (keep `id`, `title` and `kind`; `updated` to the merge date):

   ```json
   {
     "id": "elliptic-curve-witness",
     "title": "The plane cubic y²z = x³ − xz² as an object of Over (Spec ↧ℂ) is integral, smooth of relative dimension 1 and projective, with Hausdorff complex points, paracompact opens, dim 1 and a complex point",
     "status": "checked",
     "kind": "test",
     "module": "HodgeLadder.Tests.EllipticCurveWitness",
     "declarations": [
       "HodgeLadder.Tests.ellipticCurve_witness",
       "HodgeLadder.Tests.ellipticCurve_t2Space",
       "HodgeLadder.Tests.ellipticCurve_openParacompactSpace",
       "HodgeLadder.Tests.dim_ellipticCurve",
       "HodgeLadder.Tests.relativeDimension_ellipticCurve_eq",
       "HodgeLadder.Tests.ellipticCurve_complexPoint_nonempty",
       "HodgeLadder.Tests.hodgeConjecture_ellipticCurve",
       "HodgeLadder.Tests.lefschetzOneOne_ellipticCurve",
       "HodgeLadder.Tests.hodge_eq_span_zero_ellipticCurve",
       "HodgeLadder.Tests.ellipticCurve_fundamentalClass_ne_zero",
       "HodgeLadder.Tests.ellipticCurveChartMeet_eq_pointI"
     ],
     "depends_on": [
       "elliptic-curve-smooth",
       "elliptic-curve-integral",
       "elliptic-curve-cm",
       "lefschetz-1-1",
       "nonvacuity-tests"
     ],
     "contributors": [
       "claude-code"
     ],
     "note": "Checked 2026-11-28. Plan: docs/notes/2026-11-27-t1-plan.md, node E4. The four scheme instances at ellipticCurve by inferInstance (isIntegral_ellipticCurve, smoothOfRelativeDimension_ellipticCurve, smooth_ellipticCurve, isProjective_ellipticCurve); T2Space from upstream's IsProjective.complexPoint_t2Space; paracompact opens from upstream's ComplexPoint.openParacompactSpace; dim = 1 and uniqueness of the relative dimension from upstream's SmoothOfRelativeDimension.dim_eq; a complex point (the origin). Upstream's HodgeConjecture specializes at E; the checked Lefschetz (1,1) theorem and the codimension-zero equality hold at E, and the class of E at its generic point is nonzero (upstream's cycleComponentSheafClass_genericPoint_ne_zero). ellipticCurveChartMeet = ellipticCurvePointI by rfl. No sign. Red team: pass (docs/sketches/elliptic-curve-integral.redteam.md)."
   }
   ```

   In `docs/roadmap.md`, row `elliptic-curve-witness`: status `checked`, dependencies `` `elliptic-curve-smooth`, `elliptic-curve-integral`, `elliptic-curve-cm`, `lefschetz-1-1`, `nonvacuity-tests` ``, and end the row with `` `HodgeLadder.Tests.EllipticCurveWitness` ``. The roadmap row's "`cycleComponentSheafClass` elaborate at it" is met by `ellipticCurve_fundamentalClass_ne_zero`.

## Not required

- A point class on E (the closed point `ellipticCurveOrigin`, coheight 1, its `cycleComponentSheafClass` nonzero in H²) would be the first non-vacuity test in codimension one at E. It needs the coheight of a closed point on a curve, which the witness does not supply; a candidate for a later rung, `elliptic-point-class-nonzero`.
- `isIntegral_ellipticCurve` and `isIntegral_ellipticCurveScheme` are the same instance at reducible transparency (`ellipticCurve` is an `abbrev`); harmless, keep both for the two spellings.
