# Red team: `plane-cubic-subscheme` (foundation, issue #226, T1 plan node E1)

Date: 2026-11-27. Worktree `plane-cubic-subscheme`, branch `track/plane-cubic-subscheme`, candidate commit `fb660cf` on base `b9ae5a1`. Files: `HodgeLadder/General/ProjQuotient.lean` (237 lines, namespace `HodgeLadder.ProjQuotient`), `HodgeLadder/General/Hypersurface.lean` (249 lines, namespace `HodgeLadder.Hypersurface`), `HodgeLadder/Plane/Cubic/Subscheme.lean` (398 lines, namespace `HodgeLadder.Tests`); all three imported from `HodgeLadder.lean`; ledger entry still `open` with no declarations. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same as `main` at `30ea512` (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain` unchanged; the worktree's `.lake/packages` is a link to `main`'s).

**Verdict: pass with changes.**

No sign enters this rung, and nothing forces one. The linear term of the curve is a choice of object, fixed literally by `cubicForm` and checked by `ring` in `dehomogenize_two_cubicForm`; the curve is y²z = x³ − xz², affine chart y² = x³ − x, as the plan and decision 0013 require. Over ℂ the curve y² = x³ + x is isomorphic to it, so E1 to E4 are insensitive to that sign; the uniformization rung C3 is sensitive to it (finding 6, change 3).

Read: the ledger entries `plane-cubic-subscheme`, `elliptic-curve-smooth`, `elliptic-curve-integral`, `elliptic-curve-witness`, `elliptic-curve-cm`, `p2-witness`, `p1p1-witness`; `docs/notes/2026-11-27-t1-plan.md` nodes E1 to E5, C0, C3, C7; `docs/decisions/0013-t1-reduction-and-first-instance.md`; `docs/sketches/p1p1-witness.redteam.md`; upstream `Definitions/AlgebraicGeometry/ProjectiveSpace.lean` (`Presentation`, `IsProjective`, `IsProjective.isProper`); `HodgeLadder/Tests/ProjectivePlane.lean` (`projectivePlane`, `projectiveSpace`, `okaIsoSpace`, `okaIsoSpace_hom_toBase`); the port's `Oka/AlgebraicGeometry/ProjectiveSpace/{Basic,LinearSubst,Hyperplane}.lean` and `Oka/RingTheory/MvPolynomial/HomogeneousLocalization.lean`; Mathlib `AlgebraicGeometry/ProjectiveSpectrum/{Functor,Proper,Scheme}.lean`, `RingTheory/GradedAlgebra/`; `tools/check.py`, `tools/pinwalk.py`; `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`.

Scratch (directory `scratch-redteam-pcs/` in the worktree, deleted afterwards):

| File | What it tried | Result |
|---|---|---|
| `Axioms.lean` | `#print axioms` on all 90 `def`/`theorem`/`abbrev`/`instance` names of the three files | 90 reports, each `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no missing name |
| `Probe.lean` | (a) `affineEquation = X 1 ^ 2 - (X 0 ^ 3 - X 0)` and `cubicForm = X 1 ^ 2 * X 2 - (X 0 ^ 3 - X 0 * X 2 ^ 2)` by `ring`; (b) `aeval ![-X 0, I • X 1, X 2] cubicForm = -cubicForm`; (c) `aeval ![X 0, -X 1, X 2] cubicForm = cubicForm`; (d) `chartComplexPoint 2 ![1, 0]` and `chartComplexPoint 2 ![-1, 0]` (two-torsion points); (e) `eval ![0, 1] (dehomogenize 2 cubicForm) ≠ 0` ([0 : 1 : 1] is off E); (f) `eval ![1, 0] (X 1 ^ 2 - X 0 ^ 3 - X 0) ≠ 0` (the opposite sign loses (1, 0)); (g) `projectivePlane = Over.mk (ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ))` and `ellipticCurveToPlane.left = ellipticCurveι ≫ (okaIsoSpace 2).hom` by `rfl`; (h) `inferInstance : IsProper ellipticCurve.hom` | all elaborate, no error |
| `Notation.lean`, `Notation2.lean`, `Notation3.lean` | the silent-sorry hazard (finding 5) | reproduced; details below |
| `Admit.lean`, `Stop.lean` | `theorem _ : 1 = 2 := by admit`, and the same with `stop` | each builds with a warning only; `#print axioms` gives `[sorryAx]` |

`python3 tools/check.py --no-build` after `lake build` (6176 jobs, build current): `ACCEPTED: all checks passed`. The rung is not in the ledger yet, so the checker's axiom step covered none of its declarations; the `Axioms.lean` probe above stands in for it until change 4 lands. No `sorry`, `admit`, `native_decide`, `maxHeartbeats` or `unsafe` in the three files; every public declaration has a docstring.

## 1. Is this the statement the literature makes?

Literature. For a graded ring S generated in degree one and a homogeneous ideal I, S/I is graded by the images of the pieces, and S → S/I induces a closed immersion Proj(S/I) → Proj S, which over D₊(s) is Spec of S_(s) → (S/I)_(s) [`Stacks`, the chapter on Proj and closed subschemes, tag unverified; Hartshorne, Algebraic Geometry Ex. II.3.12, no key, unverified]. The plane cubic V₊(F) for homogeneous F of degree 3 is Proj(k[x, y, z]/(F)). The curve y² = x³ − x is the Weierstrass equation with a₁ = a₂ = a₃ = a₆ = 0, a₄ = −1, discriminant Δ = −16(4a₄³ + 27a₆²) = 64 ≠ 0 and j = 1728, with complex multiplication [i](x, y) = (−x, iy) [`Silverman2009`, ch. III, the example of y² = x³ − x, locator unverified].

Field by field against the Lean:

| Literature | Lean | Match |
|---|---|---|
| homogeneous coordinates x, y, z of ℙ² | `X 0`, `X 1`, `X 2` in `MvPolynomial (Fin 3) ℂ`, graded by `MvPolynomial.gradedAlgebra` (scoped instance of `AlgebraicGeometry.ProjectiveSpace`, the same instance `ℙₒ(2; ℂ)` is built from; `ι : scheme F hF ⟶ ℙₒ(n; R)` typechecks against it) | yes |
| F = y²z − x³ + xz², degree 3 | `cubicForm := X 1 ^ 2 * X 2 - X 0 ^ 3 + X 0 * X 2 ^ 2`, `cubicForm_mem : cubicForm ∈ homogeneousSubmodule (Fin (2 + 1)) ℂ 3` | yes; probe (a) |
| the quotient grading (S/I)ₙ = image of Sₙ | `ProjQuotient.grading 𝒜 I i := (𝒜 i).map (mkₐ R I)`; `decompose'` is `decomposeQuot`, well defined because homogeneous components of elements of I lie in I (`I.isHomogeneous`), with both inverse laws proved | yes |
| Proj(S/I) → Proj S closed immersion | `quotι := Proj.map (mkGraded 𝒜 I) _`, `isClosedImmersion_quotι` from `isClosedImmersion_map`: over `Proj.basicOpen 𝒜 s` the restriction is, up to the iso `isoOfRangeEq`, `Spec.map (Away.map f s)` followed by `basicOpenIsoSpec.inv`, closed by `IsClosedImmersion.spec_of_surjective` and `away_map_surjective` | yes; local on the target over the cover by D₊(s), s homogeneous of positive degree |
| affine chart z ≠ 0: y² = x³ − x | `chartIdeal_two : chartIdeal cubicForm 2 = span {affineEquation}`, `affineEquation := X 1 ^ 2 - X 0 ^ 3 + X 0`, with `dehomogenize 2` sending (X 0, X 1, X 2) to (X 0, X 1, 1) (port's `dehomogenize_X_succAbove`, `dehomogenize_X_self`) | yes; y² − x³ + x = 0 is y² = x³ − x |
| chart y ≠ 0, u = x/y, w = z/y: w = u³ − uw² | `chartIdeal_one`, `infinityEquation := X 1 - X 0 ^ 3 + X 0 * X 1 ^ 2`, `dehomogenize 1` sending (X 0, X 1, X 2) to (X 0, 1, X 1) | yes; F(u, 1, w) = w − u³ + uw² |
| chart ring (S/(F))_(xᵢ) ≅ k[Y]/(F dehomogenized) | `Hypersurface.awayEquiv` (`fromAway`: a/xᵢᵐ ↦ dehomogenize i a; `toAway`: Yⱼ ↦ x_{i.succAbove j}/xᵢ), both inverse laws proved | yes |
| the chart lies over the standard chart of ℙ² through k[Y] → k[Y]/(f) | `chartIso_inv_ι`, `ellipticCurveChartAffine_inv_ι`, `ellipticCurveChartInfinity_inv_ι` | yes |
| [0 : 1 : 0] is the only point with z = 0 | `compl_chartAffine` | yes |

Upstream's `IsProjective f` is `Nonempty (Presentation f)`. `isProjective_ellipticCurve` gives `ambientDimension := 2`, `immersion := ellipticCurveι ≫ (okaIsoSpace 2).hom : ellipticCurve.left ⟶ ℙ(Fin (2 + 1); Spec ↧ℂ)`, closedness by instance (closed immersion followed by an iso), and `immersion_toBase` from `okaIsoSpace_hom_toBase` and `ellipticCurve_hom`. This is the pattern `p2-witness` and `p1p1-witness` used. Probe (h): upstream's `IsProjective.isProper` then gives `IsProper ellipticCurve.hom`.

## 2. Can the hypotheses be satisfied?

The E1 objects carry no hypotheses. The general files have one, `hF : F ∈ homogeneousSubmodule (Fin (n + 1)) R d` in `HodgeLadder.Hypersurface`, met by `cubicForm_mem`; `ProjQuotient` needs a homogeneous ideal, met by `Hypersurface.ideal cubicForm cubicForm_mem` (`Ideal.homogeneous_span`). The consumers' hypotheses are instances on `ellipticCurve`: `nonempty_complexPoint_ellipticCurve` and `nonempty_ellipticCurve` hold here; integrality and smoothness are E2 and E3.

## 3. Is the conclusion trivially true?

Partly, and the tests cover the gap. `isProjective_ellipticCurve` and `isClosedImmersion_ellipticCurveToPlane` hold for `quotι` of every homogeneous ideal, the zero ideal (E = ℙ²) and the unit ideal (E = ∅) included: the same proof goes through with any F. So neither instance carries information about the cubic. The content is in the chart isomorphisms (explicit rings, ring identities checked by `ring`), in `ellipticCurve_chart_cover` (uses the relation x³ = y²z + xz² and fails for F with an x-free part such as F = y²z), in `nonempty_complexPoint_ellipticCurve` (fails for E = ∅) and in `compl_chartAffine` (fails for E = ℙ², where the complement of z ≠ 0 is a line, and for E = ∅, where the point `ellipticCurveInfinity` cannot be built). I found no definition unfolding to `True`, no `ℕ∞` coercion, no empty index type and no unused hypothesis.

## 4. Interface axioms

Not an interface rung; no structure with axioms is introduced (decision 0003). The two instances `ProjQuotient.gradedMonoid` and `ProjQuotient.gradedAlgebra` are data on the local family `grading 𝒜 I`; Mathlib at the pin has no other grading on `A ⧸ I` to form a diamond with.

## 5. Checker run and the silent-sorry hazard

`check.py --no-build` passes; the axiom probe gives the three standard axioms on all 90 declarations (table above). The declarations change 4 names are the ones the ledger title means: `HodgeLadder.Tests.ellipticCurve : Over (Spec ↧ℂ)`, `isProjective_ellipticCurve : IsProjective ellipticCurve.hom`, the two chart isomorphisms with the rings in the title.

The hazard the prover reported, reproduced at `v4.35.0-rc4`:

- With `local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R` and `variable (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ 𝒜 d)`, the `variable` command gives no message. The same notation in a theorem binder elaborates correctly (`bar (hG : G ∈ 𝒜 d)` in `Notation.lean`).
- A declaration that does not mention `hF` compiles without it. One that mentions `hF` in its body fails with `Unknown identifier hF` or `failed to infer have declaration type`, and the declaration is not added (`Unknown constant`).
- With `include hF in theorem foo : F = F := rfl`, Lean reports `error: internal exception #3`, yet adds `foo` to the file's environment: `#check @foo` prints `∀ F ∈ sorry, F = F` (with unassigned metavariables under `pp.all`), `#print foo` prints `theorem ScratchPCS.foo : sorry := sorry`, `Expr.hasSorry` on its type is `true`, and `#print axioms foo` prints `'ScratchPCS.foo' does not depend on any axioms`.

Every path that keeps such a declaration also emits an error, so `lean` exits 1, `lake build` fails and no `.olean` is written; `check.py`'s build step is the guard that catches it. The text scan (`\bsorry\b`) cannot detect it, and in the failing file `#print axioms` misses it, so the axiom step is no backstop on its own. The candidate's `Hypersurface.lean` uses the notation in theorem binders only and spells the term out in the `Chart` section's `variable`; the 90-name probe confirms nothing survived.

A related gap found on the way: `admit` (and the `stop` tactic) yields `sorryAx` with a warning only, so `lake build` succeeds and the `\bsorry\b` scan misses it; the axiom step catches it only in declarations a ledger rung names or that depend on one. `HodgeLadder/` and `port/` contain no `admit` or `stop` tactic today (grep). Proposed guard (a checker-rule change, so a decision record and the propagation-map rows for "Change the checker rules"; outside this rung): `check_build` rejects when `lake build` output contains ``declaration uses `sorry` `` (Lake replays cached logs, so this also covers cached modules; confirm on a clean build), and the scan pattern becomes `\b(sorry|admit)\b`. Known-weaknesses row: change 5.

## 6. Conventions

| Convention | Used where | In `docs/conventions.md` | Truth depends on it |
|---|---|---|---|
| Coordinates and grading of ℙ² (x₀, x₁, x₂ in degree one, `U i = D₊(xᵢ)`, `okaIsoSpace`) | `ellipticCurveToPlane`, `isProjective_ellipticCurve`, the chart opens `U 2 ℂ 2`, `U 2 ℂ 1` | yes, row "Projective space: coordinates, grading, dimension, projectivity" | no |
| Dehomogenization at xᵢ (`dehomogenize R i`, Yⱼ = x_{i.succAbove j}/xᵢ) | `chartIso`, `awayEquiv`, `dehomogenize_{two,one}_*` | partly, rows "Algebraic affine chart and the standard chart of ℙⁿ" and "Segre embedding"; the chart variable names for E are new | the chart equations, which are equalities of polynomials: yes for the ring identities, no for any `Prop` downstream of E1 to E4 |
| The curve: F = y²z − x³ + xz², so a₄ = −1 | `cubicForm`, `affineEquation`, `infinityEquation` | no; change 3 adds it | E1 to E4: no (y² = x³ + x is isomorphic over ℂ, by x ↦ ix up to a scaling of y). C3 `elliptic-curve-uniformization`: yes. With Mathlib's ℘'² = 4℘³ − g₂℘ − g₃ (`derivWeierstrassP_sq`, per the plan note), Φ z = [℘ z : ℘' z / 2 : 1] lands on y² = x³ − x exactly when g₂ = 4, g₃ = 0, which the plan fixes (L = c·ℤ[i] with g₂ = 4); y² = x³ + x would need g₂ = −4 |
| CM substitution and Proj.map variance | E5 `elliptic-curve-cm` (planned) | no; change 3 records the checked identities | E5's equalities `ellipticI ≫ ellipticI = ellipticNeg`, `ellipticI⁴ = 𝟙` are equalities of morphisms; see finding 6 below |

On the E5 question in the brief. Probe (b): σ : x ↦ −x, y ↦ iy, z ↦ z sends F to −F, since (iy)²z − (−x)³ + (−x)z² = −y²z + x³ − xz². Probe (c): y ↦ −y fixes F. σ is a degree-preserving automorphism of ℂ[x, y, z] with σ(F) = −F ∈ (F) and σ⁻¹(F) = −F as well, so σ maps (F) onto (F) and induces a graded automorphism of S/(F); `Proj.map` of it is an automorphism of E. A unit multiple of F generates the same ideal, so scaling F by a unit preserves the quotient; nothing more is needed. Two cautions for the E5 prover: (i) `Proj.map` is contravariant (`Proj.map f : Proj ℬ ⟶ Proj 𝒜` for `f : 𝒜 →+*ᵍ ℬ`, `Proj.map_comp` reverses order), harmless for powers of one map; (ii) two graded maps that differ by scaling all variables by one unit give the same morphism of `Proj` without being equal as ring maps, so state `ellipticNeg` by the substitution σ² = (x, y, z) ↦ (x, −y, z) itself, which makes `ellipticI ≫ ellipticI = ellipticNeg` follow from `Proj.map_comp` and a ring identity. `ProjQuotient` has no lemma producing the graded map S/I → S/I from a graded map S → S preserving I; that lemma is E5's to write.

Over the affine chart the CM map is (x, y) ↦ (−x, iy) on y² = x³ − x, matching `Silverman2009` and the plan. The same substitution also preserves y² = x³ + x, so E5 alone would not detect a sign slip in the linear term; the two-torsion test points of change 6 do (probe (f)).

## 7. Equality first

E1 is a foundation rung of definitions and identifications. Its identities (`dehomogenize_two_cubicForm`, `dehomogenize_one_cubicForm`, `chartIdeal_two`, `chartIdeal_one`, `chartIso_inv_ι`, the two `_inv_ι` lemmas, `ellipticCurve_chart_cover`, `compl_chartAffine`) are exact equalities, with no scalar. No inclusion is claimed.

## 7b. Non-vacuity

Smallest test lemmas that fail for a trivial E: `HodgeLadder.Tests.nonempty_complexPoint_ellipticCurve : Nonempty (AlgebraicGeometry.ComplexPoint ellipticCurve)` (fails for E = ∅) and `HodgeLadder.Tests.compl_chartAffine` (fails for E = ℙ² and for E = ∅); both exist and are checked. A sign slip in the linear term (y² = x³ + x) passes every lemma of the candidate except the literal equalities `dehomogenize_two_cubicForm` and `chartIdeal_two`, which restate the definitions; a semantic pin costs six lines (change 6). Downstream, upstream's statement hypotheses at `ellipticCurve` (as `p1p1-witness` Probe1 did) belong to E4 `elliptic-curve-witness`, after integrality and smoothness.

## 8. Placement, gaps, ledger

- Placement. `HodgeLadder/Plane/Cubic/Subscheme.lean` is `next.py`'s fallback path. The file's namespace is `HodgeLadder.Tests`, the downstream titles name `HodgeLadder.Tests.ellipticCurve`, and the projective witnesses it sits beside are `HodgeLadder/Tests/{ProjectivePlane,P1p1Witness}.lean`. Move it to `HodgeLadder/Tests/EllipticCurve.lean` (change 1); no file of that name exists.
- Duplication (decision 0011). Mathlib at the pin has no grading on a quotient by a homogeneous ideal (searched `RingTheory/GradedAlgebra/`, `HomogeneousIdeal` users, `GradedAlgebra`/`GradedRing` with `⧸`) and no closed-immersion lemma for `Proj.map` (`ProjectiveSpectrum/{Functor,Proper}.lean`; `Proper.lean` uses `IsClosedImmersion.spec_of_surjective` only for the diagonal). Upstream has neither. The port has two near-duplicates: `HomogeneousIdeal.irrelevant_le_map_of_surjective` (`Oka/AlgebraicGeometry/ProjectiveSpace/LinearSubst.lean`) restates `ProjQuotient.irrelevant_le_map`, and `HomogeneousLocalization.Away.map_surjective` (`ProjectiveSpace/Hyperplane.lean`) restates `ProjQuotient.away_map_surjective`; the port's take `Function.Surjective f`, the candidate's take degreewise surjectivity, and the two are equivalent for graded maps. Keeping the local pair holds `ProjQuotient` at layer 0 without a port import; the gaps row must name the overlap (change 2). The port's `hyperplane` closed immersion is a special case of `isClosedImmersion_map`; no change asked. `check.py`'s import-clash step passes, so no name collides with Mathlib.
- Layers (`tools/pinwalk.py` graph, 2026-11-27): `HodgeLadder.General.ProjQuotient` 0, `HodgeLadder.General.Hypersurface` 2, the test module 7.
- Merge. `main` has moved three commits past the base; `HodgeLadder.lean` and `ledger/ladder.json` changed there, so rebase before the pull request. No Lean dependency of the rung changed.

## 9. Drift

The candidate was built at the current pin (`2ead713`, `v4.35.0-rc4`), the pin of `main`. No drift to diff. At a future bump the rows of change 2 name the Mathlib directories to diff.

## 10. Findings

1. The object is the curve the plan names: E = V₊(y²z − x³ + xz²) in coordinates x = X 0, y = X 1, z = X 2; affine chart y² = x³ − x; chart at infinity w = u³ − uw² with u = x/y, w = z/y; [0 : 1 : 0] is the only point with z = 0. Checked by `ring` in the candidate and by probe (a).
2. `IsProjective` is met honestly through upstream's `Presentation` with ambient dimension 2, a closed immersion into upstream's `projectivePlane`, and the triangle over `Spec ↧ℂ`; `IsProper` follows from upstream (probe (h)).
3. The graded quotient and `isClosedImmersion_map` are correct and general; neither is in Mathlib or upstream at the pin; two helper lemmas restate port lemmas in an equivalent form.
4. `isProjective_ellipticCurve` alone is uninformative (true for every homogeneous ideal); the charts, the cover lemma, `Nonempty (ComplexPoint ellipticCurve)` and `compl_chartAffine` carry the content and would fail for E = ℙ² or E = ∅.
5. Silent-sorry hazard reproduced: a `local notation` over section variables inside a `variable` binder gives `F ∈ sorry` with no message at the `variable` command; every surviving use errors, so `lake build` catches it; `#print axioms` does not. `admit` and `stop` evade the text scan with a warning only.
6. No sign is forced. The linear-term sign is a choice of curve, irrelevant to E1 to E4 and load-bearing for C3; the CM substitution maps F to −F, so it induces an automorphism of E by `Proj.map`, and it does not distinguish y² = x³ − x from y² = x³ + x.
7. File placement disagrees with the namespace and the neighbouring witnesses.

## 11. Required changes

1. Move `HodgeLadder/Plane/Cubic/Subscheme.lean` to `HodgeLadder/Tests/EllipticCurve.lean` (module `HodgeLadder.Tests.EllipticCurve`; namespace unchanged), replace the import line in `HodgeLadder.lean` by `public import HodgeLadder.Tests.EllipticCurve`, delete the empty `HodgeLadder/Plane/`, and in the module docstring replace "No sign convention enters." by: "No sign convention enters this file; the sign of the linear term fixes the curve and is recorded in `docs/conventions.md`, row \"Plane cubic E and its charts\"."

2. In `docs/gaps.md`, section "Algebraic geometry and commutative algebra", insert in layer order:

   | `HodgeLadder.ProjQuotient.grading`, `mem_grading_iff`, `mk_mem_grading`, `gradedMonoid`, `gradedAlgebra` (the images of the pieces grade A ⧸ I for a homogeneous ideal I, any `AddMonoid` index), `pieceMap`, `decomposeAux`, `decomposeQuot`, `mkGraded`, `mkGraded_surjOn`, `irrelevant_le_map`, `away_map_surjective`, `isClosedImmersion_map` (`Proj.map` of a graded ring map onto every piece is a closed immersion), `quotι`, `isClosedImmersion_quotι`, `quotι_preimage_basicOpen` | `HodgeLadder.General.ProjQuotient` | 0 | Mathlib at the pin has no grading on a quotient by a homogeneous ideal and no closed-immersion lemma for `Proj.map`; `irrelevant_le_map` and `away_map_surjective` restate the port's `HomogeneousIdeal.irrelevant_le_map_of_surjective` (`Oka/AlgebraicGeometry/ProjectiveSpace/LinearSubst.lean`) and `HomogeneousLocalization.Away.map_surjective` (`Oka/AlgebraicGeometry/ProjectiveSpace/Hyperplane.lean`) with degreewise surjectivity in place of surjectivity (equivalent for graded maps), kept local to stay at layer 0 without a port import; at a bump check Mathlib `RingTheory/GradedAlgebra/` for a quotient grading and `AlgebraicGeometry/ProjectiveSpectrum/` for a closed-immersion lemma; rung `plane-cubic-subscheme` | 2026-11-27 |

   | `HodgeLadder.Hypersurface.ideal`, `grading`, `scheme`, `ι`, `π`, `chartIdeal`, `ChartRing`, `dehomQ`, `awayπ`, `awayπ_surjective`, `fromAway`, `toAway`, `awayEquiv` ((R[X₀, …, Xₙ] ⧸ (F))_(Xᵢ) ≃ R[Y] ⧸ (dehomogenize i F)), `fromAway_awayπ`, `ι_preimage_U`, `chartIso`, `chartIso_inv_ι`, `chartPoint`, `chartPoint_ι` (the hypersurface V₊(F) ⊂ ℙₒ(n; R) of a homogeneous F over any ring, with its standard charts) | `HodgeLadder.General.Hypersurface` | 2 | Mathlib and upstream have no hypersurface in projective space; `awayEquiv` extends the port's `awayXEquiv` from the polynomial ring to its quotient by F; at a bump check Mathlib `AlgebraicGeometry/ProjectiveSpectrum/` and upstream `Definitions/AlgebraicGeometry/ProjectiveSpace.lean` for closed subschemes of ℙⁿ; rung `plane-cubic-subscheme` | 2026-11-27 |

3. In `docs/conventions.md`, add after the row "Segre embedding of ℙ¹ × ℙ¹":

   | Plane cubic E and its charts | this repository, `HodgeLadder.Tests.cubicForm`, `ellipticCurve`, `ellipticCurveToPlane`, `isProjective_ellipticCurve`, `affineEquation`, `infinityEquation`, `ellipticCurveChartAffine`, `ellipticCurveChartInfinity`, `ellipticCurveOrigin`, `ellipticCurveInfinity` (`HodgeLadder/Tests/EllipticCurve.lean`, rung `plane-cubic-subscheme`); `HodgeLadder.Hypersurface.chartIso`, `awayEquiv` (`HodgeLadder/General/Hypersurface.lean`); the port's `dehomogenize`, `ProjectiveSpace.chart`, `U` | homogeneous coordinates x = X 0, y = X 1, z = X 2 of `ℙₒ(2; ℂ)`; F = y²z − x³ + xz² (`X 1 ^ 2 * X 2 - X 0 ^ 3 + X 0 * X 2 ^ 2`), so E : y²z = x³ − xz², Weierstrass form y² = x³ + a₄x with a₄ = −1, Δ = 64; chart z ≠ 0 is `dehomogenize 2` with (X 0, X 1) = (x/z, y/z) and equation y² − x³ + x; chart y ≠ 0 is `dehomogenize 1` with (X 0, X 1) = (u, w) = (x/y, z/y) and equation w − u³ + uw²; `ellipticCurveOrigin` is [0 : 0 : 1], `ellipticCurveInfinity` is [0 : 1 : 0] = (u, w) = (0, 0); the presentation of `isProjective_ellipticCurve` is `ellipticCurveι ≫ (okaIsoSpace 2).hom`, ambient dimension 2, into `projectivePlane`; the CM substitution x ↦ −x, y ↦ iy, z ↦ z sends F to −F and y ↦ −y fixes F | none for E1 to E4 (y² = x³ + x is isomorphic over ℂ and every statement there is a `Prop` about this object). Load-bearing for C3 `elliptic-curve-uniformization`: Φ z = [℘ z : ℘' z / 2 : 1] lands on y² = x³ − x exactly when g₂ = 4 and g₃ = 0, against Mathlib's ℘'² = 4℘³ − g₂℘ − g₃, and Φ (i z) = [−x : iy : z] uses ℘(iz) = −℘(z), ℘'(iz) = i℘'(z) on L = iL; also C0 `elliptic-curve-points` (the chart equations) and C7 (the action of ellipticI^*). E5 must state `ellipticNeg` by the substitution (x, y, z) ↦ (x, −y, z): `Proj.map` identifies ring maps that differ by a common unit scaling of the variables | read from source; chart identities by `ring`, CM substitution, two-torsion points and [0 : 1 : 1] ∉ E checked in scratch (red team 2026-11-27, `plane-cubic-subscheme`) |

4. Ledger entry `plane-cubic-subscheme`: `status` `checked`, `module` `HodgeLadder.Tests.EllipticCurve`, `contributors` `["claude-code"]`, `declarations`:

   `HodgeLadder.Tests.cubicForm`, `HodgeLadder.Tests.cubicForm_mem`, `HodgeLadder.Tests.ellipticCurve`, `HodgeLadder.Tests.ellipticCurve_hom`, `HodgeLadder.Tests.ellipticCurveToPlane`, `HodgeLadder.Tests.isClosedImmersion_ellipticCurveToPlane`, `HodgeLadder.Tests.isProjective_ellipticCurve`, `HodgeLadder.Tests.dehomogenize_two_cubicForm`, `HodgeLadder.Tests.dehomogenize_one_cubicForm`, `HodgeLadder.Tests.affineEquation`, `HodgeLadder.Tests.infinityEquation`, `HodgeLadder.Tests.ellipticCurveChartAffine`, `HodgeLadder.Tests.ellipticCurveChartInfinity`, `HodgeLadder.Tests.ellipticCurveChartAffine_inv_ι`, `HodgeLadder.Tests.ellipticCurveChartInfinity_inv_ι`, `HodgeLadder.Tests.ellipticCurve_chart_cover`, `HodgeLadder.Tests.ellipticCurveOrigin`, `HodgeLadder.Tests.ellipticCurveInfinity`, `HodgeLadder.Tests.ellipticCurveOrigin_ι`, `HodgeLadder.Tests.ellipticCurveInfinity_ι`, `HodgeLadder.Tests.ellipticCurveTwoTorsionPos`, `HodgeLadder.Tests.ellipticCurveTwoTorsionNeg`, `HodgeLadder.Tests.nonempty_complexPoint_ellipticCurve`, `HodgeLadder.Tests.nonempty_ellipticCurve`, `HodgeLadder.Tests.compl_chartAffine`, `HodgeLadder.ProjQuotient.gradedAlgebra`, `HodgeLadder.ProjQuotient.mkGraded`, `HodgeLadder.ProjQuotient.isClosedImmersion_map`, `HodgeLadder.ProjQuotient.quotι`, `HodgeLadder.ProjQuotient.isClosedImmersion_quotι`, `HodgeLadder.Hypersurface.scheme`, `HodgeLadder.Hypersurface.ι`, `HodgeLadder.Hypersurface.awayEquiv`, `HodgeLadder.Hypersurface.chartIso`, `HodgeLadder.Hypersurface.chartIso_inv_ι`, `HodgeLadder.Hypersurface.chartPoint_ι`.

   `note`: "Checked 2026-11-27. E = Proj (ℂ[x, y, z] ⧸ (y²z − x³ + xz²)) with x = X 0, y = X 1, z = X 2 (HodgeLadder.General.Hypersurface on HodgeLadder.General.ProjQuotient: the quotient grading by a homogeneous ideal, and Proj.map of a graded map onto every piece is a closed immersion, Spec of a surjection over each D₊(s)). Projective: the presentation ellipticCurveι ≫ okaIsoSpace 2, ambient dimension 2, into projectivePlane. Charts z ≠ 0 and y ≠ 0 are Spec ℂ[x, y]/(y² − x³ + x) and Spec ℂ[u, w]/(w − u³ + uw²) over the standard charts of ℙ², covering E; tests: [0 : 0 : 1], [0 : 1 : 0], the two-torsion points (±1, 0), and the complement of z ≠ 0 is the single point [0 : 1 : 0]. No sign in the rung; the curve's linear term is a choice recorded in the conventions row \"Plane cubic E and its charts\" (load-bearing for elliptic-curve-uniformization). Red team: pass with changes (docs/sketches/plane-cubic-subscheme.redteam.md)."

   Add the matching row to `docs/roadmap.md` (propagation map, "Prove a rung").

5. In `docs/gaps.md`, "Known weaknesses", add:

   | A `local notation` standing for a term in section variables, used inside a `variable` binder (`local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R` with `variable (hF : F ∈ 𝒜 d)`), elaborates the binder to `F ∈ sorry` with no message at the `variable` command (Lean `v4.35.0-rc4`; red team `plane-cubic-subscheme`, finding 5). Every declaration that uses the binder fails (unknown identifier, or `internal exception #3` under `include`), so `lake build` fails; in the failing file `#print axioms` reports no axioms for the resulting constant `foo : sorry := sorry`, and the `\bsorry\b` scan cannot detect it. Separately, `admit` and the `stop` tactic yield `sorryAx` with a warning only and evade the scan; the axiom step catches them only inside the closure of ledger-named declarations. Spell terms out in `variable` binders, as `HodgeLadder.General.Hypersurface` does | the build gate is the only guard against the first; a declaration with `admit` outside every ledger closure passes `tools/check.py`. Proposed checker rule (decision record first): reject `lake build` output containing ``declaration uses `sorry` `` and scan for `\b(sorry|admit)\b` | 2026-11-27 |

6. Add two sign-pinning test points to `HodgeLadder/Tests/EllipticCurve.lean` after `ellipticCurveInfinity` (compiled in scratch as written):

   ```lean
   /-- The two-torsion point `(x, y) = (1, 0)`, `[1 : 0 : 1]`; it lies on `y² = x³ − x` and not on
   `y² = x³ + x`, so it pins the sign of the linear term. -/
   def ellipticCurveTwoTorsionPos : ComplexPoint ellipticCurve :=
     chartComplexPoint 2 ![1, 0] (by rw [dehomogenize_two_cubicForm]; simp)

   /-- The two-torsion point `(x, y) = (−1, 0)`, `[−1 : 0 : 1]`. -/
   def ellipticCurveTwoTorsionNeg : ComplexPoint ellipticCurve :=
     chartComplexPoint 2 ![-1, 0] (by rw [dehomogenize_two_cubicForm]; simp; norm_num)
   ```

   and list them in the module docstring's "Main definitions".

Optional, no change required: a test that [0 : 1 : 1] is off E (probe (e)); deriving the port's `hyperplane` closed immersion from `isClosedImmersion_map` at the next port edit.
