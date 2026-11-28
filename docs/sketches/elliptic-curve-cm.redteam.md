# Red team: `elliptic-curve-cm` (foundation, issue #251, T1 plan node E5)

Date: 2026-11-28. Worktree `elliptic-curve-cm`, branch `track/elliptic-curve-cm`, candidate commit `dce695c` on base `19a4bda`. Files: `HodgeLadder/General/ProjQuotientMap.lean` (176 lines, namespace `HodgeLadder.ProjQuotient`), `HodgeLadder/Tests/EllipticCurveCM.lean` (497 lines, namespace `HodgeLadder.Tests`), both imported from `HodgeLadder.lean`. Ledger entry still `open`.

**Verdict: pass with changes.**

No sign was unexpected. `ellipticI` acts on complex points as (x, y) ↦ (−x, iy) in the chart z ≠ 0, which is Silverman's [i] on y² = x³ − x and the normalized [i] (pullback of the invariant differential dx/2y is i · dx/2y). It also agrees with z ↦ iz under the planned uniformization Φ z = [℘ z : ℘' z / 2 : 1]. The three identities hold exactly as equalities of substitutions: (−1, i, 1)² = (1, −1, 1) and (1, −1, 1)² = (1, 1, 1) componentwise. None of them uses the fact that `Proj.map` identifies substitutions that differ by a common unit scaling. The test suite has one hole. Nothing proves `ellipticNeg ≠ 𝟙`, so the tests as written would also pass if `ellipticI` were an involution. Change 1 closes it with a checked lemma.

Read: `python3 tools/next.py elliptic-curve-cm`; the ledger entries `elliptic-curve-cm`, `plane-cubic-subscheme`, `elliptic-square-witness`, `elliptic-curve-points`; `docs/sketches/plane-cubic-subscheme.redteam.md` §6, §8, §11; `docs/notes/2026-11-27-t1-plan.md` nodes E5, E7, C3, C7, D6; `HodgeLadder/General/ProjQuotient.lean`, `HodgeLadder/General/Hypersurface.lean` (`chartPoint`, `chartPoint_ι`), `HodgeLadder/Tests/EllipticCurve.lean` (`chartComplexPoint`, the test points); the port's `Oka/AlgebraicGeometry/ProjectiveSpace/{LinearSubst,BaseChange,Hyperplane}.lean`; Mathlib `RingTheory/GradedAlgebra/{RingHom,Homogeneous/Maps,HomogeneousLocalization}.lean`, `AlgebraicGeometry/ProjectiveSpectrum/Functor.lean`; `docs/conventions.md` row "Plane cubic E and its charts"; `docs/gaps.md` "Algebraic geometry and commutative algebra"; `docs/references.md` (`Silverman2009`).

Scratch (directory `.rt-cm-probe/` in the worktree, deleted afterwards):

| File | What it tried | Result |
|---|---|---|
| `Axioms.lean`, `A2.lean` | `#print axioms` on all 76 `theorem`/`def`/`abbrev` names of the two files, plus the `_assoc` forms | each `[propext, Classical.choice, Quot.sound]` |
| `Probe.lean` | (a) `ellipticNeg ≠ 𝟙` through the point (i, 1 − i); (b) the image of (i, 1 − i) under `ellipticI` differs from the inverse-substitution image (−i, −1 − i); (c) `ellipticI ≫ ellipticI ≫ ellipticI ≠ ellipticI`; (d) `ellipticIIso.inv = ellipticI ≫ ellipticI ≫ ellipticI`; (e) `IsIso ellipticI` | all five check |
| `Final.lean` | the exact text of change 1 | checks, standard axioms |

`python3 tools/check.py --no-build` on the candidate (build current, `.olean`s of both modules present): `ACCEPTED: all checks passed`. The rung is not in the ledger yet, so the checker's axiom step covered none of its declarations; `Axioms.lean` stands in for it.

## 1. Is this the statement the literature makes?

Literature. On E : y² = x³ − x over ℂ, the map [i](x, y) = (−x, iy) is an automorphism, and with [−1](x, y) = (x, −y) it gives End(E) ⊇ ℤ[i] (`Silverman2009`, ch. III, Example 4.4 for [i] and §III.2 for the negation on a Weierstrass curve with a₁ = a₃ = 0; locators unverified, the key's chapter is VI). Under the normalized embedding [·] with [α]^*ω = αω for ω = dx/2y, the pullback is [i]^*ω = d(−x)/(2iy) = (−1/i) ω = i ω, so (x, y) ↦ (−x, iy) is the normalized [i], and (x, y) ↦ (−x, −iy) is [−i].

| Literature | Lean | Match |
|---|---|---|
| E ⊂ ℙ², y²z = x³ − xz² | `ellipticCurve` from `plane-cubic-subscheme`, F = `X 1 ^ 2 * X 2 - X 0 ^ 3 + X 0 * X 2 ^ 2` | yes (that rung's red team) |
| [i] on homogeneous coordinates [x : y : z] ↦ [−x : iy : z] | `ellipticI := diagHom iScalars ..`, `iScalars = ![-1, Complex.I, 1]`, `diagSubst c = aeval fun j => C (c j) * X j` | yes; on functions the ring map is x ↦ −x, y ↦ iy, z ↦ z (`diagSubst_iScalars_X_*`), and `Proj.map` of a ring map pulls functions back along the morphism |
| [−1] on [x : y : z] ↦ [x : −y : z] | `ellipticNeg := diagHom negScalars ..`, `negScalars = ![1, -1, 1]` | yes, stated by the substitution itself, as the plane-cubic red team asked |
| [i] ∘ [i] = [−1] | `ellipticI_comp_self : ellipticI ≫ ellipticI = ellipticNeg` | yes, exact |
| [−1] ∘ [−1] = 1 | `ellipticNeg_comp_self` | yes, exact |
| [i]⁴ = 1 | `ellipticI_pow_four : ellipticI ≫ ellipticI ≫ ellipticI ≫ ellipticI = 𝟙 _` | yes |
| [i] an automorphism over ℂ | `ellipticIIso : ellipticCurve ≅ ellipticCurve` in `Over (Spec ↧ℂ)`, inverse `ellipticI ≫ ellipticNeg` | yes |
| [i](x, y) = (−x, iy) on points | `chartComplexPoint_comp_diagHom` at i = 2: the point with chart coordinates v goes to (c ∘ succAbove 2) * v = (−v₀, i v₁) | yes; the direction check is the next paragraph |

Direction on points, by direct computation. `chartComplexPoint 2 v` is `Spec.map (eval v) ≫ chart 2` (through `Hypersurface.chartPoint_ι`), with Y₀ = x/z, Y₁ = y/z. `chart_comp_linearSubstMap_diag` gives `chart 2 ≫ linearSubstMap σ = Spec.map (chartSubst d) ≫ chart 2` with d = (c₀, c₁) = (−1, i). Then `Spec.map (eval v) ≫ Spec.map (chartSubst d) = Spec.map (chartSubst d ≫ eval v)`, the ring map Yⱼ ↦ eval v (dⱼ Yⱼ) = dⱼ vⱼ, so the image point has coordinates d * v = (−v₀, i v₁). `eval_comp_chartSubst` records the same identity. The test `ellipticCurvePointI_comp_ellipticI` fixes it on a point: (i, 1 − i) ↦ (−i, 1 + i). On E: (1 − i)² = −2i = i³ − i, and (1 + i)² = 2i = (−i)³ + i. The reversed direction (the inverse substitution, x ↦ −x, y ↦ −iy) would send (i, 1 − i) to (−i, −1 − i). Probe (b) checks that this point is different from (−i, 1 + i), so the test separates i from −i.

Consistency with C3. On L = c·ℤ[i] (so iL = L), ℘(iz) = i⁻²℘(z) = −℘(z) and ℘'(iz) = i⁻³℘'(z) = i ℘'(z), so Φ(iz) = [−℘ z : i ℘' z / 2 : 1] = [i](Φ z). The planned `Point.continuousMap ellipticI (Φ z) = Φ (I * z)` is therefore true with this `ellipticI`. With [−i] in its place it would be false.

## 2. Can the hypotheses be satisfied?

The headline statements are closed equalities with no hypotheses. `diagHom c hc hF` takes c with nonzero entries and a proof that the substitution sends F into (F); `iScalars` and `negScalars` meet both (`iScalars_ne_zero`, `diagSubst_iScalars_mem`, and the `neg` versions). `chartComplexPoint_comp_diagHom` takes two on-curve proofs and cᵢ = 1. Its instances in the file (origin, two-torsion points, (i, 1 − i)) discharge all of them.

## 3. Trivially true?

Tried: (i) the whole endomorphism set of E collapses (E empty, or `Proj.map` of a quotient by a non-proper ideal). Ruled out: `ellipticI_ne_id` uses `chartComplexPoint_injective` and the two-torsion points (±1, 0), which `ellipticI` swaps. (ii) `ellipticNeg = 𝟙`, which would make `ellipticI_comp_self` say [i] is an involution. The candidate's tests do not exclude it: `ellipticI ≠ 𝟙` and `ellipticI ≠ ellipticNeg` both hold for an involution distinct from [−1]. Probe (a) proves `ellipticNeg ≠ 𝟙` (it moves (i, 1 − i) to (i, i − 1)). Change 1 adds that proof. With it, `ellipticI` has order exactly four (probe (c) derives [i]³ ≠ [i]). (iii) `diagHom_congr` and `projQuotMap_congr` use `subst` on an equality of scalars or of graded maps. Both are exact equalities, and neither identifies distinct substitutions.

The scaling quirk. `Proj.map` of λσ equals `Proj.map` of σ for a unit λ (all variables scaled together). So, for instance, `diagHom ![-1, 1, -1] ..` should equal `ellipticNeg`. No proof in the candidate invokes this. `ellipticI_comp_self` is `diagHom_comp` (that is, `Proj.map_comp` plus `diagSubst_comp`, `ring` on each variable) followed by `diagHom_congr iScalars_mul_self`, with `iScalars * iScalars = negScalars` proved by `fin_cases` and `simp` on the three entries (1, −1, 1). I did not try to prove the scaling identity itself; nothing here needs it.

## 4. Interface rung

No structure, no axioms, no `Prop` inputs. Not applicable.

## 5. Checker

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`. Every declaration of both files reports the three standard axioms (scratch `Axioms.lean`, `A2.lean`). The declarations change 4 names are the ones the title means: `ellipticI`, `ellipticNeg`, `ellipticI_comp_self`, `ellipticI_pow_four`, with `ellipticNeg_comp_self` and `ellipticIIso` as the automorphism the consumers use.

Over `Spec ℂ`. `diagHom` is `Over.homMk (diagEndo ..)` with the triangle from `diagEndo_ι` (the square against `ellipticCurveι`, which is `projQuotMap_quotι`) and the port's `linearSubstMap_toSpec`. The structure map of `ellipticCurve` is `ellipticCurveι ≫ toSpec`, and the `change` that unfolds it elaborates. The morphism is honestly over ℂ.

Automorphism, for E7. `ellipticWeilEndo := prod.map ellipticI (ellipticI ≫ ellipticI ≫ ellipticI)` (ledger title of `elliptic-square-witness`). `ellipticIIso.inv` is `ellipticI ≫ ellipticNeg`, which equals `ellipticI ≫ ellipticI ≫ ellipticI` after one rewrite by `ellipticI_comp_self` (probe (d)). Change 1 adds that lemma and an `IsIso ellipticI` instance, so E7 can pick either form. The plan note's `ellipticI⁻¹` (for `prod.map ellipticI ellipticI⁻¹`) is then `inv ellipticI`, equal to `ellipticIIso.inv` by `IsIso.inv_eq_of_hom_inv_id`.

## 6. Conventions

| Convention | Used where | In `docs/conventions.md` | Truth depends on it |
|---|---|---|---|
| Coordinates x = X 0, y = X 1, z = X 2 of ℙ²; chart z ≠ 0 with (Y₀, Y₁) = (x/z, y/z) through `dehomogenize 2` and `succAbove` | `chartComplexPoint`, `awayMap_comp_toAwayX`, every point test | yes, row "Plane cubic E and its charts" | the point tests yes (they are equalities of points); the identities of morphisms no |
| The curve y² = x³ − x (a₄ = −1) | `diagSubst_iScalars_cubicForm`, the two-torsion tests | yes, same row | the CM identities no: the same substitution preserves y² = x³ + x, as the plane-cubic red team noted. The two-torsion tests yes |
| CM scalars: [i] ↔ (−1, i, 1), [−1] ↔ (1, −1, 1) on (x, y, z) | `iScalars`, `negScalars`, `ellipticI`, `ellipticNeg` | partly (the plane-cubic row records the substitution sends F to −F); the choice i over −i and the point action are new, change 3 adds them | `ellipticI_comp_self`, `ellipticI_pow_four`: no (with −i in place of i, both still hold). C3's `Point.continuousMap ellipticI (Φ z) = Φ (I * z)`: yes. C7's matrix of `ellipticI^*` on (x₁, x₂): yes, up to the orientation conventions of the row "Torus cycle and winding classes". D6 and the Weil-space rungs use only (ellipticI^*)² = −1 and the eigenvalues ±i: no |
| `Proj.map` variance: contravariant in the ring map, `projQuotMap (g ∘ f) = projQuotMap g ≫ projQuotMap f`; on points, p ↦ p ≫ φ is evaluation after the substitution, so coordinates v ↦ c * v | `projQuotMap_comp`, `diagHom_comp`, `chartComplexPoint_comp_diagHom` | no; change 3 adds it | for diagonal substitutions the order of composition is invisible (they commute). The point action is load-bearing for every point test and for C3 |
| `Proj.map` identifies λσ with σ for a unit λ | nowhere in the proofs | yes, the plane-cubic row's last sentence | no; recorded so a later rung stating a non-diagonal CM map (or `[−1]` by (−1, 1, −1)) knows the equality of morphisms is weaker than the equality of substitutions |

Borrowed inputs: `Proj.map_comp`, `Proj.map_id`, `Proj.awayι_comp_map_of_eq` (port), `linearSubstMap_toSpec` (port), `HomogeneousIdeal.irrelevant_le_map_comp`, `irrelevant_le_map_of_surjective` (port). None carries a sign. `Proj.map_comp`'s order (`map (g.comp f) = map g ≫ map f`) is read from `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean:207`, and `projQuotMap_comp` states the same order.

## 7. Equality first

All three headline results are identities of morphisms in `Over (Spec ↧ℂ)`. Each is proved exactly, with no scalar, through equalities of graded ring maps. Nothing is up to a unit.

## 7b. Non-vacuity

The smallest lemmas that would fail if the identities held for a degenerate reason: `HodgeLadder.Tests.ellipticI_ne_id` (exists), `HodgeLadder.Tests.ellipticI_ne_ellipticNeg` (exists), `HodgeLadder.Tests.ellipticNeg_ne_id` (missing; change 1). The direction test is `HodgeLadder.Tests.ellipticCurvePointI_comp_ellipticI` (exists). Its premise `chartComplexPoint_injective` is proved from `Spec.map_injective` and the monomorphism `ellipticCurveι`, so it is not circular.

## 8. Pin drift

The candidate was built at the pin of `main` (upstream `2ead713`, Lean and Mathlib `v4.35.0-rc4`). `main` has moved one commit past the base (`d1c59da`, `singular-cochain-pullback`), which touches `HodgeLadder.lean`, `docs/conventions.md`, `docs/gaps.md`, `docs/roadmap.md` and `ledger/ladder.json` and leaves the pin alone. Rebase before the pull request (change 6). No Lean dependency of this rung changed. At a future bump the gaps row of change 2 names the directories to diff.

## Findings

1. Direction and scalar are right: `ellipticI` acts on points as (x, y) ↦ (−x, iy). That is Silverman's and the normalized [i], and it matches Φ(iz) for the planned uniformization. The test on (i, 1 − i) separates i from −i (probe (b)).
2. `ellipticI_comp_self`, `ellipticNeg_comp_self`, `ellipticI_pow_four` are exact equalities of substitutions read through `Proj.map_comp`. The scaling quirk of `Proj.map` plays no part.
3. The general lemma `ProjQuotient.projQuotMap` is sound and general (any R-algebras graded by `Submodule R`, same universe as `Proj.map` needs). Mathlib at the pin has no graded map of quotients (searched `RingTheory/GradedAlgebra/`, `→+*ᵍ` users, `Ideal.quotientMap` in graded files) and no `irrelevant ≤ comap irrelevant` lemma (`Homogeneous/Maps.lean` has `map_le_iff_le_comap` and `irrelevant_le_map_comp` only). Upstream and the port have neither. `check.py`'s clash step passes.
4. `ellipticI` is an honest `Over` morphism and an isomorphism (`ellipticIIso`). E7 needs the inverse in the form [i]³, one rewrite away. Change 1 states it.
5. The test suite misses `ellipticNeg ≠ 𝟙`, so it does not show that `ellipticI` has order four. Probe (a) proves it.
6. The general module `HodgeLadder.General.ProjQuotientMap` has no `docs/gaps.md` row. `tools/pinwalk.py`'s graph puts it at layer 1 (imports `HodgeLadder.General.ProjQuotient`, layer 0), and the test module at layer 8.
7. `chart_comp_linearSubstMap_diag` and `awayMap_comp_toAwayX` (a diagonal linear substitution of ℙ² in the standard chart) are general facts about the port's ℙ², kept in a test module. The port's `chart_comp_map` (`BaseChange.lean`) and `chart_comp_hyperplane` (`Hyperplane.lean`) have the same shape. A row lets a pin walk find them (change 2, second row).
8. The roadmap row describes a different proof ("a linear automorphism of upstream ℙ² ... compositions checked on the two charts"). The candidate works on Oka's ℙ² through `linearSubstMap` and proves the compositions globally by `Proj.map_comp`.
9. Placement is consistent with #212: the general lemma under `General/` at layer 1, the CM test module beside `Tests/EllipticCurve.lean` in the same namespace. `next.py`'s path `HodgeLadder/Elliptic/Curve/Cm.lean` is its fallback for an id with no module and should not be followed.
10. Outside this rung: in `docs/gaps.md` "Algebraic geometry and commutative algebra" the rows are out of layer order (`Tests.ProjectivePlanePoint` 9 and `Tests.CycleClassMultiplicativeCodimZero` 27 sit above `General.Segre` 2). No change asked here. The librarian can reorder at the next pin walk.

## Required changes

1. Add to `HodgeLadder/Tests/EllipticCurveCM.lean`, after `ellipticI_ne_ellipticNeg` and after `ellipticIIso` respectively (checked in scratch as written, standard axioms; inside the file's `noncomputable section` the `def` needs no `noncomputable`):

   ```lean
   /-- The point `(i, i − 1)` of `E`, the reflection `y ↦ −y` of `(i, 1 − i)`. -/
   def ellipticCurvePointIFlip : ComplexPoint ellipticCurve :=
     chartComplexPoint 2 ![Complex.I, -(1 - Complex.I)] (by
       rw [dehomogenize_two_cubicForm]
       simp only [map_add, map_sub, map_pow, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
       linear_combination (1 - Complex.I) * Complex.I_sq)

   /-- `[−1]` sends `(i, 1 − i)` to `(i, i − 1)`. -/
   theorem ellipticCurvePointI_comp_ellipticNeg :
       ellipticCurvePointI ≫ ellipticNeg = ellipticCurvePointIFlip :=
     chartComplexPoint_comp_diagHom_eq 2 _ _ _ (by simp [negScalars])
       (by funext j; fin_cases j <;> simp [negScalars, show (2 : Fin 3).succAbove 1 = 1 from rfl]) _ _

   /-- **`[−1]` is not the identity**: it moves `(i, 1 − i)`. So `[i]` has order exactly four. -/
   theorem ellipticNeg_ne_id : ellipticNeg ≠ 𝟙 ellipticCurve := by
     intro h
     have := ellipticCurvePointI_comp_ellipticNeg
     rw [h, Category.comp_id] at this
     have h2 := congrFun (chartComplexPoint_injective 2 _ _ this) 1
     simp at h2
     norm_num [Complex.ext_iff] at h2
   ```

   ```lean
   /-- The inverse of `[i]` is `[i]³`, the form `elliptic-square-witness` uses. -/
   theorem ellipticIIso_inv : ellipticIIso.inv = ellipticI ≫ ellipticI ≫ ellipticI := by
     rw [ellipticI_comp_self]
     rfl

   /-- `[i]` is an isomorphism. -/
   instance isIso_ellipticI : IsIso ellipticI := ellipticIIso.isIso_hom
   ```

   Add `ellipticCurvePointIFlip` to the docstring's "Main definitions", and `ellipticCurvePointI_comp_ellipticNeg`, `ellipticNeg_ne_id`, `ellipticIIso_inv`, `isIso_ellipticI` to "Main results". In the module docstring replace "so `[i]` is neither `𝟙` nor `[−1]` (`ellipticI_ne_id`, `ellipticI_ne_ellipticNeg`)" by "so `[i]` is neither `𝟙` nor `[−1]` (`ellipticI_ne_id`, `ellipticI_ne_ellipticNeg`); `[−1]` moves `(i, 1 − i)`, so `[−1] ≠ 𝟙` and `[i]` has order four (`ellipticNeg_ne_id`)".

2. In `docs/gaps.md`, section "Algebraic geometry and commutative algebra", insert after the `HodgeLadder.General.ProjQuotient` row:

   | `HodgeLadder.ProjQuotient.irrelevant_le_comap` (a graded ring map sends the irrelevant ideal into the irrelevant ideal), `quotMap`, `quotMap_mk`, `quotMap_comp_mkGraded`, `quotMap_ext`, `quotMap_comp`, `quotMap_id` (a graded map with f(I) ⊆ J induces the graded map A ⧸ I → B ⧸ J), `irrelevant_le_map_quotMap`, `projQuotMap`, `projQuotMap_quotι`, `projQuotMap_congr`, `projQuotMap_comp`, `projQuotMap_id` (its `Proj.map`, the square against `quotι`, functoriality in `Proj.map`'s reversed order) | `HodgeLadder.General.ProjQuotientMap` | 1 | Mathlib at the pin has no graded map between quotients by homogeneous ideals and no `irrelevant ≤ comap irrelevant` lemma (`RingTheory/GradedAlgebra/Homogeneous/Maps.lean` has `map_le_iff_le_comap` and `irrelevant_le_map_comp`); upstream and the port have neither; at a bump check Mathlib `RingTheory/GradedAlgebra/` for a quotient grading with its functoriality and `AlgebraicGeometry/ProjectiveSpectrum/Functor.lean` for `Proj.map` of quotients; rung `elliptic-curve-cm` | 2026-11-28 |

   and, after the `HodgeLadder.Tests.P1p1Witness` row:

   | `HodgeLadder.Tests.awayMap_comp_toAwayX`, `chart_comp_linearSubstMap_diag` (a diagonal substitution Xⱼ ↦ cⱼXⱼ of ℙ² with cᵢ = 1, in the standard chart Xᵢ ≠ 0, is Yⱼ ↦ c_{i.succAbove j} Yⱼ), `val_fromZeroRingHom`, `eval_comp_chartSubst` | `HodgeLadder.Tests.EllipticCurveCM` | 8 | the port has the same shape for base change (`ProjectiveSpace.chart_comp_map`, `Oka/AlgebraicGeometry/ProjectiveSpace/BaseChange.lean`) and for the hyperplane (`chart_comp_hyperplane`, `Hyperplane.lean`) and none for `linearSubstMap`; stated for `Fin 3` over ℂ; at a bump check the port's `ProjectiveSpace/LinearSubst.lean` and Mathlib `AlgebraicGeometry/ProjectiveSpectrum/` for `linearSubstMap` in charts; rung `elliptic-curve-cm` | 2026-11-28 |

3. In `docs/conventions.md`, add after the row "Plane cubic E and its charts":

   | Complex multiplication on E | this repository, `HodgeLadder.Tests.diagSubst`, `diagHom`, `iScalars`, `negScalars`, `ellipticI`, `ellipticNeg`, `ellipticIIso`, `chartComplexPoint_comp_diagHom` (`HodgeLadder/Tests/EllipticCurveCM.lean`, rung `elliptic-curve-cm`); `HodgeLadder.ProjQuotient.projQuotMap`, `projQuotMap_comp` (`HodgeLadder/General/ProjQuotientMap.lean`); Mathlib `Proj.map`, `Proj.map_comp` | `ellipticI` is `Proj.map` of the substitution x ↦ −x, y ↦ iy, z ↦ z (scalars `![-1, Complex.I, 1]` on (X 0, X 1, X 2)), `ellipticNeg` of y ↦ −y (`![1, -1, 1]`); `Proj.map` is contravariant (`projQuotMap (g.comp f) = projQuotMap g ≫ projQuotMap f`), and on complex points p ↦ p ≫ φ sends chart coordinates v of z ≠ 0 to (c₀v₀, c₁v₁), so `ellipticI` is (x, y) ↦ (−x, iy) and `ellipticNeg` is (x, y) ↦ (x, −y), pinned by (i, 1 − i) ↦ (−i, 1 + i) and (i, 1 − i) ↦ (i, i − 1); this is the normalized [i] of `Silverman2009` ([i]^*(dx/2y) = i · dx/2y; locator unverified) and equals z ↦ iz under Φ z = [℘ z : ℘' z / 2 : 1] on L = iL (℘(iz) = −℘(z), ℘'(iz) = i℘'(z)) | none for `ellipticI_comp_self`, `ellipticNeg_comp_self`, `ellipticI_pow_four` (they hold with −i in place of i); D6 and the Weil-space rungs use only (ellipticI^*)² = −1. Load-bearing for C3 `elliptic-curve-uniformization` (`Point.continuousMap ellipticI (Φ z) = Φ (I * z)` is false for [−i]) and for the matrix of `ellipticI^*` in C7 `elliptic-curve-cohomology` | read from source; point action derived from `Spec.map_comp` and checked on four test points; `ellipticNeg ≠ 𝟙` and the i-versus-−i separation checked in scratch (red team 2026-11-28, `elliptic-curve-cm`) |

4. Ledger entry `elliptic-curve-cm`: `status` `checked`, `module` `HodgeLadder.Tests.EllipticCurveCM`, `contributors` `["claude-code"]`, `declarations`:

   `HodgeLadder.ProjQuotient.quotMap`, `HodgeLadder.ProjQuotient.quotMap_comp_mkGraded`, `HodgeLadder.ProjQuotient.irrelevant_le_map_quotMap`, `HodgeLadder.ProjQuotient.projQuotMap`, `HodgeLadder.ProjQuotient.projQuotMap_quotι`, `HodgeLadder.ProjQuotient.projQuotMap_comp`, `HodgeLadder.ProjQuotient.projQuotMap_id`, `HodgeLadder.Tests.diagHom`, `HodgeLadder.Tests.diagHom_comp`, `HodgeLadder.Tests.diagHom_one`, `HodgeLadder.Tests.chart_comp_linearSubstMap_diag`, `HodgeLadder.Tests.chartComplexPoint_comp_diagHom`, `HodgeLadder.Tests.chartComplexPoint_injective`, `HodgeLadder.Tests.diagSubst_iScalars_cubicForm`, `HodgeLadder.Tests.diagSubst_negScalars_cubicForm`, `HodgeLadder.Tests.ellipticI`, `HodgeLadder.Tests.ellipticNeg`, `HodgeLadder.Tests.ellipticI_comp_self`, `HodgeLadder.Tests.ellipticNeg_comp_self`, `HodgeLadder.Tests.ellipticI_pow_four`, `HodgeLadder.Tests.ellipticIIso`, `HodgeLadder.Tests.ellipticIIso_inv`, `HodgeLadder.Tests.ellipticCurveOrigin_comp_ellipticI`, `HodgeLadder.Tests.ellipticCurveTwoTorsionPos_comp_ellipticI`, `HodgeLadder.Tests.ellipticCurvePointI_comp_ellipticI`, `HodgeLadder.Tests.ellipticCurvePointI_comp_ellipticNeg`, `HodgeLadder.Tests.ellipticI_ne_id`, `HodgeLadder.Tests.ellipticI_ne_ellipticNeg`, `HodgeLadder.Tests.ellipticNeg_ne_id`.

   `note`: "Checked 2026-11-28. ellipticI = Proj.map of x ↦ −x, y ↦ iy, z ↦ z on ℂ[x, y, z] ⧸ (F), which sends F to −F (HodgeLadder.General.ProjQuotientMap: a graded map preserving homogeneous ideals induces the graded map of quotients and its Proj.map, over the closed immersion); ellipticNeg by y ↦ −y itself. ellipticI ≫ ellipticI = ellipticNeg, ellipticNeg ≫ ellipticNeg = 𝟙, ellipticI⁴ = 𝟙 exactly, as equalities of substitutions through Proj.map_comp, no common rescaling; ellipticIIso with inverse ellipticI³. On points (x, y) ↦ (−x, iy) in the chart z ≠ 0 (Silverman's normalized [i]); tests: the origin is fixed, (±1, 0) are swapped by [i] and fixed by [−1], (i, 1 − i) ↦ (−i, 1 + i) pins i against −i, [−1] moves (i, 1 − i), so [i] has order four. Conventions row \"Complex multiplication on E\" (load-bearing for elliptic-curve-uniformization). Red team: pass with changes (docs/sketches/elliptic-curve-cm.redteam.md)."

   The title stays as posted.

5. `docs/roadmap.md`, row `elliptic-curve-cm`: status `checked`, and replace the description by "`Proj.map` of the diagonal substitution (−x, iy, z) on ℂ[x, y, z] ⧸ (F) through `HodgeLadder.General.ProjQuotientMap` (graded map of quotients), over Oka's `linearSubstMap`; compositions exact by `Proj.map_comp`; point action in the chart z ≠ 0; `ellipticIIso`; size small; `docs/notes/2026-11-27-t1-plan.md`".

6. Rebase `track/elliptic-curve-cm` onto `main` (`d1c59da`) before the pull request; `HodgeLadder.lean`, `docs/conventions.md`, `docs/gaps.md`, `docs/roadmap.md` and `ledger/ladder.json` changed there.

## Not done

- The scaling identity (for example `diagHom ![-1, 1, -1] .. = ellipticNeg`) was not proved; no rung needs it.
- `Silverman2009` locators for [i] (III.4.4) and the normalized embedding are from memory and stay unverified; the computation [i]^*(dx/2y) = i · dx/2y above replaces the citation for the purpose of fixing i against −i.
