# Red team: `p1p1-witness` (test, issue #105)

Date: 2026-11-27. Worktree `p1p1-witness`, branch `track/p1p1-witness`, candidate commit `58362c6` on base `e2d86b3` (= `main`). Files: `HodgeLadder/General/Segre.lean` (module `HodgeLadder.General.Segre`, namespace `HodgeLadder.Segre`, 672 lines) and `HodgeLadder/Tests/P1p1Witness.lean` (module `HodgeLadder.Tests.P1p1Witness`, namespace `HodgeLadder.Tests`, 222 lines); both imported from `HodgeLadder.lean`; ledger entry already `checked` with 22 declarations. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same as `main` (the worktree's `.lake/packages` is `main`'s; `lakefile.toml` and `lake-manifest.json` are unchanged by the candidate).

**Verdict: pass with changes.**

No sign enters this rung. Mathlib's Koszul sign (−1)^p appears nowhere, and nothing else is forced. The rung's conclusion is four `Prop` instances (`IsIntegral`, `SmoothOfRelativeDimension 2`, `Smooth`, `IsProjective`) on one object, so the coordinate order of the Segre map is invisible to every consumer (proof irrelevance); it is recorded as a convention row all the same (change 1).

Read: the ledger entries `p1p1-witness`, `p1p1-fibres-transversal`, `cycle-class-multiplicative-p1p1`, `p1p1-point-class-nonzero`, `cup-positive-degree-test`, `complex-points-prod`; `docs/sketches/cycle-class-multiplicative.md` (sub-rungs table and the ℙ¹ × ℙ¹ items), `docs/sketches/cycle-class-multiplicative.redteam.md`, `docs/sketches/complex-points-prod.redteam.md` (changes 8, O1); `docs/decisions/0010-two-support-route-and-p2-first.md`; upstream `HodgeConjecture/Statement.lean` (`HodgeConjecture`), `Definitions/AlgebraicGeometry/ProjectiveSpace.lean` (`ProjectiveSpace`, `toBase`, `Presentation`, `IsProjective`, `IsProjective.isProper`), `Definitions/.../ComplexPoint/Basic.lean` (`Point`, `ComplexPoint`), `Definitions/.../Cycle/FundamentalClass.lean` (`cycleComponentSheafClass`, `algebraicCycleClassSpan`), `Other/AlgebraicGeometry/SmoothProjectiveVariety.lean`; the port's `Oka/AlgebraicGeometry/ProjectiveSpace/{Basic,Points,FromGlobalSections,BaseChange}.lean`; `HodgeLadder/Tests/{ProjectiveLine,ProjectivePlane,ProjectiveLinePoint}.lean`, `HodgeLadder/General/ComplexPointProd.lean`, `HodgeLadder/Normalization/ProductChart.lean`, `HodgeLadder/Cycle/MultiplicativeNoReg.lean`; Mathlib `AlgebraicGeometry/Geometrically/Integral.lean`, `ProjectiveSpectrum/Basic.lean` (`Proj.fromOfGlobalSections`), `GammaSpecAdjunction.lean`, `Scheme.lean`, `RingTheory/MvPolynomial/Homogeneous.lean`; `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`, `docs/roadmap.md`.

Scratch (directory `scratch_rt/` in the worktree, deleted afterwards; about 10 s each with `lake env lean`):

| File | What it tried | Result |
|---|---|---|
| Probe1 | (a) `example (h : HodgeConjecture) (p : ℕ) : Hdg^p(p1p1; ℚ) ≤ algebraicCycleClassSpan p1p1 p := h p1p1 p`; (b) `⟨p1p1.left, p1p1.hom⟩ : SmoothProjectiveComplexVariety`; (c) `cycleComponentSheafClass p1p1 x hx` at coheight 1; (d) `@cycleComponentSheafClass_cup_of_transversal_noReg p1p1 _ _ _ 2 _` and its `#check` at `d := 2`; (e) `(prodChart_localChart_mem_maximalAtlas (d := 1) (e := 1) a b).1` against `IsManifold.maximalAtlas 𝓘(ℂ, Fin 2 → ℂ) ω (ComplexPoint p1p1)`; (f) `Nonempty (ComplexPoint p1p1)` from a point of ℙ¹ built as `Over.homMk (Spec.map (eval 0) ≫ chart 0 ≫ okaIso.hom)` and `pointProdHomeomorph`; (g) `segreF R a (X₀₀ X₁₁ − X₀₁ X₁₀) = 0` for every piece `a`; (h) `pairEquiv (k, l) = 2k + l` by `decide` | all elaborate, no error. Every instance argument of the statement of record, of the bundled wrapper and of the transversal theorem is found at `p1p1` by instance search |
| Probe2 | the two `erw` steps replaced by `rw`: `rw [← projectiveLine_hom_eq, Over.prodLeftIsoPullback_hom_fst_assoc]` in `p1p1OkaIso_hom_fst`, and `rw [Category.assoc, Category.assoc, show ProjectiveSpace.toBase (Fin (3 + 1)) (Spec ↧ℂ) = (projectiveSpace 3).hom from rfl, okaIsoSpace_hom_toBase, hso, p1p1OkaIso_hom_fst]` in `isProjective_p1p1`; `#check @awayEval` under `open HodgeLadder.Segre AlgebraicGeometry.ProjectiveSpace` | both replacements compile; `awayEval` is ambiguous between `HodgeLadder.Segre.awayEval` and the port's `AlgebraicGeometry.ProjectiveSpace.awayEval` (finding 9) |
| Probe3 | without `HodgeLadder.Tests.P1p1Witness`: `infer_instance` for `IsProjective`, `IsIntegral`, `SmoothOfRelativeDimension 2`, `Smooth` of `(projectiveLine ⨯ projectiveLine)` | the first three fail, `Smooth` succeeds (instance `smooth_prod` of `complex-points-prod`): the rung supplies three instances that were missing |

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`, with `[Classical.choice, Quot.sound, propext]` on all 22 named declarations. `lake build HodgeLadder.Tests.P1p1Witness` replays from cache (build current). No `sorry`, `native_decide`, `maxHeartbeats` or `unsafe` in either file; every public declaration has a docstring.

## 1. Is this the statement the literature makes?

Literature: a morphism f : X → T is projective (Hartshorne's sense, called H-projective in the Stacks project) when it factors as a closed immersion X → ℙⁿ_T followed by the projection, with ℙⁿ_T = ℙⁿ_ℤ ×_ℤ T [`Stacks`, definition of H-projective morphism, tag unverified; Hartshorne, Algebraic Geometry II.4, no key, unverified]. Over a field this agrees with every other definition. The Segre embedding ℙʳ × ℙˢ → ℙ^{rs+r+s}, ([a], [b]) ↦ [aᵢ bⱼ] in lexicographic order, is a closed immersion over any base [`Stacks`, Segre embedding, tag unverified; Hartshorne Ex. I.2.14, II.3.16, unverified]. ℙ¹ ×_ℂ ℙ¹ is a smooth projective surface, integral since ℙ¹ is geometrically integral [`Stacks`, tags unverified].

Upstream's `IsProjective f` is `Nonempty (Presentation f)`. Field by field:

| Field of `ProjectiveSpace.Presentation` | Literature | This rung | Match |
|---|---|---|---|
| `ambientDimension : ℕ` | n | `3` | yes; rs + r + s = 3 at r = s = 1 |
| `immersion : X ⟶ ℙ(Fin (ambientDimension + 1); T)`, with `ℙ(n; S) = pullback (terminal.from S) (terminal.from (Proj ℤ[n]))` | i : X → ℙⁿ_ℤ ×_ℤ T | `p1p1OkaIso.hom ≫ segre ℂ ≫ (okaIsoSpace 3).hom`, landing in `(projectiveSpace 3).left = ℙ(Fin (3 + 1); Spec ↧ℂ)` | yes; the port's `ℙₒ(3; ℂ) = Proj ℂ[x₀, …, x₃]` is carried to upstream's base change of `Proj ℤ[x]` by `okaIsoSpace 3`, the iso of the pullback square `isPullback_projectiveSpace` (checked in `p2-witness`) |
| `[isClosedImmersion : IsClosedImmersion immersion]` | i a closed immersion | filled by instance search from `hs : IsClosedImmersion s` (from `isClosedImmersion_segre`) and the two isomorphisms | yes |
| `immersion_toBase : immersion ≫ toBase … = f` | p ∘ i = f | `rw`/`erw` chain: `okaIsoSpace_hom_toBase`, `segre_toSpec`, `p1p1OkaIso_hom_fst`, ending at `p1p1.hom` | yes; the triangle is over `Spec ℂ` and its last step is `Over.w prod.fst` |

`isClosedImmersion_segre` is proved honestly: closed immersions are local at the target (`IsZariskiLocalAtTarget.of_iSup_eq_top` on the cover `U 3 R m`, `iSup_U`); `segre_preimage` identifies the preimage of `D₊(x_{(k,l)})` with the piece `D₊(a_k) × D₊(b_l)` of `prodCover`; there the map is the iso of the piece with `Spec Γ`, then `Spec` of `awayEval (segreF R a) …`, surjective by `awayEval_segre_surjective`, then `basicOpenIsoSpec.inv`. Surjectivity is the literature's argument: the chart coordinates are a_k b_l / (a_i b_j), so taking l = j (respectively k = i) recovers each coordinate of each factor, and the coordinate ring of the product of affine charts is generated by the two factors (`closure_range_union_eq_top` on Mathlib's `isPushout_appTop_of_isPullback`).

`segre` is glued from four local maps `zpoint`, each the point with homogeneous coordinates `segreF R a (X m) = a_{m.1} b_{m.2}` (dehomogenized in the chart a), over the cover `Scheme.Pullback.openCoverOfLeftRight` of the two standard covers. Compatibility on overlaps is "coordinates proportional by a unit" (`segre_hX`, from `exists_unit_of_comp_chart_eq` on each factor) plus "same constants" (`segre_hC`). This is the textbook construction.

Integrality. `geometricallyIntegral_toSpec n R` (for every ring R) reads `geometrically_iff_of_commRing`: every base change to a field K is integral; Oka's `isPullback_map` identifies it with `ℙₒ(n; K)`, whose integrality is the `p2-witness` argument over any field (the `Field` section, copied from `ProjectivePlane.lean` with ℂ replaced by K). Mathlib's instance at `Geometrically/Integral.lean:107` (geometrically integral, flat, universally open, over an integral scheme, locally noetherian) gives `IsIntegral (pullback projectiveLine.hom projectiveLine.hom)`, and `Over.prodLeftIsoPullback` carries it to `p1p1.left`. Flatness, universal openness and local noetherianity come from smoothness and finite type; all were found by `inferInstance`.

The rung's claim is the literature's.

## 2. Can the hypotheses be satisfied?

The rung is the instance. Non-vacuity of the object, checked in scratch (Probe1 f): `Nonempty (ComplexPoint p1p1)`, from the point x₀ ≠ 0, x₁/x₀ = 0 of ℙ¹ and `pointProdHomeomorph`. The file itself carries `nonempty_p1p1 : Nonempty p1p1.left` and `dim_p1p1 : dim p1p1.left = 2`. The scheme is nonempty and two-dimensional; IsProjective cannot hold vacuously for it (nothing degenerate like an empty scheme or an ambient dimension 0).

## 3. Is the conclusion trivially true?

No. `p1p1_witness` is a conjunction of four class instances on a concrete object; none of the classes unfolds to `True`, and three of the four instances are not found before this rung (Probe3). `IsProjective` needs a closed immersion into some ℙⁿ over the base, and the presentation's `isClosedImmersion` field carries the proof `isClosedImmersion_segre`; upstream's `IsProjective.isProper` derives properness from it, so the instance has consequences. No hypothesis is unused: the files have no theorem with hypotheses beyond instance arguments. Attempts at a short proof: `infer_instance` without the file fails for `IsProjective` and `IsIntegral` (Probe3).

## 4. Interface rung

Not one. No structure, no axiom.

## 5. Checker

`python3 tools/check.py --no-build` accepts; standard axioms on all 22 named declarations. Each named declaration is the one the ledger means: `isProjective_p1p1 : IsProjective p1p1.hom`, `isIntegral_p1p1 : IsIntegral p1p1.left`, `smoothOfRelativeDimension_p1p1 : SmoothOfRelativeDimension 2 p1p1.hom`, `p1p1_witness` their conjunction with `Smooth`, `exists_segre_oka R` the Segre closed immersion over `Spec R` for every ring, `isClosedImmersion_segre R`, `segre_toSpec R`. The ledger does not name the object `HodgeLadder.Tests.p1p1` that downstream rungs will cite, nor `HodgeLadder.Segre.segreF_X`, the lemma that pins the Segre coordinates (change 3).

## 6. Conventions

| Convention | Where | Choice | Truth depends on it? | Register |
|---|---|---|---|---|
| Product spelling | `p1p1 := projectiveLine ⨯ projectiveLine` | the categorical product in `Over (Spec ↧ℂ)`, as required by the ledger note of this rung and change 8 of `complex-points-prod` | no for this rung; downstream rungs must use the same `p1p1` (Probe1 shows the transversal theorem, the cycle classes and `prodChart` all elaborate at it) | row "Complex points of a product and product charts" (exists) |
| Relative dimension spelling | `smoothOfRelativeDimension_p1p1 : SmoothOfRelativeDimension 2 _` by `inferInstanceAs (… (1 + 1) _)` | literal 2 and `1 + 1` both found; `Fin 2` and `Fin (1 + 1)` atlases agree (Probe1 e) | no | exists (same row) |
| Segre coordinates | `HodgeLadder.Segre.segreF_X`, `pairEquiv := finProdFinEquiv.trans (finCongr _)` | x_{pairEquiv (k, l)} = a_k b_l, with pairEquiv (k, l) = 2k + l: x₀ = a₀b₀, x₁ = a₀b₁, x₂ = a₁b₀, x₃ = a₁b₁ (lexicographic, the literature's order); image in the quadric x₀x₃ = x₁x₂ (Probe1 g, h); first factor of `prodP1` is `pullback.fst` | no: a permutation of the coordinates of ℙ³ is an automorphism over the base, and `IsProjective` is a `Prop`, so no consumer can see the presentation | missing; change 1 |
| Homogeneous coordinates of Oka's ℙⁿ | port's `chart i`, `dehomogenize R i`, `U n R i = D₊(xᵢ)` | chart i has coordinates x_j / x_i (row "Algebraic affine chart and the standard chart of ℙⁿ") | no | exists |
| Comparison with upstream's ℙⁿ | `okaIsoSpace n` over `Spec ℂ` (`okaIsoSpace_hom_toBase`) | pullback iso along `ULift ℤ → ℂ` | no | exists via `p2-witness` |

No sign convention. The Koszul sign (−1)^p of Mathlib is not used. The one equality in the rung, `immersion_toBase`, is exact (an equality of morphisms of schemes); there is no scalar to misplace.

Borrowed inputs and their conventions: Mathlib's geometrically integral pullback instance (no convention), Mathlib's `IsClosedImmersion.spec_of_surjective`, `IsZariskiLocalAtTarget.of_iSup_eq_top`, `Proj.awayι_preimage_basicOpen`, `Proj.SpecMap_awayMap_awayι` (all about the same `Proj` that Oka's ℙₒ is), Oka's `isPullback_map`, `chart_toSpec`, `chart_preimage_U`, `opensRange_chart`, `dehomogenize_X_self`, `dehomogenize_X_succAbove`. Each is stated against the same `homogeneousSubmodule (Fin (N + 1)) R` grading (variables in degree 1) that `zpoint_preimage` and `exists_unit_of_zpoint_eq` fix with `X_mem_homogeneousSubmodule_one`.

## 7. Equality first

The rung is a test witness, neither identity nor inclusion. It is a step toward the equality `cycle-class-multiplicative-p1p1` ([{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)], open, in the ledger) through `p1p1-fibres-transversal` (open, in the ledger) and toward the test `cup-positive-degree-test` (open, in the ledger). The single equation in the rung, the triangle over `Spec ℂ`, is proved exactly.

## 7b. Non-vacuity

The smallest test that would fail if the object were degenerate: `Nonempty (ComplexPoint HodgeLadder.Tests.p1p1)` (upstream `AlgebraicGeometry.ComplexPoint`), checked in scratch (Probe1 f) from `HodgeLadder.ComplexPointProd.pointProdHomeomorph` and `AlgebraicGeometry.ProjectiveSpace.chart_toSpec`; it does not exist in the tree (optional change O3; `p1p1-fibres-transversal` will need points anyway). For the Segre map itself the smallest test is the quadric relation `segreF R a (X (pairEquiv (0,0)) * X (pairEquiv (1,1)) - X (pairEquiv (0,1)) * X (pairEquiv (1,0))) = 0`, from `HodgeLadder.Segre.segreF_X` by `ring` (Probe1 g). It is a sanity check only: it also holds for the colexicographic order and for the symmetric map x_{(k,l)} = a_k a_l, so it cannot pin the map. The pin is `segreF_X` itself (in the tree), together with the values of `pairEquiv` (Probe1 h, by `decide`); neither the quadric relation nor the pairEquiv values are in the tree (O3). Upstream's `HodgeConjecture` elaborates at `p1p1` (Probe1 a), and so does `HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal_noReg` at `d := 2` (Probe1 d), so the instances are the ones the consumers need.

## 8. Pin drift

Checked at the current pin (`2ead713`); no drift to diff. Upstream definitions the rung depends on and what a change would do:

| Upstream declaration | Risk |
|---|---|
| `ProjectiveSpace.Presentation`, `AlgebraicGeometry.IsProjective` | the file's header says it will move to Mathlib with #26061. If upstream switches to Mathlib's notion (a closed immersion into ℙ(n; T), or ample-bundle style over a general base), `isProjective_p1p1` breaks at build time, and the Segre immersion still applies. Truth cannot silently change: the anonymous constructor names every field |
| `ProjectiveSpace`, `ProjectiveSpace.toBase` | a change of the base-change presentation breaks `okaIsoSpace` and `projectiveLine` (already pinned by `p2-witness`, `projective-line-witness`) |
| `SmoothOfRelativeDimension.dim_eq`, `ComplexPoint.openParacompactSpace`, `Point` | used for `dim_p1p1`, `p1p1_openParacompactSpace`; signature changes break the build only |

Mathlib-side: `Over.prodLeftIsoPullback_hom_fst(_assoc)`, the geometrically integral pullback instance, `isPushout_appTop_of_isPullback`, `Proj.awayι`, `Proj.basicOpenIsoSpec`. Port-side: Oka's `ℙₒ` API is ours. A future Mathlib `AlgebraicGeometry.ProjectiveSpace` namespace would collide with the port's (an existing port-wide risk, outside this rung). The two `erw` steps unify `Over.mk_hom` and the reducible `p1p1`; both have `rw` replacements that compile (Probe2), so change 2.

## Findings

1. The object, the four instances and the presentation match upstream's `IsProjective` field by field and the literature's H-projective morphism; the Segre map is the lexicographic Segre map x_{(k,l)} = a_k b_l, a closed immersion over every ring, and the triangle over the base commutes exactly.
2. Upstream's `HodgeConjecture`, upstream's `SmoothProjectiveComplexVariety`, `cycleComponentSheafClass` and the transversal theorem `cycleComponentSheafClass_cup_of_transversal_noReg` (at `d := 2`) all elaborate at `p1p1` with the instances found by search; `prodChart_localChart_mem_maximalAtlas (d := 1) (e := 1)` lands in the `Fin 2` atlas of `ComplexPoint p1p1`.
3. Before this rung `IsProjective`, `IsIntegral` and `SmoothOfRelativeDimension 2` of `projectiveLine ⨯ projectiveLine` are not inferable; `Smooth` is (`smooth_prod`). The rung adds content.
4. Non-vacuity: `p1p1.left` and `ComplexPoint p1p1` are nonempty (the second in scratch), dimension 2.
5. No sign. The Segre coordinate order is recorded but invisible downstream (`IsProjective` is a `Prop`).
6. Name clashes and existing equivalents. No Segre map in Mathlib (`grep -i segre` finds only `NumberTheory/Height`), upstream, or the port. No Mathlib lemma named `isUnit_of_basicOpen_eq_top`; it is a two-line case of `RingedSpace.isUnit_of_isUnit_germ` and `Scheme.mem_basicOpen_top`. `ringHom_eq_of_toSpecΓ` is injectivity of `ΓSpec.adjunction.homEquiv` (Mathlib's `ext_to_Spec` is the other direction of the same adjunction); no clash. `sharp α` is `(ΓSpecIso A).inv ≫ α.appTop`, which Mathlib leaves unnamed. `eval₂_mul_of_isHomogeneous` has no Mathlib equivalent (Mathlib's `IsHomogeneous.eval₂` is about degrees). Mathlib's `Proj.fromOfGlobalSections` (and the port's `Proj.awayToLocalization`) builds `X ⟶ Proj 𝒜` from a global `A →+* Γ(X, ⊤)` generating the unit ideal; `zpoint Z F (X i)` is the case where one `F (X i)` is a unit. It cannot replace `glue` here, since the Segre coordinates are sections of 𝒪(1, 1), not global functions; it could replace `zpoint` and `point` at the cost of a comparison lemma (optional O4).
7. Placement. `General/SimplicialCochainSpan.lean` already imports the port, so a General module importing `LefschetzPort` has precedent. `General/Segre.lean` imports `HodgeLadder.General.ComplexPointProd` only for `closure_range_union_eq_top`, a pushout-of-rings lemma; that pulls upstream's complex-point stack into a pure scheme module. Acceptable; optional O2 moves the ring lemma.
8. The `Field` section of `P1p1Witness.lean` duplicates the ℂ proofs of `ProjectivePlane.lean` (`chart_zero_inter_nonempty`, `isReduced_okaProjectiveSpace`, `irreducibleSpace_okaProjectiveSpace`) for a general field. Two `IsIntegral ℙₒ(n; ℂ)` instances now exist (`Prop`, harmless). Optional O1.
9. `HodgeLadder.Segre.awayEval` and the port's `AlgebraicGeometry.ProjectiveSpace.awayEval` (field-valued points) share a short name. Under `open AlgebraicGeometry.ProjectiveSpace`, as in the sections `Chart` and `SegreMap` of `Segre.lean`, the identifier is overloaded and resolved by elaboration; under both opens a bare `#check @awayEval` is ambiguous (Probe2). It builds today; a signature change in the port could change which one elaborates. Optional O5.
10. Two `erw` steps, both removable by `rw` (Probe2). Change 2.
11. Docs not yet updated by the candidate: no conventions row for the Segre map, no `docs/gaps.md` rows for the new general lemmas, `docs/roadmap.md` row still `open` with "(Segre embedding missing)". Changes 1, 4, 5.

## Required changes

1. **`docs/conventions.md`**, new row after "Complex points of a product and product charts", exact text:

   `| Segre embedding of ℙ¹ × ℙ¹ | this repository, `HodgeLadder.Segre.segre`, `segreF`, `segreF_X`, `pairEquiv`, `prodCover`, `isClosedImmersion_segre`, `segre_toSpec` (`HodgeLadder/General/Segre.lean`), and `HodgeLadder.Tests.isProjective_p1p1`, `p1p1OkaIso` (`HodgeLadder/Tests/P1p1Witness.lean`, rung `p1p1-witness`); the port's `ProjectiveSpace.chart`, `dehomogenize`, `U`; Mathlib `finProdFinEquiv` | `prodP1 R = pullback (toSpec 1 R) (toSpec 1 R)`, first factor `pullback.fst` with coordinates a, second `pullback.snd` with coordinates b; x_{pairEquiv (k, l)} = a_k b_l with pairEquiv (k, l) = 2k + l (lexicographic): x₀ = a₀b₀, x₁ = a₀b₁, x₂ = a₁b₀, x₃ = a₁b₁, image in the quadric x₀x₃ = x₁x₂; on the piece D₊(a_i) × D₊(b_j) the coordinates are dehomogenized in chart (i, j) and x_{(i,j)} = 1 there; the presentation of `isProjective_p1p1` is `p1p1OkaIso.hom ≫ segre ℂ ≫ (okaIsoSpace 3).hom`, ambient dimension 3; no sign, no scalar | none: `IsProjective` is a `Prop`, and any permutation of the coordinates of ℙ³ is an automorphism over the base, so no consumer can see the coordinate order. A future rung that uses the Segre map itself (a pullback of the hyperplane class, 𝒪(1) restricting to 𝒪(1, 1)) must state its coordinate order against this row | read from source; quadric relation and pairEquiv values checked in scratch (red team 2026-11-27, `p1p1-witness`) |`

2. **Replace the two `erw` steps** in `HodgeLadder/Tests/P1p1Witness.lean` with the forms that compile (Probe2):
   - in `p1p1OkaIso_hom_fst`, replace `rw [← projectiveLine_hom_eq]` and `erw [Over.prodLeftIsoPullback_hom_fst_assoc]` by `rw [← projectiveLine_hom_eq, Over.prodLeftIsoPullback_hom_fst_assoc]`;
   - in `isProjective_p1p1`, replace the `immersion_toBase` proof by
     `rw [Category.assoc, Category.assoc, show ProjectiveSpace.toBase (Fin (3 + 1)) (Spec ↧ℂ) = (projectiveSpace 3).hom from rfl, okaIsoSpace_hom_toBase, hso, p1p1OkaIso_hom_fst]`.

3. **`ledger/ladder.json`, rung `p1p1-witness`**: add to `declarations` `HodgeLadder.Tests.p1p1`, `HodgeLadder.Segre.pairEquiv`, `HodgeLadder.Segre.segreF_X`, `HodgeLadder.Tests.p1p1OkaIso_hom_fst`; append to `note`, exact text: " Red team pass with changes (docs/sketches/p1p1-witness.redteam.md): upstream's HodgeConjecture, SmoothProjectiveComplexVariety, cycleComponentSheafClass and cycleComponentSheafClass_cup_of_transversal_noReg (d := 2) elaborate at p1p1 with the instances found by search; ComplexPoint p1p1 is nonempty. Segre coordinates: conventions row \"Segre embedding of ℙ¹ × ℙ¹\"; downstream rungs cite the object as HodgeLadder.Tests.p1p1 and pass d := 2 explicitly."

4. **`docs/gaps.md`, "General lemmas kept local"**, two rows, exact text:

   `| `HodgeLadder.Segre.eval₂_mul_of_isHomogeneous` (scaling the variables by c scales a degree-n homogeneous polynomial by cⁿ), `awayEval` and its lemmas (`awayEval_mk`, `awayEval_mk_of_eq_one`, `awayEval_fromZero`, `awayEval_comp_awayMap`, `awayEval_eq_of_smul`, `comp_awayEval`), `isUnit_of_basicOpen_eq_top`, `ringHom_eq_of_toSpecΓ`, `sharp` and its lemmas, `point`, `zpoint` and their lemmas (`point_eq_point`, `zpoint_preimage`, `exists_unit_of_zpoint_eq`, `zpoint_eq_of_smul`, `zpoint_toSpec`, `comp_zpoint`), `glue`, `ι_glue`, `comp_chart`, `exists_unit_of_comp_chart_eq`; the Segre map `segre`, `segre_toSpec`, `segre_preimage`, `awayEval_segre_surjective`, `isClosedImmersion_segre` | `HodgeLadder.General.Segre` | morphisms to Proj of a polynomial ring from local homogeneous coordinates, and the Segre closed immersion ℙ¹ ×_R ℙ¹ ⟶ ℙ³ over every ring; Mathlib has `Proj.fromOfGlobalSections` (global coordinates only) and no Segre map; `HodgeLadder.Segre.awayEval` shares its short name with the port's `AlgebraicGeometry.ProjectiveSpace.awayEval`; at a pin bump check Mathlib for a Segre embedding, for morphisms to ℙⁿ from line-bundle data, and for an injectivity lemma of `ΓSpec.adjunction.homEquiv` in `toSpecΓ` form; rung `p1p1-witness` | 2026-11-27 |`

   `| `HodgeLadder.Tests.geometricallyIntegral_toSpec` (Oka's ℙⁿ over every ring is geometrically integral), `isIntegral_okaProjectiveSpace_field`, `irreducibleSpace_okaProjectiveSpace_field`, `isReduced_okaProjectiveSpace_field`, `isIrreducible_U_field`, `chart_zero_inter_nonempty_field` | `HodgeLadder.Tests.P1p1Witness` | ℙⁿ over a field is integral, the `p2-witness` argument for any field; general facts about the port's ℙₒ kept with their first consumer; at a pin bump check Mathlib for integrality and geometric integrality of projective space; rung `p1p1-witness` | 2026-11-27 |`

5. **`docs/roadmap.md`**, row `p1p1-witness`: status `checked`; replace "ℙ¹ × ℙ¹ integral, smooth, projective (Segre embedding missing)" with "ℙ¹ × ℙ¹ integral, smooth of relative dimension 2, projective through the Segre closed immersion into ℙ³ (`HodgeLadder.General.Segre`)".

## Optional changes

- O1. Derive the ℂ instances of `ProjectivePlane.lean` from the new field versions, or move the field versions there and drop the copies.
- O2. Move `HodgeLadder.ComplexPointProd.closure_range_union_eq_top` to a ring-level General module so that `General/Segre.lean` stops importing the complex-point stack.
- O3. Add to the tree `Nonempty (ComplexPoint p1p1)` (Probe1 f, about ten lines; `p1p1-fibres-transversal` needs points anyway), the `pairEquiv` values (Probe1 h, one line by `decide`), and the quadric relation (Probe1 g, two lines; a sanity check, see 7b).
- O4. A comparison `zpoint Z F (X i) … = Proj.fromOfGlobalSections _ F _` when `F (X i)` is a unit, so the local constructor sits on Mathlib's API.
- O5. Rename `HodgeLadder.Segre.awayEval` (for example to `awayEvalRingHom`) to remove the overload with the port's `ProjectiveSpace.awayEval`.
- O6. Cite the definition of a projective morphism and the Segre embedding with keys: a `Hartshorne1977` row in `docs/references.md` (II.4 projective morphism, Ex. I.2.14 and II.3.16 Segre embedding; numbering unverified), or `Stacks` with tags once verified.

CLAUDE.md is the coordinator's; no change to it is required of the prover.
