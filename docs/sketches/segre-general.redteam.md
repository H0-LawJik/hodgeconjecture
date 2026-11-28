# Red team: `segre-general` (foundation, issue #227, T1 plan node E6)

Date: 2026-11-28. Worktree `segre-general`, branch `track/segre-general`, candidate commit `692770c` on base `0fd3685`. `main` is two commits ahead (`eb665a1`, `8e84167`); neither touches the pins, `HodgeLadder/General/Segre.lean` or `HodgeLadder/Tests/ProjectivePlane.lean`, so a rebase only meets the append to `HodgeLadder.lean`. File: `HodgeLadder/Segre/General.lean` (module `HodgeLadder.Segre.General`, namespace `HodgeLadder.Segre.General`, 431 lines, layer 7 by `tools/pinwalk.py`), imported from `HodgeLadder.lean`; ledger entry `checked` with 29 declarations. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same as `main` (the worktree's `.lake/packages` is `main`'s).

**Verdict: pass with changes.**

No sign and no scalar enter this rung. The Segre coordinates are x_{(k,l)} = a_k b_l exactly; the only equations are `segre_toSpec`, `prodImmersion_fst` and the presentation's triangle `immersion_toBase`, equalities of morphisms of schemes proved exactly; the conclusion `IsProjective (X ⨯ Y).hom` is a `Prop`. The changes are a non-vacuity test, two docstring or comment edits, a gaps row move and a ledger note.

Read: ledger entries `segre-general`, `p1p1-witness`, `elliptic-square-witness`; `docs/notes/2026-11-27-t1-plan.md` (E6, E7); `docs/sketches/p1p1-witness.redteam.md`, `docs/sketches/complex-points-prod.redteam.md` (instance method, finding 6 on placement); upstream `Definitions/AlgebraicGeometry/ProjectiveSpace.lean` (`ProjectiveSpace`, `toBase`, `Presentation`, `IsProjective`, `IsProjective.isProper`); `HodgeLadder/General/Segre.lean`, `HodgeLadder/Tests/{ProjectivePlane,P1p1Witness,EllipticCurve}.lean`; Mathlib `CategoryTheory/MorphismProperty/Limits.lean` (`pullbackMap`), `AlgebraicGeometry/Morphisms/{ClosedImmersion,Proper,Finite}.lean`; `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`, the handoff `docs/handoffs/2026-11-28-segre-general.md`.

Scratch (directory `scratch_rt_sg/` in the worktree, deleted afterwards; `lake env lean`, 8 to 28 s each):

| File | What it tried | Result |
|---|---|---|
| Probe1 | (a) `pairEquiv 1 2 (1, 0) = 3`, `pairEquiv 1 2 (0, 2) = 2`, `pairEquiv 2 1 (1, 0) = 2`, `pairEquiv 2 1 (2, 1) = 5` by `decide`; `segreDim 2 3 = 11`, `segreDim 0 0 = 0` by `rfl`; (b) `pairEquiv 1 1 = HodgeLadder.Segre.pairEquiv` by `rfl`; (c) the swapped order `fun p => pairEquiv 1 1 p.swap` differs from `pairEquiv 1 1`, by `decide`; (d) every 2 × 2 minor x_{(k,l)} x_{(k',l')} − x_{(k,l')} x_{(k',l)} maps to 0 under `segreF R 1 2 a`, by `segreF_X` and `ring`; (e) `(prodPresentation P Q).ambientDimension = d * e + d + e` and (f) `(prodPresentation P Q).immersion = prodImmersion P Q ≫ segre ℂ _ _ ≫ (okaIsoSpace _).hom`, both `rfl`; (g) `IsProjective` and `IsProper` of `(ellipticCurve ⨯ ellipticCurve).hom` by `inferInstance`; (h) `IsClosedImmersion (segre R 0 0)`; (i) `IsProjective (X ⊗ Y).hom` from the two factor instances; (j) `inferInstance` for `MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0}`, with trace | (a) to (h) elaborate; (i) is not inferred (finding 6); (j) fails, `tryResolve` of both candidate instances fails (finding 7) |
| Probe2 | the gotcha in plain `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: three spellings of the goal; the same goal under `set_option backward.isDefEq.respectTransparency.types false`; the same goal for `@IsOpenImmersion` | all three spellings fail without the option; with it, `inferInstance` succeeds; `IsOpenImmersion` succeeds without it. Mathlib's own `IsClosedImmersion.comp` carries the same option (finding 7) |
| Old / New | 16 instance searches with `trace.Meta.synthInstance`, the same imports (`P1p1Witness`, `EllipticCurve`, `EllipticCurveSmooth`, `ComplexPointProd`) without and with `HodgeLadder.Segre.General`: `IsProjective` of `projectivePlane`, `projectiveSpace 4`, `p1p1`, `ellipticCurve`; `IsProper` of the same three; `Smooth` of `p1p1`, ℙ¹ ⨯ ℙ², (ℙ¹ ⨯ ℙ²) ⨯ ℙ¹; `SmoothOfRelativeDimension (1 + 1) p1p1.hom`, `1 ellipticCurve.hom`, `2 projectivePlane.hom`; `IsIntegral p1p1.left`; `IsProper X.hom` from `[IsProjective X.hom]`; `Smooth (X ⨯ Y).hom` from the factors; and four failing or new goals (bare `IsProjective X.hom`, `IsProjective (X ⨯ Y).hom` with one factor instance, `IsProper (X ⨯ Y).hom` with none, `IsProjective (ℙ¹ ⨯ ℙ¹ ⨯ ℙ¹).hom`) | 27.8 s and 26.3 s wall; 58061 and 58108 trace lines. After normalizing line numbers the diff is: `isProjective_prod` added to two candidate lists for `p1p1` (tried second, `isProjective_p1p1` wins first); the one-hypothesis failing goal gains 14 lines and the no-hypothesis `IsProper (X ⨯ Y)` goal 4 lines (one application, failing on the factor); the triple product now resolves through `isProjective_prod` then `isProjective_p1p1`. No `Smooth`, `SmoothOfRelativeDimension` or `IsIntegral` trace changes (finding 5) |
| Probe3, Probe4 | `¬ IsProjective (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))))` in the file's namespace and opens, with `#print axioms` | compiles in six lines; axioms `[propext, Classical.choice, Quot.sound]` (section 7b, change 1) |

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`; the 29 named declarations of the rung all appear, `segreDim` with no axioms, `segreDim_add_one` with `propext`, the other 27 with `[Classical.choice, Quot.sound, propext]`. `lake env lean HodgeLadder/Segre/General.lean`: 7.6 s. No `sorry`, `native_decide`, `maxHeartbeats`, `set_option`, `erw` or `unsafe` in the file.

## 1. Is this the statement the literature makes?

Literature. A morphism f : X → T is H-projective when it factors as a closed immersion X → ℙⁿ_T followed by the projection [`Stacks`, definition of H-projective morphism, tag unverified]. The Segre morphism ℙʳ_S ×_S ℙˢ_S → ℙ^{rs+r+s}_S, ([a], [b]) ↦ [a_k b_l] with the pairs in lexicographic order, is a closed immersion over every base [`Stacks`, Segre embedding, tag unverified]; hence a fibre product of H-projective morphisms over T is H-projective (closed immersions are stable under base change and composition) [`Stacks`, tag unverified].

Upstream's `IsProjective f` is `Nonempty (Presentation f)`. Field by field, for `prodPresentation P Q` with `d = P.ambientDimension`, `e = Q.ambientDimension`:

| Field of `ProjectiveSpace.Presentation` | Literature | This rung | Match |
|---|---|---|---|
| `ambientDimension : ℕ` | (d + 1)(e + 1) − 1 | `segreDim d e = d * e + d + e`, with `segreDim_add_one : segreDim m n + 1 = (m + 1) * (n + 1)` | yes; in ℕ the truncated (m + 1)(n + 1) − 1 equals mn + m + n since the product is at least 1; Probe1 (e) by `rfl` |
| `immersion : X ⟶ ℙ(Fin (ambientDimension + 1); T)` | X ×_T Y → ℙᵈ_T ×_T ℙᵉ_T → ℙ^N_T | `prodImmersion P Q ≫ segre ℂ d e ≫ (okaIsoSpace N).hom` (Probe1 f); `prodImmersion` is `Over.prodLeftIsoPullback` followed by `pullback.map` of `P.immersion ≫ (okaIsoSpace d).inv` and `Q.immersion ≫ (okaIsoSpace e).inv` over `𝟙 (Spec ℂ)` | yes; `okaIsoSpace` is the `p2-witness` comparison of Oka's `ℙₒ(N; ℂ)` with upstream's base change of `Proj ℤ[x]` |
| `[isClosedImmersion : IsClosedImmersion immersion]` | composite of closed immersions | instance search from `isClosedImmersion_prodImmersion` (Mathlib's `MorphismProperty.pullbackMap` for `@IsClosedImmersion`, then the iso on the left) and `isClosedImmersion_segre` | yes |
| `immersion_toBase` | p ∘ i = f | `okaIsoSpace_hom_toBase`, `segre_toSpec`, `prodImmersion_fst`; the last step is `Over.w prod.fst` | yes, exact |

`isClosedImmersion_segre` is the literature's proof, generalized from the reviewed m = n = 1 case without change of shape: closed immersions are local at the target (`IsZariskiLocalAtTarget.of_iSup_eq_top` over the standard opens `U N R`); the preimage of D₊(x_{(k,l)}) is the piece D₊(a_k) × D₊(b_l) of `prodCover` (`segre_preimage`); on it the map is the piece's iso with `Spec Γ`, `Spec` of `awayEvalOf (segreF R m n a)`, and `basicOpenIsoSpec.inv`. Surjectivity (`awayEvalOf_segre_surjective`): with a = (i, j), the chart coordinate a_{i.succAbove k}/a_i is the image of x_{(i.succAbove k, j)}/x_{(i,j)}, and symmetrically for b; the ring of the product of affine charts is generated by the two factors (`closure_range_union_eq_top` on Mathlib's `isPushout_appTop_of_isPullback`). The glue (`segre_hX`, `segre_hC`) is the m = n = 1 argument: on overlaps the two factor coordinates are proportional by units c₁, c₂, so the Segre coordinates are proportional by c₁c₂.

The rung's claim is the literature's, specialized to T = Spec ℂ for the product instance; the Segre map itself is stated over every commutative ring R.

## 2. Can the hypotheses be satisfied?

Yes. `isProjective_p1p2` in the file (ℙ¹ ⨯ ℙ², both factors by `isProjective_projectiveSpace`). Probe1 (g): `IsProjective (ellipticCurve ⨯ ellipticCurve).hom` and `IsProper` of the same by `inferInstance`, so the consumer `elliptic-square-witness` gets projectivity of E × E with no further work. The Segre map exists for every (m, n) including (0, 0) (Probe1 h).

## 3. Is the conclusion trivially true?

No. `IsProjective` needs a closed immersion into some upstream ℙᴺ over the base, and upstream derives `IsProper` from it, so the instance has consequences; Probe3 shows `IsProjective` fails for the affine line, so the class is not vacuous (section 7b). Without the candidate, `IsProjective (ℙ¹ ⨯ ℙ¹ ⨯ ℙ¹).hom` and `IsProjective (X ⨯ Y).hom` from the factor instances are not inferred (Old trace: "no instances"). No upstream, port or Mathlib lemma gives projectivity of products or of composites (grep for `IsProjective.comp`, `isProjective_comp`, `IsProjective (pullback`, `IsProjective (… ⨯`: no hits outside this file), so no short proof bypasses the Segre map. No hypothesis is unused: `[IsProjective X.hom]`, `[IsProjective Y.hom]` supply the two presentations. No `ℕ∞`, no empty index type: the index type `Fin (m + 1) × Fin (n + 1)` is nonempty for all m, n.

## 4. Interface rung

Not one. No structure, no axiom.

## 5. Checker

`python3 tools/check.py --no-build` accepts, standard axioms on all 29 named declarations. Each is the one the ledger means: `segre R m n : prodP R m n ⟶ ℙₒ(segreDim m n; R)`, `isClosedImmersion_segre R m n : IsClosedImmersion (segre R m n)`, `segre_toSpec`, `segre_one_one : segre R 1 1 = HodgeLadder.Segre.segre R`, `isProjective_prod : IsProjective (X ⨯ Y).hom` for `X Y : Over (Spec ↧ℂ)`, `isProjective_p1p2`. Unnamed helpers (`chartFst`, `chartSnd`, `segreIdx`, `prodCover_f_fst`, `prodCover_f_snd`, the anonymous `IsOpenImmersion` instance) follow the `p1p1-witness` practice and are fine.

`segre_one_one` by `rfl` is a genuine consistency check: the general and the reviewed m = n = 1 maps share `glue`, `zpoint` and `finProdFinEquiv`, and the swapped coordinate order is a different index map (Probe1 c), whose Segre map differs from the reviewed one by a nontrivial permutation of ℙ³, so `rfl` could not close it. It carries the field-by-field review of `p1p1-witness` to (1, 1); for general (m, n) the pin is `segreF_X` with `pairEquiv_val`.

## 6. Conventions

| Convention | Where | Choice | Truth depends on it? | Register |
|---|---|---|---|---|
| Segre coordinate order | `pairEquiv`, `pairEquiv_val`, `segreF_X` | x_{pairEquiv (k, l)} = a_k b_l, pairEquiv (k, l) = l + (n + 1)k, lexicographic, first factor `pullback.fst` (Probe1 a to d) | no: a permutation of the coordinates of ℙᴺ is an automorphism over the base and `IsProjective` is a `Prop`; load-bearing only for a future pullback of the hyperplane class | row "Segre embedding of ℙᵐ × ℙⁿ" (added by the candidate; text checked against the source, accurate) |
| Ambient dimension | `segreDim` | mn + m + n, not the truncated subtraction (m + 1)(n + 1) − 1 | no for `IsProjective` (existential); a consumer that reads the number gets mn + m + n | same row |
| Product spelling | `isProjective_prod` on `X ⨯ Y` | the categorical product in `Over (Spec ↧ℂ)`; not found on Mathlib's `X ⊗ Y` (Probe1 i) | no for truth; yes for instance search | row "Complex points of a product and product charts" (exists); change 2 records the matching caveat at the instance |
| Oka's ℙⁿ against upstream's | `okaIsoSpace`, `okaIsoSpace_hom_toBase`, new `okaIsoSpace_inv_toSpec` | the `p2-witness` comparison | no | exists via `p2-witness` |
| Chart coordinates of ℙⁿ | port's `chart`, `dehomogenize`, `U` | chart i has coordinates x_j / x_i | no | row "Algebraic affine chart and the standard chart of ℙⁿ" (exists) |

No sign convention: Mathlib's Koszul sign (−1)^p appears nowhere. Borrowed inputs (Mathlib `pullbackMap`, `IsClosedImmersion.spec_of_surjective`, `IsZariskiLocalAtTarget.of_iSup_eq_top`, `Proj.basicOpenIsoSpec`; port `chart_toSpec`, `chart_preimage_U`, `opensRange_chart`, `dehomogenize_X_self`, `dehomogenize_X_succAbove`; the ladder's `glue`, `zpoint`, `exists_unit_of_comp_chart_eq`) are all stated against the same `homogeneousSubmodule (Fin (N + 1)) R` grading with variables in degree 1, as fixed by `X_mem_homogeneousSubmodule_one`. No new row is missing.

## 7. Equality first

Neither identity nor inclusion: a foundation instance. Its equations are exact (section 1). It is a step toward the test `elliptic-square-witness` (open, in the ledger) and through it the Weil-class rungs on E × E.

## 7b. Non-vacuity

If upstream's `IsProjective` were trivially true (an empty structure, a field dropped at a bump), every positive instance on the ladder, this one included, would still check. The smallest test that would fail is a negative one, `¬ IsProjective` of a non-proper morphism, stated through upstream's `AlgebraicGeometry.IsProjective` and `AlgebraicGeometry.IsProjective.isProper` with Mathlib's `IsFinite.iff_isProper_and_isAffineHom`, `IsFinite.SpecMap_iff`, `RingHom.finite_algebraMap` and `Polynomial.not_finite`. It does not exist in the tree (grep for `¬ IsProjective`, `not_isProjective`, `¬ IsProper`: no hits). It compiles in six lines (Probe4); change 1 adds it to this file. For the Segre map, the minors of Probe1 (d) are a sanity check only; the pin is `segreF_X` with `pairEquiv_val`, both in the tree.

## 8. Pin drift

Checked at the current pin `2ead713`, the pin of `main`; no drift to diff. Upstream declarations the rung depends on: `ProjectiveSpace.Presentation` (all four fields named in `prodPresentation`, so a change of fields breaks the build), `AlgebraicGeometry.IsProjective` (the anonymous constructor `⟨⟨_⟩⟩` breaks if the class changes shape), `ProjectiveSpace.toBase` (through `okaIsoSpace_hom_toBase`, already pinned by `p2-witness`). The upstream file says `IsProjective` will move to Mathlib (#26061); if it does, this instance and `not_isProjective_affineLine` (change 1) are the two places to re-check. Mathlib-side: `MorphismProperty.pullbackMap` (renamed from `pullback_map` on 2026-03-20; the old alias is deprecated), `Over.prodLeftIsoPullback`, and the `respectTransparency` behaviour of finding 7.

## Findings

1. The presentation of `X ⨯ Y` matches upstream's `Presentation` field by field and the literature's H-projective product; the Segre map is the lexicographic x_{(k,l)} = a_k b_l for all (m, n), a closed immersion over every ring, lying over `Spec R`; every equation is exact.
2. `segre_one_one` by `rfl` is a real check against the reviewed ℙ¹ × ℙ¹ map (section 5); the general index map agrees with it and differs from the swapped order.
3. Ambient dimension `segreDim d e = de + d + e`, with `segreDim_add_one` relating it to (d + 1)(e + 1); correct.
4. E × E: `IsProjective (ellipticCurve ⨯ ellipticCurve).hom` and its `IsProper` resolve by `inferInstance`.
5. Instance safety. Head `IsProjective (Over.hom (X ⨯ Y))`, subgoals on the two factors, structurally smaller: no loop. Over 16 searches the only trace changes are on `IsProjective` goals of a product shape; `Smooth`, `SmoothOfRelativeDimension`, `IsIntegral` and `IsProper` of non-products are unchanged; the failing goals gain 4 to 14 trace lines; total wall time unchanged within noise (27.8 s and 26.3 s). `isProjective_p1p1` and `isProjective_prod` both apply to `p1p1`; `Prop`, so no diamond.
6. The instance is not found for Mathlib's `X ⊗ Y` (Probe1 i), the second product spelling at the pin. Consumers use `⨯` (`elliptic-square-witness` title, `p1p1`), so this is a caveat for the docstring (change 2).
7. The gotcha reproduces, with a narrower cause than the handoff gives. Mathlib's `IsMultiplicative @IsClosedImmersion` instance exists and resolves; `IsStableUnderComposition` fails because unifying it with the parent projection fails under the default `backward.isDefEq.respectTransparency.types`; with the option set false, `inferInstance` succeeds, and Mathlib's own `IsClosedImmersion.comp` sets that option for the same reason. `@IsOpenImmersion` is unaffected. Recorded only in the handoff; the use site has no comment (change 3).
8. Mathlib, upstream and port equivalents: none. `grep -i segre` in Mathlib finds only `NumberTheory/Height/Basic.lean` (heights of x_i y_j, no schemes); none in upstream or the port; no projectivity of products anywhere. `pinwalk --clash` reports only `pairEquiv` against `Nat.pairEquiv`, harmless (different namespace).
9. Placement. `HodgeLadder/Segre/General.lean` is `next.py`'s fallback shape and opens a single-file directory; four such directories already exist (`Glpos`, `Lefschetz`, `Pullback`, `Torus`). It imports `HodgeLadder.Tests.ProjectivePlane` for `okaIsoSpace`, which `HodgeLadder/General/` modules avoid; `Hodge/WedgeSheafify.lean` and `Hodge/DeRhamScalarSheaf.lean` are precedent for a non-Tests module importing Tests. Acceptable as is. The two Segre homes share short names (`segre`, `segreF`, `pairEquiv`, `prodCover`, `segre_toSpec`, `isClosedImmersion_segre`) across `HodgeLadder.Segre` and `HodgeLadder.Segre.General`; a file that opens both gets ambiguous identifiers (optional O2).
10. Ledger declaration list: complete for the rung's statements; `HodgeLadder.Segre.General.not_isProjective_affineLine` to be added with change 1.
11. Gaps row: layer 7 is correct (`pinwalk`), text accurate; it sits between two layer-2 rows (`HodgeLadder.General.Segre`, `HodgeLadder.General.Hypersurface`), against the "rows within a category by layer" rule of `docs/gaps.md` (change 4).
12. Conventions row "Segre embedding of ℙᵐ × ℙⁿ": accurate against the source, placed after the ℙ¹ × ℙ¹ row. No sign.

## Required changes

1. **Non-vacuity test.** In `HodgeLadder/Segre/General.lean`, section `Tests`, after `isProjective_p1p2`, add (compiles in the file's namespace and opens, Probe4):

   ```lean
   /-- The affine line over `ℂ` is not projective in upstream's sense: a projective morphism is
   proper (upstream's `IsProjective.isProper`), a proper affine morphism is finite, and `ℂ[X]` is
   not a finite `ℂ`-module. A non-vacuity check on `IsProjective`. -/
   theorem not_isProjective_affineLine :
       ¬ IsProjective (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)))) := by
     intro _
     have hf : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)))) :=
       IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
     rw [IsFinite.SpecMap_iff] at hf
     exact Polynomial.not_finite (RingHom.finite_algebraMap.mp hf)
   ```

   In the module docstring, "Main results", after the `isProjective_p1p2` bullet add: `* test `HodgeLadder.Segre.General.not_isProjective_affineLine`: the affine line over ℂ is not projective`. In `ledger/ladder.json`, rung `segre-general`, append `"HodgeLadder.Segre.General.not_isProjective_affineLine"` to `declarations`.

2. **Docstring of `isProjective_prod`.** Append, exact text: "The instance matches the categorical product `X ⨯ Y`; it is not found for Mathlib's `X ⊗ Y` (`CartesianMonoidalCategory (Over S)`), which is not defeq to `X ⨯ Y` (conventions row \"Complex points of a product and product charts\")."

3. **The gotcha, at the use site and in the handoff.** In `isClosedImmersion_prodImmersion`, on the line before `have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=`, add the comment, exact text: `-- Not found by `inferInstance` at the pin: the parent projection of Mathlib's `IsMultiplicative @IsClosedImmersion` fails to unify under the default `backward.isDefEq.respectTransparency.types`, which Mathlib's own `IsClosedImmersion.comp` sets to false.` In `docs/handoffs/2026-11-28-segre-general.md`, replace the Gotcha line by, exact text: "- Gotcha: `inferInstance` fails on `MorphismProperty.IsStableUnderComposition @IsClosedImmersion` although `IsMultiplicative` resolves: unification with the parent projection fails under the default `backward.isDefEq.respectTransparency.types` (with the option false it succeeds, and Mathlib's `IsClosedImmersion.comp` sets it for the same reason; `@IsOpenImmersion` is unaffected). `IsMultiplicative.toIsStableUnderComposition` by hand works."

4. **`docs/gaps.md`.** Move the row beginning `| `HodgeLadder.Segre.General.segre` (the Segre closed immersion` unchanged to sit after the row of `HodgeLadder.General.Hypersurface` (layer 2) and before the row of `HodgeLadder.Tests.P1p1Witness` (layer 7).

5. **`ledger/ladder.json`, rung `segre-general`, `note`.** Append, exact text: " Red team pass with changes (docs/sketches/segre-general.redteam.md): presentation checked field by field against upstream's Presentation, ambient dimension segreDim d e = de + d + e; segre_one_one is a real check against the reviewed ℙ¹ × ℙ¹ map; IsProjective (ellipticCurve ⨯ ellipticCurve).hom resolves; the instance matches X ⨯ Y and not Mathlib's X ⊗ Y; instance traces on 16 existing searches change only on product-shaped IsProjective goals; non-vacuity test not_isProjective_affineLine. No sign."

## Optional changes

- O1. Module docstring: add "Literature: the Segre embedding is a closed immersion over every base [`Stacks`, Segre embedding, tag unverified]."
- O2. Rename the general declarations apart from the m = n = 1 ones (for example `segreMN`), or state the m = n = 1 map as `HodgeLadder.Segre.General.segre R 1 1` in a later cleanup, so that a file opening both namespaces gets no ambiguous identifiers.
- O3. Name the anonymous instance `IsOpenImmersion ((prodCover R m n).f a)` (`isOpenImmersion_prodCover_f`), as in `complex-points-prod` O2.
- O4. Wrap the statement line of `isProjective_p1p2` (113 characters) at 100.
- O5. A corollary `IsProjective (X ⊗ Y).hom` by transport along `IsLimit.conePointUniqueUpToIso (tensorProductIsBinaryProduct X Y) (limit.isLimit _)`, if a consumer picks the `⊗` spelling.
