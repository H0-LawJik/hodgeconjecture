# Red team: `affine-chart-analytic` (statement)

Date: 2026-11-26. Worktree `affine-chart-analytic`, base `c486870`, uncommitted `HodgeLadder/Normalization/AffineChart.lean` and the section "affine-chart-analytic: statement" of `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713` (package checkout and `lake-manifest.json` agree), Lean and Mathlib `v4.35.0-rc4`. Statement pass, before the proofs.

Targets: `affineCoordinates`, `affineChart`, the rung `affineChart_mem_maximalAtlas` (sorry), `affineChart_compatible_localChart` (from the rung), `affineChart_apply_map`, `affineChart_source`, `affineChart_target`; the ℙⁿ instance `projectiveChartImmersion`, `projectiveChartOpen(_eq)`, `projectiveChartSchemeIso(_over)`, `projectiveChartIso`, `projectiveChart`, `projectiveChart_mem_maximalAtlas`, `projectivePlane_chart_mem_maximalAtlas` and `projectiveChart_symm_underlying` (sorry).

Read at the pin: upstream `Lemmas/AlgebraicGeometry/ComplexPoint/{Manifold,AffineSpace,AnalyticMap,Open,Basic}.lean`, `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean` (`Point`, `map`, `underlying`, `evaluate`, `evaluate_map`, `evaluate_res`, `isoMapHomeomorph`); Mathlib `AlgebraicGeometry/AffineSpace.lean`, `Analysis/Analytic/Polynomial.lean`; the port's `Oka/AlgebraicGeometry/ProjectiveSpace/{Basic,Points}.lean` and `Oka/RingTheory/MvPolynomial/HomogeneousLocalization.lean` (`toAwayX`, `awayXEquiv`); this repository's `Normalization/ChartStep.lean`, `Normalization/Germ.lean`, `Tests/ProjectivePlane.lean`; `cycle-class-multiplicative.redteam.md` finding 12; `cycle-class-germ.redteam.md`.

Scratch files (inside the worktree, deleted afterwards; each is a copy of `AffineChart.lean` with additions, since the module has no `.olean`):

| File | What | Result |
|---|---|---|
| RT1 | trivial proofs of the rung; the hypotheses on ℙ²; the inverse chart lands in the source | trivial proofs fail (section 3); the rest compiles |
| RT2 | a proof of `projectiveChart_symm_underlying` for every n and i; the corollary `projectiveChart_symm_mem_U_iff`; index checks on ℙ² at i = 2 and i = 0; `#print axioms` of every sorry-free declaration | all compile; standard axioms (`propext`, `Classical.choice`, `Quot.sound`) for every sorry-free declaration and both new proofs; `affineChart_compatible_localChart` carries `sorryAx` from the rung only |
| RT3 | an open-immersion constructor `openImmersionAffineIso`, `openImmersionChart`, `openImmersionChart_symm` | compiles, no sorry |
| RT4 | `#synth` of the charted space and manifold instances on ℙ² | upstream's `instChartedSpace…` at d = 2 and `isManifold_omega (projectiveSpace 2) 2` |
| RT5 | the route's new lemma, analyticity of evaluation of a regular section on an open of 𝔸ⁿ in affine coordinates; the statement of a conjugation test | the lemma is proved (30 lines, standard axioms); the test statement elaborates |
| RT6 | the four Lean blocks of sections 7, 8 and 9 exactly as printed here, in a copy of the file with the sorry body of `projectiveChart_symm_underlying` replaced by the section 7 proof | all compile; standard axioms for `projectiveChart_symm_mem_U_iff`, `analyticAt_evaluate_affineSpaceEquiv_symm`, `openImmersionChart_symm` |

`python3 tools/check.py --no-build` in the worktree: every checked rung ACCEPTED; REJECTED on the sorry scan at `AffineChart.lean:97` and `:188`, the two open bodies. The scan covers the whole tree, so the file cannot reach `main` before both are proved.

**Verdict: pass with changes.** The rung is the literature's statement that algebraic coordinates are holomorphic coordinates, at full strength (membership in the ω-maximal atlas, which is compatibility with every `localChart` in both directions). It is true, its hypotheses are met sorry-free on every ℙⁿ, and the trivial proofs fail. Its truth depends on one convention, the absence of conjugation, and the hypothesis "e lies over Spec ℂ" enforces it. `projectiveChart_symm_underlying` is true for every n and i (proved in scratch) and gives the coordinate lines the consumers need. The changes are a proof to transplant, a corollary for the consumers, an optional open-immersion constructor, a module split, and ledger fields (section 9).

## 1. Is this the statement the literature makes?

Literature (`Serre1956` §§1–2, section numbers unverified; I could not read the text in this session, so this is a paraphrase). A complex algebraic variety X has an associated analytic space X^h on the same set of complex points; for every Zariski open U and regular function f on U, f is holomorphic on U^h; a morphism of varieties is holomorphic; for X smooth of dimension d, X^h is a complex manifold of dimension d. In particular an isomorphism of varieties U ≅ 𝔸^d is a biholomorphism U^h ≅ ℂ^d, so its coordinates form a holomorphic chart of X^h.

Field by field:

| Literature | Lean | Match |
|---|---|---|
| X smooth of dimension d over ℂ | `X : Over (Spec ↧ℂ)`, `[SmoothOfRelativeDimension d X.hom]` | yes; no integrality or separatedness is needed for this local statement, and none is assumed |
| U Zariski open | `U : X.left.Opens`, upstream's `openScheme X U` | yes |
| isomorphism of ℂ-varieties U ≅ 𝔸^d | `e : openScheme X U ≅ Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ)` in `Over (Spec ↧ℂ)` | yes; "over Spec ℂ" is exactly ℂ-linearity, which excludes a twist by a field automorphism (section 6) |
| the coordinates of 𝔸^d | `affineSpaceEquiv (Fin d)`: coordinate m is `(ΓSpecIso ℂ).hom (z.left.appTop (AffineSpace.coord m))` | yes |
| X^h and its complex structure | upstream's `ChartedSpace (Fin d → ℂ) (ComplexPoint X)`, atlas the range of `localChart X d`, built from étale coordinates; `isManifold_omega` | yes; RT4 confirms the instance found is upstream's |
| "holomorphic chart" | `∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X)` | yes; ω over ℂ is analytic, and maximal-atlas membership is analytic transitions with every chart of the atlas in both directions, which `affineChart_compatible_localChart` spells out |

The chart is `affineCoordinates` (upstream homeomorphisms only: `Point.isoMapHomeomorph e`, `affineSpaceHomeomorph`) lifted along upstream's `isOpenEmbedding_map_open`; `affineChart_apply_map`, `_source`, `_target` confirm the source is U(ℂ) and the target is ℂ^d.

Full strength. Maximal-atlas membership is the strongest form of "the chart is holomorphic" Mathlib has. A stronger hypothesis-free variant (every iso of an open with an open of 𝔸^d, or étale maps) is not needed by either consumer.

## 2. Can the hypotheses be satisfied?

Yes, on every ℙⁿ, with every declaration involved sorry-free (RT2: `projectiveChartIso`, `projectiveChart`, `projectiveChartOpen_eq`, `projectiveChartSchemeIso_over`, `affineChart_apply_map`, `_source`, `_target` use the standard axioms only). In RT1:

```lean
example : ∃ (U : (projectiveSpace 2).left.Opens)
    (_ : openScheme (projectiveSpace 2) U ≅ Over.mk (complexAffineSpace (Fin 2) ↘ Spec ↧ℂ)),
    True := ⟨_, projectiveChartIso 2 2, trivial⟩

example (v : Fin 2 → ℂ) : (projectiveChart 2 2).symm v ∈ (projectiveChart 2 2).source :=
  (projectiveChart 2 2).map_target (by rw [projectiveChart, affineChart_target]; trivial)
```

The instance `SmoothOfRelativeDimension 2 (projectiveSpace 2).hom` is `smoothOfRelativeDimension_projectiveSpace` (`p2-witness`). The chart source is nonempty for every d because 𝔸^d(ℂ) is.

## 3. Is the conclusion trivially true?

No. Attempts on `affineChart_mem_maximalAtlas`, all failed:

- `apply StructureGroupoid.subset_maximalAtlas; exact ⟨_, rfl⟩` (would need `affineChart` to be some `localChart X d z` by definition; it is a different chart, built from different coordinates);
- `exact Set.mem_univ _`;
- the prover's `rfl`, `simp`, `aesop`, `trivial`, `exact?`, and `exact IsManifold.chart_mem_maximalAtlas _` (timeout).

Why it cannot be trivial: the ω-maximal atlas over ℂ is a proper subset of the partial homeomorphisms; the chart followed by coordinatewise conjugation is a partial homeomorphism with the same source that lies outside it whenever d ≥ 1 (section 7b). No hypothesis is unused: `e` fixes the chart and d, the instance fixes the charted space. There is no `ℕ∞` coercion and no empty index type (d = 0 gives the one-point model, harmless).

`projectiveChart_symm_underlying` is an equation of points with a computed right side; `rfl`, `simp`, `aesop`, `trivial`, `exact?` fail (prover), and the proof in RT2 needs 45 lines (section 7).

## 4. Interface rung?

No. There is no structure and no axiom (decision 0003). The statement is about upstream's charted space and Mathlib's maximal atlas only.

## 5. Checked rung?

Not yet. `check.py --no-build` output is in the preamble. `#print axioms` on every sorry-free declaration of the file gives the three standard axioms (RT2). When the rung is proved, the ledger must name the declarations listed in change C.

## 6. Conventions

| Convention | Where | Effect on truth |
|---|---|---|
| No conjugation in the coordinates | `affineSpaceEquiv` is `(ΓSpecIso ℂ).hom (z.left.appTop (coord m))`; upstream's `evaluate_top_eq_appTop` is the same formula for `Point.evaluate ⊤`; `localChart`'s coordinates are `Point.evaluate` of étale coordinate sections (`localChart_apply_component_eq_evaluate`). Both sides use ℂ-points over Spec ℂ, so the values are ℂ-linear in the functions | decisive: a conjugated chart is outside the atlas for d ≥ 1. The hypothesis "e is an iso in `Over (Spec ↧ℂ)`" is what makes the coordinates ℂ-linear; a scheme isomorphism over Spec of complex conjugation would give an antiholomorphic chart |
| Coordinate order and scaling | coordinate m is `AffineSpace.coord m`; on ℙⁿ, Yₘ = x_{i.succAbove m} / xᵢ (`toAwayX_X`; Mathlib `SpecIso_inv_appTop_coord` sends `coord m` to `X m`) | none for this rung (linear changes of coordinates preserve the atlas); decisive for consumers, because `htr` of `cycle-class-multiplicative` indexes coordinates |
| Dimension | the model is `Fin d → ℂ` with d the dimension of the affine space in `e`; the instance is `SmoothOfRelativeDimension d X.hom`, a `Prop` class | the two d's are the same variable by elaboration; since U(ℂ) is nonempty, no other relative dimension is possible on U. For `cycle-class-germ`'s `dim X.left` form, use `obtain rfl := SmoothOfRelativeDimension.dim_eq (f := X.hom) d` as in that red team's RT5 |
| ω | Mathlib `contDiffGroupoid ω` over ℂ | analytic, the literature's "holomorphic" |

Consistency with "Holomorphic adapted chart": that row fixes holomorphy against `localChart` with no conjugation; this rung produces exactly such charts, so a consumer can meet `he` of `cycle-class-germ` with `affineChart` followed by a ℂ-linear L (for p2: the chart at i = 2 with L the identity or a coordinate splitting).

Index check for the ℙ² consumer (RT2, all three by `rw [projectiveChart_symm_mem_U_iff]; rfl`):

```lean
example (v : Fin 2 → ℂ) : ((projectiveChart 2 2).symm v).underlying ∈
    (okaIsoSpace 2).hom ''ᵁ ProjectiveSpace.U 2 ℂ 0 ↔ v 0 ≠ 0
example (v : Fin 2 → ℂ) : ((projectiveChart 2 2).symm v).underlying ∈
    (okaIsoSpace 2).hom ''ᵁ ProjectiveSpace.U 2 ℂ 1 ↔ v 1 ≠ 0
example (v : Fin 2 → ℂ) : ((projectiveChart 2 0).symm v).underlying ∈
    (okaIsoSpace 2).hom ''ᵁ ProjectiveSpace.U 2 ℂ 1 ↔ v 0 ≠ 0
```

So at i = 2, L₀ = {x₀ = 0} is {v₀ = 0} and L₁ = {x₁ = 0} is {v₁ = 0}, matching `htr` with a = b = 1 (coordinate a + 0 = 1 for L₁). At i = 0 the coordinates are (x₁/x₀, x₂/x₀), and L₀ lies outside the chart. The docstrings' "(x₀ / x₂, x₁ / x₂)" at i = 2 is correct.

Added to `docs/conventions.md`: row "Algebraic affine chart and the standard chart of ℙⁿ". `p1p1-fibres-transversal` will build its own isomorphism with 𝔸²; the row notes that this choice fixes which fibre is coordinate 0, to be checked in that rung's red team.

## 7. Equality first

The rung is a membership, not an identity between classes. It is a step toward the identity `cycle-class-multiplicative-p2` ([L₀] ∪ [L₁] = [[0 : 0 : 1]], open) through `p2-lines-transversal` (open); both rungs exist in the ledger.

`projectiveChart_symm_underlying` is an exact equality of points, and it is true for every n and i. Proof checked in RT2 (standard axioms):

```lean
theorem projectiveChart_symm_underlying (n : ℕ) (i : Fin (n + 1)) (v : Fin n → ℂ) :
    ((projectiveChart n i).symm v).underlying =
      (okaIsoSpace n).hom.base ((AlgebraicGeometry.ProjectiveSpace.chart i).base
        (AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id ℂ) v)) := by
  set z := (affineSpaceEquiv (Fin n)).symm v
  have h1 : ((projectiveChart n i).symm v).underlying =
      (projectiveChartImmersion n i).base
        ((AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.base z.underlying) := by
    change (Point.map (openInclusion _ _) (Point.map (projectiveChartIso n i).inv z)).underlying = _
    simp only [Point.underlying_map]
    change ((projectiveChartOpen n i).ι).base
      (((projectiveChartImmersion n i).isoOpensRange.hom).base
        ((AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.base z.underlying)) = _
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_hom_ι]
  rw [h1]
  change (okaIsoSpace n).hom.base ((ProjectiveSpace.chart i).base _) = _
  congr 2
  apply PrimeSpectrum.ext
  ext P
  have key : ∀ s : Γ(Spec (.of (MvPolynomial (Fin n) ℂ)), ⊤),
      (AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.base z.underlying ∈
        (Spec (.of (MvPolynomial (Fin n) ℂ))).basicOpen s ↔
        MvPolynomial.eval v (affineGlobalPolynomial
          ((AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.appTop s)) ≠ 0 := by
    intro s
    rw [← evaluate_affineSpaceEquiv_symm_top]
    rw [← Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero (U := ⊤) _ z trivial]
    change _ ↔ z.underlying ∈ (complexAffineSpace (Fin n)).basicOpen _
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  have hP := key ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ))).inv P)
  rw [AlgebraicGeometry.basicOpen_eq_of_affine] at hP
  have hpoly : affineGlobalPolynomial ((AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ))).inv P)) = P := by
    rw [affineGlobalPolynomial]
    change ((Scheme.ΓSpecIso _).inv ≫ (AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.appTop ≫
      (AffineSpace.SpecIso (Fin n) (.of ℂ)).inv.appTop ≫ (Scheme.ΓSpecIso _).hom) P = P
    rw [← Scheme.Hom.comp_appTop_assoc, Iso.inv_hom_id, Scheme.Hom.id_appTop]
    simp
  rw [hpoly] at hP
  change P ∈ _ ↔ P ∈ RingHom.ker _
  rw [RingHom.mem_ker, MvPolynomial.coe_eval₂Hom]
  have : (MvPolynomial.eval₂ (RingHom.id ℂ) v P) = MvPolynomial.eval v P := rfl
  rw [this]
  constructor
  · intro h; by_contra h'; exact (PrimeSpectrum.mem_basicOpen _ _).mp (hP.mpr h') h
  · intro h; by_contra h'; exact hP.mp ((PrimeSpectrum.mem_basicOpen _ _).mpr h') h
```

The route differs from the sketch's step 3 (which goes through `Spec.map` of evaluation): it compares prime ideals by basic opens, using upstream's `evaluate_affineSpaceEquiv_symm_top`, which already identifies the composite ring map with `MvPolynomial.eval v`.

## 7b. Non-vacuity test

The smallest test that fails if maximal-atlas membership were automatic is a conjugated chart outside the atlas. It does not exist on the ladder, in upstream at the pin (no upstream file mentions `maximalAtlas`), or in Mathlib (no lemma that conjugation is not ℂ-differentiable). Statement, elaborated in RT5:

```lean
theorem projectiveChart_conj_not_mem_maximalAtlas :
    (projectiveChart 1 0).trans
        (Homeomorph.piCongrRight fun _ : Fin 1 => Complex.conjCLE.toHomeomorph).toOpenPartialHomeomorph ∉
      IsManifold.maximalAtlas 𝓘(ℂ, Fin 1 → ℂ) ω (ComplexPoint (projectiveSpace 1))
```

Proof sketch: with the rung, the transition from `projectiveChart 1 0` to the conjugated chart is v ↦ conj v on ℂ¹, which would be analytic, and conj has no complex derivative. This is the test that guards the convention of section 6. Proposed as a new test rung (change F); it is not a condition for posting this statement.

## 8. Pin drift

The rung has not been checked against any other commit; the pin is `2ead713` in `lakefile.toml`, `lake-manifest.json` and the package checkout. No drift. Upstream declarations the statement and planned proof depend on, for the drift list: `localChart`, the `ChartedSpace (Fin d → ℂ) (ComplexPoint X)` instance, `isManifold_omega`, `openScheme`, `openInclusion`, `isOpenEmbedding_map_open`, `Point.isoMapHomeomorph`, `Point.map`, `Point.underlying`, `Point.evaluate`, `evaluate_map`, `evaluate_res`, `complexAffineSpace`, `affineSpaceEquiv`, `affineSpaceHomeomorph`, `affineGlobalPolynomial`, `evaluate_top_eq_appTop`, `evaluate_affineSpaceEquiv_symm_top`, `isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen`, `exists_evaluate_basicOpen_eq_div`, `mem_overOpen_basicOpen_iff_evaluate_ne_zero`, `analyticAt_localChart_symm_evaluate`, `localChart_apply_component_eq_evaluate`. All are in upstream's main `Definitions` and `Lemmas` trees; none is in `Other`.

The planned route (sketch, steps 1 and 2) is correct. Step 1 uses `analyticAt_localChart_symm_evaluate` directly. Step 2's new lemma is true and correctly scoped: analyticity at every v₀ whose point lies in the open where the section is defined. Proof checked in RT5 (standard axioms; needs `import Mathlib.Analysis.Analytic.Polynomial`):

```lean
theorem analyticAt_evaluate_affineSpaceEquiv_symm {n : ℕ}
    (V : (complexAffineSpace (Fin n)).Opens) (t : Γ(complexAffineSpace (Fin n), V))
    {v₀ : Fin n → ℂ} (hv₀ : (affineSpaceEquiv (Fin n)).symm v₀ ∈ Point.overOpen V) :
    AnalyticAt ℂ (fun v ↦ Point.evaluate V t ((affineSpaceEquiv (Fin n)).symm v)) v₀ := by
  have hpoly : ∀ p : MvPolynomial (Fin n) ℂ,
      AnalyticAt ℂ (fun v : Fin n → ℂ ↦ MvPolynomial.eval v p) v₀ := fun p =>
    AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id ℂ (Fin n → ℂ)) p v₀ trivial
  obtain ⟨f, hfV, hvf⟩ := (isAffineOpen_top (complexAffineSpace (Fin n))).exists_basicOpen_le
    ⟨((affineSpaceEquiv (Fin n)).symm v₀).underlying, hv₀⟩ trivial
  let t' := (complexAffineSpace (Fin n)).presheaf.map (homOfLE hfV).op t
  obtain ⟨k, a, h⟩ := Point.exists_evaluate_basicOpen_eq_div
    (X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ))
    (isAffineOpen_top (complexAffineSpace (Fin n))) f t'
  have hN : (affineSpaceEquiv (Fin n)).symm ⁻¹'
      Point.overOpen ((complexAffineSpace (Fin n)).basicOpen f) ∈ 𝓝 v₀ :=
    (isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen f).mem_nhds hvf
  have hf0 : MvPolynomial.eval v₀ (affineGlobalPolynomial f) ≠ 0 := by
    rw [← evaluate_affineSpaceEquiv_symm_top]
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)) (U := ⊤) f _ trivial).mp hvf
  have hrat : AnalyticAt ℂ (fun v ↦ MvPolynomial.eval v (affineGlobalPolynomial a) /
      MvPolynomial.eval v (affineGlobalPolynomial f) ^ k) v₀ :=
    (hpoly _).div ((hpoly _).pow k) (pow_ne_zero k hf0)
  apply hrat.congr
  filter_upwards [hN] with v hv
  rw [Point.evaluate_res (X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)) hfV t _ hv]
  erw [h _ hv]
  rw [evaluate_affineSpaceEquiv_symm_top, evaluate_affineSpaceEquiv_symm_top]
```

(RT5 had `hpoly` as a separate lemma; RT6 rechecks the inlined text above.) The lemma is general mathematics about upstream's complex points; record it in `docs/gaps.md` "To upstream" when it lands.

An alternative for step 2: upstream's `analyticAt_localChart_symm_map` (`AnalyticMap.lean`) makes every morphism analytic in `localChart` coordinates on both sides. Applied to `e.inv ≫ openInclusion X U : 𝔸^d ⟶ X`, with Mathlib's `AffineSpace.smoothOfRelativeDimension_of_card_eq` for 𝔸^d, it reduces step 2 to the case X = 𝔸^d, which still needs the lemma above once. Either route works; the sketch's route avoids an instance on 𝔸^d.

## 9. Verdict: pass with changes

Numbered findings:

1. The statement is the literature's, at full strength; each field matches (section 1).
2. The hypotheses are met sorry-free on every ℙⁿ (section 2); trivial proofs fail (section 3).
3. `[SmoothOfRelativeDimension d X.hom]` is the right hypothesis: the charted space is indexed by d, the d of `e` and of the instance are one variable, and U(ℂ) ≠ ∅ rules out any other relative dimension. The class is a `Prop`, so the instance found in a consumer is the same.
4. The iso form is the general one: an open immersion j : 𝔸^d ⟶ X over Spec ℂ gives U = range j and e from `isoOpensRange`; RT3 checks the constructor (change A). Both consumers are served; `p1p1-fibres-transversal` must build an isomorphism of its product open with 𝔸² (or an open immersion), and its coordinate order is that rung's convention.
5. No conjugation enters, and the statement's truth depends on that; "over Spec ℂ" guarantees it (section 6). The chart meets `he` of `cycle-class-germ` after a ℂ-linear L.
6. `projectiveChart_symm_underlying` is true for every n and i and is proved in scratch (section 7). At i = 2 the chart has coordinates (x₀/x₂, x₁/x₂), and L₀, L₁ are the coordinate lines {v₀ = 0}, {v₁ = 0} (section 6). What `p2-lines-transversal` reads is the membership form, change B.
7. The planned route is correct; its new lemma is true, correctly scoped and proved in scratch (section 8).
8. Layering: `HodgeLadder/Normalization/AffineChart.lean` is the only module outside `HodgeLadder/Tests/` that imports a `Tests` module (`Tests.ProjectivePlane`, which brings the port's Oka library). Harmless for truth; change D.
9. The ledger entry has `depends_on: []` while the file imports `open-subscheme-chart-analytic`'s module and `p2-witness`'s module, and names a module path that will not exist (change C).
10. No non-vacuity test of the convention exists (section 7b, change F).
11. No pin drift (section 8).

Recommended changes:

| # | Change | Where |
|---|---|---|
| A | Optional, recommended for both consumers: add the open-immersion constructor below, after `affineChart_target`. `projectiveChartIso` may stay as written | `AffineChart.lean` |
| B | Prove `projectiveChart_symm_underlying` with the proof of section 7, and add the corollary below, which is the form `p2-lines-transversal` reads | `AffineChart.lean` (or the module of change D) |
| C | Ledger `affine-chart-analytic`: `depends_on: ["open-subscheme-chart-analytic", "p2-witness"]`; `module` the module that reaches every declaration (with change D, `HodgeLadder.Tests.ProjectiveChart`, which imports `HodgeLadder.Normalization.AffineChart`; check.py imports only the ledger's module); declarations `affineCoordinates`, `affineChart`, `affineChart_mem_maximalAtlas`, `affineChart_compatible_localChart`, `affineChart_apply_map`, `affineChart_source`, `affineChart_target`, `projectiveChartIso`, `projectiveChart`, `projectiveChart_mem_maximalAtlas`, `projectivePlane_chart_mem_maximalAtlas`, `projectiveChart_symm_underlying`, `projectiveChart_symm_mem_U_iff`, plus change A's names if added; the note cites this file | ledger |
| D | Move the section `Projective` to `HodgeLadder/Tests/ProjectiveChart.lean` (namespace unchanged), so the Normalization module imports no `Tests` module and no port module; the general module then imports `ChartStep` and upstream's `AffineSpace` only | new file, root import |
| E | When the rung lands, add `analyticAt_evaluate_affineSpaceEquiv_symm` (section 8) to `docs/gaps.md` "To upstream" | `docs/gaps.md` |
| F | New test rung `affine-chart-conj-test`, depending on `affine-chart-analytic`: `projectiveChart_conj_not_mem_maximalAtlas` (section 7b) | ledger, roadmap |

Change A, checked in RT3:

```lean
/-- An open immersion `j : 𝔸^d ⟶ X` over `Spec ℂ` identifies its range with `𝔸^d`. -/
def openImmersionAffineIso (X : Over (Spec ↧ℂ)) {d : ℕ}
    (j : Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) ⟶ X) [IsOpenImmersion j.left] :
    openScheme X j.left.opensRange ≅ Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) :=
  Over.isoMk j.left.isoOpensRange.symm (by
    change j.left.isoOpensRange.inv ≫ (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) =
      j.left.opensRange.ι ≫ X.hom
    have hw : j.left ≫ X.hom = complexAffineSpace (Fin d) ↘ Spec ↧ℂ := Over.w j
    calc _ = j.left.isoOpensRange.inv ≫ j.left ≫ X.hom := by rw [hw]
      _ = _ := by rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp])

/-- The affine chart of an open immersion `j : 𝔸^d ⟶ X` over `Spec ℂ`. -/
def openImmersionChart (X : Over (Spec ↧ℂ)) {d : ℕ}
    (j : Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) ⟶ X) [IsOpenImmersion j.left] :
    OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ) :=
  affineChart X j.left.opensRange (openImmersionAffineIso X j)

/-- The inverse of the chart of `j` is `j` on complex points, after the affine coordinates. -/
theorem openImmersionChart_symm (X : Over (Spec ↧ℂ)) {d : ℕ}
    (j : Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) ⟶ X) [IsOpenImmersion j.left]
    (v : Fin d → ℂ) :
    (openImmersionChart X j).symm v = Point.map j ((affineSpaceEquiv (Fin d)).symm v) := by
  apply Over.OverMorphism.ext
  change ((affineSpaceEquiv (Fin d)).symm v).left ≫ j.left.isoOpensRange.hom ≫
    j.left.opensRange.ι = ((affineSpaceEquiv (Fin d)).symm v).left ≫ j.left
  rw [Scheme.Hom.isoOpensRange_hom_ι]
```

Change B corollary, checked in RT2 (after `projectiveChart_symm_underlying`):

```lean
/-- The inverse chart at `v` lies over the standard open `xⱼ ≠ 0` exactly when coordinate `j` of
`Fin.insertNth i 1 v` is nonzero. On ℙ² at `i = 2`: in `U j` for `j = 0, 1` iff `v j ≠ 0`. -/
theorem projectiveChart_symm_mem_U_iff (n : ℕ) (i j : Fin (n + 1)) (v : Fin n → ℂ) :
    ((projectiveChart n i).symm v).underlying ∈
        (okaIsoSpace n).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U n ℂ j ↔
      Fin.insertNth (α := fun _ => ℂ) i 1 v j ≠ 0 := by
  rw [projectiveChart_symm_underlying, Scheme.Hom.apply_mem_image_iff]
  have h := AlgebraicGeometry.ProjectiveSpace.chart_base_evalPoint_mem_U_iff (R := ℂ)
    (RingHom.id ℂ) i j (Fin.insertNth (α := fun _ => ℂ) i 1 v) (by simp)
  rwa [AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec_insertNth] at h
```

Not changed: the statement of the rung, the hypothesis form, and the definitions. Nothing here weakens a statement.

## Sources

`Serre1956` (§§1–2, numbering unverified; paraphrased, text not read in this session). Upstream and Mathlib declarations by name, read at `2ead713` and `v4.35.0-rc4`.
