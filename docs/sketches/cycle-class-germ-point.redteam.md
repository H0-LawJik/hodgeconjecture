# Red team: `cycle-class-germ-point` (statement)

Date: 2026-11-26. Worktree `cycle-class-germ-point`, base `62a6c1d`, uncommitted `HodgeLadder/Tests/CycleClassGermPoint.lean` and the section "cycle-class-germ-point: statement" of `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Statement pass, before the proof (phase 1).

Targets, namespace `HodgeLadder.Tests.CycleClassGermPoint`: `closedPointChart` and its helpers, the proved `transport_supportedClass_eq_pointRelativeCoclass`, the rung `pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass` (sorry), and the two proved consequences.

Read at the pin: `Other/AlgebraicGeometry/Cycle/Component/PointClassNormalization.lean`, `Other/AlgebraicGeometry/Cycle/Component/PointPurity.lean`, `Other/AlgebraicGeometry/Cycle/SmoothPair/PointCoclassSection.lean`, `Other/AlgebraicGeometry/Cycle/SmoothPair/PointPurity.lean`, `Other/AlgebraicTopology/LocalHomology/ChartPointClassNormalization.lean`, `Other/AlgebraicTopology/LocalHomology/ChartFundamentalClass.lean`, `Definitions/AlgebraicGeometry/Cycle/SmoothPair/CoclassSection.lean`, `Definitions/` and `Lemmas/AlgebraicTopology/LocalHomology/NormalProjectionCoclass.lean`, `Lemmas/AlgebraicGeometry/Cycle/Local/LocalHomology.lean`; in this repository `HodgeLadder/Normalization/{Germ,ChartStep,Singular}.lean` and `docs/sketches/cycle-class-germ.redteam.md` (change H).

Scratch files (inside the worktree while running, deleted afterwards):

| File | What | Result |
|---|---|---|
| RT-A | `chartAt (Fin (dim X.left) → ℂ) y₀ = localChart X (dim X.left) y₀ := rfl` | compiles |
| RT-B | the rung from `cycle-class-germ` with the `Germ` import | compiles in 8 lines: `transport_supportedClass_eq_chartNormalProjectionCoclass` at `closedPointChart`, then `rw [← transport_supportedClass_eq_pointRelativeCoclass]` |
| RT-C | right side nonzero on every open `W ∋ y₀` in the chart source (with `Germ`) | compiles |
| RT-D | the sign-flipped rung (right side negated) is false, given `cycle-class-germ` | compiles: on `W ⊓ W'` the chart coclass equals its negative, so it is 0 over ℚ, against RT-C |
| RT-G | the module with `HodgeLadder.Normalization.Singular` replaced by `Other.AlgebraicGeometry.Cycle.Component.PointClassNormalization`, plus the import and dependency guard of change 2 | compiles; guard silent. Positive controls: a probe theorem using `exists_open_chartNormalProjectionCoclass_eq` fails the build, and so does adding `public import HodgeLadder.Normalization.Singular` |
| RT-N | Germ-free non-vacuity lemma of change 4 | compiles in 28 s; a direct proof at the concrete chart hit a kernel deterministic timeout, the generic form below does not |
| RT-W | `∃ X, IsIntegral ∧ Smooth ∧ IsProjective ∧ Nonempty (ComplexPoint X)` at `HodgeLadder.Tests.point` | compiles |
| RT-P2 | consequence `transport_supportedClass_eq_chartNormalProjectionCoclass_closedPoint` instantiated at `projectiveSpace 2` and `(projectiveChart 2 0).symm 0`; `coheight_underlying` there | elaborates (d = 2) |

`python3 tools/check.py --no-build` in the worktree: every checked rung ACCEPTED; REJECTED only on the sorry scan at `HodgeLadder/Tests/CycleClassGermPoint.lean:185`, the rung's body. Expected in phase 1; the file cannot reach `main` until the body is proved.

**Verdict: pass with changes.** The statement is the literature's local description of the class of a point, exact, at the chart of `adaptedChart_closedPoint`. It is true at the pin (RT-B), it pins the sign (RT-D), and its right side is nonzero (RT-C, RT-N). The point route avoids every step of the `cycle-class-germ` proof between the coclass section and the chart coclass, and shares the normalization of ℂ^d with it; the changes make the boundary explicit, widen it to exclude `normalization-singular`, and enforce it in the build.

## 1. Is this the statement the literature makes?

Literature. For a point y of a complex manifold X of dimension d, the class of y in H^{2d}(X, X ∖ {y}; ℚ) is the generator that pairs to 1 with the local orientation class of the complex orientation [`Fulton1998` ch. 19, `Bredon1997`, `MilnorStasheff1974`; chapter numbers unverified]. Restricted to a holomorphic chart centred at y with all coordinates normal, it is the pullback along the chart of the generator of H^{2d}(ℂ^d, ℂ^d ∖ 0) dual to the orientation (v₁, iv₁, …, v_d, iv_d). This is the codimension-d case of the statement quoted in section 1 of `docs/sketches/cycle-class-germ.redteam.md`.

Field by field:

| Literature | Lean | Match |
|---|---|---|
| class of y in H^{2d}(X, X ∖ {y}) | `analyticPointLocalCoclass X d y` = `normalizedRelativeCoclass` of `localClassOfChart d (localChart X d y) y` | yes; `localClassOfChart` is the image of `standardComplexLocalClass ℚ d` under the radial compression into the chart target followed by the inverse chart (`chartModelEmbeddingPair`) |
| class of Z = {y} in H^{2d}(X, X ∖ Z) | `analyticComponentPointRelativeCoclass X x d z`, the pullback along `neighborhoodSupportToPointPairMap ⊤ (cycleComponentSupport X x) (cycleComponentMap X x z)` | yes; the support is the singleton (`cycleComponentSupport_eq_singleton_of_coheight_eq_dimension`), so the pair map is the identity of pairs up to spelling |
| restriction to a neighbourhood W | `relativeCohomologyMap` along `neighborhoodSupportInclusionPairMap (W ⊆ ⊤)` | yes, same spelling as `cycle-class-germ` |
| holomorphic chart centred at y, all coordinates normal | `closedPointChart X y₀` = `(chartAt y₀ ≫ (· + −chartAt y₀ y₀)) ≫ (uniqueProd ℂ (Fin d → ℂ) (Fin 0 → ℂ)).symm`, tangential factor ℂ⁰ | yes; `chartAt = localChart` by `rfl` (RT-A), translation and `uniqueProd` are ℂ-affine and preserve orientation |
| pullback of the dual generator | `chartNormalProjectionCoclass (Fin 0 → ℂ) d e Z hS W hW` = pullback along `(e ·).2` of `normalizedRelativeCoclass (standardComplexLocalClass ℚ d)` | yes |
| degree | `2 * dim X.left` on both sides, no cast `d − (d − p)` | yes |
| sign, scalar | equality, coefficient 1 | yes, and the negated form is false (RT-D) |

Same chart as `adaptedChart_closedPoint`. Read side by side: `adaptedChart_closedPoint` (`Germ.lean:161`) sets `c := chartAt y₀`, `T := (Homeomorph.addRight (−(c y₀))).toOpenPartialHomeomorph`, `L := ContinuousLinearEquiv.uniqueProd ℂ (Fin (dim X.left) → ℂ) (Fin 0 → ℂ)`, `e := (c.trans T).trans L.symm.toHomeomorph.toOpenPartialHomeomorph`. `closedPointChart` and `closedPointChartLinear` are the same terms with the `let`s inlined; the proofs of the four hypotheses are copied line for line. Same e, same L. The identity is textual: the existential in `adaptedChart_closedPoint` hides the witness, so no Lean statement can compare them (change 6).

The `∀ z` form is stronger than needed: the component of a closed point has one complex point, and the consequence picks z from `range_cycleComponentMap`.

## 2. Can the hypotheses be satisfied?

The rung has no hypotheses beyond the instances and two points. Instances: `HodgeLadder.Tests.point` (Spec ℂ, d = 0) with a complex point `𝟙 _` (RT-W), and `projectiveSpace 2` (d = 2) with the instances of `HodgeLadder/Tests/ProjectivePlane.lean` and the point `(projectiveChart 2 0).symm 0` (RT-P2). `SmoothOfRelativeDimension (dim X.left) X.hom` is found by upstream's `SmoothOfRelativeDimension.of_isIntegral`. A point z of the component exists for every y₀ by `range_cycleComponentMap` (used in the last consequence).

The d = 0 instance is degenerate (H^0, W ∖ Z = ∅, row "Degree-zero orientation and the unit"). The d = 2 instance is even: a conjugated chart would change the sign by (−1)^d = +1 there, so the concrete instance would not see that error; the rung is stated for every X, so odd d is covered by the statement, not by an example.

## 3. Trivially true?

No definition unfolds to `True`, no coercion, no empty index: W must contain y₀ and lie in the chart source. Both sides live in H^{2d}(W, W ∖ {y₀}; ℚ) ≅ ℚ. The right side is nonzero on every admissible W (RT-C, RT-N), so the existential cannot be met by two zeros, and the negated statement is false (RT-D). The prover's trivial attempts (`rfl`, `simp`, `trivial`, `decide`, `aesop`, `Subsingleton.elim`, `simp` with both definitions unfolded at W = source) all failed; I add the two failures I met while writing RT-C and RT-D: `rw` with `chartNormalProjectionCoclass_restrict` and `LinearMap.comp_apply` does not fire through the coercion `↑(⟨e.source, _⟩ : Opens _)` or `↑(⊤ : Opens _)`, and `erw` or an explicit helper is needed (phase-2 trap, section 9).

## 4. Interface rung

Not an interface rung; no structure, no axioms.

## 5. Checker

Section above: only the sorry at line 185. The module is not yet imported from `HodgeLadder.lean`; add the import with the proof. Names to put in the ledger: `closedPointChartLinear`, `closedPointChart`, `closedPointChart_source`, `closedPointChart_apply_snd`, `mem_closedPointChart_source`, `coheight_underlying`, `closedPointChart_mem_maximalAtlas`, `closedPointChart_support`, `mem_smoothSupportAmbientOpen_closedPoint`, `transport_supportedClass_eq_pointRelativeCoclass`, `pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass`, `transport_restrict_eq_pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass`, `transport_supportedClass_eq_chartNormalProjectionCoclass_closedPoint`, and the non-vacuity lemmas of change 4, all under `HodgeLadder.Tests.CycleClassGermPoint`. At phase 2 confirm the axioms line is the standard three for each.

## 6. Conventions, and what the cross-check can detect

| Convention | Row | Truth depends on it | Check |
|---|---|---|---|
| Complex orientation of ℂ^d (consecutive Re, Im) | "Complex orientation of ℂ^p" | yes, for the identity with a fixed sign; both sides use it | shared by both sides, so not tested here |
| Normalization: pair to 1 | "Fundamental-class normalization", "Universal-coefficient evaluation" | yes | shared, not tested here |
| Point local coclass via `localClassOfChart` of `localChart` | new row "Point local coclass" (added) | yes | read from source |
| Holomorphic chart (no conjugation) | "Holomorphic adapted chart" | yes, (−1)^d | `closedPointChart` is `chartAt` up to translation; atlas membership proved |
| Normalization iso against the transport | "Normalization iso against the singular transport" | yes | the point route reaches the left side through upstream's `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section`, not through `normalization_singular` |
| Ordinary-class cone sign | "Mapping-cone connecting map" | no: the rung is relative, before the supported-to-ordinary map | upstream's header in `PointClassNormalization.lean` says the legacy comparison "has its own cone sign"; do not extend this test to `analyticComponentPointPositiveKernelClass` without that row |

Shared inputs of the two code paths (findings 1 and 2):

| Input | `cycle-class-germ` | point route |
|---|---|---|
| definition of [Z]: `cycleComponentSupportedInjectiveClass`, via `cycleComponentSmoothSupportCoclassSection`, which is the gluing (`smoothClosedSupportCoclassSection`) of `chartNormalProjectionCoclass` germs of upstream's flattening charts | used | used (inside `cycleComponentSupportedInjectiveClass_unique`) |
| `standardComplexLocalClass`, `normalizedRelativeCoclass`, `chartNormalProjectionCoclass` (right side) | used | used |
| `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section` (upstream) | inside `normalization_singular` | directly, inside `analyticComponentPointSupportedInjectiveCoclass_section_normalization` |
| `normalization_singular` (ladder) | used | not used (and not visible after change 1) |
| stalk as chart germ `smoothClosedSupportCoclassStalk_eq_chartGerm`, `chartNormalProjectionCoclass_pairImage`, lift to the open subscheme U | used | not used |
| chart step: `analyticAt_transition_of_factor`, `exists_open_chartNormalProjectionCoclass_eq`, `exists_open_complexDifferentiable_localClass_invariance` (holomorphic transitions) | used | not used (forbidden by change 2) |
| tangential matching `ContinuousLinearEquiv.ofFinrankEq`, degree cast by `subst` | used | absent; at p = d the tangential factor is ℂ⁰ |
| singleton comparison `smoothClosedSupportCoclassSection_eq_point_of_singleton`, `smoothClosedPointNormalCoclass_eq_analyticPointLocalCoclass` (complex-linear invariance `centeredComplexLinear_preserves_standardComplexLocalClass`, translation, radial) | not used | used |
| `localClassOfChart`, `chartTargetPointPairMap_localClass`, `centeredComplexUnivBall_preserves_standardComplexLocalClass` | not used | used in phase 2 |

So the point route goes flattening-chart coclass, then (upstream) the old point coclass of `localChart`, then (phase 2) the chart coclass of e. The germ route goes flattening-chart coclass, then (chart step) the chart coclass of e. A sign or scalar error in the germ route's plumbing, in its chart step, or in `normalization_singular` would make the two disagree; an error in the orientation of ℂ^d (for example (Re, …, Re, Im, …, Im), sign (−1)^{d(d−1)/2}), in `normalizedRelativeCoclass`, or in the gluing definition of the coclass section would cancel. The rows above, not this test, guard those. Inside Lean both routes are theorems at one pin and cannot disagree; the test's value is a second derivation that breaks if either route's normalization moves at a pin bump, and it covers p = d only.

## 7. Equality first

An identity, proved exactly once the body is in (RT-B shows it holds at the pin with coefficient 1). It is a test of `cycle-class-germ`, itself an identity.

## 7b. Non-vacuity

Smallest test that fails on a trivially true statement: the right side is nonzero on every admissible W. With `Germ` it follows from `chartNormalProjectionCoclass_germ_ne_zero` (RT-C); without `Germ` from upstream's `chartNormalProjectionCoclass_apply_normalClass`, `flattenedSupportNeighborhood_subset_source`, `chartNormalProjectionCoclass_restrict` on `e.restrOpen W` (RT-N, change 4). Neither is in the module yet. The sign-flip refutation RT-D needs `cycle-class-germ` and so stays outside this module; after phase 2 the same argument with the rung in place of RT-B gives it Germ-free (optional).

## 8. Pin drift

The rung and `cycle-class-germ` were elaborated at the same pin `2ead713`; no drift. Upstream `Other` inputs to add to the drift list (library `Other`, outside upstream's statement guard): `cycleComponentSupportedInjectiveClass_point_normalization`, `analyticComponentPointSupportedInjectiveCoclass_relative`, `analyticComponentPointRelativeCoclass`, `analyticComponentPointSupportedInjectiveCoclass`, `analyticPointLocalCoclass`, `analyticPointLocalHomologyClass`, `analyticPointLocalCoclass_apply_localClass`, `neighborhoodSupportToPointPairMap`, `neighborhoodSupportInclusionPairMap_toPoint`, `cycleComponentSupport_eq_singleton_of_coheight_eq_dimension`, `range_cycleComponentMap`, `chartTargetPointPairMap_localClass`, `localClassOfChart`. On a bump, diff `localClassOfChart` and `chartModelEmbeddingPair` first: they fix the point route's orientation.

## 9. Phase-2 route

Sound, and independent of `Germ` as planned. Checked step by step against the sources:

1. `flattenedSupportNeighborhood (Fin 0 → ℂ) d e y₀ hy` with `h0` from `closedPointChart_apply_snd`: available upstream.
2. `chartNormalProjectionCoclass_unique` (upstream, `Lemmas/AlgebraicTopology/LocalHomology/NormalProjectionCoclass.lean:142`): exact statement needed.
3. `neighborhoodSupportInclusionPairMap_toPoint` is a `@[simp]` lemma upstream; it needs the same S on both maps, and the rung spells S as `↑(cycleComponentAnalyticClosedSupport X x)` while `analyticComponentPointRelativeCoclass` uses `cycleComponentSupport X x`. They are defeq (the statement elaborates); expect a `change`. For `cycleComponentMap X x z = y₀`: y₀ cannot be substituted (z's type mentions `y₀.underlying`); generalize w := `cycleComponentMap X x z` with its membership proof, then `subst w`, as the sketch says.
4. The normal fibre of the flattened neighbourhood of e is v ↦ e.symm (0, B_r v) = (chartAt y₀).symm (chartAt y₀ y₀ + B_r v) with B_r = `univBall 0 r` (`univBall_zero_tangent_normal`, the normal part only since E = ℂ⁰). Composed with the inclusion into the chart target this is the centred radial map followed by translation by `chartAt y₀ y₀`, which is the hypothesis of `chartTargetPointPairMap_localClass` after `centeredComplexUnivBall_preserves_standardComplexLocalClass`; the pattern is upstream's `smoothClosedPointNormalTargetPairMap_comp_inclusion` without its linear factor.
5. `analyticPointLocalCoclass_apply_localClass` gives 1.

Traps met in scratch: `rw` with lemmas stated for `e.source` or `(⊤ : Set _)` misses goals spelled with `↑(⟨e.source, _⟩ : Opens _)` or `↑(⊤ : Opens _)`; use `erw` or a helper stated in the goal's spelling. Kernel time: a direct proof at the concrete `closedPointChart` timed out in the kernel; prove step 4 for an abstract chart `c` and translation, then instantiate.

## 10. Verdict and changes

**pass with changes.**

1. Narrow the imports so that neither `cycle-class-germ` nor `normalization-singular` is in the module's environment. Replace `public import HodgeLadder.Normalization.Singular` by `public import Other.AlgebraicGeometry.Cycle.Component.PointClassNormalization` (the only import of `Singular`; RT-G compiles with it). Keep `HodgeLadder.Normalization.ChartStep`: only `translate_mem` and `trans_mem_maximalAtlas` are used, for `closedPointChart_mem_maximalAtlas`. `Germ` imports both `Singular` and `ChartStep`, so neither can import `Germ` back (an import cycle); the remaining imports are upstream and Mathlib.

2. Enforce the boundary in the build, in the module, after the last declaration (RT-G, with a positive control). Add `meta import Lean` to the imports. Imported theorem bodies are not visible under the module system, so the dependency part checks this file's proofs only; the import part covers everything else.

```lean
-- Independence guard (red team on `cycle-class-germ-point`): this module does not see
-- `cycle-class-germ` or `normalization-singular`, and the rung's proof does not use the chart
-- step of `cycle-class-germ`. A docstring cannot precede `run_cmd`.
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for m in [`HodgeLadder.Normalization.Germ, `HodgeLadder.Normalization.Singular] do
    if (env.getModuleIdx? m).isSome then
      throwError "cycle-class-germ-point must not import {m}"
  let forbidden : List Name :=
    [`AlgebraicTopology.Singular.exists_open_chartNormalProjectionCoclass_eq,
     `AlgebraicTopology.Singular.exists_open_complexDifferentiable_localClass_invariance,
     `AlgebraicGeometry.ComplexPoint.smoothClosedSupportCoclassStalk_eq_chartGerm,
     `HodgeLadder.Normalization.analyticAt_transition_of_factor,
     `HodgeLadder.Normalization.analyticAt_transition_of_mem_maximalAtlas]
  for f in forbidden do
    unless env.contains f do throwError "independence guard is stale: {f}"
  let rec go (fuel : Nat) (todo : List Name) (seen : NameSet) : NameSet :=
    match fuel, todo with
    | 0, _ | _, [] => seen
    | fuel + 1, n :: rest =>
      if seen.contains n then go fuel rest seen else
      match env.find? n with
      | some ci => go fuel ((ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]).toList ++ rest)
          (seen.insert n)
      | none => go fuel rest (seen.insert n)
  let s := go 1000000
    [`HodgeLadder.Tests.CycleClassGermPoint.pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass] {}
  for f in forbidden do
    if s.contains f then throwError "cycle-class-germ-point uses {f}"
```

   No checker rule: the guard runs on every build, and a rule in `tools/check.py` would need a decision record for one rung.

3. Docstrings. In the module docstring, replace "The module does not import `HodgeLadder.Normalization.Germ`, so no proof here can use `cycle-class-germ`" by: "The module imports neither `HodgeLadder.Normalization.Germ` nor `HodgeLadder.Normalization.Singular`, and a guard at the end of the file fails the build if it does or if the rung's proof uses the chart step of `cycle-class-germ`. The two code paths share the definition of the coclass section (a gluing of flattening-chart `chartNormalProjectionCoclass` germs), `standardComplexLocalClass` and `normalizedRelativeCoclass`; they differ in everything between, so the test detects an error in either route's plumbing at p = dim X, and an error in the orientation of ℂ^d would cancel." In the rung's docstring, add the row "Point local coclass" to the cited rows.

4. Non-vacuity in the module, Germ-free (RT-N):

```lean
set_option backward.isDefEq.respectTransparency false in
/-- A chart coclass is nonzero on every open `W` of the source that meets the support. -/
theorem chartNormalProjectionCoclass_ne_zero_of_mem {M : Type} [TopologicalSpace M]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (W : Opens M) (hW : (W : Set M) ⊆ e.source)
    (y : M) (hyW : y ∈ W) (hy : y ∈ e.source) (h0 : (e y).2 = 0) :
    chartNormalProjectionCoclass E c e S hS W hW ≠ 0 := by
  intro hz
  let er := e.restrOpen W W.isOpen
  have hyr : y ∈ er.source := ⟨hy, hyW⟩
  have hSr : ∀ z ∈ er.source, z ∈ S ↔ (er z).2 = 0 := fun z hz => hS z hz.1
  have hF := flattenedSupportNeighborhood_subset_source E c er y hyr
  have hFW : (flattenedSupportNeighborhood E c er y hyr : Set M) ⊆ (W : Set M) :=
    fun _ hz => (hF hz).2
  have h1 := chartNormalProjectionCoclass_apply_normalClass E c er S hSr y hyr h0
  have h2 : chartNormalProjectionCoclass E c er S hSr
      (flattenedSupportNeighborhood E c er y hyr) hF =
      relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap hFW S)
        (chartNormalProjectionCoclass E c e S hS W hW) := by
    rw [chartNormalProjectionCoclass_restrict]
    rfl
  rw [h2, hz, map_zero, map_zero] at h1
  exact zero_ne_one ((LinearMap.zero_apply _).symm.trans h1)

/-- Non-vacuity: the right side of the rung is nonzero on every open `W ∋ y₀` inside the chart
source. -/
theorem chartNormalProjectionCoclass_closedPointChart_ne_zero (y₀ : ComplexPoint X)
    (W : Opens (ComplexPoint X)) (hW : (W : Set (ComplexPoint X)) ⊆ (closedPointChart X y₀).source)
    (hyW : y₀ ∈ W) :
    chartNormalProjectionCoclass (Fin 0 → ℂ) (dim X.left) (closedPointChart X y₀)
      (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X))
      (closedPointChart_support X y₀) W hW ≠ 0 :=
  chartNormalProjectionCoclass_ne_zero_of_mem _ _ _ _ _ W hW y₀ hyW
    (mem_closedPointChart_source X y₀) (by rw [closedPointChart_apply_snd, add_neg_cancel])
```

   The generic lemma is the W-form of `Germ`'s `chartNormalProjectionCoclass_germ_ne_zero` and belongs upstream: record it in `docs/gaps.md` "To upstream".

5. Ledger at phase 2: `module` `HodgeLadder.Tests.CycleClassGermPoint`, the declarations of section 5, and a note that states the shared and distinct inputs of section 6 in one sentence each, that the module imports neither `Germ` nor `Singular` (guarded), and that the test covers p = dim X. If `depends_on` keeps `cycle-class-germ`, the note must say that the proof does not use it; the proof's own ladder dependency is `open-subscheme-chart-analytic` (`ChartStep`, atlas lemmas only). Add the `Other` names of section 8 to the drift list.

6. Optional, later: to make "same e" a theorem, move `closedPointChart` and its four lemmas to a small module imported by both `Germ.lean` and this test, and restate `adaptedChart_closedPoint` with it. That edits a checked module and is outside this rung.

No stronger statement proposed: every holomorphic adapted chart at a closed point would need the chart step and lose the independence; the rung is the right size for a cross-check.
