# Red team: `p2-lines-transversal` (statement)

Date: 2026-11-26. Worktree `p2-lines-transversal`, base `62a6c1d`, uncommitted `HodgeLadder/Tests/ProjectivePlaneLines.lean` and the section "p2-lines-transversal: statement" of `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713` (package checkout `rev-parse HEAD` and `lake-manifest.json` agree), Lean and Mathlib `v4.35.0-rc4`.

Targets: `planeLineRestrict`, `planeLinePrime`, `planeEvalPoint`, `planeChartPoint`, `planeLine`, `planeOriginPoint`, `planeOrigin`; `coheight_planeLine`, `coheight_planeOrigin`, `planeOrigin_support_eq_inter`, `planeOrigin_support_eq_singleton`, `mem_planeLine_support_iff`, `planeLines_transversal`, `planeLine_zero_ne_one`, `planeOrigin_support_subset_smoothSupportAmbientOpen`; the open lemma `cycleComponent_planeLine_mem_smoothLocus`.

Read at the pin: upstream `Definitions/AlgebraicGeometry/Cycle/Support.lean` (`cycleComponent`, `cycleComponentι`, `cycleComponentSupport`), `Cycle/Component/SmoothClosedLift.lean` (`cycleComponentAnalyticClosedSupport`), `Cycle/Component/SingularClosedFiltration.lean`, `Cycle/Component/SmoothSupportPurity.lean` (`cycleComponentSmoothSupportAmbientOpen`), `Stratification/Basic.lean` (`singularLocusClosed`, `reducedSmoothClosedFiltration`), `Cycle/FundamentalClass.lean` (`cycleComponentSheafClass`), `Lemmas/AlgebraicGeometry/Smooth/DimensionFormula.lean` (`coheight_le_complex`); Mathlib `AlgebraicGeometry/Scheme.lean` (`le_iff_specializes`), `IdealSheaf/{Basic,Subscheme}.lean`, `Morphisms/Smooth.lean`; the port's `Oka/AlgebraicGeometry/ProjectiveSpace/Basic.lean` (`chart`, `U`, `chart_preimage_U`, `iSup_U`) and `Oka/RingTheory/MvPolynomial/HomogeneousLocalization.lean` (`dehomogenize`); this repository's `Tests/ProjectiveChart.lean`, `Tests/ProjectivePlane.lean`.

Scratch files (directory `scratch_rt/` inside the worktree, deleted afterwards). The worktree's `.olean` of `HodgeLadder.Tests.ProjectivePlaneLines` is newer than the source, so each file imports the module.

| File | What | Result |
|---|---|---|
| RT1 | the general statement of `cycle-class-multiplicative` copied verbatim from the sketch with a `sorry` body; the ℙ² instance by `exact` against a target written with degree `4`; the same with `d := 2` and `a = b = 1` given explicitly; the chart with L₁ as coordinate 0 (must fail); distinctness of the three points; L₀(ℂ) is more than a point | all compile; one warning, the `sorry` of the copied general statement |
| RT2 | trivial proofs: `Smooth` of the line by `infer_instance`, `smoothLocus_eq_top`, `simp` on the open lemma, `simp` on the point's coheight, `htr` with `chartAt` and `aesop` | all fail (section 3); `(⊤ : projectivePlane.left) = genericPoint _` by `rfl` succeeds |
| RT3 | `#print axioms` of the 17 targets | 15 print `[propext, Classical.choice, Quot.sound]`; `cycleComponent_planeLine_mem_smoothLocus` and `planeOrigin_support_subset_smoothSupportAmbientOpen` add `sorryAx` |
| RT4 | the hypothesis `hz` of the open lemma is satisfiable, k = 0, 1 | proved (Mathlib `range_subschemeι`, `coe_support_vanishingIdeal`) |
| RT5 | scheme-level intersection `closure {L₀} ∩ closure {L₁} = closure {[0 : 0 : 1]}` | proved, about 45 lines, standard axioms (change 2) |

Wall time of each `lake env lean` run: 20 s or less, default heartbeats.

`python3 tools/check.py --no-build` in the worktree: every checked rung ACCEPTED; one REJECTED, the sorry scan at `ProjectivePlaneLines.lean:410`, the open lemma. The scan covers the tree, so the file stays off `main` until that lemma is proved.

**Verdict: pass with changes.** The three points are the generic points of {x₀ = 0}, {x₁ = 0} and the closed point [0 : 0 : 1] of the ladder's ℙ², the invariants are the ones upstream indexes cycle classes by, every proved item is the exact hypothesis of `cycle-class-multiplicative` that it claims to be, and the instance `cycle-class-multiplicative-p2` closes by `exact` (RT1). The open lemma is true and its planned route uses Mathlib declarations that exist at the pin. Changes: ledger and module bookkeeping when the lemma lands (required), a scheme-level intersection lemma as a cross-check of "T is the only component" (recommended, exact Lean below, checked), one sentence of the sketch (recommended), and a conventions row (done).

## 1. Is this the statement the literature makes?

The literature statement this rung feeds: on a nonsingular X, if Z and W meet properly and transversally along a single component T, then [Z]·[W] = [T] and the cycle map is a ring homomorphism [`Fulton1998` §8.2 and Cor. 19.2; numbering unverified]. On ℙ² the coordinate lines {x₀ = 0}, {x₁ = 0} meet transversally in the one point [0 : 0 : 1]. The test rung must supply, in upstream's API, the generic points of these three subvarieties and the hypotheses `hx`, `hw`, `ht`, `hT`, `htr`, `hxreg`, `hwreg` of `cycleComponentSheafClass_cup_of_transversal`.

| Literature object | Lean | Comparison |
|---|---|---|
| ℙ² over ℂ | `projectivePlane = Over.mk (ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ))` | rung `p2-witness`, passed; coordinate indices agree with Oka's ℙₒ(2; ℂ) through `okaIsoSpace` (conventions row "Projective space") |
| the affine chart x₂ ≠ 0 with coordinates Yₘ = xₘ / x₂ | `projectiveChartImmersion 2 2 = ProjectiveSpace.chart 2 ≫ (okaIsoSpace 2).hom` | the port's chart i has Yⱼ = x_{i.succAbove j} / xᵢ, and `Fin.succAbove 2 m = m` for m = 0, 1 (`dehomogenize_two_X_castSucc`); `chart_preimage_U` says the chart meets D₊(xⱼ) in the basic open of `dehomogenize 2 (X j)`. So "Y_k vanishes" is tied to "x_k vanishes" by a proved lemma about the port's `U` |
| generic point of L_k = {x_k = 0} | `planeLine k = planeChartPoint (ker (Y_k ↦ 0))` | the prime (Y_k) of ℂ[Y₀, Y₁] (`X_mem_planeLinePrime_iff`: Y_m ∈ it iff m = k). Its image lies off D₊(x_k) (`planeLine_not_mem_U`), and on the chart x₂ ≠ 0 its complex points are {v_k = 0} (`mem_planeLine_support_iff`). Mathematically its closure is an irreducible closed curve inside the irreducible curve {x_k = 0}, hence equal to it. Global equality `L_k(ℂ) = {z ∉ D₊(x_k)}` is not stated; no consumer needs it (the second chart would be needed for the points of x₂ = 0) |
| the closed point [0 : 0 : 1] | `planeOrigin = ((projectiveChart 2 2).symm 0).underlying = planeChartPoint (ker eval₀)` | `planeOrigin_eq`; the inverse chart at v has homogeneous coordinates `Fin.insertNth 2 1 v` (conventions row "Algebraic affine chart"), which is (0, 0, 1) at v = 0 |
| specialization L_k ⤳ pt | `planeOrigin_lt_planeLine` | via `planeChartPoint_specializes_iff` (open embedding) and `PrimeSpectrum.le_iff_specializes`: (Y_k) ⊆ (Y₀, Y₁), strict |

**Coheight is the right invariant.** Upstream's `cycleComponentSheafClass X x hx` takes `hx : Order.coheight x = p` and lands in degree 2p. Mathlib's scheme preorder is `a ≤ b ↔ b ⤳ a` (`Scheme.le_iff_specializes`, `rfl`), so the generic point is `⊤` (RT2: `⊤ = genericPoint` by `rfl`) and the coheight of x is the length of the longest chain of generalizations above x, the codimension of closure {x}. Coheights 1, 1, 2 are the codimensions of two lines and a point in ℙ². The proof uses `L < ⊤`, `pt < L` and upstream's `coheight_le_complex` (≤ d = 2); a dual-order reading would give dimension, which agrees with codimension on lines of ℙ² and differs at the point (0 versus 2). The point's coheight 2 therefore tests the order direction.

**`hT` is the right notion.** The general statement asks for T(ℂ) = Z(ℂ) ∩ W(ℂ) as sets of complex points. The literature asks that T be the only component of Z ∩ W (with transversality giving multiplicity one). For closed subsets of a scheme of finite type over ℂ, the closed points are dense in every closed subset (Jacobson property) and they are the complex points, so equality of complex points implies equality of the closed subsets of the scheme: the general statement's `hT` implies the literature's set-theoretic condition, and `htr` gives multiplicity one at every complex point of T. The general statement therefore needs nothing more. On ℙ² the scheme-level equality is also cheap to check directly (RT5, change 2), which removes the appeal to the Jacobson property for this test.

**`htr` coordinate order.** The general `htr` reads L₀ off coordinates `⟨i, _⟩`, i < a, and L₁ off `⟨a + j, _⟩`. With a = b = 1 these are coordinates 0 and 1. `projectiveChart 2 2` has coordinates (x₀/x₂, x₁/x₂), so L₀ is coordinate 0 and L₁ is coordinate 1, as proved. RT1 checks the converse: with L₁ read off coordinate 0 the condition fails at the chart point (0, 1). No conjugation enters: the chart is in the ω-maximal atlas (`projectivePlane_chart_mem_maximalAtlas`), which a conjugated coordinate would leave (conventions row "Algebraic affine chart").

**`hxreg`, `hwreg`.** `cycleComponentSmoothSupportAmbientOpen X x` is the complement of `underlying ⁻¹' (cycleComponentι '' (smoothLocus (cycleComponentι ≫ X.hom))ᶜ)`, the k = 0 term of upstream's filtration (`reducedSmoothClosedFiltration _ S 0 = S`, S = `singularLocusClosed`). The `rintro ⟨z, hz, hzy⟩` reduction to the open lemma is exact: membership fails only through a non-smooth z of the reduced closure lying over [0 : 0 : 1].

## 2. Can the hypotheses be satisfied?

The proved targets have no hypotheses. The open lemma has one, `hz : cycleComponentι _ (planeLine k) z = planeOrigin`; RT4 shows a z exists for k = 0, 1 (`range_subschemeι`, `coe_support_vanishingIdeal`, and `planeOrigin ∈ closure {planeLine k}`), so the lemma is not vacuous. The hypotheses of the general statement are met by the proved items, as RT1 checks by elaboration.

## 3. Is the conclusion trivially true?

Attempts, each under ten lines (RT2 and the prover's list in the sketch):

| Target | Attempt | Result |
|---|---|---|
| open lemma | `Smooth (cycleComponentι _ (planeLine k) ≫ projectivePlane.hom)` by `infer_instance` | fails to synthesize |
| open lemma | `rw [Scheme.Hom.smoothLocus_eq_top]` | fails: no `Smooth` instance |
| open lemma | `simp [Scheme.Hom.mem_smoothLocus]` | unsolved goal (formal smoothness of a stalk map) |
| `coheight_planeOrigin` | `simp [planeOrigin, planeOriginPoint]` | unsolved |
| `htr` | `⟨chartAt _ y, chart_mem_maximalAtlas y, mem_chart_source _ y, by aesop⟩` | aesop fails; upstream's `localChart` is not adapted to the lines by any unfolding |

No definition among the targets unfolds to `True`, no index type is empty (`Fin 1` twice in `htr`), the `ℕ∞` coercions are those of upstream's `hx` and are pinned by the point's value 2 (finite and ≠ 0), and every hypothesis of the open lemma is used by the planned route (`hz` places z over the chart x₂ ≠ 0). The supports are non-degenerate: L₀(ℂ) contains the chart point (0, 1), so it is not the singleton (RT1), and the three points are pairwise distinct (`planeLine_zero_ne_one`, RT1).

## 4. Interface rung?

No. This is a test rung with no structure and no assumed input.

## 5. Checked rung?

Not yet. RT3: the fifteen sorry-free targets print the three standard axioms; the open lemma and the one theorem that uses it print `sorryAx`. The checker rejects the worktree on that sorry only. The ledger names no declarations yet; when the lemma lands, every target in this report's list is the declaration the rung means (the names and statements in the sketch section match the file).

## 6. Conventions

| Convention | Where fixed | Truth depends on it? | Row |
|---|---|---|---|
| homogeneous coordinate indices of ℙ², through `okaIsoSpace` | conventions row "Projective space" | no sign; the names L₀, L₁ and the test's correspondence with the docstring | existing, consistent |
| chart i = 2 has coordinates (x₀/x₂, x₁/x₂), no conjugation; inverse at v is `Fin.insertNth 2 1 v` | row "Algebraic affine chart and the standard chart of ℙⁿ" | `htr` indexes coordinates, so the order is load-bearing (RT1 negative test) | existing, consistent; now proved in Lean by `mem_planeLine_support_iff` |
| holomorphic adapted chart, ω-maximal atlas over `localChart` | row "Holomorphic adapted chart" | the sign of `cycle-class-multiplicative` at odd normal rank; here a = b = 1, so a conjugated chart would flip the sign, which atlas membership excludes | existing |
| scheme order `a ≤ b ↔ b ⤳ a`; coheight = codimension; complex support = `underlying ⁻¹' closure {x}`; Z_reg from `smoothLocus (cycleComponentι ≫ X.hom)` on the reduced closure | upstream `Cycle/Support.lean`, `SmoothClosedLift.lean`, `SmoothSupportPurity.lean`; Mathlib `Scheme.le_iff_specializes` | the degree 2p of every cycle class and the hypotheses `hx`, `ht`, `hxreg`; no sign | **added**: row "Cycle components: scheme points, coheight, complex supports, smooth locus" |

The result is not an identity, so its truth depends on no sign. The downstream identity `cycle-class-multiplicative-p2` has sign + and depends on the rows above through `htr`.

## 7. Equality first

The rung's items are exact: coheights are equalities in `ℕ∞`, `hT` and the singleton are equalities of sets, `htr` is an `↔` at every point of the chart source. They are the inputs of the identity `cycle-class-multiplicative-p2`, [L₀] ∪ [L₁] = [[0 : 0 : 1]] with sign +, an open rung (ledger), which follows by `exact` from the open general rung `cycle-class-multiplicative` (RT1).

## 7b. Non-vacuity test

For this rung: `planeLine_zero_ne_one`, the RT1 negative test (with `projectiveChart 2 2` and L₁ on coordinate 0, the `htr` clause is false), and the RT1 test that `cycleComponentAnalyticClosedSupport projectivePlane (planeLine 0)` is not `{planeOriginPoint}`. Each fails if the points, the chart order or the supports degenerate. For the consumer, the test that the identity is about a nonzero class is `p2-point-class-nonzero`, `cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin ≠ 0` in upstream's API; it exists in the ledger as an open rung, depending on this one.

## 8. Pin drift

The rung was written and red-teamed at the current pin `2ead713`; no drift. Drift list for the next bump (definitions the rung's truth depends on):

| Source | Declarations |
|---|---|
| upstream `Definitions` | `cycleComponent`, `cycleComponentι`, `cycleComponentSupport`, `cycleComponentAnalyticClosedSupport`, `cycleComponentSingularClosedFiltration`, `cycleComponentSingularAmbientClosedFiltration`, `cycleComponentSingularAnalyticClosedFiltration`, `cycleComponentSmoothSupportAmbientOpen`, `reducedSmoothClosedFiltration`, `singularLocusClosed`, the charted space `localChart` (through `maximalAtlas`) |
| upstream `Lemmas` | `SmoothOfRelativeDimension.coheight_le_complex`, `SmoothOfRelativeDimension.height_add_coheight_le_complex` |
| Mathlib | `Scheme.le_iff_specializes`, `Scheme.IdealSheafData.vanishingIdeal`, `subschemeι`, `subschemeCover`, `Scheme.Hom.smoothLocus`, `Scheme.Hom.preimage_smoothLocus_eq` |
| the port | `ProjectiveSpace.chart`, `U`, `chart_preimage_U`, `opensRange_chart`, `iSup_U`, `dehomogenize`, `dehomogenize_X_succAbove` |
| this repository | `okaIsoSpace`, `projectiveChartImmersion`, `projectiveChartOpen_eq`, `projectiveChart`, `projectiveChart_symm_underlying`, `affineChart_source`, `affineChart_target` |

A change upstream to the order direction (coheight read as height), to `cycleComponentSupport` (for example a closure taken in X(ℂ)), or to the filtration index of `cycleComponentSmoothSupportAmbientOpen` would change which hypotheses these items discharge. The file unfolds each of them by a `change`, `rw` or `rintro` (`mem_planeLine_support_iff`, `planeOrigin_lt_planeLine`, `planeOrigin_support_subset_smoothSupportAmbientOpen`), so such a change shows as a build failure here; rerun RT1's instantiation after any bump.

## The open lemma and its route

The lemma is true: the reduced closure of L_k is a line ℙ¹, smooth over ℂ everywhere. The route in the sketch is sound, and every Mathlib name it cites exists at the pin: `IdealSheafData.subschemeCover`, `opensRange_subschemeCover_map`, `subschemeCover_map_subschemeι`, `glueDataObjι_ι`, `vanishingIdeal_ideal` (generated by `@[simps! ideal]` on `vanishingIdeal`, so a grep for its declaration finds nothing; use it through `simp only [vanishingIdeal_ideal]`), `Scheme.Hom.preimage_smoothLocus_eq`, `Scheme.Hom.smoothLocus_eq_top`, `isAffineOpen_opensRange`, `Ideal.quotientKerAlgEquivOfSurjective`. Step 3 also needs `IsOpenMap.preimage_closure_eq_closure_preimage` and `PrimeSpectrum.vanishingIdeal_closure`, `vanishingIdeal_singleton`, both at the pin. Two cautions for phase 2:

1. The affine open of the cover is `⟨projectiveChartOpen 2 2, isAffineOpen_opensRange _⟩ : X.affineOpens`, and `I.ideal U` is computed against `U.fromSpec`, which differs from `projectiveChartImmersion 2 2` by the ring isomorphism Γ(X, U) ≅ ℂ[Y₀, Y₁] of `isoOpensRange` and `IsAffineOpen.isoSpec`. Keep the comap of `planeLinePrime k` along that isomorphism explicit; the `Spec` carrier versus `PrimeSpectrum` mismatch that blocked `rw` in this file recurs here (RT5 needed `planeChartPoint_specializes_iff` applied with explicit arguments for the same reason).
2. Smoothness of `Spec (ℂ[Y₀, Y₁] ⧸ (Y_k)) → Spec ℂ` needs the algebra structure over ℂ to be the one from `MvPolynomial.C`, as in `projectiveChartSchemeIso_over`; a `RingHom` iso that forgets it would leave a smoothness goal over a different ℂ-structure.

## 9. Verdict: pass with changes

Findings:

1. The three points, the chart and its coordinate order are what the docstrings say (section 1); the coordinate correspondence is proved through the port's `U` and `dehomogenize`.
2. Coheight is upstream's index and the values 1, 1, 2 are the codimensions; the point's value tests the order direction.
3. `hT` on complex points implies the literature's "T is the only component" by the Jacobson property; the general statement needs nothing more. On ℙ² it holds at scheme level too (RT5).
4. `htr` is met with L₀ first; the swapped order fails (RT1); no conjugation.
5. The `hxreg`, `hwreg` reduction is exact; the open lemma is true, its hypothesis is satisfiable (RT4), and the route's names exist.
6. `cycle-class-multiplicative-p2` closes by `exact`, also against the target in degree `4` (RT1).
7. No trivial proof found (section 3).

Changes:

A (required, when the open lemma is proved). Import `HodgeLadder.Tests.ProjectivePlaneLines` from `HodgeLadder.lean`; set the ledger `module` to `HodgeLadder.Tests.ProjectivePlaneLines` and list the declarations of this report's target list (plus those of change B if adopted); replace "Not attempted" in the ledger note and record the drift list of section 8 there or in the sketch. Until then the file stays off `main` (checker sorry scan).

B (recommended). Add the scheme-level cross-check of `hT`, so that "the lines meet in the one point" is checked in Lean at the level of scheme points as well as complex points. Checked in RT5 against the module as it stands, standard axioms:

```lean
/-- A prime of `ℂ[Y₀, Y₁]` containing `Y₀` and `Y₁` contains the maximal ideal `(Y₀, Y₁)`. -/
theorem planeEvalPoint_zero_le (q : PrimeSpectrum (MvPolynomial (Fin 2) ℂ))
    (h0 : (planeLinePrime 0).asIdeal ≤ q.asIdeal) (h1 : (planeLinePrime 1).asIdeal ≤ q.asIdeal) :
    (planeEvalPoint 0).asIdeal ≤ q.asIdeal := by
  intro f hf
  rw [mem_planeEvalPoint_iff] at hf
  have hspan : f ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 2))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push Not at hcon
    have hm0 : m = 0 := by ext i; exact hcon i trivial
    subst hm0
    rw [MvPolynomial.mem_support_iff] at hm
    apply hm
    have := hf
    rw [MvPolynomial.eval_zero] at this
    simpa [MvPolynomial.constantCoeff] using this
  refine (Ideal.span_le.mpr ?_) hspan
  rintro _ ⟨i, -, rfl⟩
  fin_cases i
  · exact h0 ((X_mem_planeLinePrime_iff 0 0).mpr rfl)
  · exact h1 ((X_mem_planeLinePrime_iff 1 1).mpr rfl)

/-- At the level of scheme points, `L₀ ∩ L₁` is the closure of `[0 : 0 : 1]`: the point is the only
component of the intersection. -/
theorem closure_planeLine_inter :
    closure {planeLine 0} ∩ closure {planeLine 1} =
      closure ({planeOrigin} : Set projectivePlane.left) := by
  ext y
  refine ⟨fun ⟨h0, h1⟩ => ?_, fun hy => ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj⟩ := exists_mem_U y
    have hy2 : y ∈ (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2 := by
      fin_cases j
      · exact absurd hj (closure_planeLine_subset 0 h0)
      · exact absurd hj (closure_planeLine_subset 1 h1)
      · exact hj
    rw [← projectiveChartOpen_eq] at hy2
    obtain ⟨q, rfl⟩ := hy2
    have h0' := (planeChartPoint_specializes_iff (planeLinePrime 0) q).mp
      (specializes_iff_mem_closure.mpr h0)
    have h1' := (planeChartPoint_specializes_iff (planeLinePrime 1) q).mp
      (specializes_iff_mem_closure.mpr h1)
    rw [planeOrigin_eq]
    exact specializes_iff_mem_closure.mp
      ((planeChartPoint_specializes_iff (planeEvalPoint 0) q).mpr
        (planeEvalPoint_zero_le q h0' h1'))
  · exact specializes_iff_closure_subset.mp
      ((Scheme.le_iff_specializes).mp (planeOrigin_lt_planeLine 0).le) hy
  · exact specializes_iff_closure_subset.mp
      ((Scheme.le_iff_specializes).mp (planeOrigin_lt_planeLine 1).le) hy
```

C (recommended). In the sketch section "What this rung shows about the general statement", point (2), replace "it holds here without knowing `closure {L₀} ∩ closure {L₁} = {[0 : 0 : 1]}` at the level of scheme points, and the general proof does not need that" by: "on a scheme of finite type over ℂ the complex points are dense in every closed subset, so `hT` implies the scheme-level equality `closure {x} ∩ closure {w} = closure {t}` (T is the only component, as the literature requires); on ℙ² that equality is `closure_planeLine_inter`."

D (done). Conventions row "Cycle components: scheme points, coheight, complex supports, smooth locus" added to `docs/conventions.md`.

Considered and not required: a global description `z ∈ L_k(ℂ) ↔ z.underlying ∉ D₊(x_k)` for every z (needs the chart x₀ ≠ 0 or x₁ ≠ 0 for the points with x₂ = 0; no consumer reads L_k away from [0 : 0 : 1]).

## Sources

`Fulton1998` §8.2, Cor. 19.2 (numbering unverified); the Jacobson property of schemes of finite type over a field [`Stacks`, tag unverified]. Upstream, Mathlib and port declarations by name, read at `2ead713` and Mathlib `v4.35.0-rc4`.
