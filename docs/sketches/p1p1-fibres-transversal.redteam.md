# Red team: `p1p1-fibres-transversal`

Date: 2026-11-27. Worktree `p1p1-fibres-transversal`, branch `track/p1p1-fibres-transversal`, candidate commit `27a6c4c` (base `16daf66`): `HodgeLadder/Tests/P1p1Fibres.lean`, module `HodgeLadder.Tests.P1p1Fibres`, 652 lines, 69 declarations, and its import in `HodgeLadder.lean`. Ledger not yet updated. Pin: `Paul-Lez/HodgeConjecture@2ead713179628a3c738197d5996f51c8a9c886ac` (package checkout `HEAD`), Lean and Mathlib `v4.35.0-rc4`, the same as `main` at `e733367`.

Read: the ledger entry and `python3 tools/next.py p1p1-fibres-transversal`; `docs/sketches/cycle-class-multiplicative.md` (finding 12, sub-rungs table); `docs/sketches/p1p1-witness.redteam.md`, `complex-points-prod.redteam.md`, `p2-lines-transversal.redteam.md`; `HodgeLadder/Tests/CycleClassMultiplicativeP2.lean`; the statements of `HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal` (`HodgeLadder/Cycle/Multiplicative.lean:580`) and `_noReg` (`HodgeLadder/Cycle/MultiplicativeNoReg.lean:285`); `HodgeLadder/Tests/ProjectiveLinePoint.lean` (`infty`, `openOne`, `not_mem_openOne_iff`); `HodgeLadder/Tests/ProjectiveChart.lean` (`projectiveChart`); `HodgeLadder/Normalization/AffineChart.lean` (`affineChart_source`, `affineChart_target`); upstream `Definitions/AlgebraicGeometry/Cycle/Support.lean` (`cycleComponentι`), `Cycle/Component/SmoothClosedLift.lean` (`cycleComponentAnalyticClosedSupport`), `Cycle/Component/SmoothSupportPurity.lean` (`cycleComponentSmoothSupportAmbientOpen`), `Cycle/Component/SingularClosedFiltration.lean`, `Lemmas/AlgebraicGeometry/Smooth/DimensionFormula.lean` (`coheight_le_complex`); Mathlib `IdealSheaf/Basic.lean`, `IdealSheaf/Functorial.lean` (`map_vanishingIdeal`), `IdealSheaf/Subscheme.lean` (`Hom.toImage`), `Topology/Sober.lean` (`IsGenericPoint.image`, `genericPoint_spec`); `docs/conventions.md`, `docs/references.md`, `docs/gaps.md`.

Scratch (directory `scratch-rt/` inside the worktree, deleted afterwards; the worktree's `.olean` of the module is current):

| File | What | Result |
|---|---|---|
| App | the prover's application file, re-run unchanged: `cycleComponentSheafClass_cup_of_transversal_noReg p1p1 (d := 2)` and `cycleComponentSheafClass_cup_of_transversal p1p1 (d := 2)` applied term by term to the rung's lemmas, target `cup [p1p1FibreFst] [p1p1FibreSnd] (2 * (1 + 1)) = [p1p1Corner]` | both elaborate by plain term application, no `show` or `convert`; 5.8 s wall |
| Probe P1 | coordinate order: `¬ ∀ z ∈ p1p1Chart.source, (z ∈ supp p1p1FibreFst ↔ p1p1Chart z 1 = 0)`, witness `prod.lift inftyPoint (lineChart.symm ![1])` | proved; the swapped indexing is false |
| Probe P2 | `p1p1FibreFst ≠ p1p1Corner`, `p1p1FibreSnd ≠ p1p1Corner`, `p1p1FibreFst ≠ ⊤` | proved from the `lt` lemmas |
| Probe P3 | `closure (Set.range s) = closure {s ⊤}` by `rw [← Set.image_univ]; exact ((genericPoint_spec P).image s.continuous).symm` | proved; Mathlib route for `closure_range_eq_closure_top` |
| Probe P4 | `(cycleComponentAnalyticClosedSupport p1p1 p1p1Corner : Set _).Nonempty` | proved; `htr` quantifies over a nonempty set |
| Trivial T1 to T4 | `htr` with `chartAt`, `IsManifold.chart_mem_maximalAtlas`, `mem_chart_source` and `simp`; `coheight p1p1FibreFst = 1` by `simp`; `coheight p1p1Corner = 2` by `simp [p1p1Corner]`; `hT` by `ext; simp`; P3 inlined at the call site of `smooth_cycleComponentι_p1p1FibreFst` | T1 to T3 fail (unsolved goals); T4 compiles |
| Axioms | `#print axioms` of all 69 declarations of the module | every one `[propext, Classical.choice, Quot.sound]` |
| O2 | the texts of optional changes O1 and O2, in the module's namespace and `open` lines | both compile, standard axioms |

`python3 tools/check.py --no-build` in the worktree: `ACCEPTED: all checks passed`. The rung's declarations are not yet in the ledger, so the checker printed no axioms line for them; the scratch `Axioms` file covers all 69.

**Verdict: pass with changes.** The three points are the generic points of the reduced fibres pr₁⁻¹(∞) = {∞} × ℙ¹ and pr₂⁻¹(∞) = ℙ¹ × {∞} and the closed point (∞, ∞), with ∞ = [1 : 0] the checked point `infty` of `projective-line-point`. Each proved item is the exact hypothesis of `cycleComponentSheafClass_cup_of_transversal` it claims to be, and both transversal theorems apply by term. The chart carries content: it is a product of holomorphic charts in the ω-maximal atlas, with the fibres as its two coordinate hyperplanes, and the swapped indexing is provably false. No sign enters this rung, and none can enter `cycle-class-multiplicative-p1p1` beyond the theorem's computed (−1)^{(2·1)(2·1)} = 1. The changes are bookkeeping and one docstring: the ledger title names the chart `openOne`, which misses ∞, and must be corrected; one docstring overstates a hypothesis; one general lemma has a two-line Mathlib route; ledger, gaps, conventions, roadmap and sketch rows follow.

## Findings

### 1. Is this the statement the literature makes?

The literature statement this rung feeds: on a nonsingular variety, the cycle map is a ring homomorphism, and two subvarieties meeting transversally along one component T have [Z]·[W] = [T] [`Fulton1998` §8.2 and Cor. 19.2; numbering unverified]. On ℙ¹ × ℙ¹ the fibres {p} × ℙ¹ and ℙ¹ × {q} meet transversally in the reduced point (p, q), and their classes are pr₁*[p], pr₂*[q] [`Fulton1998` ch. 19, flat pullback; numbering unverified].

| Literature object | Lean | Comparison |
|---|---|---|
| ℙ¹ × ℙ¹ over ℂ | `p1p1 = projectiveLine ⨯ projectiveLine` in `Over (Spec ↧ℂ)` | rung `p1p1-witness`, passed; projections `prod.fst`, `prod.snd`; complex points `(map prod.fst z, map prod.snd z)` (conventions row "Complex points of a product and product charts") |
| the point ∞ = [1 : 0] of ℙ¹ | `infty = okaIso.hom.base okaInfty`; `inftyPoint = lineChart.symm 0`, `inftyPoint_underlying : inftyPoint.underlying = infty` | `okaInfty` is Oka's chart 0 at `dehomogenizeVec 0 ![1, 0] = 0`; `not_mem_openOne_iff : y ∉ openOne ↔ y = infty` with `openOne` the chart x₁ ≠ 0, so ∞ = {x₁ = 0} = [1 : 0] |
| the chart x₀ ≠ 0 of ℙ¹, coordinate x₁ / x₀ | `lineChart = projectiveChart 1 0` | chart i has coordinate m equal to x_{i.succAbove m} / xᵢ (conventions row "Algebraic affine chart"), here x₁ / x₀; `underlying_eq_infty_iff`: on the source, b lies over ∞ exactly when the coordinate is 0 |
| generic point of {∞} × ℙ¹ = pr₁⁻¹(∞) | `p1p1FibreFst = fibreSectionFst.left ⊤`, `fibreSectionFst = prod.lift constInfty (𝟙 _)` | `fst_p1p1FibreFst` (pr₁ is ∞), `snd_p1p1FibreFst` (pr₂ is the generic point of ℙ¹); on complex points the closure is exactly {pr₁ z over ∞} (`mem_p1p1FibreFst_support_iff_fst`) |
| generic point of ℙ¹ × {∞} = pr₂⁻¹(∞) | `p1p1FibreSnd = fibreSectionSnd.left ⊤` | symmetric (`fst_p1p1FibreSnd`, `snd_p1p1FibreSnd`, `mem_p1p1FibreSnd_support_iff_snd`) |
| the closed point (∞, ∞) | `p1p1Corner = (prod.lift inftyPoint inftyPoint).underlying` | `p1p1Corner_support_eq_singleton`: its complex support is the one complex point (∞, ∞) |
| reduced structure | upstream `cycleComponentι X x = (vanishingIdeal ⟨closure {x}, _⟩).subschemeι` | the reduced closed subscheme on closure {x}; `smooth_cycleComponentι_of_closedImmersion` identifies it with the section's source ℙ¹ through `ker_eq_vanishingIdeal_of_isReduced` and Mathlib's `Hom.toImage`, and the `change` in its proof pins the upstream definition by defeq |

**Coheight is the right invariant.** Upstream indexes `cycleComponentSheafClass X x hx` by `hx : Order.coheight x = p`, degree 2p. Mathlib's scheme order is `a ≤ b ↔ b ⤳ a`, so ⊤ is the generic point and coheight is codimension of the closure. The values 1, 1, 2 come from the strict chain (∞, ∞) < fibre < ⊤ and upstream's `SmoothOfRelativeDimension.coheight_le_complex` at d = 2 (`coheight_eq_one_of_between`); a fibre of coheight 1 and a point of coheight 2 on a surface are the literature's codimensions.

**`hT` is the right notion.** The theorem asks T(ℂ) = Z(ℂ) ∩ W(ℂ) on complex points. `mem_p1p1Fibres_inter_iff` proves both inclusions with content: a complex point in both supports has both projections equal to `inftyPoint` (`eq_inftyPoint_of_underlying`), so it is `prod.lift inftyPoint inftyPoint` by `eq_prodLift`. A scheme-level form, closure {Z} ∩ closure {W} = closure {T}, was added on ℙ² as a cross-check (`closure_planeLine_inter`); here it would need the fibre of ℙ¹ × ℙ¹ over (∞, ∞) or a Jacobson argument, and the theorem uses only the complex-point form (optional change O3).

**`htr` is the literature's transversality.** `p1p1Chart = prodChart projectiveLine projectiveLine lineChart lineChart` has coordinates (x₁/x₀ ∘ pr₁, x₁/x₀ ∘ pr₂), first factor first (`p1p1Chart_apply_zero`, `p1p1Chart_apply_one`, both by `prodChart_apply` and `rfl`). It lies in the ω-maximal atlas by `prodChart_mem_maximalAtlas` (rung `complex-points-prod`) and `projectiveChart_mem_maximalAtlas` (rung `affine-chart-analytic-p2`). On its source, {∞} × ℙ¹ is {v₀ = 0} and ℙ¹ × {∞} is {v₁ = 0} (`mem_p1p1FibreFst_support_iff`, `mem_p1p1FibreSnd_support_iff`). Two distinct coordinates of a holomorphic chart have independent differentials at every point, so T_y Z + T_y W = T_y X at y = (∞, ∞): the transversality of the literature, holomorphically.

**`hxreg`, `hwreg`.** `cycleComponentSmoothSupportAmbientOpen X x` is the complement of `underlying ⁻¹' (cycleComponentι '' (smoothLocus)ᶜ)` (upstream filtration at k = 0). Both proofs reduce it to `smoothLocus = ⊤`, from `Smooth (cycleComponentι ≫ p1p1.hom)`, which is proved from the section being a closed immersion with reduced smooth source ℙ¹. This is stronger than the hypothesis (the whole fibre is smooth) and correct: each fibre is isomorphic to ℙ¹.

### 2. Can the hypotheses be satisfied?

The rung's targets have no hypotheses; they are the hypotheses of the transversal theorem, instantiated. Scratch App shows both theorems accept them by term at `X = p1p1`, `d := 2`, `a = b = 1`. The general lemmas have satisfiable hypotheses, each used once at the two sections: `ker_eq_vanishingIdeal_of_isReduced` (`[IsReduced P]`, instance on ℙ¹), `smooth_cycleComponentι_of_closedImmersion` (`[IsReduced P.left] [Smooth P.hom] [IsClosedImmersion s.left]`, all found for ℙ¹ and the two sections), `closure_range_eq_closure_top` (`[IsIntegral P]`). Probe P4: `htr` quantifies over a nonempty set.

### 3. Is the conclusion trivially true?

| Target | Attempt (under ten lines) | Result |
|---|---|---|
| `p1p1Fibres_transversal` | upstream `chartAt`, `IsManifold.chart_mem_maximalAtlas`, `mem_chart_source`, then `constructor <;> simp` | unsolved goals; upstream's `localChart` is not adapted to the fibres by unfolding |
| `coheight_p1p1FibreFst` | `simp` | unsolved goals |
| `coheight_p1p1Corner` | `simp [p1p1Corner]` | unsolved goals |
| `p1p1Corner_support_eq_inter` | `ext y; simp` | unsolved goals |
| swapped `htr` (fibre {∞} × ℙ¹ as coordinate 1) | Probe P1 | false, proved |

No definition unfolds to `True`; the ℕ∞ coercions are `((1 : ℕ) : ℕ∞)` and `((1 : ℕ) : ℕ∞) + ((1 : ℕ) : ℕ∞)`, exactly the theorem's `↑a`, `↑a + ↑b`; no index type is empty (`Fin 1` twice, `Fin 2`); every hypothesis of every lemma is used. Circularity: the module imports neither `HodgeLadder.Cycle.Multiplicative` nor any cycle-class module; it proves facts about points, supports and charts only.

### 4. Interface rung

Not an interface rung (decision 0003); no structure, no axioms.

### 5. Checked rung: checker and declarations

`tools/check.py --no-build`: ACCEPTED. All 69 declarations print the three standard axioms (scratch `Axioms`, plus the three `smooth_cycleComponentι_*` names separately). No `sorry`, `native_decide` or `unsafe`. The declarations the ledger should name are listed in change 2; each is the object the title means (finding 1 table).

Instances declared in the module: `isSeparated_projectiveLine`, `isSeparated_p1p1_fst`, `isSeparated_p1p1_snd`, `isClosedImmersion_fibreSectionFst`, `isClosedImmersion_fibreSectionSnd`. All are `Prop`-valued, so they cannot change how an upstream statement elaborates.

### 6. Conventions

| Convention | Where it enters | Row | Truth depends on it? |
|---|---|---|---|
| ∞ = [1 : 0], the closed point off x₁ ≠ 0 | `infty`, `inftyPoint` | missing; add (change 8c) | no: any closed point of ℙ¹ gives the same statements; downstream, `fibre-class-pullback` must pull back the class of the same point `infty` |
| chart of ℙ¹ is x₀ ≠ 0 with coordinate x₁ / x₀ | `lineChart = projectiveChart 1 0` | "Algebraic affine chart and the standard chart of ℙⁿ"; its `p1p1-fibres-transversal` sentence describes a planned isomorphism with 𝔸² that was not built (change 8a) | for `htr`, yes: the chart x₁ ≠ 0 (`openOne`) misses ∞, so its product cannot contain (∞, ∞); this is the title error (change 1) |
| product chart coordinates first factor first, `Fin.append` | `p1p1Chart` | "Complex points of a product and product charts" | yes for `htr` (Probe P1: swapped indexing false); no for the class identity (finding 7) |
| Z = {∞} × ℙ¹ is the first cup factor, W = ℙ¹ × {∞} the second | `htr` order, `cup` order of the application | "Transversal product of cycle classes" | the identity holds for both orders here (even degrees); the order must match `cup-positive-degree-test`'s pr₁*[pt] ∪ pr₂*[pt], and it does |
| coheight as codimension; `↑1 + ↑1` | `coheight_p1p1Corner_add` | "Cycle components: scheme points, coheight, complex supports, smooth locus" | yes; matches the theorem's `ht` by term |
| reduced structure on closure {x} | upstream `cycleComponentι` | same row | yes for `hxreg`, `hwreg`; matched by defeq in `smooth_cycleComponentι_of_closedImmersion` |

No cited or assumed input: the rung is unconditional, and the borrowed results (`prodChart_mem_maximalAtlas`, `projectiveChart_mem_maximalAtlas`, `coheight_le_complex`, `coheight_infty`, `closure_infty`, Mathlib's `IsClosedImmersion.of_comp`, `map_vanishingIdeal`, `Hom.toImage_imageι`) carry no sign or scalar.

### 7. Equality first; signs

This rung proves no identity between classes; it supplies the hypotheses of one. The identity it is a step toward is `cycle-class-multiplicative-p1p1`, [{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)], exact, which is open in the ledger and holds by term from this rung (scratch App; change O1 gives its exact statement).

Signs. Nothing in this rung is −1, and nothing other than Mathlib's Koszul (−1)^p conventions is forced. The only sign on the route of the identity is `(−1)^((2·1)·(2·1)) = 1` of `cup_singular_comparison`, computed inside the theorem by `Even.neg_one_pow`. The coordinate order cannot introduce one: swapping the two complex coordinates of ℂ² has complex determinant −1 and real determinant (−1)² = 1, so it preserves the complex orientation (conventions row "Product of local classes": ℂ-linear reorderings leave the chart coclass unchanged). The factor order cannot either: degree-2 classes would commute with sign (−1)^{2·2} = 1. The ladder has no checked graded commutativity for the sheaf `cup`, so the factor order still matters formally for `cup-positive-degree-test`: that rung must state pr₁*[∞] ∪ pr₂*[∞], first factor first, to compose with `cycle-class-multiplicative-p1p1` and `fibre-class-pullback` without a commutativity lemma. Its ledger title already does.

As on ℙ², the identity constrains signs only where [(∞, ∞)] ≠ 0 (`p1p1-point-class-nonzero`), and a uniform (−1)^p on codimension-p classes satisfies it (c₁ · c₁ = +1). `cup-positive-degree-test` asks only for ≠ 0 and is insensitive to every sign.

### 7b. Non-vacuity

Present in the module: `p1p1FibreFst_ne_p1p1FibreSnd` (the two fibres are different scheme points), `p1p1Chart_p1p1CornerPoint` (the corner is the chart origin), and the strict inequalities `p1p1Corner_lt_p1p1FibreFst`, `p1p1Corner_lt_p1p1FibreSnd`, `p1p1FibreFst_lt_top`, `p1p1FibreSnd_lt_top`. The smallest test that would fail if `htr` were satisfiable trivially is Probe P1 (the swapped indexing is false); it is not in the module (optional change O2 gives it). For the downstream identity, the smallest test is `cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner ≠ 0` (upstream `AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass`), rung `p1p1-point-class-nonzero`, open; without it, `cycle-class-multiplicative-p1p1` holds for [T] = 0 as well.

### 8. Pin drift

The rung was written at the current pin `2ead713`; `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are unchanged between the branch base `16daf66` and `main` `e733367`. Files changed on `main` since the base: `HodgeLadder.lean` (two imports), `HodgeLadder/Hodge/DeRhamCupBilinear.lean`, `HodgeLadder/Tests/DeRhamCupP2.lean`, `docs/conventions.md`, `docs/gaps.md`, `docs/roadmap.md`, `ledger/ladder.json`, a handoff and a red-team file. None is imported by this module. A rebase onto `main` touches only `HodgeLadder.lean` (adjacent import lines) and the documentation files that the changes below also edit (change 10).

Drift list for a future bump, the upstream and local definitions whose change could alter this rung: upstream `cycleComponentι`, `cycleComponentSupport`, `cycleComponentAnalyticClosedSupport`, `cycleComponentSmoothSupportAmbientOpen`, `cycleComponentSingularAnalyticClosedFiltration`, `SmoothOfRelativeDimension.coheight_le_complex`, the charted-space instance on `ComplexPoint`; Mathlib `Scheme.Hom.ker`, `IdealSheafData.vanishingIdeal`, `map_vanishingIdeal`, `Hom.toImage`, `smoothLocus_eq_top`, `IsClosedImmersion.of_comp`, the `OrderTop` instance on integral schemes; local `projectiveChart`, `prodChart`, `infty`, `projectiveLine_hom_eq`. Upstream has a private special case of `ker_eq_vanishingIdeal_of_isReduced` for complex points (`complexPoint_ker_eq_vanishingIdeal_closure`, `Lemmas/AlgebraicGeometry/Cycle/Support.lean:66`); a bump that makes a general version public is a clash candidate.

### 9. Placement and general lemmas

The file sits in `HodgeLadder/Tests/`, next to the ℙ² analogue `ProjectivePlaneLines.lean`. The default `HodgeLadder/P1p1/Fibres/Transversal.lean` printed by `next.py` is derived from the id when the ledger has no module; the Tests placement matches the ladder and is acceptable. Import layer: 8 (`tools/pinwalk.py` graph; `P1p1Witness` 7, `ProjectiveChart` 7, `ProjectivePlaneLines` 8). Build of the module: about 8 s.

Mathlib and upstream equivalents of the three general lemmas, searched at the pin:

| Lemma | Equivalent | Disposition |
|---|---|---|
| `ker_eq_vanishingIdeal_of_isReduced` | none public; Mathlib has `map_vanishingIdeal`, `vanishingIdeal_top`, `nilradical_eq_bot`, from which it is proved; upstream's private `complexPoint_ker_eq_vanishingIdeal_closure` is the case P = Spec ℂ | keep local; docstring overstates the hypothesis (change 4) |
| `smooth_cycleComponentι_of_closedImmersion` | none; it is about upstream's `cycleComponentι` | keep local |
| `closure_range_eq_closure_top` | a two-line consequence of Mathlib's `IsGenericPoint.image` and `genericPoint_spec` (Probe P3, T4) | delete and inline (change 5), per decision 0011 "use what Mathlib has before writing a local copy" |

Category for `docs/gaps.md`: "Algebraic geometry and commutative algebra" (diff Mathlib `AlgebraicGeometry/`, upstream `.../AlgebraicGeometry/Cycle/`), after the `HodgeLadder.Tests.P1p1Witness` row.

### 10. Folding `cycle-class-multiplicative-p1p1`

It is a direct application and the precedent bundled two rungs in one maintainer PR (#215). Fold it, in its own module so that `HodgeLadder.Tests.P1p1Fibres` keeps its light imports, mirroring `HodgeLadder/Tests/CycleClassMultiplicativeP2.lean` (optional change O1, exact text there). Proof by the theorem with `hxreg`, `hwreg`, which exercises every lemma of this rung; scratch App confirms both forms.

## Required changes

1. **Ledger title** of `p1p1-fibres-transversal`, replace with exactly:

   `On ℙ¹ × ℙ¹ the fibres {∞} × ℙ¹, ℙ¹ × {∞} and the point (∞, ∞), ∞ = [1 : 0], have coheight 1, 1, 2, their complex supports meet in (∞, ∞) alone, the product of the chart x₀ ≠ 0 of ℙ¹ with itself (coordinate x₁ / x₀ on each factor, first factor first) satisfies the transversality hypothesis htr with {∞} × ℙ¹ as coordinate 0, and (∞, ∞) lies in the smooth locus of each fibre's reduced closure`

   This corrects a specification detail that could not hold (the chart `openOne`, x₁ ≠ 0, misses ∞ by `not_mem_openOne_iff`); `htr` is existential in the chart, so the hypothesis supplied to the theorem is unchanged and nothing is weakened.

2. **Ledger entry**: `status` `checked`; `module` `HodgeLadder.Tests.P1p1Fibres`; `contributors` `["claude-code"]`; `declarations`, with `closure_range_eq_closure_top` removed per change 5:

   `HodgeLadder.Tests.lineChart`, `lineChart_mem_maximalAtlas`, `inftyPoint`, `inftyPoint_underlying`, `underlying_eq_infty_iff`, `eq_inftyPoint_of_underlying`, `constInfty`, `fibreSectionFst`, `fibreSectionSnd`, `p1p1FibreFst`, `p1p1FibreSnd`, `p1p1CornerPoint`, `p1p1Corner`, `fst_p1p1FibreFst`, `snd_p1p1FibreFst`, `fst_p1p1FibreSnd`, `snd_p1p1FibreSnd`, `mem_p1p1FibreFst_support_iff_fst`, `mem_p1p1FibreSnd_support_iff_snd`, `p1p1Corner_lt_p1p1FibreFst`, `p1p1Corner_lt_p1p1FibreSnd`, `p1p1FibreFst_lt_top`, `p1p1FibreSnd_lt_top`, `coheight_p1p1FibreFst`, `coheight_p1p1FibreSnd`, `coheight_p1p1Corner`, `coheight_p1p1Corner_add`, `mem_p1p1Fibres_inter_iff`, `p1p1Corner_support_eq_inter`, `p1p1Corner_support_eq_singleton`, `p1p1Chart`, `p1p1Chart_mem_maximalAtlas`, `p1p1Chart_apply_zero`, `p1p1Chart_apply_one`, `mem_p1p1FibreFst_support_iff`, `mem_p1p1FibreSnd_support_iff`, `p1p1Fibres_transversal`, `isClosedImmersion_fibreSectionFst`, `isClosedImmersion_fibreSectionSnd`, `ker_eq_vanishingIdeal_of_isReduced`, `smooth_cycleComponentι_of_closedImmersion`, `smooth_cycleComponentι_p1p1FibreFst`, `smooth_cycleComponentι_p1p1FibreSnd`, `p1p1Corner_support_subset_smoothSupportAmbientOpen_fst`, `p1p1Corner_support_subset_smoothSupportAmbientOpen_snd`, `p1p1FibreFst_ne_p1p1FibreSnd`, `p1p1Chart_p1p1CornerPoint` (each with the prefix `HodgeLadder.Tests.`).

3. **Ledger `depends_on`**: `["p1p1-witness", "complex-points-prod", "projective-line-point", "affine-chart-analytic", "affine-chart-analytic-p2"]` (the chart's atlas membership is `projectiveChart_mem_maximalAtlas`, rung `affine-chart-analytic-p2`). **Ledger `note`**, replace with exactly:

   `Checked 2026-11-27. Red team finding 12 on cycle-class-multiplicative. ∞ = [1 : 0] is infty of projective-line-point. The fibres are images of the generic point of ℙ¹ under the sections prod.lift constInfty (𝟙 _) and prod.lift (𝟙 _) constInfty, constInfty the constant map at inftyPoint = lineChart.symm 0; the corner is prod.lift inftyPoint inftyPoint. Checked: coheights 1, 1, 2 from the chain (∞, ∞) < fibre < ⊤ and upstream's coheight_le_complex at d = 2 (hx, hw; ht as ↑1 + ↑1 in coheight_p1p1Corner_add); p1p1Corner_support_eq_inter (hT) on complex points, with the singleton form; p1p1Fibres_transversal (htr) with p1p1Chart = prodChart of lineChart = projectiveChart 1 0 (coordinate x₁ / x₀, vanishing exactly at ∞) with itself, first factor first, in the ω-maximal atlas by prodChart_mem_maximalAtlas and projectiveChart_mem_maximalAtlas; {∞} × ℙ¹ is coordinate 0 and ℙ¹ × {∞} coordinate 1. The planned chart openOne (x₁ ≠ 0) misses ∞ and was not used; no isomorphism with 𝔸² is built. hxreg, hwreg: each section is a closed immersion (a section of a separated projection), its source ℙ¹ is reduced, so its kernel is the vanishing ideal of the fibre's closure (ker_eq_vanishingIdeal_of_isReduced) and upstream's cycleComponentι is ℙ¹ through Mathlib's Hom.toImage, smooth over ℂ (smooth_cycleComponentι_of_closedImmersion). Both cycleComponentSheafClass_cup_of_transversal and its _noReg form apply by term at p1p1 (d := 2), a = b = 1. No sign: conventions rows "Point ∞ of ℙ¹ and the fibres of ℙ¹ × ℙ¹" and "Complex points of a product and product charts". Red team pass with changes (docs/sketches/p1p1-fibres-transversal.redteam.md). Sketch: docs/sketches/cycle-class-multiplicative.md.`

4. **Docstring of `ker_eq_vanishingIdeal_of_isReduced`**: the statement has no closed-immersion hypothesis. Replace the docstring with exactly:

   `/-- The kernel of a morphism of schemes from a reduced scheme is the vanishing ideal of the closure of its range. -/`

5. **Delete `closure_range_eq_closure_top`** and inline the Mathlib route at its two call sites; in `smooth_cycleComponentι_p1p1FibreFst` and `smooth_cycleComponentι_p1p1FibreSnd` replace `(closure_range_eq_closure_top _)` with exactly:

   `(by rw [← Set.image_univ]; exact ((genericPoint_spec _).image (Scheme.Hom.continuous _)).symm)`

   (Scratch T4 compiles it at the first call site.) Remove `closure_range_eq_closure_top` from the module docstring's "General" line.

6. **`HodgeLadder.lean`**: keep the import `public import HodgeLadder.Tests.P1p1Fibres` after `HodgeLadder.Tests.P1p1Witness` when rebasing (change 10).

7. **`docs/gaps.md`**, section "Algebraic geometry and commutative algebra", new row after the `HodgeLadder.Tests.P1p1Witness` row, exactly:

   `| \`HodgeLadder.Tests.ker_eq_vanishingIdeal_of_isReduced\` (the kernel of a morphism from a reduced scheme is the vanishing ideal of the closure of its range), \`smooth_cycleComponentι_of_closedImmersion\` (if a closed immersion over Spec ℂ from a reduced smooth P has range with closure closure {x}, upstream's reduced closure \`cycleComponentι X x\` is smooth over ℂ) | \`HodgeLadder.Tests.P1p1Fibres\` | 8 | Mathlib has \`map_vanishingIdeal\` and \`Hom.toImage\`, from which both follow, and no kernel statement for reduced sources; upstream's private \`complexPoint_ker_eq_vanishingIdeal_closure\` is the case P = Spec ℂ, a clash candidate at a bump; the second is about upstream's \`cycleComponentι\`; rung \`p1p1-fibres-transversal\` | 2026-11-27 |`

8. **`docs/conventions.md`**:

   a. Row "Algebraic affine chart and the standard chart of ℙⁿ", column "Results whose truth depends on it": replace the sentence `` `p1p1-fibres-transversal`: the isomorphism with 𝔸² that it builds fixes which fibre is coordinate 0. `` with exactly:

   `` `p1p1-fibres-transversal`: on ℙ¹ the chart at i = 0 has coordinate x₁ / x₀, which vanishes exactly at ∞ = [1 : 0] (`underlying_eq_infty_iff`), while the chart at i = 1 (`openOne`) misses ∞; ℙ¹ × ℙ¹ uses `prodChart` of the chart at i = 0 with itself, and no isomorphism with 𝔸² is built. ``

   b. Row "Complex points of a product and product charts", same column: after `` `p1p1-fibres-transversal`: `htr` indexes coordinates, so the fibre cut out by the first factor's coordinate is coordinate 0. `` insert exactly:

   `` Checked: on `p1p1Chart`, {∞} × ℙ¹ = {v₀ = 0} and ℙ¹ × {∞} = {v₁ = 0} (`mem_p1p1FibreFst_support_iff`, `mem_p1p1FibreSnd_support_iff`); the swapped indexing is false (red team 2026-11-27, scratch). ``

   c. New row after "Complex points of a product and product charts", exactly:

   `` | Point ∞ of ℙ¹ and the fibres of ℙ¹ × ℙ¹ | this repository, `HodgeLadder.Tests.infty` (`HodgeLadder/Tests/ProjectiveLinePoint.lean`, rung `projective-line-point`), `inftyPoint`, `lineChart`, `fibreSectionFst`, `fibreSectionSnd`, `p1p1FibreFst`, `p1p1FibreSnd`, `p1p1Corner`, `p1p1Chart` (`HodgeLadder/Tests/P1p1Fibres.lean`, rung `p1p1-fibres-transversal`) | ∞ = [1 : 0], the closed point off the chart x₁ ≠ 0, equal to `lineChart.symm 0` with `lineChart = projectiveChart 1 0` (coordinate x₁ / x₀); `p1p1FibreFst` is the generic point of {∞} × ℙ¹ = pr₁⁻¹(∞), `p1p1FibreSnd` of ℙ¹ × {∞} = pr₂⁻¹(∞), both with the reduced structure of upstream's `cycleComponentι`; in `htr` and in `cup`, {∞} × ℙ¹ comes first (coordinate 0 and first factor), matching pr₁*[pt] ∪ pr₂*[pt] | `p1p1-fibres-transversal`: none for the choice of point (any closed point gives the same statements); the coordinate index of each fibre in `htr` depends on the first-factor-first order. `cycle-class-multiplicative-p1p1`: no sign; the theorem's only sign is (−1)^{(2·1)(2·1)} = 1, a swap of the two complex coordinates preserves the complex orientation, and degree-2 classes commute with sign +1. `fibre-class-pullback`, `cup-positive-degree-test`: must pull back the class of the same point `infty` and state pr₁* before pr₂*, since the ladder has no checked graded commutativity for `cup` at the pin | read from source; checked in scratch (red team 2026-11-27, `p1p1-fibres-transversal`) | ``

9. **`docs/roadmap.md`** row `p1p1-fibres-transversal`, replace with exactly:

   `` | `p1p1-fibres-transversal` | test | checked | `p1p1-witness`, `complex-points-prod`, `projective-line-point`, `affine-chart-analytic`, `affine-chart-analytic-p2` | the fibres {∞} × ℙ¹, ℙ¹ × {∞} and the point (∞, ∞) meet every hypothesis of the transversal theorem, with the product of the chart x₀ ≠ 0 of ℙ¹ with itself and the smooth-locus fact; `HodgeLadder.Tests.P1p1Fibres`; `docs/sketches/cycle-class-multiplicative.md` | ``

   and in `docs/sketches/cycle-class-multiplicative.md`, sub-rungs table row `p1p1-fibres-transversal`, replace `the product chart of \`openOne\` satisfies \`htr\` (in the maximal atlas by \`affine-chart-analytic\`)` with `the product of the chart x₀ ≠ 0 of ℙ¹ with itself satisfies \`htr\` (in the maximal atlas by \`prodChart_mem_maximalAtlas\` and \`affine-chart-analytic-p2\`; the chart \`openOne\` misses ∞)`.

10. **Rebase** onto `main` (`e733367` or later) before the pull request; resolve `HodgeLadder.lean` by keeping both new `DeRhamCup*` imports and this module's import, and re-run `python3 tools/check.py`.

## Optional changes

O1. **Fold `cycle-class-multiplicative-p1p1`** into this pull request as `HodgeLadder/Tests/CycleClassMultiplicativeP1p1.lean`, module `HodgeLadder.Tests.CycleClassMultiplicativeP1p1`, imports `HodgeLadder.Tests.P1p1Fibres` and `HodgeLadder.Cycle.Multiplicative`, statement exactly:

```lean
/-- **`[{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)]` on ℙ¹ × ℙ¹**, exact, sign `+`: the Yoneda cup product
of the cycle classes of the fibres of the first and second projections over `∞ = [1 : 0]` is the
cycle class of their intersection point. Conventions rows "Transversal product of cycle classes"
and "Point ∞ of ℙ¹ and the fibres of ℙ¹ × ℙ¹". -/
theorem p1p1Fibres_cup_eq_p1p1Corner :
    HodgeLadder.Cup.cup
        (cycleComponentSheafClass p1p1 p1p1FibreFst coheight_p1p1FibreFst)
        (cycleComponentSheafClass p1p1 p1p1FibreSnd coheight_p1p1FibreSnd)
        (2 * (1 + 1)) (by ring) =
      cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner_add :=
  HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal p1p1 (d := 2)
    p1p1FibreFst p1p1FibreSnd p1p1Corner coheight_p1p1FibreFst coheight_p1p1FibreSnd
    coheight_p1p1Corner_add (by norm_num) p1p1Corner_support_eq_inter
    p1p1Corner_support_subset_smoothSupportAmbientOpen_fst
    p1p1Corner_support_subset_smoothSupportAmbientOpen_snd p1p1Fibres_transversal
```

(compiled in scratch App, inside `open AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLadder.Tests`). Ledger for that rung: `checked`, declaration `HodgeLadder.Tests.p1p1Fibres_cup_eq_p1p1Corner`, note stating that the identity is non-vacuous only once `p1p1-point-class-nonzero` is checked.

O2. **Coordinate-order test** in `HodgeLadder/Tests/P1p1Fibres.lean`, non-vacuity section (Probe P1, compiled):

```lean
/-- Coordinate `1` of the product chart does not cut out `{∞} × ℙ¹`: the order of `htr` is
visible. -/
theorem not_forall_mem_p1p1FibreFst_iff_coord_one : ¬ ∀ z ∈ p1p1Chart.source,
    (z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst ↔ p1p1Chart z 1 = 0) := by
  intro h
  have ht : (![1] : Fin 1 → ℂ) ∈ lineChart.target := by
    rw [lineChart, projectiveChart, affineChart_target]; trivial
  set b : ComplexPoint projectiveLine := lineChart.symm ![1]
  have hb1 : lineChart b 0 = 1 := by rw [show lineChart b = ![1] from lineChart.right_inv ht]; rfl
  set z : ComplexPoint p1p1 := prod.lift inftyPoint b
  have hfst : Point.map prod.fst z = inftyPoint := prod.lift_fst _ _
  have hsnd : Point.map prod.snd z = b := prod.lift_snd _ _
  have hz : z ∈ p1p1Chart.source := by
    rw [mem_p1p1Chart_source_iff, hfst, hsnd]; exact ⟨inftyPoint_mem_source, lineChart.map_target ht⟩
  have hmem : z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst := by
    rw [mem_p1p1FibreFst_support_iff_fst, hfst, inftyPoint_underlying]
  have := (h z hz).mp hmem
  rw [p1p1Chart_apply_one, hsnd, hb1] at this
  exact one_ne_zero this
```

(This exact text compiled in scratch `O2` inside `namespace HodgeLadder.Tests` with the module's `open` lines, standard axioms; the same file compiled O1 there too.)

O3. **Scheme-level cross-check of `hT`**, closure {p1p1FibreFst} ∩ closure {p1p1FibreSnd} = closure {p1p1Corner}, as on ℙ² (`closure_planeLine_inter`). It needs the fibre of ℙ¹ × ℙ¹ over (∞, ∞) or a Jacobson argument; better placed with `fibre-class-pullback`, which needs closure {p1p1FibreFst} = pr₁⁻¹{infty} at the scheme level anyway.

O4. Move `ker_eq_vanishingIdeal_of_isReduced` to a `HodgeLadder/General/` module at layer 0; the Tests placement follows the `P1p1Witness` precedent and is acceptable.

## What was tried and failed

- Trivial proofs T1 to T3 (section 3): all fail.
- Swapped coordinate indexing (Probe P1): false, as it should be.
- A Mathlib or upstream lemma equal to `ker_eq_vanishingIdeal_of_isReduced`: none public at the pin (search of `IdealSheaf/` for `ker` with `vanishingIdeal`, and of upstream); only upstream's private special case.
- A scheme-level `hT` in under ten lines: not attempted beyond identifying the missing fibre input (O3).
