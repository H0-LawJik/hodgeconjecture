# Red team: `local-class-pullback-submersion` (statement and proof)

Date: 2026-11-27. Candidate: commit `c6f03ad` on `track/local-class-pullback-submersion` (base `c901bbc`), `HodgeLadder/Local/ClassPullback.lean` (namespace `HodgeLadder.LocalClassPullback`, 7 declarations) and `HodgeLadder/Tests/P1p1FstPullback.lean` (16 declarations), both imported from `HodgeLadder.lean`. Ledger not yet updated; no sketch file. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same as `main` at `cf87c43`.

Read: the ledger entries `local-class-pullback-submersion`, `fibre-class-pullback`, `supported-class-pullback`, `supported-pullback-transport`, `local-class-product(-test)`, `p1p1-fibres-transversal`, `cycle-class-multiplicative-p1p1`, `cycle-class-germ`; `python3 tools/next.py` for this rung and for `fibre-class-pullback`; `docs/sketches/cycle-class-multiplicative.md` (sub-rungs table, finding 15); upstream `Definitions/AlgebraicTopology/LocalHomology/NormalProjectionCoclass.lean` and its `Lemmas` twin (`neighborhoodSupportInclusionPairMap`, `chartNormalProjectionPair`, `chartNormalProjectionCoclass`, `chartNormalProjectionCoclass_restrict`, `chartNormalProjectionCoclass_apply_normalClass`, `chartNormalProjectionCoclass_unique`), `Lemmas/AlgebraicGeometry/Cycle/Transport/CohomologySheaf.lean` (`complexSupportInjectiveSectionCohomologyEquiv`), `Other/AlgebraicGeometry/Cycle/FundamentalClass.lean` (`cycleComponentSupportedInjectiveClass_unique`); this repository's `HodgeLadder/Normalization/Germ.lean` (`transport_supportedClass_eq_chartNormalProjectionCoclass`, `chartNormalProjectionCoclass_pairImage`), `HodgeLadder/Normalization/GermNoReg.lean` (`_of_adapted`), `HodgeLadder/Local/ClassProduct.lean`, `HodgeLadder/Tests/P1p1Fibres.lean`, `HodgeLadder/Tests/CycleClassGermPoint.lean`; `docs/conventions.md` (rows "Complex orientation of ℂ^p", "Fundamental-class normalization", "Holomorphic adapted chart", "Complex points of a product and product charts", "Point ∞ of ℙ¹ and the fibres of ℙ¹ × ℙ¹", "Product of local classes"); `docs/gaps.md`; `docs/references.md`; decision 0012.

Scratch: five files in `scratch_rt/` inside the worktree, checked with `lake env lean` against the worktree build (oleans of both modules current with `c6f03ad`), then deleted. Nothing under `.lake/packages` was touched.

| File | Content | Result |
|---|---|---|
| Axioms | `#print axioms` on the 7 module declarations and 13 test declarations; trivial proofs (`rfl`, `simp`, `aesop`) of `chartNormalProjectionCoclass_pullback` with `hn` removed | standard axioms on all 20; all three trivial proofs fail |
| NonVac | the non-vacuity lemma of change R1 (exact text below), `#print axioms` on the 3 remaining test declarations | compiles; standard axioms on all 5 |
| Assembly | `cycle-class-germ` (no-reg form) on ℙ¹ with `lineAdaptedChart` and on ℙ¹ × ℙ¹ with `p1p1FstChart`, composed with `restrict_pullback_eq_chartNormalProjectionCoclass` at V = V' = ⊤ | compiles, standard axioms (finding 9) |
| Iso, Steps | elaboration bisection of the assembly | located the timeout in a `Set _` binder (finding 10) |
| Id | `neighborhoodSupportPullbackPairMap id` equals `neighborhoodSupportInclusionPairMap` | `rfl` |

`python3 tools/check.py --no-build` exits 0 on the branch. The new declarations are not yet named in the ledger, so the checker did not print their axioms; the scratch `#print axioms` covers all 23.

**Sign: +, exact, and no sign can enter.** Upstream's `chartNormalProjectionCoclass E c e S hS W hW` is by definition `relativeCohomologyMap ℚ (2 * c) (chartNormalProjectionPair E c e S hS W hW) u_c` with u_c = `normalizedRelativeCoclass (standardComplexLocalClass ℚ c) (standardComplexLocalClass_ne_zero_for_chart c)`. The target pair `puncturedPair ℂ c` and the class u_c depend on c alone: E, e, S and W do not occur in them. Both sides of the rung use the same c. Under `hn` the two maps of pairs into (ℂ^c, ℂ^c ∖ 0) are equal (`pullbackPairMap_comp_chartNormalProjectionPair`, checked pointwise by `ext`), so both sides are pullbacks of one class along one map. No −1 and no Koszul sign appears (the rung has no products). The coordinate swap of the ℙ¹ × ℙ¹ instance enters only as the ℂ-linear witness L of `cycle-class-germ`'s hypothesis `he`; L does not occur in any coclass (finding 4).

**Verdict: pass with changes.** The statement is the chart form of the naturality of the local Thom class under maps that are the identity on normal fibres, exact, at full strength (stronger than the ledger title: any continuous f, no holomorphy). The proof is short because upstream defines the chart coclass as a pullback; the content is the pair-map equality, which uses `hn` (finding 7). The pr₁ instance meets every hypothesis, and with `cycle-class-germ` it gives the local identity `fibre-class-pullback` needs, in scratch. Changes: one non-vacuity lemma, two docstring corrections on the swap, the posting records, and notes to the two consumer rungs.

## 1. Is this the statement the literature makes?

Source. [`MilnorStasheff1974`, Thom isomorphism chapter; section numbers unverified]: the Thom class u_ξ ∈ H^n(E, E ∖ 0) of an oriented n-plane bundle is natural under bundle maps that are orientation-preserving isomorphisms on fibres: for g : E' → E covering f with g an orientation-preserving isomorphism on each fibre, g^* u_ξ = u_{ξ'}. [`Bredon1993`, orientation and Thom class sections; numbering unverified]: the same naturality. For a submanifold S ⊂ M with tubular chart e : M ⊇ U → E × ℂ^c, S = {n = 0}, the local class of S on (U, U ∖ S) is the pullback of the Thom class of the trivial bundle ℂ^c along the normal projection. For f transverse to S, the normal bundle of f⁻¹ S is f^* of the normal bundle of S, and the local class of f⁻¹ S is f^* of the local class of S. In charts where f is the identity on normal coordinates this is the rung.

| Field | Literature | Lean | Match |
|---|---|---|---|
| ambient spaces | manifolds M, M′, f smooth and transverse to S | `M M' : Type` with topologies, `f : M' → M` continuous (`hf`) | Lean is more general: no smoothness, no transversality; transversality is replaced by `hn` |
| chart of the target | tubular chart of S in M, normal fibre ℂ^c | `e : OpenPartialHomeomorph M (E × (Fin c → ℂ))`, `hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0`, upstream's chart form (tangent first, normal second) | yes |
| chart of the source | tubular chart of f⁻¹ S in M′ | `e' : OpenPartialHomeomorph M' (E' × (Fin c → ℂ))`, `hS'`, same c | yes; equal codimension is forced by the shared c |
| f is the identity on normal fibres | f^* ν_S ≅ ν_{f⁻¹S} by the differential, orientation preserved | `hn : ∀ y ∈ W', (e (f y)).2 = (e' y).2`, literal equality of normal coordinates | yes, at full strength: equality of coordinates gives the fibre map id on ℂ^c, which preserves every orientation |
| preimage | f⁻¹ S ∩ W′ | `hSS : ∀ y ∈ W', f y ∈ S → y ∈ S'`; with `hS'` and `hn`, S′ ∩ W′ = f⁻¹ S ∩ W′ follows; `_preimage` takes S′ = f⁻¹ S | yes |
| local classes | Thom class pulled back along the normal projection, 1 on the complex orientation | upstream's `chartNormalProjectionCoclass` (u_c pulled back along `chartNormalProjectionPair`) | yes; u_c is 1 on upstream's complex orientation class (rows "Complex orientation of ℂ^p", "Fundamental-class normalization") |
| conclusion | f^* u_S = u_{f⁻¹S} in H^{2c}(W′, W′ ∖ f⁻¹S) | `relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportPullbackPairMap f hf hWW hSS) (coclass e on W) = coclass e' on W'` | yes, exact |

The ledger title says "holomorphic submersion written in charts as a coordinate projection". For a map (t″, t, n) ↦ (t, n) in charts, `hn` holds, so the Lean statement implies the title. The extra generality is harmless: the chart coclass depends only on the normal coordinate, and holomorphy is needed only where a chart coclass is identified with a cycle class (`cycle-class-germ`, on each side separately). The ledger note should say so (change R3).

`neighborhoodSupportPullbackPairMap` is the map of pairs given by f on both subspaces, built with Mathlib's `TopPair.ofHom` exactly as upstream builds `neighborhoodSupportInclusionPairMap`; at f = id it is that map by `rfl` (scratch file Id). `inclusion_comp_pullbackPairMap` holds by `rfl`.

## 2. Can the hypotheses be satisfied?

Yes, with both sides nonzero. The pr₁ instance `p1p1Fst_chartNormalProjectionCoclass_pullback` discharges `hS` (`lineAdaptedChart_adapted`), `hS'` (`mem_p1p1FibreFst_support_iff'`), `hSS` (`map_fst_mem_infty_support_iff`) and `hn` (`p1p1FstChart_apply_snd`) for every admissible (W, W′). The candidate's non-vacuity lemma `p1p1Fst_chartNormalProjectionCoclass_ne_zero` shows each chart coclass is nonzero on its own flattened neighbourhood; it does not exhibit one (W, W′) with `MapsTo pr₁ W' W` at which the identity is an equality of nonzero classes (the flattened neighbourhood of the corner need not map into that of ∞). The two chart sources are such a pair: `pr₁` maps `p1p1FstChart.source` into `lineAdaptedChart.source` (`mem_p1p1Chart_source_iff`), and the right side there restricts to the nonzero flattened-neighbourhood class. Change R1 adds this lemma; it compiles in scratch.

## 3. Trivially true?

No. With `hn` removed, `rfl`, `simp` and `aesop` fail (scratch file Axioms), and the statement without `hn` is false in general: replacing the normal coordinate of e′ by its complex conjugate keeps `hS'` and multiplies the right side by (−1)^c (row "Holomorphic adapted chart"; not re-derived in Lean here, since it needs a degree computation the rung does not use). The three-line proof uses `hn` in `pullbackPairMap_comp_chartNormalProjectionPair`; the remaining hypotheses type the pair maps. No definition unfolds to `True`, no index type is empty (c = 1 in the instance), no `ℕ∞` coercion occurs (degree `2 * c : ℕ`).

## 4. Sign, the coordinate swap and the holomorphy hypothesis

1. Upstream's chart convention E × ℂ^c holds on both sides: `chartNormalProjectionPair` reads `(e w.1).2`, and `p1p1FstChart`, `lineAdaptedChart` both have values in `(Fin k → ℂ) × (Fin 1 → ℂ)`. The statement contains no reordering.
2. `fstSplit` sends v ↦ ((v 1), (v 0)): tangent block the second factor's coordinate x₁/x₀ ∘ pr₂, normal block the first's, x₁/x₀ ∘ pr₁. The normal block matches `p1p1Chart_apply_zero` and `mem_p1p1FibreFst_support_iff` ({∞} × ℙ¹ = {v₀ = 0}). Checked from source.
3. `cycle-class-germ`'s hypothesis is `L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ)` with `he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈ maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω`. Its conclusion names `chartNormalProjectionCoclass E p e …` alone, so the identity holds for every e admitting some such L, and L does not occur in it. An orientation-reversing real map cannot be L: L is ℂ-linear for the Pi structures on `Fin k → ℂ` (the instance used for E = `Fin 0 → ℂ`, `Fin 1 → ℂ`), with real determinant |det_ℂ L|² > 0. For the instance, L = `fstSplit.symm` and `p1p1FstChart_holomorphic` is `he` up to the `dim` substitution of finding 10.
4. The candidate's docstrings say the split "leaves the chart coclass unchanged" and cite the real determinant (−1)^{(2a)(2b)} = 1. Both statements are true and neither describes the proof: no two chart coclasses are compared in this rung, and the determinant is irrelevant because L does not occur in a coclass. Change R2 replaces the text.
5. A conjugated normal coordinate in e′ (the only odd-sign hazard in row "Holomorphic adapted chart") is excluded twice: it breaks `hn`, and it breaks `he` for e′.

Nothing other than +1 is forced, and no −1 appears.

## 5. Checked rung: axioms and names

Standard axioms (`propext`, `Classical.choice`, `Quot.sound`) on all 7 module declarations and all 16 test declarations, by `#print axioms` in scratch. The checker passes on the branch. The ledger's suggested path `HodgeLadder/Local/Class/Pullback/Submersion.lean` is `tools/next.py`'s default for a rung without a module; `HodgeLadder.Local.ClassPullback` sits beside `HodgeLadder.Local.ClassProduct` and is the better name. The ledger must set `module` explicitly (change R3).

## 6. Conventions

| Convention | Where | Truth of this rung depends on it? |
|---|---|---|
| chart form E × ℂ^c, normal block second | upstream `chartNormalProjectionPair`; row "Holomorphic adapted chart" | no: the rung holds for any chart of that form; the consumer needs both charts in it |
| u_c = `normalizedRelativeCoclass (standardComplexLocalClass ℚ c) _` | rows "Complex orientation of ℂ^p", "Fundamental-class normalization" | no: the same class sits on both sides, so any orientation convention gives a true identity; the consumer's sign comes from `cycle-class-germ` on each side |
| `relativeCohomologyMap` contravariant, `relativeCohomologyMap_comp` for `f ≫ g` | upstream | no sign |
| normal coordinates tied literally (`hn`), no conjugation, no scalar | this rung | yes: a conjugate costs (−1)^c, a scalar λ ≠ 0 on ℂ^c costs nothing (ℂ-linear), a real reflection costs −1; `hn` excludes all three |
| ∞ = [1 : 0], `lineChart` coordinate x₁/x₀ | row "Point ∞ of ℙ¹ and the fibres of ℙ¹ × ℙ¹" | instance only; any closed point gives the same statement |
| product chart, first factor first; `fstSplit` order (v₁ | v₀) | row "Complex points of a product and product charts"; this rung | instance only; the order enters only through `he` |

Missing row: the rung itself. Change R5 adds row "Pullback of local classes along a chart projection".

## 7. Equality first

The rung is an identity, proved exactly: an equality of classes in H^{2c}(W′, W′ ∖ S′; ℚ), no scalar, sign +. It is a step toward the identity `pullbackCoh f [Z] = [f⁻¹ Z]` of rung `fibre-class-pullback` (open), first use pr₁*[∞] = [{∞} × ℙ¹] in `cup-positive-degree-test` (open).

## 7b. Non-vacuity

Smallest test that fails if the identity were 0 = 0: the instance at one admissible pair with a nonzero side. At the pin the ingredients exist: `HodgeLadder.Tests.p1p1Fst_chartNormalProjectionCoclass_ne_zero` (flattened neighbourhoods, through upstream's `chartNormalProjectionCoclass_apply_normalClass`), upstream's `chartNormalProjectionCoclass_restrict`, and `HodgeLadder.Tests.mem_p1p1Chart_source_iff`. The combined lemma is missing; change R1 adds it (`p1p1Fst_chartNormalProjectionCoclass_pullback_source_ne_zero`). Since the right side is nonzero over ℚ, the identity also separates + from −.

## 8. Pin drift

No drift. The branch was built against `2ead713`, the pin of `main` at `cf87c43`; `main` changed no pin file since the branch base `c901bbc`. Upstream definitions the rung unfolds: `chartNormalProjectionCoclass`, `chartNormalProjectionPair`, `neighborhoodSupportComplementPair`, `neighborhoodSupportInclusionPairMap`, `puncturedPair`; the proof `unfold`s the coclass and rewrites with `relativeCohomologyMap_comp`, so a change of either definition breaks the build. `chartNormalProjectionCoclass` has no `rfl` pin in `HodgeLadder/CycleClass/Pins.lean` (optional O1). `main` added two imports at the end of `HodgeLadder.lean` and edited `ledger/ladder.json`, `docs/gaps.md`, `docs/conventions.md`; the branch needs a rebase before merge (change R9).

## Findings

1. Statement is the chart form of the naturality of the Thom class [`MilnorStasheff1974`; `Bredon1993`; numbering unverified], exact, stronger than the ledger title (any continuous f, no holomorphy).
2. Sign + is structural: both sides pull back the single class u_c along equal maps of pairs; no convention for u_c can change the identity.
3. The coordinate swap `fstSplit` enters only as L = `fstSplit.symm` in `he` of `cycle-class-germ`; L is ℂ-linear, so orientation-preserving, and absent from every coclass. The docstrings misdescribe this (R2).
4. `hn` is load-bearing: trivial proofs without it fail, and without it a conjugated normal coordinate gives (−1)^c.
5. Hypotheses are satisfiable on ℙ¹ × ℙ¹; a single-instance non-vacuity lemma is missing (R1).
6. Standard axioms on all 23 declarations; checker passes; module placement is right, the ledger must name it.
7. Brevity: the proof is three rewrites because upstream defines the coclass as a pullback. The content is `pullbackPairMap_comp_chartNormalProjectionPair` (two `ext` goals closed by `hn`), honest and complete. The rung's weight for `fibre-class-pullback` is in `cycle-class-germ` and in the two open sub-rungs.
8. `restrict_pullback_eq_chartNormalProjectionCoclass` has the shape `fibre-class-pullback` needs: at V = V′ = ⊤ its α is the restriction hypothesis `cycle-class-germ` produces, verbatim.
9. Assembly in scratch: for every y′ ∈ `p1p1FstChart.source` there is W′ ∋ y′ on which the restriction of `relativeCohomologyMap (pr₁ pair at ⊤) (T [∞])` equals the restriction of `T [{∞} × ℙ¹]`, T upstream's transport `complexSupportInjectiveSectionCohomologyEquiv … ⊤ (2 * 1)` of the supported class. Inputs: `transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted` on each side (no smooth-locus hypothesis), this rung's restricted form, upstream's `chartNormalProjectionCoclass_restrict`. Standard axioms.
10. Elaboration hazards for the consumer: `cycle-class-germ` states `he` over `Fin (dim X.left) → ℂ`, while `lineAdaptedChart_holomorphic` and `p1p1FstChart_holomorphic` use `Fin 1`, `Fin 2`; a five-line wrapper generalized over `d` with `obtain rfl := SmoothOfRelativeDimension.dim_eq (f := X.hom) d` bridges it (O3). A binder `W' ⊆ ((⊤ : Opens (ComplexPoint p1p1)) : Set _)` with `Set _` unresolved ran past 1000000 heartbeats; writing `Set (ComplexPoint p1p1)` and passing the restricted lemma's arguments by name elaborated in under a minute.
11. What remains for `fibre-class-pullback` at pr₁: (a) `supported-class-pullback`; (b) `supported-pullback-transport`, stated with `neighborhoodSupportPullbackPairMap` at the evaluation open ⊤ on both sides so that finding 9 composes by term; (c) a second chart pair: `p1p1FstChart.source` meets {∞} × ℙ¹ in {∞} × (ℙ¹ ∖ {[0 : 1]}) (`mem_p1p1Chart_source_iff`), so the point (∞, [0 : 1]) needs `lineAdaptedChart` with a product chart using x₀/x₁ on the second factor (for example `p1p1StdChart 0 1` of `p1p1-point-class-nonzero`) split like `fstSplit`; (d) germs to sections: equal restrictions near every point of {∞} × ℙ¹ and zero germs off it give equal normalized sections on Y ∖ T_sing = Y (the fibre is smooth, `smooth_cycleComponentι_p1p1FibreFst`), then `cycleComponentSupportedInjectiveClass_unique` with `normalization-singular`, then `forgetSupport` through (a). For a general smooth f, (c) needs charts e′ with (e′ ·).2 = (e ·).2 ∘ f, a holomorphic submersion normal form; whether Mathlib's implicit function theorem gives an analytic chart at the pin is unverified. Decision 0010 needs only pr₁.
12. Placement and records: gaps row for the 7 general declarations under "Local cohomology, orientation and the cycle class", layer 0 by `python3 tools/pinwalk.py` (R6); the test file is layer 9 and holds instance lemmas only, no gaps row.

## Required changes

**R1. Non-vacuity at one admissible pair.** Append to `HodgeLadder/Tests/P1p1FstPullback.lean`, before `end HodgeLadder.Tests`, and add both to the module docstring's main results (checked in scratch, standard axioms):

```lean
/-- `pr₁` maps the source of `p1p1FstChart` into the source of `lineAdaptedChart`. -/
theorem mapsTo_fst_p1p1FstChart_source :
    Set.MapsTo (Point.map prod.fst) p1p1FstChart.source lineAdaptedChart.source := by
  intro z hz
  rw [p1p1FstChart_source, mem_p1p1Chart_source_iff] at hz
  rw [lineAdaptedChart_source]
  exact hz.1

/-- Non-vacuity of `p1p1Fst_chartNormalProjectionCoclass_pullback` at one admissible pair, the two
chart sources: the pullback along `pr₁` of the chart coclass of `{∞}` is nonzero, so the identity
there is an equality of nonzero classes and separates `+` from `-` over `ℚ`. -/
theorem p1p1Fst_chartNormalProjectionCoclass_pullback_source_ne_zero :
    relativeCohomologyMap ℚ (2 * 1)
        (neighborhoodSupportPullbackPairMap (Point.map prod.fst) (Point.continuous_map _)
          mapsTo_fst_p1p1FstChart_source (fun z _ h => (map_fst_mem_infty_support_iff z).mp h))
        (chartNormalProjectionCoclass (Fin 0 → ℂ) 1 lineAdaptedChart
          (cycleComponentAnalyticClosedSupport projectiveLine infty) lineAdaptedChart_adapted
          lineAdaptedChart.source subset_rfl) ≠ 0 := by
  rw [p1p1Fst_chartNormalProjectionCoclass_pullback (hW' := subset_rfl)]
  intro hz
  apply p1p1Fst_chartNormalProjectionCoclass_ne_zero.1
  rw [← chartNormalProjectionCoclass_restrict (Fin 1 → ℂ) 1 p1p1FstChart _
    mem_p1p1FibreFst_support_iff' (flattenedSupportNeighborhood_subset_source _ _ _ _ _) subset_rfl,
    hz, map_zero]
```

**R2. Docstrings on the swap.**

(a) In `HodgeLadder/Local/ClassPullback.lean`, module docstring, paragraph "Signs.", replace the sentence beginning "A reordering appears only when" through "`(-1)^{(2a)(2b)} = 1`)." with:

> A reordering appears only when a chart in the maximal atlas, with values in `ℂ^d`, is split into tangent and normal blocks to produce `e` or `e'`. The split enters through the holomorphy hypothesis `he` of `cycle-class-germ` alone, as its `ℂ`-linear witness `L`; the chart coclass reads only the normal coordinate `(e ·).2`, so `L` does not occur in it, and this theorem assumes no holomorphy (row "Pullback of local classes along a chart projection" of `docs/conventions.md`).

(b) In `HodgeLadder/Tests/P1p1FstPullback.lean`, module docstring, replace "The reordering `fstSplit` is `ℂ`-linear, so it costs no sign (row "Holomorphic adapted chart" of `docs/conventions.md`; real determinant `(-1)^{(2·1)(2·1)} = 1`)." with:

> `fstSplit` enters only as the witness `L = fstSplit.symm` of hypothesis `he` of `cycle-class-germ`; the coclass of `p1p1FstChart` reads only its normal coordinate, which is `lineChart ∘ pr₁` (`p1p1FstChart_apply_snd`), so the reordering contributes no sign (row "Pullback of local classes along a chart projection" of `docs/conventions.md`). `cycle-class-germ` states `he` over `Fin (dim X.left) → ℂ`; these lemmas state it over `Fin 1 → ℂ` and `Fin 2 → ℂ`, and feed it after `obtain rfl := SmoothOfRelativeDimension.dim_eq (f := X.hom) d` in a statement generalized over `d`.

and in the same docstring's main results, replace "the hypotheses `he`, `hy` of `cycle-class-germ` for the two charts" with "the hypotheses `he` (up to the `dim` substitution above) and `hy` of `cycle-class-germ` for the two charts".

**R3. Ledger entry `local-class-pullback-submersion`.** Status `checked`, kind `foundation`, `module` `HodgeLadder.Local.ClassPullback`, `depends_on` `[]`, contributors `claude-code`, declarations:

`HodgeLadder.LocalClassPullback.neighborhoodSupportPullbackPairMap`, `HodgeLadder.LocalClassPullback.inclusion_comp_pullbackPairMap`, `HodgeLadder.LocalClassPullback.pullbackPairMap_comp_chartNormalProjectionPair`, `HodgeLadder.LocalClassPullback.chartNormalProjectionCoclass_pullback`, `HodgeLadder.LocalClassPullback.chartNormalProjectionCoclass_pullback_preimage`, `HodgeLadder.LocalClassPullback.restrict_pullback_eq_chartNormalProjectionCoclass`, `HodgeLadder.LocalClassPullback.chartNormalProjectionCoclass_flattened_ne_zero`.

Note, verbatim:

> Checked 2026-11-27. Exact, sign +, no scalar. Chart form, stronger than the title: for any continuous f : M′ → M, charts e of M and e′ of M′ in upstream's E × ℂ^c form (normal block second, the same c), adapted to S and S′ (hS, hS′), f mapping W′ ⊆ e′.source into W ⊆ e.source with f⁻¹ S ∩ W′ ⊆ S′ (hSS) and (e (f y)).2 = (e′ y).2 on W′ (hn), the pullback along the map of pairs neighborhoodSupportPullbackPairMap of chartNormalProjectionCoclass of e on W is chartNormalProjectionCoclass of e′ on W′. No holomorphy is assumed; a submersion written in charts as a coordinate projection satisfies hn. Proof: the two normal projections agree as maps of pairs (pullbackPairMap_comp_chartNormalProjectionPair, from hn), and both coclasses pull back the same class u_c of (ℂ^c, ℂ^c ∖ 0) (relativeCohomologyMap_comp), so no sign can enter. Restricted form restrict_pullback_eq_chartNormalProjectionCoclass is the shape fibre-class-pullback consumes at V = V′ = ⊤ (red team scratch: composed with cycle-class-germ on ℙ¹ and ℙ¹ × ℙ¹). Literature: naturality of the Thom class under maps that are orientation-preserving isomorphisms on fibres [MilnorStasheff1974; Bredon1993; numbering unverified]. Register row Pullback of local classes along a chart projection. Tests: local-class-pullback-submersion-p1p1. Red team: pass with changes (docs/sketches/local-class-pullback-submersion.redteam.md).

**R4. Test rung `local-class-pullback-submersion-p1p1`.** New ledger entry, status `checked`, kind `test`, module `HodgeLadder.Tests.P1p1FstPullback`, `depends_on` `["local-class-pullback-submersion", "p1p1-fibres-transversal"]`, contributors `claude-code`. Title: "The pullback along pr₁ : ℙ¹ × ℙ¹ → ℙ¹ of the chart coclass of ∞ in the chart x₀ ≠ 0 is the chart coclass of {∞} × ℙ¹ in the product chart split with the first factor's coordinate as normal block; both charts holomorphic in the sense of cycle-class-germ; both sides nonzero at the two chart sources". Declarations: the 16 of the file (`HodgeLadder.Tests.lineAdaptedChart`, `lineAdaptedChart_source`, `lineAdaptedChart_apply_snd`, `fstSplit`, `p1p1FstChart`, `p1p1FstChart_source`, `p1p1FstChart_apply_snd`, `mem_infty_support_iff`, `lineAdaptedChart_adapted`, `map_fst_mem_infty_support_iff`, `mem_p1p1FibreFst_support_iff'`, `p1p1Fst_chartNormalProjectionCoclass_pullback`, `lineAdaptedChart_holomorphic`, `p1p1FstChart_holomorphic`, `p1p1CornerPoint_mem_p1p1FstChart_source`, `p1p1Fst_chartNormalProjectionCoclass_ne_zero`, each with the `HodgeLadder.Tests.` prefix) and the two of R1. Note:

> Checked 2026-11-27. Instance of local-class-pullback-submersion at pr₁, the first use named by fibre-class-pullback. e = lineAdaptedChart (lineChart with an empty tangent block, ℂ^0 × ℂ^1), e′ = p1p1FstChart = p1p1Chart followed by fstSplit (v₀, v₁) ↦ ((v₁), (v₀)): tangent block the second factor's coordinate, normal block the first's; hn is p1p1FstChart_apply_snd. fstSplit enters cycle-class-germ only as L = fstSplit.symm in he; it does not occur in either coclass. Non-vacuity: p1p1Fst_chartNormalProjectionCoclass_pullback_source_ne_zero (both sides nonzero at W = lineAdaptedChart.source, W′ = p1p1FstChart.source). The product chart misses (∞, [0 : 1]); fibre-class-pullback needs a second chart pair there. Red team: docs/sketches/local-class-pullback-submersion.redteam.md.

**R5. Register row.** Add to `docs/conventions.md`, after row "Product of local classes (model and chart)":

> | Pullback of local classes along a chart projection | this repository, `HodgeLadder.LocalClassPullback.chartNormalProjectionCoclass_pullback`, `restrict_pullback_eq_chartNormalProjectionCoclass`, `neighborhoodSupportPullbackPairMap` (`HodgeLadder/Local/ClassPullback.lean`, rung `local-class-pullback-submersion`); instance `HodgeLadder.Tests.p1p1Fst_chartNormalProjectionCoclass_pullback` (`HodgeLadder/Tests/P1p1FstPullback.lean`, rung `local-class-pullback-submersion-p1p1`); upstream `chartNormalProjectionPair`, `chartNormalProjectionCoclass`, `relativeCohomologyMap_comp` | both charts in upstream's form E × ℂ^c, tangent block first, normal block second, the same c on both sides; `hn`: (e (f y)).2 = (e′ y).2 on W′, the normal coordinates equal as functions (no conjugation, no reordering, no scalar); the map of pairs (W′, W′ ∖ S′) → (W, W ∖ S) is f on points. Both coclasses pull back the one class u_c = `normalizedRelativeCoclass (standardComplexLocalClass ℚ c) _` of (ℂ^c, ℂ^c ∖ 0), which depends on c alone, so f^*(coclass of e) = coclass of e′, sign +, exact, for every continuous f; no holomorphy assumed. ℙ¹ × ℙ¹ instance: e = `lineAdaptedChart` (ℂ^0 × ℂ^1, normal coordinate x₁/x₀), e′ = `p1p1FstChart` = `p1p1Chart` then `fstSplit` (v₀, v₁) ↦ ((v₁), (v₀)), tangent block the second factor's coordinate, normal block the first's; `hn` is `p1p1FstChart_apply_snd`. `fstSplit` enters only through `he` of `cycle-class-germ`, as L = `fstSplit.symm`, ℂ-linear, and occurs in neither coclass | `local-class-pullback-submersion`; `fibre-class-pullback` (pr₁*[∞] = [{∞} × ℙ¹]). The identity holds under every convention for u_c, since one class sits on both sides; the consumer's sign comes from `cycle-class-germ` on each side (rows "Holomorphic adapted chart", "Complex orientation of ℂ^p", "Fundamental-class normalization"). A conjugated normal coordinate in e′ would cost (−1)^c; it breaks `hn` and `he` | read from source; checked in scratch (red team 2026-11-27, `docs/sketches/local-class-pullback-submersion.redteam.md`): standard axioms on all 23 declarations; composed with `cycle-class-germ` on ℙ¹ and on ℙ¹ × ℙ¹ |

**R6. Gaps row.** Add to `docs/gaps.md`, category "Local cohomology, orientation and the cycle class", after the `HodgeLadder.General.LocalOrientation` row (both layer 0):

> | `HodgeLadder.LocalClassPullback.neighborhoodSupportPullbackPairMap` (the map of pairs (W′, W′ ∖ S′) → (W, W ∖ S) of a continuous f), `inclusion_comp_pullbackPairMap`, `pullbackPairMap_comp_chartNormalProjectionPair`, `chartNormalProjectionCoclass_pullback`, `chartNormalProjectionCoclass_pullback_preimage`, `restrict_pullback_eq_chartNormalProjectionCoclass`, `chartNormalProjectionCoclass_flattened_ne_zero` (upstream's chart coclass is natural under any continuous map that ties the normal coordinates; any spaces) | `HodgeLadder.Local.ClassPullback` | 0 | general statements about upstream's `chartNormalProjectionPair` and `chartNormalProjectionCoclass`, next to upstream's `neighborhoodSupportInclusionPairMap` and `chartNormalProjectionCoclass_restrict`; the pin pulls the coclass back only along inclusions (the open-embedding case is this repository's `chartNormalProjectionCoclass_pairImage`) | 2026-11-27 |

**R7. Consumer notes.** Append to the ledger note of `supported-pullback-transport`:

> State the map of pairs as HodgeLadder.LocalClassPullback.neighborhoodSupportPullbackPairMap (Point.map f) (Point.continuous_map _) with W′ := ((⊤ : Opens (ComplexPoint Y)) : Set (ComplexPoint Y)), W := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X)), hWW := fun _ _ => trivial, against complexSupportInjectiveSectionCohomologyEquiv at ⊤ on both sides, so that restrict_pullback_eq_chartNormalProjectionCoclass applies by term (red team of local-class-pullback-submersion, finding 11).

Append to the ledger note of `fibre-class-pullback`:

> local-class-pullback-submersion checked 2026-11-27 (chart form, any continuous f with tied normal coordinates). Red team finding 11: the local identity at pr₁ composes in scratch from cycle-class-germ (no-reg form) on ℙ¹ and on ℙ¹ × ℙ¹ and restrict_pullback_eq_chartNormalProjectionCoclass at ⊤. Remaining at pr₁: supported-class-pullback; supported-pullback-transport in the pair-map spelling above; a second chart pair at (∞, [0 : 1]), which p1p1FstChart misses; germs to sections on Y ∖ T_sing = Y, then cycleComponentSupportedInjectiveClass_unique and forgetSupport. A general smooth f also needs charts e′ with (e′ ·).2 = (e ·).2 ∘ f (holomorphic submersion normal form; unverified at the pin).

**R8. Roadmap.** In `docs/roadmap.md`, row `local-class-pullback-submersion`: status `checked`, description "chart coclasses pull back along any continuous map tying the normal coordinates, sign +, exact; `HodgeLadder.Local.ClassPullback`". Add a row `local-class-pullback-submersion-p1p1` | test | checked | `local-class-pullback-submersion`, `p1p1-fibres-transversal` | "pr₁*(coclass of ∞) = coclass of {∞} × ℙ¹ in adapted holomorphic charts, both sides nonzero; `HodgeLadder.Tests.P1p1FstPullback`".

**R9. Rebase.** Rebase onto `main` (`cf87c43`) before merge: `HodgeLadder.lean` gained two imports at the same tail, and `ledger/ladder.json`, `docs/gaps.md`, `docs/conventions.md` changed. Re-run `python3 tools/check.py` after the rebase.

## Optional

- O1. Pin the definition in `HodgeLadder/CycleClass/Pins.lean`: `chartNormalProjectionCoclass E c e S hS W hW = relativeCohomologyMap ℚ (2 * c) (chartNormalProjectionPair E c e S hS W hW) (normalizedRelativeCoclass (standardComplexLocalClass ℚ c) (standardComplexLocalClass_ne_zero_for_chart c)) := rfl`. The rung already breaks loudly on drift through `unfold`; the pin records the convention next to the others.
- O2. Add `r"[Pp]ullbackPairMap|chartNormalProjectionCoclass_pullback"` to the phrase list of "Local cohomology, orientation and the cycle class" in `tools/pinwalk.py`.
- O3. For `fibre-class-pullback`, the `dim` wrapper used in scratch (standard axioms):

```lean
theorem germ_d (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {d : ℕ} [SmoothOfRelativeDimension d X.hom] (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin d → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0)
    (y : ComplexPoint X) (hy : y ∈ e.source) : <conclusion of
      transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted> := by
  obtain rfl := SmoothOfRelativeDimension.dim_eq (f := X.hom) d
  exact transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted X x hx e L he hS y hy
```

## Attempts that failed or were set aside

- Trivial proofs of the main identity without `hn`: `rfl`, `simp`, `aesop` all fail.
- A Lean counterexample without `hn` (conjugated normal coordinate, factor −1 at c = 1) was set aside: it needs a degree computation on (ℂ, ℂ ∖ 0) that no checked lemma supplies directly; the (−1)^c is recorded in row "Holomorphic adapted chart".
- The first three assembly drafts timed out (200000 to 1000000 heartbeats). Bisection placed the fault in an unresolved `Set _` in a binder typing the pair; with explicit types and named arguments the assembly elaborates and checks.
