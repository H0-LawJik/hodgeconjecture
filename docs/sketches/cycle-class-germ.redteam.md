# Red team: `cycle-class-germ` (statement)

Date: 2026-11-26. Branch `track/cycle-class-germ`, base `7240569`, uncommitted `HodgeLadder/Normalization/Germ.lean` and the section "cycle-class-germ: statement" of `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Statement pass, before the proof.

Targets: the rung `transport_supportedClass_eq_chartNormalProjectionCoclass` (sorry), the chart step `lift_mem_maximalAtlas_openScheme` (sorry) and its instance `lift_mem_maximalAtlas_smoothSupportAmbient`, and the five proved helpers.

Read at the pin: `Definitions/AlgebraicTopology/LocalHomology/NormalProjectionCoclass.lean`, `Definitions/AlgebraicTopology/LocalHomology/ComplexClass.lean`, `Lemmas/AlgebraicTopology/LocalHomology/NormalProjectionCoclass.lean`, `Lemmas/AlgebraicTopology/LocalHomology/NormalProjectionOverlap.lean`, `Lemmas/AlgebraicGeometry/ComplexPoint/Manifold.lean`, `Definitions/AlgebraicGeometry/ClosedImmersion/HolomorphicCharts.lean` and its `Lemmas` twin, `Definitions/AlgebraicGeometry/Cycle/SmoothPair/CoclassSection.lean`, `Definitions/AlgebraicGeometry/Cycle/Component/SmoothSupportCoclassSection.lean`, `Lemmas/AlgebraicGeometry/Smooth/Equidimensional.lean`, and in `Other`: `AlgebraicTopology/Support/RelativeCohomologyGerm.lean`, `AlgebraicGeometry/Cycle/Component/PointBoundary.lean`, `AlgebraicGeometry/Cycle/Component/PointClassNormalization.lean`, `AlgebraicGeometry/Cycle/Component/BorelMoore.lean`, `AlgebraicGeometry/ComplexPoint/ClosedImmersion.lean`; Mathlib `Geometry/Manifold/HasGroupoid.lean`, `IsManifold/Basic.lean`, `Topology/OpenPartialHomeomorph/Constructions.lean` (`lift_openEmbedding`).

Scratch files (inside the worktree, deleted afterwards):

| File | What | Result |
|---|---|---|
| RT1 | `Germ.lean` with `#print axioms` for every declaration | compiles in 32 s; the five helpers use `propext`, `Classical.choice`, `Quot.sound`; the rung and `lift_mem_maximalAtlas_smoothSupportAmbient` add `sorryAx` (from the two open bodies) |
| RT2 | all four chart hypotheses met in positive codimension, on every X, at every complex point (section 2) | compiles, standard axioms |
| RT3 | germ equality is the `∃ W` form, for any two classes on any two opens (section 3) | compiles, standard axioms |
| RT4 | four trivial proofs of the rung | all fail (section 3) |
| RT5 | `chartAt = localChart X (dim X.left)` by `rfl`; a chart of the maximal atlas for a bound `{d} [SmoothOfRelativeDimension d X.hom]` transfers to `dim X.left` by `obtain rfl := SmoothOfRelativeDimension.dim_eq (f := X.hom) d` | both compile |
| RT6 | the second instance argument of the chart step | `smoothOfRelativeDimension_comp 0 d U.ι X.hom` then `simpa` proves it for every U; `inferInstance` fails, so the argument is needed as written |
| RT7 | `chartNormalProjectionCoclass_germ_ne_zero` (section 7b) | compiles, standard axioms |

`python3 tools/check.py --no-build` in the worktree: every checked rung ACCEPTED; REJECTED on the sorry scan at `Germ.lean:73` and `Germ.lean:213`. The scan covers every file in the tree, so `Germ.lean` cannot reach `main` until both bodies are proved (finding 9).

**Verdict: pass with changes.** The statement is the literature's local description of the cycle class at full strength, exact, with the sign fixed by the complex orientation and protected by the holomorphy hypothesis `he`. It is true, satisfiable in positive codimension at the pin, and not provable by a trivial argument. The changes add the positive-codimension witness and a germ non-vacuity lemma, cite the convention rows in the docstring, correct two sentences of the sketch, and record the redundancy of `hyU` as a stronger rung. None changes the statement.

## 1. Is this the statement the literature makes?

Literature. For a closed subvariety Z of codimension p of a complex manifold X and a point y of Z_reg, the class of Z in H^{2p}_Z(X) restricts near y to the Thom class of the normal bundle with its complex orientation: in holomorphic coordinates (t, n) ∈ ℂ^{d−p} × ℂ^p with Z = {n = 0}, it is the pullback along n of the generator of H^{2p}(ℂ^p, ℂ^p ∖ 0) that pairs to 1 with the orientation class of ℂ^p ordered (v₁, iv₁, …, v_p, iv_p) [`Fulton1998` ch. 19, `Iversen1986`, `Bredon1997`, `MilnorStasheff1974`; chapter and section numbers unverified]. The local class at a smooth point has multiplicity one because Z is reduced. In even real degree the sign choices that separate Thom-class and Poincaré-dual conventions, of the form (−1)^{k(n−k)} with k = 2p, are all +1.

Field by field:

| Literature | Lean | Source | Match |
|---|---|---|---|
| X smooth projective integral over ℂ, X(ℂ) a complex manifold of dimension d | `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`; charted space `localChart X (dim X.left)`, `isManifold_omega` | upstream `Lemmas/AlgebraicGeometry/ComplexPoint/Manifold.lean` | yes; RT5 confirms `chartAt` is `localChart X (dim X.left)` by `rfl` |
| Z of codimension p, as a set | `cycleComponentAnalyticClosedSupport X x` = `Point.underlying ⁻¹' closure {x}`, `hx : Order.coheight x = p` | upstream `Definitions` | yes |
| [Z] ∈ H^{2p}_Z(X; ℚ) as a relative class on (X, X ∖ Z) | `complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ (2p) (rationalSupportAddEquivSupportedInjectiveHomology X Z (2p) [Z])` | upstream `Lemmas`; the ladder's Φ by `supported-model-agreement` | yes, the form `normalization_singular` uses |
| holomorphic coordinates near y | `e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ))`, `L`, `he : e ≫ L ∈ maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω` | Mathlib | yes (section 6): ω over ℂ is analytic, and Mathlib's `ContDiffWithinAt` at ω requires analytic Taylor coefficients |
| Z = {n = 0} in the chart | `hS : ∀ z ∈ e.source, z ∈ Z ↔ (e z).2 = 0` | the predicate upstream's `chartNormalProjectionCoclass` takes | yes |
| y ∈ Z_reg | `hy : y ∈ e.source`, `hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x`; y ∉ Z allowed | upstream `Definitions` | weaker than the literature by `hyU` only; see 1a |
| Thom class pulled back along n | `chartNormalProjectionCoclass E p e Z hS W hW` = pullback along `w ↦ (e w).2` of `normalizedRelativeCoclass (standardComplexLocalClass ℚ p)` | upstream `Definitions/AlgebraicTopology/LocalHomology/NormalProjectionCoclass.lean:54` | yes; orientation consecutive (Re, Im), normalized to pair to 1 |
| equality of germs at y | `∃ W ⊆ e.source, y ∈ W ∧ restriction = chart coclass` | | equivalent (RT3, section 3) |

1a. `hyU` is an honest extra hypothesis. For y ∉ Z it holds automatically, since Z_sing ⊆ Z. For y ∈ Z it follows from `he` and `hS`: the reduced germ of Z at y is a complex submanifold, the analytic and algebraic local rings of the reduced closure have the same completion, so the scheme-theoretic closure is regular at y. That implication is not at the pin. The statement with `hyU` is formally weaker than the literature's and equivalent in truth. It does not weaken the use in `cycle-class-multiplicative`, whose `hxreg`, `hwreg` give y ∈ U at every point of T, the only points where step 5 of that plan needs a germ of [Z]. Recorded as a stronger rung (change G).

1b. Full strength. The rung quantifies over every holomorphic adapted chart, every tangential factor E and every y. The germ form is what step 5 of `cycle-class-multiplicative` consumes. The equality on all of e.source ∩ U (one open, no shrinking) follows from the germ form by purity below degree 2p, which upstream uses for N; it is a corollary, and no rung needs it yet.

## 2. Can the hypotheses be satisfied?

The sketch's witness `adaptedChart_genericPoint` meets `he`, `hS`, `hy` at p = 0 and leaves `hyU`, which needs a lemma missing at the pin. RT2 meets all four in positive codimension with what the pin has, on every X and at every complex point y₀: x = the closed point under y₀, p = dim X, E = ℂ⁰, e = `chartAt y₀`, translated so that y₀ goes to 0, followed by the inverse of `ContinuousLinearEquiv.uniqueProd`. Z is {y₀}; `hyU` holds because U = ⊤ for a component of maximal codimension (`cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension`, `Other`). On ℙ¹ this is p = 1 at any complex point.

With upstream's affine chart of ℙ¹ in place of `chartAt`, `he` needs `affine-chart-analytic`: nothing at the pin relates `complInftyHomeomorph` or `affineSpaceHomeomorph` to the maximal atlas. The translated `localChart` avoids that rung. Text (compiles with `HodgeLadder.Normalization.Singular`, `Other.AlgebraicGeometry.Cycle.Component.PointBoundary`, `Other.AlgebraicGeometry.ComplexPoint.ClosedImmersion`, `Mathlib.AlgebraicGeometry.AlgClosed.Basic`, `Mathlib.Analysis.Complex.Polynomial.Basic`; standard axioms):

```lean
theorem translate_mem {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (v : F) :
    (Homeomorph.addRight v).toOpenPartialHomeomorph ∈ contDiffGroupoid ω 𝓘(ℂ, F) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa using ((contDiff_id.add contDiff_const : ContDiff ℂ ω fun x : F => x + v)).contDiffOn
  · simpa [Homeomorph.addRight_symm] using
      ((contDiff_id.add contDiff_const : ContDiff ℂ ω fun x : F => x + -v)).contDiffOn

theorem trans_mem_maximalAtlas {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {M : Type} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℂ, F) ω M]
    {c : OpenPartialHomeomorph M F} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℂ, F) ω M)
    {T : OpenPartialHomeomorph F F} (hT : T ∈ contDiffGroupoid ω 𝓘(ℂ, F)) :
    c.trans T ∈ IsManifold.maximalAtlas 𝓘(ℂ, F) ω M := by
  intro e' he'
  have he'' := (contDiffGroupoid ω 𝓘(ℂ, F)).subset_maximalAtlas he'
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ω 𝓘(ℂ, F)).trans ((contDiffGroupoid ω 𝓘(ℂ, F)).symm hT)
      (StructureGroupoid.compatible_of_mem_maximalAtlas hc he'')
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ω 𝓘(ℂ, F)).trans
      (StructureGroupoid.compatible_of_mem_maximalAtlas he'' hc) hT

theorem adaptedChart_closedPoint (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (y₀ : ComplexPoint X) :
    ∃ (x : X.left) (_ : Order.coheight x = dim X.left)
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin (dim X.left) → ℂ)))
      (L : ((Fin 0 → ℂ) × (Fin (dim X.left) → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ)),
      e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
        IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X) ∧
      (∀ z ∈ e.source,
        z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0) ∧
      y₀ ∈ e.source ∧ y₀ ∈ cycleComponentSmoothSupportAmbientOpen X x := by
  have hclosed : IsClosed {y₀.underlying} :=
    (pointEquivClosedPoint X.hom ⟨y₀.left, Over.w y₀⟩).2
  have hx : Order.coheight y₀.underlying = dim X.left :=
    SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed (f := X.hom) _ hclosed
  let c := chartAt (Fin (dim X.left) → ℂ) y₀
  let T := (Homeomorph.addRight (-(c y₀))).toOpenPartialHomeomorph
  let L := ContinuousLinearEquiv.uniqueProd ℂ (Fin (dim X.left) → ℂ) (Fin 0 → ℂ)
  let e := (c.trans T).trans L.symm.toHomeomorph.toOpenPartialHomeomorph
  have hsrc : e.source = c.source := by simp [e, T]
  refine ⟨y₀.underlying, hx, e, L, ?_, ?_, ?_, ?_⟩
  · apply StructureGroupoid.mem_maximalAtlas_of_eqOnSource (e := c.trans T)
    · constructor
      · simp [e, T]
      · intro z _
        simp [e, L, T]
    · exact trans_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y₀) (translate_mem _)
  · intro z hz
    rw [hsrc] at hz
    have hy₀ : y₀ ∈ c.source := mem_chart_source _ y₀
    change z.underlying ∈ closure {y₀.underlying} ↔ _
    rw [hclosed.closure_eq, Set.mem_singleton_iff]
    have : (e z).2 = c z + -(c y₀) := by simp [e, L, T]
    rw [this, add_neg_eq_zero]
    constructor
    · intro h
      rw [underlying_injective_of_locallyOfFiniteType h]
    · intro h
      rw [c.injOn hz hy₀ h]
  · rw [hsrc]; exact mem_chart_source _ y₀
  · rw [cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension X _ hx]
    trivial
```

The two general lemmas `translate_mem` and `trans_mem_maximalAtlas` are also what the downstream chart moves need (the plan's `htr` chart followed by a coordinate permutation, the flattening chart followed by its linear identification).

For the chart step, ψ = `chartAt` of the open subscheme meets `hψ` (`IsManifold.chart_mem_maximalAtlas`), and RT6 discharges the second instance argument for every U.

## 3. Trivially true?

- RT4, four attempts on the rung, all fail: `⟨⟨e.source, e.open_source⟩, subset_rfl, hy, rfl⟩` (type mismatch), the same with `simp_all [chartNormalProjectionCoclass, chartNormalProjectionPair]` (unsolved goal), with `Subsingleton.elim _ _` (no instance), and `aesop` (heartbeat timeout). The sketch's three attempts also fail.
- Neither side is forced to zero at points of Z. The right side pairs to 1 with upstream's flattened normal class (`chartNormalProjectionCoclass_apply_normalClass`), so it is nonzero on the flattened neighbourhood; its germ at y ∈ Z is nonzero (RT7, section 7b). The left side's sheafified restriction to U is nonzero (`toSheaf_transport_supportedClass_ne_zero`, proved).
- Each hypothesis is used. Without `he` the statement is false for odd p: replacing the normal coordinate n by its conjugate keeps `hS` and multiplies the chart coclass by (−1)^p (conjugation on ℂ^p is diag(1, −1, …) in consecutive real coordinates, determinant (−1)^p), so both charts satisfying the conclusion would force 2·germ = 0 against the nonzero germ of RT7. Without `hS` the right side is undefined. `hy` is needed for W ∋ y ⊆ e.source. `hyU` is redundant in truth (1a).
- No ℕ∞ issue: `p : ℕ` appears as `(p : ℕ∞)` in `hx`, as `2 * p` in degrees, as `Fin p` in the chart, the same spellings upstream uses.
- Germ form. RT3 proves, for any space, support, degree, opens U, V ∋ x and classes a on U, b on V: equality of `supportRelativeCohomologyGerm` at x iff `∃ W ≤ U ⊓ V, x ∈ W` on which the restrictions agree. Forward direction through `supportRelativeCohomologyGerm_eq_zero_iff` (`Other`) applied to the difference on U ⊓ V; backward is upstream's `supportRelativeCohomologyGerm_eq_of_restrict_eq`. With U = ⊤, V = e.source and `chartNormalProjectionCoclass_restrict`, the rung's conclusion is equality of germs at y, and it persists on every smaller open around y.

## 4. Interface rung

Not applicable: no structure, no axioms. The chart step is a separate theorem with an open proof; it says nothing about cohomology and cannot imply the rung.

## 5. Checker

Not a checked rung. The five helpers print the three standard axioms (RT1). `check.py --no-build` rejects the worktree on the sorry scan only (finding 9).

## 6. Conventions

| Convention | Where it enters | Register row | Truth depends on it |
|---|---|---|---|
| Complex orientation of ℂ^p, consecutive (Re, Im) | right side (`standardComplexLocalClass`) | "Complex orientation of ℂ^p" | yes, an identity |
| Local class pairs to 1 with the orientation class | right side (`normalizedRelativeCoclass`), left side through upstream's flattening-chart germs | "Fundamental-class normalization", "Universal-coefficient evaluation" | yes |
| N against the singular transport, no sign | the proof route (`coclassSection_eq_singular`) | "Normalization iso against the singular transport" | yes |
| Holomorphy of charts: Mathlib's ω-maximal atlas over upstream's `localChart`; normal coordinate is the second factor of E × ℂ^p | `he`, `hS`, right side | new row "Holomorphic adapted chart" (added) | yes: an antiholomorphic normal coordinate changes the right side by (−1)^p; every ℂ-linear change of normal coordinates, reorderings included, leaves it unchanged |
| Complex structure on X(ℂ) | `localChart` from evaluations (`Point.evaluate`) of étale coordinate sections, holomorphic transitions by `analyticAt_localChart_transition`; upstream's flattening chart is `localChart` of the ambient open followed by a bi-analytic map and a ℂ-linear basis of the normal space | same new row | yes, for the same reason; both the left side (via upstream's flattening charts) and `he` refer to this one structure, so no conjugation can enter between them |

Borrowed results the proof will cite: `exists_open_chartNormalProjectionCoclass_eq` (upstream) assumes `AnalyticAt ℂ` of the transition and its inverse, which `he` and the chart step give; its orientation invariance is `exists_open_complexDifferentiable_localClass_invariance` for any invertible complex matrix, so no sign. `smoothClosedSupportCoclassStalk_eq_chartGerm` (upstream) is stated with the same `chartNormalProjectionCoclass`. Every cited input uses the definitions the statement is written against; none is an assumed `Prop`.

The `L` argument is harmless. It is universally quantified with `he`; two choices differ by a ℂ-linear automorphism of ℂ^d, an element of the groupoid, so `he` for one L gives it for all. It also forces E ≅ ℂ^{d−p}, which the proof needs to match upstream's tangential factor `Fin (d − p) → ℂ`; `chartNormalProjectionCoclass` reads only `(e ·).2`, so post-composing e with `L' × id` leaves the right side unchanged. The ℝ-structure on E that `chartNormalProjectionCoclass` takes is the one induced from ℂ and does not enter the value.

## 7. Equality first

The rung is an identity, exact, with no sign and no scalar; the docstring says so. It should cite the register rows (change C). It is a step toward `cycle-class-multiplicative` ([Z] ∪ [W] = [T], in the ledger, open).

## 7b. Non-vacuity

Smallest test that fails if the conclusion were trivially true: the germ at y ∈ Z of the right side is nonzero. Not in the repository or upstream; RT7 proves it at the pin (standard axioms, imports `HodgeLadder.Normalization.Singular` and `Other.AlgebraicGeometry.Hodge.CodimensionZeroNonvanishing`):

```lean
set_option backward.isDefEq.respectTransparency false in
theorem chartNormalProjectionCoclass_germ_ne_zero {M : Type} [TopologicalSpace M]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (y : M) (hy : y ∈ e.source) (h0 : (e y).2 = 0) :
    supportRelativeCohomologyGerm (TopCat.of M) S (2 * c) ⟨e.source, e.open_source⟩ y hy
      (chartNormalProjectionCoclass E c e S hS e.source subset_rfl) ≠ 0 := by
  intro h
  obtain ⟨W, hWU, hyW, hz⟩ :=
    (supportRelativeCohomologyGerm_eq_zero_iff (TopCat.of M) S (2 * c) _ y hy _).mp h
  have hWs : (W : Set M) ⊆ e.source := hWU
  have hz' : chartNormalProjectionCoclass E c e S hS W hWs = 0 := by
    rw [← chartNormalProjectionCoclass_restrict E c e S hS hWs subset_rfl]
    exact hz
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
        (chartNormalProjectionCoclass E c e S hS W hWs) := by
    rw [chartNormalProjectionCoclass_restrict]
    rfl
  rw [h2, hz', map_zero, map_zero] at h1
  exact zero_ne_one ((LinearMap.zero_apply _).symm.trans h1)
```

Route: a zero germ gives W with zero restriction (`supportRelativeCohomologyGerm_eq_zero_iff`); on the flattened neighbourhood of `e.restrOpen W` the chart coclass is that restriction (`chartNormalProjectionCoclass_restrict`, then `rfl`, since `restrOpen` keeps the function) and pairs to 1 (`chartNormalProjectionCoclass_apply_normalClass`). Together with RT2 it makes the rung's conclusion a nonzero identity in positive codimension. A second test with an independent code path: at a closed point, upstream's `cycleComponentSupportedInjectiveClass_point_normalization` and `analyticComponentPointSupportedInjectiveCoclass_relative` (`Other`) give the left side as `analyticComponentPointRelativeCoclass`, built from `analyticPointLocalCoclass`, the older point coclass; the rung at the RT2 chart then says that class restricts to the chart coclass. Proposed test rung `cycle-class-germ-point` (change H).

## 8. Pin drift

The sketch, the file and this pass read the same commit `2ead713`; no drift. The statement's type uses upstream's statement library only (`Definitions` and `Lemmas`) and Mathlib. `Other` declarations used:

| Where | `Other` declarations |
|---|---|
| helpers in `Germ.lean` | `cycleComponentSupportedInjectiveClass_normalization` (`Cycle/FundamentalClass.lean`), `cycleComponentSmoothSupportCoclassSection_ne_zero` (`Hodge/CodimensionZeroNonvanishing.lean`), `coheight_genericPoint_eq_zero`, `cycleComponentAnalyticClosedSupport_genericPoint_eq_top` (`Hodge/CodimensionZeroComparison.lean`); `normalization_singular`'s closure as listed in `normalization-singular.redteam.md` §8 |
| RT2 witness | `cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension` (`Cycle/Component/PointBoundary.lean`), `underlying_injective_of_locallyOfFiniteType` (`ComplexPoint/ClosedImmersion.lean`) |
| RT3, the planned proof | `supportRelativeCohomologyGerm_eq_zero_iff` (`AlgebraicTopology/Support/RelativeCohomologyGerm.lean`), `supportRelativeCohomologySheafOpenIso_unit_apply`, `supportRelativeCohomologySectionOnOpen_restrict` (`AlgebraicTopology/Support/RelativeCohomologyOpenTransport.lean`) |
| test rung H | `cycleComponentSupportedInjectiveClass_point_normalization`, `analyticComponentPointSupportedInjectiveCoclass_relative` (`Cycle/Component/PointClassNormalization.lean`) |

A change in `Other` can break the proof and cannot change what the rung says.

## 9. Chart step

`lift_mem_maximalAtlas_openScheme` is true: the transition from the lifted ψ to `localChart X d w` factors as ψ's transition to `localChart (openScheme X U) d z` (analytic by `hψ`) followed by `localChart X d w ∘ ι ∘ (localChart U z)⁻¹`, whose components are evaluations of sections of X restricted to U, analytic by upstream's `analyticAt_localChart_symm_evaluate` on U; the inverse uses the same lemma on X for sections of U, which are sections of X over opens inside U. The one input not at the pin is that `Point.evaluate` commutes with the open immersion. It is split correctly: the main proof needs it only for ψ = `localChart` of `cycleComponentSmoothLocusAmbientOpenOver X x`, which upstream's flattening chart is built on; stating it for the whole maximal atlas costs nothing. The second instance argument holds for every U (RT6), and there is no global instance, so it is an argument as written. `lift_mem_maximalAtlas_smoothSupportAmbient` lifts along the same open embedding upstream uses to transport the coclass section (`cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding`, which is `isOpenEmbedding_map_open`), so the two lifts agree definitionally. Name `open-subscheme-chart-analytic`: fine; kind foundation, no dependencies.

## 10. Verdict

**Pass with changes.**

Findings:

1. The statement is the literature's germ description of the cycle class at a smooth point, for every holomorphic adapted chart, exact.
2. Sign: the only place a sign could hide is an antiholomorphic or orientation-reversing normal coordinate; `he` excludes the first, and upstream's invariance theorem rules out a sign from any ℂ-linear reordering. Without `he` the statement is false for odd p.
3. `hyU` is redundant in truth and harmless for `cycle-class-multiplicative`; it records a gap at the pin.
4. The hypotheses are satisfiable in positive codimension at the pin on every X (RT2), without `affine-chart-analytic`; the sketch says otherwise in its non-vacuity paragraph.
5. The `∃ W` form is equivalent to germ equality (RT3).
6. Four trivial proofs fail (RT4).
7. The downstream statement binds `{d} [SmoothOfRelativeDimension d X.hom]`; the rung uses `dim X.left`. They connect by `obtain rfl := SmoothOfRelativeDimension.dim_eq (f := X.hom) d` (RT5).
8. Sketch record: it says the ledger names `HodgeLadder/Cycle/Class/Germ.lean`; the ledger entry has `"module": null` and no file path.
9. The sorry scan rejects the tree while `Germ.lean` has its two `sorry`s, so the statement cannot be committed to `main` as `stated`; it stays on the branch until both proofs land, or the chart step lands first on its own.

Changes:

| # | Change | Who | Status |
|---|---|---|---|
| A | Conventions row "Holomorphic adapted chart" | red team | done (`docs/conventions.md`) |
| B | Add `translate_mem`, `trans_mem_maximalAtlas`, `adaptedChart_closedPoint` (section 2 text) to `Germ.lean` as proved helpers; correct the docstring of `adaptedChart_genericPoint` and the sketch's non-vacuity paragraph to say that positive codimension is met at the pin | prover | open |
| C | Rung docstring: cite the register rows "Complex orientation of ℂ^p", "Fundamental-class normalization", "Normalization iso against the singular transport", "Holomorphic adapted chart"; say that `hyU` is automatic off Z and implied on Z by `he`, `hS` (gap, change G) | prover | open |
| D | Sketch: replace "The ledger entry names the file `HodgeLadder/Cycle/Class/Germ.lean`" with the module path actually in use | maintainer | open |
| E | Ledger: add `open-subscheme-chart-analytic` (foundation, no dependencies, declarations `lift_mem_maximalAtlas_openScheme`, `lift_mem_maximalAtlas_smoothSupportAmbient`) and make `cycle-class-germ` depend on it | maintainer | open |
| F | Add `chartNormalProjectionCoclass_germ_ne_zero` (section 7b text, checked in RT7) to `Germ.lean` | prover | open |
| G | New rung, stronger, open: `analytic-smooth-locus`, under `he` and `hS`, `e.source ∩ Z ⊆ cycleComponentSmoothSupportAmbientOpen X x`; with it the rung holds without `hyU` | maintainer | open |
| H | New test rung `cycle-class-germ-point`: at a closed point and the chart of `adaptedChart_closedPoint`, the rung's conclusion, cross-checked against upstream's point normalization | maintainer | open |
| I | `cycle-class-multiplicative`: either bind `dim X.left` in place of `{d}`, or note the `dim_eq` substitution of RT5 in the sketch | maintainer | open, optional |

No change to the statement of the rung or of the chart step.
