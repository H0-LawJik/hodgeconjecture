# Red team: `p2-fundamental-class-every-point` (test)

Date: 2026-11-27. Worktree `p2-fundamental-class-every-point` at base `9a9b9cb` (= `main`), with the uncommitted module `HodgeLadder/P2/Fundamental/Class/Every/Point.lean` (249 lines, module `HodgeLadder.P2.Fundamental.Class.Every.Point`). No sketch, no ledger edit yet. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same as on `main`.

Read: the ledger entries of this rung and of `p2-fundamental-class`; `docs/sketches/p2-fundamental-class.redteam.md` (change H proposed this rung); `docs/conventions.md` rows "Complex orientation of ℂ^p", "Point local coclass", "Degree on H⁴(ℙ²)", "Fundamental class of ℙ²(ℂ)"; `docs/references.md` row `Hatcher2002`; `docs/gaps.md` "General lemmas kept local"; the independence guard at the end of `HodgeLadder/Tests/CycleClassSignTestP2.lean`. Upstream at the pin: `Other/AlgebraicGeometry/ComplexPoint/LocalOrientation.lean` (`complexLocalOrientation`, `span_complexLocalOrientation_eq_top`), `LocalOrientationNeighborhood.lean` (`complexLocalOrientationNeighborhood`, `…NeighborhoodClass`, `…NeighborhoodClass_restrict`, `exists_neighborhood_complexLocalOrientation`), `LocalOrientationCoherence.lean` (`localClassOfChart_localChart_eq`, `complexLocalOrientation_eq_localClassOfChart_localChart`), `OrientationHomologySheaf.lean`, `Other/AlgebraicTopology/Sheaf/HomologySection.lean` (`relativeHomologyToHomologySheafSection`, `…_germ`), `Other/AlgebraicTopology/Singular/Sheaf/ChainHomology.lean` (`singularChainHomologySheaf`, `singularChainHomologySheafStalkIso`), `Other/AlgebraicTopology/LocalHomology/ChartFundamentalClassGenerator.lean` (`localClassOfChart_ne_zero`, needs only `T1Space`), `HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Cohomology.lean` (`relativeHomologyProjection`, `supportInclusionPairMap`), `…/RelativeHomotopyInvariance.lean` (`relativeChainProjection_naturality`).

Scratch files (directory `scratch/` in the worktree, `lake env lean`, 6 to 8 s each, deleted afterwards):

| File | What | Result |
|---|---|---|
| RT1 | `#print axioms` on all 9 declarations and on upstream's `complexLocalOrientationNeighborhoodClass_restrict`, `localClassOfChart_localChart_eq`; `#synth` of the instances; non-vacuity, load-bearing hypothesis, sign separation; trivial proofs | standard axioms everywhere (`propext`, `Classical.choice`, `Quot.sound`); `T2Space (ComplexPoint projectivePlane)` is upstream's `ComplexProjectiveSpace.instT2SpaceProjectiveSpaceComplexPoint 2`, `SmoothOfRelativeDimension 2 projectivePlane.hom` is `smoothOfRelativeDimension_projectiveSpace 2`; `complexLocalOrientation projectivePlane 2 y ≠ 0` and `≠ −complexLocalOrientation projectivePlane 2 y` at every y; `¬ ∀ μ y, (relativeHomologyProjection …).hom μ = complexLocalOrientation projectivePlane 2 y` (μ = 0 fails it); from the `∃!`, a μ whose image at every y is the orientation and not its negative; `complexLocalOrientation … y = localClassOfChart 2 (localChart projectivePlane 2 y) y _` by `rfl`; `simp [hμ]`, `aesop`, `subst y; exact hμ` on the rung all fail |
| RTGeneral | lines 60 to 213 of the module (the 7 general lemmas) under the four upstream imports `Other.AlgebraicGeometry.ComplexPoint.LocalOrientationNeighborhood`, `Other.AlgebraicTopology.Sheaf.HomologySection`, `Other.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator`, `Mathlib.Topology.LocallyConstant.Basic` only | clean: the general lemmas need no ladder module |
| RTRung | the general lemmas and `relativeHomologyProjection_eq_complexLocalOrientation_of_planeOrigin` under `HodgeLadder.Tests.ProjectivePlaneFundamental` plus upstream imports, without `ProjectivePlaneFundamentalDegree` | clean: only the `∃!` form needs `ProjectivePlaneFundamentalDegree` |

The module itself elaborates clean with `lake env lean` (6.5 s, no warnings). `python3 tools/check.py --no-build` after deleting the scratch files: `ACCEPTED: all checks passed`; the module is not in the ledger or `HodgeLadder.lean` yet, so the checker does not scan it and RT1 is the axiom evidence until phase 2 names it.

**Verdict: pass with changes.** The statement is upstream's complex local orientation at every point, exactly, as the image of the class of `p2-fundamental-class`; with the `∃!` form it is the literature's definition of the fundamental class of an orientation (every point), in place of the one-point characterization. The proof is correct, not circular, carries no sign or scalar, and uses the standard axioms. No orientation comes out −1 anywhere: a chart-change flip is excluded by upstream's checked coherence theorem, and RT1 separates the orientation from its negative at every point. The changes are placement (general lemmas to a `General/` module behind upstream imports only, rung module renamed under `Tests/`), the `docs/gaps.md` row, and the text that `p2-fundamental-class` and `docs/conventions.md` carry about "not proved".

## 1. Is this the statement the literature makes?

Literature [`Hatcher2002` §3.3; recalled, numbering unverified]: an R-orientation of an n-manifold M is a function x ↦ μ_x with μ_x a generator of Hₙ(M | x; R) = Hₙ(M, M ∖ x; R), locally consistent: each x has a neighborhood B and one class μ_B ∈ Hₙ(M | B; R) whose image at every y ∈ B is μ_y. A fundamental class is an element of Hₙ(M; R) whose image in Hₙ(M | x; R) is a generator for every x; the fundamental class of the orientation is the one whose image at every x is μ_x. Theorem 3.26: for M closed, connected and R-orientable, Hₙ(M; R) → Hₙ(M | x; R) is an isomorphism for every x.

| Literature | Lean | Check |
|---|---|---|
| Hₙ(M; ℚ), n = 4, M = ℙ²(ℂ) | `Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2)` | as in the parent rung; `2 * 2` is the index of `complexLocalOrientation projectivePlane 2` (its type is `RelativeHomology ℚ (pointComplementPair z) (2 * d)`), and d = 2 is forced by the instance `smoothOfRelativeDimension_projectiveSpace 2` |
| Hₙ(M, M ∖ y; ℚ) for every y | `RelativeHomology ℚ (pointComplementPair y) (2 * 2)`, `pointComplementPair y = TopPair.ofSubset {y}ᶜ` | the general lemmas pass between the two forms with no cast |
| the restriction Hₙ(M) → Hₙ(M, M ∖ y) | `relativeHomologyProjection ℚ (pointComplementPair y) (2 * 2)` | the chain quotient; no sign |
| the orientation x ↦ μ_x | `complexLocalOrientation projectivePlane 2 y` = `localClassOfChart 2 (localChart projectivePlane 2 y) y _` (by `rfl`) | each value a generator (`span_complexLocalOrientation_eq_top`, `localClassOfChart_ne_zero`); local consistency is upstream's `exists_neighborhood_complexLocalOrientation` (an open N in place of Hatcher's ball, which is all the definition uses) |
| [M]: image μ_y at every y | `existsUnique_forall_restrict_complexLocalOrientation` (`∃! μ, ∀ y, …`) | exact, no scalar |
| the rung as titled | `relativeHomologyProjection_eq_complexLocalOrientation_of_planeOrigin` | stronger than the title: any μ restricting to μ_{[0:0:1]} restricts to μ_y at every y; applied to the unique μ of `p2-fundamental-class` it is the title |

The parent red team recorded that the one-point condition already determines [M] on a connected manifold; that remains true. This rung proves the every-point form directly, so `existsUnique_forall_restrict_complexLocalOrientation` is the literature's definition token for token, and the docstring's "the literature's definition of the fundamental class of the complex orientation" is accurate given row "Complex orientation of ℂ^p".

## 2. Can the hypotheses be satisfied?

`existsUnique_forall_restrict_complexLocalOrientation` has no hypotheses. `relativeHomologyProjection_eq_complexLocalOrientation_of_planeOrigin` takes `hμ`, met by `existsUnique_restrict_complexLocalOrientation` (used in the `∃!` proof itself). The general lemmas take:

- `T2Space (ComplexPoint X)`: met at X = ℙ² by upstream's instance (RT1 `#synth`).
- `SmoothOfRelativeDimension d X.hom`: met at d = 2 (RT1 `#synth`). A wrong d fails to elaborate, so the degree cannot drift silently.
- `PreconnectedSpace (ComplexPoint X)`: met at ℙ² by `ComplexPoint.connectedSpace` with `IsIntegral`, `Smooth` and the `QuasiSeparatedSpace` the module supplies by `quasiSeparatedSpace_of_quasiSeparated`. Load-bearing: on a disconnected X(ℂ), a class equal to the orientation on one component and 0 on another meets `hx` and fails the conclusion.
- `hq`, `hx`, `hμ`: met by the parent's μ. Load-bearing: RT1 shows μ = 0 fails the conclusion at every y.

## 3. Trivially true?

No. `complexLocalOrientation projectivePlane 2 y` is nonzero at every y (RT1, upstream `localClassOfChart_ne_zero`), so the conclusion is a nonzero equality at every point; `¬ ∀ μ y, …` holds (RT1), so `hμ` is used; `simp [hμ]`, `aesop`, `subst` fail. No definition unfolds to `True`, no `ℕ∞` coercion, no empty index type (ℙ²(ℂ) has `planeOriginPoint`).

**Circularity.** `complexLocalOrientation` at y is the chart class at y, by `rfl`; it refers to no global class. `complexLocalOrientationNeighborhoodClass` is built from the chart at its centre (upstream's `chartOrientationNeighborhoodClass`), and its restriction to the orientation at nearby z is a theorem whose last step is the chart coherence `complexLocalOrientation_eq_localClassOfChart_localChart`. The homology sheaf, its stalk iso and the germ theorem are pure singular topology. Nothing in the chain is defined from μ or from the conclusion.

## 4. Interface axioms

None: no structure, upstream definitions only.

## 5. Axioms and names

RT1, `#print axioms`, all `[propext, Classical.choice, Quot.sound]`:

- `HodgeLadder.LocalOrientation.homologySheafStalkIso_germ_section`
- `HodgeLadder.LocalOrientation.eventually_restrict_eq_smul`
- `HodgeLadder.LocalOrientation.exists_eq_smul_complexLocalOrientation`
- `HodgeLadder.LocalOrientation.smul_complexLocalOrientation_injective`
- `HodgeLadder.LocalOrientation.restrict_top_eq_complexLocalOrientation`
- `HodgeLadder.LocalOrientation.relativeHomologyProjection_pointComplementPair_eq`
- `HodgeLadder.LocalOrientation.relativeHomologyProjection_eq_complexLocalOrientation_of_eq`
- `HodgeLadder.Tests.relativeHomologyProjection_eq_complexLocalOrientation_of_planeOrigin`
- `HodgeLadder.Tests.existsUnique_forall_restrict_complexLocalOrientation`

and upstream's `complexLocalOrientationNeighborhoodClass_restrict`, `localClassOfChart_localChart_eq`. No `sorry`, `native_decide`, `axiom`, `unsafe` or `set_option` in the module; one `erw` (line 194) rewrites by `hfst : TopPair.Hom.fst (supportInclusionPairMap …) = 𝟙 _ := rfl`, which holds because upstream defines `supportInclusionPairMap` as `TopPair.ofHom (𝟙 X) …` (a drift point, section 8). The `∃!` uses the parent's `existsUnique_restrict_complexLocalOrientation`, the declaration the parent ledger entry names.

## 6. Conventions

| Convention | Used by | Truth depends on it? | Row |
|---|---|---|---|
| Ordering of real coordinates of ℂ^d in `standardComplexLocalClass` | every value of `complexLocalOrientation` | no: a different ordering (for example real parts first, (−1)^{d(d−1)/2} = −1 at d = 2) multiplies every μ_y by the same sign, and point independence is a statement about a family against itself; the literature reading μ = [ℙ²] does depend on it, as in the parent | "Complex orientation of ℂ^p" (pinned) |
| Chart coherence: the class from the chart at z equals the class from the chart at z' at every common point | `complexLocalOrientationNeighborhoodClass_restrict`, through `localClassOfChart_localChart_eq` | yes: a transition reversing orientation would make the conclusion false. Upstream proves coherence because the transitions are holomorphic (charts of the 𝓘(ℂ, ℂ^d) atlas), so their derivatives are ℂ-linear (`tangentCoordChange`), with real determinant \|det_ℂ\|² > 0, whatever the ordering convention; a theorem at the pin with standard axioms (RT1) | none; new row (change 4) |
| Stalk identification of the homology sheaf | `homologySheafStalkIso_germ_section`, `eventually_restrict_eq_smul` | no: both germs are compared through the same iso, used only for injectivity and through upstream's `relativeHomologyToHomologySheafSection_germ`; a sign or scalar in the iso cancels | none needed |
| Naturality of `relativeChainProjection` | `relativeHomologyProjection_pointComplementPair_eq` | no: commutation of a square, identity on X | none needed |
| Generator coefficient q | `exists_eq_smul_complexLocalOrientation`, `smul_complexLocalOrientation_injective` | the proof shows q = 1 at every point, exactly | none needed |

**Could a chart-change flip hide?** No. A flip between the chart at y and the chart at some z ∈ N would make `complexLocalOrientationNeighborhoodClass_restrict` false, and that theorem is checked; RT1 also shows o_y ≠ −o_y at every y, so the exact equality at every y separates the two. An antiholomorphic chart is outside the atlas upstream's `localChart` is taken from. What the rung cannot see is a uniform fault in the orientation of ℂ², which the pinned row carries.

**Nothing is up to scalar.** The only scalar is q, proved equal to `1` at every point (`hfx`, then `IsLocallyConstant.apply_eq_of_preconnectedSpace`).

`docs/conventions.md`: row "Fundamental class of ℙ²(ℂ)" says "That μ restricts to `complexLocalOrientation` at every other point is not proved in Lean"; this rung proves it (change 3); a new row for chart coherence (change 4).

## 7. Equality first

Both P2 declarations assert exact equalities in H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ y; ℚ) at every y; `∃!` is exact. No inclusion and no scalar.

## 7b. Non-vacuity

The smallest test that fails if the rung were trivially true: at some y the image of μ is nonzero. The parent's `HodgeLadder.Tests.ne_zero_of_restrict_complexLocalOrientation` (μ ≠ 0) exists and covers the hypothesis side; RT1 proves the stronger `¬ ∀ μ y, (relativeHomologyProjection ℚ (pointComplementPair y) (2 * 2)).hom μ = complexLocalOrientation projectivePlane 2 y` in 4 lines from `localClassOfChart_ne_zero`, and the sign separation o_y ≠ −o_y in 6. Neither is a named lemma; change 6 proposes one.

## 8. Pin drift

Checked at `2ead713`, the current pin; no drift. For the next bump, diff: upstream `complexLocalOrientation`, `localClassOfChart`, `localChart`, `mem_localChart_source`, `complexLocalOrientationNeighborhood`, `mem_complexLocalOrientationNeighborhood`, `complexLocalOrientationNeighborhoodClass`, `complexLocalOrientationNeighborhoodClass_restrict`, `localClassOfChart_localChart_eq`, `span_complexLocalOrientation_eq_top`, `localClassOfChart_ne_zero`, `singularChainHomologySheaf`, `singularChainHomologySheafStalkIso`, `relativeHomologyToHomologySheafSection`, `relativeHomologyToHomologySheafSection_germ`, `supportInclusionPairMap` (must keep `TopPair.ofHom (𝟙 X)` for the `rfl` of `hfst`), `relativeChainProjection_naturality`, `relativeHomologyProjection`, `relativeHomologyMap`, `pointComplementPair`, `ComplexPoint.connectedSpace`, `ComplexProjectiveSpace.instT2SpaceProjectiveSpaceComplexPoint`, `smoothOfRelativeDimension_projectiveSpace`; Mathlib `TopCat.Presheaf.germ_eq`, `TopCat.Presheaf.germ_res_apply`, `IsLocallyConstant.iff_eventually_eq`, `IsLocallyConstant.apply_eq_of_preconnectedSpace`. A change of `complexLocalOrientation` or of its chart construction changes what the rung means (recheck rows "Complex orientation of ℂ^p", "Fundamental class of ℙ²(ℂ)" and the new coherence row); a sign or scalar in the stalk iso cannot alter truth (section 6).

## Findings

1. **No −1 anywhere, and no sign other than +1 is forced.** The orientation is upstream's at every point; the coefficient is 1 at every point, proved; o_y ≠ −o_y (RT1). Mathlib's Koszul sign does not enter this rung (no products).
2. **Correct and exact.** The germ route replaces the injectivity H₄(ℙ², ℙ² ∖ N) → H₄(ℙ², ℙ² ∖ z) the ledger note found missing: two sections over U and N with equal germs at y agree on a smaller W (`germ_eq`), which gives the same local constancy. Sound.
3. **The statement matches the literature and is stronger than the title.** Any μ with the one-point condition restricts to μ_y everywhere; the `∃!` form is Hatcher's definition of the fundamental class of the orientation.
4. **Not circular.** `complexLocalOrientation` is the chart class (`rfl`); the neighborhood class is chart-built; coherence is upstream's checked theorem on holomorphic transitions.
5. **Hypotheses are met and load-bearing** (section 2), including preconnectedness for the general form.
6. **The general lemmas are general and sit behind the wrong import.** They need only upstream imports (RTGeneral), and the rung theorem needs only `ProjectivePlaneFundamental` (RTRung). The module imports `ProjectivePlaneFundamentalDegree`, hence `CycleClassSignTestP2`, hence `CycleClassMultiplicativeP2`. The independence guard in `CycleClassSignTestP2` judges an imported constant by its module and taints every module whose import closure meets the multiplicativity proof, so any future root using these general lemmas from this module would be flagged by a guard of that form although its proof is clean. They also need a `docs/gaps.md` row (decision 0011). Upstream has no equivalent at the pin (no every-point or locally-constant-coefficient theorem in `Other/AlgebraicGeometry/ComplexPoint/`; `complexOrientationHomologySheafIso` carries the same content in sheaf form).
7. **The module path is `tools/next.py`'s fallback.** `HodgeLadder/P2/Fundamental/Class/Every/Point.lean` comes from capitalizing the rung id when the ledger has no `module`; no ledger rung uses that shape, and it opens a new top-level directory holding one file four levels down. The ℙ² tests live in `HodgeLadder/Tests/`.
8. **Two docs now say "not proved".** The parent ledger note ("Not proved: that μ restricts to complexLocalOrientation at every other point …") and conventions row "Fundamental class of ℙ²(ℂ)" become stale when this lands. The parent docstring of `existsUnique_restrict_complexLocalOrientation` says "is not proved here", which stays true of its module.
9. **Minor.** `smul_complexLocalOrientation_injective` asks for `T2Space` where upstream's `localClassOfChart_ne_zero` needs `T1Space`; `homologySheafStalkIso_germ_section` holds for any Hausdorff `TopCat`, it does not use X. Neither affects truth.

## Changes

1. **(required) Split the module.** Move the 7 lemmas of namespace `HodgeLadder.LocalOrientation` (lines 66 to 213) to a new `HodgeLadder/General/LocalOrientation.lean` (module `HodgeLadder.General.LocalOrientation`) with only the imports `Other.AlgebraicGeometry.ComplexPoint.LocalOrientationNeighborhood`, `Other.AlgebraicTopology.Sheaf.HomologySection`, `Other.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator`, `Mathlib.Topology.LocallyConstant.Basic` (RTGeneral elaborated exactly this). Put the two P2 theorems in `HodgeLadder/Tests/ProjectivePlaneFundamentalEveryPoint.lean` (module `HodgeLadder.Tests.ProjectivePlaneFundamentalEveryPoint`), importing `HodgeLadder.General.LocalOrientation`, `HodgeLadder.Tests.ProjectivePlaneFundamentalDegree` (for the `∃!`) and `Other.AlgebraicGeometry.ComplexPoint.SmoothConnected`; delete `HodgeLadder/P2/`. Keeping the `∃!` with the rung theorem is acceptable: the `∃!` needs the parent's uniqueness, which lives in `ProjectivePlaneFundamentalDegree` by the parent's change B, and the P2 statements are no reuse target. Each module gets its own module docstring; the general one carries steps 1 to 5 of the current docstring.
2. **(required, phase 2) Ledger and imports.** `module`: `HodgeLadder.Tests.ProjectivePlaneFundamentalEveryPoint`; `declarations`: the 9 names of section 5, headline `HodgeLadder.Tests.existsUnique_forall_restrict_complexLocalOrientation`; both modules imported from `HodgeLadder.lean`; status `checked` only after `python3 tools/check.py` scans them. Title unchanged. Note: "Checked 2026-11-27. Exactly one μ ∈ H₄(ℙ²(ℂ); ℚ) restricts to complexLocalOrientation projectivePlane 2 y at every y (Hatcher's definition of the fundamental class of an orientation); any μ restricting to it at [0 : 0 : 1] does. Route: a relative class on an open U gives a section of upstream's singular homology sheaf whose germ at z is its restriction to H(X, X ∖ z) (relativeHomologyToHomologySheafSection_germ); comparing germs with upstream's complexLocalOrientationNeighborhoodClass makes the coefficient against the orientation locally constant (TopCat.Presheaf.germ_eq), hence constant on connected ℙ²(ℂ), and 1 at [0 : 0 : 1]. No sign or scalar: the coefficient is 1 at every point. A chart-change flip would contradict upstream's checked coherence localClassOfChart_localChart_eq (holomorphic transitions); a uniform fault in the orientation of ℂ² is invisible here and carried by row \"Complex orientation of ℂ^p\". General lemmas in HodgeLadder.General.LocalOrientation, for any smooth X with X(ℂ) Hausdorff and preconnected. Red team: docs/sketches/p2-fundamental-class-every-point.redteam.md, pass with changes 1 to 6."
3. **(required, phase 2) Stale "not proved".** In the ledger note of `p2-fundamental-class`, replace "Not proved: that μ restricts to complexLocalOrientation at every other point (not needed for the one-point reading; rung p2-fundamental-class-every-point)." with "That μ restricts to complexLocalOrientation at every other point is rung p2-fundamental-class-every-point (checked)." In `docs/conventions.md` row "Fundamental class of ℙ²(ℂ)", replace "That μ restricts to `complexLocalOrientation` at every other point is not proved in Lean (mathematically: upstream's coherence `complexOrientationHomologySheafIso` and connectedness); the one-point reading does not need it" with "μ restricts to `complexLocalOrientation` at every point (`existsUnique_forall_restrict_complexLocalOrientation`, rung `p2-fundamental-class-every-point`, from upstream's chart coherence and connectedness; no sign)", and add that rung to its last column.
4. **(required, phase 2) `docs/conventions.md`, new row** after "Fundamental class of ℙ²(ℂ)": Convention "Coherence of the complex local orientation"; Fixed where "upstream `Other/AlgebraicGeometry/ComplexPoint/LocalOrientationCoherence.lean` (`localClassOfChart_localChart_eq`, `complexLocalOrientation_eq_localClassOfChart_localChart`), `LocalOrientationNeighborhood.lean` (`complexLocalOrientationNeighborhoodClass_restrict`); used by `HodgeLadder.General.LocalOrientation`"; Choice "the class of `standardComplexLocalClass ℚ d` transported through the chart at z equals the one through the chart at z' at every common point, because the transition derivative `tangentCoordChange 𝓘(ℂ, ℂ^d)` is ℂ-linear (real determinant \|det_ℂ\|² > 0), whatever the real ordering of ℂ^d"; Results "`p2-fundamental-class-every-point` (an equality at every point): a transition reversing orientation would make it false; insensitive to the ordering convention of ℂ^d and to a sign or scalar in `singularChainHomologySheafStalkIso`"; Status "read from source, standard axioms at `2ead713` (red team 2026-11-27, `docs/sketches/p2-fundamental-class-every-point.redteam.md`)".
5. **(required, phase 2) `docs/gaps.md`, "General lemmas kept local"**, one row: `HodgeLadder.LocalOrientation.homologySheafStalkIso_germ_section`, `eventually_restrict_eq_smul`, `exists_eq_smul_complexLocalOrientation`, `smul_complexLocalOrientation_injective`, `restrict_top_eq_complexLocalOrientation`, `relativeHomologyProjection_pointComplementPair_eq`, `relativeHomologyProjection_eq_complexLocalOrientation_of_eq` (the coefficient of a relative class against upstream's complex local orientation is locally constant; on a Hausdorff preconnected X(ℂ) a class restricting to the orientation at one point restricts to it everywhere) | `HodgeLadder.General.LocalOrientation` | statements about upstream's `complexLocalOrientation`, its neighborhood class and homology sheaf alone, natural next to `complexOrientationHomologySheafIso` in `Other/AlgebraicGeometry/ComplexPoint/OrientationHomologySheaf.lean`; the first holds for any Hausdorff `TopCat`; rung `p2-fundamental-class-every-point` | 2026-11-27. Also the roadmap row, the `CLAUDE.md` Files table (`HodgeLadder/General/…` row gains `LocalOrientation`) and the status block, per the propagation map.
6. **(optional) Non-vacuity lemma** in the Tests module, the sign separation RT1 elaborated:

   ```lean
   /-- The orientation at every point is not its negative, so the identity at every point
   separates `μ` from `−μ`. -/
   theorem complexLocalOrientation_ne_neg (y : ComplexPoint projectivePlane) :
       complexLocalOrientation projectivePlane 2 y ≠
         -complexLocalOrientation projectivePlane 2 y := by
     intro h
     have h0 := localClassOfChart_ne_zero 2 (localChart projectivePlane 2 y) y
       (mem_localChart_source _ 2 y)
     have h2 : (2 : ℚ) • complexLocalOrientation projectivePlane 2 y = 0 := by
       rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel _
     exact h0 ((smul_eq_zero.mp h2).resolve_left (by norm_num))
   ```

   Also optional: weaken `[T2Space]` to `[T1Space]` on `smul_complexLocalOrientation_injective`, and state `homologySheafStalkIso_germ_section` for any `(Y : TopCat) [T2Space Y]` (finding 9).
