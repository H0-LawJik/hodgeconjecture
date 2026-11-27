# Red team: `p2-fundamental-class` (statement and proof)

Date: 2026-11-27. Worktree `p2-fundamental-class` at `41f2f6b`, plus the uncommitted `HodgeLadder/Tests/ProjectivePlaneFundamental.lean` (the rung module, 188 lines), `HodgeLadder/Tests/ProjectivePlaneFundamentalDegree.lean` (corollaries, 84 lines) and the section "p2-fundamental-class: statement" of `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, the same as on `main` (`44a0e85`).

Read: both Lean files; the sketch section; the ledger entry; `docs/sketches/cycle-class-sign-test-p2.redteam.md` (findings 1, 2, 6 and change G); `HodgeLadder/Tests/CycleClassSignTestP2.lean` (`planeDegree_eq_eval_of_restrict`, `subsingleton_H'_compl_planeOrigin`, the independence guard); `docs/conventions.md` rows "Complex orientation of ℂ^p", "Degree on H⁴(ℙ²)", "Transversal product of cycle classes", "Universal-coefficient evaluation", "Cohomology of an open"; `docs/references.md`. Upstream at the pin: `Other/AlgebraicGeometry/ComplexPoint/LocalOrientation.lean` (`complexLocalOrientation`, `span_complexLocalOrientation_eq_top`), `LocalOrientationNeighborhood.lean`, `OrientationHomologySheaf.lean` (`complexOrientationHomologySheafIso`), `Lemmas/AlgebraicTopology/Singular/Cohomology.lean` (`relativeHomologyProjection`, `relativeChainShortComplex`, `relativeChainShortComplex_shortExact`), `Lemmas/AlgebraicTopology/LocalHomology/ChartFundamentalClass.lean` (`pointComplementPair`), `Other/AlgebraicTopology/Singular/EmptySubspace.lean` (`homologyEmptySubspaceIso`), `Definitions/AlgebraicTopology/Support/Cohomology.lean` (`relH.forget_injective_of_eq_bot`), `Definitions/AlgebraicTopology/Support/CohomologyInjectiveModel.lean` (`relHAddEquivSupportedSectionsHomology`), `Lemmas/AlgebraicGeometry/Cycle/Transport/CohomologySheaf.lean` (`complexSupportInjectiveSectionCohomologyEquiv`).

Build state: the corollary module's `.olean` was older than its source. `lake build --no-build` named only that module as stale; I rebuilt it alone (5.1 s, no upstream or Mathlib job) and `lake env lean` on its source is clean.

Scratch files (in the worktree, `lake env lean`, deleted afterwards):

| File | What | Result |
|---|---|---|
| RT1 | `#print axioms` on all 14 declarations; non-vacuity; trivial proofs | standard axioms everywhere; `μ ≠ 0` for every μ with `hμ` (3 lines) and `complexLocalOrientation … ≠ 0` (5 lines); `⟨0, by simp⟩`, `⟨0, rfl⟩`, `infer_instance` on H₃ = 0, `simp` on the surjectivity, `aesop` on surjectivity for an arbitrary pair: all fail |
| RT2 | the sign-test guard's import-closure walk, with `import all` of the three modules and their constants expanded, roots `planeDegree_eq_eval_of_restrict`, `exists_planeDegree_eq_eval`, `existsUnique_restrict_complexLocalOrientation`, `eval_planeOrigin_of_restrict`, `exists_restrict_complexLocalOrientation` | no root reaches a module that is or imports `HodgeLadder.Cycle.Multiplicative`, `Tests.CycleClassMultiplicativeP2`, `Local.ClassProduct` or `Normalization.Germ`; positive control `planeDegree_planeLines_cup` fires (`coheight_planeOrigin_add`, from `CycleClassMultiplicativeP2`); the rung module is untainted |
| RT3 | are the theorem bodies visible to RT2's walk? | yes for all three modules under `import all` |

`python3 tools/check.py --no-build` after deleting the scratch files: `ACCEPTED: all checks passed`. The new modules are not in the ledger yet, so the checker does not scan them; RT1 is the axiom evidence until phase 2 names them.

**Verdict: pass with changes.** The statement is upstream's local orientation, exactly, as the image of a class in H₄(ℙ²(ℂ); ℚ); the proof is correct, carries no sign, and uses standard axioms. With the corollaries, μ is unique, so the ladder now has the literature's one-point characterization of [ℙ²] for upstream's complex local orientation, and `planeDegree` is ⟨Ψ −, μ⟩ with no hypothesis. The changes are text (docstrings, ledger title and note, sketch) and the choice to post the `∃!` form with the rung.

## 1. Is this the statement the literature makes?

Literature [`Hatcher2002` §3.3, Theorem 3.26 and the definition of a fundamental class; numbering unverified]: for a closed connected n-manifold M that is R-orientable, Hₙ(M; R) → Hₙ(M, M ∖ x; R) is an isomorphism for every x, and the fundamental class of an orientation is the class whose image at every x is the orientation's local generator μ_x. On a connected M an orientation is determined by its value at one point, so the class whose image at one point x is μ_x is the fundamental class of the orientation through μ_x. For a complex manifold the orientation is the complex one. `docs/references.md` lists `Hatcher2002` §3.3 for the cap product only (change G).

| Literature | Lean | Check |
|---|---|---|
| Hₙ(M; ℚ), n = 4, M = ℙ²(ℂ) | upstream `Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2)` | singular homology of the analytic topology (row "Cohomology of an open"); `2 * 2` is the index of `complexLocalOrientation projectivePlane 2` |
| Hₙ(M, M ∖ x; ℚ) | upstream `RelativeHomology ℚ (pointComplementPair planeOriginPoint) (2 * 2)`, `pointComplementPair x = TopPair.ofSubset {x}ᶜ` | `P.snd` is `TopCat.of {x}ᶜ` by `rfl`; the proof of the surjectivity passes between them with no cast |
| the restriction Hₙ(M) → Hₙ(M, M ∖ x) | upstream `relativeHomologyProjection` = `homologyMap (relativeChainProjection …)` | the quotient map on chains; no sign |
| μ_x for the complex orientation, x = [0 : 0 : 1] | upstream `complexLocalOrientation projectivePlane 2 planeOriginPoint` = `localClassOfChart 2 (localChart …)` of `standardComplexLocalClass ℚ 2` | complex local generator if `localChart` is orientation preserving (it is holomorphic, from algebraic étale coordinates) and `standardComplexLocalClass` is the complex orientation of ℂ² (row "Complex orientation of ℂ^p", pinned by `complexRealHomeomorph_eq`). Generator: `span_complexLocalOrientation_eq_top` |
| Theorem 3.26(a) at x | `planeOrigin_relativeHomologyProjection_bijective` | proved directly from H₃ = H₄ = 0 of ℙ²(ℂ) ∖ x; no orientability or connectedness hypothesis is used |
| [M], the unique class restricting to μ_x | `existsUnique_restrict_complexLocalOrientation` (corollary module); the rung `exists_restrict_complexLocalOrientation` is its existence half | exact, no scalar |
| deg α = ⟨α, [M]⟩ | `exists_planeDegree_eq_eval` | `planeDegree_eq_eval_of_restrict` with its hypothesis discharged; no hypothesis left |

**Is μ the literature's [ℙ²]?** Yes, at the one point, with two qualifications:

- The identification needs `complexLocalOrientation` at [0 : 0 : 1] to be the complex local generator. This rung cannot detect a fault there. A real-parts-first ordering of ℂ² would multiply `standardComplexLocalClass ℚ 2` by (−1)^{d(d−1)/2} = −1, making μ = −[ℙ²] and upstream's [pt] = −PD(pt), and every Lean statement in both files would stay true (deg [pt] = 1 and ⟨Ψ [pt], μ⟩ = 1 are both insensitive to it, since μ_pt and the normalization of [pt] share the class). The pinned row "Complex orientation of ℂ^p" is what excludes it. The conjugate orientation is invisible and harmless: (−1)^2 = +1, so [ℙ²] is the same for both.
- **Point independence is not needed for the reading.** On a connected manifold the one-point condition determines the orientation and hence [M]; the literature reading uses the orientation at one point only. That μ also restricts to `complexLocalOrientation projectivePlane 2 y` at every other y is true in mathematics (upstream proves the family coherent: `complexLocalOrientationNeighborhoodClass_restrict` and `complexOrientationHomologySheafIso`; ℙ²(ℂ) is connected) and not proved here. It would test upstream's coherence, which is already a theorem upstream; it cannot change a sign at a = b = 1, because H⁴(ℙ²; ℚ) is one-dimensional and the degree is pinned by one value. Proposed as an optional rung (H).

## 2. Can the hypotheses be satisfied?

The rung and its corollaries `exists_planeDegree_eq_eval`, `existsUnique_…`, `subsingleton_homology_{three,four}_compl_planeOrigin`, `planeOrigin_relativeHomologyProjection_{surjective,bijective}` have no hypotheses. `subsingleton_homology_compl_planeOrigin_of_H'` takes `Subsingleton (Sheaf.H' planeConst n planeOriginCompl)`, met at n = 3 (`subsingleton_H'_three_compl_planeOrigin`) and at every n ≥ 3 (`subsingleton_H'_compl_planeOrigin`); both are used. The pair lemmas take `Subsingleton (Homology ℚ P.snd n)`, met at the point pair for n = 3, 4. `eval_planeOrigin_of_restrict` takes `hμ`, met by the rung.

## 3. Trivially true?

No. If `complexLocalOrientation projectivePlane 2 planeOriginPoint` were 0 the rung would close with `⟨0, map_zero _⟩`; it is not 0 (RT1, from `eval_planeOrigin_of_restrict` and injectivity). `⟨0, by simp⟩`, `⟨0, rfl⟩`, `aesop` on the rung, `infer_instance` on H₃ = 0, `simp` on the surjectivity fail (RT1 and the prover's list). The surjectivity of `relativeHomologyProjection ℚ P 1` for an arbitrary pair resists `aesop` too, and fails in general (a pair (S¹, two points) has H₀(A) ≠ 0 and the map H₁(S¹) → H₁(S¹, A) is not onto), so the hypothesis of the pair lemma is load-bearing. No definition unfolds to `True`, no `ℕ∞` coercion enters, no index type is empty, every hypothesis is used. `4`, `3 + 1` and `2 * 2` agree by `Nat` reduction, not by a cast.

## 4. Interface axioms

None: a foundation rung over upstream definitions, no structure.

## 5. Axioms and names

RT1, `#print axioms`, all `[propext, Classical.choice, Quot.sound]`: `relativeHomologyProjection_surjective_of_subsingleton`, `relativeHomologyProjection_injective_of_subsingleton`, `relativeHomologyProjection_bijective_of_eq_empty`, `subsingleton_relH_compl_planeOrigin`, `subsingleton_relativeCohomology_compl_planeOrigin`, `subsingleton_homology_compl_planeOrigin_of_H'`, `subsingleton_homology_three_compl_planeOrigin`, `planeOrigin_relativeHomologyProjection_surjective`, `exists_restrict_complexLocalOrientation`, `subsingleton_homology_four_compl_planeOrigin`, `planeOrigin_relativeHomologyProjection_bijective`, `existsUnique_restrict_complexLocalOrientation`, `exists_planeDegree_eq_eval`, `eval_planeOrigin_of_restrict`. The rung's statement is the hypothesis `hμ` of `planeDegree_eq_eval_of_restrict` token for token (lines 402 to 403 of `CycleClassSignTestP2.lean`), under `∃`. `tools/check.py --no-build`: accepted (the modules are not scanned until phase 2).

**Independence (RT2).** The corollary module imports `CycleClassSignTestP2`, which imports the multiplicativity proof for its positive control, and that guard's roots do not include `planeDegree_eq_eval_of_restrict`. RT2 ran the guard's own import-closure walk on the new roots and on `planeDegree_eq_eval_of_restrict`: none reaches the multiplicativity proof. So the reading deg = ⟨Ψ −, [ℙ²]⟩ is independent of `cycle-class-multiplicative`, which is what makes deg ([L₀] ∪ [L₁]) = 1 a two-input fact (section 6). Change E adds those roots to a guard.

## 6. Conventions

| Convention | Used by | Truth depends on it? | Row |
|---|---|---|---|
| Sheaf Hⁿ of the open to singular Hⁿ(V, V ∖ ⊤) (support-⊤ transport) | `subsingleton_relativeCohomology_compl_planeOrigin` | no: an `AddEquiv` composite (`relHAddEquivSupportedSectionsHomology` then `complexSupportInjectiveSectionCohomologyEquiv projectivePlane ⊤ V n`, which takes `openParacompactSpace` internally), used only through `Equiv.subsingleton`; a sign or scalar in it is invisible | "Cohomology of an open" |
| `relH` with empty second open | `subsingleton_relH_compl_planeOrigin` | no: injectivity of `forget` (upstream `relH.forget_injective_of_eq_bot`), vanishing only | same |
| Universal coefficients | step 4 | no: `relativeCohomologyEquivDualHomology` used only to transport vanishing, then `Module.subsingleton_dual_iff` over the field ℚ | "Universal-coefficient evaluation" |
| Homology sequence of a pair | the pair lemmas | no: exactness at two spots; the connecting map's sign drops out (its target is zero) | none needed |
| Complex orientation of ℂ² | the literature reading of μ | yes, for μ = [ℙ²] and Ψ [pt] = PD(pt); no, for every Lean statement of the rung | "Complex orientation of ℂ^p" (pinned); new row "Fundamental class of ℙ²(ℂ)" |
| Ψ and its pairing | `exists_planeDegree_eq_eval` | signs (−1)^n, (−1)^{n(n±1)/2} are +1 at n = 4; T against Ψ fixed by `forgetRel_supportedEquivPair` | "Sheaf–singular comparison Ψ", "Degree on H⁴(ℙ²)" |

**Is the support-⊤ transport a sound substitute for "Ψ on the open"?** Yes. Upstream's `rationalCohomologyAddEquivSingularCohomology` is stated for X(ℂ) only; the transport with support ⊤ on V lands in singular Hⁿ(V, V ∖ ⊤) = Hⁿ(V, ∅), and `homologyEmptySubspaceIso` (on the homology side, after universal coefficients) removes the empty second space. Only `Subsingleton` passes along it, so no hidden scalar or sign can matter. The ledger note's "Ψ on the open" should be reworded to say this (change B).

**What this adds to the sign question at a = b = 1.** The sign-test red team found that the checked pair deg [pt] = 1, [L₀] ∪ [L₁] = [pt] constrains only a product: with upstream's [Lᵢ] = cᵢ · h, ε · c₀ · c₁ = 1, ε = +1, so c₀ · c₁ = 1, *conditional on reading `planeDegree` as ⟨−, [ℙ²]⟩*. This rung removes the condition and nothing else:

- Now unconditional, given the pinned orientation row: ⟨Ψ [pt], [ℙ²]⟩ = 1, so upstream's point class on ℙ², read through Ψ, is the literature's Poincaré dual of a point, sign +, exactly (row "Sheaf–singular comparison Ψ" fixes Ψ itself). This excludes every convention whose sign is −1 in codimension 2, for example (−1)^{p(p−1)/2} or (−1)^{p(p+1)/2} on classes of codimension p.
- Still c₀ · c₁ = 1 only. A uniform (−1)^p on classes of codimension p, which is what a conjugate normal orientation would produce, gives c₀ = c₁ = −1 and [pt] with sign +, and satisfies everything checked. The sign-test conclusion that only c₀ · c₁ is pinned stands.
- Correction to the sign-test note (change G there, repeated in this rung's ledger note): naturality under the coordinate swap of ℙ² gives c₀ = c₁ and so c₀² = 1, which leaves c₀ = ±1; it does not separate the sign. Only an evaluation of [L] on a fundamental class of a line (deg ([L] restricted to a transversal line) = 1) or the divisor–Chern identity read against c₁(𝒪(1)) fixes it.

`docs/conventions.md`: new row "Fundamental class of ℙ²(ℂ)"; row "Degree on H⁴(ℙ²)" now records the discharge; the tail of row "Transversal product of cycle classes" drops "conditional on the literature reading of the degree" and records the (−1)^p blind spot and the swap correction.

## 7. Equality first

The rung asserts an exact equality in H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ pt; ℚ) between the image of μ and upstream's local orientation; no scalar. `existsUnique_…` is exact. `exists_planeDegree_eq_eval` and `eval_planeOrigin_of_restrict` are exact identities. No inclusion is involved.

**`∃` or `∃!` for the posted rung.** The rung as titled ("Some μ") is the `∃`, which is what `hμ` needs. The literature's characterization, and the docstrings' "the fundamental class", need `∃!`, which costs one import of `CycleClassSignTestP2` (read from its `.olean`, 5 s, not the 4.5 min elaboration) and RT2 shows that import does not pull in the multiplicativity proof for these roots. Post the rung with the corollary module as its `module` and both files' declarations, headline `existsUnique_restrict_complexLocalOrientation` (change B). This strengthens the rung; the `∃` stays as a named declaration. Moving the H⁴ vanishing into the rung module would duplicate three Mayer–Vietoris steps for no gain.

## 7b. Non-vacuity

Smallest test that fails if the rung were trivially true: `eval_planeOrigin_of_restrict` (⟨Ψ [pt], μ⟩ = 1), which exists. From it, RT1 proves in 3 lines that every μ with `hμ` is nonzero and in 5 lines that `complexLocalOrientation projectivePlane 2 planeOriginPoint ≠ 0`. Change E proposes keeping the first as a named lemma.

## 8. Pin drift

Checked at `2ead713`, the current pin; no drift. For the next bump, diff: upstream `complexLocalOrientation`, `span_complexLocalOrientation_eq_top`, `pointComplementPair`, `relativeHomologyProjection`, `relativeChainProjection`, `relativeChainShortComplex`, `relativeChainShortComplex_shortExact`, `homologyEmptySubspaceIso` (and `emptySubspacePair`, which must stay `TopPair.ofSubset ∅` for the `subst` in `relativeHomologyProjection_bijective_of_eq_empty`), `relH.forget_injective_of_eq_bot`, `relHAddEquivSupportedSectionsHomology`, `ambientRationalInjectiveComplex` and its three companions, `complexSupportInjectiveSectionCohomologyEquiv`, `neighborhoodSupportComplementPair`, `relativeCohomologyEquivDualHomology`, `openParacompactSpace`; Mathlib `ShortComplex.ShortExact.homology_exact₂`, `homology_exact₃`, `Exact.epi_f`, `Exact.mono_g`, `Module.subsingleton_dual_iff`; the ladder's `planeOrigin_support_eq_singleton`, `subsingleton_H'_three_compl_planeOrigin`, `subsingleton_H'_compl_planeOrigin`, `planeDegree_eq_eval_of_restrict`. A change of sign or scalar in any equivalence of steps 2 to 5 cannot alter truth (vanishing only); a change of `complexLocalOrientation` changes what the rung means, and the rows "Complex orientation of ℂ^p" and "Fundamental class of ℙ²(ℂ)" must be rechecked then.

## Findings

1. **Correct and exact.** The route (sheaf H³(V) = 0, `relH` injects, support-⊤ transport, universal coefficients and a zero dual, empty second space, the pair sequence) is sound; every step but the last is a transported vanishing, the last is exactness. No sign enters any Lean statement.
2. **μ is the literature's [ℙ²], at one point, given the pinned orientation row.** Uniqueness (`existsUnique_…`) is the literature's one-point characterization; existence alone (the rung module) is half of it, and its module docstring says "the one-point characterization" (change A).
3. **The reading is now unconditional.** `exists_planeDegree_eq_eval` removes the condition the sign-test red team recorded (its finding 6). Consequence: upstream's [pt] on ℙ² is +PD(pt) exactly, which excludes conventions with sign −1 in codimension 2.
4. **Nothing changes about c₀ and c₁ separately.** Only c₀ · c₁ = 1 is pinned; a uniform (−1)^p is invisible. The coordinate swap would give c₀ = c₁, still not the sign (section 6). The ledger note inherited from change G of the sign test says otherwise (change B).
5. **The orientation convention is a blind spot of this rung.** A real-parts-first ordering of ℂ² would flip μ and [pt] together and leave every Lean statement true; the pinned row carries it, and the new conventions row says so.
6. **The one-point reading suffices.** Restriction to the local orientation at every other point is optional (H).
7. **Independence from the multiplicativity proof holds** for every new root and for `planeDegree_eq_eval_of_restrict` (RT2); the committed guard in `CycleClassSignTestP2` does not check the latter.
8. **The general pair lemmas are general.** `relativeHomologyProjection_{surjective,injective}_of_subsingleton` and `relativeHomologyProjection_bijective_of_eq_empty` hold for any pair; similar `homology_exact₂`/`homology_exact₃` uses exist in `HodgeLadder/Normalization/GermNoReg.lean` and in the port, none on `relativeChainShortComplex`. Upstream candidates (F).

## Changes

**A (required). Rung-module docstring.** In the module docstring of `HodgeLadder/Tests/ProjectivePlaneFundamental.lean`, replace "This is the hypothesis `hμ` of `planeDegree_eq_eval_of_restrict` (rung `cycle-class-sign-test-p2`), and the one-point characterization of the fundamental class `[ℙ²]` in the literature." with: "This is the hypothesis `hμ` of `planeDegree_eq_eval_of_restrict` (rung `cycle-class-sign-test-p2`) and the existence half of the literature's one-point characterization of the fundamental class `[ℙ²]`; uniqueness is `existsUnique_restrict_complexLocalOrientation` in `HodgeLadder.Tests.ProjectivePlaneFundamentalDegree`." In the paragraph "No sign or normalization enters", append: "Reading `μ` as the fundamental class of the complex orientation uses that `complexLocalOrientation` at the point is the complex local generator (row \"Complex orientation of ℂ^p\" of `docs/conventions.md`, pinned); no statement here can detect a fault there."

**B (required, phase 2). Ledger.** `module`: `HodgeLadder.Tests.ProjectivePlaneFundamentalDegree` (it imports the rung module, so the checker reaches every declaration); `declarations`: all 14 of section 5 plus `planeOriginCompl`; both modules imported from `HodgeLadder.lean`. Title: "Exactly one μ ∈ H₄(ℙ²(ℂ); ℚ) restricts to complexLocalOrientation projectivePlane 2 [0 : 0 : 1] (the one-point characterization of [ℙ²]); it discharges the hypothesis of planeDegree_eq_eval_of_restrict, so deg α = ⟨Ψ α, μ⟩ for every α". Note: "Existence from H₃(ℙ²(ℂ) ∖ pt; ℚ) = 0, uniqueness from H₄(ℙ²(ℂ) ∖ pt; ℚ) = 0: sheaf vanishing (p2-point-class-nonzero, cycle-class-sign-test-p2), carried to singular cohomology of the open by upstream's support-⊤ transport complexSupportInjectiveSectionCohomologyEquiv (vanishing only, so no scalar matters), universal coefficients over ℚ, and the homology sequence of the pair. No sign enters. μ is the literature's [ℙ²] for the complex orientation given row \"Complex orientation of ℂ^p\"; with deg [pt] = 1 this gives Ψ [pt] = PD(pt) exactly. The scalars of [L₀], [L₁] against the line class still satisfy only c₀ · c₁ = 1: a uniform (−1)^p in codimension p is invisible; naturality under the coordinate swap would give c₀ = c₁ = ±1, and the sign needs [L] evaluated on a fundamental class of a line or the divisor–Chern identity against c₁(𝒪(1)). Not proved: that μ restricts to complexLocalOrientation at every other point (not needed for the one-point reading)."

**C (required). Docstring of `existsUnique_restrict_complexLocalOrientation`.** Replace with: "**The fundamental class of ℙ²(ℂ)**: exactly one `μ ∈ H₄(ℙ²(ℂ); ℚ)` restricts to the complex local orientation at `[0 : 0 : 1]`. On a connected manifold this one-point condition is the literature's characterization of the fundamental class of the orientation through that local generator; that the generator is the complex one is row \"Complex orientation of ℂ^p\" of `docs/conventions.md`. That `μ` restricts to `complexLocalOrientation` at every other point is not proved here."

**D (required). Sketch, "Signs and normalization".** After "That reading also needs `complexLocalOrientation` to be the literature's local orientation at pt; the row \"Complex orientation of ℂ^p\" of `docs/conventions.md` pins it, outside this rung." add: "Unlike deg [pt] = 1, the reading is sensitive to that row: a real-parts-first ordering of ℂ² ((−1)^{d(d−1)/2} = −1 at d = 2) would make μ = −[ℙ²] and upstream's [pt] = −PD(pt), with every statement here still true. The conjugate orientation is invisible ((−1)² = 1)." In the paragraph that begins "The \"Ψ on the open\" of the ledger note is step 3", replace "hence bijective, and μ unique." with "hence bijective, and μ unique; the red team checked (RT2) that none of these roots reaches the multiplicativity proof."

**E (optional). Non-vacuity lemma and guard roots.** In the corollary module, after `eval_planeOrigin_of_restrict` (RT1 elaborated this body):

```lean
/-- A class restricting to the complex local orientation at `[0 : 0 : 1]` is nonzero. -/
theorem ne_zero_of_restrict_complexLocalOrientation
    (μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2))
    (hμ : (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
      complexLocalOrientation projectivePlane 2 planeOriginPoint) : μ ≠ 0 := by
  rintro rfl
  have := eval_planeOrigin_of_restrict 0 hμ
  simp at this
```

Separately, when `CycleClassSignTestP2.lean` is next touched, add `HodgeLadder.Tests.planeDegree_eq_eval_of_restrict` to the roots of its independence guard (RT2 found it clean).

**F (phase 2). `docs/gaps.md`, "General lemmas kept local".** List `relativeHomologyProjection_surjective_of_subsingleton`, `relativeHomologyProjection_injective_of_subsingleton`, `relativeHomologyProjection_bijective_of_eq_empty` as upstream candidates (statements about any `TopPair`, next to `relativeChainShortComplex_shortExact` and `homologyEmptySubspaceIso`), as the sketch plans.

**G (optional). `docs/references.md`.** Extend the `Hatcher2002` row's §3.3 description with: "orientations, Hₙ(M; R) → Hₙ(M, M ∖ x; R) an isomorphism for a closed connected R-orientable n-manifold, and the fundamental class (Theorem 3.26; unverified numbering)".

**H (new rung, optional). `p2-fundamental-class-every-point`:** for every y ∈ ℙ²(ℂ), the image of μ in H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ y; ℚ) is `complexLocalOrientation projectivePlane 2 y`. Route: the set of good points is open and closed, and ℙ²(ℂ) is connected. On upstream's chart neighborhood N = `complexLocalOrientationNeighborhood projectivePlane 2 y`, μ and `complexLocalOrientationNeighborhoodClass` both live in H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ N; ℚ), and the second restricts to `complexLocalOrientation` at every z ∈ N (`complexLocalOrientationNeighborhoodClass_restrict`); if that group maps injectively to H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ z; ℚ) for every z ∈ N, μ is good at one point of N exactly when it is good at all of them. That injectivity is not at the pin in this form. It tests upstream's coherence and the full literature definition; it cannot change any sign on ℙ², since H⁴ is one-dimensional and the degree is pinned by one value. Depends on `p2-fundamental-class`.
