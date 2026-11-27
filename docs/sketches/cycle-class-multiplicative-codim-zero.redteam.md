# Red team: `cycle-class-multiplicative-codim-zero` (statement and proof)

Date: 2026-11-26. Worktree on branch `track/cycle-class-multiplicative-codim-zero` at `1daa64d`, plus the uncommitted `HodgeLadder/Tests/CycleClassMultiplicativeCodimZero.lean` (205 lines) and the sketch section "cycle-class-multiplicative-codim-zero: statement" in `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, the same in the worktree and on `main` (`6b45e4b`).

Read: the Lean file, the sketch section, the ledger entries of this rung, `cycle-class-multiplicative`, `fundamental-class-unit`, `cup-positive-degree-test-p2` and `p2-point-class-nonzero` (the last two on `main`), `HodgeLadder/Cycle/Multiplicative.lean` (statement of the main theorem), `HodgeLadder/Tests/FundamentalClassUnit.lean`, `docs/sketches/cycle-class-multiplicative.final.redteam.md` (sections 2, 7b, 8), `docs/sketches/fundamental-class-unit.redteam.md`, `docs/conventions.md`, `docs/references.md`, `docs/gaps.md`; upstream `Definitions/AlgebraicGeometry/Cycle/Support.lean` (`cycleComponent`, `cycleComponentι`), `Definitions/.../Cycle/Component/SingularClosedFiltration.lean`, `Lemmas/AlgebraicGeometry/Smooth/Equidimensional.lean` (`SmoothOfRelativeDimension.of_isIntegral`, `dim_eq`), `Other/AlgebraicGeometry/Cycle/Component/GenericPoint.lean`, `Other/AlgebraicGeometry/Hodge/CodimensionZeroComparison.lean`, `CodimensionZeroNonvanishing.lean`.

Scratch (non-module copies of the file under the worktree, compiled with `lake env lean`, deleted afterwards): RT1 prints axioms of all nine declarations and walks the transitive constant closure (types and values) of three theorems to see which named inputs each uses; RT2 tries trivial proofs, a short proof from `fundamental-class-unit`, nonvanishing of the right side, and a sign test; RT3 instantiates the rung on Spec ℂ and on ℙ².

**Verdict: pass with changes.** `[X] ∪ [X] = [X]` stands at the pin: exact, sign `+`, standard axioms, every hypothesis of `cycleComponentSheafClass_cup_of_transversal` discharged on every smooth integral projective `X`. The missing lemma is true and correctly proved. The changes correct two claims in the prose: the two routes to `[X] = 1` share `cycle-class-germ`, Ψ and the line `[X] = c • 1`, and the instance is sign-visible only for a sign that does not vanish into `1` at `a = b = 0`.

## 1. Is this the statement the literature makes?

Literature: the cycle class map is a ring homomorphism on transversal intersections, cl(Z) ∪ cl(W) = cl(Z ∩ W) (`Fulton1998` ch. 19, `Voisin2002` vol. I ch. 11; numbering unverified), and cl(X) = 1 is its unit. At Z = W = X the intersection is X, transversal for the trivial reason that the normal spaces are 0, and the identity reads cl(X) ∪ cl(X) = cl(X).

```lean
theorem cycleComponentSheafClass_genericPoint_cup_self (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cup (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (2 * (0 + 0)) (by ring) =
      cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero_add_zero X)
```

| Literature | Lean | Check |
|---|---|---|
| X smooth projective connected over ℂ | the three instances of upstream's `cycleComponentSheafClass` | no extra hypothesis: `d := dim X.left` and `SmoothOfRelativeDimension (dim X) X.hom` come from upstream's instance `SmoothOfRelativeDimension.of_isIntegral` |
| Z = W = T = X, codimension 0 | `genericPoint X.left`, coheight `↑0` (upstream `coheight_genericPoint_eq_zero`) and `↑0 + ↑0` for T | the second proof is `rw` then `rfl`; by proof irrelevance the right side is literally `[X]`: in RT2, `have h2 : cycleComponentSheafClass X η (coheight_genericPoint_eq_zero_add_zero X) = one X := cycleComponentSheafClass_genericPoint_eq_one X` is accepted by definitional unfolding |
| cl(X) ∪ cl(X) | ladder `cup` (Yoneda, decision 0009) in degree `2 * (0 + 0)` | the degree the main theorem produces; it reduces to 0 |
| = cl(X), sign + | `= cycleComponentSheafClass X η _` | (−1)^{(2·0)(2·0)} = 1 and the local + of `local-class-product` at a = b = 0 |

The statement is the literature's identity at its smallest instance. It is a direct application of the main theorem, so its content is that every hypothesis can be met (section 2) and that the conclusion is not degenerate (section 3).

## 2. Can the hypotheses be satisfied?

Yes, on every `X`, and concretely (RT3, elaborates with no errors):

```lean
example : ∃ X : Over (Spec ↧ℂ), ∃ _ : IsIntegral X.left, ∃ _ : Smooth X.hom,
    ∃ _ : IsProjective X.hom,
    cup (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (2 * (0 + 0)) (by ring) =
      cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero_add_zero X) :=
  ⟨point, inferInstance, inferInstance, inferInstance,
    cycleComponentSheafClass_genericPoint_cup_self point⟩
example := cycleComponentSheafClass_genericPoint_cup_self projectivePlane
example := genericPoint_transversal projectivePlane 2
```

with `point` from `HodgeLadder.Tests.Witness` (d = 0) and `projectivePlane` from `HodgeLadder.Tests.ProjectivePlaneLines` (d = 2, where the chart model `Fin 2 → ℂ` is not degenerate).

What each hypothesis tests at this instance:

| Hypothesis | Discharge | Content tested |
|---|---|---|
| `hx`, `hw`, `ht` | upstream `coheight_genericPoint_eq_zero`; `↑0 + ↑0` by `rfl` | Mathlib's order on scheme points (generic point is `⊤`), already pinned by row "Cycle components" |
| `hd` | `Nat.zero_le _` | none |
| `hT` | `Set.inter_self` | none: holds for every x = w = t |
| `hxreg`, `hwreg` | the missing lemma | real: X(ℂ) ∖ Z_sing(ℂ) = X(ℂ) for Z = X (section 3 below) |
| `htr` | `chartAt y`, `IsManifold.chart_mem_maximalAtlas`, `mem_chart_source`; both supports `⊤` | only that upstream's `IsManifold 𝓘(ℂ, Fin (dim X) → ℂ) ω` instance resolves at `d = dim X`; the coordinate conditions are conjunctions over `Fin 0` and the supports are all of X(ℂ) |

So the instance tests satisfiability of the main theorem's hypotheses on every `X`, with one hypothesis of real content (`hxreg`). It does not test `hT` on a proper intersection or the coordinate conditions of `htr`; `cycle-class-multiplicative-p2` does. The prover's sketch says this correctly. It is a meaningful test of non-vacuity of the hypotheses, and a weak test of the main theorem's mathematics, for the reason in section 3.

### The missing lemma

`cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top` is true: closure {η} = X, so upstream's `cycleComponent X η` is the reduced closed subscheme with vanishing ideal `vanishingIdeal ⊤ = X.nilradical = ⊥` (Mathlib `vanishingIdeal_top`, `nilradical_eq_bot` on the reduced, because integral, X); `isIso_subschemeι_iff_eq_bot` makes `cycleComponentι X η` an isomorphism; isomorphisms are smooth, so `cycleComponentι ≫ X.hom` is smooth, its smooth locus is `⊤`, upstream's `cycleComponentSingularClosedFiltration X η 0` (the complement of that smooth locus) is `⊥`, and the complement of the complex points over its image is `⊤`. Both `change` steps are accepted by the kernel, so they match upstream's definitions (`Definitions/AlgebraicGeometry/Cycle/Support.lean:47,53`, `SingularClosedFiltration.lean`). The helper needs only `IsIntegral`. Upstream has no such lemma: `Other/.../GenericPoint.lean` and `CodimensionZeroComparison.lean` give `cycleComponentAnalyticClosedSupport_genericPoint_eq_top` but nothing about the smooth locus (grep at the pin). Both belong upstream (change 4).

## 3. Is the conclusion true for a reason unrelated to the mathematics?

Trivial attempts, all fail (RT2):

| Attempt | Result |
|---|---|
| `rfl` on the rung | the two sides are not definitionally equal |
| `simp` on the rung | unsolved goal `cup [X] [X] 0 _ = [X]` |
| `exact Subsingleton.elim _ _` | no `Subsingleton H^(2 * (0 + 0))(X; ℚ)` instance |
| `rfl` on the missing lemma | not definitionally equal |
| `simp` on the missing lemma | no progress |

Both sides are nonzero: upstream `cycleComponentSheafClass_genericPoint_ne_zero X` elaborates against the right side with the `↑0 + ↑0` proof (RT2). No hypothesis is unused: the main theorem consumes all eight.

A short proof does exist, from another checked rung (RT2, accepted):

```lean
  have h := cycleComponentSheafClass_genericPoint_eq_one X
  have h2 : cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero_add_zero X)
      = (one X : H^(2 * 0)(X; ℚ)) := h
  rw [h2]
  exact one_cup _
```

That is `fundamental-class-unit` plus the unit law, the mathematics, so it does not make the statement wrong. It does mean the rung adds no new identity to the ladder: its value is the hypothesis check of section 2 and the second route to `[X] = 1` of section 6.

## 4. Interface rung?

No. The rung is a theorem about upstream's definitions; there is no structure and no axiom.

## 5. Checker and axioms

`python3 tools/check.py --no-build` at the worktree base: `ACCEPTED: all checks passed`. The new module is not yet imported from `HodgeLadder.lean` and the ledger entry names no declarations, so the checker does not see it yet (change 1). `#print axioms` in RT1, on all nine declarations of the file (`isIso_cycleComponentι_genericPoint`, `cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top`, `coheight_genericPoint_eq_zero_add_zero`, `genericPoint_support_eq_inter`, `genericPoint_support_subset_smoothSupportAmbientOpen`, `genericPoint_transversal`, `cycleComponentSheafClass_genericPoint_cup_self`, `cup_smul_one_smul_one`, `cycleComponentSheafClass_genericPoint_eq_one_of_cup_self`): `propext`, `Classical.choice`, `Quot.sound` for each. No `sorry`, `native_decide` or `set_option` in the file. The rung theorem applies `HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal`, the declaration the ledger names for `cycle-class-multiplicative`.

## 6. Conventions, and the two routes

Conventions used: the cup product (row "Cup product"), the coheight direction (row "Cycle components"), the transversal product with its sign chain (row "Transversal product of cycle classes"), and, for the derived `[X] = 1`, the unit `one X = fieldCohomologyUnit ℚ X` (row "Degree-zero orientation and the unit"). The rung is an equality, so its truth is sensitive to a sign; at a = b = 0 every sign in the chain is computed or the local `+` of `local-class-product` at the model ℂ⁰ × ℂ⁰ = ℂ⁰. No new convention enters.

**Independence of the two routes (RT1, transitive constant closure).**

| Input | `..._eq_one` (fundamental-class-unit) | `..._eq_one_of_cup_self` (this rung) |
|---|---|---|
| `cycleComponentSheafClass_genericPoint_eq_one`, `_ne_neg_one` | itself | not used |
| `forgetRel_chartNormalProjectionCoclass_zero`, `forgetRel_eq_oneSing_of_standardLocalClass_zero` | used | not used |
| `exists_cycleComponentSheafClass_genericPoint_eq_smul_one`, `exists_mem_cycleComponentSmoothSupportAmbientOpen` | used | used |
| `HodgeLadder.Normalization.transport_supportedClass_eq_chartNormalProjectionCoclass` (`cycle-class-germ`) | used | used (through the transversal theorem) |
| `HodgeLadder.Cup.cup_singular_comparison` (Ψ) | used (at p = 0) | used |
| `HodgeLadder.Cup.one_cup` | used | used |

The main theorem's closure does not contain `cycleComponentSheafClass_genericPoint_eq_one`; the derived theorem does not use the degree-0 evaluation lemmas. So the claim "does not use the `fundamental-class-unit` theorem" is right. The module docstring's "two independent routes" and the docstring "proved without its degree-`0` germ computation" overstate it: both routes identify the germ of `[X]` with the chart coclass `chartNormalProjectionCoclass` at c = 0 by the same `cycle-class-germ`, both pass through Ψ, and both start from `[X] = c • 1`, `c ≠ 0`. They differ only in the last step: `fundamental-class-unit` evaluates the degree-0 coclass on `standardLocalClass ℚ 0` (value 1, so c = 1); the transversal route uses that the coclass is idempotent under `relCup2` (`local-class-product` at a = b = 0), which with c ≠ 0 forces c = 1 without evaluating it. A defect in the shared inputs, for instance a germ identification off by a constant κ ≠ 1, would enter both routes. In Lean such a defect cannot coexist with both checked statements, but the agreement of the two routes is evidence only about the last step (changes 2, 3).

**Sign visibility.** The sketch's argument is right as stated for a constant sign: if the main theorem read `[Z] ∪ [W] = ε • [T]` with a fixed ε = ±1, then at codimension zero c² = ε c, c ≠ 0, so `[X] = ε • 1`, and ε = −1 contradicts the checked `[X] ≠ −1`. Equivalently, `cup [X] [X] ≠ −[X]` follows from the rung and upstream nonvanishing alone (RT2, standard axioms; change 5). The limitation: the instance detects only the value of the sign at a = b = 0. The two odd signs that `docs/conventions.md` names as the plausible failure modes of the product, (−1)^{ab} (real-parts-first ordering of ℂ^k ≅ ℝ^{2k}) and (−1)^a or (−1)^b (a conjugate normal coordinate in one chart), are all 1 there. Those need an instance with a, b ≥ 1 and [T] ≠ 0: `cycle-class-multiplicative-p2` with `p2-point-class-nonzero` (both checked on `main`). So the codimension-zero rung is a sign test for a global constant sign only. Conventions row "Transversal product of cycle classes" now says so.

## 7. Equality first

The rung is an identity, proved exactly: no scalar, sign `+` with (−1)^{0} = 1 computed inside the main theorem. `cycleComponentSheafClass_genericPoint_eq_one_of_cup_self` is also an exact identity (`[X] = 1`), proved from c(c − 1) = 0 and c ≠ 0, with `one X ≠ 0` from `rationalCohomologyUnit_ne_zero` on the nonempty X(ℂ).

### 7b. Non-vacuity

Smallest tests that fail if the statement were trivially true, in upstream's API:

| Test | Exact names | Exists? |
|---|---|---|
| right side nonzero | `cycleComponentSheafClass_genericPoint_ne_zero X` (upstream `Other`), at the `↑0 + ↑0` proof | yes; elaborates in RT2 |
| opposite sign false | `cup [X] [X] (2 * (0 + 0)) _ ≠ -cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero_add_zero X)` | not in the file; proved in RT2 in ten lines (change 5, optional) |
| `[X]` not a non-unit idempotent | `cycleComponentSheafClass_genericPoint_eq_one_of_cup_self` | yes, in the file |

## 8. Pin drift

None: the worktree, `main` and the build all use `2ead713`. New upstream names this rung depends on, to add to the drift list of the sketch: `cycleComponent`, `cycleComponentι` (their `vanishingIdeal`/`subschemeι` bodies, which the helper unfolds by `change`), `cycleComponentSingularClosedFiltration` at k = 0, `cycleComponentSmoothSupportAmbientOpen` (unfolded by `change`), `SmoothOfRelativeDimension.of_isIntegral`; `Other`: `coheight_genericPoint_eq_zero`, `cycleComponentAnalyticClosedSupport_genericPoint_eq_top`, `cycleComponentSheafClass_genericPoint_ne_zero`; Mathlib: `Scheme.isIso_subschemeι_iff_eq_bot`, `Scheme.IdealSheafData.vanishingIdeal_top`, `Scheme.nilradical_eq_bot`, `Scheme.Hom.smoothLocus_eq_top`, `genericPoint_closure`. A change to the body of `cycleComponent` or of the smooth ambient open would break the `change` steps, so drift there breaks the build.

**Merge drift.** `main` is two commits ahead (`b1da246`, `6b45e4b`): it appended an 85-line section to `docs/sketches/cycle-class-multiplicative.md` at the same place as this worktree's section, changed two rows of `docs/conventions.md` (not the row edited here) and the ledger. Rebase before posting; hand-merge the sketch.

## 9. Findings

1. **`[X] ∪ [X] = [X]` stands**, exact, sign `+`, standard axioms, every hypothesis discharged, on every X; instantiated on Spec ℂ and ℙ² (sections 2, 5).
2. **The missing lemma is true and correctly proved**, and belongs upstream with its helper (section 2).
3. **The instance is honest but thin.** `hd`, `hT` and the coordinate part of `htr` are vacuous at a = b = 0; `hxreg` and the atlas instance at `d = dim X` carry the content. The prover's sketch states this.
4. **No trivial proof.** `rfl`, `simp`, `Subsingleton.elim` fail; both sides are nonzero. A four-line proof from `fundamental-class-unit` and `one_cup` exists; it is mathematics. The rung adds a route and a hypothesis check; the identity itself already follows from `fundamental-class-unit` (section 3).
5. **"Two independent routes" overstates independence.** The derived `[X] = 1` does not use `fundamental-class-unit`'s theorem or its degree-0 evaluation, but both routes use `cycle-class-germ`, Ψ, `one_cup` and `[X] = c • 1`; they differ in the last step only (section 6).
6. **Sign visibility is for a constant sign only.** The argument from `[X] ≠ −1` is right for ε constant in (a, b); (−1)^{ab} and (−1)^a are invisible at a = b = 0 and are tested by the ℙ² instance (section 6). Conventions row updated.
7. **Record.** The ledger entry is `open` with no declarations, and the module is not imported from the root.

## Recommended changes

| # | Change | Where |
|---|---|---|
| 1 | Import the module from the root (`public import HodgeLadder.Tests.CycleClassMultiplicativeCodimZero`); ledger entry `checked`, `module: "HodgeLadder.Tests.CycleClassMultiplicativeCodimZero"`, the nine declarations (ten with change 5), note naming the red team and findings 5, 6; roadmap row; status block | `HodgeLadder.lean`, `ledger/ladder.json`, `docs/roadmap.md`, `CLAUDE.md` |
| 2 | Replace the module docstring paragraph beginning "Two independent routes." by the text below | `HodgeLadder/Tests/CycleClassMultiplicativeCodimZero.lean` |
| 3 | In the docstring of `cycleComponentSheafClass_genericPoint_cup_self`, replace "this is a consistency check of two independent routes: the unit law with the degree-`0` germ, against the transversal theorem." by "this is a consistency check of two routes that share `cycle-class-germ`, Ψ and `[X] = c • 1` and differ in the last step: evaluation of the degree-`0` chart coclass, against its idempotence under `relCup2`." In the docstring of `cycleComponentSheafClass_genericPoint_eq_one_of_cup_self`, replace "proved without its degree-`0` germ computation." by "proved without `forgetRel_chartNormalProjectionCoclass_zero`; it still uses `cycle-class-germ` through the transversal theorem." | same file |
| 4 | Add `isIso_cycleComponentι_genericPoint` and `cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top` to the "General lemmas kept local" table: statement-level facts about upstream's `cycleComponent` at the generic point, natural next to `cycleComponentAnalyticClosedSupport_genericPoint_eq_top` in upstream `Other/AlgebraicGeometry/Hodge/CodimensionZeroComparison.lean` | `docs/gaps.md` |
| 5 | Optional: add the sign test below to the file | same file |
| 6 | In the sketch section, replace "So the codimension-zero instance is sign-visible: if the transversal theorem carried a global sign ε = ±1" by "So the codimension-zero instance is sign-visible for a sign constant in (a, b): if the transversal theorem carried a fixed sign ε = ±1", and add after that sentence: "Signs that equal 1 at a = b = 0, such as (−1)^{ab} or (−1)^a, are invisible here; `cycle-class-multiplicative-p2` with `p2-point-class-nonzero` tests them." Replace "Two routes, and sign visibility" text "The rung reaches the same identity through the transversal theorem" by "The rung reaches the same identity through the transversal theorem, sharing `cycle-class-germ`, Ψ and `[X] = c • 1` with `fundamental-class-unit`". Add the drift names of section 8 | `docs/sketches/cycle-class-multiplicative.md` |
| 7 | Rebase on `main` and hand-merge the sketch | branch |

Text for change 2:

```lean
Two routes to `[X] = 1`. `fundamental-class-unit` proves `[X] = 1` by evaluating the degree-`0`
chart coclass on upstream's standard local class (`forgetRel_chartNormalProjectionCoclass_zero`);
with the unit law `one_cup` it gives `[X] ∪ [X] = [X]` at once. The transversal theorem gives the
same identity through relative cup products, `local-class-product` at `a = b = 0` and uniqueness
of supported classes; its import closure does not contain `fundamental-class-unit`. The routes
share `cycle-class-germ` (`transport_supportedClass_eq_chartNormalProjectionCoclass`), the
comparison `cup_singular_comparison`, `one_cup` and the line `[X] = c • 1`, `c ≠ 0`
(`exists_cycleComponentSheafClass_genericPoint_eq_smul_one`); they differ in the last step,
evaluation of the degree-`0` coclass against its idempotence under `relCup2`. Conversely, from the
transversal route, `c² = c` and `c ≠ 0` give `c = 1`:
`cycleComponentSheafClass_genericPoint_eq_one_of_cup_self` recovers `fundamental-class-unit`
without `forgetRel_chartNormalProjectionCoclass_zero`. Both sides of the identity are nonzero
(upstream `cycleComponentSheafClass_genericPoint_ne_zero`). The instance detects a sign of the
transversal theorem only if it is `−1` at `a = b = 0`; `(−1)^{ab}` and `(−1)^a` are `1` there
(`docs/conventions.md`, row "Transversal product of cycle classes").
```

Lean for change 5 (checked in RT2 under the name `rt_cup_self_ne_neg`, standard axioms):

```lean
/-- Sign test for `cycle-class-multiplicative-codim-zero`: the opposite sign is false,
`[X] ∪ [X] ≠ −[X]`, from the rung and upstream's `cycleComponentSheafClass_genericPoint_ne_zero`
alone (no use of `fundamental-class-unit`). -/
theorem cycleComponentSheafClass_genericPoint_cup_self_ne_neg (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cup (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (2 * (0 + 0)) (by ring) ≠
      -cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero_add_zero X) := by
  rw [cycleComponentSheafClass_genericPoint_cup_self]
  intro h
  have h2 : (2 : ℚ) • cycleComponentSheafClass X (genericPoint X.left)
      (coheight_genericPoint_eq_zero_add_zero X) = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  rcases smul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact cycleComponentSheafClass_genericPoint_ne_zero X h3
```

Its `-cycleComponentSheafClass ...` line runs past 100 characters; break it after `≠` when adding it.

## Sources

`Fulton1998` ch. 19 and `Voisin2002` vol. I ch. 11 (numbering unverified). Upstream declarations by name, read at `2ead713`.
