# Red team: `fundamental-class-unit`

Date: 2026-11-26. Worktree at `c486870` plus the uncommitted `HodgeLadder/Tests/FundamentalClassUnit.lean` (331 lines) and the sketch section "fundamental-class-unit: statement" in `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713` (lakefile, manifest and the checkout under `.lake/packages` agree), Lean and Mathlib `v4.35.0-rc4`. Statement and proof reviewed together (phase 1 finished both).

Read: the Lean file, the sketch section, the ledger entries of `fundamental-class-unit`, `cycle-class-germ`, `one-is-kappa`, `cycle-class-multiplicative-codim-zero`, `cycle-class-germ-point`, decisions 0009, 0010 and 0011, `docs/conventions.md`, `docs/references.md`, `docs/gaps.md`, the checked `HodgeLadder/Cup/{Product,Yoneda,OneIsKappa,KappaCancel,SingularCup,RelativeCup,SupportedPairForget}.lean` and `HodgeLadder/Normalization/Germ.lean`, and upstream at the pin: `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean`, `Definitions/AlgebraicTopology/LocalHomology/{FundamentalClass,ComplexClass,NormalProjectionCoclass}.lean`, `Definitions/AlgebraicGeometry/Cycle/Local/Purity.lean`, `Lemmas/AlgebraicTopology/LocalHomology/FundamentalClassGenerator.lean`, `Lemmas/AlgebraicGeometry/Hodge/Filtration.lean`, and in `Other`: `Hodge/Filtration.lean`, `Cohomology/RationalDegreeZero.lean`, `Hodge/CodimensionZero{Comparison,Nonvanishing}.lean`, `Cycle/Component/CoclassNonzero.lean`.

Scratch (worktree root, compiled with `lake env lean`, deleted afterwards): RT1 prints axioms of all twelve declarations, prints `cupSing` and `cohIso`, and tries trivial proofs of the rung; RT2 instantiates the rung at Spec ℂ and at ℙ², proves the sign test [X] ≠ −1, the scalar test (c = 1 for every c with [X] = c • 1), [X] ∪ [X] = [X], and uniqueness of the left unit; RT3 imports `HodgeLadder` and the new module together. The new module itself was recompiled from source (`lake env lean`, 44 s, no output).

**Verdict: pass with changes.** [X] = 1 stands at the pin: exact, sign +, no scalar, standard axioms. The changes are about where the general lemmas live, one misattribution in two docstrings, one stale docstring in a checked module, one added sign-visible test, the ledger record, a conventions row (added by this pass) and a `docs/gaps.md` row.

## 1. Is this the statement the literature makes?

Literature: for X smooth, connected, projective of dimension n, the cycle class of X itself is the unit, cl([X]) = 1 ∈ H⁰(X; ℚ); equivalently the fundamental class [X] ∈ H_{2n} is Poincaré dual to 1 (`Fulton1998` ch. 19, `Voisin2002` vol. I ch. 11; section numbers unverified). The Lean statement:

```lean
theorem cycleComponentSheafClass_genericPoint_eq_one (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) =
      (one X : H^(2 * 0)(X; ℚ))
```

| Literature | Lean | Source | Check |
|---|---|---|---|
| X smooth projective, connected | `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]` | upstream statement library | the three instances `cycleComponentSheafClass` itself requires; integral gives connected X(ℂ) through upstream `ComplexPoint.connectedSpace` (`Other`) |
| the cycle X, codimension 0 | `genericPoint X.left` with `coheight_genericPoint_eq_zero X : Order.coheight _ = ↑0` | Mathlib, upstream `Other` (a proof term) | p is forced to `0`; the `ℕ∞` coercion is harmless because the index p is the `ℕ` on the right |
| cl([X]) | `cycleComponentSheafClass X x hx` = `forgetSupport` of `cycleComponentSupportedInjectiveClass`, the unique supported class whose restriction to X ∖ Z_sing is the normalized coclass section (`Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean:88`) | upstream statement library | the class of record: `algebraicCycleClassSpan` is the span of exactly these |
| 1 ∈ H⁰ | `one X := oneY ↧(ComplexPoint X)`, the unit of the ladder's `cup` (decision 0009) | `HodgeLadder.Cup.Product` | two-sided unit (`one_cup`, `cup_one`, checked), so it is the unique unit (RT2: any left unit `e` equals `one X`, two lines). `one_eq_fieldCohomologyUnit` identifies it with upstream's `fieldCohomologyUnit ℚ X = fieldCohomologyClass ℚ X 1`, the constant class 1 |
| H⁰ | `H^(2 * 0)(X; ℚ)`, ascription of `one X : H^0` | upstream notation | `2 * 0` reduces to `0`; the statement elaborates with no cast |

Upstream's normalization at p = 0 reads: the local class on the smooth locus evaluates to 1 on the complex orientation class of the normal space ℂ⁰ (docstring of `cycleComponentSheafClass`). That class, `standardComplexLocalClass ℚ 0`, is by definition the pullback along the one-point map `standardComplexRealPairIso 0` of `standardLocalClass ℚ 0`, the class of the unique 0-simplex of ℝ⁰ with coefficient 1 (`FundamentalClass.lean:226` with `standardLocalCycle ... 1`). So upstream's definition agrees with the literature's normalization, which is what the rung confirms by proof. Upstream at the pin has only the span forms in codimension 0 (`algebraicCycleClassSpan_zero_eq_top`, `cycleComponentSheafClass_genericPoint_ne_zero`); no `[X] = 1` exists upstream, so the rung is new content and duplicates nothing.

## 2. Can the hypotheses be satisfied?

Yes. RT2 elaborates

```lean
example : ∃ X : Over (Spec ↧ℂ), ∃ _ : IsIntegral X.left, ∃ _ : Smooth X.hom,
    ∃ _ : IsProjective X.hom,
    cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) =
      (one X : H^(2 * 0)(X; ℚ)) := by
  obtain ⟨X, h1, h2, h3⟩ := exists_smooth_projective_integral
  exact ⟨X, h1, h2, h3, cycleComponentSheafClass_genericPoint_eq_one X⟩
```

and the rung at `projectiveSpace 2` (instances from `HodgeLadder.Tests.ProjectivePlane`), a positive-dimensional instance.

## 3. Is the conclusion trivially true?

No. RT1: `first | rfl | simp | decide | exact Subsingleton.elim _ _ | (unfold one oneY; rfl)` leaves the goal unsolved. H⁰(X; ℚ) is a line, not a subsingleton (`rationalCohomologyUnit_ne_zero`), so the only content is the scalar, and RT2 shows the statement pins it:

- sign test: `cycleComponentSheafClass X (genericPoint X.left) _ ≠ -(one X)`, from the rung, `one_eq_fieldCohomologyUnit` and `rationalCohomologyUnit_ne_zero` (9 lines);
- scalar test: `∀ c : ℚ, [X] = c • one X → c = 1` (`rt_scalar_pinned`, 12 lines, standard axioms).

Every hypothesis is used: the three instances by `cycleComponentSheafClass`; inside the proof, connectedness for the line, `T2Space` and paracompact opens for Ψ.

**Hidden scalars.** The final equality mentions only upstream's [X] and `one X`, so no intermediate object can carry a scalar into it. The intermediates were still checked for consistency, since a wrong normalization there would make the proof fail, not succeed:

| Place | Why no scalar hides |
|---|---|
| Ψ = `rationalCohomologyAddEquivSingularCohomology` | enters on both sides of `Ψ [X] = c • Ψ (one X)`; the proof needs only additivity (`map_rat_smul`), not injectivity, and no normalization of Ψ |
| `oneSing` | pinned twice, independently: as the unit of `cupSing` (`cupSing_oneSing`, through `cup_singular_comparison` at p = 0) and as the class whose value on the vertex is 1 (`forgetRel_eq_oneSing_of_standardLocalClass_zero`). A scaled `oneSing` would break one of the two |
| `cohIso` | `homologyMapIso (dualIsoYoneda _)`, degreewise `ModuleCat.homLinearEquiv` (row "Singular cup product"); RT1 printed both definitions |
| `constSingularCocycle ℚ (𝟙 (𝟙_ _))` | the cocycle with value `1 ∈ ℚ` on every vertex; `oneSing_ne_zero` evaluates it at a vertex and gets `1` |
| ℂ⁰ ≅ ℝ⁰ | `standardComplexRealPairIso 0` is a map of one-point pairs (both subspaces empty); `relativeHomologyMap ℚ 0 iso.inv (standardLocalClass ℚ 0) = standardComplexLocalClass ℚ 0` is `rfl` (the `Nat.mul_comm 0 2 ▸` cast reduces) |
| `normalizedDual` | `Classical.choose` of a functional with value 1 at the class; the proof uses only that value plus `span_standardLocalClass_zero_eq_top`, so the choice cannot matter |

## 4. Interface rung

Not applicable: no structure, no assumed `Prop` input.

## 5. Checker and axioms

RT1, `#print axioms` on all twelve declarations (`cycleComponentSheafClass_genericPoint_eq_one`, `one_eq_fieldCohomologyUnit`, `exists_cycleComponentSheafClass_genericPoint_eq_smul_one`, `oneSing`, `cupSing_oneSing`, `oneSing_cupSing`, `cohomologyMap_oneSing`, `oneSing_ne_zero`, `rationalCohomologyAddEquivSingularCohomology_one`, `exists_mem_cycleComponentSmoothSupportAmbientOpen`, `forgetRel_eq_oneSing_of_standardLocalClass_zero`, `forgetRel_chartNormalProjectionCoclass_zero`): each `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, `axiom`, `unsafe` or heartbeat options in the file. The sketch counts eleven declarations; there are twelve with `oneSing`.

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`. The module is not yet imported from `HodgeLadder.lean` nor named in the ledger, so the checker did not see it; RT3 imports `HodgeLadder` and the module together without error, so the root import will not clash. The prover reruns the full `python3 tools/check.py` after change E.

The named declaration is the ledger's: its type, printed by `#check`, is the ledger title with `_ = coheight_genericPoint_eq_zero X`.

## 6. Conventions

| Convention used | Where | Row | Truth depends on it? |
|---|---|---|---|
| (−1)^{pq} of `cup_singular_comparison` | `rationalCohomologyAddEquivSingularCohomology_one`, p = q = 0 | "Cup product" | no at p = 0: `Int.negOnePow_zero` |
| Ψ | same | "Sheaf–singular comparison Ψ" | no: enters additively on both sides (finding 3) |
| `cohIso`, Tau Ceti unit law with unitors `λ`, `ρ` | `cupSing_oneSing`, `oneSing_cupSing` | "Singular cup product" | yes for `Ψ (one X) = oneSing`; no sign (`unitors_equal`, `unitors_inv_equal`) |
| Fundamental-class normalization (value 1 on the orientation class) | `forgetRel_chartNormalProjectionCoclass_zero` via `normalizedDual_apply_self` | "Fundamental-class normalization" | yes |
| Complex orientation of ℂ^p at p = 0; reference 0-simplex with coefficient +1 | `standardComplexLocalClass ℚ 0`, `standardAmbientClassZero_projection` | "Complex orientation of ℂ^p" (sign (−1)^d, d = 0) and the new row below | yes: coefficient −1 would give [X] = −1 |
| Universal-coefficient evaluation ⟨[φ], [x]⟩ = φ(x) | `relativeCohomologyEquivDualHomology_normalizedRelativeCoclass`, `linearDualHomologyEquiv_homologyπ_apply` | "Universal-coefficient evaluation" | yes, no sign |
| Pair maps (W, W ∖ Z) → (⊤, ⊤ ∖ Z) → (X, X ∖ Z) | `neighborhoodSupportInclusionPairMap`, `ofSubsetIsoNeighborhoodTop` | "Pair spellings of (X, X ∖ Z)" | no sign: identity on points |
| Forgetting supports against Ψ | `forgetRel_supportedEquivPair`, `supportedEquivPair_eq_transport` | "Supported comparison Φ" | no sign (`supported-pair-forget`) |
| Germ identity | `transport_supportedClass_eq_chartNormalProjectionCoclass` at p = 0 | "Holomorphic adapted chart", "Normalization iso against the singular transport" | no sign; at p = 0 holomorphy is vacuous |
| Unit of `cup`; κ = `n ↦ n`; upstream constant class `zmultiplesAddHom ℚ 1` | `one_eq_fieldCohomologyUnit` | "Rational Ext normalization", "Integer-to-rational coefficients" | yes for the identification with upstream's unit |

Missing row added to `docs/conventions.md`: "Degree-zero orientation and the unit". It records that the orientation class of ℂ⁰ is the point with coefficient +1, that the singular unit is the constant cocycle 1, and that Ψ(1) = 1 with no sign. These three facts decide [X] = +1 and are not stated in any existing row.

**Where the sign is decided (finding A).** The docstring of `forgetRel_eq_oneSing_of_standardLocalClass_zero` says "This is where the sign of `[X]` is decided" and credits `standardLocalClass_zero_epsilon`; the sketch says the same ("The decisive input is upstream's `standardLocalClass_zero_epsilon`"). The proof does not call that lemma directly. The value 1 comes from three facts. `hγ` (upstream `normalizedDual_apply_self`) gives the normalization. `standardAmbientClassZero_projection` says `standardLocalClass ℚ 0` is the vertex with coefficient 1, by definition. `SSet.ιChainComplex_constCochain` says the constant cocycle is 1 on that vertex. The augmentation lemma enters only through `span_standardLocalClass_zero_eq_top` → `standardLocalClass_zero_ne_zero`, that is, for nonvanishing. The two statements are the same fact read differently: ε = 1 holds exactly because the reference 0-simplex has coefficient +1. The attribution should still name the lemma the proof uses; see change A.

## 7. Equality first

The rung is an identity and is proved exactly: `c = 1` is derived, and the scalar test in RT2 confirms no other c is compatible. The sign + is in the theorem docstring ("Exact, sign `+`, no scalar"). Change A adds the conventions row reference that the docstring rule asks for.

## 7b. Non-vacuity

Smallest test lemma that would fail if the statement were trivially true: `one X ≠ 0`, i.e. upstream `rationalCohomologyUnit_ne_zero` with `one_eq_fieldCohomologyUnit`. It exists, and both sides are nonzero (`cycleComponentSheafClass_genericPoint_ne_zero`). The smallest sign-visible test, [X] ≠ −(one X), does not exist in the tree; RT2 proved it in 9 lines, and change C adds it.

## 8. Pin drift

Checked against `2ead713`, the current pin; no drift. For the next bump, add these inputs to the sketch's drift list, besides the ones it names. Upstream statement closure: `normalizedDual_apply_self`, `relativeCohomologyEquivDualHomology_normalizedRelativeCoclass` (`Lemmas/AlgebraicGeometry/Cycle/Local/Purity.lean`), `standardComplexLocalClass_ne_zero_for_chart` (`Lemmas/AlgebraicTopology/LocalHomology/ChartFundamentalClassGenerator.lean`), `cohomologyEquivDualHomology_relativeCohomologyToAbsolute`, `relativeCohomologyEquivDualHomology_relativeCohomologyMap` (`Lemmas/AlgebraicTopology/Singular/Cohomology.lean`), `openParacompactSpace` (`Lemmas/AlgebraicGeometry/ComplexPoint/ProjectiveParacompact.lean`), `standardLocalRelativeHomologyZeroε` and the definitions of `standardLocalClass`, `standardComplexLocalClass`, `standardComplexRealPairIso`, `chartNormalProjectionCoclass`. `Other`: `rationalCohomologyUnit_ne_zero` (`Cohomology/RationalDegreeZero.lean`), `coheight_genericPoint_eq_zero`, `cycleComponentAnalyticClosedSupport_genericPoint_eq_top` (`Hodge/CodimensionZeroComparison.lean`). Vendored Tau Ceti (port pin, not upstream): `singularCup_constSingularCocycle_left`, `_right`, `singularCohomologyMap_homologyπ_constSingularCocycle`, `iCycles_constSingularCocycle`, `SSet.ιChainComplex_constCochain`. The `rfl` for the ℂ⁰ → ℝ⁰ transport depends on `standardComplexLocalClass` keeping its `▸` spelling; a change breaks the build and cannot pass silently.

A change that could alter truth: a different coefficient or vertex convention for `standardLocalClass` at d = 0, or a normalization of `cycleComponentSmoothSupportCoclassSection` other than value 1. Both are definitions in the statement library and are covered by `HodgeLadder.CycleClass.Pins`; this rung is the test that would turn red.

## Findings and changes

A. **Sign attribution (docstrings).** In `forgetRel_eq_oneSing_of_standardLocalClass_zero` replace the last two sentences of the docstring by:

```lean
/-- **On the point `ℝ⁰`, a degree-`0` class normalized on the standard local class forgets to
the unit.** Upstream's `standardLocalClass ℚ 0` is the class of the unique singular point with
coefficient `1` (`standardAmbientClassZero_projection`), and the constant cocycle `1` takes the
value `1` there; `H₀(ℝ⁰; ℚ)` is a line (`span_standardLocalClass_zero_eq_top`, whose
nonvanishing input is the augmentation `standardLocalClass_zero_epsilon`). This is where the sign
of `[X]` is decided; `docs/conventions.md`, row "Degree-zero orientation and the unit". -/
```

In the theorem docstring of `cycleComponentSheafClass_genericPoint_eq_one`, append: "Conventions: rows \"Degree-zero orientation and the unit\", \"Fundamental-class normalization\" (`docs/conventions.md`)." In the sketch, replace "The decisive input is upstream's `standardLocalClass_zero_epsilon` (the standard local class of ℝ⁰ has augmentation 1)" by "The decisive inputs are upstream's normalization `normalizedDual_apply_self` and `standardAmbientClassZero_projection` (the standard local class of ℝ⁰ is the point with coefficient 1; equivalently, augmentation 1)". Also fix the declaration count (twelve).

B. **Move the general lemmas (decision 0011).** `oneSing`, `cupSing_oneSing`, `oneSing_cupSing`, `cohomologyMap_oneSing` and `oneSing_ne_zero` are facts about every space and `cupSing`; `rationalCohomologyAddEquivSingularCohomology_one` and `one_eq_fieldCohomologyUnit` are facts about the cup front for every X. Move them to a new module `HodgeLadder/Cup/SingularUnit.lean`, namespace `HodgeLadder.Cup`, imported by `HodgeLadder/Tests/FundamentalClassUnit.lean` and the root. No name clash: `oneSing` occurs nowhere else in `HodgeLadder/` or `port/`. Generalize `rationalCohomologyAddEquivSingularCohomology_one` from `[IsProjective X.hom]` to the hypotheses of `cup_singular_comparison`:

```lean
theorem rationalCohomologyAddEquivSingularCohomology_one (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] :
    rationalCohomologyAddEquivSingularCohomology X 0 (one X) =
      oneSing (TopCat.of (ComplexPoint X))
```

(same proof). Add a row to `docs/gaps.md`, "General lemmas kept local": `oneSing`, `cupSing_oneSing`, `oneSing_cupSing`, `cohomologyMap_oneSing`, `oneSing_ne_zero` (the class of the constant 0-cocycle 1 is a natural two-sided unit for the singular cup, nonzero on a nonempty space; any space) | `HodgeLadder.Cup.SingularUnit` | general singular cohomology, transported along `cohIso`; Tau Ceti has the cochain-level unit laws but no class in upstream's model | 2026-11-26. `forgetRel_eq_oneSing_of_standardLocalClass_zero` and `forgetRel_chartNormalProjectionCoclass_zero` are local-class facts; they may stay in the test module or go to `HodgeLadder/Normalization/`, and B does not require either. If the move is deferred, the rung still passes; record the deferral in the handoff.

C. **Sign-visible test.** Add to the test module (proved in RT2):

```lean
/-- Sign test for `fundamental-class-unit`: `[X] ≠ −1`. -/
theorem cycleComponentSheafClass_genericPoint_ne_neg_one (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) ≠
      -(one X : H^(2 * 0)(X; ℚ)) := by
  rw [cycleComponentSheafClass_genericPoint_eq_one]
  intro h
  have h2 : (2 : ℚ) • (one X : H^(2 * 0)(X; ℚ)) = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  rcases smul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · rw [one_eq_fieldCohomologyUnit] at h3
    exact rationalCohomologyUnit_ne_zero X h3
```

(`Nonempty (ComplexPoint X)` was found by instance search in RT2.)

D. **Stale docstring in a checked module.** `adaptedChart_genericPoint` (`HodgeLadder/Normalization/Germ.lean:128`) says `hyU` "needs `cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤`, which is not at the pin". That holds for an arbitrary `y`, but the new `exists_mem_cycleComponentSmoothSupportAmbientOpen` supplies a `y` with `hyU` for every component, and that is enough for every use that needs one point. Append: "For one point, `HodgeLadder.Tests.exists_mem_cycleComponentSmoothSupportAmbientOpen` gives a `y` with `hyU`." If B moves that helper, use the new name. Docstring only; no statement changes.

E. **Ledger and root.** Module path `HodgeLadder.Tests.FundamentalClassUnit`. It matches every other `kind: "test"` rung (`HodgeLadder.Tests.*`) and supersedes `tools/next.py`'s derived hint `HodgeLadder/Fundamental/Class/Unit.lean`. Import it from `HodgeLadder.lean`, set `module`, list the declarations (the rung, C's test, the helpers under their final names), status `checked`, contributors, and a note: "Exact, sign +. [X] = c • 1 on the line H⁰; Ψ(1) = oneSing; at a point of X ∖ Z_sing the germ identity and supported-pair-forget give the restriction of Ψ[X] as oneSing; c = 1. Sign decided by upstream's normalization against the point with coefficient 1 (conventions row Degree-zero orientation and the unit). Red team 2026-11-26: pass with changes (docs/sketches/fundamental-class-unit.redteam.md)." Add `cup-singular-comparison-absolute`, `cochain-cup-upstream` and `supported-pair-forget` to `depends_on` (all three used: `cup_singular_comparison`, `cupSing` and `cohIso`, `forgetRel_supportedEquivPair`). Update the roadmap row and the Status block. For the kill criterion of decision 0010, record that `fundamental-class-unit` holds: the front is not killed at codimension 0.

F. **Conventions row (done in this pass).** Added "Degree-zero orientation and the unit" to `docs/conventions.md`. If B renames `oneSing`'s namespace, update the row's declaration names.

Attempts that failed: `rfl`, `simp`, `decide`, `Subsingleton.elim`, and `unfold one oneY; rfl` on the rung (RT1). I found no reading of `one X`, of [X] or of any intermediate under which the identity holds for a reason unrelated to the orientation of the point. The rung stands.
