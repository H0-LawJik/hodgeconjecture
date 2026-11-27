# Red team: `cycle-class-multiplicative` (statement and proof)

Date: 2026-11-26. Branch `track/cycle-class-multiplicative` at `fa9303b` plus uncommitted work (`HodgeLadder/Cycle/Multiplicative.lean`, 625 lines; sketch section "cycle-class-multiplicative: statement and route"). `main` is one commit ahead (`b709544`, `p2-lines-transversal`). Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same in the worktree and on `main`. Target: `HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal` and its 19 route declarations.

Read: the module in full; the sketch section and the earlier plan red team (`cycle-class-multiplicative.redteam.md`); the statements used from `cup_singular_comparison'` (`HodgeLadder/Cup/CupSingular.lean`), `relCup2` and `forgetRel_relCup2` (`TriadCup.lean`), `supportedEquivPair` (`SupportedPair.lean`), `forgetRel_supportedEquivPair` and `supportedEquivPair_eq_transport` (`SupportedPairForget.lean`), `transport_supportedClass_eq_chartNormalProjectionCoclass` and `coclassSection_eq_singular` (`Normalization/Germ.lean`), `normalization_singular` (`Normalization/Singular.lean`), `chartUnionIso` and `chartNormalProjectionCoclass_eq_relCup2` (`Local/ClassProduct.lean`); at the pin `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean` (`cycleComponentSupportedClassNormalizationIso`, `cycleComponentSupportedInjectiveClass`, `cycleComponentSheafClass`), `Other/AlgebraicGeometry/Cycle/FundamentalClass.lean` (`cycleComponentSupportedInjectiveClass_unique`), `Lemmas/AlgebraicGeometry/ComplexPoint/Manifold.lean` (`localChart`, `isManifold_omega`); on `main` `HodgeLadder/Tests/ProjectivePlaneLines.lean`; `docs/conventions.md`, `docs/references.md`.

Scratch (directory `scratch_rt/` inside the worktree, deleted afterwards):

| File | What it does | Result |
|---|---|---|
| RT1 `RtAx.lean` | `#print axioms` on all 20 declarations of the module, `#check` of the main theorem | standard three axioms on every one; `ω` prints as `⊤ : WithTop ℕ∞`, the analytic level |
| RT2 `RtP2.lean` | a verbatim copy of `main`'s `ProjectivePlaneLines.lean` plus `import HodgeLadder.Cycle.Multiplicative`, then the main theorem applied to `projectivePlane`, `planeLine 0`, `planeLine 1`, `planeOrigin` | elaborates with no error; `rt_p2_instance` has the standard three axioms |
| RT3 `RtTriv.lean` | trivial proofs of the conclusion: `rfl`; `Subsingleton.elim`; `simp [cycleComponentSheafClass, HodgeLadder.Cup.cup]`; `simp_all` with `hT` only | all four fail (rfl: sides differ; no `Subsingleton` instance; unsolved goals twice) |
| RT4 | `python3 tools/check.py --no-build` in the worktree | `ACCEPTED: all checks passed` (the new module is not yet imported from the root, so the checker does not see it; RT1 covers it) |

A grep of the module finds no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by` or `extern`.

**Verdict: pass with changes.** [Z] ∪ [W] = [T] stands: exact, sign +, no scalar, with every hypothesis used and a Lean model of the hypotheses in positive codimension (RT2). The sign is inherited from checked inputs and is not forced by the proof: a − in `local-class-product` would turn the conclusion into [Z] ∪ [W] = −[T]. The changes below concern the record (ledger, docstring citations, a dependency list that overstates what the proof uses) and one cheap corollary. None weakens the statement.

## 1. Is this the statement the literature makes?

Literature: for X nonsingular, the cycle map A^*(X) → H^{2*}(X; ℚ) is a ring homomorphism [`Fulton1998` Cor. 19.2, numbering unverified], and when Z and W meet transversally along an integral T the intersection product is [T] with multiplicity one [`Fulton1998` §8.2, numbering unverified]. The topological form for complex submanifolds meeting transversally: the class of Z ∩ W is the cup product of the classes [`Voisin2002` vol. I, ch. 11, section numbers unverified]. Relative cup with open A, B: [`Hatcher2002` §3.2].

| Literature | Lean (RT1 `#check`) | Comment |
|---|---|---|
| X smooth projective integral of dimension d over ℂ | `X : Over (Spec ↧ℂ)`, `IsIntegral X.left`, `Smooth X.hom`, `IsProjective X.hom`, `SmoothOfRelativeDimension d X.hom` | upstream's hypotheses of record; `d = dim X.left` by upstream `SmoothOfRelativeDimension.dim_eq` |
| Z, W, T integral subvarieties of codimensions a, b, a + b | scheme points `x w t` with `Order.coheight _ = ↑a`, `↑b`, `↑a + ↑b` | upstream's indexing (row "Cycle components" on `main`): coheight is codimension, and `cycleComponentSheafClass X t ht` lands in degree 2(a + b) |
| T = Z ∩ W as sets, one component | `hT` on complex points | implies the scheme-level equality by the Jacobson property (red team of `p2-lines-transversal`; checked on ℙ² as `closure_planeLine_inter`). The classes are built from complex points only, so this is the form the proof needs |
| Z and W transversal at every point of T | `htr`: at each y ∈ T(ℂ) a chart φ in Mathlib's `IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω` with Z ∩ φ.source = {φ_0 = … = φ_{a−1} = 0} and W ∩ φ.source = {φ_a = … = φ_{a+b−1} = 0} | see below: equivalent to holomorphic transversality along T(ℂ) |
| (implicit) Z, W smooth along T | `hxreg`, `hwreg`: T(ℂ) ⊆ `cycleComponentSmoothSupportAmbientOpen` of x and of w | implied by `htr` in mathematics (a reduced variety whose analytic germ is a submanifold is regular there); the pin lacks that implication (rung `analytic-smooth-locus`, open). Harmless: no instance of the literature's theorem is excluded |
| a + b ≤ d | `hd` | implied by `ht`; needed for the indices `⟨i, by omega⟩` in `htr` |
| [Z] · [W] = [T] | `cup [Z] [W] (2 * (a + b)) _ = [T]`, upstream classes, the ladder's Yoneda `cup` | exact |

**`htr` is transversality, neither stronger nor weaker.** If φ is as in `htr`, Z and W are complex submanifolds near y whose conormal spaces are spanned by dφ_0, …, dφ_{a−1} and dφ_a, …, dφ_{a+b−1}, which are independent, so T_yZ + T_yW = T_yX. Conversely, if Z and W are smooth at y and transversal, choose holomorphic local equations f_1, …, f_a of Z and g_1, …, g_b of W with independent differentials; transversality makes all a + b of them independent, and completing them to a coordinate system gives φ. Because Z is reduced and equals the coordinate subspace near y, its local ideal is (φ_0, …, φ_{a−1}); the same for W; so the scheme-theoretic intersection near y has ideal (φ_0, …, φ_{a+b−1}), which is reduced. This is the multiplicity-one condition. Coordinate order inside `htr` carries no content: any holomorphic chart can be permuted ℂ-linearly.

**Scope.** The statement is the textbook transversal case with one integral component. It is narrower than [`Fulton1998`] in two ways, both stated openly in the docstring and in decision 0009: (i) several components T_i (proposed earlier as a separate rung, finding 13 of the plan red team); (ii) transversality only at the generic point of T, with Z or W allowed to be singular at special points of T. Case (ii) is a stronger theorem that the germ route does not reach: at a point of T where Z is singular, upstream's [Z] is not a chart coclass, so the germ of the product there is not computed by `cycle-class-germ`. It would need a separate argument, for example that a section of 𝓗^{2(a+b)}_T over U_T is determined on a dense open of T. Proposed as a new rung (section 9, change F).

## 2. Can the hypotheses be satisfied?

Yes, in Lean (RT2). After copying `main`'s `ProjectivePlaneLines.lean` into the worktree's scratch, this elaborates, with standard axioms:

```lean
theorem rt_coheight_origin :
    Order.coheight planeOrigin = ((1 : ℕ) : ℕ∞) + ((1 : ℕ) : ℕ∞) := by
  rw [coheight_planeOrigin]; rfl

theorem rt_p2_instance :
    HodgeLadder.Cup.cup (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0))
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1)) (2 * (1 + 1))
        (by ring) =
      cycleComponentSheafClass projectivePlane planeOrigin rt_coheight_origin :=
  HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal projectivePlane (d := 2)
    (planeLine 0) (planeLine 1) planeOrigin (coheight_planeLine 0) (coheight_planeLine 1)
    rt_coheight_origin (by norm_num) planeOrigin_support_eq_inter
    (planeOrigin_support_subset_smoothSupportAmbientOpen 0)
    (planeOrigin_support_subset_smoothSupportAmbientOpen 1) planeLines_transversal
```

The only adaptation is `ht`: `coheight_planeOrigin` states `= ((2 : ℕ) : ℕ∞)` and the theorem asks for `↑a + ↑b`; `rfl` closes the difference. The elaboration took about 5 s: the statement of the instance does not mention `supportedEquivPair`, so it carries none of the kernel cost of section 7. This is rung `cycle-class-multiplicative-p2` in full (change A).

At a = b = 0 the hypotheses hold except `hxreg`, which needs U_X = ⊤ at the generic point (rung `cycle-class-multiplicative-codim-zero`, open), as the plan red team found.

## 3. Is the conclusion true for a reason unrelated to the mathematics?

No.

- RT3: `rfl`, `Subsingleton.elim`, `simp` with both definitions unfolded, and `simp_all` with `hT` all fail on the bare conclusion.
- No definition on either side unfolds to a constant: the left side is a Yoneda product of two `forgetSupport` images, the right side a third `forgetSupport` image; `H^{2(a+b)}(X; ℚ)` has no `Subsingleton` instance.
- Every hypothesis is used. `hT` builds `unionComplIso` and gives T's adapted chart from φ; `htr`, `hxreg`, `hwreg` are used at each y ∈ T(ℂ) in `normalization_eq_coclassSection_of_product`; `hd` is needed for `htr` to be well formed; the coheights fix the degrees and enter `cycle-class-germ`.
- The ℕ∞ coercion in `ht` is harmless: RT2 shows the class unifies at degree 2 · (1 + 1) on ℙ², and the plan red team (S2) checked the general case.
- If Z(ℂ) ∩ W(ℂ) is empty, `hT` fails, since T(ℂ) is nonempty.

**The proof is honest.** Route, checked against the code:

1. `γ` comes from surjectivity of Φ_T, with Φ_T γ the pullback along `(unionComplIso hT').inv` of `relCup2 (Φ_Z α_Z) (Φ_W α_W)`. Z is the first factor of `relCup2`, matching the first argument of `cup`.
2. `cup_forgetSupport_of_product` gives Ψ([Z] ∪ [W]) = (−1)^{(2a)(2b)} • Ψ(forget γ). In order it uses `forgetRel_supportedEquivPair` (T), `forgetRel_unionComplIso`, `forgetRel_relCup2`, `forgetRel_supportedEquivPair` (Z, then W), and `cup_singular_comparison' X _ _ h` with x = [Z], y = [W]. The factor order agrees on both sides, and `forgetRel_relCup2` carries no sign.
3. `hsign : (−1)^{2a · 2b} = 1` by `Even.neg_one_pow ⟨a * (2 * b), by ring⟩`, a genuine computation (2a · 2b = a(2b) + a(2b)); `one_smul` removes it.
4. `eq_supportedInjectiveClass_of_product` is the term `cycleComponentSupportedInjectiveClass_unique X t ht γ (normalization_eq_coclassSection_of_product …)`. Upstream's uniqueness (in `Other`) is injectivity of the normalization isomorphism `N_T` together with `N_T α_T = coclass section`, so γ = α_T follows only from N_T γ = coclass section, which is the content of the localization lemma.
5. Localization covers all of U_T. `TopCat.Presheaf.section_ext` (Mathlib, `Topology/Sheaves/Stalks.lean`) quantifies over every y ∈ U_T. The proof splits on y ∈ T(ℂ). Off T, both germs are zero by upstream `supportRelativeCohomologyGerm_eq_zero_of_not_mem`. On T, `htr y hyT` supplies a chart at that very y, so points of T outside any one chart domain are handled by their own chart. Points of T_sing are not in U_T and are not needed. Membership y ∈ U_T, needed by `cycle-class-germ` for T, comes from `section_ext` itself.
6. At y ∈ T(ℂ), `germ_transport_eq_of_chart` applies `cycle-class-germ` three times, to the split charts eZ, eW, eT. It restricts the three identities to V = V_Z ∩ V_W ∩ V_T (`restrict_eq_chartNormalProjectionCoclass`), restricts the product (`transport_restrict_of_supportedEquivPair_eq`, through `relCup2_restrict` and the glue squares, all proved by `ext; rfl`), and closes with `chartNormalProjectionCoclass_eq_relCup2`. Its two consistency hypotheses `hnZ`, `hnW` are discharged by `fun _ _ => rfl`. This is the literal statement that the normal coordinate of eT is (normal coordinate of eZ, normal coordinate of eW) in that order: (eT y).2 (castAdd b i) = φ y ⟨i⟩ = (eZ y).2 i and (eT y).2 (natAdd a j) = φ y ⟨a + j⟩ = (eW y).2 j.
7. The final `rfl` is `cycleComponentSheafClass X t ht = forgetSupport … (cycleComponentSupportedInjectiveClass X t ht)`, which holds by definition at the pin (upstream `cycleComponentSheafClass_eq_forgetSupport` is `rfl`, and `cycle-class-pins` pins it).

The two closing `convert … using 2` steps (in `germ_transport_eq_of_chart` and in the localization) only reconcile spellings of the same germ (`⊤` against `V`, and `trivial` against membership proofs). The kernel checks the stated type, so `convert` cannot hide a gap here.

## 4. Interface rung?

Not applicable. The module adds two definitions (`unionComplIso`, `normalSplit`/`splitChart`) that are data built from Mathlib and upstream, no structure and no axiom (decision 0003).

## 5. Checker and axioms

RT1: each of the 20 declarations reports `[propext, Classical.choice, Quot.sound]`: the 19 route declarations (`neighborhoodSupportInclusionPairMap_comp_ofSubsetIsoNeighborhoodTop_inv`, `restrictToNeighborhood_comp_ofSubsetIsoNeighborhoodTop_hom`, `unionComplIso`, `unionComplIso_fst_apply`, `mem_iff_of_eq_inf`, `unionComplIso_restrict`, `forgetRel_unionComplIso`, `restrict_eq_chartNormalProjectionCoclass`, `normalSplit`, `splitChart`, `splitChart_mem_maximalAtlas`, `relativeCohomologyMap_apply_apply`, `restrict_supportedEquivPair`, `cup_forgetSupport_of_product`, `transport_restrict_of_supportedEquivPair_eq`, `closeds_eq_inf_of_coe_eq`, `germ_transport_eq_of_chart`, `normalization_eq_coclassSection_of_product`, `eq_supportedInjectiveClass_of_product`) and the main theorem. RT4: the checker accepts the worktree. It does not yet see this module, which is not imported from `HodgeLadder.lean` (change B). The ledger entry still has `status: open`, `module: null`, `declarations: []`.

**Dependencies overstated.** The ledger lists `supported-open-naturality` and `supported-model-agreement-open` in `depends_on`, and its note says the general-V formula "enters only through restriction to small opens". The proof does not use them: neither `HodgeLadder.Cup.SupportedOpenNaturality` nor `HodgeLadder.Cup.SupportedAgreementOpen` is in the import closure of the module (grep of every `import` reachable from its five imports). Restriction to small opens goes through `supportedEquivPair_eq_transport` at ⊤ and upstream's restriction maps. Change C corrects the record.

## 6. Conventions

| Convention | Where | Enters how | Truth depends on it? |
|---|---|---|---|
| Yoneda cup, diagrammatic `Ext.comp` | row "Cup product" | factor order of `cup [Z] [W]` | no: (−1)^{(2a)(2b)} = 1 (`cup_gradedComm`) |
| Sheaf–singular comparison Ψ | row "Sheaf–singular comparison Ψ"; `cup_singular_comparison'` | the only global sign, (−1)^{pq} | no in even degrees; computed as 1 |
| Supported comparison Φ | rows "Supported comparison Φ", "Pair spellings"; `supportedEquivPair` | both pinned by checked identities: forgetRel ∘ Φ = Ψ ∘ forgetSupport (no sign) and Φ = upstream transport at ⊤ (`supportedEquivPair_eq_transport`). A hidden sign in Φ would contradict one of the two kernel-checked equalities | yes, and fixed by those checked identities |
| Triad relative cup, forget | row "Triad relative cup product"; `forgetRel_relCup2` | relCup2 forgets to cupSing, no sign, A factor first | yes; checked |
| Triad relative cup naturality | row of that name; `relCup2_restrict` | restriction to V | yes; checked, no sign |
| Pair isomorphisms | `unionComplIso`, `chartUnionIso`, `ofSubsetIsoNeighborhoodTop`, `restrictToNeighborhood` | all `isoOfSubset (Homeomorph.refl _)` or inclusions; `forgetRel_unionComplIso` and the glue squares are proved by `ext; rfl` | no sign possible: identity on points |
| Holomorphic adapted chart | row of that name; `cycle-class-germ` | eZ, eW, eT are φ followed by the ℂ-linear coordinate permutation `normalSplit` (built from `LinearEquiv.funCongrLeft ℂ ℂ` and `sumArrowLequivProdArrow` over ℂ), and `splitChart_mem_maximalAtlas` shows `eZ.trans normalSplit.symm` is in the atlas, so `cycle-class-germ`'s `he` holds with L = `normalSplit.symm`. No conjugation, so no (−1)^c | yes; a conjugated normal coordinate would cost (−1)^c |
| Product of local classes | row "Product of local classes (model and chart)"; `chartNormalProjectionCoclass_eq_relCup2` | the local sign +; `hnZ`, `hnW` by `rfl` make the three normal coordinates literally consistent | yes: a − here gives [Z] ∪ [W] = −[T] |
| Fundamental-class normalization; normalization iso | rows of those names; `normalization_singular`, `coclassSection_eq_singular`, upstream `cycleComponentSupportedInjectiveClass_unique` | γ = α_T from equality of normalized sections | yes; checked, exact |
| Cycle components, coheight | row on `main` (added by `p2-lines-transversal`) | degrees and hypotheses | yes for degrees; checked on ℙ² |
| Field and smoothness level of the atlas | Mathlib `ω = ⊤ : WithTop ℕ∞` (RT1 prints `⊤`), model `𝓘(ℂ, Fin d → ℂ)` | `htr` uses the maximal atlas over ℂ at level ω, the level of upstream's instance `isManifold_omega` | yes, through the field: over ℂ every level n ≥ 1 already forces holomorphic transition maps, so the level is immaterial; a real model `𝓘(ℝ, ℝ^{2d})` would admit conjugated charts and the identity would fail for odd normal codimension |

Recomputed independently: the composite sign is (−1)^{(2a)(2b)} · (+1) = +1. The splitting by `k` is ℂ-linear. The chart coclass of each split chart is read directly in that chart, so no invariance under reordering is even invoked. The only reordering-type statement on the route is that eT's normal coordinate is (z', z''), and it holds by `rfl`. Ψ appears on both sides and is cancelled by its injectivity, so its internal conventions enter only through `cup_singular_comparison'`.

New register row (this pass): "Transversal product of cycle classes", after the "Holomorphic adapted chart" row, so that it does not touch the lines `main` changed.

## 7. Equality first

The rung is an identity, proved exactly: `cup [Z] [W] = [T]`, no scalar, the sign + computed. The inclusions on the route (the pair (X, (X ∖ Z) ∪ (X ∖ W)) read as (X, X ∖ T)) are identity maps of points, proved sign-free in Lean.

### 7b. Non-vacuity and sign visibility

The sign + is visible only where [T] ≠ 0. Smallest tests that would fail if the statement were trivially true or carried the wrong sign:

| Test | Upstream API | Exists? |
|---|---|---|
| ℙ²: [pt] ≠ 0, so [L₀] ∪ [L₁] = [pt] ≠ 0 and ≠ −[pt] | `cycleComponentSheafClass projectivePlane planeOrigin _ ≠ 0` | no: `p2-point-class-nonzero` and `cup-positive-degree-test-p2` are open |
| codimension zero: [X] ∪ [X] = [X] with [X] = 1 ≠ −1 | `cycleComponentSheafClass X (genericPoint X.left) _`, ladder `cycleComponentSheafClass_genericPoint_ne_neg_one` | the inequality exists (`HodgeLadder.Tests.FundamentalClassUnit`); the instance needs `cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤`, rung `cycle-class-multiplicative-codim-zero`, open |
| local sign | `relCup2_model_eval_orient` = 1, `relCup2_model_ne_zero` | yes (`local-class-product`) |

So the global sign is not yet tested by a nonvanishing statement in positive degree; it rests on the checked local sign. The two open rungs above are the cheapest sign-visible instances. Order them right after this rung (change D).

## 8. Pin drift

None: built at `2ead713`, the current pin. For the next bump, add to the diff list:

- Statement library: `cycleComponentSheafClass`, `cycleComponentSupportedInjectiveClass`, `cycleComponentSupportedClassNormalizationIso`, `cycleComponentSmoothSupportCoclassSection`, `cycleComponentAnalyticClosedSupport`, `cycleComponentSmoothSupportAmbientOpen`, `supportRelativeCohomologyGerm` with `_eq_of_restrict_eq`, `_eq_zero_of_not_mem`, `_restrict` (`Lemmas/AlgebraicTopology/Support/RelativeCohomologySheaf.lean`), `chartNormalProjectionCoclass` and `chartNormalProjectionCoclass_restrict` (`Lemmas/.../SmoothPair/CoclassOverlap.lean`), `neighborhoodSupportInclusionPairMap(_comp)`, `neighborhoodSupportComplementPair`, `openParacompactSpace`, `SmoothOfRelativeDimension.dim_eq`, and the charted structure (`localChart`, `isManifold_omega`).
- `Other` (unguarded): `cycleComponentSupportedInjectiveClass_unique`, `cycleComponentSupportedInjectiveClass_normalization`, `cycleComponentSupportedClassNormalizationIso_apply`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section`, `rationalCohomologyAddEquivSingularCohomology`.
- Mathlib: `TopCat.Presheaf.section_ext`, `StructureGroupoid.mem_maximalAtlas_of_eqOnSource`, `LinearEquiv.funCongrLeft`, `LinearEquiv.sumArrowLequivProdArrow`, the meaning of `ω` in `WithTop ℕ∞`.

The uniqueness lemma in `Other` is a two-line consequence of the definition of `cycleComponentSupportedInjectiveClass` in the statement library. Drift there would break the build of this module.

**Merge drift.** `main` changed `docs/sketches/cycle-class-multiplicative.md` (96 lines) and `docs/conventions.md` (one row) since this worktree's base. Rebase before posting; the sketch file will need a hand merge of two appended sections.

## 9. Findings

1. **[Z] ∪ [W] = [T] stands**, exact, sign +, standard axioms, every hypothesis used, no trivial proof (sections 3, 5).
2. **The statement is the literature's transversal case** with one component. `htr` is holomorphic transversality along T(ℂ), and it also gives multiplicity one; `hT` on complex points is the right form; `hxreg`, `hwreg`, `hd` are implied by the others in mathematics and exclude no instance (section 1).
3. **The sign is not forced.** It comes from (−1)^{(2a)(2b)} = 1 and the local + of `local-class-product`; a local − would change the conclusion. No sign hides in Ψ, Φ, `unionComplIso`, `chartUnionIso` or `splitChart`: Φ is pinned by two checked identities, the pair maps are identities on points, and `normalSplit` is ℂ-linear (section 6).
4. **Localization is complete.** Germs on all of U_T are covered: off T both germs vanish, and on T `htr` gives a chart at the same point (section 3, item 5).
5. **`set_option backward.isDefEq.respectTransparency false` on `forgetRel_unionComplIso` is harmless.** It relaxes the elaborator's transparency during unification only. The statement's terms are explicit (`relativeCohomologyMap`, `forgetRel` on named pairs), the consumer rewrites with the lemma by `rw`, which matches the stated type, and the kernel rechecks the proof. The same option is used in the checked `forgetRel_relCup2` and `cup_singular_comparison_supported_pair`.
6. **The general lemma `cup_forgetSupport_of_product` is correct for all p, q.** Its (−1)^{pq} is the genuine sign of `cup_singular_comparison'` and is visible in odd degrees; equivalently, by `cup_singular_comparison_swap`, the sign disappears with the factors of `cupSing` swapped. It does not need to be its own rung: its hypothesis `hγ` names a proof-internal object (Φ_T γ against `relCup2`). List it among this rung's declarations, since the several-components rung will reuse it.
7. **Kernel cost is not a CI risk.** About 96 s for the module, as measured by the prover, against a 240-minute CI budget. Kernel heartbeats are deterministic, so a module that passes the default limit locally passes it on CI with the same toolchain. Consumers whose statements avoid `supportedEquivPair` (such as the ℙ² instance, about 5 s) do not pay it.
8. **Record overstates dependencies.** `supported-open-naturality` and `supported-model-agreement-open` are not in the import closure (section 5).
9. **Docstring citations.** The main theorem's docstring names its sign sources but no register rows; `docs/conventions.md` rule 2 asks for the row names (change E).
10. **Sign visibility in positive degree is still open** (`p2-point-class-nonzero`); the codimension-zero instance is the cheapest sign-visible test (section 7b).

## Recommended changes

| # | Change | Where |
|---|---|---|
| A | Prove `cycle-class-multiplicative-p2` now, from RT2: a test module on `main`'s ℙ² file with the two declarations of section 2 (`rt_coheight_origin` renamed `coheight_planeOrigin_add`, `rt_p2_instance` renamed `planeLines_cup_eq_planeOrigin`) | new `HodgeLadder/Tests/ProjectivePlaneLinesCup.lean` importing `HodgeLadder.Tests.ProjectivePlaneLines` and `HodgeLadder.Cycle.Multiplicative`; ledger |
| B | Import the module from the root; set the ledger entry to `checked`, `module: "HodgeLadder.Cycle.Multiplicative"`, and list all 20 declarations; roadmap row; status block | `HodgeLadder.lean`, `ledger/ladder.json`, `docs/roadmap.md`, `CLAUDE.md` |
| C | Remove `supported-open-naturality` and `supported-model-agreement-open` from `depends_on`, and replace the note's "enters only through restriction to small opens" with: "Restriction to small opens goes through `supportedEquivPair_eq_transport` at ⊤ and upstream's restriction maps; the general-V rungs are not used." | `ledger/ladder.json` |
| D | Put `cycle-class-multiplicative-codim-zero`, `p2-point-class-nonzero` and `cup-positive-degree-test-p2` next in order: they are the sign-visible tests | ledger order, roadmap |
| E | Append to the docstring of `cycleComponentSheafClass_cup_of_transversal`: "Conventions (`docs/conventions.md`): rows \"Cup product\", \"Sheaf–singular comparison Ψ\", \"Supported comparison Φ\", \"Triad relative cup product\", \"Holomorphic adapted chart\", \"Product of local classes (model and chart)\" and \"Transversal product of cycle classes\"." | `HodgeLadder/Cycle/Multiplicative.lean` |
| F | New rungs with stronger statements (this rung stays as stated): `cycle-class-multiplicative-no-reg` (drop `hxreg`, `hwreg` via `analytic-smooth-locus`), and `cycle-class-multiplicative-generic` (transversality only at the generic point of T, Z and W possibly singular elsewhere on T) | ledger, roadmap |
| G | Add the drift list of section 8 to the sketch's drift section; rebase on `main` and hand-merge the sketch | sketch, branch |

## Sources

`Fulton1998` Cor. 19.2 and §8.2 (numbering unverified); `Voisin2002` vol. I ch. 11 (section numbers unverified); `Hatcher2002` §3.2; `Bredon1997` (supports, unverified). Upstream declarations by name, read at `2ead713`.
