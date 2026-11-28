# Red team: `pullback-functorial`

Verdict: **pass with changes**

Candidate: WIP commit `942d2cd` on `track/pullback-functorial`, `HodgeLadder/Pullback/Functorial.lean` (module `HodgeLadder.Pullback.Functorial`, namespace `HodgeLadder.Pullback`, imports only `HodgeLadder.Cup.PullbackVariety`) and `HodgeLadder/Tests/PullbackFunctorial.lean`, built against upstream `2ead713`, Mathlib `1f41440`, Lean `v4.35.0-rc4`. Red team 2026-11-27, issue #224, plan node A1 of `docs/notes/2026-11-27-t1-plan.md`.

Read: the ledger entries `pullback-functorial`, `cup-pullback`, `weil-space`, `de-rham-pullback`, `pullback-singular-naturality`, `elliptic-square-cohomology`, and on `main` (`8eba28e`) `supported-class-pullback`, `pullback-port-agreement`, `supported-pullback-functorial`; `HodgeLadder/Cup/Pullback.lean`, `HodgeLadder/Cup/PullbackVariety.lean`; `HodgeLadder/Supported/Pullback.lean` on `main`; upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (the notation `H^n(X; K)` and `fieldCohomologyModule`); Mathlib `CategoryTheory/Adjunction/Unique.lean`, `CategoryTheory/Adjunction/CompositionIso.lean`, `Topology/Sheaves/Functors.lean`; `docs/gaps.md`, `docs/conventions.md`, `docs/references.md`. No thinker sketch exists for this rung.

Scratch: `rtscratch/` in the worktree (files `A` to `Q`), each a plain `lake env lean` run against the built `.olean`; deleted after the pass. Every Lean claim below marked "scratch" elaborated there.

## Findings

1. **The statement is the literature's functoriality of pullback on sheaf cohomology.** `Iversen1986` (inverse image of sheaves, (g ∘ f)⁻¹ ≅ f⁻¹ g⁻¹ and the induced maps on cohomology; recalled, chapter numbers unverified) and `Bredon1997` (functoriality of sheaf cohomology in the space; sections unverified) give (h ∘ g)^* = g^* ∘ h^* and id^* = id for constant coefficients. Field by field:

   | Field | Literature (recalled) | Lean | Match |
   |---|---|---|---|
   | Group | Hⁿ(X(ℂ); ℚ), sheaf cohomology of the constant sheaf | upstream notation `H^n(X; ℚ)` = `Sheaf.H.{0} ((constantFunctor ↧(ComplexPoint X)).obj (AddCommGrpCat.of ℚ)) n` | yes |
   | Map | g^* induced by g(ℂ) : X'(ℂ) → X(ℂ) | `HodgeLadder.Cup.pullbackCoh g n`, the checked map of rung `cup-pullback` (multiplicative, unital, additive) | yes; `pp.fullNames` on `pullbackCoh_comp` and `pullbackCohLinear_apply` shows `HodgeLadder.Cup.pullbackCoh` (scratch, Q) |
   | Composition | (h ∘ g)^* = g^* ∘ h^* | `pullbackCoh_comp : pullbackCoh (g ≫ h) n α = pullbackCoh g n (pullbackCoh h n α)` for `g : X ⟶ Y`, `h : Y ⟶ Z`; Mathlib's `≫` is diagrammatic, so `g ≫ h` is h ∘ g | yes; the order is the only one the types allow |
   | Identity | id^* = id | `pullbackCoh_id : pullbackCoh (𝟙 X) n α = α` | yes |
   | Linearity | g^* is ℚ-linear | `pullbackCohLinear g n : H^n(X; ℚ) →ₗ[ℚ] H^n(X'; ℚ)` with `_apply` by `rfl`; the `Module ℚ` instance is upstream's `fieldCohomologyModule ℚ X n` (scratch: `(inferInstance : Module ℚ (H^n(X; ℚ))) = fieldCohomologyModule ℚ X n := rfl` elaborates) | yes |
   | Space level | (f₁ ≫ f₂)^* = f₁^* ∘ f₂^* for continuous maps | `pullbackH_comp`, `pullbackH_id` on `HQ X n` for `X : TopCat.{0}` | yes |

   The plan's elaborated A1 text (`pullbackCoh_comp`, `pullbackCoh_id`, `pullbackCohLinear` by `toRatLinearMap`) is matched verbatim up to namespace.

2. **The hypotheses can be satisfied.** There are none beyond the data: any morphisms over `Spec ℂ`. The test module instantiates both laws at `prod.fst : p1p1 ⟶ projectiveLine` and its section `fibreSectionSnd` (`prod.lift_fst`), and `pointMap (g ≫ h) = pointMap g ≫ pointMap h` and `pointMap (𝟙 X) = 𝟙 _` hold by `rfl` (scratch, L).

3. **The conclusions are not trivially true.** Attempts (scratch, L): `rfl` for `pullbackCoh_comp` times out at `isDefEq` (40,000 heartbeats); `rfl` for `pullbackCoh_id` is a type mismatch; `simp [pullbackCoh, pullbackH]` for the identity law leaves `(rationalExtEquiv _ n).symm (conjExt (pullbackQ (pointMap (𝟙 X))) (pullbackQX (pointMap (𝟙 X))) (rationalExtEquiv _ n α)) = α` and the kernel times out on the partial term. No main statement mentions a local definition: the types of `pullbackCoh_comp`, `pullbackCoh_id`, `pullbackH_comp`, `pullbackH_id` involve only the checked `pullbackCoh`/`pullbackH` and upstream's `H^n`. `pullbackQComp` and `pullbackQId` appear only in the auxiliary `pullbackQX_comp`/`pullbackQX_id`, where they are the canonical `leftAdjointUniq` isos; the laws do not depend on which iso is chosen there, since they are equalities of maps on `Ext` after `conjExt_natIso` cancels it. `pullbackCohLinear` is a bundling whose `_apply` is `rfl`, so its laws are exactly those of `pullbackCoh`. Every hypothesis is used.

4. **Interface rung:** not applicable; no structure, no axioms.

5. **Checker and axioms.** `python3 tools/check.py --no-build` exits 0 (`ACCEPTED: all checks passed`), but the candidate is not root-imported or in the ledger, so the checker does not cover it. `#print axioms` (scratch, A) on all 20 named declarations (`pullbackCoh_comp`, `pullbackCoh_id`, `pullbackCohLinear`, `_apply`, `_comp`, `_id`, `pullbackCoh_injective_of_section`, `pullbackH_comp`, `pullbackH_id`, `isoConj`, `conjExt_natIso`, `conjExt_comp_functor`, `conjExt_id_functor`, `pullbackQComp`, `pullbackQId`, `pullbackQX_comp`, `pullbackQX_id`, `leftAdjointUniq_comp_triangle`, `leftAdjointUniq_id_triangle`, `leftAdjointUniq_hom_app_eq`) and the two tests: `[propext, Classical.choice, Quot.sound]` for each. No `sorry`, `native_decide`, `axiom`, `unsafe` or `set_option` in either file. The test's input `acyclic_compl_infty` is a checked theorem of `projective-line-class-nonzero`, so the test is unconditional.

6. **Signs and normalizations.** No sign enters, and none was found. Conventions the result uses:

   | Convention | Where | Truth depends on it? | Register |
   |---|---|---|---|
   | Order of composition | Mathlib `≫` diagrammatic; `(g ≫ h)^* = g^* ∘ h^*` | the composition law as stated (the opposite order does not typecheck) | add to the pullback row (change 5) |
   | f⁻¹ℚ_X ≅ ℚ_Y | `pullbackQX`, `leftAdjointUniq` against `constantSheafAdj`, no sign | no: any choice of iso compatible with composition gives the same laws, and `pullbackQX_comp`/`_id` prove the canonical one is compatible | already in the pullback row on `main` |
   | (f₁ ≫ f₂)⁻¹ ≅ f₂⁻¹ ⋙ f₁⁻¹, (𝟙 X)⁻¹ ≅ 𝟭 | `pullbackQComp`, `pullbackQId`, `leftAdjointUniq` against `pushforward (f₁ ≫ f₂) = pushforward f₁ ⋙ pushforward f₂` (`rfl`) | no (cancels in `conjExt_natIso`) | add (change 5) |
   | ℚ-structure on `H^n(X; ℚ)` | upstream `fieldCohomologyModule ℚ X n` (`Module.ofMinimalAxioms`, q acts by `Sheaf.H.map (fieldScalarSheaf ℚ X q)`) | linearity: no (an additive map of ℚ-vector spaces is ℚ-linear for the unique ℚ-structure); consumers that compare with upstream spans and `baseChange ℂ` need it to be upstream's, and it is (`rfl`, scratch A) | add (change 5) |

   For the space-level law against the port: `HodgeLadder.Supported.pullbackH_eq_pullbackConst` (on `main`) identifies `pullbackH f` with the port's `H.pullback f` followed by f⁻¹ℚ_X ≅ ℚ_Y, exactly. With `pullbackH_comp` it gives `pullbackConst (f₁ ≫ f₂) ℚ = pullbackConst f₁ ℚ ∘ pullbackConst f₂ ℚ` by three rewrites; the two checked results are consistent and no sign can appear between them. Coefficients other than ℚ are not covered (that is the port side of `supported-pullback-functorial`).

7. **Equality first.** Both laws are identities, proved exactly: equalities of maps, no scalar, no `∃ c ≠ 0`.

   7b. **Non-vacuity.** The smallest test that fails if the laws held trivially (zero groups or the zero map) is `HodgeLadder.Tests.p1p1_pullbackCoh_fst_class_ne_zero`: `pullbackCoh prod.fst (2 * 1) (cycleComponentSheafClass projectiveLine infty coheight_infty') ≠ 0`, stated in upstream's API (`cycleComponentSheafClass`, `H^(2 * 1)(·; ℚ)`). It exists, and it uses both laws through `pullbackCoh_injective_of_section`. Limits of strength: it pins injectivity of `prod.fst^*` in degree 2 and nothing about values; the value test `pr₁^*[∞] = [{∞} × ℙ¹]` is rung `fibre-class-pullback` (open). The ℚ-structure is exercised only through `map_zero`; the `rfl` instance check of finding 1 is the substantive check there.

8. **Pin drift.** The branch base `8ee8053` and `main` (`8eba28e`) have identical `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` (empty diff), upstream `2ead713` in both, and no change under `HodgeLadder/Cup/` between them. No drift.

9. **Kernel cost: diagnosis confirmed, located on upstream's `Module ℚ` instance term.** Serial timings, fresh files, `profiler.threshold` 200 to 500 ms, `Elab.async false` where per-declaration attribution was needed (scratch B to P):

   | Declaration (scratch) | Kernel time |
   |---|---|
   | `pullbackCoh g n α = pullbackCoh g n α := rfl` | 0.01 s |
   | `AddMonoidHom.id (H^n(X; ℚ)) = AddMonoidHom.id _ := rfl` | 0.004 s |
   | `fieldCohomologyModule ℚ X n = fieldCohomologyModule ℚ X n := rfl` | 2.2 s (2.6 s at a variable field `K`) |
   | `(inferInstance : Module ℚ (H^n(X; ℚ))) = fieldCohomologyModule ℚ X n := rfl` | 8.2 s |
   | `(LinearMap.id : H^n(X; ℚ) →ₗ[ℚ] H^n(X; ℚ)) = LinearMap.id := rfl` | 7.5 s (5.1 s with the semiring given as `Ring.toSemiring`) |
   | `pullbackCohLinear g n = pullbackCohLinear g n := rfl` | 16.1 s |
   | the same `_comp` statement through `toAddMonoidHom` | 24.5 s (it still mentions `pullbackCohLinear`) |
   | candidate, in order: `pullbackH_comp` 4.3 s, `pullbackH_id` 2.0 s, `pullbackCoh_comp` 2.3 s, `pullbackCoh_id` 2.3 s, `pullbackCohLinear` 43.7 s (plus 1.0 s), `_apply` 13.9 s, `_comp` 21.3 s, `_id` 6.8 s | module about 114 s, about 86 s of it the four `pullbackCohLinear` declarations |

   With `set_option diagnostics true` the kernel's unfold counts for the bare `fieldCohomologyModule K X n = fieldCohomologyModule K X n` are dominated by `Functor.obj` (30,144), `AddCommGrpCat.str` (23,720), `AddGroup.toSubNegMonoid` (22,456), `HSMul.hSMul` (17,200), `Preadditive.homGroup` (2,608) and `Function.Injective.addCommGroup` (2,448): the kernel unfolds `Ext`'s additive group, `nsmul`/`zsmul` fields included, to compare two instance paths. Upstream's declared type of `fieldCohomologyModule` carries `CommSemiring.toSemiring (Semifield.toCommSemiring (Field.toSemifield _))` and `Sheaf.H` with the generic `HasSheafify` instance, while its value is built with upstream's local `instHasExtSheafOpensCarrierOfGrothendieckTopologyAddCommGrpCat` and `analyticHasDerivedCategory._proof_1` (scratch, D2); the ladder elaborates `Rat.semiring`. So the cost attaches to each declaration whose type or value contains the instance term; elaboration stays under 0.6 s. Spellings tried:

   - a named `abbrev HQl X n := H^n(X; ℚ)`: `LinearMap.id` 14.9 s, worse;
   - `LinearMap.restrictScalars ℚ`: 6.5 s, no gain;
   - a ladder shortcut `noncomputable instance (priority := high) shortQ X n : Module ℚ (H^n(X; ℚ)) := fieldCohomologyModule ℚ X n`: the instance 3.1 s once; then `LinearMap.id = LinearMap.id` and `lin g n = lin g n` under 0.3 s each, the bundled def 29.8 s, `shortQ X n = fieldCohomologyModule ℚ X n := rfl` 3.4 s.

   The shortcut is the only spelling that removes the per-consumer cost. It is a second `Module ℚ` instance on an upstream type that already has one; the precedent row for `holomorphicFormRatModule` in `docs/gaps.md` says such an instance must go once upstream supplies one, and `CLAUDE.md` forbids instances that change how upstream statements elaborate. Do not adopt it in this rung; record the measurement (change 4) so a decision can be opened if T1 build time becomes the bottleneck. This cost recurs in every T1 rung that states through `pullbackCohLinear` (`weil-space`, `de-rham-pullback`, `elliptic-square-cohomology`): budget about 7 to 25 s per declaration.

10. **Duplicated general lemmas.** The branch predates #233. On `main`, `HodgeLadder.Supported.conjExt_conjExt` is `conjExt_comp_functor` read right to left (same hypotheses, `conjExt G b (conjExt F a x) = conjExt (F ⋙ G) (G.mapIso a ≪≫ b) x`), and `conjExt_natIso` is the iso case of `HodgeLadder.Supported.conjExt_eq_of_natTrans` (τ = e.inv). No name clash (different namespaces), and the candidate cannot import `HodgeLadder.Supported.Pullback` without pulling the port into the import closure of every T1 consumer. Keep the candidate's copies (lower layer, 5 against a module that imports `LefschetzPort`) and record the duplication (change 4). No clash with Mathlib, upstream or the port for any candidate name (`git grep` on `main`, `grep` of `.lake/packages`). Mathlib's `Adjunction.leftAdjointCompIso`, `leftAdjointIdIso` and their coherence lemmas (`CompositionIso.lean`) build comparable isos from `conjugateIsoEquiv`; using them would mean re-expressing the checked `pullbackQX`, which is a `leftAdjointUniq`, so the local triangle lemmas are justified; they are clash candidates at a bump.

11. **Reuse by `supported-pullback-functorial`.** That rung needs (f₁ ≫ f₂)⁻¹ ≅ f₂⁻¹ ⋙ f₁⁻¹ for abelian sheaves (the port's `pullbackAb`), and its ledger note says Mathlib has none. `pullbackQComp` and `pullbackQId` are stated for `ModuleCat ℚ` only. The same definitions at any coefficient category `A` with the hypotheses of `TopCat.Sheaf.pullback` elaborate, agree with `pullbackQComp f₁ f₂` and `pullbackQId X` by `rfl` at `A = ModuleCat ℚ`, and instantiate at `AddCommGrpCat.{0}` (scratch, K). Optional change 1.

12. **Placement.** Layers from `tools/pinwalk.py`'s `graph()` (the module is not yet root-imported, so the printed walk omits it): `HodgeLadder.Cup.Pullback` 3, `HodgeLadder.Cup.PullbackVariety` 4, `HodgeLadder.Pullback.Functorial` 5, `HodgeLadder.Tests.PullbackFunctorial` 48 (through `P1p1Fibres`). Keep `HodgeLadder/Pullback/Functorial.lean`: it matches `next.py`'s file field, the T1 consumers import it without the 60-odd `Cup` files' context, and the `Pullback` directory is where `de-rham-pullback`-style laws can follow. The namespace `HodgeLadder.Pullback` has one Mathlib neighbour, `AlgebraicGeometry.Scheme.Pullback`, reached only through `Scheme.`; no ambiguity under the usual `open`s. The test belongs in its own rung, following `supported-class-pullback-test` and `local-class-pullback-submersion-p1p1` (kind `test`), since it pulls layer 48 into nothing else.

13. **Docstring errors.** `pullbackCoh_injective_of_section` says "A retraction of `p`"; `s` with `s ≫ p = 𝟙` is a section of `p` (the name is right, the docstring is wrong). `pullbackCohLinear`'s docstring does not say which ℚ-structure it uses, which is what the T1 consumers rely on.

## Required changes

1. `HodgeLadder/Pullback/Functorial.lean`, docstring of `pullbackCoh_injective_of_section`, replace with:

   ```
   /-- A section of `p` makes `p^*` injective: if `s ≫ p = 𝟙`, then `s^* ∘ p^* = id`. -/
   ```

2. Same file, docstring of `pullbackCohLinear`, replace with:

   ```
   /-- **Pullback as a `ℚ`-linear map** `g^* : Hⁿ(X; ℚ) →ₗ[ℚ] Hⁿ(X'; ℚ)`. Additivity is
   `pullbackCoh_add`; a group homomorphism between `ℚ`-vector spaces is `ℚ`-linear. The
   `ℚ`-structure on both sides is upstream's `fieldCohomologyModule ℚ` (instance search finds it,
   and it agrees by `rfl` with `inferInstance`). Kernel cost: about 7 to 25 s per declaration whose
   type mentions this map (`docs/gaps.md`, Known weaknesses). -/
   ```

3. Rebase the branch on `main` (`8eba28e` or later), import both modules from `HodgeLadder.lean`, and add two ledger entries. Edit `pullback-functorial` to:

   - `"status": "checked"`, `"module": "HodgeLadder.Pullback.Functorial"`, `"contributors": ["claude-code"]`
   - `"declarations"`: `HodgeLadder.Pullback.pullbackCoh_comp`, `HodgeLadder.Pullback.pullbackCoh_id`, `HodgeLadder.Pullback.pullbackCohLinear`, `HodgeLadder.Pullback.pullbackCohLinear_apply`, `HodgeLadder.Pullback.pullbackCohLinear_comp`, `HodgeLadder.Pullback.pullbackCohLinear_id`, `HodgeLadder.Pullback.pullbackCoh_injective_of_section`, `HodgeLadder.Pullback.pullbackH_comp`, `HodgeLadder.Pullback.pullbackH_id`, `HodgeLadder.Pullback.pullbackQComp`, `HodgeLadder.Pullback.pullbackQId`, `HodgeLadder.Pullback.pullbackQX_comp`, `HodgeLadder.Pullback.pullbackQX_id`, `HodgeLadder.Pullback.conjExt_pullbackQ_comp`, `HodgeLadder.Pullback.conjExt_pullbackQ_id`, `HodgeLadder.Pullback.isoConj`, `HodgeLadder.Pullback.isoConj_trans`, `HodgeLadder.Pullback.isoConj_refl`, `HodgeLadder.Pullback.conjExt_eq_isoConj`, `HodgeLadder.Pullback.mapExactFunctor_natIso`, `HodgeLadder.Pullback.conjExt_natIso`, `HodgeLadder.Pullback.conjExt_comp_functor`, `HodgeLadder.Pullback.conjExt_id_functor`, `HodgeLadder.Pullback.conjExt_eq_of_comp_iso`, `HodgeLadder.Pullback.conjExt_eq_of_id_iso`, `HodgeLadder.Pullback.leftAdjointUniq_hom_app_eq`, `HodgeLadder.Pullback.leftAdjointUniq_comp_triangle`, `HodgeLadder.Pullback.leftAdjointUniq_id_triangle`
   - `"note"`: "Checked 2026-11-27. For g : X ⟶ Y and h : Y ⟶ Z over Spec ℂ, pullbackCoh (g ≫ h) n α = pullbackCoh g n (pullbackCoh h n α) and pullbackCoh (𝟙 X) n α = α, exact, no sign, no scalar; pullbackCohLinear g n : H^n(X; ℚ) →ₗ[ℚ] H^n(X'; ℚ) bundles pullbackCoh with upstream's ℚ-structure fieldCohomologyModule ℚ (rfl), with _comp and _id. Space level: pullbackH_comp, pullbackH_id for continuous maps of TopCat.{0}. Route: conjExt is invariant under a natural iso of exact functors and compatible with composition of functors (Mathlib Ext.comp_mapExactFunctor, Ext.mapExactFunctor_comp_mk₀_natTransApp); (f₁ ≫ f₂)⁻¹ ≅ f₂⁻¹ ⋙ f₁⁻¹ and (𝟙 X)⁻¹ ≅ 𝟭 by leftAdjointUniq, with pullbackQX_comp and pullbackQX_id from the abstract triangle lemmas. With pullbackH_eq_pullbackConst this makes the port's H.pullback followed by f⁻¹ℚ_X ≅ ℚ_Y functorial for coefficients ℚ. Kernel cost about 7 to 25 s per declaration mentioning pullbackCohLinear (docs/gaps.md, Known weaknesses). Non-vacuity in pullback-functorial-test. Red team docs/sketches/pullback-functorial.redteam.md."

   Add `pullback-functorial-test`:

   - `"title"`: "Non-vacuity of pullback-functorial: prod.fst^* : H^n(ℙ¹; ℚ) → H^n(ℙ¹ × ℙ¹; ℚ) is injective through the section prod.lift (𝟙) ∞, and the pullback of the point class [∞] ∈ H²(ℙ¹; ℚ) is nonzero"
   - `"status": "checked"`, `"kind": "test"`, `"module": "HodgeLadder.Tests.PullbackFunctorial"`, `"contributors": ["claude-code"]`
   - `"declarations"`: `HodgeLadder.Tests.p1p1_pullbackCoh_fst_injective`, `HodgeLadder.Tests.p1p1_pullbackCoh_fst_class_ne_zero`
   - `"depends_on"`: `pullback-functorial`, `projective-line-class-nonzero`, `p1p1-fibres-transversal`
   - `"note"`: "Uses both laws (s^* ∘ p^* = (s ≫ p)^* = id) and rules out zero groups and the zero map in degree 2. It pins injectivity only; the first value test of a pullback in positive degree is fibre-class-pullback (pr₁^*[∞] = [{∞} × ℙ¹])."

4. `docs/gaps.md` (on the rebased branch).

   In "Homological algebra and derived categories", add the row:

   ```
   | `HodgeLadder.Pullback.isoConj`, `isoConj_trans`, `isoConj_refl`, `conjExt_eq_isoConj`, `mapExactFunctor_natIso`, `conjExt_natIso`, `conjExt_comp_functor`, `conjExt_id_functor`, `conjExt_eq_of_comp_iso`, `conjExt_eq_of_id_iso` (conjugation of self-extensions by an iso; `conjExt` is invariant under a natural iso of exact functors, compatible with composite functors and trivial for `𝟭`); any abelian categories | `HodgeLadder.Pullback.Functorial` | 5 | not in Mathlib at the pin; Mathlib inputs `Ext.comp_mapExactFunctor`, `Ext.id_mapExactFunctor`, `Ext.mapExactFunctor_comp_mk₀_natTransApp`. `conjExt_comp_functor` is `HodgeLadder.Supported.conjExt_conjExt` read right to left, and `conjExt_natIso` is the iso case of `HodgeLadder.Supported.conjExt_eq_of_natTrans`: derive those two from these when `HodgeLadder.Supported.Pullback` is next edited; rung `pullback-functorial` | 2026-11-27 |
   ```

   In "Sheaves and sheafification", append `CategoryTheory/Adjunction/Unique.lean`, `CategoryTheory/Adjunction/CompositionIso.lean` to the Mathlib list of the "Diff at a bump" line, and add the row:

   ```
   | `HodgeLadder.Pullback.pullbackQComp`, `pullbackQId` ((f₁ ≫ f₂)⁻¹ ≅ f₂⁻¹ ⋙ f₁⁻¹ and (𝟙 X)⁻¹ ≅ 𝟭 on sheaves of ℚ-vector spaces, by `leftAdjointUniq`), `pullbackQX_comp`, `pullbackQX_id`, `conjExt_pullbackQ_comp`, `conjExt_pullbackQ_id`, `pullbackH_comp`, `pullbackH_id`; the abstract `leftAdjointUniq_hom_app_eq`, `leftAdjointUniq_comp_triangle`, `leftAdjointUniq_id_triangle` (components of `leftAdjointUniq` along a composite and along the identity, by comparing units) | `HodgeLadder.Pullback.Functorial` | 5 | Mathlib at the pin has no composition or identity iso for `TopCat.Sheaf.pullback`; clash candidates at a bump: `Adjunction.leftAdjointCompIso`, `leftAdjointIdIso` and their coherence lemmas in `CategoryTheory/Adjunction/CompositionIso.lean` (built from `conjugateIsoEquiv`, so the checked `pullbackQX` would need re-expressing to use them) and any composition iso added to `Topology/Sheaves/Functors.lean`; rung `pullback-functorial` | 2026-11-27 |
   ```

   In "Known weaknesses", add the row:

   ```
   | Kernel cost of upstream's `Module ℚ` instance on `H^n(X; ℚ)` (`AlgebraicGeometry.ComplexPoint.fieldCohomologyModule ℚ X n`, built by `Module.ofMinimalAxioms`): each declaration whose type or value contains the instance term pays kernel time, elaboration stays under 0.6 s (red team `pullback-functorial`, serial, fresh files at `2ead713`): `fieldCohomologyModule ℚ X n = fieldCohomologyModule ℚ X n := rfl` 2.2 s (2.6 s at a variable field); `(inferInstance : Module ℚ (H^n(X; ℚ))) = fieldCohomologyModule ℚ X n := rfl` 8.2 s; `LinearMap.id = LinearMap.id` on `H^n(X; ℚ)` 7.5 s; `pullbackCohLinear g n = pullbackCohLinear g n := rfl` 16.1 s; the additive-only statements (`AddMonoidHom.id`, `pullbackCoh g n α = pullbackCoh g n α`) under 0.01 s. Diagnostics show the kernel unfolding `Ext`'s additive group with its `nsmul`/`zsmul` fields (`Function.Injective.addCommGroup`, `Preadditive.homGroup`, `AddCommGrpCat.str`, about 30,000 unfoldings of `Functor.obj`) to compare two instance paths. `HodgeLadder.Pullback.Functorial`: `pullbackCohLinear` 43.7 s, `_comp` 21.3 s, `_apply` 13.9 s, `_id` 6.8 s, the other declarations about 11 s together; module about 114 s. An `abbrev` of the type (14.9 s for `LinearMap.id`) and `LinearMap.restrictScalars ℚ` (6.5 s) do not help. A ladder shortcut `instance (priority := high) : Module ℚ (H^n(X; ℚ)) := fieldCohomologyModule ℚ X n` does (3.1 s once, then under 0.3 s for the two `rfl` statements, the bundled def 29.8 s), but it is a second instance on an upstream type that has one and needs a decision record first | Every T1 rung stating through `pullbackCohLinear` (`weil-space`, `de-rham-pullback`, `elliptic-square-cohomology` and their consumers) pays about 7 to 25 s of kernel time per declaration; keep statements on `pullbackCoh` where linearity is not used, and open a decision on the shortcut instance if T1 build time becomes the bottleneck | 2026-11-27 |
   ```

5. `docs/conventions.md` (on the rebased branch), row "Pullback of cohomology and of cohomology with supports":

   - column "Fixed where": append "; `HodgeLadder.Pullback.pullbackCoh_comp`, `pullbackCoh_id`, `pullbackCohLinear`, `pullbackQComp`, `pullbackQId` (rung `pullback-functorial`)".
   - column "Choice": append "; functorial exactly: `pullbackCoh (g ≫ h) n = pullbackCoh g n ∘ pullbackCoh h n` with Mathlib's diagrammatic `≫` (so (h ∘ g)^* = g^* ∘ h^*) and `pullbackCoh (𝟙 X) n = id`, no sign, no scalar; (f₁ ≫ f₂)⁻¹ ≅ f₂⁻¹ ⋙ f₁⁻¹ and (𝟙 X)⁻¹ ≅ 𝟭 by `leftAdjointUniq`, compatible with f⁻¹ℚ_X ≅ ℚ_Y (`pullbackQX_comp`, `pullbackQX_id`); `pullbackCohLinear` carries upstream's ℚ-structure `fieldCohomologyModule ℚ` (`rfl` against `inferInstance`)".
   - column "Results whose truth depends on it": append "; `pullbackCoh_comp`, `pullbackCoh_id` and every T1 computation through a square f ≫ prod.fst = prod.fst ≫ i (`weil-space`, `de-rham-pullback`, `elliptic-square-cohomology`)".
   - column "Status": append "; functoriality checked at `2ead713` (red team 2026-11-27, `pullback-functorial`)".

## Optional

1. Generalize `pullbackQComp` and `pullbackQId` to any coefficient category `A` with the variables of `TopCat.Sheaf.pullback` (`Topology/Sheaves/Functors.lean`, lines 80 to 84), for example `sheafPullbackComp A f₁ f₂ := (pullbackPushforwardAdjunction A (f₁ ≫ f₂)).leftAdjointUniq ((pullbackPushforwardAdjunction A f₂).comp (pullbackPushforwardAdjunction A f₁))` and `sheafPullbackId A X := (pullbackPushforwardAdjunction A (𝟙 X)).leftAdjointUniq Adjunction.id`, keeping `pullbackQComp := sheafPullbackComp (ModuleCat.{0} ℚ)` (the agreement is `rfl`, scratch K). `supported-pullback-functorial` then reuses it at `AddCommGrpCat.{0}`. Update the gaps row names if adopted.
2. Add the square lemma, which `elliptic-square-cohomology` and `weil-space` will each write otherwise (scratch M, kernel under 0.2 s):

   ```lean
   theorem pullbackCoh_comm {W X Y Z : Over (Spec ↧ℂ)} (f : W ⟶ X) (g : X ⟶ Z) (f' : W ⟶ Y)
       (g' : Y ⟶ Z) (w : f ≫ g = f' ≫ g') (n : ℕ) (α : H^n(Z; ℚ)) :
       pullbackCoh f n (pullbackCoh g n α) = pullbackCoh f' n (pullbackCoh g' n α) := by
     rw [← pullbackCoh_comp, w, pullbackCoh_comp]
   ```

3. Pin the ℚ-structure in the test module against upstream's scalar action (scratch M, kernel 9.6 s):

   ```lean
   theorem pullbackCoh_fieldScalar {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X) (n : ℕ) (q : ℚ)
       (α : H^n(X; ℚ)) :
       pullbackCoh g n (Sheaf.H.map.{0} (fieldScalarSheaf ℚ X q) n α) =
         Sheaf.H.map.{0} (fieldScalarSheaf ℚ X' q) n (pullbackCoh g n α) := by
     rw [← field_smul_eq, ← field_smul_eq, ← pullbackCohLinear_apply, map_smul,
       pullbackCohLinear_apply]
   ```

4. Follow-ups outside this rung: `pullbackConst_comp` and `pullbackConst_id` at coefficients ℚ (three rewrites through `pullbackH_eq_pullbackConst` and `pullbackH_comp`) belong in the module of `supported-pullback-functorial`, which already imports the port; do not import `HodgeLadder.Supported.Pullback` here.

## What was tried and failed

- `rfl` for `pullbackCoh_comp` (heartbeat timeout at `isDefEq`), `rfl` for `pullbackCoh_id` (type mismatch), `simp [pullbackCoh, pullbackH]` for the identity law (goal left open, kernel timeout): no trivial proof.
- Searching for a degenerate source of truth: no local definition in the statements; `H^n(X; ℚ)` is nonzero in degree 2 on ℙ¹ (`projective-line-class-nonzero`), so neither law is vacuous.
- Cheaper spellings of the linear map: a named `abbrev` of the type (worse, 14.9 s), `restrictScalars ℚ` (6.5 s), the semiring written as `Ring.toSemiring` (5.1 s against 7.5 s), the composition law through `toAddMonoidHom` (24.5 s, since it still mentions `pullbackCohLinear`), a generic lemma instantiated at `H^n(X; ℚ)` (8.0 s, the cost is in the instantiated type). Only the shortcut instance removed the cost, and it is not admissible without a decision.
- A sign or scalar between `pullbackH_comp` and the port's pullback: excluded, both identities are exact and compose by rewriting.
