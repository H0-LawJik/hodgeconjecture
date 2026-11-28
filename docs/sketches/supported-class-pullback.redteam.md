# Red team: `supported-class-pullback`

Verdict: **pass with changes**

Candidate: WIP commit `5cb56b8` on `track/supported-class-pullback`, `HodgeLadder/Supported/Class/Pullback.lean` (namespace `HodgeLadder.Supported`), built against upstream `2ead713`. Red team 2026-11-27.

Read: the ledger entries `supported-class-pullback`, `supported-pullback-transport`, `local-class-pullback-submersion`, `fibre-class-pullback`, `cup-pullback`, `one-is-kappa`, `supported-pair-forget`, `cycle-class-germ`; `python3 tools/next.py` for the first three; `docs/sketches/cycle-class-multiplicative.md` (sub-rung table) and finding 15 of `docs/sketches/cycle-class-multiplicative.redteam.md`; `HodgeLadder/Cup/{Pullback,PullbackVariety,OneIsKappa,AbYoneda,SupportedPair,SupportedPairForget,SupportedFinal}.lean`; the port's `port/LefschetzPort/Oka/Topology/Sheaves/Cohomology/Pullback.lean` (`H.mapOfExact`, `pullbackAb`, `pullbackConstantSheafIso`, `pullbackConstZIso`, `H.pullback`); upstream `Definitions/AlgebraicGeometry/Cohomology/WithSupport.lean` (`forgetSupport`, the `H_[Z]^n(X; K)` notation), `Definitions/AlgebraicTopology/Support/Cohomology.lean` (`supportH`, `supportH.forget`), `Mathlib/CategoryTheory/Sites/SheafCohomology/Pair.lean` (`pairSheaf`, `pairSheafMap`, `relH`, `relH.forget`), `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean` and `Other/AlgebraicGeometry/Cycle/FundamentalClass.lean` (`cycleComponentSupportedInjectiveClass`, `_unique`); Mathlib `Algebra/Homology/DerivedCategory/Ext/Map.lean`; `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`.

Scratch: `scratch_rt/Probe1.lean` to `Probe8.lean` in the worktree, against the built `.olean`; deleted after the pass. Every Lean claim below marked "scratch" elaborated there.

## Findings

1. **The construction is the literature's pullback of cohomology with supports.** `docs/references.md` lists `Bredon1997` (sheaf cohomology with supports, sections unverified) and `Iversen1986` (cohomology with supports, chapters unverified); neither text is in the repository, so the definition below is recalled, unverified, and no quotation is possible. The standard map: for continuous f : Y → X, closed Z ⊆ X and closed Z' ⊇ f⁻¹Z, the inverse image f⁻¹ is exact and f⁻¹ Γ_Z → Γ_{Z'} f⁻¹ gives H^n_Z(X; F) → H^n_{Z'}(Y; f⁻¹F); in the pair model H^n_Z(X; F) = Ext^n(ℤ[X, X ∖ Z], F), it is "apply f⁻¹, precompose with ℤ[Y, Y ∖ Z'] → f⁻¹ ℤ[X, X ∖ Z]". Field by field against the Lean:

   | Field | Literature (recalled) | Lean | Match |
   |---|---|---|---|
   | Source group | H^n_Z(X; A_X) | upstream `TopCat.Sheaf.supportH X Z A_X n` = `Ext (pairSheaf (X ∖ Z ⟶ ⊤)) A_X n` | yes (`forgetSupport_eq` is `rfl`) |
   | Support condition | Z' ⊇ f⁻¹Z | `hZ : ⇑(Point.continuousMap g) ⁻¹' Z ⊆ Z'`, turned into `Z'.compl ≤ f⁻¹(Z.compl)` by `compl_le_of_preimage_subset` | yes; strictly more general than the ledger title (target f⁻¹S), which `supportedPullbackPreimage` recovers |
   | Functor | exact f⁻¹ | the port's `pullbackAb f = TopCat.Sheaf.pullback AddCommGrpCat f`, applied by `Ext.mapExactFunctor` | yes |
   | Pair map | ℤ[Y, Y ∖ Z'] → f⁻¹ℤ[X, X ∖ Z], from j_! commuting with f⁻¹ | `supportPairMap`: `pairSheafMap` along Y ∖ Z' ≤ f⁻¹(X ∖ Z), then `pairPullback`, the cokernel map of `freePullback : ℤ[f⁻¹U] ⟶ f⁻¹ℤ[U]`, which classifies the unit image of the generator of `ℤ[U]` | yes; the Lean does not prove `freePullback` an isomorphism, and nothing here needs it |
   | Coefficients | f⁻¹A_X ≅ A_Y | `(pullbackConstantSheafIso f).hom.app A`, uniqueness of left adjoints | yes |
   | Forget compatibility | Γ_Z → Γ is natural in f | `supportH_forget_supportPullback` (any space, any A), then `forgetSupport_supportedPullback` against `HodgeLadder.Cup.pullbackCoh` | yes |

   `pp.fullNames` (scratch, Probe8) confirms the right-hand side is `HodgeLadder.Cup.pullbackCoh g n`, the declaration rung `cup-pullback` proves additive, multiplicative and unital, and that `forgetSupport` is upstream's `AlgebraicGeometry.ComplexPoint.forgetSupport`. No local shadow exists.

2. **The hypotheses can be satisfied.** `forgetSupport_supportedPullback` has none beyond the data. The non-vacuity theorem's instance hypotheses hold on pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹ (scratch, Probe1, about 16 s):

   ```lean
   open HodgeLadder.Tests in
   attribute [local instance] p1p1_openParacompactSpace in
   example : ∃ α : H_[⊤]^0(projectiveLine; ℚ),
       supportedPullback (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤ (Set.subset_univ _) 0 α ≠ 0 :=
     supportedPullback_top_ne_zero _
   ```

   This is the morphism `fibre-class-pullback` first uses, so the test sits on the consumer's own data (change 3).

3. **The conclusion is not trivially true.** Attempts, all failed as they should: `with_reducible_and_instances rfl` on `pullbackH_eq_pullbackConst` ("not definitionally equal"); `simp [pullbackH, pullbackConst]` (unsolved goal, then kernel deterministic timeout); `simp [supportedPullback, pullbackCoh, forgetSupport]` on the forget identity (unsolved, kernel timeout). The zero map is ruled out: in scratch (Probe2), on any X' that is integral, smooth, T2, paracompact on opens and has a complex point, `¬ ∀ α : H_[⊤]^0(X; ℚ), forgetSupport ℚ X' ⊤ 0 0 = pullbackCoh g 0 (forgetSupport ℚ X ⊤ 0 α)` holds, through `pullbackCoh_one` and `oneSing_ne_zero`. No `ℕ∞`, no empty index type, no definition that unfolds to `True`; `hZ` is used in the definition. A global −1 in degree 0 is also excluded by the degree-zero test, since 1 ≠ −1 in H⁰(X'; ℚ) ≠ 0.

4. **What the identity pins, and what it leaves open.** The identity determines `supportedPullback g Z Z'` only through `forgetSupport` on X', which is injective when Z' = ⊤ (upstream `forgetSupport_injective_of_eq_top`) and far from injective in general. Pinned case (scratch, Probe1):

   ```lean
   example {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X) (Z : Closeds (ComplexPoint X)) (n : ℕ)
       (α : H_[Z]^n(X; ℚ)) (β : H_[⊤]^n(X'; ℚ))
       (hβ : forgetSupport ℚ X' ⊤ n β = pullbackCoh g n (forgetSupport ℚ X Z n α)) :
       supportedPullback g Z ⊤ (Set.subset_univ _) n α = β :=
     forgetSupport_injective_of_eq_top ℚ X' ⊤ rfl n
       ((forgetSupport_supportedPullback g Z ⊤ _ n α).trans hβ.symm)
   ```

   Unpinned case: on the complex line with Z' = {0} and n = 2, H²_{0}(ℂ; ℚ) ≅ ℚ and H²(ℂ; ℚ) = 0 (recalled), so the identity reads 0 = 0 and any map into ker `forgetSupport` would satisfy it as well. The supported map with Z' ≠ ⊤ is pinned by `supported-pullback-transport` (finding 9), and its first positive-degree value test is `fibre-class-pullback` itself. Record the gap in the ledger note (change 5).

5. **Interface axioms.** Not an interface rung: no structure, no `Prop` hypothesis standing for a missing object (decision 0003).

6. **Checker and axioms.** `python3 tools/check.py --no-build` in the worktree: `ACCEPTED (no sorry)`, `ACCEPTED (import clash: none with Mathlib)`, `ACCEPTED (ledger well-formed)`, `ACCEPTED: all checks passed`. The rung is not in the ledger yet, so the checker printed no axioms line for it. `#print axioms` in scratch (Probe1) on `forgetSupport_supportedPullback`, `pullbackH_eq_pullbackConst`, `supportH_forget_supportPullback`, `supportedPullback_top_ne_zero`, `exists_forgetSupport_supportedPullback_eq_one`, `forgetSupport_surjective_of_eq_top`, `conjExt_conjExt`, `conjExt_eq_of_natTrans`, `forgetPullbackMate_square`, `terminal_square`: each depends on `[propext, Classical.choice, Quot.sound]` only.

7. **Signs and normalizations.** No −1 appears and nothing other than Mathlib's Koszul conventions is forced; the construction has no shift at all. Conventions the statement and proof use:

   | Convention | Where fixed | Choice | Truth depends on it |
   |---|---|---|---|
   | Inverse image | Mathlib `TopCat.Sheaf.pullback` (left adjoint of pushforward), for AddCommGrpCat (the port's `pullbackAb`) and for `ModuleCat ℚ` (`pullbackQ`) | standard | no sign possible |
   | f⁻¹A_X ≅ A_Y, f⁻¹ℚ_X ≅ ℚ_Y | port `pullbackConstantSheafIso`, `pullbackConstZIso`; ladder `pullbackQX` | `leftAdjointUniq` of the composite adjunction against `constantSheafAdj`; no sign, no scalar | the forget identity and `pullbackH_eq_pullbackConst`; `forgetPullbackMate_square` checks the two agree through `forgetQX` |
   | Ext on an exact functor | Mathlib `Ext.mapExactFunctor` | `Ext.mapExactFunctor_comp` (composition preserved exactly) and `Ext.mapExactFunctor_extClass` (extension classes go to extension classes, `Ext/Map.lean:230`) | a degree twist ε(n) would satisfy every checked law of `cup-pullback` (ε(n) = (−1)^n is multiplicative and unital) and cancel from both sides of the forget identity; `mapExactFunctor_extClass` fixes ε(1) = 1, and with multiplicativity ε(n) = 1 on Yoneda products of degree-one classes, which is all of Ext^n (recalled; no Lean statement at the pin). In even degree (cycle classes, degree 2p) ε(2p) = ε(1)^{2p} = 1 regardless |
   | Free sheaf generator | upstream `freeAbelianSheafHomAddEquiv`, `freeAbelianSheafGenerator`, `freeAbelianSheafTerminalIso` (`[𝟙 T] ↦ 1`, gaps row `freeAbelianSheafTerminalIso_hom_generator`) | maps out of ℤ[U] are sections over U | `terminal_square`; no sign |
   | κ : ℤ → ℚ | rung `one-is-kappa`; conventions row "Integer-to-rational coefficients" | n ↦ n · 1 | `pullbackH_eq_pullbackConst` (exact, no scalar) |

   None of these has a row in `docs/conventions.md`; add one (change 6). The truth of `forgetSupport_supportedPullback` depends on the coefficient isomorphisms only through their agreement, which is proved; the truth of `fibre-class-pullback` will depend on the pair map's normalization against `relativeCohomologyMap`, which is the transport rung.

8. **`pullbackH_eq_pullbackConst` is honest.** Left side: rung `cup-pullback`'s `pullbackH`, conjugation by `pullbackQ f` on Ext(ℚ_X, ℚ_X) in sheaves of ℚ-vector spaces, transported by `rationalExtEquiv`. Right side: the port's `H.pullback f` (Ext from ℤ_X in abelian sheaves, through `pullbackConstZIso`), then `H.map` of f⁻¹ℚ_X ≅ ℚ_Y. They live in different sheaf categories, `rfl` fails at reducible and instance transparency (finding 3), and the proof goes through `eq_kappa_comp_forgetEnd`, two `conjExt_conjExt` steps and the mate `forgetPullbackMate` of f_* ∘ forget = forget ∘ f_*. The identity is exact, no scalar. It settles the open item "agreement with the port's abelian-group pullback `TopCat.Sheaf.H.pullback`" in the `cup-pullback` note. It is an identity between two named constructions with consumers beyond this rung (any use of the port's `H.pullback`, which `port/LefschetzPort/Oka/Topology/Sheaves/Cohomology/{BaseChange,PushforwardAcyclic,PullbackZero}.lean` and `Oka/Geometry/RingedSpace/LocallyRingedSpace/{Cohomology,CohomologyBaseChange}.lean` use), so give it its own rung, `pullback-port-agreement`, in the same module, and update the `cup-pullback` note (change 5). A note edit alone would leave a checked identity without a ledger name, and the checker prints axioms only for ledger-named declarations.

9. **What remains for `fibre-class-pullback`, and the transport statement.** After this rung, `supported-pullback-transport` has both dependencies checked (`supported-pair-forget` is checked) and becomes ready. Its exact statement, which elaborates in scratch (Probe6, with `sorry`):

   ```lean
   variable {X X' : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
     [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
     [IsIntegral X'.left] [Smooth X'.hom] [T2Space (ComplexPoint X')]
     [∀ U : Opens (ComplexPoint X'), ParacompactSpace U]

   theorem supportedEquivPair_supportedPullback (g : X' ⟶ X) (Z : Closeds (ComplexPoint X))
       (Z' : Closeds (ComplexPoint X'))
       (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') (n : ℕ)
       (α : H_[Z]^n(X; ℚ)) :
       supportedEquivPair X' Z' n (supportedPullback g Z Z' hZ n α) =
         relativeCohomologyMap ℚ n
           (TopPair.ofSubsetHom (pointMap g) (fun _ ha => compl_le_of_preimage_subset g Z Z' hZ ha))
           (supportedEquivPair X Z n α)
   ```

   Its absolute case also elaborates (Probe6) and is unchecked anywhere on the ladder; it reads `pullbackCoh` in singular terms and is the Z = ⊤ shadow of the statement above:

   ```lean
   theorem singular_pullbackCoh (g : X' ⟶ X) (n : ℕ) (β : H^n(X; ℚ)) :
       rationalCohomologyAddEquivSingularCohomology X' n (pullbackCoh g n β) =
         cohomologyMap ℚ n (pointMap g) (rationalCohomologyAddEquivSingularCohomology X n β)
   ```

   The proof needs an input the ladder lacks: a cochain map f⁻¹ 𝒮•_X → 𝒮•_Y of sheafified singular cochain complexes (adjoint to the presheaf map 𝒮•_X(U) → 𝒮•_Y(f⁻¹U) given by cochain pullback along f restricted to f⁻¹U → U), compatible with the augmentations `iotaQ`, and naturality of upstream's `relHAddEquivSupportedSectionsHomologyOfFlasque` and `supportedRationalSingularSectionCohomologyEquivRelative` for such a map. Upstream's flasque model takes a flasque resolution and f⁻¹ does not preserve flasqueness, so the comparison runs through the Hom-complex naming of classes (`supCocycle`) on the Y side. The thinker should split this out before a prover starts.

   With the transport and `local-class-pullback-submersion` checked, `fibre-class-pullback` still needs: (a) `hZ` for the cycle supports, which on the first use is cheap from `HodgeLadder.Tests.mem_p1p1FibreFst_support_iff_fst` and the closed point `infty`; (b) at each y in X'(ℂ) ∖ Z'_sing, an adapted chart on X' in which g is a coordinate projection of a chart adapted to Z on X (for pr₁, the product chart of rung `complex-points-prod`); (c) the germ form on both sides, `HodgeLadder.Normalization.transport_supportedClass_eq_chartNormalProjectionCoclass` and `germ_coclassSection_eq` (rung `cycle-class-germ`) with `normalization_singular`; (d) sections of the local relative-cohomology sheaf agree when all germs agree (Mathlib); (e) `cycleComponentSupportedInjectiveClass_unique` to conclude `supportedPullback g Z_x Z_x' hZ (2p) η_x = η_x'`, then `forgetSupport_supportedPullback`. Functoriality in g is not on this route.

10. **Functoriality.** Not required by the route in finding 9. Follow-up rung `supported-pullback-functorial`, both statements elaborating in scratch (Probe7, with `sorry`; `Point.continuousMap (h ≫ g) = Point.continuousMap g ∘ Point.continuousMap h` holds by `rfl`, so the composite support hypothesis is `fun _ ha => hZ' (hZ ha)`):

    ```lean
    theorem supportedPullback_id {X : Over (Spec ↧ℂ)} (Z : Closeds (ComplexPoint X)) (n : ℕ)
        (α : H_[Z]^n(X; ℚ)) :
        supportedPullback (𝟙 X) Z Z (fun _ h => h) n α = α

    theorem supportedPullback_comp {X X' X'' : Over (Spec ↧ℂ)} (h : X'' ⟶ X') (g : X' ⟶ X)
        (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
        (Z'' : Closeds (ComplexPoint X''))
        (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z')
        (hZ' : ⇑(Point.continuousMap h) ⁻¹' (Z' : Set (ComplexPoint X')) ⊆ Z'') (n : ℕ)
        (α : H_[Z]^n(X; ℚ)) :
        supportedPullback (h ≫ g) Z Z'' (fun _ ha => hZ' (hZ ha)) n α =
          supportedPullback h Z' Z'' hZ' n (supportedPullback g Z Z' hZ n α)
    ```

    Mathlib at the pin has `Ext.mapExactFunctor` for `F ⋙ G` (`Ext/Map.lean:254`) and no identity or composition isomorphism for `TopCat.Sheaf.pullback`, so these need `pullback (h ≫ g) ≅ pullback g ⋙ pullback h` built from `leftAdjointUniq` and its compatibility with `pullbackConstantSheafIso`. `supportedPullback_id` with Z = ⊤ in positive degree would give the first positive-degree value test of this rung without `fibre-class-pullback`.

11. **Kernel cost.** `lake env lean -Dprofiler=true -Dprofiler.threshold=3000` on the module: 3 min 0 s wall, `type checking 164s`, spread over eleven declarations between 4.6 s and 30.6 s (the profiler output does not name them), elaboration 3.3 s, tactics 14.3 s. The module has no downstream modules. Accept, and record it in `docs/gaps.md` "Known weaknesses" (change 7), next to the `CycleClassSignTestP2` row, which has the same cause: types restating upstream's `H_[Z]^n(X; ℚ)` at `TopCat.of (ComplexPoint X)`.

12. **Elaboration gotchas worth a gaps row.** (a) In scratch (Probe3), `forgetSupport ℚ X Z n α = TopCat.Sheaf.supportH.forget Z _ n α := rfl` without the space fails with "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000)"; with `(X := TopCat.of (ComplexPoint X))` it checks at once, as in the candidate's `forgetSupport_eq`. The unifier has to solve `↥?T =?= ComplexPoint X` from `Z : Closeds (ComplexPoint X)`. (b) In `forgetSupport_surjective_of_eq_top`, instance search does not find `IsIso (cokernel.π (… .map (homOfLE (le_top : Z.compl ≤ ⊤))))` at `TopCat.of (ComplexPoint X)` (scratch, Probe4: "failed to synthesize", then a `whnf` timeout), and the candidate works around it by naming upstream's auto-generated instance `TopCat.Sheaf.instIsIsoSheafOpensCarrierGrothendieckTopologyAddCommGrpCatπMapFreeAbelianSheafOfFactEqBot`. That name is generated from the instance's type and changes when upstream edits it, so a pin bump can break the file for a reason unrelated to the mathematics. The same fact proved at a variable space finds the instance; replacement in change 2 (scratch, Probe5, checks in about 24 s). Both belong with the existing instance-search rows (`TopCat.of T` discrimination keys), in gaps, since neither is a sign or normalization convention.

13. **Placement.** `HodgeLadder/Supported/Class/Pullback.lean` is `next.py`'s fallback from the rung id; the `Class` segment carries no meaning. The existing supported modules are `HodgeLadder/Cup/Supported*.lean` in namespace `HodgeLadder.Cup`, built for front `cup`, which decision 0012 closed. This rung belongs to the `fibre-class-pullback` family, already uses namespace `HodgeLadder.Supported`, and defines generic names (`free`, `terminal_square`, `unit_forgetQX`) that should stay out of `HodgeLadder.Cup`. Recommend `HodgeLadder/Supported/Pullback.lean`, module `HodgeLadder.Supported.Pullback`, namespace unchanged, and the ledger `module` of `supported-pullback-transport` set to `HodgeLadder.Supported.PullbackTransport`, so the family shares a directory. Move the two non-vacuity theorems to `HodgeLadder/Tests/SupportedPullback.lean` under a test rung, as `supported-pair-forget-test` does for `supported-pair-forget`. They are the only users of `HodgeLadder.Cup.SingularUnit` (layer 21); with them moved, the main module's layer drops from 22 to 5 (`python3 tools/pinwalk.py` graph: `Cup.PullbackVariety` 4, `Cup.OneIsKappa` 4, the port's `Cohomology.Pullback` 1, `General.FreeAbelianTerminal` 0), which matters to the pin walk once the transport rung imports it. The test module's layer is 22.

14. **Docstring and style.** The module docstring's "Main definitions" omits `free` and `preimageSupport`, and "Main results" omits `forgetSupport_surjective_of_eq_top`, `terminal_square`, `conjExt_conjExt`, `conjExt_eq_of_natTrans`, `forgetPullbackMate_square`, `unit_forgetQX`. Line 34 has 156 characters and line 500 has 107; there are double blank lines at 167 to 168, 280, 283 to 284 and 445. `unit_forgetQX` restates the step `F2` inside `HodgeLadder.Cup.adj_tensorQSheafInt_comp_forgetQX` (`OneIsKappa.lean:53`); leave `OneIsKappa` alone in this pull request (one Lean file) and note the duplicate in the gaps row.

15. **Drift.** The candidate was built on `a568e7b`; `main` is at `cf87c43`. `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` and `port/` are unchanged between them (upstream pin `2ead713` on both; `.lake/packages/HodgeConjecture` is at `2ead713`), and `git diff a568e7b main -- HodgeLadder/Cup HodgeLadder/General port` is empty, so no definition this rung depends on moved. `git merge-tree` reports one textual conflict, in `HodgeLadder.lean` (both sides append imports); rebase onto `main` before the ledger edits, since `main` changed `ledger/ladder.json`, `docs/gaps.md`, `docs/conventions.md` and `docs/roadmap.md` (change 9). Upstream definitions on the route: `supportH`, `supportH.forget`, `relH`, `relH.forget`, `pairSheaf`, `pairSheafMap`, `freeAbelianSheafHomAddEquiv`, `freeAbelianSheafTerminalIso`, `H'.addEquivTerminal`, `forgetSupport`, `constantFunctor`. `forgetSupport_eq` is an `rfl` pin of the last against `supportH.forget`, so a bump that changes `forgetSupport` breaks the build here.

## Required changes

1. **Move and split.** Rename the module to `HodgeLadder/Supported/Pullback.lean` (`HodgeLadder.Supported.Pullback`), keep namespace `HodgeLadder.Supported`, drop `public import HodgeLadder.Cup.SingularUnit` from it, and move `exists_forgetSupport_supportedPullback_eq_one` and `supportedPullback_top_ne_zero` to a new `HodgeLadder/Tests/SupportedPullback.lean` (namespace `HodgeLadder.Tests`, importing `HodgeLadder.Supported.Pullback`, `HodgeLadder.Cup.SingularUnit`, `HodgeLadder.Tests.P1p1Witness`). Update `HodgeLadder.lean` with both imports. Keep `forgetSupport_surjective_of_eq_top` in the main module.

2. **Replace the auto-generated instance name.** In the main module, replace the body of `forgetSupport_surjective_of_eq_top` by this lemma and proof:

   ```lean
   omit g in
   /-- With `W = ⊥`, forgetting the pair `(V, W)` is surjective, on any space. -/
   theorem relH_forget_surjective_of_eq_bot (T : TopCat.{0})
       (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) {W V : Opens T}
       (f : W ⟶ V) (hW : W = ⊥) (n : ℕ) :
       Function.Surjective (CategoryTheory.Sheaf.relH.forget F f n) :=
     haveI : Fact (W = ⊥) := ⟨hW⟩
     (Abelian.Ext.precompAddEquiv (asIso (cokernel.π
       ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)).map f))) F n).surjective

   omit g in
   /-- With support the whole space, forgetting the support is surjective. -/
   theorem forgetSupport_surjective_of_eq_top (Z : Closeds (ComplexPoint X)) (hZ : Z = ⊤)
       (n : ℕ) : Function.Surjective (forgetSupport ℚ X Z n) :=
     (Sheaf.H'.addEquivTerminal isTerminalTop _ n).surjective.comp
       (relH_forget_surjective_of_eq_bot (TopCat.of (ComplexPoint X)) _ _ (by rw [hZ]; ext; simp) n)
   ```

   (Checked in scratch outside the section; adjust `omit` to the section's variables.)

3. **Add the consumer's instance as a test**, in `HodgeLadder/Tests/SupportedPullback.lean`:

   ```lean
   attribute [local instance] p1p1_openParacompactSpace in
   /-- **Non-vacuity on the first use**: along pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹, with support the whole space,
   the supported pullback is nonzero in degree zero. -/
   theorem supportedPullback_prodFst_ne_zero :
       ∃ α : H_[⊤]^0(projectiveLine; ℚ),
         supportedPullback (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤ (Set.subset_univ _) 0 α ≠ 0 :=
     supportedPullback_top_ne_zero _
   ```

4. **Module docstrings.** Main module, "Main definitions": add `HodgeLadder.Supported.free`, `HodgeLadder.Supported.preimageSupport`. "Main results": replace the list by

   ```
   * `HodgeLadder.Supported.supportH_forget_supportPullback`, `HodgeLadder.Supported.terminal_square`
   * `HodgeLadder.Supported.pullbackH_eq_pullbackConst`, `HodgeLadder.Supported.forgetPullbackMate_square`,
     `HodgeLadder.Supported.unit_forgetQX`, `HodgeLadder.Supported.conjExt_conjExt`,
     `HodgeLadder.Supported.conjExt_eq_of_natTrans`
   * `HodgeLadder.Supported.forgetSupport_supportedPullback`
   * `HodgeLadder.Supported.relH_forget_surjective_of_eq_bot`,
     `HodgeLadder.Supported.forgetSupport_surjective_of_eq_top`
   ```

   and wrap line 34 at 100 characters. Test module: its own docstring naming the three tests and rung `supported-class-pullback-test`.

5. **Ledger** (after the rebase of change 9).
   - `supported-class-pullback`: `status` `checked`; `module` `HodgeLadder.Supported.Pullback`; `declarations` `HodgeLadder.Supported.supportedPullback`, `supportedPullbackPreimage`, `preimageSupport`, `compl_le_of_preimage_subset`, `forgetSupport_eq`, `forgetSupport_supportedPullback`, `supportPullback`, `supportPairMap`, `pairPullback`, `freePullback`, `freePullback_naturality`, `terminal_square`, `supportH_forget_supportPullback`, `relH_forget_surjective_of_eq_bot`, `forgetSupport_surjective_of_eq_top` (each with the `HodgeLadder.Supported.` prefix); `depends_on` `["cup-pullback", "pullback-port-agreement"]`; `note`: "Checked 2026-11-27. For g : X' ⟶ X over Spec ℂ and closed Z' ⊇ g⁻¹Z (as sets of complex points), supportedPullback g Z Z' hZ n : H_[Z]^n(X; ℚ) →+ H_[Z']^n(X'; ℚ) applies the exact inverse image f⁻¹ of abelian sheaves (the port's pullbackAb), precomposes with the pair map ℤ[Y, Y ∖ Z'] ⟶ f⁻¹ℤ[X, X ∖ Z] (cokernel map of ℤ[f⁻¹U] ⟶ f⁻¹ℤ[U], the unit image of the generator) and postcomposes with f⁻¹ℚ_X ≅ ℚ_Y. forgetSupport_supportedPullback: forgetSupport (g^* α) = pullbackCoh g (forgetSupport α), exact, no sign, through supportH_forget_supportPullback (any space, any coefficients) and pullbackH_eq_pullbackConst. The identity pins the supported map only when Z' = ⊤ (forgetSupport injective there); for Z' ≠ ⊤ it is pinned by supported-pullback-transport. Degree-zero tests in supported-class-pullback-test. Open: functoriality in g (supported-pullback-functorial). Red team docs/sketches/supported-class-pullback.redteam.md."
   - New rung `pullback-port-agreement`: `title` "cup-pullback's rational pullback pullbackH equals the port's abelian pullback TopCat.Sheaf.H.pullback followed by f⁻¹ℚ_X ≅ ℚ_Y, exactly"; `status` `checked`; `kind` `foundation`; `module` `HodgeLadder.Supported.Pullback`; `declarations` `HodgeLadder.Supported.pullbackH_eq_pullbackConst`, `pullbackConst`, `forgetPullbackMate`, `unit_forgetPullbackMate`, `forgetPullbackMate_square`, `unit_forgetQX`, `pullbackConstZIso_inv_kappa`, `conjExt_conjExt`, `conjExt_eq_of_natTrans` (prefix `HodgeLadder.Supported.`); `depends_on` `["cup-pullback", "one-is-kappa"]`; `note`: "Checked 2026-11-27. For continuous f : Y ⟶ X, pullbackH f n α = H.map (f⁻¹ℚ_X ≅ ℚ_Y) (H.pullback f α) on HQ X n, no sign, no scalar. The comparison f⁻¹(forget M) ⟶ forget(f⁻¹M) is the mate of f_* ∘ forget = forget ∘ f_*; it matches the two identifications of f⁻¹ℚ_X with ℚ_Y (forgetPullbackMate_square), and κ : ℤ_X → ℚ_X (one-is-kappa) moves the unit. Settles the agreement item of cup-pullback. Red team docs/sketches/supported-class-pullback.redteam.md, finding 8."
   - New rung `supported-class-pullback-test`: `kind` `test`; `status` `checked`; `module` `HodgeLadder.Tests.SupportedPullback`; `declarations` `HodgeLadder.Tests.exists_forgetSupport_supportedPullback_eq_one`, `HodgeLadder.Tests.supportedPullback_top_ne_zero`, `HodgeLadder.Tests.supportedPullback_prodFst_ne_zero`; `depends_on` `["supported-class-pullback", "p1p1-witness"]`; `note`: "Degree zero, support the whole space only: rules out the zero map and a global sign in degree 0, and instantiates on pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹. Positive degrees and supports Z' ≠ ⊤ are untested here; the first value test there is fibre-class-pullback (pr₁*[∞] = [{∞} × ℙ¹])."
   - `cup-pullback` `note`: replace "Open: agreement with the port's abelian-group pullback TopCat.Sheaf.H.pullback, and functoriality in g." by "Agreement with the port's abelian-group pullback TopCat.Sheaf.H.pullback: checked, pullbackH_eq_pullbackConst (rung pullback-port-agreement). Open: functoriality in g, and agreement with singular cohomologyMap (absolute case of supported-pullback-transport)."
   - `supported-pullback-transport` `note`: replace "Not attempted." by "Statement: supportedEquivPair X' Z' n (supportedPullback g Z Z' hZ n α) = relativeCohomologyMap ℚ n (TopPair.ofSubsetHom (pointMap g) (fun _ ha => compl_le_of_preimage_subset g Z Z' hZ ha)) (supportedEquivPair X Z n α), for X, X' integral, smooth, T2 and paracompact on opens (elaborates at 2ead713). Missing input: a cochain map f⁻¹𝒮•_X ⟶ 𝒮•_Y of sheafified singular cochains over the augmentations, and naturality of upstream's flasque supported-sections model for it; split before proving. Absolute case: Ψ_{X'} (pullbackCoh g n β) = cohomologyMap ℚ n (pointMap g) (Ψ_X β)." and set its `module` to `HodgeLadder.Supported.PullbackTransport`.
   - `fibre-class-pullback` `note`: append "Remaining after supported-class-pullback: supported-pullback-transport, local-class-pullback-submersion, an adapted chart on X' in which g is a coordinate projection (complex-points-prod for pr₁), germ-to-section and cycleComponentSupportedInjectiveClass_unique; red team docs/sketches/supported-class-pullback.redteam.md, finding 9."
   - Bump `updated`.

6. **Conventions row.** Add to `docs/conventions.md` after "Pullback to an open":

   `| Pullback of cohomology and of cohomology with supports | this repository, `HodgeLadder.Cup.pullbackH`, `pullbackCoh`, `pullbackQX` (rung `cup-pullback`); `HodgeLadder.Supported.supportPullback`, `supportedPullback`, `supportPairMap`, `freePullback`, `pullbackConst` (rung `supported-class-pullback`), `pullbackH_eq_pullbackConst` (rung `pullback-port-agreement`); the port's `TopCat.Sheaf.H.pullback`, `pullbackConstantSheafIso`, `pullbackConstZIso` | Mathlib's inverse image `TopCat.Sheaf.pullback`; f⁻¹A_X ≅ A_Y and f⁻¹ℚ_X ≅ ℚ_Y by `leftAdjointUniq` against `constantSheafAdj`, no sign; classes move by `Ext.mapExactFunctor`, which preserves composition exactly and sends extension classes to extension classes (`Ext.mapExactFunctor_extClass`), so no degree twist; the pair map ℤ[Y, Y ∖ Z'] ⟶ f⁻¹ℤ[X, X ∖ Z] is the cokernel map of ℤ[f⁻¹U] ⟶ f⁻¹ℤ[U], the unit image of the generator, no sign | `forgetSupport_supportedPullback` and `pullbackH_eq_pullbackConst` (both exact); `fibre-class-pullback` and every identity built on it. A sign on the pair map would flip pr₁*[∞] = [{∞} × ℙ¹] and leave spans unchanged; a uniform twist (−1)^n would pass every checked law of `cup-pullback` and is excluded only by `mapExactFunctor_extClass` | checked at `2ead713` (red team 2026-11-27, `supported-class-pullback`); agreement with `relativeCohomologyMap` and `cohomologyMap` on singular cohomology open (rung `supported-pullback-transport`) |`

7. **Gaps rows** (`docs/gaps.md`, Layer after change 1, Opened 2026-11-27).
   - Homological algebra: `| `HodgeLadder.Supported.conjExt_conjExt` (conjugating twice is conjugating by the composite functor), `conjExt_eq_of_natTrans` (conjugations by two exact functors related by a natural transformation that matches the identifications agree); any abelian categories | `HodgeLadder.Supported.Pullback` | 5 | not in Mathlib at the pin; `Ext.mapExactFunctor_comp` and `Ext.mapExactFunctor_comp_mk₀_natTransApp` are the Mathlib inputs | 2026-11-27 |`
   - Sheaves and sheafification: `| `HodgeLadder.Supported.free`, `free_map_generator`, `freePullback`, `freePullback_naturality`, `pairPullback`, `π_pairPullback`, `constantSheafAdj_unit_apply`, `pullbackConstZIso_inv_apply`, `pullbackConstZIso_inv_generator`, `terminal_square` (inverse image of free and pair sheaves on any topological space); `forgetPullbackMate`, `unit_forgetPullbackMate`, `unit_forgetQX`, `forgetPullbackMate_square`, `pullbackConstZIso_inv_kappa` (inverse images of abelian and of rational sheaves agree through `forget`) | `HodgeLadder.Supported.Pullback` | 5 | not in Mathlib or upstream at the pin; `unit_forgetQX` restates the step `F2` inside `HodgeLadder.Cup.adj_tensorQSheafInt_comp_forgetQX`, so derive that one from it when `OneIsKappa` is next edited | 2026-11-27 |`; and add `HodgeConjecture/Mathlib/CategoryTheory/Sites/SheafCohomology/` (upstream's `pairSheaf`, `freeAbelianSheafTerminalIso`) to the category's "Diff at a bump" list.
   - Local cohomology, orientation and the cycle class: `| `HodgeLadder.Supported.supportPairMap`, `supportPullback`, `supportH_forget_supportPullback` (pullback of cohomology with supports along any continuous map, any coefficient group, compatible with `supportH.forget`), `relH_forget_surjective_of_eq_bot` | `HodgeLadder.Supported.Pullback` | 5 | upstream has `supportH`, `supportH.forget` and `relH.forget_injective_of_eq_bot` and no pullback in the space | 2026-11-27 |`
   - Port-specific: `| `HodgeLadder.Supported.pullbackConst`, `pullbackH_eq_pullbackConst` (the ladder's rational `pullbackH` equals the port's `H.pullback` followed by f⁻¹ℚ_X ≅ ℚ_Y) | `HodgeLadder.Supported.Pullback` | 5 | stated against the port's `Oka/Topology/Sheaves/Cohomology/Pullback.lean`; recheck when that file is refreshed from the Lefschetz stack | 2026-11-27 |`
   - Known weaknesses: `| `HodgeLadder.Supported.Pullback` takes about 3 minutes to elaborate, 164 s of it kernel type checking over eleven declarations of 4.6 s to 30.6 s (`lake env lean -Dprofiler=true`, 2026-11-27); same cause as `CycleClassSignTestP2`, types restating upstream's `H_[Z]^n(X; ℚ)` at `TopCat.of (ComplexPoint X)`. No downstream modules yet; accepted | Rebuild time on edits; importers read the `.olean` | 2026-11-27 |`
   - Known weaknesses: `| At `TopCat.of (ComplexPoint X)`, `forgetSupport ℚ X Z n α = TopCat.Sheaf.supportH.forget Z _ n α := rfl` times out at `whnf` (200000 heartbeats) unless the space is given as `(X := TopCat.of (ComplexPoint X))`, and instance search misses `IsIso (cokernel.π ((freeAbelianSheaf _).map (homOfLE (le_top : Z.compl ≤ ⊤))))` under `Fact (Z.compl = ⊥)`, which it finds at a variable space (red team `supported-class-pullback`, finding 12). Workaround: name the space explicitly, and prove such facts at a variable `T : TopCat` and specialize (`relH_forget_surjective_of_eq_bot`); do not cite auto-generated instance names | A pin bump can rename an auto-generated instance and break a proof that names it | 2026-11-27 |`

8. **Roadmap.** Row `supported-class-pullback`: status `checked`, depends `cup-pullback`, `pullback-port-agreement`. Add rows `pullback-port-agreement` (foundation, checked, `cup-pullback`, `one-is-kappa`, "pullbackH = the port's H.pullback, exact") and `supported-class-pullback-test` (test, checked, `supported-class-pullback`, `p1p1-witness`, "degree zero, support ⊤, on pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹").

9. **Rebase** `track/supported-class-pullback` onto `main` (`cf87c43` or later) before changes 5 to 8; resolve the `HodgeLadder.lean` import conflict by keeping both sides. Rebuild and run `python3 tools/check.py`.

## Optional

- Open `supported-pullback-functorial` with the statements of finding 10 (kind `foundation`, `depends_on` `["supported-class-pullback"]`); with Z = ⊤ it gives the positive-degree value test this rung lacks.
- Open the absolute case `singular_pullbackCoh` of finding 9 as a first sub-rung of `supported-pullback-transport` if the thinker splits it; it also reads `pullbackCoh` against upstream's `cohomologyMap`, which no rung does yet.
- Remove the double blank lines listed in finding 14.

## What was tried and failed

- Proving the agreement by `rfl` at reducible and instance transparency, and by unfolding with `simp`: fails (different sheaf categories; kernel timeout).
- Proving the forget identity by unfolding with `simp`: fails.
- Replacing `supportedPullback` by `0` in the identity: refuted in degree zero on any X' with a complex point.
- Writing `forgetSupport_eq` without the explicit space: `whnf` timeout.
- Dropping the named instance from `forgetSupport_surjective_of_eq_top` and relying on instance search at `TopCat.of (ComplexPoint X)`: fails; the variable-space lemma of change 2 succeeds.
- Looking for a positive-degree value test of the supported map that avoids functoriality and the cycle class: none exists at the pin. Every candidate needs `pullbackCoh (𝟙 X) = id`, a retraction, or `fibre-class-pullback`.
