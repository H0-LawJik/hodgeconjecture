# Red team: `singular-cochain-pullback`

Verdict: **pass with changes**

Candidate: WIP commit `ef5fe80` on `track/singular-cochain-pullback`, `HodgeLadder/Supported/SingularCochainPullback.lean` (namespace `HodgeLadder.Supported`, plus the general `HodgeLadder.extendMap_single_square`), built against upstream `2ead713`. Issue #237, sub-rung R1 of `supported-pullback-transport`. Red team 2026-11-28.

Read: the ledger entries `singular-cochain-pullback`, `supported-class-pullback`, `ext-map-cocycle`, `supported-pullback-named`, `supported-pullback-section`, `supported-pair-named`, `end-class-right-mult`; `python3 tools/next.py singular-cochain-pullback`; `docs/sketches/supported-pullback-transport.md` (R1 statements, R3 to R5 consumers, the instance and transparency notes, the signs table); finding 9 of `docs/sketches/supported-class-pullback.redteam.md`; `HodgeLadder/Supported/Pullback.lean` (`supportPullback`, `supportedPullback`); `HodgeLadder/General/ExtMapCocycle.lean` at `main` `30ea512` (`mapExactFunctor_hom_named`); `HodgeLadder/Cup/EndClass.lean` (`iotaQ`); `HodgeLadder/Cup/SupportedFinal.lean` (`supCocycle`, the `HasDerivedCategory` local instances); `HodgeLadder/Hodge/RationalDeRhamComplex.lean` (generic extend layer); the port's `Oka/Topology/Sheaves/Cohomology/Pullback.lean`; upstream `Lemmas/AlgebraicTopology/Singular/Sheaf/CochainRestriction.lean` (whole file), `Definitions/AlgebraicTopology/Singular/Sheaf/Cochain.lean` (`constantSingularZeroCochain`, `constantsToSingularCochainZero`, `constantsToSingularCochainZeroSheaf`, `constantsToSingularCochainSheafComplex`), `Other/AlgebraicGeometry/Cohomology/SupportSingularComparison.lean` (`constantsToSingularCochainZero_comp_singularRestrictionToRawPushforward`), `Lemmas/AlgebraicGeometry/Cohomology/SingularComparison.lean`, `SingularSheafComparison.lean`, `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (`constantFieldSheafComplexIntIsoSingle`), `Mathlib/Algebra/Homology/MapExtend.lean` (`mapExtendCanonicalIso`); `docs/conventions.md`, `docs/gaps.md` (branch and `main`), `docs/references.md`.

Scratch: `scratch_rt_scp/` in the worktree (`Probe1` to `Probe4`, `NoOpt`, `NoOpt5`, `NoIota`, `IotaAlt`, `Orig`), against the built `.olean`; deleted after the pass. Every Lean claim marked "scratch" below elaborated there.

## Findings

1. **The map is the right one, and its coboundary square is exact.** Upstream's `singularRestrictionToRawPushforward R j n` is, on sections over V, the linear dual of `preimageOpenChainMap R j V`, the singular chain map of σ ↦ j ∘ σ from f⁻¹V to V; so a cochain φ goes to φ ∘ f_#, the textbook cochain pullback [`Hatcher2002`, recalled; section unverified for this use]. `singularRestrictionSheaf` sheafifies it (`sheafifyLift`, pinned by `toSheafify_comp_singularRestrictionSheaf`). The file name and docstring of upstream speak of open embeddings, but the variable is a bare `j : U ⟶ X` in `TopCat.{u}` and no openness is used anywhere in the file (read in full), so the candidate's use along any continuous `f` is sound. `singularPullbackSheaf f n` is `(pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv.symm` of it, the transpose under f⁻¹ ⊣ f_* (the counit after f⁻¹ of the restriction); the port's `pullbackAb f` is by `abbrev` Mathlib's `TopCat.Sheaf.pullback AddCommGrpCat f`, the left adjoint of that same adjunction, so the types match on the nose. This is the literature's map f⁻¹𝒮ⁿ_X → 𝒮ⁿ_Y adjoint to restriction of cochains [`Bredon1997`, ch. I to III; `Iversen1986`; sections unverified]. `singularPullbackSheaf_comm` is upstream's `singularRestrictionSheafComplex.comm` moved through `homEquiv_naturality_left_symm` and `_right_symm`: exact, no sign, no scalar. In scratch, the defining property is a one-line term, `(Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _) : unit.app _ ≫ (pushforward f).map (singularPullbackSheaf f n) = singularRestrictionSheaf ℚ f n` (with the transparency option; optional item O1).

2. **The constants pin is exact and uses the same iso as `supportedPullback`.** `constants_comp_singularPullbackSheaf` states `f⁻¹(ℚ_X → 𝒮⁰_X) ≫ singularPullbackSheaf f 0 = (pullbackConstantSheafIso f).hom.app (AddCommGrpCat.of ℚ) ≫ (ℚ_Y → 𝒮⁰_Y)`, an equality of sheaf maps with no scalar slot. The iso is the port's `leftAdjointUniq` of `pullbackConstantSheafAdj f` (= `constantSheafAdj ⋙ pullbackPushforwardAdjunction`) against `constantSheafAdj`, which is exactly the term `supportPullback` postcomposes with (`(TopCat.Sheaf.pullbackConstantSheafIso f).hom.app A`, `HodgeLadder/Supported/Pullback.lean:155`, with `A = AddCommGrpCat.of ℚ` in `supportedPullback`). The proof transposes both sides under `pullbackConstantSheafAdj`, reduces to global sections of the constant section r, and closes with upstream's raw identity (`constantsToSingularCochainZero_comp_singularRestrictionToRawPushforward`: the constant cochain r · ε restricts to r · ε). The upstream constant zero-cochain is `r • openZeroAugmentation`, value r on every point, so the factor is 1. `rfl`, `simp` and `aesop` each fail on the pin statement (scratch `Probe3`), so it does not hold by unfolding.

3. **Fit with R3: the consumer composite elaborates and closes, no sign.** In scratch (`Probe1`, with `ExtMapCocycle` copied from `main` `30ea512` because the branch predates #243), at `F = pullbackAb (pointMap g)` and `ι = iotaQ X`:
   - `comp_test`: `(F.mapCochainComplexSingleFunctor 0).inv.app _ ≫ F.mapHomologicalComplex.map (iotaQ X) ≫ singularPullbackInt g = (singleFunctor _ 0).map ((pullbackConstantSheafIso (pointMap g)).hom.app (AddCommGrpCat.of ℚ)) ≫ iotaQ X'`, by `rw [iotaQ_comp_singularPullbackInt, Iso.inv_hom_id_app_assoc]` (needs `respectTransparency false`; without it the `rw` fails on the `TopCat.Sheaf` versus `AbSheaf` spelling).
   - `named_test`: for `α : H_[Z]^n(X; ℚ)`, `z : PairCocycle X Z n` and `hα` in the sketch's form, `(α.mapExactFunctor F).hom ≫ (Q.map ((singleFunctor _ 0).map (pullbackConstantSheafIso …).hom.app ℚ ≫ iotaQ X'))⟦n⟧' = ShiftedHom.map (equivHomShift.symm (((cocycleMap F z).precomp ((F.mapCochainComplexSingleFunctor 0).inv.app _)).postcomp (singularPullbackInt g))) Q`, closed with no `sorry` by `mapExactFunctor_hom_named`, `comp_test`, `Cocycle.equivHomShift_symm_postcomp` and `Functor.commShiftIso_hom_naturality`.

   This is R3's `supportedPullback_named` minus the `supportPairMap` precomposition and the unfolding of `supportedPullback`. Notes for R3: `h` from `mapExactFunctor_hom_named` prints the pair sheaf as `Sheaf.pairSheaf (homOfLE _)` while `PairCocycle` prints `pairSheaf' …`; they agree by unfolding and `erw [h]` was needed. The constant sheaf appears as `𝓒(↧(ComplexPoint X); ℚ)` on one side and `(constantFunctor _).obj ℚ` on the other, same term. The two `HasDerivedCategory` instances were declared as `HasDerivedCategory.standard _` (conventions row "Derived-category instances in statements"); R3 must reuse `SupportedFinal`'s terms. `Probe1` took about 3 minutes wall time including the copied `ExtMapCocycle`.

4. **Non-vacuity: present, and of the right size for a foundation leaf.** `constants_comp_singularPullbackSheaf_ne_zero [Nonempty Y]` says the constants square is a nonzero map: the right side is a mono (`constantsToSingularCochainZeroSheaf_mono`, upstream) after an iso, applied to the nonzero constant section 1 (through the local `constantSheafIsoLocallyConstantSheaf`). In scratch, `singularPullbackSheaf f 0 ≠ 0` on nonempty Y follows in three lines, so a zero cochain pullback fails the test. Hypotheses satisfiable: `constants_comp_singularPullbackSheaf_ne_zero (𝟙 (TopCat.of PUnit.{1}))` elaborates, and `⟨Over.mk (𝟙 (Spec ↧ℂ)), Over.mk (𝟙 (Spec ↧ℂ)), ⟨𝟙 _⟩⟩ : ∃ X X' : Over (Spec ↧ℂ), Nonempty (X' ⟶ X)` gives a `g` for the `Variety` section (scratch). The test pins degree 0 only. Degrees n ≥ 1 enter through the definition alone, and R4 evaluates them on sections through `toSheafify_comp_singularRestrictionSheaf`; that is the right place, so no higher-degree test is required here.

5. **Transparency options: scoped per declaration, four of five needed.** Each `set_option backward.isDefEq.respectTransparency false in` is attached to one declaration. With all five removed (scratch `NoOpt`), `constants_comp_singularPullbackSheaf` (`rw` miss), `constants_comp_singularPullbackSheafComplex` (unsolved `simp` goal), `constants_comp_singularPullbackSheaf_ne_zero` (the `0` of the statement does not synthesize, then `rw` misses) and `singularPullbackInt` (instance failure) each fail on their own. With only the option on `iotaQ_comp_singularPullbackInt` removed (scratch `NoOpt5`), the file compiles with no error, kernel 37.5 s against 36.6 s with it. That option is unneeded; precedent: the red team of `simplicial-complex-span` deleted measured-unneeded copies. The option relaxes elaborator unification only; the kernel checks the resulting terms at full transparency, so it cannot make a false statement pass. It is not recorded in the module docstring (change 2).

6. **Kernel cost: about 37 s in one one-line theorem; accepted for a leaf, recorded.** `lake env lean -Dprofiler=true`: whole file 48 s wall, type checking 36.6 s (and 37.5 s on a second run, slightly above the 30 s in the brief); with `iotaQ_comp_singularPullbackInt` deleted (scratch `NoIota`) the file takes 7 s and no declaration exceeds 0.5 s of kernel time. The cost is the kernel unfolding `iotaQ X = (constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫ rationalToSingularCochainComplexInt X` to `extendSingleIso.inv ≫ extendMap (constantsToSingularCochainSheafComplex …)` across the `AnalyticAdditiveSheaf X` and `TopCat.Sheaf` spellings, the cause recorded in gaps' instance-search row. One attempt to cut it failed: unfolding with `simp only [iotaQ, rationalToSingularCochainComplexInt, constantsToSingularCochainComplexInt, constantFieldSheafComplexIntIsoSingle]` before the same term gave a type mismatch and still spent 23.7 s in the kernel (scratch `IotaAlt`). Well under the sketch's 600 s kill criterion. Consumers read the `.olean`.

7. **Instance claim confirmed; the local instances should be named.** At the pin, `inferInstance` fails for `(pullbackAb (pointMap g)).Additive` and `PreservesFiniteLimits (pullbackAb (pointMap g))` (scratch `Probe2`), while the variable-map theorems apply. The candidate installs them as anonymous `local instance`s in the `Variety` section. R3, R4 and the test need the same three at `pointMap g`; with anonymous instances each consumer must restate them, and the auto-generated names are fragile. Gaps' instance-search row records named `Prop`-valued local instances activated by `attribute [local instance]` as the ladder's pattern (change 3). `Prop`-valued instances carry no type-level risk (conventions row "Derived-category instances in statements").

8. **Placement, dependencies, axioms.**
   - `HodgeLadder/Supported/` is right: every consumer (R3 to R5) is a `Supported` module. The module name differs from the sketch's `HodgeLadder.Supported.CochainPullback` and from `next.py`'s default path `HodgeLadder/Singular/Cochain/Pullback.lean`; keep the candidate's name and record it in the ledger.
   - `python3 tools/pinwalk.py` graph: layer 17, driven by `HodgeLadder.Cup.EndClass` (layer 16, for `iotaQ`). The `General` section needs only the port, upstream and `HodgeLadder.General.LocallyConstantSheaf`; a split would put it at layer 2 (optional O3).
   - The module imports no `HodgeLadder.Supported.Pullback`. Its imports come from `end-class-right-mult` (`iotaQ`), `cup-pullback` (`pointMap`), `supported-raw-map` (`relSeq`) and the port; the ledger's only dependency, `supported-class-pullback`, is conceptual (the shared iso of finding 2). Add the three import rungs (change 5).
   - It imports one upstream `Other` module (`Other.AlgebraicGeometry.Cohomology.SupportSingularComparison`) for one `Prop` lemma; a drift in that lemma's statement breaks the build, so it needs no `rfl` pin under decision 0010. Ten other ladder modules already import `Other`.
   - `HodgeLadder.extendMap_single_square` is general (any preadditive categories with zero objects, additive `F`). Its content overlaps `HodgeLadder.mapHomologicalComplex_homFromSingleExtend` with `extendSingleIso_inv_comp_extendMap` (`HodgeLadder.Hodge.RationalDeRhamComplex`, layer 17), stated in the `homFromSingleExtend` spelling; importing that module would pull in the de Rham stack, so a local copy in the `extendSingleIso.inv ≫ extendMap` spelling that `iotaQ` unfolds to is justified, but the overlap goes in the gaps row (change 6). No name clash on `main`.
   - `#print axioms` (scratch `Probe2`): all fourteen declarations, `HodgeLadder.extendMap_single_square`, `singularPullbackSheaf`, `singularPullbackSheaf_comm`, `constants_comp_singularPullbackSheaf`, `singularPullbackSheafComplex`, `constants_comp_singularPullbackSheafComplex`, `pullbackAb_additive`, `pullbackAb_preservesFiniteLimits`, `pullbackAb_preservesFiniteColimits`, `constants_comp_singularPullbackSheaf_ne_zero`, `singularPullbackInt`, `iotaQ_comp_singularPullbackInt`, `PairCocycle`, `RelCochain`, depend on `[propext, Classical.choice, Quot.sound]` only. `python3 tools/check.py --no-build` on the branch exits 0 ("ACCEPTED: all checks passed"); it does not yet cover this module, which is neither root-imported nor named in the ledger (change 4).
   - `PairCocycle` is exactly the type of `HodgeLadder.Cup.supCocycle` (`SupportedFinal.lean:125`); `RelCochain` matches the sketch's R4 and R5 binders.

9. **Signs and scalars: none.** No sign or scalar other than 1 appears in any statement or proof. Conventions used, each checked against `docs/conventions.md`:

   | Convention | Where | Register row | Truth depends on it? |
   |---|---|---|---|
   | inverse image f⁻¹ as Mathlib's left adjoint of f_* | `TopCat.Sheaf.pullback`, port `pullbackAb` | "Pullback of cohomology and of cohomology with supports" | the type of every statement; no sign |
   | f⁻¹ℚ_X ≅ ℚ_Y by `leftAdjointUniq` | port `pullbackConstantSheafIso` | same row | yes: the pin is an equality; a scalar c here would have to appear on the right side, and the same iso is used by `supportPullback` |
   | cochain restriction φ ↦ φ ∘ f_# | upstream `singularRestrictionToRawPushforward` | missing; added by change 7 | the definition of the map; a sign (−1)^n per degree would break `singularPullbackSheaf_comm` |
   | adjoint transpose | `homEquiv.symm` of `pullbackPushforwardAdjunction` | missing; added by change 7 | no sign: Mathlib's `homEquiv` is counit after the left adjoint |
   | singular coboundary δφ = φ ∘ ∂ | upstream, Mathlib | "Singular coboundary" | the comm square, inherited from upstream's `singularRestrictionSheafComplex` |
   | constant zero-cochain r ↦ r · ε | upstream `constantSingularZeroCochain` | missing; added by change 7 | yes, through the pin; factor 1 by upstream's raw identity |
   | ℕ to ℤ extension and single complexes | upstream `mapExtendCanonicalIso`, Mathlib `extendSingleIso`, `mapCochainComplexSingleFunctor`, `singleMapHomologicalComplex` | missing; added by change 7 | identifications in degree 0, no sign; `mapExtendCanonicalIso_hom_f` makes it the identity through the canonical identifications |

   The downstream equality R6 (`supportedEquivPair_supportedPullback`) is sensitive to every factor in this table: an equality of classes is not invariant under a nonzero rational scalar. Spans would be.

10. **Equality first.** Every theorem in the rung is an exact identity of sheaf or complex maps (`singularPullbackSheaf_comm`, `constants_comp_singularPullbackSheaf`, `constants_comp_singularPullbackSheafComplex`, `iotaQ_comp_singularPullbackInt`); none holds up to a scalar. The rung is a step toward the equality `supportedEquivPair_supportedPullback` of rung `supported-pullback-transport` (R6, open) through R3, R4, R5; all those rungs exist in the ledger.

11. **Non-vacuity test by name.** The smallest test that fails if the cochain pullback were zero is `HodgeLadder.Supported.constants_comp_singularPullbackSheaf_ne_zero`, in the module, built from upstream's `AlgebraicTopology.Singular.constantsToSingularCochainZeroSheaf_mono` and the local `HodgeLadder.constantSheafIsoLocallyConstantSheaf`. It exists and is checked.

12. **Pin drift: none.** The branch, its base `9ee1b3b` and `main` `30ea512` all pin upstream `2ead713` and Lean and Mathlib `v4.35.0-rc4` (no diff in `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`). `main` has moved since the branch point: `ledger/ladder.json`, `docs/gaps.md` (rows renumbered, new rows), `docs/conventions.md`, `docs/roadmap.md`, `HodgeLadder.lean`, and `tools/check.py` (decision 0014, a scan of the build log for the placeholder warning). The candidate has no placeholder; the rebase must still run the new checker (change 1).

## Required changes

1. **Rebase** `track/singular-cochain-pullback` onto `main` (`30ea512` or later). Add `public import HodgeLadder.Supported.SingularCochainPullback` to `HodgeLadder.lean`, then run the full `python3 tools/check.py` (build, build-log placeholder scan, sorry scan, axioms, ledger).

2. **Transparency options.** Delete the line `set_option backward.isDefEq.respectTransparency false in` directly above the docstring of `iotaQ_comp_singularPullbackInt`. Keep the other four. Append to the module docstring, after the instance paragraph:

   ```
   `set_option backward.isDefEq.respectTransparency false` is set on four declarations,
   `constants_comp_singularPullbackSheaf`, `constants_comp_singularPullbackSheafComplex`,
   `constants_comp_singularPullbackSheaf_ne_zero` and `singularPullbackInt`: each fails without it
   at the pin (red team scratch), from the two spellings `TopCat.Sheaf AddCommGrpCat Y` and
   `Y.AbSheaf` of one category. `iotaQ_comp_singularPullbackInt` takes about 37 s of kernel time,
   unfolding upstream's `iotaQ`.
   ```

3. **Name the three local instances** in the `Variety` section so consumers can activate them:

   ```lean
   /-- `pullbackAb_additive` installed at `pointMap g`, where instance search misses it. -/
   local instance pointPullbackAdditive : (TopCat.Sheaf.pullbackAb (pointMap g)).Additive :=
     pullbackAb_additive _

   /-- `pullbackAb_preservesFiniteLimits` installed at `pointMap g`. -/
   local instance pointPullbackPreservesFiniteLimits :
       PreservesFiniteLimits (TopCat.Sheaf.pullbackAb (pointMap g)) :=
     pullbackAb_preservesFiniteLimits _

   /-- `pullbackAb_preservesFiniteColimits` installed at `pointMap g`. -/
   local instance pointPullbackPreservesFiniteColimits :
       PreservesFiniteColimits (TopCat.Sheaf.pullbackAb (pointMap g)) :=
     pullbackAb_preservesFiniteColimits _
   ```

   and replace the docstring's sentence "so the three exactness facts are stated at a variable map and installed as local instances in the `Variety` section." with "so the three exactness facts are stated at a variable map and installed in the `Variety` section as the named local instances `pointPullbackAdditive`, `pointPullbackPreservesFiniteLimits`, `pointPullbackPreservesFiniteColimits`; a consumer activates them with `attribute [local instance]`." Add the three names to the ledger's declaration list (change 5).

4. **Handoff** `docs/handoffs/2026-11-28-singular-cochain-pullback.md` in the format of `docs/harness.md`, with a pointer to this verdict and the 37 s kernel cost.

5. **Ledger** entry `singular-cochain-pullback` on `main`'s `ledger/ladder.json` (bump `updated`):

   ```json
   "status": "checked",
   "module": "HodgeLadder.Supported.SingularCochainPullback",
   "declarations": [
     "HodgeLadder.extendMap_single_square",
     "HodgeLadder.Supported.singularPullbackSheaf",
     "HodgeLadder.Supported.singularPullbackSheaf_comm",
     "HodgeLadder.Supported.constants_comp_singularPullbackSheaf",
     "HodgeLadder.Supported.singularPullbackSheafComplex",
     "HodgeLadder.Supported.constants_comp_singularPullbackSheafComplex",
     "HodgeLadder.Supported.pullbackAb_additive",
     "HodgeLadder.Supported.pullbackAb_preservesFiniteLimits",
     "HodgeLadder.Supported.pullbackAb_preservesFiniteColimits",
     "HodgeLadder.Supported.constants_comp_singularPullbackSheaf_ne_zero",
     "HodgeLadder.Supported.pointPullbackAdditive",
     "HodgeLadder.Supported.pointPullbackPreservesFiniteLimits",
     "HodgeLadder.Supported.pointPullbackPreservesFiniteColimits",
     "HodgeLadder.Supported.singularPullbackInt",
     "HodgeLadder.Supported.iotaQ_comp_singularPullbackInt",
     "HodgeLadder.Supported.PairCocycle",
     "HodgeLadder.Supported.RelCochain"
   ],
   "depends_on": ["supported-class-pullback", "end-class-right-mult", "cup-pullback", "supported-raw-map"],
   "contributors": ["claude-code"],
   "note": "Checked 2026-11-28. For any continuous f : Y ⟶ X in TopCat.{0}, singularPullbackSheaf f n : f⁻¹𝒮ⁿ_X ⟶ 𝒮ⁿ_Y is the transpose under pullbackPushforwardAdjunction of upstream's singularRestrictionSheaf ℚ f n (cochain φ ↦ φ ∘ f_#; upstream's file speaks of open embeddings but takes any map). singularPullbackSheaf_comm: it commutes with the sheafified singular coboundary, exact. constants_comp_singularPullbackSheaf: on constants it is the port's pullbackConstantSheafIso f (the iso supportedPullback postcomposes with) followed by the inclusion of constants, exact, no sign, no scalar. In ℤ-degrees along g : X' ⟶ X over Spec ℂ, singularPullbackInt g and iotaQ_comp_singularPullbackInt (the same square for iotaQ, through mapCochainComplexSingleFunctor). Non-vacuity constants_comp_singularPullbackSheaf_ne_zero on nonempty Y. The composite with mapExactFunctor_hom_named at pullbackAb (pointMap g), the core of supported-pullback-named, compiled in red-team scratch. iotaQ_comp_singularPullbackInt takes about 37 s of kernel time. Red team docs/sketches/singular-cochain-pullback.redteam.md."
   ```

6. **Gaps rows** in `main`'s `docs/gaps.md`, "General lemmas kept local" (Layer from `tools/pinwalk.py`'s graph on 2026-11-28; update if change 3 or a rebase moves it):

   In "Homological algebra and derived categories", in layer order (before the layer-20 rows):

   ```
   | `HodgeLadder.extendMap_single_square` (extending to `ℤ`-degrees a square out of a single complex, through `extendSingleIso`, `mapExtendCanonicalIso` and `singleMapHomologicalComplex`; any preadditive categories with zero objects, additive `F`) | `HodgeLadder.Supported.SingularCochainPullback` | 17 | Mathlib has `extendSingleIso` and upstream `mapExtendCanonicalIso` and no square of this shape at the pin; the same fact in the `homFromSingleExtend` spelling is `HodgeLadder.mapHomologicalComplex_homFromSingleExtend` with `extendSingleIso_inv_comp_extendMap` (`HodgeLadder.Hodge.RationalDeRhamComplex`), kept separate to avoid importing the de Rham stack; merge both into one `General` module when either is next edited; rung `singular-cochain-pullback` | 2026-11-28 |
   ```

   In "Singular homology, cohomology and simplicial cochains", by layer:

   ```
   | `HodgeLadder.Supported.singularPullbackSheaf`, `singularPullbackSheaf_comm`, `singularPullbackSheafComplex`, `constants_comp_singularPullbackSheaf`, `constants_comp_singularPullbackSheafComplex`, `constants_comp_singularPullbackSheaf_ne_zero` (inverse image of upstream's sheafified singular cochains along any continuous map of `TopCat.{0}`, the transpose of `singularRestrictionSheaf`, with the constants square against the port's `pullbackConstantSheafIso`) | `HodgeLadder.Supported.SingularCochainPullback` | 17 | upstream has the restriction `singularRestrictionSheaf` and `singularRestrictionSheafComplex` (`Lemmas/AlgebraicTopology/Singular/Sheaf/CochainRestriction.lean`) and the raw constants identity (library `Other`) and no inverse-image form; natural next to `singularRestrictionSheafComplex`; at a pin bump, check whether upstream adds an adjoint form; rung `singular-cochain-pullback` | 2026-11-28 |
   ```

   In "Known weaknesses", extend the instance-search row (the one starting "Instance search misses the `HodgeLadder.Cup` instances") by appending to its first cell, before " | Each consumer": " The same holds for the port's exactness instances of `pullbackAb` at `pointMap g`: `HodgeLadder.Supported.pullbackAb_additive`, `pullbackAb_preservesFiniteLimits`, `pullbackAb_preservesFiniteColimits` are stated at a variable map and installed as `pointPullbackAdditive`, `pointPullbackPreservesFiniteLimits`, `pointPullbackPreservesFiniteColimits` (rung `singular-cochain-pullback`)." And add the row:

   ```
   | `HodgeLadder.Supported.iotaQ_comp_singularPullbackInt` takes about 37 s of kernel type checking (`lake env lean -Dprofiler=true`, 2026-11-28; the rest of `HodgeLadder.Supported.SingularCochainPullback` builds in 7 s, no other declaration above 0.5 s): a one-line term whose type check unfolds upstream's `iotaQ` (`constantFieldSheafComplexIntIsoSingle`, `rationalToSingularCochainComplexInt`) to `extendSingleIso.inv ≫ extendMap` across the `AnalyticAdditiveSheaf X` and `TopCat.Sheaf` spellings. Unfolding with `simp only` first did not reduce it (red team scratch). A leaf; accepted | Rebuild time on edits; importers read the `.olean` | 2026-11-28 |
   ```

7. **Conventions row** in `docs/conventions.md`, directly after "Pullback of cohomology and of cohomology with supports":

   ```
   | Pullback of sheafified singular cochains | this repository, `HodgeLadder.Supported.singularPullbackSheaf`, `singularPullbackSheafComplex`, `singularPullbackInt`, `constants_comp_singularPullbackSheaf`, `iotaQ_comp_singularPullbackInt` (rung `singular-cochain-pullback`); upstream `singularRestrictionToRawPushforward`, `singularRestrictionSheaf`, `singularRestrictionSheafComplex` (`Lemmas/AlgebraicTopology/Singular/Sheaf/CochainRestriction.lean`), `constantSingularZeroCochain`, `constantsToSingularCochainZero_comp_singularRestrictionToRawPushforward` (library `Other`, `Other/AlgebraicGeometry/Cohomology/SupportSingularComparison.lean`), `HomologicalComplex.mapExtendCanonicalIso`; Mathlib `TopCat.Sheaf.pullbackPushforwardAdjunction`, `Functor.mapCochainComplexSingleFunctor`, `HomologicalComplex.extendSingleIso`; the port's `pullbackConstantSheafIso` | on sections over V, upstream's restriction is the linear dual of σ ↦ f ∘ σ on singular chains of f⁻¹V (`preimageOpenChainMap`), so φ ↦ φ ∘ f_#, no sign [`Hatcher2002`, recalled; section unverified]; upstream's file speaks of open embeddings and takes any continuous map; `singularPullbackSheaf f n` is its transpose under f⁻¹ ⊣ f_* (`homEquiv.symm`, the counit after f⁻¹ of the restriction), no sign; it commutes with δφ = φ ∘ ∂ exactly; on constants it is f⁻¹ℚ_X ≅ ℚ_Y (`leftAdjointUniq` against `constantSheafAdj`, the same iso `supportPullback` postcomposes with) followed by r ↦ r · ε, upstream's constant zero-cochain, factor 1; in ℤ-degrees, `mapExtendCanonicalIso`, `mapCochainComplexSingleFunctor` and `extendSingleIso` are degree-zero identifications with no sign | `supported-pullback-named`, `supported-pullback-section`, `supported-pullback-transport` (equalities of classes): a scalar c ≠ 1 on the constants identification would rescale g^*α against the pullback of its singular class and leave spans unchanged; a sign (−1)^n per degree on the cochain map would break `singularPullbackSheaf_comm` | checked at `2ead713` (red team 2026-11-28, `docs/sketches/singular-cochain-pullback.redteam.md`; the composite with `mapExactFunctor_hom_named` at `pullbackAb (pointMap g)` compiled in scratch, no sign) |
   ```

8. **Roadmap row** on `main`'s `docs/roadmap.md`: set `singular-cochain-pullback` to `checked`, dependencies `supported-class-pullback`, `end-class-right-mult`, `cup-pullback`, `supported-raw-map`, text "f⁻¹𝒮•_X ⟶ 𝒮•_Y on sheafified singular cochains, adjoint of upstream's restriction, constants pinned exactly (sketch R1)".

## Optional

- O1. Add the unit form for R4, elaborated in scratch:

  ```lean
  set_option backward.isDefEq.respectTransparency false in
  /-- The defining property of `singularPullbackSheaf`: its image under `f_*` after the unit is
  upstream's restriction. -/
  theorem unit_comp_singularPullbackSheaf (n : ℕ) :
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit.app _ ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f).map (singularPullbackSheaf f n) =
      singularRestrictionSheaf ℚ f n :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  ```

- O2. Add the corollary `singularPullbackSheaf f 0 ≠ 0` on nonempty Y (three lines in scratch: `intro h; apply constants_comp_singularPullbackSheaf_ne_zero f; rw [h]; exact comp_zero`, with the type ascription `(… : (pullbackAb f).obj (singularCochainSheaf ℚ X 0) ⟶ singularCochainSheaf ℚ Y 0)` and the transparency option).
- O3. Move the `General` section (and `extendMap_single_square`) to a module at layer 2 so consumers that do not need `iotaQ` avoid `HodgeLadder.Cup.EndClass`.

## What was tried and failed

- `rfl`, `simp`, `aesop` on the constants pin: all fail (scratch `Probe3`); the pin is not true by unfolding.
- Removing all five transparency options: four declarations fail independently (finding 5); removing only the `iotaQ` one compiles.
- Cutting the 37 s kernel time of `iotaQ_comp_singularPullbackInt` by unfolding `iotaQ` with `simp only` before the term: type mismatch, and 23.7 s of kernel time spent anyway (scratch `IotaAlt`).
- In the R3 composite: `rw [iotaQ_comp_singularPullbackInt]` without the transparency option fails on the `AbSheaf` spelling; `rw [← Category.assoc] at e` unfolded the `iotaQ` abbreviation and the next `rw` missed; `rw [DerivedCategory.Q.map_comp]` before restating the equation timed out at `whnf` (200000 heartbeats). The working route states the reassociated equation explicitly, uses `erw` for `mapExactFunctor_hom_named`, and closes with `Functor.commShiftIso_hom_naturality` (finding 3).
- The unit form via `rw [← Adjunction.homEquiv_unit]` fails (spelling mismatch at `pushforward.map`); the term-mode version in O1 works.
- `inferInstance` for `(pullbackAb (pointMap g)).Additive` and `PreservesFiniteLimits (pullbackAb (pointMap g))`: fails, confirming the sketch's instance note.
