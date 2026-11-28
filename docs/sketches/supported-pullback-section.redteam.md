# Red team: `supported-pullback-section` (R4 of `supported-pullback-transport`, issue #276)

Verdict: **pass with changes**

Date 2026-11-28. Candidate: WIP commit `59b8a1c` on `track/supported-pullback-section`, `HodgeLadder/Supported/Pullback/Section.lean` (337 lines, namespace `HodgeLadder.Supported`), root-imported, ledger untouched. Base `1ab3252`; the branch adds that file and one line of `HodgeLadder.lean`. Pin `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the pin of `main` at `33ef5c1` as well (no pin file differs between the base and `main`).

Read: `python3 tools/next.py supported-pullback-section` and `supported-pullback-transport`; the ledger entries of R1 to R6; `docs/sketches/supported-pullback-transport.md` (R4 block, signs table, kill criteria); the red-team files of `singular-cochain-pullback` (R1), `supported-pullback-named` (R3) and `supported-pair-named` (R5); `HodgeLadder/Supported/{SingularCochainPullback,PullbackNamed,PairNamed,Pullback}.lean`; `HodgeLadder/Cup/{SupportedFinal,SupportedPair,SupportedPairForget,SupportedRawMap}.lean`; upstream `Lemmas/AlgebraicTopology/Singular/RelativeCochainConeNaturality.lean` (`relativeDualCochainShortComplexNatMap`, `relativeDualCochainShortComplexIntMap`, `relativeDualCochainCohomologyEquiv_naturality`), `Lemmas/AlgebraicTopology/Singular/Sheaf/CochainRestriction.lean` (`preimageOpenChainMap`, `singularRestrictionToRawPushforward`, `toSheafify_comp_singularRestrictionSheaf`), `Definitions/AlgebraicTopology/Singular/Cohomology.lean` (`relativeCohomologyMap`), `Mathlib/Topology/Category/TopPair.lean` (`TopPair.ofSubsetHom`); `docs/conventions.md` rows "Pair spellings of (X, X ∖ Z)", "Pullback of cohomology and of cohomology with supports", "Pullback of sheafified singular cochains", "Supported pullback on cocycle-named classes"; `docs/gaps.md`.

Scratch: `scratch-rt-sps/` in the worktree, five files compiled with `lake env lean` against the branch build; deleted at the end. Nothing under `.lake/packages` touched.

The kill criterion does not fire: no sign and no scalar appears in R4, and none appears in R6 assembled from R3, R4 and R5 (finding 3).

## Findings

1. **Statement against the sketch.** `pullbackCocycle_supCocycle` is the sketch's R4 block verbatim: binders `(Z Z' hZ)`, `x : RelCochain X Z p`, `hx` on `(relSeq … Z.compl ⊤).X₁.d p (p + 1)`; left side `pullbackCocycle g Z Z' hZ (supCocycle X Z ((rawMap …).τ₁.f p x) (map_d_eq_zero _ x hx))`; right side `supCocycle X' Z' ((rawMap …).τ₁.f p ((relPullback g Z Z' hZ).f p x)) (map_d_eq_zero _ _ (map_d_eq_zero _ x hx))`. `openPairPullback` is the sketch's `TopPair.ofHom` of y ↦ `pointMap g y` on both parts, from `openInclusionPair X'(ℂ) (Opens.infLELeft ⊤ Z'.compl)` to `openInclusionPair X(ℂ) (Opens.infLELeft ⊤ Z.compl)`, and `relPullback` is the sketch's `forget₂` image of `(relativeDualCochainShortComplexIntMap ℚ (openPairPullback g Z Z' hZ)).τ₁`. Instance binders: T2 and paracompact opens on X and X' (section variables); integrality and smoothness are absent and unneeded.

2. **Literature.** The fact is that the inverse image of the sheafified singular-cochain resolution, read on global sections, is composition with g on singular cochains, so a relative cocycle x on (X, X ∖ Z) pulls back to x ∘ g_# on (X', X' ∖ Z') [`Bredon1997`, ch. III; `Hatcher2002`; sections unverified, as in the sketch]. Field by field: "the pulled-back cocycle" is R3's `pullbackCocycle` (the cocycle that names g^*α, `supportedPullback_named`); "the sheafified relative cocycle" is `supCocycle (rawMap x)` (the cocycle `exists_supported_rep` produces); "x ∘ g_#" is `relPullback x`, upstream's `HomologicalComplex.linearDualMap ((relativeChainFunctor ℚ).map f)` extended to ℤ-degrees, which is `relativeCohomologyMap`'s own cochain map (`relativeCochainComplexMap`). On raw cochains upstream's `singularRestrictionToRawPushforward` is `(preimageOpenChainMap …).f n).hom.dualMap`, the dual of σ ↦ g ∘ σ, and `singularRestriction_relPullback` identifies the two by `rfl` after the `relSeq` comparison, so both are φ ↦ φ ∘ g_# with no sign.

3. **R6 closes from R3, R4 and R5; no sign, no scalar.** Scratch `R6.lean` proves all three R6 statements of the sketch with standard axioms (`#print axioms`: `[propext, Classical.choice, Quot.sound]` for each), about 65 s for the file:
   - `supportedEquivPair_supportedPullback` in the ledger's spelling, in 9 tactic lines plus two helpers (`pair_square`: `topPairIso X'.hom ≫ openPairPullback = ofSubsetHom (pointMap g) _ ≫ topPairIso X.hom` by `Arrow.Hom.ext` and `rfl`; `cls_relPullback`: `mapHomologyIso` carries the class of `relPullback x` to `homologyMap τ₁` of the class of `x`, from `homologyMap_cls` and Mathlib's `ShortComplex.mapHomologyIso_hom_naturality`). The proof is `exists_supported_rep` on X, R3 with R4 rewritten into it, R5 on X' at `y := relPullback x` and on X at `y := x`, `cls_relPullback`, upstream's `relativeDualCochainCohomologyEquiv_naturality` (`erw`), `relativeCohomologyMap_comp` twice and `pair_square`. Every step is a rewrite by an equality; nothing multiplies.
   - `singular_pullbackCoh` (absolute case, Z = Z' = ⊤) in 5 lines: `forgetSupport_surjective_of_eq_top`, `forgetSupport_supportedPullback`, `forgetRel_supportedEquivPair` twice, the theorem above, `forgetRel_relativeCohomologyMap`, `rfl`.
   - `transport_supportedPullback` (the ledger note's `neighborhoodSupportPullbackPairMap` form at ⊤ against `complexSupportInjectiveSectionCohomologyEquiv`) through a helper `transport_eq_inv` (`supportedEquivPair_eq_transport` turned around by `Iso.inv_hom_id`) and one pair equality by `Arrow.Hom.ext` and `rfl`.
   Exact text in required change H, so the next prover can paste it.

4. **Direction and the map of pairs (attack 2).** `openPairPullback g Z Z' hZ : openInclusionPair X'(ℂ) (⊤, Z'ᶜ) ⟶ openInclusionPair X(ℂ) (⊤, Zᶜ)` is covariant in g, as `relativeDualCochainShortComplexIntMap` needs (`f : X ⟶ Y` gives `SC(Y) ⟶ SC(X)`), so `relPullback` runs from relative cochains of X to those of X'. Its second component uses `compl_le_of_preimage_subset g Z Z' hZ`, the same proof term R6's `TopPair.ofSubsetHom (pointMap g) (fun _ ha => compl_le_of_preimage_subset g Z Z' hZ ha)` uses. `pair_square` checks in Lean that the two agree through `topPairIso` on both sides (both are y ↦ `pointMap g y` on points). So R6's `relativeCohomologyMap` and R4's `relPullback` are the same map, read in pair spellings (1) and (3) of the conventions row.

5. **Signs (attack 3).** None. The proof's factors: the generator goes to the unit image of the generator (`gen_supportPairMap`, from `π_pairPullback` and unit naturality; the conventions row "Pullback of cohomology and of cohomology with supports" already records it); the unit followed by `g_*` of the cochain pullback is upstream's restriction (`unit_comp_singularPullbackInt`, from R1's `unit_comp_singularPullbackSheaf`, transpose under `homEquiv`, factor 1); `sInt_XIso`, `mapExtendCanonicalIso` and `extendXIso` are degree identifications that `simp` cancels with `Iso.inv_hom_id`; `toSheafify_comp_singularRestrictionSheaf` is upstream's definition of the sheafified restriction; the raw identity is `rfl`. `fromSingleEquiv_precomp_map_postcomp` unfolds `Cochain.fromSingleEquiv` and the single-complex isos by `simp` with no `neg` lemma. A −1 variant of the theorem would be false on the nonzero instance of finding 7 (the groups are ℚ-vector spaces).

6. **No trivial truth.** The conclusion is an equality in `PairCocycle X' Z' p`, a subgroup of Hom-complex cochains out of the pair sheaf; no `True`, no coercion, no empty index. `hZ` is used (in `pullbackCocycle`, `openPairPullback`, `relPullback`); `hx` is used (both `supCocycle` proofs). A ten-line proof would need the two sides to agree for a reason unrelated to the cochain pullback: `pairCocycle_ext` reduces the claim to one value at the generator, and that value on the right is the sheafified `relPullback x`, which depends on g. A `relPullback` replaced by `0` would make the right side the zero cocycle, and finding 7's left side is nonzero, so the theorem would fail; I did not find a shortcut.

7. **Non-vacuity (attack 5).** The theorem holds at x = 0 as 0 = 0, so on its own it allows a trivial instance. Scratch `Test.lean` (17 lines, standard axioms) gives a nonzero one on pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹ with support ⊤ in degree 0: some relative cocycle x on ℙ¹(ℂ) has `supCocycle (rawMap (relPullback x))` with nonzero derived class. Proof: `supportedPullback_prodFst_ne_zero`, `exists_supported_rep`, R3, `rw [pullbackCocycle_supCocycle _ _ _ _ x hx] at hz`, then R3's own non-vacuity argument (`iotaQ_quasiIso p1p1`, `Preadditive.IsIso.comp_right_eq_zero`, `Ext.homAddEquiv.injective`). Text in required change B. It tests degree 0 and Z = ⊤ only; positive degree and proper support are left to `supported-pullback-transport-test` (g^*[∞] ≠ 0 in degree 2).

8. **Smallest test lemma.** Change B's `supCocycle_relPullback_prodFst_ne_zero`, in upstream's and the ladder's API: `prod.fst`, `projectiveLine`, `p1p1` (`HodgeLadder.Tests`), `HodgeLadder.Tests.supportedPullback_prodFst_ne_zero`, `HodgeLadder.Cup.exists_supported_rep`, `HodgeLadder.Supported.supportedPullback_named`, `iotaQ_quasiIso`. It does not exist yet.

9. **The explicit-space pitfall (attack 4).** The gaps row "At `TopCat.of (ComplexPoint X)`, `forgetSupport … := rfl` times out" asks for the space named explicitly and for facts proved at a variable `T : TopCat`. The file follows it: `sInt_XIso (X := TopCat.of (ComplexPoint X))`, `pairCocycle_ext (Y := TopCat.of (ComplexPoint X'))`, and the three general lemmas (`pairCocycle_ext`, `fromSingleEquiv_precomp_map_postcomp`, `gen_supportPairMap`) at a variable space or category. Two more pitfalls surfaced while assembling R6 and the test, for the next prover: (a) `rw [pullbackCocycle_supCocycle]` without `x hx` leaves a side goal `hx` (the right side's proof term mentions `hx`); pass `g Z Z' hZ x hx` or `_ _ _ _ x hx`; (b) in degree 0 write the degree as `((0 : ℕ) : ℤ)`; `.f 0` elaborates to the integer literal and the rewrite misses. (c) `transport_eq_inv X' Z'` fails since the space is implicit; write `(Y := X')`.

10. **Imports.** `public import HodgeLadder.Cup.SupportedForgetGen` is unused: scratch `NoForgetGen.lean` (the file with that line removed, namespace renamed) compiles with no error, and no declaration of `SupportedForgetGen` or `ConstantGenerator` occurs in the file. `HodgeLadder.Supported.PullbackNamed` brings everything the file uses. Change C. The layer stays 23 either way (`PullbackNamed` is 22).

11. **Heartbeats, transparency and kernel time.** `lake env lean -Dprofiler=true` on the file without the unused import: 2 min 14 s wall, 110 s type checking, 9.3 s tactic execution; three declarations above 2 s, by position 8.0 s, 18 s and 81.8 s (the last is the main theorem). Below the sketch's 600 s split threshold. The two `set_option maxHeartbeats 1000000` lines (on `gen_supCocycle` and the main theorem) are unneeded: the file compiles with both removed. The file sets `attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1 _aux_3 _aux_5`, auto-generated instance names that a pin bump can rename (gaps row on auto-generated names); ten modules of `HodgeLadder/Cup/` carry the same line, so this is the ladder's existing pattern. Here it is unneeded: the file compiles with that line removed, and with the line and both heartbeat options removed together (scratch `NoBoth.lean`, 1 min 59 s wall, no error). Change C.

12. **Placement (attack 6).** The ledger entry has `module: null`, so `next.py` printed its fallback path `Supported/Pullback/Section.lean`. The sketch names R4 `HodgeLadder.Supported.PullbackSection`, and R1, R3 and R5 sit flat in `HodgeLadder/Supported/` (`SingularCochainPullback`, `PullbackNamed`, `PairNamed`), as R5's red team (finding 11) asked. A directory `Supported/Pullback/` beside the module `Supported/Pullback.lean` is legal Lean, and it would be the only one there. Recommend the flat name; change D.

13. **Ledger dependencies.** The entry lists `singular-cochain-pullback` and `supported-pullback-named`. The file also uses `cocycleMap` (`ext-map-cocycle`, through `fromSingleEquiv_precomp_map_postcomp`), `supportPairMap`, `freePullback`, `π_pairPullback`, `compl_le_of_preimage_subset` (`supported-class-pullback`), `supCocycle`, `supportedSection_eq_pairEval'` (`cup-singular-comparison`, `HodgeLadder.Cup.SupportedFinal`), `rawMap`, `relSeq` (`supported-raw-map`), `rawMap_comm₁₂_apply`, `rawMapMid_apply` (`supported-relative-cup`, `HodgeLadder.Cup.SupportedRelCup`), `sInt_XIso` (`right-mult-cocycle`), all checked. Change E.

14. **Gaps.** Three general lemmas at a variable space or category: `pairCocycle_ext` (a Hom-complex cocycle out of upstream's `pairSheaf'` is fixed by its generator value; any `Y : TopCat.{0}`, any complex), `gen_supportPairMap` (the pair map of `supportPullback` on generators; any continuous map of `TopCat.{0}`) and `fromSingleEquiv_precomp_map_postcomp` (any abelian categories, additive `F`). They belong in "General lemmas kept local" in the #212 layout, at layer 23 (`python3 tools/pinwalk.py --hubs`: `HodgeLadder.Supported.Pullback.Section`, layer 23, 0 downstream). Kernel time goes in "Known weaknesses". Change F.

15. **Conventions.** Used: the pair map on generators (row "Pullback of cohomology and of cohomology with supports", no sign, now checked on a generator value by `gen_supportPairMap`); the cochain pullback as φ ↦ φ ∘ g_# (row "Pullback of sheafified singular cochains"); the Hom-complex naming (row "Supported pullback on cocycle-named classes"); the pair spellings (3) `openInclusionPair … (Opens.infLELeft ⊤ Z.compl)` and (1) `TopPair.ofSubset`, related by `topPairIso`, the identity on points; upstream's `relativeDualCochainShortComplexIntMap` and `relativeDualCochainCohomologyEquiv_naturality` (in R6), the linear dual of the chain map and `extendHomologyIso` naturality, no sign. R4 and R6 are equalities, so their truth depends on each. Each matches the definitions it is stated against, checked in Lean where it matters (`singularRestriction_relPullback` by `rfl`, `pair_square` by `rfl`). No new row; change G appends to two rows.

16. **Checker.** `python3 tools/check.py --no-build` in the worktree: `ACCEPTED: all checks passed`. The ledger names no declaration of this rung yet, so the checker's axiom scan does not cover it; scratch `#print axioms HodgeLadder.Supported.pullbackCocycle_supCocycle`: `[propext, Classical.choice, Quot.sound]`. Recheck after change E.

17. **Pin drift.** None: the base `1ab3252` and `main` (`33ef5c1`) have the same `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`. `main` has moved on the ledger and docs since the base, so the pull request needs a rebase or merge of `ledger/ladder.json`.

## Required changes

A. Keep the statement and proof of `pullbackCocycle_supCocycle` as they are.

B. Add a test (new file `HodgeLadder/Tests/SupportedPullbackSection.lean`, or append to `HodgeLadder/Tests/SupportedPullback.lean` with `public import HodgeLadder.Supported.PullbackSection` there), scratch-compiled, standard axioms:

```lean
attribute [local instance] pointPullbackAdditive pointPullbackPreservesFiniteLimits
  pointPullbackPreservesFiniteColimits finHasDerivedCategory finSiteHasDerivedCategory
  p1p1_openParacompactSpace in
set_option backward.isDefEq.respectTransparency false in
/-- **Non-vacuity of `pullbackCocycle_supCocycle`**: along pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹, with support
the whole space, some relative cocycle `x` on ℙ¹(ℂ) has `supCocycle (rawMap (relPullback x))`
with nonzero derived class in degree zero. -/
theorem supCocycle_relPullback_prodFst_ne_zero :
    ∃ (x : RelCochain projectiveLine ⊤ 0)
      (hx : (relSeq (TopCat.of (ComplexPoint projectiveLine)) (⊤ : Closeds _).compl ⊤).X₁.d
        ((0 : ℕ) : ℤ) (((0 : ℕ) : ℤ) + 1) x = 0),
      ShiftedHom.map (Cocycle.equivHomShift.symm (supCocycle p1p1 ⊤
        ((rawMap (TopCat.of (ComplexPoint p1p1)) (⊤ : Closeds _).compl ⊤).τ₁.f ((0 : ℕ) : ℤ)
          ((relPullback (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤ (Set.subset_univ _)).f
            ((0 : ℕ) : ℤ) x))
        (map_d_eq_zero _ _ (map_d_eq_zero _ x hx)))) DerivedCategory.Q ≠ 0 := by
  obtain ⟨α, hα0⟩ := supportedPullback_prodFst_ne_zero
  obtain ⟨x, hx, -, hα⟩ := exists_supported_rep projectiveLine ⊤ α
  have hz := supportedPullback_named (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤
    (Set.subset_univ _) α _ hα
  rw [pullbackCocycle_supCocycle _ _ _ _ x hx] at hz
  refine ⟨x, hx, fun h0 => hα0 ?_⟩
  rw [h0] at hz
  have : Smooth p1p1.hom := smooth_p1p1
  have : QuasiIso (iotaQ p1p1) := iotaQ_quasiIso p1p1
  have : IsIso (DerivedCategory.Q.map (iotaQ p1p1)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  have h1 := (Preadditive.IsIso.comp_right_eq_zero _ _).1 hz
  apply Abelian.Ext.homAddEquiv.injective
  rw [map_zero]
  exact h1
```

The scratch file had `open CategoryTheory Limits TopologicalSpace AlgebraicGeometry ComplexPoint CochainComplex HomComplex` and `open HodgeLadder.Cup HodgeLadder.Supported HodgeLadder.Tests`, and the local instance `projectiveLine_openParacompactSpace` of `HodgeLadder/Tests/SupportedPullback.lean` (which is file-local there; in a new file restate it as that file does). List it in the ledger (change E) and in the test file's "Main results".

C. Delete the line `public import HodgeLadder.Cup.SupportedForgetGen` (finding 10), the line `attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1 TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5` and both `set_option maxHeartbeats 1000000 in` lines (finding 11; scratch compiled the file with all four removed). Keep `backward.isDefEq.respectTransparency false` (not tested for removal) and `linter.auxLemma false` (harmless). If a rebuild fails without one of them, restore that one and say which in the ledger note.

D. Move the file to `HodgeLadder/Supported/PullbackSection.lean`, module `HodgeLadder.Supported.PullbackSection`, and change the root import in `HodgeLadder.lean` to `public import HodgeLadder.Supported.PullbackSection`.

E. Ledger entry `supported-pullback-section`: `status` `checked`; `module` `HodgeLadder.Supported.PullbackSection`; `declarations` `HodgeLadder.Supported.openPairPullback`, `HodgeLadder.Supported.relPullback`, `HodgeLadder.Supported.pullbackCocycle_supCocycle`, `HodgeLadder.Supported.pairCocycle_ext`, `HodgeLadder.Supported.fromSingleEquiv_precomp_map_postcomp`, `HodgeLadder.Supported.gen_supportPairMap`, `HodgeLadder.Supported.singularPullbackInt_f_sInt_XIso`, `HodgeLadder.Supported.unit_comp_singularPullbackInt`, `HodgeLadder.Supported.singularRestriction_relPullback`, `HodgeLadder.Supported.gen_supCocycle`, and the test of change B (`HodgeLadder.Tests.supCocycle_relPullback_prodFst_ne_zero`); `depends_on` `singular-cochain-pullback`, `supported-pullback-named`, `ext-map-cocycle`, `supported-class-pullback`, `cup-singular-comparison`, `supported-raw-map`, `supported-relative-cup`, `right-mult-cocycle`; note: "Checked 2026-11-28. Sketch: docs/sketches/supported-pullback-transport.md (sub-rung R4), statement as posted. For a relative cocycle x on (X(ℂ), X(ℂ) ∖ Z), pullbackCocycle g Z Z' hZ (supCocycle (rawMap x)) = supCocycle (rawMap (relPullback x)), where relPullback is the forget₂ image of upstream's relativeDualCochainShortComplexIntMap τ₁ along openPairPullback, the map of open pairs (⊤, Z'ᶜ) ⟶ (⊤, Zᶜ) given by g (relativeCohomologyMap's own cochain map). Exact, no sign, no scalar: a pair cocycle is fixed by its generator value (pairCocycle_ext); the pair map sends the generator to the unit image of the generator (gen_supportPairMap); unit then g_* of the cochain pullback is upstream's restriction (unit_comp_singularPullbackInt); upstream's raw restriction and relPullback agree by rfl. Non-vacuity: supCocycle_relPullback_prodFst_ne_zero (pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹, support ⊤, degree 0). The red team assembled R6 from R3, R4 and R5 in scratch (all three statements, standard axioms, no sign); text in the red-team file, change H. Kernel type checking about 110 s for the file, 82 s for the main theorem. Red team docs/sketches/supported-pullback-section.redteam.md." Append to the note of `supported-pullback-transport`: "Update 2026-11-28: all three statements compiled in scratch from R3, R4 and R5 (standard axioms, no sign, about 65 s); Lean text in docs/sketches/supported-pullback-section.redteam.md, change H."

F. `docs/gaps.md`.
   - "General lemmas kept local", "Homological algebra and derived categories", after the `HodgeLadder.Hodge.DeRhamScalarSheaf` row: "| `HodgeLadder.Supported.fromSingleEquiv_precomp_map_postcomp` (the degree-zero component of `cocycleMap F z` precomposed with a map into `F A` through `mapCochainComplexSingleFunctor` and postcomposed with a chain map; any abelian categories, additive `F`) | `HodgeLadder.Supported.PullbackSection` | 23 | a `simp` computation on Mathlib's `Cochain.fromSingleEquiv` and `Functor.mapCochainComplexSingleFunctor` next to `HodgeLadder.ExtMapCocycle.cocycleMap`; no equivalent found at the pin; rung `supported-pullback-section` | 2026-11-28 |"
   - "Local cohomology, orientation and the cycle class", after the `HodgeLadder.Supported.Pullback` row: "| `HodgeLadder.Supported.pairCocycle_ext` (a Hom-complex cocycle out of upstream's `pairSheaf' Y U ⊤ U` is determined by its degree-zero value at the generator, through `pairSheafHomAddEquiv` and `freeAbelianSheafHomAddEquiv`; any `Y : TopCat.{0}`, any complex), `gen_supportPairMap` (the pair map of `supportPullback` followed by `f⁻¹ h ≫ ψ` sends the generator to the unit image of `h(gen)` under `f_* ψ`; any continuous map of `TopCat.{0}`) | `HodgeLadder.Supported.PullbackSection` | 23 | upstream has `pairSheafHomAddEquiv` and `freeAbelianSheafHomAddEquiv` and no statement in this form; companions of `supportPairMap` and `π_pairPullback`; rung `supported-pullback-section` | 2026-11-28 |"
   - "Known weaknesses": "| `HodgeLadder.Supported.PullbackSection` takes about 2 min to elaborate, 110 s of it kernel type checking (by position `pullbackCocycle_supCocycle` 82 s, the next two 18 s and 8 s; `lake env lean -Dprofiler=true`, 2026-11-28); same cause as `Supported.Pullback` and `Supported.PairNamed`, types restating the pair sheaf and the flasque model at `TopCat.of (ComplexPoint X)`. A leaf until R6; accepted | Rebuild time on edits; importers read the `.olean` | 2026-11-28 |"

G. `docs/conventions.md`.
   - Row "Pullback of sheafified singular cochains", result column, append: "On a relative cocycle x on (X(ℂ), X(ℂ) ∖ Z), the pair cocycle `pullbackCocycle g Z Z' hZ (supCocycle (rawMap x))` is `supCocycle (rawMap (relPullback x))`, with `relPullback` upstream's `relativeDualCochainShortComplexIntMap` τ₁ along the map of open pairs `openPairPullback` (the linear dual of σ ↦ g ∘ σ on relative chains, the cochain map of `relativeCohomologyMap`); upstream's raw restriction and `relPullback` agree by `rfl`; no sign, no scalar (`pullbackCocycle_supCocycle`, rung `supported-pullback-section`)." Status column, append: "; the section computation checked at `2ead713` (red team 2026-11-28, `docs/sketches/supported-pullback-section.redteam.md`; R6 assembled in scratch, no sign)".
   - Row "Pair spellings of (X, X ∖ Z)", convention column, append: "A map of pairs given by g : X' ⟶ X reads the same in spellings (1) and (3): `topPairIso X'.hom ≫ openPairPullback g Z Z' hZ = TopPair.ofSubsetHom (pointMap g) _ ≫ topPairIso X.hom`, by `Arrow.Hom.ext` and `rfl` (red team `supported-pullback-section`, scratch)."

H. For the prover of `supported-pullback-transport` (R6), not part of this rung. The text below compiled in scratch against this branch (imports `HodgeLadder.Supported.Pullback.Section`, `HodgeLadder.Supported.PairNamed`, `HodgeLadder.Cup.SupportedPairForget`, `HodgeLadder.Local.ClassPullback`; rename the first after change D), about 65 s for the file, standard axioms. Put the declarations in `namespace HodgeLadder.Supported`; `pair_square`, `cls_relPullback` and `transport_eq_inv` are helpers; the prover may rename them.

```lean
open CategoryTheory Category Limits TopologicalSpace Opposite Abelian CochainComplex HomComplex
  AlgebraicTopology.Singular AlgebraicGeometry ComplexPoint HodgeLadder.Cup HodgeLadder.Supported

variable {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X)

attribute [local instance] pointPullbackAdditive pointPullbackPreservesFiniteLimits
  pointPullbackPreservesFiniteColimits finHasDerivedCategory finSiteHasDerivedCategory

theorem pair_square (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') :
    (topPairIso (TopCat.of (ComplexPoint X')) Z'.compl).hom ≫ openPairPullback g Z Z' hZ =
      TopPair.ofSubsetHom (pointMap g) (fun _ ha => compl_le_of_preimage_subset g Z Z' hZ ha) ≫
        (topPairIso (TopCat.of (ComplexPoint X)) Z.compl).hom := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem cls_relPullback (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') {p : ℕ}
    (x : RelCochain X Z p)
    (hx : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) x = 0) :
    (ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
        (openInclusionPair (TopCat.of (ComplexPoint X')) (Opens.infLELeft ⊤ Z'.compl))).X₁.sc p)
        (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
        (cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) ((relPullback g Z Z' hZ).f p x)
          (map_d_eq_zero _ x hx)) =
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map (HomologicalComplex.homologyMap
        (relativeDualCochainShortComplexIntMap ℚ (openPairPullback g Z Z' hZ)).τ₁ p)
        ((ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
          (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl))).X₁.sc p)
          (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
          (cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) x hx)) := by
  rw [relPullback, ← homologyMap_cls _ _ _ _ x hx]
  exact ConcreteCategory.congr_hom (ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ (p : ℤ)).map
      (relativeDualCochainShortComplexIntMap ℚ (openPairPullback g Z Z' hZ)).τ₁)
    (forget₂ (ModuleCat ℚ) AddCommGrpCat)) _

variable [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] [IsIntegral X'.left] [Smooth X'.hom]
  [T2Space (ComplexPoint X')] [∀ U : Opens (ComplexPoint X'), ParacompactSpace U]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem supportedEquivPair_supportedPullback (Z : Closeds (ComplexPoint X))
    (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z')
    (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    supportedEquivPair X' Z' n (supportedPullback g Z Z' hZ n α) =
      relativeCohomologyMap ℚ n
        (TopPair.ofSubsetHom (pointMap g) (fun _ ha => compl_le_of_preimage_subset g Z Z' hZ ha))
        (supportedEquivPair X Z n α) := by
  obtain ⟨x, hx, -, hα⟩ := exists_supported_rep X Z α
  have h3 := supportedPullback_named g Z Z' hZ α _ hα
  rw [pullbackCocycle_supCocycle g Z Z' hZ x hx] at h3
  rw [supportedEquivPair_of_named X' Z' _ _ (map_d_eq_zero _ x hx) h3,
    supportedEquivPair_of_named X Z α x hx hα, cls_relPullback g Z Z' hZ x hx]
  erw [relativeDualCochainCohomologyEquiv_naturality]
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, ← LinearMap.comp_apply,
    ← relativeCohomologyMap_comp, pair_square]

set_option backward.isDefEq.respectTransparency false in
theorem singular_pullbackCoh (n : ℕ) (β : H^n(X; ℚ)) :
    rationalCohomologyAddEquivSingularCohomology X' n (pullbackCoh g n β) =
      cohomologyMap ℚ n (pointMap g) (rationalCohomologyAddEquivSingularCohomology X n β) := by
  obtain ⟨α, rfl⟩ := forgetSupport_surjective_of_eq_top (X := X) ⊤ rfl n β
  rw [← forgetSupport_supportedPullback g ⊤ ⊤ (fun _ _ => trivial) n α,
    ← forgetRel_supportedEquivPair, ← forgetRel_supportedEquivPair,
    supportedEquivPair_supportedPullback, forgetRel_relativeCohomologyMap]
  rfl

open HodgeLadder.LocalClassPullback in
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem transport_eq_inv {Y : Over (Spec ↧ℂ)} [IsIntegral Y.left] [Smooth Y.hom]
    [IsProjective Y.hom] [T2Space (ComplexPoint Y)]
    [∀ U : Opens (ComplexPoint Y), ParacompactSpace U]
    (W : Closeds (ComplexPoint Y)) (n : ℕ) (β : H_[W]^n(Y; ℚ)) :
    complexSupportInjectiveSectionCohomologyEquiv Y W ⊤ n
        (rationalSupportAddEquivSupportedInjectiveHomology Y W n β) =
      relativeCohomologyMap ℚ n (ofSubsetIsoNeighborhoodTop W).inv
        (supportedEquivPair Y W n β) := by
  rw [supportedEquivPair_eq_transport, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    Iso.inv_hom_id, relativeCohomologyMap_id, LinearMap.id_apply]

open HodgeLadder.LocalClassPullback in
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem transport_supportedPullback [IsProjective X.hom] [IsProjective X'.hom]
    (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z')
    (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    complexSupportInjectiveSectionCohomologyEquiv X' Z' ⊤ n
        (rationalSupportAddEquivSupportedInjectiveHomology X' Z' n
          (supportedPullback g Z Z' hZ n α)) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportPullbackPairMap (Point.map g) (Point.continuous_map _)
          (W' := ((⊤ : Opens (ComplexPoint X')) : Set (ComplexPoint X')))
          (W := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
          (fun _ _ h => hZ h))
        (complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ n
          (rationalSupportAddEquivSupportedInjectiveHomology X Z n α)) := by
  have hp : (ofSubsetIsoNeighborhoodTop Z').inv ≫
      (TopPair.ofSubsetHom (pointMap g) (fun _ ha => compl_le_of_preimage_subset g Z Z' hZ ha) ≫
        (ofSubsetIsoNeighborhoodTop Z).hom) =
      neighborhoodSupportPullbackPairMap (Point.map g) (Point.continuous_map _)
          (W' := ((⊤ : Opens (ComplexPoint X')) : Set (ComplexPoint X')))
          (W := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
          (fun _ _ h => hZ h) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl
  rw [transport_eq_inv (Y := X') Z', supportedEquivPair_supportedPullback,
    supportedEquivPair_eq_transport X Z n α, ← hp, relativeCohomologyMap_comp,
    relativeCohomologyMap_comp]
  rfl
```

In scratch the three groups sat in separate namespaces with the same `variable` and `attribute` lines; in one section the text above is the same declarations. R6's own red team should still run its non-vacuity test (`supported-pullback-transport-test`, g^*[∞] ≠ 0 in degree 2), since a positive-degree, proper-support instance is the case none of R3 to R5 tests.

## What I tried

| Attempt | Result |
|---|---|
| `pair_square` by `Arrow.Hom.ext <;> ext y <;> rfl` | compiles: R4's pair map and R6's `ofSubsetHom (pointMap g)` agree through `topPairIso` |
| `cls_relPullback` by `rw [← ConcreteCategory.comp_apply]` and `congr 1` | the rewrite missed (target not type-correct at `implicit` transparency); `ConcreteCategory.congr_hom` of `mapHomologyIso_hom_naturality` at `shortComplexFunctor … p` works |
| R6 main theorem, 9 tactic lines | compiles, standard axioms, no sign; `erw` needed for upstream's naturality (`forget₂` applied to a `ModuleCat` map) |
| R6 absolute case, without importing `HodgeLadder.Cup.SupportedPairForget` | `forgetRel_supportedEquivPair` unknown; with the import, 5 lines |
| R6 transport form with a local `have key : ∀ {Y} [inst …], …` | timeout at `whnf` (200000); as a separate lemma `transport_eq_inv` it compiles |
| R6 transport form rewriting both transports with `transport_eq_inv` | wrong shape (`congr 2` reached an `AddEquiv` against a `LinearMap` type); rewriting only the left side and proving the pair equality first works |
| non-vacuity test with `.f 0` | rewrite missed (`0` against `↑0`); with `((0 : ℕ) : ℤ)` and `rw [pullbackCocycle_supCocycle _ _ _ _ x hx]` it compiles |
| file without `public import HodgeLadder.Cup.SupportedForgetGen` | compiles; 110 s type checking under the profiler |
| file without either `maxHeartbeats 1000000` | compiles |
| file without the `local implicit_reducible` line on auto-generated names | compiles; with both heartbeat options also removed, compiles (1 min 59 s wall) |
| sign search in the proof | none: `pairCocycle_ext`, `gen_supportPairMap` (unit naturality), `unit_comp_singularPullbackInt` (R1's transpose), `gen_supCocycle` (iso round trip), upstream's `toSheafify_comp_singularRestrictionSheaf`, and `rfl` on raw cochains |
