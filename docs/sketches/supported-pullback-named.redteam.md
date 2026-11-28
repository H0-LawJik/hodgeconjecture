# Red team: `supported-pullback-named` (R3 of `supported-pullback-transport`, issue #261)

Verdict: **pass with changes**

Date 2026-11-28. Candidate: WIP commit `03533be` on `track/supported-pullback-named`, `HodgeLadder/Supported/PullbackNamed.lean` (namespace `HodgeLadder.Supported`, plus three lemmas in `HodgeLadder.ExtMapCocycle`), root import and a gaps row added, ledger untouched. Base `d1c59da`; pin `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`.

Read: `python3 tools/next.py supported-pullback-named`; the ledger entries `supported-pullback-named`, `singular-cochain-pullback`, `ext-map-cocycle`, `supported-pair-named`, `supported-pullback-section`, `supported-pullback-transport`; `docs/sketches/supported-pullback-transport.md` (R3 block, R4 to R6 consumers, signs table, kill criteria); `docs/sketches/singular-cochain-pullback.redteam.md` (finding 3), `docs/sketches/ext-map-cocycle.redteam.md`, and the R5 red team in progress (`docs/sketches/supported-pair-named.redteam.md` on `track/supported-pair-named`); `HodgeLadder/General/ExtMapCocycle.lean`, `HodgeLadder/General/HomComplex.lean`, `HodgeLadder/Supported/SingularCochainPullback.lean`, `HodgeLadder/Supported/Pullback.lean` (`supportPairMap`, `supportPullback`, `supportedPullback`), `HodgeLadder/Cup/SupportedFinal.lean` (`finHasDerivedCategory`, `finSiteHasDerivedCategory`, `exists_supported_rep`), `HodgeLadder/Cup/SupportedClass.lean` (`iotaQ_quasiIso`), `HodgeLadder/Tests/SupportedPullback.lean`; R5's `HodgeLadder/Supported/Pair/Named.lean` at `958222b`; Mathlib `HomotopyCategory/HomComplex.lean` (`Cocycle.precomp`, `Cocycle.postcomp`), `HomComplexShift.lean` (`equivHomShift_symm_precomp`, `_postcomp`), `DerivedCategory/Ext/Basic.lean`; `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`.

Scratch: `scratch_rt_spn/` in the worktree, compiled against the built `.olean` with `lake env lean` (for R5, a symlinked copy of the build tree plus R5's `Pair/Named.olean`; the oleans of every shared dependency are byte-identical between the two worktrees, checked with `cmp`). Deleted at the end. Files: `P1` (signatures, `#print axioms`), `P2` (instance `rfl` checks and the R6-shaped composite with R5), `P3` (nonzero instance on pr₁), `Triv` (the conclusion without `hα`), `Moved`, `MovedRw`, `CtxRw`, `CtxRwMod` (the general lemmas against `ExtMapCocycle` alone, and with `rw` in place of `erw`), `NoOpt` (`iotaQ_square` without the transparency option), and a profiler run of the candidate file.

## Findings

1. **Statement against the sketch and the literature.** `pullbackCocycle` and `supportedPullback_named` equal the sketch's R3 block term for term (the sketch writes `pullbackAb`, the file `TopCat.Sheaf.pullbackAb`, same constant). The source statement [`Bredon1997`, ch. II and III; `Iversen1986`, chapters on inverse image and supports; sections unverified, as in the sketch] is: if a class in H^n_Z(X; A) = Ext^n(A_{X,X∖Z}, A_X) is represented, through a resolution A_X → 𝒮•_X, by a cocycle z : ℤ_{X,X∖Z} → 𝒮•_X[n], then f^* of it is represented through the resolution of A_Y by φ ∘ f⁻¹z ∘ (ℤ_{Y,Y∖Z'} → f⁻¹ℤ_{X,X∖Z}), where φ : f⁻¹𝒮•_X → 𝒮•_Y lies over f⁻¹A_X ≅ A_Y. Field by field: the resolution is `iotaQ X` (ℚ_X[0] → 𝒮_X, upstream's, rung `end-class-right-mult`); "represented by z" is the hypothesis form `α.hom ≫ (Q.map (iotaQ X))⟦n⟧' = ShiftedHom.map (equivHomShift.symm z) Q`, the form `exists_supported_rep` produces; f⁻¹z is `cocycleMap (pullbackAb (pointMap g)) z` (rung `ext-map-cocycle`); the pair map is `supportPairMap` (rung `supported-class-pullback`), read in degree zero through Mathlib's `mapCochainComplexSingleFunctor`; φ is `singularPullbackInt g` (rung `singular-cochain-pullback`), which lies over `pullbackConstantSheafIso` by `iotaQ_comp_singularPullbackInt`; f^* is `supportedPullback`, which unfolds to `(mk₀ pair map) ∘ mapExactFunctor α ∘ (mk₀ coefficient iso)` with the same `supportPairMap` and the same `pullbackConstantSheafIso` (`Supported/Pullback.lean:150`). Match.

2. **Hypotheses are satisfiable, and with a nonzero class.** `exists_named_supportedPullback` discharges `hα` on every integral smooth X (with T2 and paracompact opens) and every α, through `exists_supported_rep`. Scratch `P3` goes further: on pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹ with support ⊤ in degree 0,

   ```lean
   theorem pullbackCocycle_prodFst_ne_zero :
       ∃ z : PairCocycle projectiveLine ⊤ 0,
         ShiftedHom.map (Cocycle.equivHomShift.symm
           (pullbackCocycle (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤ (Set.subset_univ _) z))
           DerivedCategory.Q ≠ 0
   ```

   compiles in 14 lines from `HodgeLadder.Tests.supportedPullback_prodFst_ne_zero`, `exists_named_supportedPullback`, `iotaQ_quasiIso p1p1` and `Preadditive.IsIso.comp_right_eq_zero`, standard axioms (full text in recommended change R1). So the right side of the theorem is a nonzero derived class on a real instance, and a `pullbackCocycle` that were zero, or a theorem that held as 0 = 0, would fail it. The instance needs `set_option backward.isDefEq.respectTransparency false` and an explicit `IsIso (Q.map (iotaQ p1p1))` (instance search misses it across the `TopCat.Sheaf` and `AnalyticAdditiveSheaf` spellings, the known gaps row).

3. **No trivial truth.** The conclusion is an equality of morphisms in `DerivedCategory (Sheaf (Opens.grothendieckTopology _) AddCommGrpCat)`, with no `ℕ∞`, no empty index and nothing unfolding to `True`. Every argument is used: `hZ` in `pullbackCocycle` and `supportedPullback`, `hα` as the input of `mapExactFunctor_hom_named` (`h1`). Scratch `Triv`: the conclusion without `hα`, for arbitrary α and z, fails by `simp [supportedPullback, pullbackCocycle, supportPullback]` (unsolved goal, α on the left and z on the right) and by `rfl` (definitional unfolding fails); only `hα` relates the two sides. Finding 2 rules out a 0 = 0 reading.

4. **Interface rung.** Not applicable: no structure, no axiom.

5. **Checker and axioms.** `python3 tools/check.py --no-build` in the worktree exits 0 ("ACCEPTED: all checks passed"), but it does not yet cover this module's declarations (not in the ledger). `#print axioms` (scratch `P1`) for `pullbackCocycle`, `iotaQ_square`, `supportedPullback_named`, `exists_named_supportedPullback`, `mk₀_comp_named`, `comp_mk₀_named`, `precomp_postcomp_precomp`: `[propext, Classical.choice, Quot.sound]` each. No `sorry`, no `native_decide`, no new axiom. The full checker must run after the ledger entry (change 5).

6. **Derived-category instances: the same terms as `exists_supported_rep`, and compatible with R5.** The file activates `HodgeLadder.Cup.finHasDerivedCategory` and `finSiteHasDerivedCategory`, the two `local instance`s of `Cup/SupportedFinal.lean`, each a function of X alone (`#check`: `(X : Over (Spec ↧ℂ)) → HasDerivedCategory …`, no smoothness arguments), so they apply on X' as well. `exists_named_supportedPullback` feeds `exists_supported_rep`'s conjunct into `supportedPullback_named` with no conversion, so the statement uses `exists_supported_rep`'s instance terms. R5 at `958222b` declares its own `namedHasDerivedCategory`, `namedSiteHasDerivedCategory`. Scratch `P2`: `finSiteHasDerivedCategory X = namedSiteHasDerivedCategory X`, `finHasDerivedCategory X = namedHasDerivedCategory X` and `finSiteHasDerivedCategory X = HasDerivedCategory.standard _` all close by `rfl`. So R6 can compose the two either way; the R5 red team (its finding 9, change B) already asks R5 to activate `SupportedFinal`'s instances instead, which removes the second spelling.

7. **The R6-shaped composite closes, no sign.** Scratch `P2`, with R5's olean on the path and R4 as a hypothesis `hR4 : pullbackCocycle g Z Z' hZ (supCocycle X Z ((rawMap …).τ₁.f n x) _) = supCocycle X' Z' ((rawMap …).τ₁.f n y) _` (R4's statement with `relPullback x` abstracted as `y`): from `hα` in `exists_supported_rep`'s form, `supportedEquivPair X' Z' n (supportedPullback g Z Z' hZ n α)` equals R5's right side at `y`, by three lines (`supportedPullback_named g Z Z' hZ α _ hα`, `rw [hR4] at h`, `exact supportedEquivPair_of_named X' Z' _ y hy h`). Elaboration with all instances of both files active: about 50 s wall. This is R6's main statement on the X' side; the X side is R5 at `x`, and the remaining step is upstream's `relativeDualCochainCohomologyEquiv_naturality`. So the statement is the form R4 and R6 consume.

8. **The general lemmas: correct, and they belong in `HodgeLadder/General/ExtMapCocycle.lean`.**
   - `mk₀_comp_named` and `comp_mk₀_named` are Mathlib's `ShiftedHom.mk₀_comp` and `ShiftedHom.comp_mk₀` (degree-zero composition, no sign) composed with `Cocycle.equivHomShift_symm_precomp` and `_postcomp`. `comp_mk₀_named` additionally uses `DerivedCategory.Q_map_single_map` and `Functor.commShiftIso_hom_naturality`. Statements read correctly: the commuting square hypothesis `hsq : single c ≫ ι' = ι ≫ φ` is the condition under which `(e ∘ mk₀ c)` read through `ι'` is `e` read through `ι` followed by `φ⟦n⟧'`. `precomp_postcomp_precomp` is a reassociation, proved by injectivity of `equivHomShift.symm`. Mathlib at the pin has none of the three (`grep` of `Algebra/Homology/` for `precomp`, `postcomp`, `mk₀_comp`); `HodgeLadder.General.HomComplex` has `cocycle_precomp_precomp` and `cocycle_postcomp_postcomp` and no mixed form.
   - Placement. The three extend the namespace `HodgeLadder.ExtMapCocycle` from a layer-22 module, so `tools/pinwalk.py` lists them at layer 22 inside "Homological algebra and derived categories", next to the layer-0 rows of the same namespace. Scratch `Moved`: all three compile unchanged in a file importing only `HodgeLadder.General.ExtMapCocycle` (which imports `Mathlib.Algebra.Homology.DerivedCategory.Ext.Map` only), in about 5 s. `pinwalk --hubs`: `HodgeLadder.General.ExtMapCocycle` has one downstream module, this candidate; `HodgeLadder.General.HomComplex` has 18. So the move into `General/ExtMapCocycle.lean` costs no rebuild beyond this branch, puts them at layer 0 where a pin bump walks them first, and merges two gaps rows (change 2). `precomp_postcomp_precomp` fits `General/HomComplex.lean` by topic, but that edit rebuilds 18 modules for a reassociation lemma; keep it with the other two.

9. **Signs: none.** No sign, no scalar and no shift other than `Cocycle.equivHomShift`'s right shift appears. Each step and where a factor could enter:

   | Step | Possible factor | Result |
   |---|---|---|
   | `Ext.mapExactFunctor` on a named class | (−1)^n twist | none: `mapExactFunctor_hom_named` (checked, rung `ext-map-cocycle`) |
   | `mk₀ c` after, `mk₀ s` before (`Ext.comp_hom`, `ShiftedHom.comp_mk₀`, `ShiftedHom.mk₀_comp`) | sign of composing shifted morphisms | degree zero on one side: `ShiftedHom.comp` is `α ≫ β⟦a⟧' ≫ shiftFunctorAdd'` inverse, no ε; Mathlib's lemmas are equalities, no sign |
   | `equivHomShift` on both sides | shift convention | the same `rightShift` (no sign) on X and X' |
   | constants square `iotaQ_square` | scalar on f⁻¹ℚ_X ≅ ℚ_{X'} | 1: a reassociation of `iotaQ_comp_singularPullbackInt` (checked) with the iso `supportedPullback` itself uses |
   | pair map | generator image | the same `supportPairMap` term in `supportedPullback` and in `pullbackCocycle`; its value on generators is R4's |

   The truth of R6's equality depends on each row (an equality of classes is not invariant under a nonzero scalar); R3 introduces no new factor. A conventions row (change 4) records the order of the three compositions, which is load-bearing for R4: `pullbackCocycle` precomposes the pair map before the single-complex comparison, as `supportPullback` precomposes `mk₀ supportPairMap` last.

10. **Kernel cost and the two options.**
    - Profiler (`lake env lean -Dprofiler=true`, this run): 198 s of type checking and 216 s wall for the file (8.1 s `pullbackCocycle`, 38.5 s `iotaQ_square`, 114 s `supportedPullback_named`, 38 s `exists_named_supportedPullback`), with tactic execution 7.5 s and elaboration 1.8 s. Other scratch compiles ran on the machine at the same time, so these are upper figures; the candidate's docstring gives 156 s (32, 96, 28) from an unloaded run. `iotaQ_square` costs what `iotaQ_comp_singularPullbackInt` costs (37 s there), for the same reason: the kernel unfolds `iotaQ` across the two sheaf spellings. Below the sketch's 600 s split threshold; consumers read the `.olean`.
    - `set_option backward.isDefEq.respectTransparency false` on `iotaQ_square` only: needed. Scratch `NoOpt`: without it the first `rw [assoc]` fails, the goal not being type-correct at `implicit` transparency (`TopCat.Sheaf.instAbelian.toPreadditive` on `AnalyticAdditiveSheaf X'` against the `Opens.grothendieckTopology` full-subcategory spelling of `(↧(ComplexPoint X')).AbSheaf`). The option relaxes elaborator unification only; the kernel rechecks the term. Recorded in the module docstring.
    - `erw [hsq]` in `comp_mk₀_named`: unneeded. Scratch `MovedRw`, `CtxRw`, `CtxRwMod`: `rw [hsq]` closes the same proof against `ExtMapCocycle` alone, with the candidate's four imports and opens, and with the candidate's `module` header and `@[expose] public noncomputable section`. Replace it (change 1).

11. **Equality first.** `supportedPullback_named` is an exact identity of derived morphisms, "no sign, no scalar" in its docstring. It is a step toward the equality `supportedEquivPair_supportedPullback` of rung `supported-pullback-transport` (R6, open, in the ledger), through `supported-pullback-section` (R4, open, in the ledger) and `supported-pair-named` (R5, branch under red team). Finding 7 shows the step composes with R5 to the X' side of R6.

12. **Non-vacuity test by name.** The smallest lemma that fails if the statement were trivially true (0 = 0, or a zero `pullbackCocycle`) is finding 2's `pullbackCocycle_prodFst_ne_zero`, built from `HodgeLadder.Tests.supportedPullback_prodFst_ne_zero` (rung `supported-class-pullback-test`, checked), `HodgeLadder.Supported.exists_named_supportedPullback` and `HodgeLadder.Cup.iotaQ_quasiIso`. It does not exist; it compiles in scratch. It tests degree 0 and support ⊤ only; positive degree with a proper support is the job of `supported-pullback-transport-test`. The candidate's `exists_named_supportedPullback` tests the hypothesis side only. Adding the test is recommended change R1; the rung passes without it, because the conclusion, read with `Q.map (iotaQ X')` an iso on smooth integral X', determines the derived class of `pullbackCocycle g Z Z' hZ z` as the class of g^*α, which is all R4 and R6 use.

13. **Pin drift: none.** The branch base `d1c59da` and `main` `0fd3685` pin the same upstream `2ead713` and toolchain (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain` unchanged). `main` has moved by new modules outside this file's import closure (elliptic curve, de Rham pullback, torus) and by `HodgeLadder.lean`, `docs/gaps.md`, `docs/conventions.md`, `ledger/ladder.json`, `docs/roadmap.md`: a rebase conflict at most, no definition the rung depends on changed.

14. **Layer.** `python3 tools/pinwalk.py`: `HodgeLadder.Supported.PullbackNamed` is layer 22 (above `Supported.SingularCochainPullback`, 17, and `Cup.SupportedFinal`). After change 2 the three general lemmas move to layer 0 with `HodgeLadder.General.ExtMapCocycle`.

## Required changes

1. **`erw` to `rw`.** In `comp_mk₀_named`, replace the line `  erw [hsq]` by `  rw [hsq]` (scratch `CtxRwMod`).

2. **Move the general lemmas** `mk₀_comp_named`, `comp_mk₀_named`, `precomp_postcomp_precomp` (with the `universe t`, the `variable` line and the `omit … in` line they use) from `HodgeLadder/Supported/PullbackNamed.lean` to the end of `HodgeLadder/General/ExtMapCocycle.lean`, in a new `section Named` before `end HodgeLadder.ExtMapCocycle`, keeping their names and docstrings; `General/ExtMapCocycle.lean` already declares `universe w₁ w₂ t t'` and opens `Category` and `Abelian`, so drop the `universe t` line. Add to that module's docstring "Main results" the line

   ```
   * `HodgeLadder.ExtMapCocycle.mk₀_comp_named`, `HodgeLadder.ExtMapCocycle.comp_mk₀_named`:
     pre- and postcomposition of a named `Ext` class by degree-zero classes;
     `HodgeLadder.ExtMapCocycle.precomp_postcomp_precomp`
   ```

   In `PullbackNamed.lean`, delete the `namespace HodgeLadder.ExtMapCocycle … end HodgeLadder.ExtMapCocycle` block and replace the last bullet of "Main results" by

   ```
   * General lemmas used here, in `HodgeLadder.General.ExtMapCocycle`:
     `HodgeLadder.ExtMapCocycle.mk₀_comp_named`, `comp_mk₀_named`, `precomp_postcomp_precomp`
   ```

   In `docs/gaps.md`, delete the row for `HodgeLadder.ExtMapCocycle.mk₀_comp_named` (module `HodgeLadder.Supported.PullbackNamed`, layer 22) and extend the `ext-map-cocycle` row: in its first cell, replace `` `mapExactFunctor_hom_named` (an exact functor `` by `` `mapExactFunctor_hom_named`, `mk₀_comp_named`, `comp_mk₀_named`, `precomp_postcomp_precomp` (an exact functor ``, and before `; any abelian categories)` insert `; pre- and postcomposition of a named `Ext` class by degree-zero classes keeps it named`; in its "Why local" cell append `; Mathlib has `Cocycle.equivHomShift_symm_precomp` and `_postcomp` and no `Ext` form, and `HodgeLadder.General.HomComplex` has the precomp-precomp and postcomp-postcomp cases only (the last three lemmas: rung `supported-pullback-named`)`; set its date cell to `2026-11-28`.

   If the coordinator prefers not to edit a checked rung's module, the alternative is to keep the block and leave the candidate's gaps row with layer 22; record the choice in the handoff.

3. **Module docstring.** Replace the kernel sentence `Kernel time at the pin, about 165 s for the file: 32 s for `iotaQ_square` (it unfolds `iotaQ`, as `iotaQ_comp_singularPullbackInt` does), 96 s for `supportedPullback_named`, 28 s for `exists_named_supportedPullback`.` by figures from one `lake env lean -Dprofiler=true` run on an idle machine after changes 1 and 2, in the same shape (finding 10 has a loaded run: 8, 38.5, 114, 38 s). Replace "two general facts on named classes, `comp_mk₀_named` (postcomposition by `mk₀ c` along a commuting square) and `mk₀_comp_named` (precomposition by `mk₀ s`)." by "two general facts on named classes from `HodgeLadder.General.ExtMapCocycle`, `comp_mk₀_named` (postcomposition by `mk₀ c` along a commuting square) and `mk₀_comp_named` (precomposition by `mk₀ s`)."

4. **Conventions row** in `docs/conventions.md`, directly after the row "Exact functors on Hom-complex cocycles":

   ```
   | Supported pullback on cocycle-named classes | this repository, `HodgeLadder.Supported.pullbackCocycle`, `supportedPullback_named`, `iotaQ_square` (rung `supported-pullback-named`), `HodgeLadder.ExtMapCocycle.mk₀_comp_named`, `comp_mk₀_named`; Mathlib `Ext.comp_hom`, `Ext.mk₀_hom`, `ShiftedHom.mk₀_comp`, `ShiftedHom.comp_mk₀`, `Cocycle.equivHomShift_symm_precomp`, `_postcomp` | a class α ∈ H^n_Z(X; ℚ) is named by z when `α.hom ≫ (Q.map (iotaQ X))⟦n⟧' = ShiftedHom.map (equivHomShift.symm z) Q` (right shift, no sign); `supportedPullback` is mk₀ of `supportPairMap`, then `mapExactFunctor` along `pullbackAb (pointMap g)`, then mk₀ of `pullbackConstantSheafIso`, all degree-zero compositions, no sign; `pullbackCocycle g Z Z' hZ z` is `cocycleMap` of z, precomposed with the single-complex map of `supportPairMap` followed by `(mapCochainComplexSingleFunctor 0).inv`, postcomposed with `singularPullbackInt g`; with these, g^*α is named by `pullbackCocycle` exactly | `supported-pullback-section` evaluates this `pullbackCocycle` on `supCocycle`, and `supported-pullback-transport` is an equality of classes: a sign or scalar entering here would rescale g^*α against the pullback of its singular class | checked at `2ead713` (red team 2026-11-28, `docs/sketches/supported-pullback-named.redteam.md`; the composite with R5's `supportedEquivPair_of_named` compiled in scratch, no sign) |
   ```

   And in the row "Derived-category instances in statements", append to the third cell: ` The supported-pullback chain (rungs `supported-pullback-named`, `supported-pair-named`) uses `HodgeLadder.Cup.finHasDerivedCategory` and `finSiteHasDerivedCategory` of `HodgeLadder.Cup.SupportedFinal`, functions of X alone, on X and X'; a local copy `HasDerivedCategory.standard _` agrees with them by `rfl` (red team 2026-11-28).`

5. **Ledger** entry `supported-pullback-named` (bump `updated`; if change 2 is declined, the three general declarations stay in the list, they are reachable from this module either way):

   ```json
   "status": "checked",
   "module": "HodgeLadder.Supported.PullbackNamed",
   "declarations": [
     "HodgeLadder.ExtMapCocycle.mk₀_comp_named",
     "HodgeLadder.ExtMapCocycle.comp_mk₀_named",
     "HodgeLadder.ExtMapCocycle.precomp_postcomp_precomp",
     "HodgeLadder.Supported.pullbackCocycle",
     "HodgeLadder.Supported.iotaQ_square",
     "HodgeLadder.Supported.supportedPullback_named",
     "HodgeLadder.Supported.exists_named_supportedPullback"
   ],
   "depends_on": ["singular-cochain-pullback", "ext-map-cocycle", "supported-class-pullback", "cup-singular-comparison", "end-class-right-mult"],
   "contributors": ["claude-code"],
   "note": "Checked 2026-11-28. Sketch: docs/sketches/supported-pullback-transport.md (sub-rung R3), statement as posted. A supported class α ∈ H^n_Z(X; ℚ) is named by z : PairCocycle X Z n when α.hom ≫ (Q.map (iotaQ X))⟦n⟧' = ShiftedHom.map (equivHomShift.symm z) Q, the form exists_supported_rep produces. pullbackCocycle g Z Z' hZ z: cocycleMap of z along pullbackAb (pointMap g), precomposed with the pair map supportPairMap (through mapCochainComplexSingleFunctor) and postcomposed with singularPullbackInt g. supportedPullback_named: if z names α then pullbackCocycle g Z Z' hZ z names supportedPullback g Z Z' hZ n α, exact, no sign, no scalar. Proof: mapExactFunctor_hom_named, the constants square iotaQ_square (a reassociation of iotaQ_comp_singularPullbackInt), and the general mk₀_comp_named, comp_mk₀_named, precomp_postcomp_precomp (HodgeLadder.General.ExtMapCocycle). Non-vacuity: exists_named_supportedPullback (every g^*α with X integral and smooth is named by a pulled-back cocycle). Instances: SupportedFinal's finHasDerivedCategory, finSiteHasDerivedCategory, the same terms as exists_supported_rep; R5's local copies agree by rfl. In red-team scratch, the composite with R5's supportedEquivPair_of_named (R4 as a hypothesis) closes, and on pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹ some pulled-back cocycle has nonzero derived class in degree 0. Kernel time about 160 to 200 s. Red team docs/sketches/supported-pullback-named.redteam.md."
   ```

   Then run the full `python3 tools/check.py` after rebasing onto `main`, and write `docs/handoffs/2026-11-28-supported-pullback-named.md` with a pointer to this verdict.

## Recommended changes

R1. **A nonzero test.** Add finding 2's lemma, as compiled in scratch `P3`, to `HodgeLadder/Tests/SupportedPullback.lean` (zero downstream modules; it gains `public import HodgeLadder.Supported.PullbackNamed`) and list it under rung `supported-class-pullback-test`, or in a new test file with its own test rung:

   ```lean
   attribute [local instance] pointPullbackAdditive pointPullbackPreservesFiniteLimits
     pointPullbackPreservesFiniteColimits finHasDerivedCategory finSiteHasDerivedCategory in
   set_option backward.isDefEq.respectTransparency false in
   /-- **Non-vacuity of `supportedPullback_named`**: along pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹, with support the
   whole space, some pulled-back pair cocycle has nonzero derived class in degree zero. -/
   theorem pullbackCocycle_prodFst_ne_zero :
       ∃ z : PairCocycle projectiveLine ⊤ 0,
         ShiftedHom.map (Cocycle.equivHomShift.symm
           (pullbackCocycle (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤ (Set.subset_univ _) z))
           DerivedCategory.Q ≠ 0 := by
     obtain ⟨α, hα⟩ := supportedPullback_prodFst_ne_zero
     obtain ⟨z, hz⟩ := exists_named_supportedPullback (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤
       (Set.subset_univ _) α
     refine ⟨z, fun h0 => hα ?_⟩
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

   The scratch file had a file-level `local instance` for `∀ U : Opens (ComplexPoint projectiveLine), ParacompactSpace U := openParacompactSpace projectiveLine`; supply it the same way in the test file (it is `p1p1_openParacompactSpace`'s analogue on ℙ¹, as in `HodgeLadder/Tests/CupComparison.lean`). Wall time in scratch about 25 s.

R2. **R5's instances.** Second the R5 red team's change B (activate `finHasDerivedCategory`, `finSiteHasDerivedCategory` in `Supported/Pair/Named.lean` in place of its own two instances), so R6 meets one spelling.

## What I tried that failed

- `lake env lean` with `LEAN_PATH` extended by R5's build directory: `lake env` resets `LEAN_PATH`, and a second root for the `HodgeLadder` package is not searched once the first root holds `HodgeLadder/`. A symlinked copy of the worktree build tree with R5's `Pair/Named.*` added, passed to `lean` directly, worked.
- In `P3`, `rw [← cancel_mono …]` on `hz`: the rewritten goal is not type-correct at `implicit` transparency (the `TopCat.Sheaf` and site spellings of the derived category); `Preadditive.IsIso.comp_right_eq_zero` with an explicit `IsIso` works. `CategoryTheory.IsIso.comp_right_eq_zero` does not exist; the lemma lives in `CategoryTheory.Preadditive.IsIso`. Instance search for `IsIso ((Q.map (iotaQ p1p1))⟦0⟧')` fails even with `QuasiIso (iotaQ p1p1)` in context; the `isIso_Q_map_iff_quasiIso` route of `HodgeLadder/Cup/EndClass.lean:149` works.
- Removing `respectTransparency false` from `iotaQ_square` (scratch `NoOpt`): `rw [assoc]` fails, as finding 10 records.
- Closing the conclusion of `supportedPullback_named` without `hα` (scratch `Triv`, `rfl` and `simp` with the three definitions): both fail, as they should.
