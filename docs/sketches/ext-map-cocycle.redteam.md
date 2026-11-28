# Red team: `ext-map-cocycle` (checked rung, sub-rung R2 of `supported-pullback-transport`)

Date: 2026-11-27. Worktree `ext-map-cocycle`, candidate commit `cfb4cba` on `track/ext-map-cocycle`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4` (`lakefile.toml`, `lean-toolchain` unchanged against `main`). Issue #238.

Targets: `HodgeLadder.General.ExtMapCocycle`, namespace `HodgeLadder.ExtMapCocycle`: `cocycleMap`, `cocycleMap_v`, `cocycleMap_id_v`, `cocycleMap_precomp`, `cocycleMap_postcomp`, `equivHomShift_symm_cocycleMap`, `mapDerivedCategory_shiftedHom_cocycle`; the ledger entry, the roadmap row, the `docs/gaps.md` row, the handoff.

Read at the pin: Mathlib `Algebra/Homology/DerivedCategory/ExactFunctor.lean` (all), `DerivedCategory/Ext/Map.lean` (`Ext.mapExactFunctor`, `mapExactFunctor_hom`, `id_mapExactFunctor`), `HomotopyCategory/Shift.lean` (`mapCochainComplexShiftIso`, `commShiftMapCochainComplex`, `mapHomologicalComplex_commShiftIso_hom_app_f`), `HomotopyCategory/HomComplexShift.lean` (`Cocycle.equivHomShift`), `HomotopyCategory/HomComplex.lean` (`Cochain.map`, `δ_map`); upstream `Other/AlgebraicTopology/Singular/Cap/Naturality.lean`; the port's `Oka/Topology/Sheaves/Cohomology/Pullback.lean` (`pullbackAb` and its instances); this repository's `Cup/CocycleClass.lean`, `Cup/SupportedFinal.lean`, `Cup/SupportedClass.lean`, `Cup/EndClass.lean`, `Supported/Pullback.lean`; `docs/sketches/supported-pullback-transport.md` (R2, R3, the sign table).

Scratch files (directory `scratch_rt/` in the worktree, deleted at the end):

| File | What | Result |
|---|---|---|
| Probe | the derived statement at the port's `pullbackAb f` for a variable `f : Y ⟶ X` in `TopCat.{0}`; `cocycleMap (𝟭 C) z = z`; injectivity of `cocycleMap F` for faithful `F`; additivity | all compile; with `attribute [local instance] HasDerivedCategory.standard` the `CommShift ℤ` instance on `(pullbackAb f).mapDerivedCategory` fails to synthesize; with two named `noncomputable local instance` declarations on the site spelling (the pattern of `Cup/SupportedFinal.lean`) it is found and the statement applies as a term |
| Probe2 | `#synth` of `Additive`, `PreservesFiniteLimits`, `PreservesFiniteColimits` at `pullbackAb f` and of the `CommShift` instance, with trace | the three port instances are found for a variable `f`; `Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt` is found |
| Probe3 | an R3-shaped core at a general exact functor: a named `Ext` class goes, under `Ext.mapExactFunctor F`, to the class named by `(cocycleMap F z).precomp ((F.mapCochainComplexSingleFunctor 0).inv.app X)` | proved in 22 lines from `mapDerivedCategory_shiftedHom_cocycle`, `Ext.mapExactFunctor_hom`, `Cocycle.equivHomShift_symm_precomp`, `mapDerivedCategoryFactors_hom_naturality` and `mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app`; no sign enters |
| Probe5 | the Lean blocks of changes C and D exactly as printed below | compile; `#print axioms`: `[propext, Classical.choice, Quot.sound]` |
| Probe4 | `cocycleMap F z` under `open AlgebraicTopology.Singular HodgeLadder.ExtMapCocycle` with upstream's `Cap/Naturality.lean` imported | elaborates; overload resolution picks the ladder's `cocycleMap` by type |

`python3 tools/check.py --no-build` in the worktree (olean newer than the source): `ACCEPTED: all checks passed`; all seven declarations ACCEPTED with `[Classical.choice, Quot.sound, propext]`.

**Verdict: pass with changes.** The rung states the standard compatibility of the functor induced by an exact functor on derived categories with the localization functor and with shifts, for classes named by Hom-complex cocycles. It is an exact identity of morphisms with no sign and no scalar. Mathlib's shift isomorphisms for `F.mapHomologicalComplex` are identities degreewise (`rfl` at the pin), the factor iso's shift compatibility is a Mathlib instance, and `Ext.mapExactFunctor_hom` uses the same `ShiftedHom.map _ F.mapDerivedCategory`, so the identity composes with the consumer's `Ext` map with no twist (Probe3). The two required changes are a conventions row and a correction to the gaps row; three further changes are recommended.

## Findings

1. **Literature.** The source statement (`Stacks`, chapter "Derived Categories", the sections on exact functors between abelian categories and their extension to derived categories; tag unverified) is: an exact functor F : A → B induces a functor K(A) → K(B), degreewise, on complexes; it preserves quasi-isomorphisms, hence induces D(F) : D(A) → D(B) with D(F) ∘ Q_A ≅ Q_B ∘ K(F); and K(F) commutes with the shift with identity components, since (K[1])^n = K^{n+1} with differential −d and F(−d) = −F(d). Field by field: "F applied degreewise to a map K → L[n]" is `cocycleMap F z`, components `F.map (z.v p q _)` (`cocycleMap_v`, `rfl`); "D(F) ∘ Q ≅ Q ∘ K(F)" is `F.mapDerivedCategoryFactors`; "D(F) commutes with [n]" is the `CommShift ℤ` instance on `F.mapDerivedCategory` used inside `ShiftedHom.map`; the theorem says D(F)(Q(z)) = φ_K ∘ Q(F z) ∘ φ_L^{-1}[n], which is the naturality of φ together with its compatibility with shifts. Match.

2. **Hypotheses are satisfiable.** Probe: the statement applies as a term at `F = TopCat.Sheaf.pullbackAb f`, `f : Y ⟶ X` variable in `TopCat.{0}`, with `HasDerivedCategory.standard` installed on both sheaf categories by named local instances. The other instances (`Additive`, finite limits and colimits) are the port's, found for a variable map. Also `F = 𝟭 C` for any preadditive `C`.

3. **No trivial truth.** The conclusion is an equality of morphisms in `DerivedCategory D`, with no `ℕ∞`, no empty index, no definition that unfolds to `True`. Every hypothesis is used: `[F.Additive]` by `Cochain.map` and `δ_map`; `PreservesFiniteLimits`, `PreservesFiniteColimits` and both `HasDerivedCategory` by `F.mapDerivedCategory`. The proof is four rewrites because the content is Mathlib's naturality of `mapDerivedCategoryFactors` with shifts (`ShiftedHom.map_naturality_2` and the `NatTrans.CommShift` instance); the local work is `equivHomShift_symm_cocycleMap`, which needs the degreewise identity of the shift isos. A wrong definition of `cocycleMap` (zero, or a twist by (−1)^n) would make `equivHomShift_symm_cocycleMap` false for `F = 𝟭`, since there both sides reduce to `equivHomShift.symm z` and `ShiftedHom.map _ (𝟭 _)` at identity shift isos. I could not prove the theorem without the commShift instance.

4. **Interface rung.** Not applicable; no structure, no axiom.

5. **Checker.** Run above; the seven ledger declarations are the ones in the file, with the namespace `HodgeLadder.ExtMapCocycle`, and each has the three standard axioms. `ledger/ladder.json` `updated` is `2026-11-27`; status, module, declarations, contributors, note are filled.

6. **Sign and exactness at the pin.** Checked each step for a hidden (−1)^n:
   - `Cocycle.equivHomShift = (equivHom _ _).trans (rightShiftAddEquiv _ _ _ (zero_add n)).symm` (`HomComplexShift.lean:540`). `rightShift` carries no sign (the sign ε sits in `leftShift`); already in `docs/conventions.md` (row "Hom-complex composition and derived classes").
   - `Functor.mapCochainComplexShiftIso` (`Shift.lean:202`) is `NatIso.ofComponents` of `Hom.isoOfComponents (fun _ => Iso.refl _)`; `mapHomologicalComplex_commShiftIso_hom_app_f` and `_inv_app_f` are `rfl`. The (−1)^n on the differential of `K⟦n⟧` passes through `F` because `F` is additive (`Functor.map_zsmul` is the local simp lemma there).
   - `F.mapDerivedCategory.CommShift ℤ` is `commShiftOfLocalization` from `F.mapHomotopyCategory ⋙ Qh`; `NatTrans.CommShift` is a `Prop`, so the factor iso adds no data that could carry a sign.
   - The consumer: `Ext.mapExactFunctor_hom` reads `(e.mapExactFunctor F).hom` as `(F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ e.hom.map F.mapDerivedCategory ≫ (…)⟦n⟧'`, the same `ShiftedHom.map` along the same instance. Probe3 closes the loop from `Ext.mapExactFunctor` to `cocycleMap` with no sign, which is the step the sketch's sign table assigns to R2 and R3 ("`mapExactFunctor` | a degree twist ε(n) | excluded by R2 and R3 computing the image exactly").
   No (−1)^n found. The truth of `equivHomShift_symm_cocycleMap` depends on the degreewise identity of the shift isos; a Mathlib change there would break the build of this file, which is the guard.

7. **Equality first.** The rung is an identity, proved exactly, with "no sign" in both docstrings. It is a step toward `supported-pullback-named` (R3, open, ledger row present, depends on this rung) and through it `supported-pullback-transport` (R6).

7b. **Non-vacuity.** `cocycleMap_id_v` is `cocycleMap_v` at `F = 𝟭`, so it adds nothing. Sharper cheap checks, all compiled in Probe: `cocycleMap (𝟭 C) z = z` by `rfl` (whole cocycle, types agree definitionally); `Function.Injective (cocycleMap F)` for `[F.Faithful]` (five lines), so a nonzero cocycle maps to a nonzero cocycle under a faithful functor. The strongest check of the derived statement is Probe3 (recommended change C).

8. **Fit with R3.** The ladder names classes as `ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q` (`Cup/SupportedClass.lean:89`, `Cup/SupportedFinal.lean:148`, `:159`, `:198`), the left side's inner term here, and R3's hypothesis `hα` in the sketch has that form. The factor iso in the theorem is the one `Ext.mapExactFunctor_hom` needs after `mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app`; Probe3 is R3's algebra at a general exact functor, so R3 reduces to instantiating it at `pullbackAb (pointMap g)` and composing with R1's `iotaQ_comp_singularPullbackInt` and `Cocycle.equivHomShift_symm_postcomp`. Instance note for R3: `attribute [local instance] HasDerivedCategory.standard` leaves the `CommShift` instance unsynthesized at `pullbackAb`; named local instances on the site spelling work.

9. **Mathlib and upstream equivalents.** Mathlib at the pin has `Cochain.map`, `Cochain.map_v`, `δ_map` and no `Cocycle.map`; no lemma in `DerivedCategory/` relates `mapDerivedCategory` to Hom-complex cocycles (grep of `Algebra/Homology/` for `HomComplex` together with `mapDerivedCategory`: none). `python3 tools/pinwalk.py --clash` against upstream reports two name clashes for `cocycleMap`: `AlgebraicTopology.Simplicial.cocycleMap` (`Other/AlgebraicTopology/Singular/Cap/Naturality.lean:62`) and `AlgebraicTopology.Singular.cocycleMap` (`:143`). The gaps row names only the second. Probe4: under `open AlgebraicTopology.Singular` (as in `Cup/SupportedFinal.lean:31` and `Cup/SupportedPair.lean:27`) the name still resolves by type. No clash against Mathlib.

10. **Placement.** `HodgeLadder/General/`, Layer 0 (`python3 tools/pinwalk.py` prints 0 for the module), category "Homological algebra and derived categories", placed after `General.HomComplex` (layer 0) and before `Cup.CocycleClass` (layer 0): correct for the #212 layout. Imports only `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`; the root import is present. The module name says `Ext` and the file states nothing about `Ext`; change C fixes that, or the name can stay as the rung id.

11. **Drift.** The rung was written and checked at the current pin (`2ead713`, `v4.35.0-rc4`); nothing to diff. It depends on Mathlib only; at a bump, the drift targets are `mapCochainComplexShiftIso`, `Cocycle.equivHomShift` and the `CommShift` instance on `mapDerivedCategory`, all under the gaps category's diff list.

## Required changes

A. `docs/conventions.md`, register table: add this row after the row "Hom-complex composition and derived classes".

```
| Exact functors on Hom-complex cocycles | this repository, `HodgeLadder.ExtMapCocycle.cocycleMap`, `equivHomShift_symm_cocycleMap`, `mapDerivedCategory_shiftedHom_cocycle` (rung `ext-map-cocycle`); Mathlib `Functor.mapCochainComplexShiftIso`, `Functor.mapDerivedCategoryFactors` with its `NatTrans.CommShift` instance, `Ext.mapExactFunctor_hom` | `cocycleMap F z` has components `F.map (z.v p q _)`, no sign; the shift isos of `F.mapHomologicalComplex` are the identity in each degree (`mapHomologicalComplex_commShiftIso_hom_app_f`, `rfl`), so `equivHomShift.symm (cocycleMap F z) = ShiftedHom.map (equivHomShift.symm z) (F.mapHomologicalComplex _)` exactly; in the derived category the class of `z` maps to the class of `cocycleMap F z` conjugated by `mapDerivedCategoryFactors`, no sign | `supported-pullback-named` and every identity read through `Ext.mapExactFunctor` on a cocycle-named class; a twist (−1)^n here would pass every degree-zero check and flip odd-degree pullbacks | checked (red team 2026-11-27, `docs/sketches/ext-map-cocycle.redteam.md`; the composite with `Ext.mapExactFunctor_hom` was compiled in scratch, no sign) |
```

B. `docs/gaps.md`, the `ext-map-cocycle` row, column "Why local": replace

```
upstream's `AlgebraicTopology.Singular.cocycleMap` is a different map in another namespace
```

with

```
upstream's `AlgebraicTopology.Simplicial.cocycleMap` and `AlgebraicTopology.Singular.cocycleMap` (`Other/AlgebraicTopology/Singular/Cap/Naturality.lean`) are different maps (singular cocycle pullback) with the same short name; under `open AlgebraicTopology.Singular` the name resolves by type
```

## Recommended changes

C. Add the `Ext` form to this module (it is general, R3 needs it, and it makes the module name accurate). Compiled in scratch at the pin exactly as printed, under the `Derived` section's binders plus `[HasExt.{t} C] [HasExt.{t'} D]` and `open Abelian`; standard axioms; suggested name `mapExactFunctor_hom_named`:

```lean
theorem mapExactFunctor_hom_named {X Y : C} {n : ℕ} (e : Ext.{t} X Y n) {L : CochainComplex C ℤ}
    (ι : (CochainComplex.singleFunctor C 0).obj Y ⟶ L)
    (z : Cocycle ((CochainComplex.singleFunctor C 0).obj X) L n)
    (h : e.hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q) :
    (e.mapExactFunctor F).hom ≫
        (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
          (F.mapHomologicalComplex _).map ι))⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm ((cocycleMap F z).precomp
        ((F.mapCochainComplexSingleFunctor 0).inv.app X))) DerivedCategory.Q := by
  have h2 := congrArg (fun φ => ShiftedHom.map φ F.mapDerivedCategory) h
  simp only at h2
  rw [mapDerivedCategory_shiftedHom_cocycle] at h2
  have hmap : ShiftedHom.map (e.hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧') F.mapDerivedCategory =
      e.hom.map F.mapDerivedCategory ≫ (F.mapDerivedCategory.map (DerivedCategory.Q.map ι))⟦(n : ℤ)⟧' := by
    simp only [ShiftedHom.map, Functor.map_comp, assoc, Functor.commShiftIso_hom_naturality]
  rw [hmap] at h2
  have hY : (F.mapDerivedCategorySingleFunctor 0).hom.app Y ≫
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app Y) =
        F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj Y) := by
    rw [← cancel_epi ((F.mapDerivedCategorySingleFunctor 0).inv.app Y), Iso.inv_hom_id_app_assoc]
    exact (F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app Y).symm
  rw [Cocycle.equivHomShift_symm_precomp, Ext.mapExactFunctor_hom]
  rw [DerivedCategory.Q.map_comp, Functor.map_comp, assoc, assoc, ← Functor.map_comp_assoc,
    hY, ← Functor.map_comp, ← F.mapDerivedCategoryFactors_hom_naturality, Functor.map_comp,
    reassoc_of% h2]
  have hX := F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X
  rw [reassoc_of% hX, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp [ShiftedHom.map]
```

The import becomes `Mathlib.Algebra.Homology.DerivedCategory.Ext.Map`. If it lands here, add it to the ledger declarations and the gaps row; if it lands in R3, put it there under the same name.

D. Replace `cocycleMap_id_v` by the whole-cocycle form, and add injectivity for faithful functors (both compiled in scratch):

```lean
/-- Sanity check: for the identity functor, `cocycleMap` is the identity on cocycles. -/
theorem cocycleMap_id (z : Cocycle K L n) : cocycleMap (𝟭 C) z = z :=
  rfl

/-- For a faithful additive functor, `cocycleMap` is injective: a nonzero cocycle maps to a
nonzero cocycle. -/
theorem cocycleMap_injective [F.Faithful] :
    Function.Injective (cocycleMap F (K := K) (L := L) (n := n)) := by
  intro z w h
  ext p q hpq
  have := congrArg (fun c : Cocycle _ _ n => c.1.v p q hpq) h
  simpa using F.map_injective this
```

Both compile as written in the `Map` section (the unused section variable `F` is left out of `cocycleMap_id`); standard axioms. Update the ledger declarations and the gaps row.

E. `docs/sketches/supported-pullback-transport.md`, elaboration notes paragraph (line 59): append

```
At `pullbackAb`, `attribute [local instance] HasDerivedCategory.standard` leaves `(pullbackAb f).mapDerivedCategory.CommShift ℤ` unsynthesized; install named `noncomputable local instance` declarations of `HasDerivedCategory.standard _` on both `Sheaf (Opens.grothendieckTopology _) AddCommGrpCat.{0}` categories, as `Cup/SupportedFinal.lean` does (red team of `ext-map-cocycle`).
```

## What I tried that failed

- A proof of the derived statement without the `NatTrans.CommShift` instance: not found; the shift compatibility of the factor iso is the content.
- `attribute [local instance] HasDerivedCategory.standard` at `pullbackAb`: the `CommShift` instance fails (finding 8).
- In Probe3, `rw [← mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]` on the `hom` side does not match (the lemma is stated with `dsimp%`); `cancel_epi` on the inverse works. `rw [Functor.map_id]` on the final `(𝟙 _)⟦n⟧'` does not match (the object is the composite functor's); `simp [ShiftedHom.map]` closes it.
