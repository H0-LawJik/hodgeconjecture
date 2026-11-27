# Red team: `wedge-sheaf-map` (statement and proof)

Date: 2026-11-27. Worktree `wedge-sheaf-map`, branch `track/wedge-sheaf-map`, base `3d07901`; uncommitted `HodgeLadder/Hodge/WedgeSheafMap.lean` (36 declarations and three local instances), the section "wedge-sheaf-map: statement" at the end of `docs/sketches/cup-hodge-filtration.md`, and the consumer check `scratch/U1.lean`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`.

Read: the ledger entries `wedge-sheaf-map`, `wedge-sheafify`, `de-rham-cup`; the module; `HodgeLadder/Hodge/{WedgeSheafify,PairingProduct,RationalDeRhamComplex,DerivedTensorBounded,WedgePresheaf,CupFiltration}.lean`, `HodgeLadder/Tests/DeRhamUnitNonzero.lean`; `docs/sketches/wedge-sheafify.redteam.md` (findings 3, 4), `pairing-product.redteam.md`, `rational-de-rham-complex.redteam.md`, `cup-hodge-filtration.redteam.md`; `docs/conventions.md`, `docs/gaps.md`; Mathlib `Algebra/Homology/ComplexShapeSigns.lean`, `Embedding/StupidTrunc.lean`, `Embedding/CochainComplex.lean`, `Limits/Shapes/ZeroMorphisms.lean`.

Scratch (`scratch/RT*.lean` in the worktree, deleted afterwards; `lake env lean` against the module's olean, which postdates the source): RT_Ax prints axioms; RT1 checks that the instance classes are `Prop`, that `0` and `−μ` satisfy `ExtendMulLeibniz`, and proves the generic uniqueness of `extendMul`; RT2 checks the renamings by `rfl` and the bound instances of `F^q`; RT3 supplies those instances and plugs the filtered restriction into `pairProductShQ_naturality`; RT4 tries trivial proofs; RT5 and RT7 try to instantiate the uniqueness at `Ω•_ℚ` (both killed at 900 s); RT6 proves the generic uniqueness of `truncMul`; RT8 proves that the unit law fails for `−deRhamWedge X`; RT9 measures a generic-`C` version of `unitComplexMul_comp_of_unit`. The prover's `scratch/U1.lean` was re-run (4.8 s, no error).

**Verdict: pass with changes.** The statement is the de Rham complex's wedge as a morphism of complexes, with the literature's Leibniz sign, which at the pin is Mathlib's Koszul sign `ε₂(p, q) = (−1)^p` and nothing else; the component lemma pins it to `wedgeSheaf p q` on every summand, exactly, and through `wedgeSheaf` to the checked square against sheafification and the forget pin. All 36 declarations and the three instances use the three standard axioms. No sign other than Mathlib's `(−1)^p` is forced anywhere. The changes are two missing instances that the filtered consumer needs (finding 4), two generic uniqueness lemmas, one of which a docstring already claims (findings 1, 4), a sign-separation test (finding 3) and bookkeeping (findings 9, 10).

## 1. Is this the statement the literature makes?

Source: the holomorphic de Rham complex `Ω•` of a complex manifold is a sheaf of differential graded algebras under the wedge product, `d(a ∧ b) = da ∧ b + (−1)^p a ∧ db` for `a` of degree `p`, and its Hodge (stupid) filtration `F^p Ω• = Ω^{≥p}` is multiplicative, `F^p ∧ F^q ⊂ F^{p+q}` ([`Voisin2002`] I, holomorphic de Rham complex and Hodge filtration; [`GriffithsHarris1978`] Ch. 0; sections unverified). The tensor product of complexes carries the Koszul sign on the second factor, `d(x ⊗ y) = dx ⊗ y + (−1)^p x ⊗ dy` ([`Stacks`], total complex of a double complex; tag unverified), which is Mathlib's convention at the pin.

| Literature | Lean | Check |
|---|---|---|
| `Ω•` as a complex of sheaves of `ℚ`-vector spaces | `rationalDeRhamComplex X = K.extend embeddingUpNat`, `K = rationalHolomorphicDeRhamComplexNat X (dim X.left)` | checked rung `rational-de-rham-complex`, pinned to upstream's `Ω•(X)` by `forgetRationalDeRhamIso` |
| `Ω• ⊗ Ω•`, Koszul differential | Mathlib `HomologicalComplex.tensorObj` (through `tensorRightComplex`), `TensorSigns (up ℤ)`: `ε₁ = 1`, `ε₂ ⟨p, _⟩ = c.ε p = p.negOnePow` (`ComplexShapeSigns.lean:159`, `:183`) | read from source; the proof of `extendMul` uses `ε₁ = 1` by `rfl` and `ε₂ = (−1)^p` by `Int.coe_negOnePow_natCast`, so the kernel checks the sign |
| the wedge on `Ω^p ⊗ Ω^q`, `a ⊗ b ↦ a ∧ b` | `ιTensorObj_deRhamWedge_f`: `ι_{p,q} ≫ (deRhamWedge X).f n = (extendXIso ⊗ₘ extendXIso) ≫ wedgeSheaf X (dim X.left) p q ≫ extendXIso⁻¹` | exact, no sign; `extendXIso` is Mathlib's identification `(K.extend e).X (e.f i) ≅ K.X i`, no sign |
| the wedge is a chain map | `deRhamWedge X : _ ⟶ _` is a morphism of complexes; obligation `ExtendMulLeibniz` discharged by `wedgeSheaf_leibniz` from `holomorphicFormDifferential_holomorphicWedge` | sign `(−1)^p` on the second term, none on the first; the cast is `eqToHom` along `p + 1 + q = p + q + 1` |
| unit: `1 ∧ b = b` | `deRhamWedge_unit : tensorHomShQ u (𝟙 Ω) ≫ deRhamWedge X = shQLeftUnitor Y Ω`, `u = rationalDeRhamUnit X` | exact, Mathlib's left unitor of complexes; assembled from the checked `wedgeSheaf_unit_left` |
| `F^p ∧ F^q ⊂ F^{p+q}` | `deRhamWedgeFiltered X p q`, `deRhamWedgeFiltered_comp_inclusion` | the restriction exists and commutes with the inclusions; unique (finding 4) |

Every object is upstream's or a checked local one. Nothing upstream states is restated.

## 2. Can the hypotheses be satisfied?

Yes. `[IsIntegral X.left] [Smooth X.hom]` and `[Nonempty (ComplexPoint X)]` hold for `HodgeLadder.Tests.point` (`Spec ℂ` over itself), as `Tests.rationalDeRhamUnit_point_ne_zero` uses; `deRhamWedge_ne_zero` then holds there. `ExtendMulLeibniz` is discharged for the sheaf wedge, not assumed.

## 3. Is any conclusion trivially true?

No. RT4: `simp` makes no progress on `deRhamWedge_unit`, leaves `deRhamWedge X ≠ 0` open, and leaves `ExtendMulLeibniz K (wedgeSheaf X d)` open after `intro p q`. Two things are cheap and the file should say so (finding 3): RT1 checks that `ExtendMulLeibniz K 0` holds by `simp` and that `ExtendMulLeibniz K μ` implies `ExtendMulLeibniz K (−μ)`, so the chain-map property alone pins nothing; the pin is the component lemma, and among consumer-facing facts the unit law, which is false for `0` (`deRhamWedge_ne_zero`) and for `−deRhamWedge X` (RT8, 30.8 s kernel, standard axioms):

```lean
theorem rt_deRhamWedge_unit_neg [Nonempty (ComplexPoint X)] :
    tensorHomShQ (deRhamUnitShQ X) (𝟙 (rationalDeRhamComplex X)) ≫ (-deRhamWedge X) ≠
      shQLeftUnitor (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X)
```

(proof: the unit law would give `−λ = λ`, so `𝟙_Ω = −𝟙_Ω` and `u = −u`, against `Tests.rationalDeRhamUnit_ne_neg`).

## 4. Interface rung?

No. Definitions and theorems; no structure, no assumed `Prop`.

## 5. Axioms and declarations

RT_Ax, `#print axioms` on all 36 of `scratch/decls.txt` (`extendMulComponent`, `extendMulComponent_eq`, `extendMulComponent_eq_zero`, `extendXIso_inv_congr`, `isZero_extend_X_of_neg`, `isZero_tensor_left`, `isZero_tensor_right`, `ExtendMulLeibniz`, `extendMul`, `ιTensorObj_extendMul_f`, `ιTensorObj_leftUnitor_hom_f`, `extendMul_unit`, `liftOfIsIsoGE`, `liftOfIsIsoGE_comp`, `isZero_stupidTrunc_X_of_lt`, `isIso_stupidTruncInclusion_f`, `truncMul`, `truncMul_comp_inclusion`, `toSheafifyTensor_comp_map_add_zsmul`, `toSheafifyTensor_hom_ext_add_zsmul`, `tensorHomShQ`, `shQLeftUnitor`, `shQLeftUnitor_eq`, `unitComplexMul_eq_shQLeftUnitor`, `unitComplexMul_comp_of_unit`, `rationalWedgePresheaf_leibniz`, `wedgeSheaf_leibniz`, `wedgeSheaf_extendMulLeibniz`, `deRhamWedge`, `deRhamUnitShQ`, `deRhamWedge_unit`, `deRhamWedge_unit_unit`, `ιTensorObj_deRhamWedge_f`, `deRhamWedge_ne_zero`, `deRhamWedgeFiltered`, `deRhamWedgeFiltered_comp_inclusion`, all in `HodgeLadder`) and on the instances `wsmCurriedTensorAdditive`, `wsmTensorLeftAdditive`, `wsmTensorRightPreservesEmpty`: each prints `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, `unsafe`, `axiom`, `implemented_by` or `set_option` in the module. `python3 tools/check.py --no-build` does not cover the module yet (not in the ledger, not imported from `HodgeLadder.lean`); run it on posting.

## 6. Conventions

| Convention | Where | Register | Truth depends on it? |
|---|---|---|---|
| Koszul sign `ε₁ = 1`, `ε₂(p, q) = (−1)^p` on `K ⊗ L` | Mathlib `TensorSigns (up ℤ)` | row "Tensor product of ℤ-indexed cochain complexes and its shifts" | yes for the chain-map property; kernel-checked against the pin in the proof of `extendMul` |
| Leibniz `d(a ∧ b) = cast(da ∧ b) + (−1)^p a ∧ db` | `holomorphicFormDifferential_holomorphicWedge`, from `formWedge_differential` | rows "Wedge product of algebraic forms", "Wedge product of holomorphic forms" | yes; it matches the Koszul sign with no twist. Known weakness: no direct form-level sign test (`docs/gaps.md`, first row), unchanged here |
| factor order `a ∧ b`, left tensor factor on the left | `ιTensorObj_deRhamWedge_f`, docstring of `deRhamWedge` | missing; add row "Wedge on complexes" (change 7) | yes for every reading of `deRhamCup` on forms; insensitive for membership |
| degree cast `eqToHom` along `p + 1 + q = p + q + 1`; `p + (q + 1) = p + q + 1` by `rfl` | `ExtendMulLeibniz`, `extendXIso_inv_congr` | same row | no sign; `holomorphicFormCast` keeps the element |
| unit law with Mathlib's `HomologicalComplex.leftUnitor` | `deRhamWedge_unit`, `shQLeftUnitor_eq` (`rfl`) | rows "Pairing product (left action)", "Sheafified wedge and the sheaf tensor" | yes: the scale of `fieldToDeRhamCohomology_cup` |
| restriction to `F^p ⊗ F^q` as the lift through `i_{p+q}` | `truncMul`, `deRhamWedgeFiltered` | same new row | no free choice: unique (RT6) |

For the borrowed inputs: `wedgeSheaf_unit_left` is stated against `rationalConstantsToFormsSheaf`, the degree-zero component of `rationalDeRhamUnit` (`homFromSingleExtend`), and against `Sheaf.monoidalCategory`'s `λ` with `ε = 𝟙` (`sheafifyQ_ε`); `extendMul_unit` turns it into Mathlib's left unitor of complexes through `ιTensorObj_leftUnitor_hom_f`, proved from the definition of `HomologicalComplex.leftUnitor` with no sign. The conventions agree.

## 7. Equality first

The rung is a construction with three identities: the component lemma, the unit law and the filtered compatibility, each exact, with no scalar. It is a step toward the identity `fieldToDeRhamCohomology_cup : ι (α ∪ β) = deRhamCup (ι α) (ι β)` of rung `de-rham-cup` (open, its last missing input is this rung) and the membership `deRhamCup_mem_hodgeFiltration` of `cup-hodge-filtration`.

## 7b. Non-vacuity

`deRhamWedge_ne_zero` (in the module): fails if the wedge were `0`. The sign analogue is RT8 (change 3). Both rest on `HodgeLadder.Tests.rationalDeRhamUnit_ne_zero` and `rationalDeRhamUnit_ne_neg` (rung `de-rham-unit-nonzero`, checked), which exist at `main`.

## 8. Pin drift

None. `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are identical on `3d07901` and `main` (`f7e1ad4`), and none of the modules this one imports or cites (`WedgeSheafify`, `PairingProduct`, `RationalDeRhamComplex`, `DerivedTensorBounded`, `WedgePresheaf`, `CupFiltration`, `Tests/DeRhamUnitNonzero`) changed between them. No name of the module occurs in `main`'s `HodgeLadder/`, `port/`, Mathlib or upstream.

## Findings

1. **Pinning.** The component lemma pins `deRhamWedge X`: every summand `Ω^{i₁} ⊗ Ω^{i₂}` with `i₁ < 0` or `i₂ < 0` is zero (`isZero_tensor_left/right`, `isZero_extend_X_of_neg`), so a chain map out of `Ω ⊗ Ω` is determined by its components on `(p, q)`, `p q : ℕ`. RT1 proves the generic form in 18 lines, 5 s:

   ```lean
   theorem eq_extendMul_of_components (hμ : ExtendMulLeibniz K μ)
       (φ : tensorObj (K.extend e) (K.extend e) ⟶ K.extend e)
       (hφ : ∀ p q : ℕ, ιTensorObj (K.extend e) (K.extend e) p q ((p + q : ℕ) : ℤ) _ ≫
         φ.f ((p + q : ℕ) : ℤ) = extendMulComponent K μ p q (p + q : ℕ)) :
       φ = extendMul K μ hμ
   ```

   (`e = ComplexShape.embeddingUpNat`). The instantiation at `Ω•_ℚ` as a named theorem `φ = deRhamWedge X` did not finish: RT5 (arguments left to unification) and RT7 (`K`, `wedgeSheaf X (dim X.left)` and `wedgeSheaf_extendMulLeibniz` passed explicitly, the summand map built with `hasTensor_shQ` in the hypothesis) were both killed at the 900 s limit, the usual zero-morphism diamond at `ShQ` (`docs/gaps.md`). The pin is therefore stated generically: `deRhamWedge X` is `extendMul K (wedgeSheaf X (dim X.left)) _` by definition, so `eq_extendMul_of_components` at those arguments is the concrete statement, and a consumer that needs it pays the cost once. It is the wedge of record: `wedgeSheaf` is fixed by its square against `toSheafifyTensor` and `toSheafify` (`eq_wedgeSheaf_iff`), reaches upstream's sheafification map of `holomorphicDeRhamPresheaf` through `forget_wedgeSheaf`, and its scale is fixed by `wedgeSheaf_unit_left`.

2. **Sign: only Mathlib's `(−1)^p`.** Read from source: `ε₂ := fun ⟨p, _⟩ => c.ε p` and `ε' := MonoidHom.mk' Int.negOnePow _` for `up ℤ`; `ε₁ = 1`. The proof of `extendMul` rewrites with `e₁ : ε₁ (p, q) = 1 := rfl` and `e₂ : (ε₂ (p, q) : ℤ) = (−1)^p := Int.coe_negOnePow_natCast p`, so a different sign could not pass the kernel. The Leibniz rule of record has `(−1)^p` on `a ∧ db` and none on `da ∧ b`, with the cast `eqToHom` (no reindexing sign), so `ExtendMulLeibniz` is that rule verbatim; no `(−1)^{pq}` and no reversed order sit in the casts. Opposite order: `wedgeSheaf q p` has source `Ω^q ⊗ Ω^p`, so a reversed product needs the braiding; `a ⊗ b ↦ b ∧ a` is a chain map for Mathlib's differential only with the twist `(−1)^{pq}`, and then equals `a ∧ b` by graded commutativity (pen and paper, no Lean statement here). The component lemma fixes the order in Lean; the docstring of `deRhamWedge` states it ("factor order `a ∧ b`, no sign"); the conventions row is change 7. A sign twist `ε(p, q) · (a ∧ b)` is a chain map only if `ε(p + 1, q) = ε(p, q) = ε(p, q + 1)` wherever the wedge and `d` are nonzero, so `ε` is constant and the unit law fixes it at `+1` (RT8 checks the `−1` case). The separate question of argument order in `deRhamCup x y := pairProductShQ μ y x` is the row "de Rham cup order (proposed)" and belongs to `de-rham-cup`.

3. **Unit law and sign separation.** The unit law is exact and is the consumer's scale. RT8 shows it is false for `−deRhamWedge X` on every `X` with a complex point (statement in section 3). Add it to the module, or to a test module that imports it (change 3); it is the analogue for the wedge of `rationalDeRhamUnit_ne_neg`.

4. **Filtration (prover's question 1).** The lift definition is acceptable: `liftOfIsIsoGE` is canonical, its content is the vanishing of `(i_p ⊗ i_q) ≫ m` below `p + q`, and `F^{p+q}` is zero below `p + q`. The docstring of `truncMul_comp_inclusion` claims uniqueness with no Lean statement; RT6 proves it generically, 15 lines, 5 s:

   ```lean
   theorem eq_truncMul_iff (φ : tensorObj (L.stupidTrunc (embeddingUpIntGE p))
         (L.stupidTrunc (embeddingUpIntGE q)) ⟶ L.stupidTrunc (embeddingUpIntGE (p + q))) :
       φ = truncMul L m p q ↔
         φ ≫ stupidTruncInclusion L (embeddingUpIntGE (p + q)) =
           tensorHom (stupidTruncInclusion L (embeddingUpIntGE p))
             (stupidTruncInclusion L (embeddingUpIntGE q)) ≫ m
   ```

   (proof: `ext n`; for `p + q ≤ n`, `cancel_mono` with `isIso_stupidTruncInclusion_f`; below, the target is zero). **The bound instances are missing.** RT2: instance search fails on `(rationalHodgeFilteredComplex X q).IsStrictlyGE q` and on `.IsStrictlyLE (dim X.left)`, and `pairProductShQ` at `B = F^q` needs both. `rationalHodgeFilteredComplex` is a `def`, so instance search does not unfold it to reach Mathlib's `IsStrictlySupported (K.stupidTrunc e) e`. RT3 supplies them (GE: `unfold rationalHodgeFilteredComplex; infer_instance`; LE: 8 lines through `isIso_stupidTruncInclusion_f`, `CochainComplex.isZero_of_isStrictlyLE` and `isZero_stupidTrunc_X_of_lt`, passing the `IsIso` explicitly as `@asIso _ _ _ _ _ this` because the generic lemma's instance path differs) and then checks the plug-in:

   ```lean
   pairProductShQ_naturality (TopCat.of (ComplexPoint X)) q (dim X.left : ℤ) 0 (dim X.left : ℤ)
     (rationalHodgeFilteredInclusion X p) (rationalHodgeFilteredInclusion X q)
     (rationalHodgeFilteredInclusion X (p + q)) (deRhamWedgeFiltered X p q) (deRhamWedge X)
     (deRhamWedgeFiltered_comp_inclusion X p q) h x y
   ```

   elaborates, with no conversion, in about 5 s for the file. So the `hm` form is right and the instances are the only gap (change 2).

5. **Unit law form (prover's question 2).** Keep both. `deRhamWedge_unit` is the form the `pairing-product` red team asked for: `tensorHomShQ` is `rfl` to `HomologicalComplex.tensorHom` under `hasTensor_shQ` (RT2, at a variable `Y`, 10.4 s kernel), `shQLeftUnitor_eq` and `unitComplexMul_eq_shQLeftUnitor` are `rfl` in the module, and `deRhamUnitShQ X` is `HEq.rfl` to `rationalDeRhamUnit X` (RT2, 3.2 s). `deRhamWedge_unit_unit` is the `hm` of `pairProductShQ_naturality` at `m = unitComplexMul`, `f = g = k = u` (U1 re-run: no conversion). No instance diamond changes the meaning: `HasTensor`, `Functor.Additive` and `PreservesColimit` are `Prop` (RT1, `#check`), and `HasZeroMorphisms C` is a subsingleton in Mathlib (`ZeroMorphisms.lean:103`), so the two zero-morphism paths of `docs/gaps.md` give the same zero; they cost kernel time and change no value.

6. **Kernel cost (prover's question 3).** About 307 s for the module is acceptable (precedent: `RationalHypercohomology` about 758 s). Keep `unitComplexMul_comp_of_unit` here: `deRhamWedge_unit_unit` uses it and moving it moves the cost without removing it. A generic-`C` version does not help: RT9 proves `unitMul_comp_of_unit` for any abelian monoidal `C` in 1.5 s, but its instantiation at `ShQ Y` in the spelling of `unitComplexMul_comp_of_unit` costs 87 s of kernel time on its own, against 97.5 s for the direct proof; the cost sits in the statement, which mentions three sheaf-level `tensorHom`s, and no proof route removes it. The cost is not yet recorded under Known weaknesses (change 6).

7. **Instances.** The three local instances are `Prop`-valued (`Functor.Additive`, `PreservesColimit`) and local, so they do not leak; their names are public, and a consumer needs them: RT8 fails to synthesize `(curriedTensor (Cup.ShQ ↧(ComplexPoint X))).Additive` until it activates `HodgeLadder.wsmCurriedTensorAdditive`, `wsmTensorLeftAdditive`, `wsmTensorRightPreservesEmpty` with `attribute [local instance]`. Say so in the module docstring (change 4). The explicit binder `[hTK : HasTensor …]` is sound: `HasTensor` is a `Prop`, so every proof is definitionally equal.

8. **Owed work (`S_c`, `ℂ`-scalar laws).** They belong after this rung and are correctly listed in the `de-rham-cup` note: they need `S_c := sheafifyQ.map (c • ·)` and its identification with upstream's `scalarHolomorphicDeRhamComplexInt X c`, which this rung does not touch. Proposal (not a change to this rung): split them into their own rung, depending on `wedge-sheaf-map`, so that the exact identity `fieldToDeRhamCohomology_cup`, which uses only the unit law and naturality, is not blocked by the `ℂ`-bilinearity in the `de-rham-cup` title.

9. **Bookkeeping (prover's question 4).** Rows needed in `docs/gaps.md` "General lemmas kept local" (change 5); Mathlib at the pin has no product on `HomologicalComplex.extend` and no lift through `stupidTruncInclusion` (`Embedding/StupidTrunc.lean` has `stupidTruncMap` and `stupidTruncXIso` only). The ledger has `module: null`, so `tools/next.py` derives `HodgeLadder/Wedge/Sheaf/Map.lean`; the module sits correctly next to `WedgeSheafify`; set `module` on posting. The sketch's sub-rung table (line 114 of `cup-hodge-filtration.md`) still names `filteredWedge p q`.

10. **Wording.** The module docstring's "last third of the former `wedge-sheaf-map`" is unclear to a reader without the history; name the split instead (change 8).

## Required changes

1. Ledger `wedge-sheaf-map`: `status: checked`, `module: "HodgeLadder.Hodge.WedgeSheafMap"`, the 36 declarations of section 5 plus those added by changes 2 and 3, contributors, a note naming this file and the verdict. `HodgeLadder.lean`: `public import HodgeLadder.Hodge.WedgeSheafMap`. Then `python3 tools/check.py`.
2. In the module: global instances `rationalHodgeFilteredComplex_isStrictlyGE (p : ℤ) : (rationalHodgeFilteredComplex X p).IsStrictlyGE p` and `rationalHodgeFilteredComplex_isStrictlyLE (p : ℤ) : (rationalHodgeFilteredComplex X p).IsStrictlyLE (dim X.left)` (texts of RT3); the generic `eq_truncMul_iff` (RT6) next to `truncMul_comp_inclusion`, and the generic `eq_extendMul_of_components` (RT1) next to `ιTensorObj_extendMul_f`, with a sentence in the docstring of `ιTensorObj_deRhamWedge_f` that it determines `deRhamWedge X` through `eq_extendMul_of_components` at `K`, `wedgeSheaf X (dim X.left)`. A concrete `eq_deRhamWedge_of_components` is not required: it did not elaborate in 900 s in two spellings (finding 1).
3. Sign separation `deRhamWedge_unit_neg` (RT8, about 31 s kernel), in the module or a test module.
4. Module docstring, "Spelling and kernel cost": add that consumers activate `HodgeLadder.wsmCurriedTensorAdditive`, `wsmTensorLeftAdditive`, `wsmTensorRightPreservesEmpty` with `attribute [local instance]` (with `Cup.sheafMonoidal` and `analyticShQMonoidal`) to state anything with `HomologicalComplex.tensorHom` or the left unitor at `TopCat.of (ComplexPoint X)`.
5. `docs/gaps.md`, "General lemmas kept local", two rows. First: `HodgeLadder.extendMulComponent`, `ExtendMulLeibniz`, `extendMul`, `ιTensorObj_extendMul_f`, `extendMulComponent_eq`, `extendMulComponent_eq_zero`, `extendMul_unit`, `extendXIso_inv_congr`, `isZero_extend_X_of_neg`, `isZero_tensor_left`, `isZero_tensor_right`, `ιTensorObj_leftUnitor_hom_f`, `liftOfIsIsoGE`, `liftOfIsIsoGE_comp`, `isZero_stupidTrunc_X_of_lt`, `isIso_stupidTruncInclusion_f`, `truncMul`, `truncMul_comp_inclusion` and the two uniqueness lemmas (a degreewise product with the Koszul Leibniz rule on an `ℕ`-indexed complex is a chain map on its extension to `ℤ`, with its unit law; its restriction to stupid truncations); module `HodgeLadder.Hodge.WedgeSheafMap`; general homological algebra absent from Mathlib at the pin, natural next to `Algebra/Homology/Embedding/Extend.lean`, `StupidTrunc.lean` and `Monoidal.lean`; rung `wedge-sheaf-map`. Second: `toSheafifyTensor_comp_map_add_zsmul`, `toSheafifyTensor_hom_ext_add_zsmul`, `tensorHomShQ`, `shQLeftUnitor`, `shQLeftUnitor_eq`, `unitComplexMul_eq_shQLeftUnitor`, `unitComplexMul_comp_of_unit` (any `Y : TopCat`; sums through the sheafified tensor, the named spellings of `tensorHom` and the left unitor on `ShQ Y`); same module and rung.
6. `docs/gaps.md`, Known weaknesses, row "Kernel cost of `HomologicalComplex.mapBifunctorMap`": append the module's timings (module build 307 s; `unitComplexMul_comp_of_unit` 97.5 s at a variable space, `deRhamWedge_unit` 40.1 s, `deRhamWedgeFiltered_comp_inclusion` 31.3 s, `deRhamWedge_unit_unit` 20.7 s, `deRhamWedgeFiltered` 16.7 s; the generic and form layers about 12 s for 23 declarations) and the two measured failure modes (a searched `HasTensor` instance for `extendMul` ran past 300 s; a unit law with `haveI` instances at the concrete space did not finish in 600 s).
7. `docs/conventions.md`: the row "Wedge on complexes" added by this red team stays with the rung.
8. Module docstring line 9: replace "last third of the former `wedge-sheaf-map`" by "the complex-level part of the original `wedge-sheaf-map`; `wedge-presheaf` and `wedge-sheafify` were split off it". Sketch `cup-hodge-filtration.md`: in the sub-rung table, `filteredWedge p q` becomes `deRhamWedgeFiltered X p q`; in "wedge-sheaf-map: statement", drop "not yet imported" on posting and add a pointer to this file.

## Not done

A direct form-level test of the Leibniz sign (known weakness, needs a nonzero 1-form; unchanged by this rung). The `ℂ`-scalar laws (finding 8). A concrete `eq_deRhamWedge_of_components` that elaborates in reasonable time (finding 1); a spelling through `tensorRightComplex` with no `haveI` in the hypothesis was not tried.
