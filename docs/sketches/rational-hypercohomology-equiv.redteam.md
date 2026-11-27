# Red team: `rational-hypercohomology-equiv` (statement and plan)

Date: 2026-11-27. Worktree `rational-hypercohomology-equiv` at base `0cdf92a`, uncommitted `HodgeLadder/Hodge/RationalHypercohomology.lean` and the section "rational-hypercohomology-equiv: statement" of `docs/sketches/cup-hodge-filtration.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, equal to `main`.

Read: the ledger entries `rational-hypercohomology-equiv`, `rational-ext-equiv`, `ext-derived-bridge`, `rational-de-rham-complex`, `de-rham-cup`, `pairing-product`; the module; the sketch and `docs/sketches/cup-hodge-filtration.redteam.md`; `HodgeLadder/Cup/SheafExact.lean`, `HodgeLadder/Cup/ExtBridge.lean`, `HodgeLadder/General/Ext.lean`; upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (`Hypercohomology`, `hypercohomologyMap`, `constantIntegerSheafComplexIntIsoSingleULift`, `hypercohomologyAddEquivConstantCohomology`, `hypercohomologyModule`) and `Lemmas/AlgebraicGeometry/Hodge/Filtration.lean`; Mathlib `Ext/MapAdjunction.lean`, `Ext/Map.lean`, `DerivedCategory/ExactFunctor.lean`, `Localization/Adjunction.lean`, `Shift/Adjunction.lean`, `Adjunction/Additive.lean`, `Shift/ShiftedHom.lean`; `docs/conventions.md`, `docs/references.md`, `docs/gaps.md`.

Scratch (directory `RTScratch/` in the worktree, deleted afterwards), each run under `timeout`:

| File | What it does | Time |
|---|---|---|
| RT1 | `#print axioms` of every declaration in the module; `#check` of the two statements from an importing file | 6 s |
| RT2, RT2b, RT2c | `rationalExtEquiv_hom` at a general `Y : TopCat` with local standard instances, one `simp only`; RT2c the statement alone | 123 s; 22 s for the statement |
| RT3, RT3p, RT3v1 | the same through three generic lemmas (`extEquiv_symm_hom`, `postcomp_hom`, `precomp_hom`), with the profiler | 110 to 135 s; kernel 73 to 84 s |
| RT4 | the unit test of section 7b, derived from the stated agreement; `rfl` and `simp only [rationalHypercohomologyEquiv_apply]` on the agreement at `n = 0` | 83 s |
| RT5, RT5b | `rationalExtEquiv_hom` at a general `Y` with the `HasDerivedCategory` instances as binders, then instantiated at `TopCat.of (ComplexPoint X)` by a term | 125 s; instantiation 36 s kernel |
| RT6, RT7 | `#synth` of the `HodgeLadder.Cup` instances at concrete spaces, with and without upstream's `implicit_reducible` attributes, with a trace | 5 s each |
| RT8 | the planned shift step from Mathlib's `Adjunction.shift_counit_app`, and the same step with a minus sign | 7 s |

**Verdict: pass with changes.** The statement is the one the route needs, at full strength, with no hidden scalar. The planned agreement proof is sound, and its one nontrivial step (moving the shift past the derived counit) is checked in scratch with no sign. The module cannot land in its present form: the checker rejects the `sorry` in the agreement (finding 4). Changes 1 and 2 are required. Changes 3 to 8 are recommended, and change 8 is for the consumer rung `rational-de-rham-complex`.

## 1. Is this the statement the literature makes?

For a complex `C` of sheaves of ℚ-vector spaces on a space `Y`, `ℍ^n(Y; C) = H^n RΓ(Y, C) = Hom_{D(Sh(Y; ℚ))}(ℚ_Y, C[n])`, and `RΓ` computed in sheaves of abelian groups gives the same groups ([`Iversen1986`], chapters unverified; [`Voisin2002`] I, hypercohomology, section unverified). The second fact is the derived form of the exact adjunction `ℚ ⊗ − ⊣ forget`, which is what the module builds. `docs/references.md` has no Kashiwara–Schapira key; the librarian can add one if a later rung cites the derived-adjunction statement directly.

| Literature | Lean | Check |
|---|---|---|
| complex of sheaves of ℚ-vector spaces | `C : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ` | any ℤ-indexed complex, unbounded; full strength |
| hypercohomology of `C` | upstream's `ℍ^n(X; (forgetComplex X).obj C)`, `SmallShiftedHom.{1}` from upstream's `ℤ_X[0]` to `forget C` in complexes of `AnalyticAdditiveSheaf X`, quasi-isomorphisms inverted | the statement of record's hypercohomology; no local redefinition |
| `Hom_{D(ℚ)}(ℚ_X, C[n])` | `ShiftedHom (Q.obj (rationalUnitComplex X)) (Q.obj C) n`, `rationalUnitComplex X = single₀ (Cup.QX _)` | `D(ShQ)` with `HasDerivedCategory.standard` (row "Derived-category instances in statements") |
| the isomorphism is additive | `≃+` | yes; the `AddCommGroup` on `ℍ` is upstream's (transported along `SmallShiftedHom.equiv`), and `hyperAddEquiv` uses upstream's `hypercohomologyEquiv_add` |
| natural in `C` | `rationalHypercohomologyEquiv_naturality`, along chain maps `f : C ⟶ C'`, upstream's `hypercohomologyMap` on the left, `ShiftedHom.comp … (mk₀ (Q.map f))` on the right | the only functoriality upstream's `ℍ` has; see finding 5 |
| on `C = ℚ_X[0]` it is the identification `H^n(X; ℚ) = Ext^n(ℚ_X, ℚ_X)` | `rationalHypercohomologyEquiv_rationalUnitComplex`: equal to `(Cup.rationalExtEquiv _ n (unitHypercohomologyEquiv X n x)).hom` | exact, no scalar, no cast: `DerivedCategory.singleFunctor _ 0` is `CochainComplex.singleFunctor _ 0 ⋙ Q` by `Iso.refl`, so `Ext.hom` has the left side's type (RT1 elaborates it from an importing file) |
| `ℍ^n(X; ℚ_X[0]) = H^n(X; ℚ)` | `unitHypercohomologyEquiv`: `hypercohomologyMapIso (forgetUnitComplexIso X)` then upstream's `hypercohomologyAddEquivConstantCohomology ℚ X n` | upstream's identification, as used by upstream's `fieldToDeRhamCohomology`; finding 8 |

The direction is that of `Adjunction.extEquiv.symm`: a class `ℤ_X → forget C[n]` goes to its adjoint `ℚ ⊗ ℤ_X → C[n]`, then to `ℚ_X → C[n]`. `rationalExtEquiv` is built with the same direction (`extEquivQ … |>.symm`), so the two sides of the agreement are the same construction on `ℚ_X[0]`, one on complexes in the derived category and one on `Ext`.

## 2. Can the hypotheses be satisfied?

The statements have no hypotheses beyond `X : Over (Spec ↧ℂ)`; `Spec ℂ` over itself is an instance (`HodgeLadder.Tests.Witness`). Content needs a nonzero class. RT4 proves, from the stated agreement, that the unit goes to the identity (section 7b); on a nonempty `X(ℂ)` the unit `Cup.one X` is nonzero (its image under upstream's Ψ is `oneSing`, `HodgeLadder.Cup.oneSing_ne_zero`), so both sides of the agreement are nonzero there.

## 3. Is the conclusion trivially true?

No. Attempts that failed: `rfl` on the agreement at `n = 0` (RT4), and `simp only [rationalHypercohomologyEquiv_apply]; done` (RT4); the prover reports `rfl`, `simp` and `exact?` failing in general. No definition unfolds to `True`, there is no `ℕ∞` coercion and no empty index type; `ℍ^0` of a nonempty `X` is nonzero (section 2). Naturality is proved and is a real compatibility (it uses `homEquiv_naturality_right_symm` and the naturality of `commShiftIso`), but it holds for any rescaling of the equivalence by an automorphism of `ℚ_X`, so it does not pin the scale; the agreement does (conventions row "Rational hypercohomology bridge").

What would make the agreement false: a −1 (or any non-identity automorphism of `ℚ_X`) inserted in `sourceIso`, `targetIso` or `forgetUnitComplexIso`. RT8 shows that the shift step does not tolerate a sign: the variant with a minus sign reduces by `simp` to `ε = −ε` and stays open.

## 4. Interface rung?

No structure and no axioms. Data introduced locally: the `HasDerivedCategory` instances (the same term as upstream's), the `CatCommSq` instances (`mapDerivedCategoryFactors.symm`), and the `Lifting` inside the proof of `adjDerived_commShift` (`CatCommSq.hComp … |>.iso.symm`). The first two are canonical; the last enters only a proof of a `Prop` (`Adjunction.CommShift` is a `Prop`), and `exact NatTrans.CommShift.liftNatTrans …` would fail to typecheck if it did not match the lifting inside `Adjunction.Localization.ε`. No axiom of any structure implies the agreement.

## 5. Checker and axioms

`python3 tools/check.py --no-build` in the worktree (scratch moved out for the run): every ledger declaration accepted with the three standard axioms; `REJECTED (sorry: HodgeLadder/Hodge/RationalHypercohomology.lean:477)`, the proof of the agreement. RT1, `#print axioms`: `rationalHypercohomologyEquiv`, `rationalHypercohomologyEquiv_naturality`, `adjDerived`, `adjDerived_commShift`, `Adjunction.mapCochainComplex`, `mapCochainComplex_commShift`, `mapCochainComplex_unit_app_f`, `mapCochainComplex_counit_app_f`, `unitHypercohomologyEquiv`, `unitHypercohomologyEquiv_hom`, `hypercohomologyMap_id` depend on `[propext, Classical.choice, Quot.sound]`; `rationalHypercohomologyEquiv_rationalUnitComplex` adds `sorryAx`. The module is not imported from `HodgeLadder.lean` yet, so `lake build` of the default target does not compile it; the checker's sorry scan is textual and finds it.

The ledger entry has `module: null` and names no path. The sketch's sentence "the ledger entry names `HodgeLadder/Rational/Hypercohomology/Equiv.lean`" is wrong; no file in `ledger/`, `docs/` or `tools/` names that path except the sketch itself (change 1).

## 6. Conventions

| Convention | Used by | Truth depends on it? | Register |
|---|---|---|---|
| Rational Ext normalization (`rationalExtEquiv`: `Adjunction.extEquiv`, `tensorQSheafInt` with `1 ⊗ 1 ↦ 1` through `TensorProduct.AlgebraTensorModule.rid`, `forgetQX` from `constantCommuteCompose`) | the right side of the agreement | yes: the agreement is an identity | row present; certified by `cup_singular_comparison` |
| Upstream's `ℍ` source `ℤ_X[0]` and `constantIntegerSheafComplexIntIsoSingleULift` (`AddEquiv.ulift`, `n ↦ ⟨n⟩`, no sign) | `sourceIso` on the left, `unitHypercohomologyEquiv` on the right | no: it enters each side once and the two occurrences cancel in the agreement; its absolute normalization is upstream's and is shared with `fieldToDeRhamCohomology` | row "Extension class and H¹(𝒪ˣ)" records `AddEquiv.ulift`; covered by the new row |
| Shift on cochain complexes and `mapHomologicalComplex.commShiftIso` (identity in each degree; the `(−1)^n` on the shifted differential commutes with an additive functor) | `targetIso`, `adjComplex_commShift` | no sign arises; a sign here would break `mapCochainComplex_commShift`, which is proved by `ext; simp` | new row "Rational hypercohomology bridge" |
| `Adjunction.homAddEquiv` | the equivalence | `homAddEquiv` is `homEquiv` (`homAddEquiv_symm_apply` is `rfl`) | new row |
| `Functor.mapDerivedCategory` and its `CommShift` (Mathlib's instance), `mapDerivedCategorySingleFunctor` | both sides | the same instance on both sides (`Ext.mapExactFunctor_hom` and `ShiftedHom.map` use it, and so does `targetIso`) | new row |
| `HasDerivedCategory` instance terms | the types of both statements | which type the identity lives in | new row "Derived-category instances in statements" |
| `forgetUnitComplexIso` (`singleMapHomologicalComplex G`, `single(forgetQX)`, inverse of upstream's `constantFieldSheafComplexIntIsoSingle`) | `unitHypercohomologyEquiv`, and through it `de-rham-cup` | yes for consumers (finding 8) | new row, consumer clause |

No borrowed result with an external sign is used. Both rows are added to `docs/conventions.md` after the row "Rational Ext normalization", away from the two rows `main` added since the worktree base, so the merge does not conflict.

## 7. Equality first

`rationalHypercohomologyEquiv_rationalUnitComplex` is an identity and is stated exactly: an equation in `ShiftedHom (Q.obj ℚ_X[0]) (Q.obj ℚ_X[0]) n`, no scalar, no `∃ c`, no cast. `rationalHypercohomologyEquiv_naturality` is an identity, proved exactly. The rung's consumer identity is `fieldToDeRhamCohomology_cup` (rung `de-rham-cup`, open), which needs this agreement to carry the scale of `Cup.cup` to `deRhamCup`.

### Is the planned agreement proof sound?

Yes. Written out (notation of the sketch, `ε''` the derived counit, `u` upstream's `ULift` iso, `σ = singleMapHomologicalComplex G`):

- Left side: `sourceIso.hom ≫ F''(h ≫ (fG⁻¹)[n]) ≫ F''((G''.commShiftIso n).inv) ≫ ε''_{(Qℚ)[n]}`. Mathlib's `Adjunction.shift_counit_app` with `adjDerived_commShift` turns the last two factors into `(F''.commShiftIso n).hom ≫ (ε''_{Qℚ})[n]`. RT8 checks exactly this step at the concrete space in two rewrites (`rw [Adjunction.shift_counit_app (adjDerived X) n Y', Iso.hom_inv_id_app_assoc]`).
- Right side, from `rationalExtEquiv_hom` and `unitHypercohomologyEquiv_hom`: `α.hom ≫ single(forgetQX⁻¹)[n] = Q(u⁻¹) ≫ h ≫ Q(σ)[n]`, because `forgetUnitComplexIso.hom ≫ constantFieldSheafComplexIntIsoSingle.hom = σ ≫ single(forgetQX)`.
- After naturality of `F''.commShiftIso n`, the two sides agree once (1) `sourceIso.hom = single(tensorQSheafInt⁻¹) ≫ (F.mapDerivedCategorySingleFunctor 0).inv ≫ F''(Q u⁻¹)` (Mathlib's `mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app`) and (2) `F''(fG⁻¹) ≫ ε''_{Qℚ} = F''(Qσ) ≫ (F.mapDerivedCategorySingleFunctor 0).hom ≫ single(ε)` hold. By `Adjunction.localization_counit_app` (whose `CatCommSq` inverses are the factor isos), (2) reduces to the complex identity `ε'_{ℚ_X[0]} = F'(σ) ≫ singleMapHomologicalComplex F ≫ single(ε_{ℚ_X})`, determined in degree 0 (`mapCochainComplex_counit_app_f`) since the target is a single complex.

Every map is a unit, a counit or a bookkeeping isomorphism. These are the two shift-free identities the sketch names.

## 7b. Non-vacuity

| Statement | Smallest test | Exists? |
|---|---|---|
| the agreement fixes the scale | `rationalHypercohomologyEquiv_one` below: the unit `Cup.one X` goes to `ShiftedHom.mk₀ _ _ (𝟙 _)` | proved in RT4 from the stated agreement, in one `rw` chain (`sorryAx` only through the agreement); add it (change 3) |
| the classes are nonzero | `HodgeLadder.Cup.oneSing_ne_zero` with `rationalCohomologyAddEquivSingularCohomology_one` on a nonempty `X(ℂ)` | both exist |

```lean
/-- The unit goes to the identity of `ℚ_X[0]`, exactly. -/
theorem rationalHypercohomologyEquiv_one :
    rationalHypercohomologyEquiv X (rationalUnitComplex X) ((0 : ℕ) : ℤ)
        ((unitHypercohomologyEquiv X 0).symm (Cup.one X)) =
      ShiftedHom.mk₀ ((0 : ℕ) : ℤ) (by simp) (𝟙 _) := by
  rw [rationalHypercohomologyEquiv_rationalUnitComplex, AddEquiv.apply_symm_apply, Cup.one,
    Cup.oneY, AddEquiv.apply_symm_apply, Cup.oneExt, Abelian.Ext.mk₀_hom,
    CategoryTheory.Functor.map_id]
  rfl
```

RT4 needs `HodgeLadder.Cup.Product` for `Cup.one`; the module itself does not import it, so the test goes where both are imported (a test module or the module after adding the import).

## 8. Pin drift

The worktree pin equals `main`'s (`2ead713`, `v4.35.0-rc4`). The worktree base `0cdf92a` is behind `main`; `git diff HEAD main` on `SheafExact.lean`, `ExtBridge.lean`, `SheafTensor.lean`, `General/Ext.lean`, `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` is empty, and on `docs/conventions.md` it is two added rows unrelated to this rung. Nothing to diff upstream.

## Findings

1. **Faithful, at full strength** (section 1). Any ℤ-indexed complex, upstream's `ℍ`, additive, natural along chain maps, agreeing exactly with the checked `rationalExtEquiv` through upstream's own `ℍ^n(ℚ_X[0]) = H^n(X; ℚ)`.

2. **No hidden scalar in the construction.** `homAddEquiv` is `homEquiv`; the shift isomorphisms are identities in each degree; `Adjunction.CommShift` is a `Prop`; the `CatCommSq` data is `mapDerivedCategoryFactors.symm`; the `ULift` iso is `AddEquiv.ulift` and cancels in the agreement. RT8: the shift step holds with no sign and fails with one.

3. **The agreement plan is sound** (section 7). The step the sketch flags as needing `adjDerived_commShift` is two rewrites at the concrete space.

4. **The module cannot land as is.** The checker rejects the `sorry` at line 477. Prove the agreement before posting; a `stated` rung would need the agreement as a sorry-free `Prop` definition, which is a weaker deliverable than the ledger title and is not recommended here, since the plan is short.

5. **Naturality is in the form consumers use.** `de-rham-cup` moves classes along chain maps of `ShQ` complexes (the unit `ℚ_X[0] → Ω•_ℚ`, the truncation inclusions, the scalar endomorphisms behind upstream's `hypercohomologyModule` and `deRham_complex_smul_eq`), and the `ShiftedHom.comp`/`mk₀` form matches upstream's `hypercohomologyMap`. A `≫` form saves each consumer a `ShiftedHom.comp_mk₀` (change 6).

6. **Instance findings: the workarounds are sound.**
   - (a) The `HodgeLadder.Cup` instances are missed at every concrete space, `TopCat.of PUnit` included, with or without upstream's `implicit_reducible` attributes (RT6). The trace (RT7) shows the candidate list for `Functor.Additive` at `TopCat.of PUnit` without `Cup.tensorQSheaf_additive`, while `#synth` at a variable `Y` finds it. This is consistent with a discrimination-tree key mismatch: `tensorQSheaf` is an `abbrev`, so the key unfolds to terms in `↑Y`, and `↑(TopCat.of T)` reduces to `T` at a concrete space (cause inferred, not traced further). The six workaround instances are `Prop`-valued (`Additive`, `PreservesFiniteLimits`, `PreservesFiniteColimits`), so supplying them by hand cannot change any term. They are reusable from an importing file with `attribute [local instance] HodgeLadder.rhTensorAdditive …` (RT5b, RT8). Every consumer at the concrete space (`de-rham-cup`, `pairing-product`, `derived-tensor-bounded` at `X(ℂ)`) will meet the same failure: record it in `docs/gaps.md` (change 7).
   - (b) The two spellings `forgetComplex` and `forgetComplexSite` are the same term with target categories that are definitionally equal; the kernel checks every crossing. Keep the statements on the analytic spelling (as now) and the site spelling inside proofs. A gaps row, not a convention: no sign or scale depends on it.
   - (c) `HasDerivedCategory` is data, and the statement types depend on the instance term. Registered as the conventions row "Derived-category instances in statements".
   - (d) `liftNatTrans` with a hand-supplied `Lifting`: sound (section 4).

7. **Local duplicate of an upstream lemma.** `HodgeLadder.hypercohomologyMap_id` restates upstream's `AlgebraicGeometry.ComplexPoint.hypercohomologyMap_id` (`HodgeConjecture/Lemmas/AlgebraicGeometry/Hodge/Filtration.lean:151`, `hypercohomologyMap X (𝟙 K) n = AddMonoidHom.id _`, built at the pin). A file that imports both and opens `AlgebraicGeometry.ComplexPoint` inside `namespace HodgeLadder` gets two candidates for one name. Use upstream's (change 5).

8. **Consumer clause for `rational-de-rham-complex`.** `de-rham-cup` will compare `forget` of the rational unit map with upstream's `fieldToHolomorphicDeRhamComplexInt ℚ X`. If that comparison goes through any isomorphism `forget ℚ_X[0] ≅ constantFieldSheafComplexInt ℚ X` other than `forgetUnitComplexIso`, an automorphism of `ℚ_X` (for example −1) can enter between the bridge and `ι`, and `fieldToDeRhamCohomology_cup` would be off by it. State the unit compatibility of `rational-de-rham-complex` through `forgetUnitComplexIso` (change 8).

9. **Build cost: accept, after one change.** Measured: the module 75 to 100 s (prover); the kernel spends 13 to 14 s on each of `unitHypercohomologyEquiv` and the agreement statement. `rationalExtEquiv_hom` at the concrete space: 276 s (prover). At a general `Y` with the `HasDerivedCategory` instances as binders: about 80 s, almost all kernel type checking (RT3p, RT3v1: 73 to 84 s; the factored proof through three generic lemmas does not lower it, so the cost sits in defeq checks of the instance terms of sheaf categories). Instantiating it at `TopCat.of (ComplexPoint X)` by a term: 36 s of kernel (RT5b). The general lemma is also reusable by `pairing-product` and `de-rham-cup`. Put it in its own module so that it builds in parallel with the definitions (change 2).

## Recommended changes

Required:

1. Prove `rationalHypercohomologyEquiv_rationalUnitComplex` by the planned route; then add `public import HodgeLadder.Hodge.RationalHypercohomology` to `HodgeLadder.lean`, set the ledger's `module` to `HodgeLadder.Hodge.RationalHypercohomology` and list the declarations (`rationalHypercohomologyEquiv`, `rationalHypercohomologyEquiv_naturality`, `rationalHypercohomologyEquiv_rationalUnitComplex`, `unitHypercohomologyEquiv`, `adjDerived`, `adjDerived_commShift`, `CategoryTheory.Adjunction.mapCochainComplex`, and the test of change 3). In the sketch, replace "the ledger entry names `HodgeLadder/Rational/Hypercohomology/Equiv.lean`, to be reconciled when the rung is posted" by "the ledger entry has no module yet".

2. State `rationalExtEquiv_hom` for a general space, with instance binders, in a new module `HodgeLadder/Cup/RationalExtHom.lean` (imports `HodgeLadder.Cup.SheafExact`, `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`), and instantiate it in the agreement proof by a term. Checked in RT5 with the standard axioms (about 80 s), and the instantiation in RT5b (36 s):

```lean
section
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasExt.{0} C] [HasExt.{0} D] [HasDerivedCategory C] [HasDerivedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- `Adjunction.extEquiv.symm` as a composite in the derived category. -/
lemma _root_.CategoryTheory.Adjunction.extEquiv_symm_hom (adj : F ⊣ G) {X : C} {Y : D} {n : ℕ}
    (e : Abelian.Ext.{0} X (G.obj Y) n) :
    (adj.extEquiv.symm e).hom =
      (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ F.mapDerivedCategory.map e.hom ≫
        (F.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app _)⟦(n : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor _ 0).map (adj.counit.app Y))⟦(n : ℤ)⟧' := by
  simp only [Adjunction.extEquiv_symm_apply, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
    Abelian.Ext.mapExactFunctor_hom, ShiftedHom.comp_mk₀, ShiftedHom.map, Category.assoc]

/-- `Ext.postcompIsoAddEquiv` in the derived category. -/
lemma postcompIsoAddEquiv_hom {X Y Z : C} (e : Y ≅ Z) (n : ℕ) (α : Abelian.Ext.{0} X Y n) :
    (HodgeLadder.Ext.postcompIsoAddEquiv e X n α).hom =
      α.hom ≫ ((DerivedCategory.singleFunctor _ 0).map e.hom)⟦(n : ℤ)⟧' := by
  simp only [HodgeLadder.Ext.postcompIsoAddEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]

/-- `Ext.precompIsoAddEquiv` in the derived category. -/
lemma precompIsoAddEquiv_hom {X Y Z : C} (e : X ≅ Y) (n : ℕ) (α : Abelian.Ext.{0} Y Z n) :
    (HodgeLadder.Ext.precompIsoAddEquiv e Z n α).hom =
      (DerivedCategory.singleFunctor _ 0).map e.hom ≫ α.hom := by
  simp only [HodgeLadder.Ext.precompIsoAddEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp]
end

section
variable (Y : TopCat.{0}) [HasDerivedCategory (Sheaf (Cup.J Y) AddCommGrpCat.{0})]
  [HasDerivedCategory (Sheaf (Cup.J Y) (ModuleCat.{0} ℚ))]

/-- `Cup.rationalExtEquiv` as a composite in the derived category of rational sheaves. -/
lemma rationalExtEquiv_hom (n : ℕ) (α : Sheaf.H.{0} (Cup.constAb Y (AddCommGrpCat.of ℚ)) n) :
    (Cup.rationalExtEquiv Y n α).hom =
      (DerivedCategory.singleFunctor _ 0).map (Cup.tensorQSheafInt Y).inv ≫
      ((Cup.tensorQSheaf Y).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
      (Cup.tensorQSheaf Y).mapDerivedCategory.map
        (α.hom ≫ ((DerivedCategory.singleFunctor _ 0).map (Cup.forgetQX Y).inv)⟦(n : ℤ)⟧') ≫
      ((Cup.tensorQSheaf Y).mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
      (((Cup.tensorQSheaf Y).mapDerivedCategorySingleFunctor 0).hom.app _)⟦(n : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor _ 0).map
        ((Cup.adjQSheaf Y).counit.app (Cup.QX Y)))⟦(n : ℤ)⟧' := by
  change (Cup.extPrecompEquiv _ n ((Cup.extEquivQ Y _ _ n).symm
    (Cup.extPostcompEquiv _ n α))).hom = _
  rw [Cup.extPrecompEquiv, precompIsoAddEquiv_hom, Cup.extEquivQ,
    Adjunction.extEquiv_symm_hom, Cup.extPostcompEquiv, postcompIsoAddEquiv_hom]
  rfl
end
```

   In RT5 the generic lemmas sat in a scratch namespace; with the names above, check that `HodgeLadder.Ext` has no lemma of the same name first. The three generic lemmas are candidates for `HodgeLadder/General/Ext.lean` and for Mathlib.

Recommended:

3. Add the test `rationalHypercohomologyEquiv_one` (section 7b, exact text) and name it in the ledger.

4. Keep the six `Prop`-valued instances and the `HasDerivedCategory` instances `local`, and say in the module docstring how a consumer activates them:

```lean
attribute [local instance] HodgeLadder.rhHasDerivedCategory HodgeLadder.rhSiteHasDerivedCategory
  HodgeLadder.rhHasExt HodgeLadder.rhQHasDerivedCategory HodgeLadder.rhTensorAdditive
  HodgeLadder.rhForgetAdditive HodgeLadder.rhTensorPFL HodgeLadder.rhTensorPFC
  HodgeLadder.rhForgetPFL HodgeLadder.rhForgetPFC
```

   (this line, with upstream's `implicit_reducible` attributes, is what RT5b and RT8 use from an importing file).

5. Replace `HodgeLadder.hypercohomologyMap_id` by upstream's: add `public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration`, delete the local lemma, and in `hypercohomologyMapIso` write `rw [← hypercohomologyMap_comp_apply, e.hom_inv_id, hypercohomologyMap_id, AddMonoidHom.id_apply]` (and the same with `e.inv_hom_id`). Not run in scratch.

6. Add the composition form of naturality (not run in scratch):

```lean
/-- Naturality in the complex, as postcomposition with the shifted map. -/
theorem rationalHypercohomologyEquiv_map
    {C C' : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ} (f : C ⟶ C') (n : ℤ)
    (x : ℍ^n(X; (forgetComplex X).obj C)) :
    rationalHypercohomologyEquiv X C' n (hypercohomologyMap X ((forgetComplex X).map f) n x) =
      rationalHypercohomologyEquiv X C n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  rw [rationalHypercohomologyEquiv_naturality, ShiftedHom.comp_mk₀]
```

7. `docs/gaps.md`. Under "General lemmas kept local":

   > | `CategoryTheory.Adjunction.mapCochainComplex`, `mapCochainComplex_unit_app_f`, `mapCochainComplex_counit_app_f`, `mapCochainComplex_commShift` (an adjunction of additive functors on ℤ-indexed cochain complexes, degreewise, commuting with shifts); `HodgeLadder.isoPostcompAddEquiv`, `isoPrecompAddEquiv` (composition with an isomorphism as an `AddEquiv` of morphism groups); `Adjunction.extEquiv_symm_hom`, `postcompIsoAddEquiv_hom`, `precompIsoAddEquiv_hom` if change 2 lands | `HodgeLadder.Hodge.RationalHypercohomology`, `HodgeLadder.Cup.RationalExtHom` | any preadditive categories; Mathlib has none of them at the pin | 2026-11-27 |

   Under "Known weaknesses":

   > | Instance search misses the `HodgeLadder.Cup` instances (`tensorQSheaf_additive`, `forgetSheaf_additive`, the exactness instances) at every concrete space `TopCat.of T`, `TopCat.of PUnit` included, while it finds them at a variable `Y` (red team `rational-hypercohomology-equiv`, trace RT7; likely a discrimination-tree key through `↑Y`). Workaround: `Prop`-valued local instances given as terms (`HodgeLadder.rhTensorAdditive` and five others). Upstream's `AnalyticAdditiveSheaf X` and `Sheaf (Opens.grothendieckTopology _) AddCommGrpCat` are two spellings of one category; instances and `rw` do not cross between them, so the module keeps statements on the first and proofs on the second | Each consumer at `X(ℂ)` repeats the `attribute [local instance]` line; build time from kernel defeq checks of the two spellings (13 to 36 s per declaration) | 2026-11-27 |

8. For rung `rational-de-rham-complex` (open), state the unit through `forgetUnitComplexIso`, with names to be fixed by that rung:

```lean
theorem forget_rationalDeRhamUnit :
    (forgetComplex X).map (rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom =
      (forgetUnitComplexIso X).hom ≫ fieldToHolomorphicDeRhamComplexInt ℚ X
```

   where `rationalDeRhamUnit X : rationalUnitComplex X ⟶ Ω•_ℚ` and `forgetRationalDeRhamIso X : (forgetComplex X).obj Ω•_ℚ ≅ Ω•(X)`. Add the clause to that rung's ledger note.
