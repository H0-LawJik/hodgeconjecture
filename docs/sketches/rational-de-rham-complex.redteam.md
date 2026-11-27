# Red team: `rational-de-rham-complex` (statement and proof)

Date: 2026-11-27. Worktree `rational-de-rham-complex` at base `41f2f6b`, uncommitted `HodgeLadder/Hodge/RationalDeRhamComplex.lean` and the section "rational-de-rham-complex: statement" of `docs/sketches/cup-hodge-filtration.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`; `lakefile.toml` and `lake-manifest.json` are the same on the base and on `main` (`44a0e85`).

Read: the ledger entries `rational-de-rham-complex`, `rational-hypercohomology-equiv`, `wedge-sheafify`, `wedge-sheaf-map`, `de-rham-cup`; the module; `HodgeLadder/Cup/SheafExact.lean` (`U`, `forgetSheaf`, `QX`, `forgetQX`), `HodgeLadder/Cup/SheafTensor.lean`; `main`'s `HodgeLadder/Hodge/RationalHypercohomology.lean` (`forgetComplex`, `rationalUnitComplex`, `forgetUnitComplexIso`, read only); the sketch section; `docs/sketches/rational-hypercohomology-equiv.redteam.md` (change 8), `wedge-presheaf.redteam.md` (finding 2), `cup-hodge-filtration.redteam.md`; upstream `Definitions/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean` (`holomorphicDeRhamPresheaf`, `holomorphicDeRhamDifferential`, `holomorphicDeRhamSheaf`, `holomorphicDeRhamComplex`, `constantsToHolomorphicDeRhamZero`, `holomorphicDeRhamComplexInt`), `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (`fieldToComplexConstantSheaf`, `constantFieldSheafComplexInt`, `fieldToHolomorphicDeRhamComplexInt`, `constantFieldSheafComplexIntIsoSingle`, `hodgeFilteredDeRhamComplex`, `hodgeFilteredDeRhamInclusion`, `hodgeFiltration`), `Definitions/AlgebraicGeometry/Hodge/AnalyticDifferentialForms.lean` (`HolomorphicForm`, `holomorphicFormOfConstant`), `Mathlib/Algebra/Homology/MapExtend.lean` (`mapExtendCanonicalIso`); Mathlib `Sites/PreservesSheafification.lean` (`sheafComposeNatIso`, `sheafifyComposeIso`, `sheafComposeIso_inv_fac`), `Sites/ConstantSheaf.lean` (`constantCommuteCompose`); `docs/conventions.md`, `docs/references.md`.

Scratch (directory `scratch_rt/` inside the worktree, deleted afterwards; 5 to 22 s each with `lake env lean`, after `lake build HodgeLadder.Hodge.RationalDeRhamComplex`, 32 s, since the olean was older than the source):

| File | What it tried | Result |
|---|---|---|
| T0 | `#synth` of `SMul ℚ` and `Module ℚ` on `HolomorphicForm X d U p` and on `Algebra.DeRham.Form ℂ 𝒪(U) p`, `SMul ℚ` and `Algebra ℚ` on `OpenHolomorphicFunctions X d U`, without this module | all six fail: no competing `ℚ`-structure at the pin |
| T1 | verbatim copies of `main`'s `rhForgetAdditive`, `forgetComplex`, `rationalUnitComplex`, `forgetUnitComplexIso`; the change-8 signature and the truncation lemma in the `forgetComplex` spelling, each by `exact` of the posted lemma; `#print axioms` on 20 declarations | all elaborate; every declaration uses `propext`, `Classical.choice`, `Quot.sound` only |
| T2 | the instance found is `holomorphicFormRatModule` (`with_reducible_and_instances rfl`); the wedge as a `ℚ`-bilinear map (`restrictScalars₁₂ ℚ ℚ`) and on `⊗[ℚ]` (`TensorProduct.lift`); the pin of the comparison against the sheafification maps (change 2); `rfl` and `simp` on `forget_rationalDeRhamUnit_unfolded` | first four succeed; `rfl` and `simp` fail |
| T3 | `hypercohomologyMap` applied to both sides of the unit and inclusion lemmas; `rationalDeRhamUnit` equals Mathlib's `extendSingleIso.inv ≫ extendMap (fromSingle₀Equiv.symm _)`; a witness `∃ Y, IsIntegral Y.left ∧ Smooth Y.hom ∧ Nonempty (forget Ω•_ℚ(Y) ≅ Ω•(Y))` at `HodgeLadder.Tests.point` | all succeed; the agreement closes at `congr 1` after `extendSingleIso_inv_comp_extendMap` (a first attempt by `rw` on `homFromSingleExtend_f_zero` failed to find the pattern) |
| T4 | `hodgeFiltration X p n` as the range of the forgotten rational truncation (change 4) | first attempt: `rw [h]` fails across the two spellings; second: `AddGroup ℍ^n(X; forget F^p Ω•_ℚ)` is not found with the site spelling; third, stated with `forgetComplex`: succeeds, standard axioms |
| T5 | `hypercohomologyMap X (forgetRationalDeRhamIso X).hom n` as posted, and the isomorphism retyped as `(forgetComplex X).obj (rationalDeRhamComplex X) ≅ Ω•(X)` with the same body | both elaborate |

**Verdict: pass with changes.** The complex, its truncations and its unit are upstream's objects with a `ℚ`-structure, compared by the canonical sheafification isomorphism; every identity is exact, with no sign and no scalar, and every proof uses the three standard axioms. Changes 1 and 2 are required before the rung is posted; 3 to 6 are recommended; 7 proposes a new rung.

## 1. Is this the statement the literature makes?

Source: [`Voisin2002`] I, the holomorphic de Rham complex `Ω•_X` of a complex manifold, the holomorphic Poincaré lemma `ℂ_X ≃ Ω•_X` (the unit is the inclusion of constants into `𝒪_X`), and the Hodge filtration `F^p H^n(X; ℂ) = Im(ℍ^n(X; Ω^{≥p}_X) → ℍ^n(X; Ω•_X))` by the stupid truncation `Ω^{≥p}` (section numbers unverified). The rung puts no new mathematics into these objects; it re-reads upstream's as sheaves of `ℚ`-vector spaces. The literature comparison is therefore with upstream, field by field.

| Object | Upstream | Rung | Match |
|---|---|---|---|
| sections | `HolomorphicForm X d U p`, `AddCommGrpCat.of` | same type, `ModuleCat.of ℚ` with `Module.compHom _ (algebraMap ℚ ℂ)` | underlying presheaf equal by `rfl` (`rationalHolomorphicFormPresheaf_comp_forget`) |
| restriction | `(holomorphicFormRestriction X d i p).toAddMonoidHom` | `.restrictScalars ℚ` of the same map | `rfl` |
| differential | `holomorphicFormDifferential X d U p` | `.restrictScalars ℚ` of the same map | `rfl` (`whiskerRight_rationalHolomorphicFormDifferential`) |
| sheaf | `presheafToSheaf J AddCommGrpCat` | `presheafToSheaf J (ModuleCat ℚ)`, compared by `sheafComposeNatIso` | `forgetRationalHolomorphicFormSheafIso`, natural in `d` |
| ℕ-complex | `CochainComplex.of` | `CochainComplex.of` | `forgetRationalHolomorphicDeRhamComplexNatIso`, `isoOfComponents` |
| ℤ-complex `Ω•(X)` | `(holomorphicDeRhamComplex X (dim X.left)).extend embeddingUpNat` | the same `extend`, same `dim X.left` | `forgetRationalDeRhamIso`, target `Ω•(X)` exactly |
| `F^p Ω•(X)` | `Ω•(X).stupidTrunc (embeddingUpIntGE p)`, `p : ℤ` | `(rationalDeRhamComplex X).stupidTrunc (embeddingUpIntGE p)`, `p : ℤ` | `forgetRationalHodgeFilteredIso`, target `F^p Ω•(X)` exactly; inclusions match (`forget_rationalHodgeFilteredInclusion`) |
| unit | `fieldToComplexConstantSheaf ℚ X` (`algebraMap ℚ ℂ` on constant sheaves) then `constantsToHolomorphicDeRhamZero` (`holomorphicFormOfConstant`), extended | sheafified `q ↦ holomorphicFormOfConstant (algebraMap ℚ ℂ q)` on `ℚ_X = constantSheaf (ModuleCat.of ℚ ℚ)` | `forget_rationalConstantsToFormsSheaf` in degree 0, `forget_rationalDeRhamUnit_unfolded` on complexes |

`hodgeFiltration` is the range of `hypercohomologyMap X (hodgeFilteredDeRhamInclusion X p) n`; the rung's inclusion lies over exactly that map, so the range of the forgotten rational truncation is upstream's `F^p` (T4, change 4). This is the statement `cup-hodge-filtration` consumes.

## 2. Can the hypotheses be satisfied?

Yes. The `Forms` section needs `[SmoothOfRelativeDimension d X.hom]`, the `Complex` section `[IsIntegral X.left] [Smooth X.hom]`. T3:

```lean
example : ∃ Y : Over (Spec ↧ℂ), ∃ (_ : IsIntegral Y.left) (_ : Smooth Y.hom),
    Nonempty ((forgetComplex Y).obj (rationalDeRhamComplex Y) ≅ holomorphicDeRhamComplexInt Y) :=
  ⟨HodgeLadder.Tests.point, inferInstance, inferInstance, ⟨forgetRationalDeRhamIso _⟩⟩
```

## 3. Is the conclusion trivially true?

No definition unfolds to `True`, no index type is empty, no `ℕ∞` coercion enters, and every hypothesis is used (smoothness for `dim X.left` and the forms, integrality through upstream's `SmoothOfRelativeDimension (dim X.left)`). Attempts:

- `rfl` and `simp` on `forget_rationalDeRhamUnit_unfolded`: both fail (T2). The prover reports the same for `forget_rationalConstantsToFormsSheaf` and `forget_rationalHodgeFilteredInclusion`.
- Replacing the unit by its negative: the forget functor is faithful and the target sheaves are torsion-free, so the statement for `−rationalDeRhamUnit X` is equivalent to `fieldToHolomorphicDeRhamComplexInt ℚ X = 0`. The lemma separates the unit from its negative as soon as upstream's unit is nonzero (section 7b).
- `forget_rationalHodgeFilteredInclusion` holds for every isomorphism in place of `forgetRationalDeRhamIso`, since `forgetRationalHodgeFilteredIso` is built from it by the functorial truncation. That is the expected shape of a coherence lemma; its content is that both sides end in upstream's `F^p Ω•(X)` and `hodgeFilteredDeRhamInclusion X p`.
- `holomorphicFormRatModule_unique` is `Subsingleton.elim`, as intended: it records that the choice of `ℚ`-structure carries no information.

**The automorphism question (prover's note).** Every posted statement survives the substitution `(u, e) ↦ (u ≫ σ, forget(σ)⁻¹ ≫ e)` for a chain automorphism `σ` of `Ω•_ℚ`, with `u = rationalDeRhamUnit X` and `e = forgetRationalDeRhamIso X` (the truncation lemma too, since stupid truncation is functorial). The definitions are concrete, so in fact `σ = 𝟙`; the gap is that no statement certifies `e`. It matters for `de-rham-cup`: its proof chains the unit lemma, the unit law `μ ∘ (u ⊗ u) = u` of `wedge-sheaf-map` and transport along `e`; for `σ = −𝟙` the twisted unit law fails, and `deRhamCup` would mean the wedge on upstream's `Ω•(X)` only through the definition of `e`. `wedge-sheafify` lives in `ShQ` and mentions neither `e` nor upstream's sheaves, so it can pin `μ` against the `ℚ`-side sheafification map and cannot pin `e`. The place to pin `e` is this rung, by Mathlib's `sheafComposeIso_inv_fac`: forgetting the `ℚ`-structure of `toSheafify J P_ℚ` and applying `e_p` gives `toSheafify J P` for upstream's presheaf `P`. By the universal property of sheafification, any `σ_p` with `toSheafify ≫ σ_p = toSheafify` is the identity, so this determines `e_p`, hence `e` (it is `isoOfComponents` of the `e_p` after identity components), hence `u` (forget is faithful). Checked in T2; change 2.

## 4. Interface rung?

No. The rung defines data and proves lemmas about it; there is no structure of axioms.

## 5. Checker and axioms

`python3 tools/check.py --no-build` on the worktree: `ACCEPTED: all checks passed`. The module is not yet imported from `HodgeLadder.lean` and the ledger entry names no declarations, so the checker does not see it yet. `#print axioms` in T1 on the 20 load-bearing declarations (`forget_rationalDeRhamUnit_unfolded`, `forget_rationalHodgeFilteredInclusion`, `forget_rationalConstantsToFormsSheaf`, `forget_rationalHolomorphicFormSheafDifferential`, `forgetRationalDeRhamIso`, `forgetRationalHodgeFilteredIso`, `rationalDeRhamUnit`, `rationalDeRhamComplex_isStrictlyLE`, `holomorphicFormRatModule_unique`, `holomorphicForm_isScalarTower`, `rationalHolomorphicFormSheaf_isZero_of_lt`, the generic lemmas, the change-8 form and the truncation lemma in the `forgetComplex` spelling): `[propext, Classical.choice, Quot.sound]` each. No `sorry`, `native_decide`, `axiom` or `unsafe` in the file. None of the main new names (`homFromSingleExtend`, `mapStupidTruncIso`, `forgetSheafifyNatIso`, `holomorphicFormRatModule`, `rationalDeRhamComplex`, `rationalDeRhamUnit`, `forgetRationalDeRhamIso` and four more) is declared elsewhere on `main`.

Instances. `rdrPreservesSheafification`, `rdrForgetAdditive`, `rdrForgetAdditive'` are `Prop`-valued (`GrothendieckTopology.PreservesSheafification` and `Functor.Additive` are `Prop` classes), local, and are the same terms as `Cup.preservesSheafification_U _` and `main`'s `rhForgetAdditive`; they carry no data and cannot change a type. `rdrForgetAdditive'` repeats `rdrForgetAdditive` because the two sections bind different variables; one instance taking only `X`, placed before both sections, would do.

## 6. Conventions

| Convention | Rung | Checked against | Truth depends on it |
|---|---|---|---|
| `ℚ`-structure on forms | `Module.compHom _ (algebraMap ℚ ℂ)`, `q • θ = (q : ℂ) • θ` (`rfl`) | unique (`subsingleton_rat_module`); no other `SMul ℚ` at the pin (T0) | no: any choice is this one |
| Comparison `e_p` | `((sheafComposeNatIso J U adj adj).app P_ℚ).symm` | Mathlib's canonical map; `forgetQX` is `constantCommuteCompose`, built from the same `sheafComposeNatIso`, which is why the degree-zero unit square closes exactly | yes for `de-rham-cup`: a non-identity automorphism in `e` would twist `deRhamCup` (section 3); pinned by change 2 |
| ℕ to ℤ | upstream's `mapExtendCanonicalIso` (identity in retained degrees, zero comparison elsewhere), `extendXIso` | `HodgeConjecture/Mathlib/Algebra/Homology/MapExtend.lean` | no sign possible: components are identities or maps between zero objects |
| Unit | `q ↦ holomorphicFormOfConstant X d U (algebraMap ℚ ℂ q)`, sheafified | upstream `fieldToComplexConstantSheaf` (`algebraMap K ℂ`) and `constantsToHolomorphicDeRhamZero` (`holomorphicFormOfConstant`); row "Rational-to-de Rham map and the range of F^p": no `(2πi)^p`, no conjugation | yes: the scale of `fieldToDeRhamCohomology_cup`; pinned exactly by `forget_rationalDeRhamUnit_unfolded` |
| `ℚ_X[0]` to upstream | `singleMapHomologicalComplex ≪≫ singleFunctor.mapIso forgetQX ≪≫ (constantFieldSheafComplexIntIsoSingle ℚ X).symm` | the body of `main`'s `forgetUnitComplexIso`, token for token (T1) | yes, as above; change 1 makes the type refer to that declaration |
| `F^p` range and indexing | `stupidTrunc (embeddingUpIntGE p)`, `p : ℤ` | upstream `hodgeFilteredDeRhamComplex`; row "Hodge filtration" | membership statements only |
| Koszul sign | not used: no tensor product in this rung | row "Tensor product of ℤ-indexed cochain complexes" | not applicable here |

Every borrowed result is stated against the definitions it is used with: `sheafComposeIso_inv_fac` is about `sheafifyComposeIso = (sheafToPresheaf).mapIso (sheafComposeNatIso.app P)`, which is `e_p.symm` after `sheafToPresheaf` by definition; `mapExtendCanonicalIso_hom_f` and `extendMap_f` are used at `embeddingUpNat`, whose `f 0 = 0` is `rfl`. The sketch says "No new convention for `docs/conventions.md`"; the comparison `e` is a normalization that `de-rham-cup` depends on, so I added the row "Rational de Rham complex and its comparison".

## 7. Equality first

Every target is an identity of morphisms, proved exactly: no scalar, no sign, no "up to". The identities that this rung prepares are `fieldToDeRhamCohomology_cup` (`de-rham-cup`, open) and, through it, the inclusion `F^p ∪ F^q ⊆ F^{p+q}` of `cup-hodge-filtration`. Change 4 adds the equality `hodgeFiltration X p n = range(…)` that the inclusion step consumes.

## 7b. Non-vacuity

The smallest test that fails if the unit statement holds for a trivial reason is upstream's unit being nonzero on a nonempty variety:

```lean
theorem fieldToHolomorphicDeRhamComplexInt_point_ne_zero :
    AlgebraicGeometry.ComplexPoint.fieldToHolomorphicDeRhamComplexInt ℚ HodgeLadder.Tests.point ≠ 0
```

With `forget_rationalDeRhamUnit` (faithful forget, `forgetUnitComplexIso` an isomorphism) it gives `rationalDeRhamUnit HodgeLadder.Tests.point ≠ 0`. It does not exist, upstream or here: upstream has the presheaf-level ingredient `holomorphicFormOfConstant_injective` on nonempty opens, but it is `private`; `HodgeLadder.Tests.hodge_zero_ne_bot` does not touch `ι` (`F^0` is everything). The test is a sanity check of an upstream definition, so it belongs upstream; change 7 proposes it as a rung here until it lands there. Not blocking: the rung's identities pin its maps to upstream's, and a zero upstream unit would be an upstream defect that the test, once written, would catch.

## 8. Pin drift

None. The rung was written at `41f2f6b`, whose `lakefile.toml` and `lake-manifest.json` are those of `main`. Between the base and `main` only `HodgeLadder.lean`, the new modules `HodgeLadder/Cup/RationalExtHom.lean`, `HodgeLadder/Hodge/RationalHypercohomology.lean` and documents changed; none of this module's dependencies changed. Drift risk at a future bump: if upstream gives `OpenHolomorphicFunctions` an `Algebra ℚ` or `HolomorphicForm` a `Module ℚ`, the instance here becomes a second, non-reducibly-equal instance (finding 6). The drift check should rerun T0's `#synth Module ℚ (HolomorphicForm X d U p)` without this module.

## Findings

1. **Statement is right** (section 1). Each object is upstream's, re-read with a `ℚ`-structure; each comparison ends in upstream's `Ω•(X)`, `F^p Ω•(X)`, `hodgeFilteredDeRhamInclusion X p` and `fieldToHolomorphicDeRhamComplexInt ℚ X`, with nothing between them but canonical isomorphisms.

2. **The unit pin is exactly change 8, but only as a copy.** The right side of `forget_rationalDeRhamUnit_unfolded` is the body of `forgetUnitComplexIso`, token for token; with verbatim copies of `forgetComplex`, `rationalUnitComplex` and `forgetUnitComplexIso` the change-8 signature closes by `exact` (T1), with no scalar and no other isomorphism. `main` now has `HodgeLadder.Hodge.RationalHypercohomology` (#179), so the folded form can be stated against the real declaration. Until it is, a later edit of `forgetUnitComplexIso` would leave this rung green and the two out of step (change 1).

3. **The automorphism gap matters, and this rung closes it** (section 3). `wedge-sheafify` cannot close it; one Mathlib lemma does (change 2). With it, `e`, and through faithfulness `u`, are pinned by statements, and `wedge-sheafify` should pin `μ` against `toSheafify` on the `ℚ` side, so that every map of the front is tied to upstream's presheaf data.

4. **Spelling: acceptable for morphism identities, awkward for ℍ** (prover's question 1). Equalities of morphisms elaborate and transfer by `exact`/`congrArg` (T1, T3, T5). `ℍ^n(X; ·)` of an object in the site spelling has no `AddGroup` instance (T4, second attempt), and `rw` does not cross the spellings (T4, first attempt). Consumers meet `ℍ` at once, so state the isomorphisms in the `forgetComplex` spelling once the module imports it (change 3).

5. **`homFromSingleExtend` is sound and agrees with Mathlib's shape** (prover's question 2). `rationalDeRhamUnit` equals `extendSingleIso.inv ≫ extendMap (fromSingle₀Equiv.symm ⟨u, _⟩)`, upstream's way of building `fieldToHolomorphicDeRhamComplexInt`, by `congr 1` after `extendSingleIso_inv_comp_extendMap` (T3). Mathlib has no map out of `A[0]` into an extended complex at the pin. Keep the definition; list the generic layer in `docs/gaps.md` "To upstream".

6. **`Module ℚ` instance: global is right at the pin** (prover's question 3). T0 shows no competing `SMul ℚ` or `Module ℚ` on `HolomorphicForm`, on the form module, or on `OpenHolomorphicFunctions`; the instance found is this one reducibly (T2); the wedge is `ℚ`-bilinear for it through `restrictScalars₁₂ ℚ ℚ` and lifts to `⊗[ℚ]` (T2), which is what `wedge-sheafify` needs. A local instance would force every consumer to repeat it while `ModuleCat.of ℚ (HolomorphicForm …)` already bakes it into `rationalHolomorphicFormPresheaf`. It is an instance on an upstream type, so record it in `docs/gaps.md` "To upstream" and in the drift check (section 8).

7. **What `wedge-sheafify` needs from here** (prover's question 4). Not a statement about `HodgeLadder.Cup.tensorLeftIso`: that isomorphism is internal to `ShQ` (tensor of sheaves as sheafified presheaf tensor) and does not involve `forgetSheafifyNatIso`. It needs the `ℚ`-bilinear wedge (finding 6), `rationalHolomorphicFormPresheaf` as the presheaf to sheafify, and change 2 to connect the sheafified wedge to upstream's sheaves.

8. **Hygiene.** The anonymous instance `(rationalDeRhamComplex X).IsStrictlyGE 0` has no docstring and no name (its sibling is `rationalDeRhamComplex_isStrictlyLE`). The sketch section was written against a base where `main` has since edited `docs/sketches/cup-hodge-filtration.md` and `docs/conventions.md`; expect a rebase conflict in the sketch.

## Recommended changes

1. **Required.** Rebase on `main`, add `public import HodgeLadder.Hodge.RationalHypercohomology`, and add, in the `Complex` section:

```lean
/-- **The unit lies over upstream's unit, through `forgetUnitComplexIso`** (red team of
`rational-hypercohomology-equiv`, change 8). Exact, no scalar. -/
theorem forget_rationalDeRhamUnit :
    (forgetComplex X).map (rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom =
      (forgetUnitComplexIso X).hom ≫ fieldToHolomorphicDeRhamComplexInt ℚ X :=
  forget_rationalDeRhamUnit_unfolded X
```

   Name `forget_rationalDeRhamUnit` in the ledger as the unit declaration of record. If the import's build time (about 758 s, serial before this module) is unwanted, put these lines in a separate module `HodgeLadder/Hodge/RationalDeRhamUnit.lean` importing both; `de-rham-cup` imports both anyway.

2. **Required.** Pin the comparison against the sheafification maps, in the `Forms` section after `forgetRationalHolomorphicFormSheafIso` (checked in T2):

```lean
/-- The comparison `forget(Ω^p_ℚ) ≅ Ω^p` carries the rational sheafification map to upstream's:
forgetting the `ℚ`-structure of `P_ℚ ⟶ Ω^p_ℚ` and applying the comparison gives `P ⟶ Ω^p`, for
`P = holomorphicDeRhamPresheaf X d p`. By the universal property of sheafification, this
determines the comparison. -/
theorem toSheafify_comp_forgetRationalHolomorphicFormSheafIso (p : ℕ) :
    Functor.whiskerRight (toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
        (rationalHolomorphicFormPresheaf X d p)) Cup.U ≫
      (sheafToPresheaf (Cup.J (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}).map
        (forgetRationalHolomorphicFormSheafIso X d p).hom =
    toSheafify (Cup.J (TopCat.of (ComplexPoint X))) (holomorphicDeRhamPresheaf X d p) :=
  sheafComposeIso_inv_fac (Cup.J (TopCat.of (ComplexPoint X))) Cup.U
    (rationalHolomorphicFormPresheaf X d p)
```

   Add to the `wedge-sheafify` ledger note: state the wedge compatibility against `toSheafify` on the `ℚ` side, and reach upstream's sheaves through this lemma.

3. **Recommended, with change 1.** Retype the two comparisons in the `forgetComplex` spelling, bodies unchanged (T5 elaborates the first):

```lean
def forgetRationalDeRhamIso : (forgetComplex X).obj (rationalDeRhamComplex X) ≅ Ω•(X) := …
def forgetRationalHodgeFilteredIso (p : ℤ) :
    (forgetComplex X).obj (rationalHodgeFilteredComplex X p) ≅ F^p Ω•(X) := …
```

   and state `forget_rationalHodgeFilteredInclusion` with `(forgetComplex X).map`. If a proof breaks on the retyping, keep the site-spelled versions as `…Site` and derive these by `exact`.

4. **Recommended.** The equality that `cup-hodge-filtration` consumes (checked in T4 in the `forgetComplex` spelling, standard axioms):

```lean
/-- Upstream's `F^p H_dR^n(X)` is the image of the hypercohomology of the rational truncation
`F^p Ω•_ℚ`, forgotten and compared with `Ω•(X)`. -/
theorem hodgeFiltration_eq_range_rational (p n : ℤ) :
    hodgeFiltration X p n = (hypercohomologyMap X ((forgetComplex X).map
      (rationalHodgeFilteredInclusion X p) ≫ (forgetRationalDeRhamIso X).hom) n).range := by
  have h : hypercohomologyMap X ((forgetComplex X).map (rationalHodgeFilteredInclusion X p) ≫
      (forgetRationalDeRhamIso X).hom) n = hypercohomologyMap X
      ((forgetRationalHodgeFilteredIso X p).hom ≫ hodgeFilteredDeRhamInclusion X p) n :=
    congrArg (hypercohomologyMap X · n) (forget_rationalHodgeFilteredInclusion X p)
  refine Eq.trans ?_ (congrArg AddMonoidHom.range h).symm
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨hypercohomologyMap X (forgetRationalHodgeFilteredIso X p).inv n y, ?_⟩
    refine (hypercohomologyMap_comp_apply X (forgetRationalHodgeFilteredIso X p).inv
      ((forgetRationalHodgeFilteredIso X p).hom ≫ hodgeFilteredDeRhamInclusion X p) n y).symm.trans ?_
    exact congrArg (hypercohomologyMap X · n y) (Iso.inv_hom_id_assoc _ _)
  · rintro ⟨y, rfl⟩
    exact ⟨_, (hypercohomologyMap_comp_apply X _ _ n y).symm⟩
```

5. **Recommended.** Name and document the lower-bound instance:

```lean
/-- `Ω•_ℚ` is zero in negative degrees. -/
instance rationalDeRhamComplex_isStrictlyGE : (rationalDeRhamComplex X).IsStrictlyGE 0 := by
  unfold rationalDeRhamComplex
  infer_instance
```

   and replace `rdrForgetAdditive`, `rdrForgetAdditive'` by one local instance taking only `X`, before both sections.

6. **Recommended, on posting.** `docs/gaps.md` "To upstream": `holomorphicFormRatModule` and `holomorphicForm_isScalarTower` (instances on upstream's `HolomorphicForm`); the generic layer (`homFromSingleExtend` and its lemmas, `mapRestrictionIso`, `mapStupidTruncIso`, `mapStupidTruncIso_inclusion`) for Mathlib. Ledger: module `HodgeLadder.Hodge.RationalDeRhamComplex`, the declarations of changes 1 and 2 with `forgetRationalDeRhamIso`, `forget_rationalHodgeFilteredInclusion`, `forget_rationalConstantsToFormsSheaf`; import from `HodgeLadder.lean`.

7. **New rung (proposed, not blocking).** `de-rham-unit-nonzero`: `fieldToHolomorphicDeRhamComplexInt ℚ HodgeLadder.Tests.point ≠ 0`, with the corollary `rationalDeRhamUnit HodgeLadder.Tests.point ≠ 0` from change 1. Offer the first upstream as a sanity check of `fieldToHolomorphicDeRhamComplexInt`; its ingredient there is the private `holomorphicFormOfConstant_injective`.
