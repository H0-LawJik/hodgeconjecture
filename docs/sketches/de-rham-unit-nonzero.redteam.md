# Red team: `de-rham-unit-nonzero` (test)

Date: 2026-11-27. Worktree `de-rham-unit-nonzero` at base `16f29dc` (= `main`), uncommitted `HodgeLadder/Tests/DeRhamUnitNonzero.lean` and the section "de-rham-unit-nonzero: statement" of `docs/sketches/cup-hodge-filtration.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`.

Read: the ledger entry and `python3 tools/next.py de-rham-unit-nonzero`; the module; `docs/sketches/rational-de-rham-complex.redteam.md` (section 3, change 7, section 7b); `HodgeLadder/Hodge/RationalDeRhamComplex.lean` (`homFromSingleExtend`, `homFromSingleExtend_f_zero`, `single_map_comp_extendSingleIso_inv_comp`, `rationalDeRhamUnit`, `forget_rationalDeRhamUnit`); `HodgeLadder/Hodge/RationalHypercohomology.lean` (`forgetComplex`, `forgetUnitComplexIso`); `HodgeLadder/Tests/Witness.lean` (`point`); upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (`fieldToComplexConstantSheaf`, `constantFieldSheafComplexInt`, `fieldToComplexConstantSheafComplexInt`, `fieldToHolomorphicDeRhamComplexInt`), `Definitions/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean` (`constantsToHolomorphicDeRhamZero`, the private `holomorphicFormOfConstant_injective` and `constantsToHolomorphicDeRhamZero_stalk_mono`, `constantsToHolomorphicDeRhamZeroSheaf`, `constantsToHolomorphicDeRhamComplexInt`), `Definitions/AlgebraicGeometry/Hodge/AnalyticDifferentialForms.lean` (`holomorphicFormOfConstant`); Mathlib `Topology/Sheaves/Sheafify.lean` (`stalkFunctor_map_unit_toSheafify_isIso`); `docs/conventions.md`, `docs/references.md`, `docs/decisions/0011-general-lemmas-stay-local.md`.

Scratch (directory `scratch_rt/`, deleted afterwards; 5 to 11 s each with `lake env lean`, against the module's built olean):

| File | What it tried | Result |
|---|---|---|
| RT1 | `#print axioms` on the six declarations; `#check` of the two point statements; `simp`, `intro h; cases h`, `decide` on both point statements; `inferInstance` for `(forgetComplex X).PreservesZeroMorphisms` and `(forgetComplex X).Additive`; proof irrelevance of the first by `rfl` | standard axioms only; signatures as in the ledger title; every trivial proof fails (`simp` leaves `¬ … = 0`, `cases` fails on dependent elimination, no `Decidable` instance); both instance searches fail; any two proofs of the `Prop` class are `rfl`-equal |
| RT2 | non-torsion forms `n • (…) ≠ 0` for `n : ℕ`, `n ≠ 0`, of the degree-zero lemma and of upstream's unit, and the sign separations `fieldToHolomorphicDeRhamComplexInt ℚ X ≠ -fieldToHolomorphicDeRhamComplexInt ℚ X` and `rationalDeRhamUnit X ≠ -rationalDeRhamUnit X` | all four check, standard axioms only (code in change 4) |

`python3 tools/check.py --no-build` on the worktree: `ACCEPTED: all checks passed`. The module is not imported from `HodgeLadder.lean` and the ledger names no declarations yet, so the checker does not see it (change 1).

## 1. Is this the statement the literature makes?

The literature fact is that the holomorphic de Rham complex resolves the constant sheaf: `ℂ_X → 𝒪_X = Ω⁰_X`, `c ↦ c`, is injective, and on a nonempty `X` it is nonzero (`Voisin2002`, vol. I, holomorphic Poincaré lemma and the holomorphic de Rham resolution; section number not verified here). The rung is the weakest consequence that rules out a zero unit, stated against upstream's definitions. Field by field:

| Piece | Lean | Upstream definition | Literature |
|---|---|---|---|
| Source | `constantFieldSheafComplexInt ℚ X` | `single₀ 𝓒(X(ℂ); ℚ)`, extended to `ℤ` along `embeddingUpNat` | `ℚ_X[0]` |
| Target | `Ω•(X)` | `holomorphicDeRhamComplex X (dim X.left)` extended to `ℤ` | `Ω•_X` in degrees `≥ 0` |
| Map | `fieldToHolomorphicDeRhamComplexInt ℚ X` | `extendMap (single₀.map (fieldToComplexConstantSheaf ℚ X)) ≫ extendMap (constantsToHolomorphicDeRhamComplex X _)`; degree zero is `algebraMap ℚ ℂ`, then `holomorphicFormOfConstant` | `ℚ → ℂ → 𝒪`, constant to constant function, no scalar |
| Hom type | `constantFieldSheafComplexInt ℚ X ⟶ Ω•(X)` in `CochainComplex (AnalyticAdditiveSheaf X) ℤ` | the hom type of upstream's map, as stated upstream | morphism of complexes of sheaves |
| `0` | `HasZeroMorphisms` of `HomologicalComplex` | zero morphisms are unique in any category, so no other `0` is possible | the zero map |
| Space | `HodgeLadder.Tests.point = Over.mk (𝟙 (Spec ℂ))` | carries `IsIntegral point.left`, `Smooth point.hom` (rung `nonvacuity-tests`) | a point |

The statement at `point` is exactly the ledger title, both halves (RT1, `#check`). The general forms are stronger and correctly hypothesized:

- `[Nonempty (ComplexPoint X)]` is necessary. On an empty `X(ℂ)` every sheaf is zero (the only open is `∅`, whose sections are terminal), so every map between sheaves on it is `0` and the statement is false. It is carried as an instance argument in the three general lemmas and supplied at `point` by `⟨𝟙 _⟩`.
- `[IsIntegral X.left] [Smooth X.hom]` are the instance arguments of `fieldToHolomorphicDeRhamComplexInt` and `rationalDeRhamUnit` themselves; the proof uses neither beyond what the definitions need.
- `K` is any field with `[Algebra K ℂ]`. The proof only uses `algebraMap K ℂ 1 = 1`. Upstream's `fieldToHolomorphicDeRhamComplexInt` takes a field, so that is the hypothesis to carry.
- For `X` of finite type over `ℂ`, `IsIntegral X.left` (nonempty) and `Smooth X.hom` (locally of finite presentation) already force a complex point by the Nullstellensatz, so the `Nonempty` argument could be derived. That is a possible stronger form, not a defect (section 9, optional).

## 2. Can the hypotheses be satisfied?

Yes: `point`, with the instances of rung `nonvacuity-tests` and `Nonempty (ComplexPoint point)` from `⟨𝟙 _⟩` (RT1, `example : Nonempty (ComplexPoint point) := ⟨𝟙 _⟩` elaborates). The point statements are the instance.

## 3. Trivially true?

No. The conclusion is a `≠ 0` between morphisms of complexes of sheaves, with no decidability, no coercion and no empty index type. `simp`, `cases` and `decide` fail (RT1). The proof uses every hypothesis: `Nonempty (ComplexPoint X)` gives the point `x` at which the stalk is taken, and `Nonempty W` (from `x ∈ W`) feeds `holomorphicFormOfConstant_ne_zero`.

Does the test do its job? It fails if any of the following held:

- the target `Ω•(X)` were a zero object in degree zero, or `holomorphicDeRhamSheaf X d 0` were zero: then every map into it is `0`;
- the unit factored through `0` anywhere (the constant sheaf map, the sheafification of `constantsToHolomorphicDeRhamZero`, the `extendMap` of `fromSingle₀Equiv`): the proof reduces exactly to the degree-zero composite through `homFromSingleExtend_f_zero` and cancellation of `singleObjXSelf` and `extendXIso`, which are isomorphisms;
- `holomorphicFormOfConstant` were zero on sections (for example if `chartEvaluationKernel` were `⊤`): then upstream's `chartEvaluation_ofConstant` (chart evaluation of `[c]` is `c`) would be contradicted.

With `forget_rationalDeRhamUnit` it gives `rationalDeRhamUnit X ≠ 0`. That closes the gap of `rational-de-rham-complex`, section 7b: the unit lemma can no longer hold because both sides are `0`.

What it does not do: it does not separate the unit from its negative. Section 3 of the `rational-de-rham-complex` red team wrote that the unit lemma "separates the unit from its negative as soon as upstream's unit is nonzero". That step needs `2 • ι ≠ 0`, which a bare `ι ≠ 0` does not give in Lean (the hom groups are not known to be torsion-free there). RT2 proves the non-torsion form `n • fieldToHolomorphicDeRhamComplexInt K X ≠ 0` for `n ≠ 0` by the same proof with `f'` replaced by `n • f'` and `1` by `n` at the end, and from it `rationalDeRhamUnit X ≠ -rationalDeRhamUnit X`. With that, `forget_rationalDeRhamUnit` is false for `−rationalDeRhamUnit X` in place of the unit, which is the sign check the October 2026 withdrawals call for (change 4).

## 4. Interface rung?

No. A test: no structure, no axioms.

## 5. Checker and axioms

`#print axioms` (RT1), each `[propext, Classical.choice, Quot.sound]`:

| Declaration | Statement |
|---|---|
| `HodgeLadder.Tests.holomorphicFormOfConstant_ne_zero` | `holomorphicFormOfConstant X d U c ≠ 0` for `[Nonempty U.unop]`, `c ≠ 0` |
| `HodgeLadder.Tests.fieldToHolomorphicFormZeroSheaf_ne_zero` | `fieldToComplexConstantSheaf K X ≫ constantsToHolomorphicDeRhamZeroSheaf X d ≠ 0` |
| `HodgeLadder.Tests.fieldToHolomorphicDeRhamComplexInt_ne_zero` | `fieldToHolomorphicDeRhamComplexInt K X ≠ 0` |
| `HodgeLadder.Tests.fieldToHolomorphicDeRhamComplexInt_point_ne_zero` | `fieldToHolomorphicDeRhamComplexInt ℚ point ≠ 0` (ledger title, first half) |
| `HodgeLadder.Tests.rationalDeRhamUnit_ne_zero` | `rationalDeRhamUnit X ≠ 0` |
| `HodgeLadder.Tests.rationalDeRhamUnit_point_ne_zero` | `rationalDeRhamUnit point ≠ 0` (ledger title, second half) |

Each is the declaration the ledger means: the upstream names `fieldToHolomorphicDeRhamComplexInt`, `fieldToComplexConstantSheaf`, `constantsToHolomorphicDeRhamZeroSheaf`, `holomorphicFormOfConstant` are upstream's (namespace `AlgebraicGeometry.ComplexPoint`, opened, not shadowed), and `rationalDeRhamUnit`, `forget_rationalDeRhamUnit`, `forgetUnitComplexIso` are `main`'s. No `sorry`, `native_decide`, `axiom` or `unsafe` in the file.

**The stalk argument (question 2).** Sound. `sheafifyMap J f'` is `((presheafToSheaf J _).map f').hom` by `rfl`, and `TopCat.Sheaf.constantFunctor.map φ` unfolds to `(presheafToSheaf J _).map ((Functor.const _).map φ)` (the `exact hfg` step). Mathlib's `toSheafify_naturality` gives `f' ≫ toSheafify J Q = toSheafify J P ≫ sheafifyMap J f'`; `stalkFunctor_map_unit_toSheafify_isIso` is stated for any `C` with colimits, a terminal object and weak sheafification, used here at `AddCommGrpCat` with `Q` upstream's `holomorphicDeRhamPresheaf X d 0`, and cancelling the isomorphism on the right gives the stalk map of `f'` zero. `stalkFunctor_map_germ_apply` and `germ_eq` at `U = V = ⊤` produce `W ∋ x` with `[1]|_W = 0`; `holomorphicFormRestriction_ofConstant` turns that restriction into `[1]` on `W`. This is upstream's private `constantsToHolomorphicDeRhamZero_stalk_mono` argument specialized to one germ, plus the sheafification step.

**The reproved private lemma.** `holomorphicFormOfConstant_ne_zero` is upstream's `holomorphicFormOfConstant_injective` line for line with `c` in place of `c − c'`: the same `Algebra.DeRham.ofConstant` lift, `Submodule.Quotient.mk_eq_zero`, the point of `U` from `Classical.arbitrary`, `extChartAt` at that point, `mem_chartEvaluationKernel_iff`, `chartEvaluation_ofConstant`, and evaluation of the alternating map at `Fin.elim0`. For a linear map, injectivity and `c ≠ 0 → f c ≠ 0` are equivalent, so the copy is faithful. Upstream's lemma is `private`, so it cannot be used at the pin.

**The hand-supplied instance (question 3).** Harmless. `(forgetComplex X).PreservesZeroMorphisms` is a `Prop` class; RT1 shows instance search does not find it (nor `(forgetComplex X).Additive`), and any two proofs are `rfl`-equal. It is a local `have` inside the proof of `rationalDeRhamUnit_ne_zero`, after the statement is elaborated, so it changes no statement; the `0` it rewrites with is the unique zero morphism.

## 6. Conventions

| Convention | Used where | Checked against | Truth depends on it |
|---|---|---|---|
| `K → ℂ` | `algebraMap K ℂ` in `fieldToComplexConstantSheaf` | upstream source; row "Rational-to-de Rham map and the range of F^p" | no: `algebraMap K ℂ 1 = 1` for every algebra structure |
| Constants to 0-forms | `holomorphicFormOfConstant` (`ofConstant` modulo the chart-evaluation kernel), no `(2πi)^p`, no conjugation | upstream source, same row | no for `≠ 0` and `≠ −`: both are insensitive to sign and to nonzero scalars |
| ℕ to ℤ | `extendXIso`, `embeddingUpNat_f_zero` | row "Rational de Rham complex and its comparison" | no: identity components |
| Unit comparison | `forgetUnitComplexIso` | same row; `forget_rationalDeRhamUnit` is exact | the transfer to `rationalDeRhamUnit` uses only that it is an isomorphism |

No new convention. The rung's truth does not depend on any sign. I added to the "Status" column of the row "Rational de Rham complex and its comparison" the nonvacuity result and the sign separation of change 4.

## 7. Equality first

A test, not an identity. It is a step toward the identity `fieldToDeRhamCohomology_cup` (`de-rham-cup`, open): it certifies that the unit lemma `forget_rationalDeRhamUnit`, an exact identity, is about a nonzero map, and with change 4 that it distinguishes the unit from its negative.

## 7b. Non-vacuity

The rung is itself the non-vacuity test of `rational-de-rham-complex` (section 7b there). The smallest test that would fail if this rung held trivially is the degree-zero lemma `HodgeLadder.Tests.fieldToHolomorphicFormZeroSheaf_ne_zero`, which exists and to which the complex statement reduces.

**For `wedge-sheafify`, question 3** (`wedgeSheaf X d 0 0 ≠ 0`; the name does not exist yet). Route, not tried in Lean: if `wedgeSheaf X d 0 0` is the sheafification of the presheaf wedge `w : P_ℚ ⊗ P_ℚ ⟶ P_ℚ` at `(0, 0)` composed with the sheafification-of-tensor isomorphism, cancel the isomorphism and repeat `fieldToHolomorphicFormZeroSheaf_ne_zero` with `f' := w`, `C := ModuleCat ℚ` (Mathlib's stalk lemma holds there) and the germ of `[1] ⊗ [1]` on `⊤`, closing by the presheaf unit law `[1] ∧ [1] = [1]` of `wedge-presheaf` and `holomorphicFormOfConstant_ne_zero`. Cheaper still once `wedge-sheaf-map` has the sheaf-level unit law `(𝟙 ⊗ u) ≫ μ = ρ`: `μ = 0` would make the right unitor, an isomorphism, zero, so `Ω⁰_ℚ` would be a zero object, contradicting `rationalConstantsToFormsSheaf X d ≠ 0` (the degree-zero half of `rationalDeRhamUnit_ne_zero`).

## 8. Pin drift

None. Base `16f29dc` is `main`; `lakefile.toml` and `lake-manifest.json` are unchanged. Drift risk at a future bump: if upstream makes `holomorphicFormOfConstant_injective` or `constantsToHolomorphicDeRhamZero_stalk_mono` public, `holomorphicFormOfConstant_ne_zero` becomes a local copy of an upstream lemma and should be replaced by it (change 3).

## Findings

1. **The test does its job** (sections 1 and 3). It is the ledger title at `point`, both halves, and it fails if the target is zero, if the unit factors through zero, or if `holomorphicFormOfConstant` vanishes. It closes the vacuity gap of `rational-de-rham-complex`, section 7b. The general forms carry the necessary `Nonempty (ComplexPoint X)`.

2. **The stalk argument and the private-lemma copy are sound** (section 5). Mathlib's stalk isomorphism is used at the right presheaf; the copy is upstream's proof with `c` for `c − c'`.

3. **The instance is harmless** (section 5). `Prop`-valued, local to one proof, absent from instance search.

4. **The sign is not yet separated** (section 3). `≠ 0` alone does not exclude that the unit lemma also holds for `−rationalDeRhamUnit X`; the non-torsion form does, and it checks in scratch (RT2).

5. **Ledger and sketch wording conflict with decision 0011.** The ledger note says "to be offered upstream", and the sketch's paragraph **Upstream** says the lemmas "belong in `Paul-Lez/HodgeConjecture`" and should go to `docs/gaps.md` "To upstream". Decision 0011 replaced that table with "General lemmas kept local" and ended upstream contributions.

6. **Path.** `tools/next.py` derives `HodgeLadder/De/Rham/Unit/Nonzero.lean` from the id; the module sits under `HodgeLadder/Tests/` next to `Witness` and `CodimensionZero`, which is right for a test. The ledger's `module` field fixes the brief.

## Verdict

**pass with changes.**

## Changes

1. **Required, on posting.** Add `public import HodgeLadder.Tests.DeRhamUnitNonzero` to `HodgeLadder.lean`. Ledger entry: `status: "checked"`, `module: "HodgeLadder.Tests.DeRhamUnitNonzero"`, `declarations`: the six names of section 5 (plus the four of change 4 if adopted). Run `python3 tools/check.py` and confirm the axioms line for each.

2. **Required.** Ledger note: replace "a sanity check of an upstream definition, to be offered upstream" with "a sanity check of upstream definitions; the reproved half of upstream's private holomorphicFormOfConstant_injective is kept local (decision 0011)". In `docs/sketches/cup-hodge-filtration.md`, rewrite the paragraph **Upstream** to: "The test is a sanity check of upstream definitions (`fieldToHolomorphicDeRhamComplexInt`, `holomorphicFormOfConstant`). `holomorphicFormOfConstant_ne_zero` reproves half of upstream's `private` `holomorphicFormOfConstant_injective`; it is kept local (decision 0011) and listed in `docs/gaps.md` "General lemmas kept local"."

3. **Required.** `docs/gaps.md` "General lemmas kept local": one row, `HodgeLadder.Tests.holomorphicFormOfConstant_ne_zero` (and `fieldToHolomorphicFormZeroSheaf_ne_zero`), module `HodgeLadder.Tests.DeRhamUnitNonzero`, why local: "upstream's `holomorphicFormOfConstant_injective` and `constantsToHolomorphicDeRhamZero_stalk_mono` are `private` at the pin; a pin bump that makes either public should replace the local copy", opened 2026-11-27.

4. **Recommended.** Add the non-torsion forms and the sign separations (RT2, checked, standard axioms, about 10 s for the file). With `n = 1` they imply the existing `≠ 0` lemmas, so the prover may derive those as corollaries or keep both. The code, to go after the existing declarations:

```lean
/-- Non-torsion form of the degree-zero test: `n • (K_X ⟶ ℂ_X ⟶ Ω⁰) ≠ 0` for `n ≠ 0`. -/
theorem nsmul_fieldToHolomorphicFormZeroSheaf_ne_zero (K : Type) [Field K] [Algebra K ℂ]
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [Nonempty (ComplexPoint X)] {n : ℕ} (hn : n ≠ 0) :
    n • (fieldToComplexConstantSheaf K X ≫ constantsToHolomorphicDeRhamZeroSheaf X d) ≠ 0 := by
  intro hfg
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  let Q := holomorphicDeRhamPresheaf X d 0
  let f' : 𝓒ᵖ(↧(ComplexPoint X); K) ⟶ Q :=
    n • ((Functor.const _).map (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
      constantsToHolomorphicDeRhamZero X d)
  have hf' : sheafifyMap J f' = 0 := by
    have : (presheafToSheaf J AddCommGrpCat).map f' = 0 := by
      rw [Functor.map_nsmul, Functor.map_comp]
      exact hfg
    change ((presheafToSheaf J AddCommGrpCat).map f').hom = 0
    rw [this]
    rfl
  have hnat := toSheafify_naturality J f'
  rw [hf', comp_zero] at hnat
  let x : ComplexPoint X := Classical.arbitrary _
  have hst := congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map hnat
  rw [Functor.map_comp, Functor.map_zero] at hst
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat Q
  have hst' : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f' = 0 :=
    (cancel_mono _).1 (hst.trans zero_comp.symm)
  have hgerm := congrArg (fun φ => φ (TopCat.Presheaf.germ 𝓒ᵖ(↧(ComplexPoint X); K) ⊤ x (by simp)
    (1 : K))) hst'
  simp only at hgerm
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hgerm
  obtain ⟨W, hxW, iU, iV, hW⟩ := Q.germ_eq (U := ⊤) (V := ⊤) x (by simp) (by simp)
    (f'.app _ (1 : K)) 0 (hgerm.trans (map_zero _).symm)
  rw [map_zero] at hW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have key : (holomorphicFormOfConstant X d (.op W) (n : ℂ) : HolomorphicForm X d (.op W) 0) =
      holomorphicFormRestriction X d iU.op 0
        (n • holomorphicFormOfConstant X d (.op ⊤) (algebraMap K ℂ 1)) := by
    rw [map_nsmul, holomorphicFormRestriction_ofConstant, (algebraMap K ℂ).map_one,
      ← map_nsmul, nsmul_eq_mul, mul_one]
  exact holomorphicFormOfConstant_ne_zero X d (.op W) (c := (n : ℂ)) (by exact_mod_cast hn)
    (key.trans hW)

/-- Non-torsion form of upstream's unit. -/
theorem nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero (K : Type) [Field K] [Algebra K ℂ]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [Nonempty (ComplexPoint X)]
    {n : ℕ} (hn : n ≠ 0) :
    n • fieldToHolomorphicDeRhamComplexInt K X ≠ 0 := by
  intro h
  have hg : constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫
      (holomorphicDeRhamComplex X (dim X.left)).d 0 1 = 0 := by
    rw [holomorphicDeRhamComplex_d]
    exact constantsToHolomorphicDeRhamZeroSheaf_comp_differential X _
  have hR := single_map_comp_extendSingleIso_inv_comp (C := AnalyticAdditiveSheaf X)
    (𝟙 _) (fieldToComplexConstantSheaf K X) (L := holomorphicDeRhamComplex X (dim X.left))
    (constantsToHolomorphicDeRhamZeroSheaf X _) hg
  have hR' := (congrArg (fun φ : (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj 𝓒(↧(ComplexPoint X); K) ⟶
        (holomorphicDeRhamComplex X (dim X.left)).extend ComplexShape.embeddingUpNat =>
      (n • φ : _ ⟶ _)) hR).symm.trans (show _ = 0 by
    change n • (_ ≫ _ ≫ fieldToHolomorphicDeRhamComplexInt K X) = 0
    rw [← Preadditive.comp_nsmul, ← Preadditive.comp_nsmul, h, comp_zero, comp_zero])
  have h0 := congrArg (fun f : (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj 𝓒(↧(ComplexPoint X); K) ⟶
        (holomorphicDeRhamComplex X (dim X.left)).extend ComplexShape.embeddingUpNat =>
      f.f 0 ≫ ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
        ComplexShape.embeddingUpNat embeddingUpNat_f_zero).hom) hR'
  simp only [HomologicalComplex.nsmul_f_apply, Preadditive.nsmul_comp] at h0
  rw [homFromSingleExtend_f_zero, HomologicalComplex.zero_f, zero_comp, Category.id_comp,
    ← Preadditive.comp_nsmul] at h0
  have hfg : n • (fieldToComplexConstantSheaf K X ≫ constantsToHolomorphicDeRhamZeroSheaf X _) = 0 :=
    (cancel_epi _).1 (h0.trans comp_zero.symm)
  exact nsmul_fieldToHolomorphicFormZeroSheaf_ne_zero K X _ hn hfg

/-- **Sign separation.** Upstream's unit is not its own negative. -/
theorem fieldToHolomorphicDeRhamComplexInt_ne_neg (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [Nonempty (ComplexPoint X)] :
    fieldToHolomorphicDeRhamComplexInt ℚ X ≠ -fieldToHolomorphicDeRhamComplexInt ℚ X := by
  intro h
  apply nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero ℚ X (n := 2) two_ne_zero
  rw [two_nsmul]; nth_rw 2 [h]; exact add_neg_cancel _

/-- **Sign separation for the rational unit**: `forget_rationalDeRhamUnit` is false for
`−rationalDeRhamUnit X`. -/
theorem rationalDeRhamUnit_ne_neg (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [Nonempty (ComplexPoint X)] : rationalDeRhamUnit X ≠ -rationalDeRhamUnit X := by
  have : (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).Additive :=
    Cup.forgetSheaf_additive _
  have : (forgetComplex X).Additive := instAdditiveHomologicalComplexMapHomologicalComplex _ _
  intro hu
  have h := forget_rationalDeRhamUnit X
  have h' : (forgetComplex X).map (-rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom =
      (forgetUnitComplexIso X).hom ≫ (-fieldToHolomorphicDeRhamComplexInt ℚ X) := by
    rw [Functor.map_neg, Preadditive.neg_comp, h, Preadditive.comp_neg]
  rw [← hu, h] at h'
  exact fieldToHolomorphicDeRhamComplexInt_ne_neg X ((cancel_epi _).1 h')
```

   This is the text that checked in RT2 (with the file's `set_option` and `attribute [local implicit_reducible]` preamble), unchanged except for docstrings and one line break.

5. **Optional, new rung.** Drop `[Nonempty (ComplexPoint X)]` from the general forms by deriving it from `IsIntegral X.left` and `Smooth X.hom` (Nullstellensatz: a nonempty scheme locally of finite type over `ℂ` has a `ℂ`-point). Not needed for the ladder.

6. **Hygiene.** The sketch section says the module is "not yet imported from the root"; update it with change 1. Correct the sentence in `docs/sketches/rational-de-rham-complex.redteam.md` section 3 ("separates the unit from its negative as soon as upstream's unit is nonzero") by a pointer to change 4 here, since `≠ 0` alone does not give it in Lean.
