# Red team: `wedge-sheafify` (statement and proof)

Date: 2026-11-27. Worktree `wedge-sheafify` at base `16f29dc`, uncommitted `HodgeLadder/Hodge/WedgeSheafify.lean` (17 declarations) and the section "wedge-sheafify: statement" of `docs/sketches/cup-hodge-filtration.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`; `lakefile.toml` and `lake-manifest.json` are identical to `main`, and the package checkout is at `2ead713`.

Read: the ledger entries `wedge-sheafify`, `wedge-presheaf`, `rational-de-rham-complex`, `wedge-sheaf-map`, `de-rham-cup`, `de-rham-unit-nonzero`; the module; `HodgeLadder/Hodge/{WedgePresheaf,RationalDeRhamComplex,PairingProduct}.lean`, `HodgeLadder/Cup/{SheafTensor,SheafExact}.lean`; `docs/sketches/cup-hodge-filtration.redteam.md` (finding 9), `wedge-presheaf.redteam.md`, `rational-de-rham-complex.redteam.md` (section 3, findings 3 and 7, change 2), `pairing-product.redteam.md` (section 1, finding 4, change 5); `docs/conventions.md` rows "Wedge product of holomorphic forms", "Tensor product of ℤ-indexed cochain complexes and its shifts", "Pairing product (left action)", "de Rham cup order (proposed)", "Rational de Rham complex and its comparison"; Mathlib `CategoryTheory/Sites/Monoidal.lean` (`Sheaf.monoidalCategory`, the `Functor.Monoidal` instance of `presheafToSheaf`), `CategoryTheory/Localization/Monoidal/Basic.lean` (`μ`, the unitors), `CategoryTheory/Sites/Sheafification.lean` (`sheafify_hom_ext`, `sheafificationAdjunction_unit_app`); upstream `Definitions/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean` (`holomorphicDeRhamPresheaf`, `holomorphicDeRhamSheaf`).

Scratch (inside the worktree under `RTScratch/`, deleted afterwards; 5 to 9 s each with `lake env lean` after a 3 s `lake build` of the module): RT1 prints axioms; RT2 proves the prover's question 1 and tries trivial proofs and the instance agreement; RT3 derives the sheaf unit law in bidegree (0, q); RT4 derives the `ℂ`-scalar laws in both factors and a conditional sheaf-level nonvacuity; RT5 reproduces the instance finding; RT6 checks sums and signs through the reference map; RT7 instantiates the hypotheses on ℙ¹.

**Verdict: pass with changes.** The statement is the literature's sheafified wedge, pinned uniquely by a square stated against Mathlib's sheafification maps and tensorator, and it reaches upstream's sheaf of `(p + q)`-forms through the checked comparison pin, exactly, with no sign and no scalar. All 17 declarations use the three standard axioms. Every downstream need tested (Leibniz shape, unit law, scalar laws in both factors) is derivable from the posted statements in under 25 lines each (RT3, RT4, the prover's Leibniz probe). Changes 1 to 4 are bookkeeping required before posting; changes 5 to 8 are recommended.

## 1. Is this the statement the literature makes?

Source: the tensor product of sheaves of modules is the sheafification of the presheaf tensor product, and a morphism out of it is determined by its values on local sections `a ⊗ b` ([`Bredon1997`] I, [`Iversen1986`] II, [`Stacks`], tensor product of sheaves of modules; sections and tags unverified). The wedge of holomorphic forms `Ω^p ⊗ Ω^q → Ω^{p+q}` is the sheaf map that sends `a ⊗ b` to `a ∧ b` on local sections ([`Voisin2002`] I, holomorphic forms; [`GriffithsHarris1978`] Ch. 0; section numbers unverified).

| Literature | Lean | Check |
|---|---|---|
| `Ω^p` as a sheaf of `ℚ`-vector spaces | `rationalHolomorphicFormSheaf X d p`, the sheafification of `rationalHolomorphicFormPresheaf X d p` (upstream's `HolomorphicForm X d U p` with `q • θ = (q : ℂ) • θ`) | checked rung `rational-de-rham-complex`; the unique `ℚ`-structure (`holomorphicFormRatModule_unique`) |
| `F ⊗ G := (F ⊗_pre G)^+` | Mathlib's `Sheaf.monoidalCategory`, the localized monoidal structure for `presheafToSheaf` with `ε = Iso.refl` | the same object up to Mathlib's tensorator `μ`; `F ⊗ G` is a lifted object (`Localization.lift₂`), so the only handle on its sections is `μ`/`δ` |
| local section `a ⊗ b` of `Ω^p ⊗ Ω^q` | `toSheafifyTensor P_p P_q (a ⊗ₜ b) = δ (η_{P⊗Q} (a ⊗ₜ b))` | equals `(η a ⊗ η b)` followed by the canonical map (finding 1, RT2) |
| `a ⊗ b ↦ a ∧ b` | `toSheafifyTensor_comp_wedgeSheaf`, `_apply`: `wedgeSheaf (δ η (a ⊗ b)) = η (a ∧ b)` | exact; `a ∧ b` is `holomorphicWedge X d U p q a b`, first factor on the left |
| uniqueness | `eq_wedgeSheaf_iff`, from `toSheafifyTensor_hom_ext` | proved (finding 1) |
| the wedge on `Ω^•` of upstream | `forget_wedgeSheaf`, `_apply`: after forgetting `ℚ` and the comparison `e_{p+q}`, `η^{upstream}_{p+q} (a ∧ b)` in `holomorphicDeRhamSheaf X d (p + q)` | exact; upstream's sheaf is `(presheafToSheaf J AddCommGrpCat).obj (holomorphicDeRhamPresheaf X d p)`, so the right side is upstream's own sheafification map |

Field by field, every object is upstream's or a checked local one: `X : Over (Spec ↧ℂ)`, `d`, `[SmoothOfRelativeDimension d X.hom]`, opens of `TopCat.of (ComplexPoint X)`, `HolomorphicForm`, `holomorphicDeRhamPresheaf`, `holomorphicDeRhamSheaf`; the local ones are `holomorphicWedge` (`wedge-presheaf`), `rationalHolomorphicFormPresheaf`, `rationalHolomorphicFormSheaf`, `forgetRationalHolomorphicFormSheafIso` (`rational-de-rham-complex`). Nothing upstream states is restated.

## 2. Can the hypotheses be satisfied?

Yes; they are upstream's. RT7, standard axioms, importing `HodgeLadder.Tests.ProjectivePlane` (the instance `smoothOfRelativeDimension_projectiveSpace`) and `HodgeLadder.Tests.ProjectiveChart`:

```lean
open HodgeLadder.Tests HodgeLadder.Normalization in
example : ∃ U : (Opens (TopCat.of (ComplexPoint (projectiveSpace 1))))ᵒᵖ,
    (rationalWedgePresheaf (projectiveSpace 1) 1 0 0).app U ≠ 0 := by
  refine ⟨Opposite.op ⊤, ?_⟩
  have : Nonempty (Opposite.unop
      (Opposite.op (⊤ : Opens (TopCat.of (ComplexPoint (projectiveSpace 1)))))) :=
    ⟨⟨(projectiveChart 1 0).symm 0, trivial⟩⟩
  exact rationalWedgePresheaf_app_ne_zero _ _ _
```

## 3. Is any conclusion trivially true?

No. RT2: `rfl` fails on `toSheafifyTensor_comp_wedgeSheaf` (not definitionally equal); `simp [toSheafifyTensor, wedgeSheaf]` leaves `toSheafify (P_p ⊗ P_q) ≫ δ ≫ …` open; with `0` in place of `wedgeSheaf` the square is left open by `simp`, and it is false whenever sheafification keeps `[1]` (finding 5). The prover's reports (`rfl` fails on `forget_wedgeSheaf`) agree. The defining square has one free morphism and `eq_wedgeSheaf_iff` shows it determines it, so the square is not satisfied by an arbitrary map. No definition unfolds to `True`, no index type is empty, no `ℕ∞` enters, and the only hypothesis beyond upstream's, `[Nonempty U.unop]` in `rationalWedgePresheaf_app_ne_zero`, is used. `rationalWedgePresheaf_app_tmul` is `rfl`; it is the intended computation rule of `TensorProduct.lift`.

## 4. Interface rung?

No. Definitions and theorems; no structure, no assumed `Prop`.

## 5. Axioms and declarations

RT1, `#print axioms` on all 17 (`toSheafifyTensor`, `toSheafifyTensor_comp_μ`, `toSheafifyTensor_comp_map`, `toSheafifyTensor_hom_ext`, `toSheafifyTensor_naturality_left`, `toSheafifyTensor_naturality_right`, `analyticShQMonoidal`, `rationalWedgeBilin`, `rationalWedgePresheaf`, `rationalWedgePresheaf_app_tmul`, `wedgeSheaf`, `toSheafifyTensor_comp_wedgeSheaf`, `eq_wedgeSheaf_iff`, `toSheafifyTensor_comp_wedgeSheaf_apply`, `forget_wedgeSheaf`, `forget_wedgeSheaf_apply`, `rationalWedgePresheaf_app_ne_zero`): each depends on `[propext, Classical.choice, Quot.sound]` and nothing else. No `sorry`, `axiom`, `native_decide`, `unsafe`, `set_option` or `maxHeartbeats` in the file. `python3 tools/check.py --no-build` on the worktree: `ACCEPTED: all checks passed`; it does not cover this module yet, which is not imported from `HodgeLadder.lean` and has no ledger declarations (change 1). The names used from other rungs are the checked declarations themselves: `forget_wedgeSheaf` cites `toSheafify_comp_forgetRationalHolomorphicFormSheafIso` and names `forgetRationalHolomorphicFormSheafIso`, both listed in the `rational-de-rham-complex` ledger entry; the nonvacuity lemma cites `holomorphicWedge_ofConstant_one_ne_zero` of `wedge-presheaf`.

## 6. Conventions

| Convention | Where | Register | Truth depends on it? |
|---|---|---|---|
| factor order `a ∧ b`, first factor of `Ω^p ⊗ Ω^q` on the left | `rationalWedgeBilin`, `rationalWedgePresheaf` | row "Wedge product of holomorphic forms" | yes for every form-level reading; see finding 3 for why the order is forced |
| `ℚ`-structure `q • θ = (q : ℂ) • θ` | `holomorphicFormRatModule` | row "Rational de Rham complex and its comparison" | no: unique (`subsingleton_rat_module`); `restrictScalars₁₂` and `TensorProduct.lift` change no value |
| sections of `F ⊗ G` read through `δ = μ⁻¹` of `presheafToSheaf`; `ε = 𝟙` by `rfl` (Mathlib's `Iso.refl` in `Sheaf.monoidalCategory`) | `toSheafifyTensor`, `wedgeSheaf` | missing; added as row "Sheafified wedge and the sheaf tensor" | the scale of `wedgeSheaf` relative to Mathlib's unitors; a change of `ε` or of the definition of `Sheaf.monoidalCategory` at a Mathlib bump would break the unit law derivation (RT3 uses `ε = 𝟙` by `rfl`) |
| comparison `e_{p+q} = (sheafComposeNatIso.app P_ℚ).symm` | `forgetRationalHolomorphicFormSheafIso` | row "Rational de Rham complex and its comparison" | yes for `forget_wedgeSheaf`; pinned by `toSheafify_comp_forgetRationalHolomorphicFormSheafIso`, which this rung cites |

Borrowed results: Mathlib's `Functor.Monoidal.δ_μ_map`, `δ_natural_left`, `δ_natural_right`, `toSheafify_naturality`, `sheafify_hom_ext`, `cancel_epi`, `Functor.map_injective`; each is an identity or a uniqueness statement with no scalar, stated against the same `presheafToSheaf` and `Sheaf.monoidalCategory` the module uses (the local instance `Cup.sheafMonoidal` is `Sheaf.monoidalCategory (J Y) (ModuleCat ℚ)`, and `analyticShQMonoidal X` agrees with it by `with_reducible rfl`, RT2).

## 7. Equality first

Every statement is an exact equality or an `↔` of equalities; no scalar anywhere. The rung is a step toward `fieldToDeRhamCohomology_cup` (`de-rham-cup`, open), through `wedge-sheaf-map` (open).

## 7b. Non-vacuity

The smallest test that fails for a trivial statement: `rationalWedgePresheaf_app_ne_zero` (in the module) for the presheaf wedge. At the sheaf level, RT4 checks

```lean
theorem rt_wedgeSheaf_ne_zero (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (h : ((toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
      (rationalHolomorphicFormPresheaf X d 0)).app U).hom (holomorphicFormOfConstant X d U 1) ≠ 0) :
    wedgeSheaf X d 0 0 ≠ 0
```

from `toSheafifyTensor_comp_wedgeSheaf_apply` and `holomorphicWedge_ofConstant_left` (five lines). The hypothesis is that `[1]` survives sheafification, which is the content of the open test `de-rham-unit-nonzero` at degree zero (finding 5).

## 8. Pin drift

None. `wedge-presheaf` and `rational-de-rham-complex` were checked at `2ead713`, the current pin, and the worktree's `lakefile.toml` and `lake-manifest.json` match `main`. For a future Mathlib bump: `Functor.LaxMonoidal.ε (presheafToSheaf J A) = 𝟙 _` and `𝟙_ (Sheaf J A) = (presheafToSheaf J A).obj (𝟙_ _)` hold by `rfl` at the pin (RT2) because `Sheaf.monoidalCategory` uses `Iso.refl`; the unit law (change 5) depends on both, and `QX Y = (sheafifyQ Y).obj (𝟙_ (PreQ Y))` holds by `rfl` at default transparency only (it fails `with_reducible_and_instances rfl`).

## Findings

1. **The square pins `wedgeSheaf`, and `toSheafifyTensor_hom_ext` is proved.** The proof cancels `δ` (an isomorphism, since `presheafToSheaf` is `Monoidal`), uses faithfulness of `sheafToPresheaf` (`map_injective`), then Mathlib's `sheafify_hom_ext` with the target a sheaf. That is the sense needed: every consumer equation is between maps out of `Ω^p_ℚ ⊗ Ω^q_ℚ` (or `ℚ_X ⊗ Ω^q_ℚ`, which is `sheafifyQ (𝟙_) ⊗ sheafifyQ P_q` by `rfl`) into a sheaf. **Prover's question 1: yes, and it does not matter for uniqueness.** RT2 proves, standard axioms, with `canon F G := toSheafifyTensor F.val G.val ≫ (ε_F ⊗ ε_G)` (ε the counit `sheafifyIso`):

   ```lean
   theorem q1 (P Q : Cup.PreQ Y) :
       toSheafifyTensor P Q = (toSheafify (Cup.J Y) P ⊗ₘ toSheafify (Cup.J Y) Q) ≫ canon _ _
   ```

   from `toSheafifyTensor_naturality_left`, `_right` and the left triangle identity of `sheafificationAdjunction` (15 lines). Mathlib has no other canonical map `F.val ⊗ G.val ⟶ (F ⊗ G).val`: `F ⊗ G` is a lifted object (`Localization.lift₂`), so `canon` is built from `δ` itself and the identity is a coherence check, not an independent pin. It matters only for evaluating `wedgeSheaf` on `s ⊗ t` with `s`, `t` sections of the sheaves that do not come from the presheaves; no planned rung does.

2. **`forget_wedgeSheaf` reaches upstream's sheaf exactly, through the pin and not a copy.** The right side is upstream's `toSheafify J (holomorphicDeRhamPresheaf X d (p + q))`, whose target is the underlying presheaf of upstream's `holomorphicDeRhamSheaf X d (p + q)` by definition; the proof applies the checked `toSheafify_comp_forgetRationalHolomorphicFormSheafIso` to the defining square. No automorphism can enter. A twist `σ` of the target with `wedgeSheaf ≫ σ` satisfying the square forces `wedgeSheaf ≫ σ = wedgeSheaf` (`eq_wedgeSheaf_iff`); a twist of `e_{p+q}` is excluded by the pin. A twist of `μ` would be a different monoidal structure: `μ` is Mathlib's (`Localization.Monoidal.μ`), and the unitors and associator of `Sheaf.monoidalCategory` are defined from the same `μ` (`λ_{LX} = ε⁻¹ ▷ _ ≫ μ ≫ L λ_X`), so every consumer that uses `Sheaf.monoidalCategory` works in one coherent structure; the unit law (RT3) fixes the scale of `wedgeSheaf` against its `λ`. "Upstream's wedge" is a slight misnomer in the prompt: upstream has no wedge; the right side is the checked local `holomorphicWedge` on upstream's forms.

3. **Factor order is consistent, and forced.** `wedgeSheaf p q` on `Ω^p ⊗ Ω^q` is `a ∧ b` with `a` from the left factor (row "Wedge product of holomorphic forms"). Mathlib's complex tensor gives `d(x ⊗ y) = dx ⊗ y + (−1)^p x ⊗ dy` (row "Tensor product of ℤ-indexed cochain complexes"), and the checked Leibniz rule is `d(a ∧ b) = cast(da ∧ b) + (−1)^p a ∧ db` with `p` the degree of the first factor; so `a ⊗ b ↦ a ∧ b` is a chain map with no twist, and `a ⊗ b ↦ b ∧ a` would need `(−1)^{pq}`. With `deRhamCup x y := pairProduct μ y x`, slot `x` of `pairProduct` (the left tensor factor) receives `y`, giving heuristically `deRhamCup [θ] [η] = [η ∧ θ]`, as the row "de Rham cup order (proposed)" records. The identity `ι (α ∪ β) = deRhamCup (ι α) (ι β)` uses only the unit law and naturality, so it is exact for this `μ` whatever the form-level reading.

4. **It is enough for `wedge-sheaf-map` and `de-rham-cup`; the unit and scalar laws are derivable.** (a) Leibniz: the prover's probe closes one term (`(d ▷ Ω^q) ≫ wedgeSheaf (p + 1) q`) in five steps; RT6 checks that sums and `ℤˣ`-signs pass through `toSheafifyTensor ≫ (presheafQ).map _` (`Functor.map_add`, `Functor.map_zsmul`, `Preadditive.comp_zsmul`), and RT3 proves the sheaf-to-presheaf transport of the degree casts (`toSheafify ≫ eqToHom = eqToHom ≫ toSheafify`, by `subst`). (b) Unit law, RT3, standard axioms:

   ```lean
   theorem rt_toSheafifyTensor_leftUnitor {Y : TopCat.{0}} (Q : Cup.PreQ Y) :
       toSheafifyTensor (𝟙_ (Cup.PreQ Y)) Q ≫
           (Cup.presheafQ Y).map (λ_ ((Cup.sheafifyQ Y).obj Q)).hom =
         (λ_ Q).hom ≫ toSheafify (Cup.J Y) Q := by
     have hε : Functor.LaxMonoidal.ε (Cup.sheafifyQ Y) = 𝟙 _ := rfl
     rw [Functor.LaxMonoidal.left_unitality, hε, id_whiskerRight, Category.id_comp]
     exact toSheafifyTensor_comp_map _ _ _ (λ_ Q).hom

   theorem rt_sheaf_unit (q : ℕ) :
       (rationalConstantsToFormsSheaf X d ▷ rationalHolomorphicFormSheaf X d q) ≫
           wedgeSheaf X d 0 q ≫
             eqToHom (congrArg (rationalHolomorphicFormSheaf X d) (Nat.zero_add q)) =
         (λ_ (rationalHolomorphicFormSheaf X d q)).hom
   ```

   the second in about 20 lines (`toSheafifyTensor_hom_ext` at `P = 𝟙_`, `toSheafifyTensor_naturality_left`, the square, the cast transport, and a presheaf unit law from `holomorphicWedge_ofConstant_left`, `holomorphicFormCast_trans`). This is the degree-(0, q) component of the complex unit law that the `pairing-product` red team (change 5) asks `wedge-sheaf-map` to state. (c) Scalars, RT4, standard axioms: with `S_c := sheafifyQ.map (c • ·)` on `P_p`, `(S_c ▷ Ω^q_ℚ) ≫ wedgeSheaf = wedgeSheaf ≫ S_c` and `(Ω^p_ℚ ◁ S_c) ≫ wedgeSheaf = wedgeSheaf ≫ S_c`, 15 lines each, from `map_smul` of `holomorphicWedge` in each argument. Neither law needs a new primitive here, but the scalar endomorphism `S_c` is not yet defined anywhere, and its identification with upstream's `scalarHolomorphicDeRhamComplexInt X c` through `forgetRationalDeRhamIso` is still owed (pairing-product red team, section 4). Change 5 places the unit law; change 6 records the rest.

5. **Nonvacuity (prover's question 3): presheaf level is enough for this rung.** The square is exact and determines `wedgeSheaf`, so the sheaf wedge is zero only if sheafification kills `[1] ∧ [1] = [1]`, that is, only if `Ω⁰_ℚ` loses its unit section. RT4 makes this precise (section 7b). With the unit law of change 5, `wedgeSheaf X d 0 q` is a split epimorphism up to the cast (`(u₀ ▷ Ω^q_ℚ) ≫ wedgeSheaf 0 q ≫ cast = λ`, an isomorphism), so `wedgeSheaf X d 0 q = 0` forces `Ω^q_ℚ` to be zero; nonvacuity of the sheaf wedge reduces to nonvacuity of `Ω_ℚ`, which belongs to `de-rham-unit-nonzero` (open). A corollary there, `wedgeSheaf point 0 0 ≠ 0`, is cheap once that rung's `rationalDeRhamUnit point ≠ 0` is checked: a nonzero `sheafifyQ.map c` gives some `U`, `r` with `η [r] ≠ 0`, hence `η [1] ≠ 0` by `ℚ`-linearity.

6. **Instances (prover's question 2).** RT5 reproduces the finding: with only `Cup.sheafMonoidal` as local instance, `#synth MonoidalCategoryStruct (Cup.ShQ (TopCat.of (ComplexPoint X)))` fails; with `analyticShQMonoidal` it succeeds, and the two structures agree by `with_reducible rfl`, so a consumer mixing `pairProductShQ` (elaborated with `Cup.sheafMonoidal` at a variable `Y`) with `wedgeSheaf` unifies. Do not move the abbrev to `HodgeLadder.Cup.SheafTensor`: that file is generic over `Y : TopCat` and imports no upstream module, and the abbrev needs `ComplexPoint`. Keep it here (every consumer of the wedge imports this module) or, at a later edit of `RationalDeRhamComplex.lean`, move it there next to the other concrete-space instances. The discrimination-tree cause should be recorded in `docs/gaps.md` (change 7); rechecking the `rational-de-rham-complex` misses against it is worthwhile but not blocking.

7. **Ledger path.** The ledger entry has `"module": null`; `tools/next.py` derives `HodgeLadder/Wedge/Sheafify.lean` from the rung id when `module` is null. No file in the repository names that path, so the sketch sentence "The ledger entry names `HodgeLadder/Wedge/Sheafify.lean`" is inaccurate. The module sits correctly next to `WedgePresheaf` and `RationalDeRhamComplex`; set `module` on posting (change 1).

8. **Generic lemmas are general (decision 0011).** `toSheafifyTensor` and its five lemmas hold for any `Y : TopCat` and are written locally; Mathlib at the pin has no equivalent (grep of `Sites/Monoidal.lean` and `Localization/Monoidal/` for `toSheafify`: none). They need a row in `docs/gaps.md` "General lemmas kept local" (change 2).

## Recommended changes

Required before posting:

1. `HodgeLadder.lean`: add `public import HodgeLadder.Hodge.WedgeSheafify`. Ledger `wedge-sheafify`: `status: checked`, `module: "HodgeLadder.Hodge.WedgeSheafify"`, the 17 declarations of section 5, contributors, and a note naming this file and the verdict.
2. `docs/gaps.md`, "General lemmas kept local": one row for `HodgeLadder.toSheafifyTensor`, `toSheafifyTensor_comp_μ`, `toSheafifyTensor_comp_map`, `toSheafifyTensor_hom_ext`, `toSheafifyTensor_naturality_left`, `toSheafifyTensor_naturality_right` (module `HodgeLadder.Hodge.WedgeSheafify`; general facts about the monoidal sheafification functor on any `TopCat`; candidates next to Mathlib's `Sites/Monoidal.lean`).
3. `docs/sketches/cup-hodge-filtration.md`, section "wedge-sheafify: statement": replace "The ledger entry names `HodgeLadder/Wedge/Sheafify.lean`" by "`tools/next.py` derives `HodgeLadder/Wedge/Sheafify.lean` from the rung id, since the ledger has `module: null`" (finding 7), and add a pointer to this file.
4. `docs/conventions.md`: the row "Sheafified wedge and the sheaf tensor" (added by this red team) stays with the rung.

Recommended:

5. **State the unit law here**, in the module, as the scale pin of `wedgeSheaf`: the generic `toSheafifyTensor_leftUnitor` (text of `rt_toSheafifyTensor_leftUnitor`, finding 4) with an explicit pin `Functor.LaxMonoidal.ε (Cup.sheafifyQ Y) = 𝟙 _ := rfl` named so a Mathlib bump breaks loudly, and `wedgeSheaf_unit_left` (text of `rt_sheaf_unit`), with the presheaf lemma and the cast transport as helpers. Checked in RT3 in under 9 s for the file. If it lands in `wedge-sheaf-map` instead, copy this statement into that rung's ledger note.
6. Ledger notes. `wedge-sheaf-map`: "Chain-map check through `toSheafifyTensor_hom_ext`, `toSheafifyTensor_naturality_left`/`_right`, the square `toSheafifyTensor_comp_wedgeSheaf` and `holomorphicFormDifferential_holomorphicWedge` (rung `wedge-presheaf`), the casts by `subst`; unit law from `wedgeSheaf_unit_left` (or change 5's text)". `de-rham-cup`: the scalar endomorphism `S_c := sheafifyQ.map (c • ·)` of `Ω^p_ℚ` must be defined and identified with upstream's `scalarHolomorphicDeRhamComplexInt X c` through `forgetRationalDeRhamIso`; the scalar laws in both factors then follow as in RT4 (finding 4c).
7. `docs/gaps.md`, "Known weaknesses": instance search misses `Cup.sheafMonoidal` at `TopCat.of (ComplexPoint X)` (key contains `Opens _.1`; the concrete goal reduces `TopCat.of` and `ComplexPoint` at reducible transparency); workaround `analyticShQMonoidal X` as a local instance; the same cause plausibly explains the `Cup.preservesSheafification_U` and `Cup.forgetSheaf_additive` misses of `rational-de-rham-complex` (not rechecked).
8. `de-rham-unit-nonzero`: add the corollary `wedgeSheaf HodgeLadder.Tests.point 0 0 ≠ 0` to its title or note (finding 5).

## Not done

Lean and ledger files are not edited (instructions). The full Leibniz identity at the sheaf level was not proved in scratch; the prover's one-term probe, RT3's cast transport and RT6's sum and sign check cover its parts. The sheaf-level `canon` identity of finding 1 is not proposed for the module.
