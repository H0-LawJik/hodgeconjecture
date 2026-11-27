# Red team: `derived-tensor-bounded`

Date: 2026-11-27. Worktree `derived-tensor-bounded` at base `146af90`, uncommitted `HodgeLadder/Hodge/DerivedTensorBounded.lean` (not yet imported from `HodgeLadder.lean`) and the section "derived-tensor-bounded: statement" of `docs/sketches/cup-hodge-filtration.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`; `lakefile.toml` and `lake-manifest.json` are byte-identical to `main`. Statement and proof reviewed together (phase 1 finished with no open goals).

**Verdict: pass with changes.** The construction is the derived tensor functor the route needs, at the strength `pairing-product` uses; no sign enters; `_unique` is the right universal property. The changes are bookkeeping, two cheap `rfl` pins against Mathlib's `Functor.map₂CochainComplex`, and a generic unit iso that `pairing-product` needs. The kernel cost is a Mathlib-level property of `HomologicalComplex.tensorHom` at `ShQ Y`; this file cannot remove it, and the generic layer already contains it.

## 1. Is this the statement the literature makes?

The literature object is the derived tensor product `− ⊗^L B` on `D(X, ℚ)` [`Stacks`, chapter "Cohomology of Sheaves", section on the derived tensor product, tag unverified; `Huybrechts2006` ch. 2–3, section numbers unverified]. Over a field every sheaf of vector spaces is flat and every complex is K-flat stalkwise, so `− ⊗^L B` is computed by `− ⊗ B` on any representative, and the derived functor of a functor that inverts quasi-isomorphisms is its lift through `Q`. Field by field:

| Field | Literature | Lean | Match |
|---|---|---|---|
| Source and target | `D(Sh(Y, ℚ))` | `DerivedCategory (ShQ Y)`, `ShQ Y = Sheaf (J Y) (ModuleCat ℚ)`, any `[HasDerivedCategory (ShQ Y)]` (universe-polymorphic, `#check @derivedTensorRight`) | yes |
| Tensor of sheaves | sheafification of the presheaf tensor | `sheafMonoidal` (Mathlib `Sheaf.monoidalCategory`), the instance of `tensor-bounded-quasi-iso` and of the wedge rungs | yes |
| Tensor of complexes | total complex, `d = d ⊗ 1 + (−1)^p 1 ⊗ d` | `HomologicalComplex.tensorObj K B` (pinned by `tensorRightComplex_obj`, `rfl`), `ε₂(p, q) = (−1)^p` | yes |
| Variable order | `K ↦ K ⊗^L B`, `B` second | `mapBifunctor K B (curriedTensor _)`, `B` second | yes; matches `pairProduct m x y = y ≫ (x ⊗ B)⟦b⟧` |
| Second argument | any complex | strictly bounded `B` (`IsStrictlyGE a`, `IsStrictlyLE b`) | weaker, sufficient: `Ω•_ℚ`, `F^p Ω•_ℚ`, `ℚ_X[0]` are strictly bounded |
| Factorization | `Q(K) ⊗^L B ≅ Q(K ⊗ B)` | `derivedTensorRightFacIso : Q ⋙ T_B ≅ tensorRightComplex Y B ⋙ Q`, `Localization.fac` | yes |
| Functoriality in `B` | bifunctor on `D × D` | chain maps `φ : B ⟶ B'` only (`derivedTensorRightMap`, `_id`, `_comp`) | weaker; every map `pairing-product` and `de-rham-cup` feed in (`F^p → Ω•`, `μ`, `u`, scalar endomorphisms `c • 𝟙`) is a chain map |
| Additivity | `⊗^L B` additive (exact, triangulated) | `derivedTensorRight_additive` (instance); no triangulated or `CommShift` structure | sufficient, see 4 |

`tensorRightComplex` is a sound stand-in for `tensorRight B`: Mathlib's `MonoidalCategory (CochainComplex (ShQ Y) ℤ)` asks for `HasGoodTensor₁₂`, `HasGoodTensor₂₃` and `HasTensor₄ObjExt` on all tuples of graded objects, instances this repository does not have for `ShQ Y`, and the functor here is pinned to `tensorObj`, `tensorHom f (𝟙 B)`, `tensorHom (𝟙 K) φ` by `rfl`. It also agrees with Mathlib's own bifunctor on complexes (finding 2).

## 2. Can the hypotheses be satisfied?

Yes. Checked in scratch (then deleted):

```lean
attribute [local instance] sheafMonoidal HasDerivedCategory.standard
noncomputable example (Y : TopCat.{0}) (X : ShQ Y) :
    DerivedCategory (ShQ Y) ⥤ DerivedCategory (ShQ Y) :=
  derivedTensorRight Y ((HomologicalComplex.single (ShQ Y) (.up ℤ) 0).obj X) 0 0
```

The only non-instance hypothesis of the generic layer, `hB`, is discharged on sheaves by the checked `tensorBoundedQuasiIso_holds` (`tensorRightComplex_isInvertedBy`).

## 3. Is the conclusion trivially true?

Everything here is data plus equations about it, so "trivially true" means a degenerate functor or an equation that holds for a reason unrelated to the construction.

- `T_B` is `Localization.lift`, and the instance `derivedMapBifunctorRight_lifting` makes it a `Localization.Lifting`; with `tensorRightComplex_obj` (`rfl` to `tensorObj K B`) this determines `T_B` up to unique isomorphism. It is not a zero or identity functor in disguise.
- `rfl`, `simp` and `ext; rfl` all fail on the generic `derivedMapBifunctorRightMap_id` (scratch, 5 s); the prover reports the same for `_app` and for removing the additivity instance.
- `derivedTensorRight_bounds` is `rfl` by design: the bounds enter only through the proof `hB`. Stated and documented; harmless.
- No unused hypotheses: the bounds feed `hB`; `[F.Additive]` gives `mapBifunctorRight_additive`; `[∀ X, (F.obj X).Additive]` gives the zero-morphism instances `mapBifunctor` needs.

## 4. Interface rung?

No. There is no structure with axioms (decision 0003). The one `Prop` input, `hB`, is a theorem on sheaves.

**`CommShift` is unnecessary; confirmed.** Write `pairProduct m x y = y ≫ (e(x))⟦b⟧ ≫ (shiftFunctorAdd' …).inv.app _`, where `e(x) : Q B ⟶ (Q C)⟦a⟧` is

`Q B ≅ Q (ℚ ⊗ B)` (λ⁻¹) `≅ T_B (Q ℚ)` (`facIso.inv`) `⟶ T_B ((Q A)⟦a⟧)` (`T_B.map x`) `≅ T_B (Q (A⟦a⟧))` (`T_B.mapIso ((Q.commShiftIso a).app A).symm`) `≅ Q (A⟦a⟧ ⊗ B)` (`facIso`) `≅ Q ((A ⊗ B)⟦a⟧)` (`Q.mapIso (mapBifunctorShift₁Iso …)`, no sign) `⟶ Q (C⟦a⟧)` (`Q.map (m⟦a⟧')`) `≅ (Q C)⟦a⟧` (`Q.commShiftIso`).

`T_B` is only ever applied to `x` and to the isomorphism `(Q.commShiftIso a).app A`, and its value is read off through `facIso`. No component of `T_B.commShiftIso` appears. Biadditivity in `x` uses `T_B.Additive` and additivity of `⟦b⟧`; in `y`, bilinearity of composition. Naturality in `A` along chain maps uses naturality of `facIso`, of `Q.commShiftIso` and of `mapBifunctorShift₁Iso` in its first argument (the last is not stated in Mathlib; it belongs to `pairing-product`). Naturality in `B` uses `derivedTensorRightMap` and `_app`. ℂ-linearity in `de-rham-cup` goes through naturality along the chain maps `c • 𝟙`, so additivity of `φ ↦ T_φ` is not needed either.

What `pairing-product` does need beyond this rung: its last clause, `pairProduct λ x y = y.comp x` on `ℚ_X[0]`, applies `T_{ℚ[0]}` to an arbitrary morphism `x` of `D(ShQ)`, which is a roof, not `Q.map` of a chain map. Computing `T_{ℚ[0]}(x)` needs a natural isomorphism `T_{𝟙} ≅ 𝟭` with a known component at `Q.obj K` (finding 3).

## 5. Checker

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`. The module is not yet in the default target and the ledger names none of its declarations, so the checker does not cover it yet. In scratch, `#print axioms` on `mapBifunctorRight`, `mapBifunctorRightMap_comp`, `mapBifunctorRight_additive`, `derivedMapBifunctorRight_additive`, `derivedMapBifunctorRightMap_unique`, `derivedMapBifunctorRightMap_comp`, `tensorRightComplex_map`, `tensorRightComplexMap_app`, `tensorRightComplex_isInvertedBy`, `derivedTensorRight_bounds`, `derivedTensorRight_additive`, `derivedTensorRightMap_app`, `derivedTensorRightMap_unique`, `derivedTensorRightMap_id`, `derivedTensorRightMap_comp` gives `[propext, Classical.choice, Quot.sound]` for each; the others are definitions or are used by these. No `sorry`, `native_decide`, `unsafe`, `axiom` or `maxHeartbeats` in the file. `lake build HodgeLadder.Hodge.DerivedTensorBounded`: 114 s, no warnings from the module.

## 6. Conventions

| Convention | Where | In `docs/conventions.md` | Truth depends on it |
|---|---|---|---|
| Koszul signs of `tensorObj` (`ε₁ = 1`, `ε₂(p, q) = (−1)^p`) | Mathlib `TensorSigns (ComplexShape.up ℤ)` through `tensorObj K B` | row "Tensor product of ℤ-indexed cochain complexes and its shifts" | not for existence or additivity of `T_B`; yes for any identity built on it (`pairing-product`, `de-rham-cup`) |
| Order of factors: `B` second | `mapBifunctor K B`, `curriedTensor` | added, row "Derived tensor with a bounded complex" | yes for `pairing-product`: shifts in the first factor carry no sign, in the second `(−1)^{p·y}` |
| Factorization iso | `Localization.fac`, no scalar | added, same row | yes for `_app` and every identity read through it |
| Components of `T_φ` | `Q.map (𝟙_K ⊗ φ)` conjugated by the factorization isos; `mapBifunctorMap (𝟙 K) φ` is `𝟙 ⊗ φ^q` on each summand, no sign since `φ` has degree 0 | added, same row | yes for naturality in `B` |
| Shift structure | none on `T_B`; `Q.commShiftIso` and `mapBifunctorShift₁Iso` (no sign) are used by consumers | existing row (shifts) and the added row | the absence of a sign in the left-action pairing |

No borrowed result carries a convention: `tensorBoundedQuasiIso_holds` is a quasi-isomorphism statement, insensitive to signs and to the scalar normalization of `tensorHom`. **Signs: none here; confirmed.**

## 7. Equality first

A foundation construction, not an identity. Its equations (`_fac`, `_app`, `_id`, `_comp`, `_bounds`, the `rfl` pins) are exact; none holds up to a scalar. It is a step toward the exact identity `fieldToDeRhamCohomology_cup` (rung `de-rham-cup`, open) through `pairing-product` (open).

## 7b. Non-vacuity

The smallest test that would fail for a degenerate `T_B` is the unit iso `T_{𝟙} ≅ 𝟭` with component `facIso.hom.app K ≫ Q.map (HomologicalComplex.rightUnitor K).hom` at `Q.obj K` (finding 3); it does not exist yet. **Not required for this rung's pass**: the `Lifting` instance and the `rfl` pin to `tensorObj` already characterize `T_B` up to unique isomorphism. It is required by `pairing-product`'s last clause, so it has to land in one of the two rungs. Mathlib names: `HomologicalComplex.tensorUnit (ShQ Y) (.up ℤ)` (`= (single _ _ 0).obj (𝟙_ _)`), `HomologicalComplex.rightUnitor` (needs `[∀ X₁, PreservesColimit (Functor.empty _) ((curriedTensor _).obj X₁)]`, available from `Cup.tensorLeft_preservesColimits`), `Localization.liftNatIso`, `Localization.Lifting.id`. `𝟙_ (ShQ Y)` under `sheafMonoidal` is the sheafified constant presheaf; the bridge to the constant sheaf `ℚ_X` of `rationalExtEquiv` belongs to `pairing-product` and should be recorded there.

## 8. Pin drift

None. The worktree pins equal `main`'s; `git diff 146af90 main` touches only `HodgeLadder/Cycle/MultiplicativeNoReg.lean`, `HodgeLadder/Normalization/GermNoReg.lean`, the root import list and docs, none of which this module or its imports depend on.

## Findings

1. **The functor is the right one at the right strength.** `T_B := Localization.lift (tensorRightComplex Y B ⋙ Q)`, additive, natural in chain maps of `B`, with `_unique` the correct universal property: `Localization.liftNatTrans` is the unique transformation whose whiskering by `Q` satisfies the `_fac` square (`Localization.natTrans_ext`). The functor itself is unique up to unique isomorphism through the `Lifting` instance and Mathlib's `Localization.Lifting.uniq`; no extra lemma needed. Additivity by `functor_additive_iff` along `Qh` and `additive_of_full_essSurj_comp` along the quotient is sound, and simpler than the route of `cup-hodge-filtration.redteam.md` finding 6 (no `mapBifunctorMapHomotopy₁`).
2. **Duplication of Mathlib.** `Functor.map₂CochainComplex` (`Algebra/Homology/Bifunctor.lean:311`) is Mathlib's bifunctor on cochain complexes. `mapBifunctorRight F B` is `F.map₂CochainComplex.flip.obj B` and `mapBifunctorRightMap F φ` is `F.map₂CochainComplex.flip.map φ`, both by `rfl` (scratch, generic context, under 0.1 s each). Keep the local definitions, since they ask for `HasMapBifunctor` only against the fixed `B`, and add the two pins (change 2). Record `mapBifunctorRight` and `derivedMapBifunctorRight` in `docs/gaps.md` "To upstream" (Mathlib).
3. **The unit iso is an input to `pairing-product`.** See 4 and 7b. The generic half is cheap and checked in scratch (change 3); the sheaf half needs naturality of `HomologicalComplex.rightUnitor` in `K`, which Mathlib proves only inside the monoidal instance unavailable here.
4. **Kernel cost: intrinsic to Mathlib's tensor of complexes at `ShQ Y`, and the generic layer is the right mitigation.** Measurements in scratch files importing the built module (`set_option profiler true`):

   | Declaration | Kernel time |
   |---|---|
   | `DerivedCategory.Q.map f`, `f` a chain map of `CochainComplex (ShQ Y) ℤ` | under 0.1 s |
   | `HomologicalComplex.tensorHom f (𝟙 B)` alone, in a fresh file, no generic layer | 9.5 s |
   | the same with `attribute [local instance 10000] Preadditive.preadditiveHasZeroMorphisms` | 9.7 s |
   | the same with a nose-level instance `((curriedTensor (ShQ Y)).obj X).Additive` | 9.4 s |
   | `(tensorRightComplex Y B).obj K = tensorObj K B := rfl` | 4.8 s |
   | `(derivedTensorRightFacIso Y B a b).hom.app K ≫ Q.map (tensorHom f (𝟙 B))` | 20.3 s |
   | `tensorRightComplex` defined directly on sheaves (no generic layer), its `obj` pin, `Q.map` of its `map` | 29 s, 2.2 s, about 10 s |
   | `inferInstance : (derivedTensorRight Y B a b).Additive`, `Functor.map_add` on `T_B` | under 0.1 s |

   With the pin, `ObjectProperty.instHasZeroMorphismsFullSubcategory` leaves the kernel's unfold list, so that diamond contributes, but `instZeroHomFunctor`, `functorCategoryPreadditive`, `Preadditive.homGroup`, `Function.Injective.addZeroClass` and `InducedCategory.Hom.hom` remain, with about 120,000 unfoldings of `Add.add`. The diagnostics point to a second mismatch between zero morphisms on `ShQ Y ⥤ ShQ Y` (functor-category instance against the preadditive one) inside `HasMapBifunctor`, which no local instance in this file reaches. A local `HasZeroMorphisms` instance is therefore not a fix, and it would move the first mismatch to every boundary with files elaborated at the default path (`tensorBoundedQuasiIso_holds`, `hasTensor_shQ`). Recommendations: (a) keep the generic layer and instantiate once, as done; (b) state `pairing-product` and the `de-rham-cup` plumbing in the same generic form (any abelian `C` with `F : C ⥤ C ⥤ C` additive in each variable, `hB` a hypothesis), instantiating at `ShQ` once; budget about 10 s per sheaf-level `tensorHom` otherwise; (c) record the cost in `docs/gaps.md` "Known weaknesses" with the table above, as a candidate Mathlib performance issue.
5. **Keep the `rfl` pins.** `tensorRightComplex_obj`, `_map`, `tensorRightComplexMap_app` are paid once per build (about 35 s of 114 s); a downstream file that uses them does not re-check their proofs, and a consumer that needs the identification would pay the same cost to prove it. `_obj` is the convention pin (it carries the Koszul sign of `tensorObj`), `_map` is what naturality in `A` rewrites with, `_app` is what naturality in `B` rewrites with. Do not drop them.
6. **Bookkeeping.** The sketch says the ledger entry names `HodgeLadder/Derived/Tensor/Bounded.lean`; the ledger has `"module": null`. The ledger title says `tensorRight B`; the Lean has `tensorRightComplex Y B`.

## Recommended changes

1. At posting: `public import HodgeLadder.Hodge.DerivedTensorBounded` in `HodgeLadder.lean`; ledger `module` `HodgeLadder.Hodge.DerivedTensorBounded`, `declarations` at least `derivedTensorRight`, `derivedTensorRightFacIso`, `derivedTensorRight_additive`, `derivedTensorRightMap`, `derivedTensorRightMap_app`, `derivedTensorRightMap_unique`, `derivedTensorRightMap_id`, `derivedTensorRightMap_comp`, `tensorRightComplex_obj`, `tensorRightComplex_isInvertedBy`, `derivedMapBifunctorRight_additive`, `derivedMapBifunctorRightMap_unique`; ledger note: "`tensorRightComplex Y B` (pinned by `rfl` to `tensorObj`, `tensorHom`) stands in for `tensorRight B`". Fix the sketch sentence of finding 6. Add `docs/gaps.md` rows for findings 2 and 4(c).
2. Pins against Mathlib, in the generic section (checked in scratch, `rfl`):

   ```lean
   /-- `mapBifunctorRight F B` is Mathlib's bifunctor on cochain complexes with `B` fixed. -/
   theorem mapBifunctorRight_eq_map₂CochainComplex
       [h : ∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
         HasMapBifunctor K₁ K₂ F (.up ℤ)] (B : CochainComplex C₂ ℤ) :
       mapBifunctorRight F B = F.map₂CochainComplex.flip.obj B := rfl

   /-- `mapBifunctorRightMap F φ` is Mathlib's bifunctor on cochain complexes applied to `φ`. -/
   theorem mapBifunctorRightMap_eq_map₂CochainComplex
       [h : ∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
         HasMapBifunctor K₁ K₂ F (.up ℤ)] {B B' : CochainComplex C₂ ℤ} (φ : B ⟶ B') :
       mapBifunctorRightMap F φ = F.map₂CochainComplex.flip.map φ := rfl
   ```

3. Generic unit iso, in a new section with one abelian category (checked in scratch, 5 s for the file); here or as the first declarations of `pairing-product`:

   ```lean
   section Unit

   variable {C : Type*} [Category* C] [Abelian C] (F : C ⥤ C ⥤ C) [F.Additive]
     [∀ X, (F.obj X).Additive] [HasDerivedCategory C]

   /-- A natural iso `mapBifunctorRight F B ≅ 𝟭` descends to `derivedMapBifunctorRight F B hB ≅ 𝟭`. -/
   def derivedMapBifunctorRightIsoId (B : CochainComplex C ℤ)
       [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
       (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
       (ρ : mapBifunctorRight F B ≅ 𝟭 _) :
       derivedMapBifunctorRight F B hB ≅ 𝟭 _ :=
     Localization.liftNatIso DerivedCategory.Q (quasiIso C (.up ℤ))
       (mapBifunctorRight F B ⋙ DerivedCategory.Q) DerivedCategory.Q _ _
       (Functor.isoWhiskerRight ρ DerivedCategory.Q ≪≫ DerivedCategory.Q.leftUnitor)

   /-- The component of `derivedMapBifunctorRightIsoId` at `Q.obj K`. -/
   theorem derivedMapBifunctorRightIsoId_hom_app (B : CochainComplex C ℤ)
       [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
       (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
       (ρ : mapBifunctorRight F B ≅ 𝟭 _) (K : CochainComplex C ℤ) :
       (derivedMapBifunctorRightIsoId F B hB ρ).hom.app (DerivedCategory.Q.obj K) =
         (derivedMapBifunctorRightFacIso F B hB).hom.app K ≫
           DerivedCategory.Q.map (ρ.hom.app K) := by
     simp [derivedMapBifunctorRightIsoId, Localization.liftNatIso, Localization.liftNatTrans_app]
     rfl

   end Unit
   ```

   The sheaf instance (not attempted; it needs `rightUnitor` naturality and pays the kernel cost of finding 4) is `derivedTensorRightUnitIso Y : derivedTensorRight Y (HomologicalComplex.tensorUnit (ShQ Y) (.up ℤ)) 0 0 ≅ 𝟭 _`, from `derivedMapBifunctorRightIsoId` with `ρ` built from `HomologicalComplex.rightUnitor`.
4. Not needed, do not add for this rung: `CommShift` on `T_B`, additivity of `φ ↦ T_φ`, invertibility of `T_φ` for a quasi-isomorphism `φ` (would need `tensor-bounded-quasi-iso` in the second variable), a bifunctor on `D × D`. If a later consumer needs any of them, open a new rung.

## What was tried

- Trivial proofs of the generic `_id` (`rfl`, `simp`, `ext; rfl`): all fail.
- Pinning `HasZeroMorphisms (ShQ Y)` to `Preadditive.preadditiveHasZeroMorphisms`: removes one diamond from the kernel trace, no speed-up. A nose-level additivity instance for `(curriedTensor _).obj X`: no speed-up. A direct sheaf-level `tensorRightComplex`: as slow as, or slower than, the generic one.
- Unit iso: generic half compiles; the sheaf half is not attempted.
- Rfl pins against `Functor.map₂CochainComplex`: both succeed.
- Downstream `inferInstance` for `T_B.Additive` with the sheaf-level instance present: immediate. The five-minute search the prover hit without it is plausibly the instance-implicit `hasB` argument of the generic instance, which sends search after `HasMapBifunctor` on `CochainComplex (ShQ Y) ℤ` (not traced).
