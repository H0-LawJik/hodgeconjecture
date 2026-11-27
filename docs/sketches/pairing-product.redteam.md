# Red team: `pairing-product` (statement and proof)

Date: 2026-11-27. Worktree `pairing-product` at base `41f2f6b`, uncommitted `HodgeLadder/Hodge/PairingProduct.lean` (not imported from `HodgeLadder.lean`) and the section "pairing-product: statement" of `docs/sketches/cup-hodge-filtration.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`; `lakefile.toml` and `lake-manifest.json` are byte-identical to `main` (`44a0e85`). Phase 1 finished with no open goals, so statement and proof are reviewed together.

Read: the ledger entries `pairing-product`, `de-rham-cup`, `wedge-sheaf-map`, `rational-de-rham-complex`, `rational-hypercohomology-equiv` (on `main`); the module; the sketch sections "Construction of the product", "derived-tensor-bounded: statement", "pairing-product: statement"; `docs/sketches/cup-hodge-filtration.redteam.md` (finding 5), `docs/sketches/derived-tensor-bounded.redteam.md`; `docs/conventions.md` rows "Cup product", "Tensor product of ℤ-indexed cochain complexes and its shifts", "Derived tensor with a bounded complex", "de Rham cup order (proposed)", and on `main` "Rational hypercohomology bridge", "Derived-category instances in statements"; Mathlib `Algebra/Homology/BifunctorShift.lean` (`mapBifunctorShift₁Iso`, `ι_mapBifunctorShift₁Iso_hom_f`, `mapBifunctorShift₂Iso`, `ι_mapBifunctorShift₂Iso_hom_f`), `CategoryTheory/Shift/ShiftedHom.lean` (`comp`, `mk₀_id_comp`, `comp_mk₀_id`); upstream `Hodge/Filtration.lean` (`SMul ℂ H_dR^n(X)`, `deRham_complex_smul_eq`); `HodgeLadder/Hodge/RationalHypercohomology.lean` on `main` (`rationalUnitComplex`, `rationalHypercohomologyEquiv`, `_map`).

Scratch files (inside the worktree, deleted afterwards) import the built module (`.lake/build` olean newer than the source): RT1 `#print axioms` on all 42 declarations; RT2 non-vacuity and sign probes in the generic layer and the `rfl` bridge to the `singleFunctor` spelling; RT3 trivial-proof attempts; RT4 to RT6 consumer-side kernel cost at `ShQ Y`, with `Elab.async false` for the serial timings; RT7 the Lean of change 2. The module itself was not recompiled.

**Verdict: pass with changes.** The pairing is the one the route needs, at full strength: with the checked bridge and the planned wedge it gives `fieldToDeRhamCohomology_cup` with no sign, biadditivity, ℂ-linearity through naturality, and statement (a) through naturality along `F^p → Ω•`. No sign enters, and every identity is exact. The changes concern kernel cost (one unused declaration to drop, one name to add) and bookkeeping.

## 1. Is this the statement the literature makes?

The literature object is the cup product on hypercohomology induced by a pairing of complexes: for `m : A ⊗ B → C`, `H^a(X, A) × H^b(X, B) → H^{a+b}(X, C)`, `(x, y) ↦ m_*(x ∪ y)`, where `x ∪ y` is represented on cocycles by `x ⊗ y` [`Iversen1986`, chapter on cup products, unverified; `Bredon1997`, products in sheaf cohomology, sections unverified]. In derived terms, with `x : ℚ → A[a]`, `y : ℚ → B[b]`: `ℚ ≅ ℚ ⊗ ℚ → A[a] ⊗ B[b] ≅ (A ⊗ B)[a + b] → C[a + b]`, the middle isomorphism carrying a Koszul convention.

| Field | Literature | Lean | Match |
|---|---|---|---|
| Category | `D(Sh(X, ℚ))` | generic: any abelian `C` with `[HasDerivedCategory C]`; sheaf layer: `DerivedCategory (ShQ Y)`, any `HasDerivedCategory` instance | yes; the bridge's instance `HasDerivedCategory.standard` is one instance |
| Classes | `x ∈ Hom(ℚ, A[a])`, `y ∈ Hom(ℚ, B[b])` | `x : ShiftedHom (Q.obj E) (Q.obj A) a`, `y : ShiftedHom (Q.obj E) (Q.obj B) b`; sheaf layer `E = unitComplex Y = ℚ_Y[0]` | yes; `unitComplex_eq_single_QX` (`rfl`) and RT2 below tie `E` to `main`'s `rationalUnitComplex` |
| Pairing of complexes | `m : A ⊗ B → C` | `m : (mapBifunctorRight F B).obj A ⟶ D`; sheaf layer `m : (tensorRightComplex Y B).obj A ⟶ D`, i.e. `tensorObj A B ⟶ D` (`tensorRightComplex_obj`, `rfl`) | yes |
| Boundedness | none needed over a field | `B` strictly bounded (input of `hB`); `A`, `D` arbitrary | the ledger title says "bounded A, B, C"; the Lean is more general in `A` and `D`, and every complex the route feeds in is bounded |
| Formula | `m_*(x ⊗ y)` on cocycles | `y ≫ (pairAction m x)⟦b⟧' ≫ (shiftFunctorAdd' a b n h).inv`, with `pairAction m x` the descent of `x ⊗ B` followed by `m⟦a⟧` | yes, with no sign: on representatives the composite sends `1` to `m(x ⊗ y)` on the `(a, b)` summand (section 6) |
| Unit | `x ∪ y` on `ℚ` is the Yoneda product | `pairProductShQ_unit`: `pairProduct λ x y = y.comp x` | yes; the order is the one registered in the row "de Rham cup order (proposed)" |
| Functoriality | natural in `(A, B, C, m)` | chain maps `f, g, k` with `m ≫ k = (f ⊗ g) ≫ m'` (`pairProductShQ_naturality`) | sufficient: every map `de-rham-cup` and `cup-hodge-filtration` feed in is a chain map |
| Bilinearity | biadditive (ℚ-bilinear) | `_add_left`, `_add_right` | ℚ-linearity follows (section 4, finding 4) |

**Is this the pairing at full strength for the route?** Walked through each use in `de-rham-cup` and `cup-hodge-filtration`, with `deRhamCup x y := pairProduct μ y x` (slot `x` of `pairProduct` gets `y`):

- `fieldToDeRhamCohomology_cup`. With `u : ℚ_X[0] → Ω•_ℚ` and the wedge unit law `(u ⊗ u) ≫ μ = λ ≫ u` (from `μ ∘ (u ⊗ 𝟙) = λ_Ω` and `complexLeftUnitor_hom_naturality`), `pairProductShQ_naturality` at `A = B = D = ℚ_X[0]`, `m = λ`, `f = g = k = u`, `m' = μ` and `pairProductShQ_unit` give `pairProduct μ (β ≫ u) (α ≫ u) = (α.comp β) ≫ u`, the image of `α ∪ β` (row "Cup product": `α ∪ β` is `α.comp β`). So `ι (α ∪ β) = deRhamCup (ι α) (ι β)` holds with no sign, given the bridge's agreement with `rationalExtEquiv` (checked on `main`). The degree proofs differ (`b + a = n` against `a + b = n`); they are proofs of a `Prop`.
- Biadditivity of `deRhamCup`: `pairProductShQ_add_right` for the first argument, `pairProductShQ_add_left` for the second (the slots are swapped).
- ℂ-linearity: upstream's `c • α` is `hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c) n α` (`deRham_complex_smul_eq`, `rfl`); the bridge turns it into postcomposition with `Q.map (c • 𝟙)` (`rationalHypercohomologyEquiv_map`), and naturality with `f = c • 𝟙` (or `g`), `k = c • 𝟙` needs `(c • 𝟙 ⊗ 𝟙) ≫ μ = μ ≫ c • 𝟙` and the same in the second factor. These belong to `wedge-sheaf-map` (or `de-rham-cup`); no new pairing statement is needed.
- Statement (a): for `x ∈ F^p`, `y ∈ F^q` from `x' : ℚ → F^p[a]`, `y' : ℚ → F^q[b]`, naturality with `f = i_q`, `g = i_p`, `k = i_{p+q}`, `m = μ_{q,p} : F^q ⊗ F^p → F^{p+q}`, `m' = μ` puts `deRhamCup x y` in the image of `ℍ^n(F^{p+q})`. `B = F^p Ω•_ℚ` is strictly bounded.

## 2. Can the hypotheses be satisfied?

Yes. The generic hypotheses are discharged in the instances: `hB` by the checked `tensorRightComplex_isInvertedBy`, `hρ` by `complexRightUnitor_hom_shift`, `hlam` by `complexLeftUnitor_hom_naturality`. The sheaf-level theorems have no hypothesis beyond instances except `hm`, which `f = g = k = 𝟙`, `m = m'` satisfies. Checked in RT2 (generic, under 8 s):

```lean
example (E : CochainComplex C ℤ) [hasE : ∀ K : CochainComplex C ℤ, HasMapBifunctor K E F (.up ℤ)]
    (hE : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F E ⋙ DerivedCategory.Q))
    (ρ : mapBifunctorRight F E ≅ 𝟭 _)
    (hρ : ∀ a : ℤ, ρ.hom.app (E⟦a⟧) = (mapBifunctorRightShiftIso F E E a).hom ≫ (ρ.hom.app E)⟦a⟧')
    {b : ℤ} (y : ShiftedHom (Q.obj E) (Q.obj E) b) :
    pairProduct F E hE (ρ.app E) (ρ.hom.app E) (zero_add b) (ShiftedHom.mk₀ 0 rfl (𝟙 _)) y = y := by
  rw [pairProduct_unit F E hE ρ hρ]; exact ShiftedHom.comp_mk₀_id y 0 rfl
```

and its mirror `pairProduct … (add_zero a) x (ShiftedHom.mk₀ 0 rfl (𝟙 _)) = x` (by `ShiftedHom.mk₀_id_comp`). On a nonzero `Q.obj E` (for `ℚ_Y[0]`, any nonempty `Y`) the pairing is therefore nonzero.

## 3. Is the conclusion trivially true?

No. Attempts in RT3, all rejected:

- `simp [pairAction, hρ, derivedMapBifunctorRightIsoId_hom_app]` on `pairAction_unit`: unsolved goals.
- `unfold pairAction; aesop_cat` on `pairAction_unit` without `hρ`: fails after exhaustive search.
- `rfl` and `ext; simp` on `complexRightUnitor_hom_shift`: type mismatch, unsolved goals.
- The prover reports `rfl` on `pairProduct_unit` and `pairProduct_add_left`, `simp [pairProduct, pairAction, hρ]` on `pairProduct_unit` and `simp [pairProduct, pairAction]` on `pairProduct_naturality_left` all leave goals.

Unused hypotheses: none. `hρ` is rewritten in `pairAction_unit`; `hlam` is used in `pairProduct_naturality_right`; the bounds feed `hB`; `[∀ X₂, PreservesColimit … ((curriedTensor C).flip.obj X₂)]` is needed for the left unitor and is omitted where unused (`omit … in`). No definition unfolds to `True`, no index type is empty, no `ℕ∞` appears.

`hρ` is a genuine hypothesis: naturality of `ρ` does not relate `ρ_{E⟦a⟧}` to `shift₁ ≫ ρ_E⟦a⟧`, two isomorphisms `E⟦a⟧ ⊗ E ≅ E⟦a⟧`. It cannot imply the unit clause by itself: the clause applies the descended functor to a roof `x`, which needs `derivedMapBifunctorRightIsoId` and its naturality.

## 4. Interface rung?

No. There is no structure with axioms (decision 0003). The `Prop` inputs `hB`, `hρ`, `hlam`, `hm` are theorems in the instances.

**Missing statements.**

- ℚ-linearity: automatic. An additive map between ℚ-vector spaces is ℚ-linear (`map_ratCast_smul`, `AddMonoidHom.toRatLinearMap`), so `pairProductShQ_add_left`, `_add_right` give it. Nothing to add.
- ℂ-linearity: through naturality along `c • 𝟙`, section 1; the inputs are the commutation of `μ` with `c • 𝟙` in each factor (rung `wedge-sheaf-map`) and the identification of `forget (c • 𝟙)` with upstream's `scalarHolomorphicDeRhamComplexInt X c` through `forgetRationalDeRhamIso` (rung `rational-de-rham-complex`). Record both in the `de-rham-cup` brief.
- Associativity: `de-rham-cup` and T1 use binary products only (`W_K ⊆ H²` of an abelian surface is spanned by products of two `H¹` classes). Not needed.
- Graded commutativity: T1 needs antisymmetry of `deRhamCup` on `H¹` (`de-rham-cup-antisymm-h1`), which follows from `fieldToDeRhamCohomology_cup`, ℂ-bilinearity, the rational span (`de-rham-rational-span`) and graded commutativity of `Cup.cup` (rung `cup-graded-commutative`). A graded commutativity of `pairProduct` itself is not needed.
- Naturality along morphisms of the derived category, and compatibility with `T_φ` for a quasi-isomorphism `φ`: not needed; every map in the route is a chain map.

## 5. Checker and axioms

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`. The module is not in the default target and the ledger names none of its declarations, so the checker does not cover it yet. RT1 (`#print axioms`, 5 s): all 42 declarations (the sketch says 40; the two `unitComplex` bound instances make 42) depend on `[propext, Classical.choice, Quot.sound]` and nothing else. No `sorry`, `native_decide`, `unsafe`, `axiom`, `set_option` or `maxHeartbeats` in the file.

## 6. Conventions

| Convention | Where | In `docs/conventions.md` | Truth depends on it |
|---|---|---|---|
| Shift in the first variable, `(A⟦a⟧) ⊗ B ≅ (A ⊗ B)⟦a⟧` | Mathlib `mapBifunctorShift₁Iso` ("does not involve signs"; `ι_mapBifunctorShift₁Iso_hom_f` is `shiftFunctorObjXIso` on each summand) | row "Tensor product of ℤ-indexed cochain complexes and its shifts" | yes: a sign here would rescale `pairAction` by `±1` in odd `a` |
| Shift in the second variable | Mathlib `mapBifunctorShift₂Iso`, `(n₁ * y).negOnePow` on the summand of first degree `n₁` | same row | not used. It would give the right-action pairing `(−1)^{ab} m(x ⊗ y)`. On the unit complex the sign is `(−1)^{0·y} = 1`, so the unit clause alone cannot tell the two pairings apart; they differ once `x` has odd degree and `y` odd shift |
| Product of shifted morphisms | Mathlib `ShiftedHom.comp f g h = f ≫ g⟦a⟧' ≫ (shiftFunctorAdd' C b a c h).inv.app _` | row "Hom-complex composition and derived classes" | yes, it is the outer step of `pairProduct`; no sign |
| `Q`'s shift iso | `Q.commShiftIso` (identities degreewise at the chain level) | rows "Derived tensor with a bounded complex", "Rational hypercohomology bridge" | no sign |
| Unitors of complexes | Mathlib `HomologicalComplex.leftUnitor`, `rightUnitor` (degreewise `λ`, `ρ` on the summand with the unit in degree 0) | added, new row "Pairing product (left action)" | yes for the unit clause: `λ_𝟙 = ρ_𝟙` (`complexLeftUnitor_tensorUnit_inv`), `ρ_{K⟦a⟧} = shift₁ ≫ ρ_K⟦a⟧` (`complexRightUnitor_hom_shift`), both exact |
| Order of the factors | `x` acts on `B` from the left, `y` applied first; on `ℚ_Y[0]`, `pairProduct λ x y = y.comp x` | row "de Rham cup order (proposed)", updated to name the primitive; new row | yes for `de-rham-cup`: the definition `deRhamCup x y := pairProduct μ y x` makes the identity sign-free; the other order would give `(−1)^{ab}` there |
| Bridge source object | `unitComplex Y = tensorUnit = (single _ _ 0).obj (QX Y)` (`rfl`); `main`'s `rationalUnitComplex X = (CochainComplex.singleFunctor _ 0).obj (QX _)` | new row | the type of every identity `de-rham-cup` states; `rfl` at a variable `Y` (RT2) |

**Element-level reading (red-team computation, by hand from the Mathlib component lemmas).** Let `x ∈ A^a`, `y ∈ B^b` be cocycles, viewed as chain maps `ℚ[0] → A⟦a⟧`, `ℚ[0] → B⟦b⟧` (degree-0 component `1 ↦ x`, resp. `y`). Then `x ⊗ B : ℚ[0] ⊗ B → A⟦a⟧ ⊗ B` sends `1 ⊗ β ↦ x ⊗ β`; it is a chain map since `d(x ⊗ β) = d_{A⟦a⟧} x ⊗ β + (−1)^0 x ⊗ dβ = x ⊗ dβ`. Shifting by `b` (`(f⟦b⟧').f p = f.f (p + b)`, no sign) and precomposing with `y` sends `1 ↦ x ⊗ y` on the summand `A⟦a⟧^0 ⊗ B^b = A^a ⊗ B^b`; `mapBifunctorShift₁Iso` moves it to the `(a, b)` summand of `(A ⊗ B)^{a+b}` with no sign, and `shiftFunctorAdd'` is `XIsoOfEq`. So `pairProduct m x y = [m(x ⊗ y)]`, the classical formula with `x` first. With the right action (`mapBifunctorShift₂Iso`, `n₁ = a`) the result is `(−1)^{ab} [m(x ⊗ y)]`. Consequently `deRhamCup [θ] [η] = [η ∧ θ]` heuristically, as the row "de Rham cup order (proposed)" says, and `y.comp x` on `ℚ_Y[0]` is the classical `x ⌣ y`, matching the checked `Ψ (α ∪ β) = cupSing (Ψ β) (Ψ α)` (row "Cup product"). This reading is not a Lean statement; nothing checked depends on it, since `fieldToDeRhamCohomology_cup` will follow from naturality and the unit clause alone.

**Borrowed results.** `tensorRightComplex_isInvertedBy` (quasi-isomorphism statement, insensitive to signs); `derivedMapBifunctorRightIsoId_hom_app` (no scalar, row "Derived tensor with a bounded complex"); Mathlib's `unitors_inv_equal` (used in `complexLeftUnitor_tensorUnit_inv`), an identity in any monoidal category. Each is stated against the definitions used here.

**A sign in `m` is visible.** RT2: `pairProduct F E hB lam (m ≫ (-𝟙 D)) h x y = -pairProduct F E hB lam m h x y` by `pairProduct_comp_target` and `simp`. So a stray `−1` in the unitor or in `μ` would rescale the unit clause and the `de-rham-cup` identity; the proofs exclude it.

## 7. Equality first

Every identity in the module is exact: the unit clause `pairProductShQ_unit` is an equality with no scalar, as are naturality, biadditivity, `complexRightUnitor_hom_shift` (no sign) and `complexLeftUnitor_tensorUnit_inv`. The rung is a step toward the exact identity `fieldToDeRhamCohomology_cup` (rung `de-rham-cup`, open; depends also on `wedge-sheaf-map`, open, and `rational-hypercohomology-equiv`, checked on `main`).

## 7b. Non-vacuity

Smallest test: the unit clause at `x = ShiftedHom.mk₀ 0 rfl (𝟙 _)`, giving `pairProduct ρ_E (mk₀ 𝟙) y = y` (Mathlib `ShiftedHom.comp_mk₀_id`). It would fail for the zero pairing whenever `y ≠ 0`. Checked in RT2 at the generic layer; not in the module. Optional to add; the unit clause carries it. The sign-visible test of the full route is `de-rham-cup-test-p2` (`deRhamCup (ι [L₀]) (ι [L₁]) ≠ 0` on ℙ², open), with `de-rham-injective` (open).

## 8. Pin drift

None. The worktree pins equal `main`'s. `git diff 41f2f6b main` adds `HodgeLadder/Cup/RationalExtHom.lean`, `HodgeLadder/Hodge/RationalHypercohomology.lean`, two root imports and docs; it changes no file this module imports (`DerivedTensorBounded`, its `Cup` imports, Mathlib `BifunctorShift`). Rebase conflicts to expect: `docs/sketches/cup-hodge-filtration.md` (`main` added 113 lines) and `docs/conventions.md` (`main` added two rows; this pass adds one and edits one).

## Findings

1. **The right pairing, at full strength.** `pairProduct m x y = [m(x ⊗ y)]` with `x` first and no sign (section 6); on `ℚ_Y[0]` it is `y.comp x`; it is natural in chain maps of `(A, B, D, m)` and biadditive. With `deRhamCup x y := pairProduct μ y x`, it yields `ι (α ∪ β) = deRhamCup (ι α) (ι β)`, biadditivity, ℂ-linearity and statement (a), each from the statements here plus inputs owned by other rungs (section 1).
2. **Signs: none; confirmed. The route has no place for the second-variable sign.** The only chain-level shift is in the first variable (`mapBifunctorShift₁Iso`). The shift of `y` enters through `ShiftedHom.comp`, the derived shift functor applied to a morphism, which has no sign. No complex of the form `A ⊗ B⟦b⟧` appears in any definition, so `mapBifunctorShift₂Iso`'s `(−1)^{p·b}` cannot enter. The unitors' `_shift` lemma is in the first variable and is exact; Mathlib's Koszul convention (`ε₂(p, q) = (−1)^p`) is compatible with it (on `K⟦a⟧ ⊗ 𝟙` both differentials are `(−1)^a d_K ⊗ 1`).
3. **The unit clause is right, and `lam` as data is harmless.** In the generic clause `lam = ρ.app E` and `m = ρ_E`; in the tensor and sheaf layers `lam` is fixed to `HomologicalComplex.leftUnitor B` and `m = λ_𝟙`, matched to `ρ_𝟙` by `complexLeftUnitor_tensorUnit_inv`. Consumers use `pairProductShQ`, where `lam` is not a parameter. A different `lam` would only change the generic `pairProduct`, which no downstream rung names.
4. **No missing statement blocks `de-rham-cup` or T1.** ℚ-linearity is automatic; ℂ-linearity comes from naturality and two facts owned by `wedge-sheaf-map` and `rational-de-rham-complex`; associativity and graded commutativity of the pairing are not used (section 4).
5. **Kernel cost: keep the four sheaf theorems, drop the unused unit iso, name the unit multiplication.** Each of `pairProductShQ_add_left`, `_add_right`, `_naturality`, `_unit` is used by `de-rham-cup` (biadditivity in each argument, the ι identity, ℂ-linearity, statement (a)); keep all four. `derivedTensorRightUnitIso` is used by no declaration (the unit clause is proved generically through `derivedMapBifunctorRightIsoId`), and costs about 40 s by the prover's measurement (a copy in RT4 ran 30 to 45 s, in an asynchronous run); drop it. Consumer-side probes (RT5, RT6, serial, `Elab.async false`): a statement that mentions `pairProductShQ` with a general `m` checks in under 1 s; with `(HomologicalComplex.leftUnitor (unitComplex Y)).hom` written as `m` it pays 7.9 s per declaration, the diamond between `tensorObj 𝟙 𝟙` and `(tensorRightComplex Y 𝟙).obj 𝟙`; with a named map typed as `(tensorRightComplex Y (unitComplex Y)).obj (unitComplex Y) ⟶ unitComplex Y` it is under 1 s again (the name costs 16 s once). `abbrev` against `def` for `pairProductShQ` made no measurable difference. A placeholder `𝟙 _` for `𝟙 (Q.obj (unitComplex Y))` cost 23 s of elaboration in one statement; written out, under 1 s. A consumer applying `pairProductShQ_unit` with the unitor spelled out paid 17 s of kernel time (RT4).
6. **Bridge to `main`'s source object.** `de-rham-cup` composes `pairProductShQ` at `Y = TopCat.of (ComplexPoint X)` with `rationalHypercohomologyEquiv`, whose source is `Q.obj (rationalUnitComplex X)`, `rationalUnitComplex X = (CochainComplex.singleFunctor _ 0).obj (Cup.QX _)`. RT2: `unitComplex Y = (CochainComplex.singleFunctor (ShQ Y) 0).obj (QX Y) := rfl` at a variable `Y`, under 1 s. The consumer must activate `main`'s `rhQHasDerivedCategory` (row "Derived-category instances in statements"); `pairProductShQ` takes any instance, so it applies.
7. **Bookkeeping.** The sketch says "The ledger entry names `HodgeLadder/Pairing/Product.lean`"; no file in the repository says that (the ledger has `"module": null`). The sketch counts 40 declarations; there are 42. The ledger note says the unit clause "needs the sheaf unit iso `derivedTensorRightUnitIso`"; the proof uses the generic iso only.

## Recommended changes

1. Drop `derivedTensorRightUnitIso` from `HodgeLadder/Hodge/PairingProduct.lean` (and from the sketch table and module docstring), keeping `derivedTensorUnitIso` and `derivedTensorUnitIso_hom_app` as the record of `T_𝟙 ≅ 𝟭`. If the ledger's wording is to be kept instead, keep it and accept about 40 s per build.
2. Name the unit multiplication and state the unit clause with it, in the sheaf section before `variable [HasDerivedCategory (ShQ Y)]`:

   ```lean
   /-- The unit multiplication `ℚ_Y[0] ⊗ ℚ_Y[0] ⟶ ℚ_Y[0]`: Mathlib's left unitor of complexes,
   typed as the `m` of `pairProductShQ`. Name it in statements; writing the unitor as `m` costs
   about 8 s of kernel time per declaration (instance diamond, `docs/gaps.md`). -/
   def unitComplexMul : (tensorRightComplex Y (unitComplex Y)).obj (unitComplex Y) ⟶ unitComplex Y :=
     (HomologicalComplex.leftUnitor (unitComplex Y)).hom

   /-- `unitComplexMul` is the left unitor, by definition. -/
   theorem unitComplexMul_eq :
       unitComplexMul Y = (HomologicalComplex.leftUnitor (unitComplex Y)).hom := rfl
   ```

   and restate the unit clause as

   ```lean
   theorem pairProductShQ_unit {a b n : ℤ} (h : a + b = n)
       (x : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj (unitComplex Y)) a)
       (y : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj (unitComplex Y)) b) :
       pairProductShQ Y 0 0 (unitComplexMul Y) h x y = y.comp x h :=
     tensorPairProduct_unit (hasE := hasB_shQ Y _) _ h x y
   ```

   Checked as written in RT7 (serial): `unitComplexMul` 17 s, `unitComplexMul_eq` 18.5 s, the restated unit clause 35 s (the present one: 30 to 35 s). With change 1 the build time is about unchanged, and each consumer statement saves about 8 s. `unitComplexMul_eq` is a pin; drop it if 18.5 s matters, since the docstring and `rfl` carry the same fact. This does not weaken the clause: `unitComplexMul Y` is `λ` by `rfl`, recorded by `unitComplexMul_eq`. If keeping the unitor spelling is preferred, keep the present theorem and add this one as `pairProductShQ_unit'`.
3. Sketch "pairing-product: statement": delete the sentence about the ledger naming `HodgeLadder/Pairing/Product.lean`; say 42 declarations; replace the `derivedTensorRightUnitIso` row; add the consumer-cost measurements of finding 5.
4. At posting: rebase on `main` (conflicts listed in section 8); `public import HodgeLadder.Hodge.PairingProduct` in `HodgeLadder.lean`; ledger `module` `HodgeLadder.Hodge.PairingProduct`, `declarations` at least `pairProduct`, `pairProduct_eq`, `pairProduct_add_left`, `pairProduct_add_right`, `pairProduct_naturality`, `pairProduct_unit`, `complexRightUnitor_hom_shift`, `complexLeftUnitor_tensorUnit_inv`, `tensorPairProduct_unit`, `unitComplex_eq_single_QX`, `pairProductShQ`, `pairProductShQ_add_left`, `pairProductShQ_add_right`, `pairProductShQ_naturality`, `pairProductShQ_unit`; ledger note: "the unit clause is proved generically from `derivedMapBifunctorRightIsoId` with `ρ` the right unitor; no sheaf-level unit iso". `docs/gaps.md` "To upstream" (Mathlib): `mapBifunctorShift₁Iso_hom_naturality₂` without a global `HasMapBifunctor` instance, `complexRightUnitor_hom_naturality`, `complexLeftUnitor_hom_naturality`, `complexRightUnitor_hom_shift`, `complexLeftUnitor_tensorUnit_inv` (unitors of complexes without the monoidal structure), and the generic `pairAction`, `pairProduct`. Add the consumer-cost rows of finding 5 to the existing "Known weaknesses" row on `mapBifunctorMap`.
5. For the `de-rham-cup` brief (no change here): state `wedge-sheaf-map`'s unit law as `HomologicalComplex.tensorHom u (𝟙 Ω•_ℚ) ≫ deRhamWedge X = (HomologicalComplex.leftUnitor Ω•_ℚ).hom` (the unitor of `complexLeftUnitor_hom_naturality`), and the scalar laws `(c • 𝟙 ⊗ 𝟙) ≫ μ = μ ≫ c • 𝟙`, `(𝟙 ⊗ c • 𝟙) ≫ μ = μ ≫ c • 𝟙`; pin `unitComplex (TopCat.of (ComplexPoint X)) = rationalUnitComplex X` by `rfl`; activate `main`'s local instances; name every sheaf-level map that enters a statement and write objects out in place of `_`.
