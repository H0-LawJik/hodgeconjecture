# Sketch: `cup-hodge-filtration`

Date: 2026-11-26. Front `cup`, decision 0009, item 8. Statements, route, sub-rungs and kill risks; amended after the red team (`docs/sketches/cup-hodge-filtration.redteam.md`, pass with changes). Modules: `HodgeLadder/Hodge/CupFiltration.lean` and the test `HodgeLadder/Tests/HodgeCupP2.lean`. The original rung is split: `cup-hodge-reduction` (checked), `form-wedge-leibniz` (checked), `cup-hodge-classes` (stated: (b) and (a_ℚ)), `cup-hodge-classes-test-p2` (checked), and `cup-hodge-filtration` (open), which keeps the complex form (a) that T1 needs.

## What upstream defines

All at the pin, `HodgeConjecture/Definitions/AlgebraicGeometry/Hodge/Filtration.lean`.

| Object | Upstream definition |
|---|---|
| `ℍ^n(X; C)` | `Localization.SmallShiftedHom` from `ℤ_X[0]` to `C` in degree `n`, in complexes of sheaves of abelian groups on `X(ℂ)` (`AnalyticAdditiveSheaf X`), inverting quasi-isomorphisms |
| `H_dR^n(X)` | `ℍ^n(X; Ω•(X))`, `Ω•(X)` the holomorphic de Rham complex (sheafified Kähler forms of holomorphic functions modulo forms vanishing in every chart), in degrees `0..dim X` |
| `F^p H_dR^n(X)` | `hodgeFiltration X p n`: the image of `ℍ^n(X; F^p Ω•) → ℍ^n(X; Ω•)`, `F^p Ω•` the stupid truncation in form degrees `≥ p` |
| `ι = fieldToDeRhamCohomology ℚ X n` | `H^n(X; ℚ) → H_dR^n(X)`, induced by `ℚ_X[0] → ℂ_X[0] → Ω•` |
| `deRhamConj` | conjugation of constant complex coefficients, transported through `H^n(X; ℂ) ≃ H_dR^n(X)` |
| `Hdg^p(X; ℚ)` | `hodgeClasses ℚ X p`: `α ∈ H^{2p}(X; ℚ)` with `ι α ∈ hodgePiece X p p (2p) = F^p ⊓ conj⁻¹(F^p)` |

Upstream has no product on `H_dR^*`, on `H^*(X; ℂ)` or on `ℍ^*`, and no wedge product of holomorphic forms. Mathlib has the tensor product of complexes (`Mathlib/Algebra/Homology/Monoidal.lean`, Koszul signs), its compatibility with shifts (`BifunctorShift.lean`, `CommShiftTwo.lean`), localization of monoidal structures (`Localization/Monoidal`), and shifts on localizations (`Shift/Localization.lean`). It has no statement that a tensor product preserves quasi-isomorphisms and no derived tensor product.

## The three parts of a Hodge class, and what is proved

A Hodge class is rational, satisfies the filtration condition `ι α ∈ F^p`, and satisfies the conjugate condition `deRhamConj (ι α) ∈ F^p`.

| Part | Closed under `cup`? | Status |
|---|---|---|
| rational | yes, by the type of `HodgeLadder.Cup.cup : H^p(X; ℚ) → H^q(X; ℚ) → H^n(X; ℚ)` | no proof needed |
| conjugate | follows from the filtration part for every rational class: `deRhamConj` fixes `ι α` (`deRhamConj_fieldToDeRhamCohomology`, checked) | `mem_hodgeClasses_iff_mem_hodgeFiltration`, proved |
| filtration | the content of the rung | open |

Checked, standard axioms:

- `mem_hodgeClasses_iff_mem_hodgeFiltration : α ∈ Hdg^p(X; ℚ) ↔ ι α ∈ hodgeFiltration X p (2p)`.
- `cupPreservesHodgeClasses_of_rational : CupRespectsHodgeFiltrationRational X → CupPreservesHodgeClasses X`, the reduction of (b) to the rational filtration form.
- `hodgeFiltration_eq_top_of_nonpos : p ≤ 0 → hodgeFiltration X p n = ⊤` and `mem_hodgeClasses_zero : α ∈ Hdg^0(X; ℚ)` (red team finding 1): the unit is a Hodge class, and (a_ℚ) holds for a degenerate reason when `p + q ≤ 0`.
- `Tests.projectivePlane_exists_hodge_cup_ne_zero`: on ℙ², `[L₀], [L₁] ∈ Hdg^1` with `[L₀] ∪ [L₁] ≠ 0`, so (b) has a nonvacuous instance and would give `[pt] ∈ Hdg^2(ℙ²; ℚ)`.
- `involute_of_mem_exteriorPower`, `formWedge_differential`: on upstream's algebraic forms, `d(θ ∧ η) = dθ ∧ η + (−1)^p θ ∧ dη`, from upstream's `Algebra.DeRham.extDeriv_mul`. This is Mathlib's Koszul sign for `ℤ`-indexed complexes (`ε₂(p, q) = (−1)^p`, `ComplexShape.ε_up_ℤ`), so the wedge product is a morphism of complexes with no sign twist.

## Statements

### (b) Products of Hodge classes (rung `cup-hodge-classes`, stated)

```lean
def CupPreservesHodgeClasses (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] : Prop :=
  ∀ (p q : ℕ) (α : H^(2 * p)(X; ℚ)) (β : H^(2 * q)(X; ℚ)),
    α ∈ Hdg^p(X; ℚ) → β ∈ Hdg^q(X; ℚ) →
    Cup.cup α β (2 * (p + q)) (by ring) ∈ Hdg^(p + q)(X; ℚ)
```

### (a_ℚ) Rational filtration form (rung `cup-hodge-classes`, stated)

```lean
def CupRespectsHodgeFiltrationRational (X) [IsIntegral X.left] [Smooth X.hom] : Prop :=
  ∀ (a b n : ℕ) (h : a + b = n) (p q : ℤ) (α : H^a(X; ℚ)) (β : H^b(X; ℚ)),
    fieldToDeRhamCohomology ℚ X a α ∈ hodgeFiltration X p a →
    fieldToDeRhamCohomology ℚ X b β ∈ hodgeFiltration X q b →
    fieldToDeRhamCohomology ℚ X n (Cup.cup α β n h) ∈ hodgeFiltration X (p + q) n
```

Membership in `F^{p+q}` is unchanged by a sign or by swapping the factors, so (a_ℚ) and (b) do not depend on the cup convention.

### (a) Complex form (rung `cup-hodge-filtration`, open; `deRhamCup` from sub-rung `de-rham-cup`)

(a) cannot be stated on upstream definitions alone, since upstream has no product on `H_dR^*`. The planned local definition and statements:

```lean
/-- `deRhamCup x y` is `pairProduct (deRhamWedge X) y x`, diagrammatic order as `Cup.cup`. -/
def deRhamCup {a b : ℤ} (x : H_dR^a(X)) (y : H_dR^b(X)) (n : ℤ) (h : a + b = n) : H_dR^n(X)

theorem fieldToDeRhamCohomology_cup {a b n : ℕ} (h : a + b = n)
    (α : H^a(X; ℚ)) (β : H^b(X; ℚ)) :
    fieldToDeRhamCohomology ℚ X n (Cup.cup α β n h) =
      deRhamCup X (fieldToDeRhamCohomology ℚ X a α) (fieldToDeRhamCohomology ℚ X b β) n
        (by omega)

theorem deRhamCup_mem_hodgeFiltration {a b n : ℤ} (h : a + b = n) {p q : ℤ}
    {x : H_dR^a(X)} {y : H_dR^b(X)}
    (hx : x ∈ hodgeFiltration X p a) (hy : y ∈ hodgeFiltration X q b) :
    deRhamCup X x y n h ∈ hodgeFiltration X (p + q) n
```

with `deRhamCup_add_left`, `deRhamCup_add_right`, `deRhamCup_smul_left (c : ℂ)`, `deRhamCup_smul_right (c : ℂ)` for upstream's complex structure (`deRham_complex_smul_eq`). The factor swap sits in the definition (red team finding 5): the primitive `pairProduct m x y = y ≫ (x ⊗ B)⟦b⟧` is `y.comp x` on `ℚ_X[0]`, so `deRhamCup x y := pairProduct μ y x` makes `ι` a homomorphism, exact, with no sign. Rule for the ladder: sheaf-side products (`Cup.cup`, `deRhamCup`) are diagrammatic; cochain and form products (`cupSing`, `relCupSing`, `formWedge`) are classical; comparisons between the two reverse the factors with no sign (conventions row "de Rham cup order (proposed)").

The zero product satisfies (a) and bilinearity; `fieldToDeRhamCohomology_cup` and the test `de-rham-cup-test-p2` (`deRhamCup (ι [L₀]) (ι [L₁]) ≠ 0` on ℙ², with `de-rham-injective`) are what pin `deRhamCup` to the cup product.

(a_ℚ) follows from (a) and `fieldToDeRhamCohomology_cup` in three lines.

## Construction of the product

Work in sheaves of `ℚ`-vector spaces `ShQ` on `X(ℂ)`, where the rational cup already lives (`rationalExtEquiv`) and the tensor product is exact (`tensor_exact`, rung `sheaf-tensor-exact`). The complex structure of the forms plays no part in membership; complex scalars act through chain maps.

1. `Ω•_ℚ`: the de Rham complex in `CochainComplex (ShQ X(ℂ)) ℤ`, sheafifying the presheaf `U ↦ HolomorphicForm X d U p` as `ℚ`-modules, with `forget(Ω•_ℚ) ≅ Ω•(X)` (sheafification commutes with the forgetful functor, `preservesSheafification_U`), its truncations `F^p Ω•_ℚ`, and the unit `u : ℚ_X[0] → Ω•_ℚ` over `fieldToHolomorphicDeRhamComplexInt ℚ X`.
2. Wedge `μ : Ω•_ℚ ⊗ Ω•_ℚ → Ω•_ℚ`: `formWedge` descends to the quotient (`wedge-descends`), is natural under restriction (upstream's `formRestriction` is induced by an algebra map), sheafifies through the monoidal sheafification functor, and is a chain map by `formWedge_differential`. It restricts to `μ_{p,q} : F^p ⊗ F^q → F^{p+q}`, and `μ ∘ (u ⊗ 𝟙) = λ` up to the unitor (`1 ∧ ω = ω`).
3. For a bounded complex `B`, the derived functor `T_B := Localization.lift (tensorRight B ⋙ Q) _ Q` of `− ⊗ B` on `D(ShQ)`: `− ⊗ B` inverts quasi-isomorphisms (`tensor-bounded-quasi-iso`). The pairing applies `T_B` to unshifted objects only and uses `Q`'s `commShiftIso` with the no-sign `mapBifunctorShift₁Iso`, so no `CommShift` on `T_B` is needed. `T_B` is additive by `Localization.functor_additive_iff` on the homotopy category, after descending `tensorRight B` with `mapBifunctorMapHomotopy₁`. A chain map `B → B'` gives a natural transformation `T_B ⇒ T_{B'}`.
4. Pairing product. For bounded `A, B, C`, a chain map `m : A ⊗ B → C`, `x : ℚ → A[a]` and `y : ℚ → B[b]` in `D(ShQ)`:
   `pairProduct m x y := y ≫ (λ⁻¹ ≫ T_B(x) ≫ shift₁ ≫ m[a])[b]`, a morphism `ℚ → C[a + b]`.
   It is natural in `(A, B, C, m)` along chain maps, biadditive, and on `A = B = C = ℚ_X[0]`, `m = λ`, it is Yoneda composition: `pairProduct λ x y = y.comp x`, so `α ∪ β = pairProduct λ β α` for the checked cup.
5. Bridge: `ℍ^n(X; forget C) ≃+ Hom_{D(ShQ)}(ℚ_X[0], C[n])`, natural in `C`, from the exact adjunction `ℚ ⊗ − ⊣ forget` on complexes (the complex version of `Adjunction.extEquiv`), agreeing with `rationalExtEquiv` and `hypercohomologyAddEquivConstantCohomology` on `C = ℚ_X[0]` (with the checked `ext-derived-bridge`).
6. `deRhamCup x y` := the bridge applied to `pairProduct μ y x`. Then (a) is naturality of `pairProduct` along the inclusions `F^p → Ω•` and `μ_{p,q}`; `fieldToDeRhamCohomology_cup` is naturality along `u` (multiplicative by step 2) together with step 4 on `ℚ_X[0]`.

## Sub-rungs, in order

Ledger rungs; `rational-hypercohomology-equiv` comes first (red team finding 9), since it is independent of the tensor and is the cheapest probe of the instance spellings.

| Id | Statement | Status |
|---|---|---|
| `cup-hodge-reduction` | `mem_hodgeClasses_iff_mem_hodgeFiltration`, `cupPreservesHodgeClasses_of_rational`, `hodgeFiltration_eq_top_of_nonpos`, `mem_hodgeClasses_zero` | checked |
| `form-wedge-leibniz` | `formWedge`, `involute_of_mem_exteriorPower`, `formWedge_differential` | checked |
| `rational-hypercohomology-equiv` | `rationalHypercohomologyEquiv (C) (n : ℤ) : ℍ^n(X; forget C) ≃+ ShiftedHom (Q.obj ℚ_X[0]) (Q.obj C) n`, natural in `C`, agreeing with `rationalExtEquiv` on `ℚ_X[0]` with no scalar | open |
| `wedge-descends` | `WedgeDescends`: `chartEvaluationKernel` is a two-sided ideal for `formWedge` | stated |
| `tensor-bounded-quasi-iso` | `TensorBoundedQuasiIso`: `QuasiIso (tensorHom f (𝟙 M))` for `M` strictly bounded, with `HasTensor` hypotheses | stated |
| `rational-de-rham-complex` | `Ω•_ℚ` with `forget(Ω•_ℚ) ≅ Ω•(X)`, truncations `F^p`, unit over `fieldToHolomorphicDeRhamComplexInt ℚ X` | open |
| `wedge-presheaf` | `formWedge` descends to `HolomorphicForm X d U`, natural under `holomorphicFormRestriction` | open |
| `wedge-sheafify` | `Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ` through the monoidal sheafification | open |
| `wedge-sheaf-map` | `deRhamWedge` a morphism of complexes, `filteredWedge p q` compatible with inclusions, unit law | open |
| `derived-tensor-bounded` | additive `T_B` with `Q ⋙ T_B ≅ tensorRight B ⋙ Q`, natural in `B` | open |
| `pairing-product` | `pairProduct`, naturality, biadditivity, `pairProduct λ x y = y.comp x` on `ℚ_X[0]` | open |
| `de-rham-injective` | `Function.Injective (fieldToDeRhamCohomology ℚ X n)` | open |
| `de-rham-cup` | `deRhamCup`, bilinearity, `fieldToDeRhamCohomology_cup` | open |
| `de-rham-cup-test-p2` | `deRhamCup (ι [L₀]) (ι [L₁]) 4 _ ≠ 0` on `projectivePlane` | open |
| `cup-hodge-filtration` | `deRhamCup_mem_hodgeFiltration`, statement (a) | open |
| `cup-hodge-classes` | `CupPreservesHodgeClasses`, `CupRespectsHodgeFiltrationRational` | stated |
| `cup-hodge-classes-test-p2` | `Tests.projectivePlane_exists_hodge_cup_ne_zero` | checked |
| `de-rham-cup-antisymm-h1` | antisymmetry of `deRhamCup` on `H¹_dR × H¹_dR` (T1 input) | open |
| `de-rham-rational-span` | `Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤`, X projective (T1 input) | open |

## What T1 needs from this rung

T1 (Weil classes on an abelian surface of Weil type, `docs/notes/2026-11-25-markman-inventory.md` §6) shows that a rational class `w ∈ W_K` has `ι w ∈ F^1`. Its complexification is a combination of products of classes in `H^{1,0} ⊂ F^1` and `H^{0,1} ⊂ F^0`, which are complex, not rational. T1 therefore needs (a) for complex classes, the ℂ-bilinearity of `deRhamCup`, and `fieldToDeRhamCohomology_cup`, more than (b). The conjugate condition comes for free, since `w` is rational. T1 also needs `H^1_dR = F^1 ⊕ conj F^1` on an abelian surface (outside this front), antisymmetry of `deRhamCup` on `H^1` (`de-rham-cup-antisymm-h1`) and the span of the rational image (`de-rham-rational-span`). This is why (a) keeps the id `cup-hodge-filtration` and (b) has its own id.

## Kill risks

1. **Derived tensor (main risk).** Steps 3 and 4 are Mathlib-level: quasi-isomorphism invariance of `− ⊗ B` for bounded `B`, the lift through the localization, its additivity, and naturality in `B`. The red team removed the `CommShift` requirement (finding 6). Each piece has Mathlib support (`HomologySequenceLemmas`, `Shift/Localization.lean`, `BifunctorShift.lean`), but their combination has not been assembled at the pin. A kill would be an obstruction to additivity of the lift. Last-resort fallback: a roof-level definition, which must reprove independence of the roof.
2. **Instance synthesis.** `inferInstance` for `HomologicalComplex.HasTensor K M` on `CochainComplex (ShQ Y) ℤ` ran over five minutes without an answer, and so did a direct `hasColimitsOfShape_discrete` probe (scratch, 2026-11-26). The statements therefore carry `HasTensor` hypotheses; the sub-rung must give the instances as explicit terms. `(curriedTensor (ShQ Y)).Additive` was missing and is now the instance `curriedTensor_additive`.
3. **Wedge descent.** Upstream's holomorphic forms are a quotient by forms vanishing in every chart. If chart evaluation were not multiplicative, `μ` would not descend; it is (pointwise wedge of covectors), but the Lean proof goes through upstream's `chartEvaluation` and `wedgeCovectors`, which are stated for generators `mk a₀ v`.
4. **Bridge bookkeeping.** Upstream's `ℍ` uses `SmallShiftedHom.{1}` over `AnalyticAdditiveSheaf X`, with source `ℤ_X[0]` extended from `ℕ`, while the product lives in `D(ShQ)`. The compatibility with `rationalExtEquiv` passes through `hypercohomologyAddEquivConstantCohomology`, the `ULift ℤ` identification and `ext-derived-bridge`. Low risk of failure, high risk of effort.
5. **Order and sign.** Membership statements (a), (a_ℚ), (b) are independent of both. The identity `fieldToDeRhamCohomology_cup` is not; it is exact with the order reversed and no sign under the left-action definition above. A wrong expectation here would be caught by the kernel, and it matters for T1's linear algebra over `K`.
6. **Vacuity.** Settled for (b) by `cup-hodge-classes-test-p2`. A Lean test with `F^{p+q} ≠ ⊤` in positive degree needs Hodge theory and is out of reach; recorded as a known weakness.

## Conventions

Registered by the red team in `docs/conventions.md`: "Tensor product of ℤ-indexed cochain complexes and its shifts", "Wedge product of algebraic forms", "de Rham cup order (proposed)", "Rational-to-de Rham map and the range of F^p".

## Issue body (`cup-hodge-filtration`)

> **Rung `cup-hodge-filtration`** (front `cup`, open). Prove `deRhamCup_mem_hodgeFiltration`: for `x ∈ hodgeFiltration X p a` and `y ∈ hodgeFiltration X q b`, `deRhamCup X x y n h ∈ hodgeFiltration X (p + q) n`, where `deRhamCup` is the de Rham cup of sub-rung `de-rham-cup` (`deRhamCup x y := pairProduct μ y x`, pinned by `ι (α ∪ β) = deRhamCup (ι α) (ι β)`). Depends on `de-rham-cup`, `wedge-sheaf-map`, `de-rham-cup-test-p2`. Start with `rational-hypercohomology-equiv`, then `tensor-bounded-quasi-iso` (`HodgeLadder.TensorBoundedQuasiIso`) and `wedge-descends` (`HodgeLadder.WedgeDescends`), both stated in `HodgeLadder.Hodge.CupFiltration`. Route and signatures: `docs/sketches/cup-hodge-filtration.md`; red team: `docs/sketches/cup-hodge-filtration.redteam.md`. The statement for rational classes and for Hodge classes is rung `cup-hodge-classes` (stated), reduced to the rational filtration form by the checked `cup-hodge-reduction`.
