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
| `rational-hypercohomology-equiv` | `rationalHypercohomologyEquiv (C) (n : ℤ) : ℍ^n(X; forget C) ≃+ ShiftedHom (Q.obj ℚ_X[0]) (Q.obj C) n`, natural in `C`, agreeing with `rationalExtEquiv` on `ℚ_X[0]` with no scalar | checked |
| `wedge-descends` | `WedgeDescends`: `chartEvaluationKernel` is a two-sided ideal for `formWedge` | checked |
| `tensor-bounded-quasi-iso` | `TensorBoundedQuasiIso`: `QuasiIso (tensorHom f (𝟙 M))` for `M` strictly bounded, with `HasTensor` hypotheses | checked |
| `rational-de-rham-complex` | `Ω•_ℚ` with `forget(Ω•_ℚ) ≅ Ω•(X)`, truncations `F^p`, unit over `fieldToHolomorphicDeRhamComplexInt ℚ X` | checked |
| `wedge-presheaf` | `formWedge` descends to `HolomorphicForm X d U`, natural under `holomorphicFormRestriction` | checked |
| `wedge-sheafify` | `Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ` through the monoidal sheafification | checked |
| `wedge-sheaf-map` | `deRhamWedge` a morphism of complexes, `filteredWedge p q` compatible with inclusions, unit law | open |
| `derived-tensor-bounded` | additive `T_B` with `Q ⋙ T_B ≅ tensorRightComplex Y B ⋙ Q`, natural in `B`; generic unit iso | checked |
| `pairing-product` | `pairProduct`, naturality, biadditivity, `pairProduct λ x y = y.comp x` on `ℚ_X[0]` | checked |
| `de-rham-injective` | `Function.Injective (fieldToDeRhamCohomology ℚ X n)` | checked |
| `de-rham-cup` | `deRhamCup`, bilinearity, `fieldToDeRhamCohomology_cup` | open |
| `de-rham-cup-test-p2` | `deRhamCup (ι [L₀]) (ι [L₁]) 4 _ ≠ 0` on `projectivePlane` | open |
| `cup-hodge-filtration` | `deRhamCup_mem_hodgeFiltration`, statement (a) | open |
| `cup-hodge-classes` | `CupPreservesHodgeClasses`, `CupRespectsHodgeFiltrationRational` | stated |
| `cup-hodge-classes-test-p2` | `Tests.projectivePlane_exists_hodge_cup_ne_zero` | checked |
| `de-rham-cup-antisymm-h1` | antisymmetry of `deRhamCup` on `H¹_dR × H¹_dR` (T1 input) | open |
| `de-rham-rational-span` | `Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤`, X projective (T1 input) | checked (`deRhamRationalSpan`, with `simplicial-complex-span`; #192) |

## wedge-presheaf: statement

Module `HodgeLadder/Hodge/WedgePresheaf.lean` (`HodgeLadder.Hodge.WedgePresheaf`), not yet imported from `HodgeLadder.lean`. The module path is `HodgeLadder/Hodge/WedgePresheaf.lean` (red team 2026-11-27). Every declaration below elaborates and is proved, with the three standard axioms only (`#print axioms`, 2026-11-26). The file checks in about 10 s with `lake env lean`; `lake build HodgeLadder.Hodge.WedgePresheaf` built it in 8.5 s.

Upstream's `chartEvaluationKernel X d U p` is a `ℂ`-submodule, so `HolomorphicForm X d U p` is a `ℂ`-module and the wedge is `ℂ`-bilinear. An `𝒪(U)`-module structure on the quotient is absent at the pin and is left out.

| Declaration | Statement | Proof |
|---|---|---|
| `formWedgeBilin R A p q` | `Form R A p →ₗ[R] Form R A q →ₗ[R] Form R A (p + q)`, `LinearMap.mk₂` of `formWedge` | bilinearity of multiplication in `⋀_A Ω_{A/R}` |
| `map_formWedge f θ η` | `Algebra.DeRham.map R f (p + q) (formWedge θ η) = formWedge (map R f p θ) (map R f q η)` for `f : A →ₐ[R] B` | `map_mul` of upstream's `extAlgMap` |
| `holomorphicWedge X d U p q` | `HolomorphicForm X d U p →ₗ[ℂ] HolomorphicForm X d U q →ₗ[ℂ] HolomorphicForm X d U (p + q)` | `LinearMap.liftQ₂` of `mkQ ∘ formWedgeBilin`, kernels by the two sides of `wedgeDescends` |
| `holomorphicWedge_mk θ η` | `holomorphicWedge [θ] [η] = [formWedge θ η]` | `rfl` |
| `holomorphicFormRestriction_holomorphicWedge i a b` | `holomorphicFormRestriction X d i (p + q) (a ∧ b) = (res i p a) ∧ (res i q b)` | representatives, `formRestriction = Algebra.DeRham.map`, `map_formWedge` |
| `holomorphicFormCast X d U h` | `HolomorphicForm X d U m →ₗ[ℂ] HolomorphicForm X d U n` for `h : m = n`, `h ▸ LinearMap.id` | definition; `holomorphicFormCast_mk` says it keeps the element of the exterior algebra |
| `holomorphicFormDifferential_holomorphicWedge a b` | `d (a ∧ b) = cast (Nat.add_right_comm p 1 q) (da ∧ b) + (-1 : ℤ)^p • (a ∧ db)` in `HolomorphicForm X d U (p + q + 1)` | representatives and `formWedge_differential` |
| `holomorphicWedge_ofConstant_left c b` | `[c] ∧ b = cast (Nat.zero_add q).symm (c • b)` | representatives |
| `holomorphicWedge_ofConstant_right a c` | `a ∧ [c] = c • a` | representatives |

Degrees in the Leibniz rule. The three terms live in `(p + q) + 1`, `(p + 1) + q` and `p + (q + 1)`. The first and third agree by `rfl`, so only `da ∧ b` carries a transport. The sign is Mathlib's Koszul sign `(−1)^p`, the one registered for `formWedge_differential` in `docs/conventions.md`, and no new convention enters. Writing out the degree identification in the proof (rewriting under the definitional cast) ran past the heartbeat limit; the proof goes through the auxiliary `holomorphicFormDifferential_formWedge_mk`, which states the identity on representatives with both transports explicit.

Trivial proofs fail: `rfl` and `simp` on naturality, and `simp` on the Leibniz rule, are rejected.

Questions for the red team. (1) Is a pointwise naturality statement enough for `wedge-sheafify`, or should it be the equation of bilinear maps `(holomorphicWedge X d V p q).compl₁₂ (res i p) (res i q) = (holomorphicWedge X d U p q).compr₂ (res i (p + q))`? (2) Is `holomorphicFormCast` by `h ▸ LinearMap.id` the right transport, against a `Submodule.mapQ` of `LinearEquiv.ofEq` on `⋀^m = ⋀^n`? (3) The unit laws are included for step 2 of the construction (`1 ∧ ω = ω`); check that they are in scope for this rung.

Red team 2026-11-27 (`docs/sketches/wedge-presheaf.redteam.md`): pass with changes, all implemented. Answers: the pointwise naturality is primary, with the bilinear-map form `holomorphicWedge_compr₂_restriction` added; the transport `h ▸ LinearMap.id` stays, with five lemmas proved by `subst h; rfl` (`holomorphicFormCast_trans`, `holomorphicFormRestriction_holomorphicFormCast`, `holomorphicFormDifferential_holomorphicFormCast`, `eqToHom_apply_eq_holomorphicFormCast`, `XIsoOfEq_hom_app_eq_holomorphicFormCast`); the unit laws are in scope. Added tests: `holomorphicWedge_ofConstant_one_ne_zero` (`[1] ∧ [1] ≠ 0` on a nonempty open) and `holomorphicWedge_ofFunction` (degree zero is multiplication of functions). The module is imported from `HodgeLadder.lean` and the rung is checked.
## derived-tensor-bounded: statement
Module `HodgeLadder.Hodge.DerivedTensorBounded` (file `HodgeLadder/Hodge/DerivedTensorBounded.lean`, imported from `HodgeLadder.lean`; the ledger rung `derived-tensor-bounded` names this module). Checked: every declaration below is proved with the three standard axioms. Red team: `docs/sketches/derived-tensor-bounded.redteam.md`, pass with changes, implemented (the two `rfl` pins against `Functor.map₂CochainComplex`, the generic unit iso).
Two layers. The generic layer works for any bifunctor `F : C₁ ⥤ C₂ ⥤ D` of abelian categories, additive in each variable, with `[HasDerivedCategory C₁] [HasDerivedCategory D]` as arguments (no choice of model) and the inversion of quasi-isomorphisms as a hypothesis `hB`. The sheaf layer sets `F = curriedTensor (ShQ Y)` and discharges `hB` with `tensorBoundedQuasiIso_holds`.
| Declaration | Statement |
|---|---|
| `mapBifunctorRight F B` | `CochainComplex C₁ ℤ ⥤ CochainComplex D ℤ`, `K ↦ mapBifunctor K B F (.up ℤ)`, `f ↦ mapBifunctorMap f (𝟙 B) F (.up ℤ)`; needs `[∀ K, HasMapBifunctor K B F (.up ℤ)]` |
| `mapBifunctorRightMap F φ` | for `φ : B ⟶ B'`, the natural transformation with components `mapBifunctorMap (𝟙 K) φ F (.up ℤ)`; `_id`, `_comp` |
| `mapBifunctorRight_additive` | instance `(mapBifunctorRight F B).Additive` |
| `mapBifunctorRight_eq_map₂CochainComplex`, `mapBifunctorRightMap_eq_map₂CochainComplex` | `mapBifunctorRight F B = F.map₂CochainComplex.flip.obj B` and `mapBifunctorRightMap F φ = F.map₂CochainComplex.flip.map φ`, both `rfl` |
| `derivedMapBifunctorRight F B hB` | `Localization.lift (mapBifunctorRight F B ⋙ Q) hB Q : DerivedCategory C₁ ⥤ DerivedCategory D`, for `hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ Q)` |
| `derivedMapBifunctorRightFacIso F B hB` | `Q ⋙ derivedMapBifunctorRight F B hB ≅ mapBifunctorRight F B ⋙ Q` (`Localization.fac`) |
| `derivedMapBifunctorRight_additive` | instance `(derivedMapBifunctorRight F B hB).Additive` |
| `derivedMapBifunctorRightMap F hB hB' φ` | `derivedMapBifunctorRight F B hB ⟶ derivedMapBifunctorRight F B' hB'` (`Localization.liftNatTrans`) |
| `derivedMapBifunctorRightMap_fac` | `whiskerLeft Q (T φ) ≫ (facIso B').hom = (facIso B).hom ≫ whiskerRight (mapBifunctorRightMap F φ) Q` |
| `derivedMapBifunctorRightMap_app` | `(T φ).app (Q.obj K) = (facIso B).hom.app K ≫ Q.map ((mapBifunctorRightMap F φ).app K) ≫ (facIso B').inv.app K` |
| `derivedMapBifunctorRightMap_unique` | any `τ` satisfying the `_fac` square equals `T φ` |
| `derivedMapBifunctorRightMap_id`, `_comp` | `T (𝟙 B) = 𝟙`, `T (φ ≫ ψ) = T φ ≫ T ψ` |
| `derivedMapBifunctorRightIsoId F B hB ρ`, `_hom_app` | for one abelian `C` and `ρ : mapBifunctorRight F B ≅ 𝟭`, an iso `derivedMapBifunctorRight F B hB ≅ 𝟭` (`Localization.liftNatIso`) with component `(facIso B).hom.app K ≫ Q.map (ρ.hom.app K)` at `Q.obj K` |
| `tensorRightComplex Y B`, `tensorRightComplexMap Y φ` | `mapBifunctorRight (curriedTensor (ShQ Y)) B` and its map; `_obj`, `_map`, `_app` pin them by `rfl` to `HomologicalComplex.tensorObj K B`, `tensorHom f (𝟙 B)`, `tensorHom (𝟙 K) φ` |
| `tensorRightComplex_isInvertedBy Y B a b` | `[B.IsStrictlyGE a] [B.IsStrictlyLE b]`: `(quasiIso (ShQ Y) (.up ℤ)).IsInvertedBy (tensorRightComplex Y B ⋙ Q)` |
| `derivedTensorRight Y B a b` | `T_B : DerivedCategory (ShQ Y) ⥤ DerivedCategory (ShQ Y)`; `derivedTensorRight_bounds`: independent of `a, b` (`rfl`) |
| `derivedTensorRightFacIso Y B a b` | `Q ⋙ T_B ≅ tensorRightComplex Y B ⋙ Q` |
| `derivedTensorRight_additive` | instance `(derivedTensorRight Y B a b).Additive` |
| `derivedTensorRightMap Y a b a' b' φ` | `T_B ⟶ T_{B'}` for `φ : B ⟶ B'`; `_fac`, `_app`, `_unique`, `_id`, `_comp` as in the generic layer |
**Signs.** None. `T_B` is built on unshifted objects; no `CommShift` structure is defined or used (red team finding 6). The only convention is Mathlib's tensor product of complexes (conventions row "Tensor product of ℤ-indexed cochain complexes and its shifts": ε₁ = 1, ε₂(p, q) = (−1)^p), which enters through `tensorObj` and is pinned by `tensorRightComplex_obj`. The components of `T_φ` are `Q.map (𝟙_K ⊗ φ)` conjugated by the factorization isos, with no scalar.
**Route for additivity.** Simpler than finding 6: `Localization.functor_additive_iff` along `Qh` (left calculus of fractions on `HomotopyCategory.quasiIso`) reduces to `Qh ⋙ T_B`; precomposed with the quotient `CochainComplex ⥤ HomotopyCategory` it is isomorphic, through `quotientCompQhIso` and the factorization iso, to `tensorRightComplex Y B ⋙ Q`, which is additive; `Functor.additive_of_full_essSurj_comp` along the quotient (full, essentially surjective) concludes. The descent of `− ⊗ B` to the homotopy category (`mapBifunctorMapHomotopy₁`) is unnecessary.
**Choices for the red team.**
1. `tensorRightComplex` plays the role of `tensorRight B`. Mathlib's `MonoidalCategory` instance on complexes asks for `HasTensor` on all pairs plus the associator conditions `HasGoodTensor₁₂`, `HasGoodTensor₂₃` on all triples; the functor is defined directly and pinned to `tensorObj`, `tensorHom` by `rfl`.
2. Boundedness is an argument (`a b` with `IsStrictlyGE`, `IsStrictlyLE`), used only to discharge `hB`; mathematically `− ⊗ B` is exact on all complexes of sheaves of `ℚ`-vector spaces, but the checked input `tensor-bounded-quasi-iso` covers bounded `B`.
3. `HasDerivedCategory (ShQ Y)` is an instance argument, so the statements hold for every model, including the `HasDerivedCategory.standard` instance used elsewhere.
4. Not stated: `T_B` additive in `φ` (`T_{φ + ψ} = T_φ + T_ψ`), not needed. The sheaf unit iso `T_{𝟙} ≅ 𝟭` (from `derivedMapBifunctorRightIsoId` with `ρ` built from `HomologicalComplex.rightUnitor` and its naturality in `K`) is left to `pairing-product`, whose last clause needs it (ledger note there).
**Trivial proofs fail.** Checked in scratch: with the instance `derivedMapBifunctorRight_additive` removed, `infer_instance` finds no `Additive` instance; `rfl` fails for `derivedMapBifunctorRightMap_app` and for `derivedMapBifunctorRightMap_id`; `simp` with the definitions unfolded leaves `derivedMapBifunctorRightMap_app` open.
**Instance findings and timings.**
- `inferInstance` for `(derivedTensorRight Y B a b).Additive` ran over five minutes without an answer; the instance is given as a term. All `HasMapBifunctor` instances on `CochainComplex (ShQ Y) ℤ` are passed by name (`hasB := hasB_shQ Y B`), from `shQ_hasCoproducts`.
- Kernel cost: each declaration that applies the generic homological layer at `ShQ Y` spends about 2.5 s per distinct application in kernel type checking (`tensorRightComplex_map` 18 s, `tensorRightComplex_isInvertedBy` 18 s, `derivedTensorRightMap_app` 11 s). Diagnostics show the kernel unfolding `HasMapBifunctor` and `mapBifunctorHomologicalComplexObj` to compare two `HasZeroMorphisms (ShQ Y)` instances: the one found by search (`ObjectProperty.instHasZeroMorphismsFullSubcategory`, through `Functor.FullyFaithful.hasZeroMorphisms`) and the one derived from `sheafIsAbelian` (`Preadditive.preadditiveHasZeroMorphisms`). Local high-priority instances for the `Abelian` path did not remove it. Stating `HasMapBifunctorRight` in the abelian context removed the cost from `hasB_shQ`. The whole file takes about two minutes with `lake env lean`; downstream rungs pay the same per application.

## de-rham-injective: statement

Module `HodgeLadder.Hodge.DeRhamInjective` (new, not yet imported from the root). Red team 7b and recommended change 9 ask for it: the ℙ² test `deRhamCup (ι [L₀]) (ι [L₁]) ≠ 0` follows from a nonzero rational cup through this rung and `fieldToDeRhamCohomology_cup`.

```lean
theorem HodgeLadder.fieldToDeRhamCohomology_rat_injective (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    Function.Injective (fieldToDeRhamCohomology ℚ X n)

theorem HodgeLadder.ker_fieldToDeRhamCohomologyLinear_rat (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    LinearMap.ker (fieldToDeRhamCohomologyLinear ℚ X n) = ⊥
```

**Hypotheses.** `IsIntegral X.left` and `Smooth X.hom` are exactly the instance arguments of upstream's `fieldToDeRhamCohomology`; `n : ℕ` is its degree argument. There is no other hypothesis: no properness, no finite type beyond smoothness, no finite-dimensionality of `H^n(X; ℚ)`. The `Algebra ℚ ℂ` instance is the one found by search (`DivisionRing.toRatAlgebra`), the same one upstream's `hodgeClasses ℚ X p` elaborates with.

**Proof.** One line: upstream's `AlgebraicGeometry.ComplexPoint.fieldToDeRhamCohomology_injective ℚ X n`, in its `Other` library (`Other.AlgebraicGeometry.Hodge.Filtration`, built at the pin, already imported by `HodgeLadder.Cup.SingularUnit`). Its route is the one in the ledger note. `ι` factors as `fieldToComplexCohomology ℚ X n : H^n(X; ℚ) → H^n(X; ℂ)` followed by `complexConstantCohomologyDeRhamEquiv X n` (`fieldToDeRhamCohomology_factor`, from `hypercohomologyMap_comp_apply`). The equivalence comes from the holomorphic Poincaré lemma. The first map has the left inverse `complexToFieldCohomology ℚ X n` (`complexToFieldCohomology_leftInverse`), the hypercohomology map of the constant-sheaf map of `complexToFieldLinear ℚ : ℂ →ₗ[ℚ] ℚ`, a retraction of `algebraMap ℚ ℂ` chosen with `Classical.choose` from `LinearMap.exists_leftInverse_of_injective`. The kernel form is `LinearMap.ker_eq_bot`.

**Axioms.** Both declarations: `propext`, `Classical.choice`, `Quot.sound` (`#print axioms`, scratch).

**Non-vacuity.** The hypotheses hold for `Spec ℂ` (rung `nonvacuity-tests`). For smooth projective integral `X`, `HodgeLadder.Tests.hodge_zero_ne_bot` gives a nonzero class in `H^0(X; ℚ)`, so there the conclusion separates elements of a nonzero group. Injectivity is a strict condition: the zero map, for one, fails it on any nonzero `H^n(X; ℚ)`.

**General lemma (decision 0011).** None added. Upstream states the result for every field `K` with `[Algebra K ℂ]`; this rung pins it at `K = ℚ` under a ladder name. Nothing goes to `docs/gaps.md`.

**Path.** The ledger's generated path is `HodgeLadder/De/Rham/Injective.lean`; the module sits under `HodgeLadder/Hodge/` next to `Conjugation` and `CupFiltration`. Set `module` in the ledger to `HodgeLadder.Hodge.DeRhamInjective` when the rung is posted.

**Timings.** `lake env lean` on the file: 19 s wall. `lake build HodgeLadder.Hodge.DeRhamInjective`: 5 s for the module.

## pairing-product: statement

Module `HodgeLadder.Hodge.PairingProduct` (file `HodgeLadder/Hodge/PairingProduct.lean`), imported from `HodgeLadder.lean`; the ledger rung `pairing-product` names this module and is checked. Every declaration below elaborates and is proved; `#print axioms` on all 42 declarations gives `[propext, Classical.choice, Quot.sound]` (2026-11-27). Red team: `docs/sketches/pairing-product.redteam.md`, pass with changes, implemented (drop the unused sheaf unit iso, name the unit multiplication `unitComplexMul`).

Three layers. The generic layer works for one abelian category `C`, a bifunctor `F : C ⥤ C ⥤ C` additive in each variable, `[HasDerivedCategory C]`, a complex `E` (the unit), and for each `B` the hypotheses of `derivedMapBifunctorRight` (`hasB`, and `hB`: `− ⊗ B` inverts quasi-isomorphisms). The tensor layer sets `F = curriedTensor C` for an abelian monoidal `C` with Mathlib's preservation instances, `E = HomologicalComplex.tensorUnit C (.up ℤ)` and `lam` the left unitor of complexes. The sheaf layer instantiates the tensor layer once at `ShQ Y`, with `hB = tensorRightComplex_isInvertedBy`. Notation: `K ⊗ B` is `mapBifunctor K B F`; `T_B` is `derivedMapBifunctorRight F B hB`; `fac` its factorization iso; `cs` is `Q.commShiftIso`.

| Declaration | Statement |
|---|---|
| `mapBifunctorRightShiftIso F B A a` | `(A⟦a⟧) ⊗ B ≅ (A ⊗ B)⟦a⟧`, Mathlib's `mapBifunctorShift₁Iso` (no sign), typed through `mapBifunctorRight` |
| `mapBifunctorShift₁Iso_hom_naturality₂` | naturality of `mapBifunctorShift₁Iso` in the second variable along `g : B ⟶ B'`, under `HasMapBifunctor` for the two pairs only (Mathlib has it under a global instance) |
| `pairAction F E hB lam m x` | for `lam : E ⊗ B ≅ B`, `m : A ⊗ B ⟶ D`, `x : ShiftedHom (Q E) (Q A) a`: `Q lam⁻¹ ≫ fac⁻¹_E ≫ T_B (x ≫ cs⁻¹_A) ≫ fac_{A⟦a⟧} ≫ Q (shift₁ ≫ m⟦a⟧) ≫ cs_D : ShiftedHom (Q B) (Q D) a` |
| `pairProduct F E hB lam m h x y` | for `h : a + b = n`, `y : ShiftedHom (Q E) (Q B) b`: `y.comp (pairAction F E hB lam m x) h : ShiftedHom (Q E) (Q D) n` |
| `pairProduct_eq` | `pairProduct … = y ≫ (pairAction … x)⟦b⟧' ≫ (shiftFunctorAdd' _ a b n h).inv.app _` (`rfl`) |
| `pairAction_add`, `pairProduct_add_left`, `pairProduct_add_right` | additive in `x` (through `T_B.Additive`) and in `y` |
| `pairProduct_comp_target` | `pairProduct (m ≫ k) x y = pairProduct m x y ≫ (Q.map k)⟦n⟧'` |
| `pairProduct_naturality_left` | `pairProduct m' (x ≫ (Q.map f)⟦a⟧') y = pairProduct ((f ⊗ 𝟙_B) ≫ m') x y` |
| `pairProduct_naturality_right` | for `g : B ⟶ B'` with `lam.hom ≫ g = (𝟙_E ⊗ g) ≫ lam'.hom`: `pairProduct lam' m' x (y ≫ (Q.map g)⟦b⟧') = pairProduct lam ((𝟙_A ⊗ g) ≫ m') x y` |
| `pairProduct_naturality` | for `f : A ⟶ A'`, `g : B ⟶ B'`, `k : D ⟶ D'` with `m ≫ k = (f ⊗ g) ≫ m'` and the unitor square: `pairProduct m' (x ≫ (Q.map f)⟦a⟧') (y ≫ (Q.map g)⟦b⟧') = pairProduct m x y ≫ (Q.map k)⟦n⟧'` |
| `pairAction_unit`, `pairProduct_unit` | for `ρ : mapBifunctorRight F E ≅ 𝟭` with `hρ : ∀ a, ρ_{E⟦a⟧} = shift₁(E, E, a) ≫ ρ_E⟦a⟧`: `pairAction (ρ.app E) ρ_E x = x` and `pairProduct (ρ.app E) ρ_E h x y = y.comp x h` |
| `complexRightUnitor_hom_naturality`, `complexLeftUnitor_hom_naturality` (and `_inv_` forms) | naturality of `HomologicalComplex.rightUnitor`, `leftUnitor` on `CochainComplex C ℤ` along chain maps, without the monoidal structure on complexes |
| `complexRightUnitor_hom_shift` (and `_inv_`) | `ρ_{K⟦a⟧} = (mapBifunctorShift₁Iso K 𝟙 a).hom ≫ ρ_K⟦a⟧`, no sign |
| `complexLeftUnitor_tensorUnit_inv` | `λ_𝟙⁻¹ = ρ_𝟙⁻¹` on the unit complex (Mathlib's `unitors_inv_equal` in degree 0; other degrees are zero objects) |
| `tensorRightUnitorNat`, `derivedTensorUnitIso hE`, `derivedTensorUnitIso_hom_app` | `mapBifunctorRight (curriedTensor C) 𝟙 ≅ 𝟭` from `rightUnitor`; its descent `T_𝟙 ≅ 𝟭` (`derivedMapBifunctorRightIsoId`), with component `fac.hom.app K ≫ Q.map ρ_K` at `Q.obj K` |
| `tensorPairProduct hB m h x y` | `pairProduct (curriedTensor C) 𝟙 hB (leftUnitor B) m h x y` |
| `tensorPairProduct_naturality` | `pairProduct_naturality` with the unitor square discharged by `complexLeftUnitor_hom_naturality` |
| `tensorPairProduct_unit hE h x y` | `tensorPairProduct hE λ_𝟙 h x y = y.comp x h` |
| `unitComplex Y`, `unitComplex_eq_single_QX` | `ℚ_Y[0] := tensorUnit (ShQ Y) (.up ℤ)`; `= (single (ShQ Y) (.up ℤ) 0).obj (QX Y)` by `rfl` (the bridge to the constant sheaf; `Cup.unitIsoQX` is `Iso.refl`) |
| `unitComplex_isStrictlyGE`, `unitComplex_isStrictlyLE` | instances, bounds `[0, 0]` |
| `unitComplexMul Y`, `unitComplexMul_eq` | the unit multiplication `(tensorRightComplex Y ℚ_Y[0]).obj ℚ_Y[0] ⟶ ℚ_Y[0]`, the left unitor of complexes (`rfl`). The unit iso `T_𝟙 ≅ 𝟭` is `derivedTensorUnitIso` of the tensor layer; no sheaf-level unit iso is stated, since none is used (the unit clause is proved generically) |
| `pairProductShQ Y lo hi m h x y` | the pairing on `D(ShQ Y)` for `B` strictly bounded in `[lo, hi]`, `m : (tensorRightComplex Y B).obj A ⟶ D` |
| `pairProductShQ_add_left`, `_add_right` | biadditivity |
| `pairProductShQ_naturality` | with `hm : m ≫ k = tensorHom f g ≫ m'` |
| `pairProductShQ_unit h x y` | `pairProductShQ Y 0 0 (unitComplexMul Y) h x y = y.comp x h` |

**Signs.** None, and every identity is exact. The shift enters only in the first variable, through `mapBifunctorShift₁Iso` (identity on summands, Mathlib docstring "does not involve signs") and `Q.commShiftIso`; the product of shifted morphisms is Mathlib's `ShiftedHom.comp` (`y ≫ g⟦b⟧' ≫ (shiftFunctorAdd' a b n h).inv`); the unitors carry no scalar. Order (conventions row "de Rham cup order (proposed)"): `x` acts on `B` from the left and `y` is applied first, so on `ℚ_Y[0]` the product is `y.comp x`; with the cup product in diagrammatic order, `pairProduct λ β α = α ∪ β`, and `deRhamCup x y := pairProduct μ y x` puts `deRhamCup` in the order of `Cup.cup`. The right-action variant would carry `(−1)^{p·b}` from `mapBifunctorShift₂Iso`; it is not used.

**Choices for the red team.**
1. `lam : E ⊗ B ≅ B` is data of the generic product (the left unitor in the tensor and sheaf layers), and naturality in `B` asks for the unitor square. In the unit clause `lam = ρ.app E` and `m = ρ_E`; the tensor layer takes `m = λ_𝟙` and passes through `λ_𝟙 = ρ_𝟙` (`complexLeftUnitor_tensorUnit_inv`).
2. The unit hypothesis `hρ` is asked only at `E`. For the right unitor it holds for every `K` (`complexRightUnitor_hom_shift`).
3. Naturality is along chain maps of `A`, `B`, `D`, as the ledger note asks; every map `de-rham-cup` feeds in (`F^p → Ω•`, `μ`, `μ_{p,q}`, `u`, `c • 𝟙`) is one. Naturality along morphisms of the derived category is not stated.
4. No sheaf-level unit iso: `derivedTensorUnitIso` and `derivedTensorUnitIso_hom_app` at `C = ShQ Y` record `T_{ℚ_Y[0]} ≅ 𝟭`; a named sheaf copy cost about 40 s and was used by nothing (red team change 1).
5. Not stated: ℚ-linearity, associativity, graded commutativity, compatibility with `T_φ` for `φ` a quasi-isomorphism, any statement on a general unit `E` beyond the hypotheses above.

**Trivial proofs fail.** Checked in scratch against the built module: `rfl` on `pairProduct_unit` and on `pairProduct_add_left`, `simp [pairProduct, pairAction, hρ]` on `pairProduct_unit`, and `simp [pairProduct, pairAction]` on `pairProduct_naturality_left` all leave goals.

**Timings and kernel cost.** The generic and tensor layers check in about 8 s with `lake env lean`. Each sheaf-level declaration pays the instance diamond of `docs/gaps.md` (Known weaknesses): in scratch, `pairProductShQ` 11 s, `pairProductShQ_add_left` 15 s, `pairProductShQ_unit` 30 to 35 s, `pairProductShQ_naturality` 48 to 60 s, `unitComplexMul` 17 s and `unitComplexMul_eq` 18.5 s (red team, serial), the `unitComplex` bound instances 3 s each. Diagnostics on the smallest instantiation (`mapBifunctorRight (curriedTensor (ShQ Y)) ℚ_Y[0]`, 7 s) show the kernel unfolding `Add.add` about 99,000 times, through `ModuleCat` hom groups, `Preadditive.homGroup` and `Function.Injective.addCommGroup`: the comparison of `Abelian.toPreadditive sheafIsAbelian` (the generic layer's path) with `Preadditive.fullSubcategory` (instance search at `ShQ Y`). Raising the priority of `Abelian.toPreadditive` and `Preadditive.preadditiveHasZeroMorphisms` locally did not change the times. Consumer side (red team, serial, `Elab.async false`): a statement that mentions `pairProductShQ` with a general `m` checks in under 1 s; with the left unitor written out as `m` it pays 7.9 s per declaration (the diamond between `tensorObj 𝟙 𝟙` and `(tensorRightComplex Y 𝟙).obj 𝟙`), and under 1 s with the named `unitComplexMul`; a placeholder `𝟙 _` for `𝟙 (Q.obj (unitComplex Y))` cost 23 s of elaboration in one statement, under 1 s written out; `abbrev` against `def` for `pairProductShQ` made no measurable difference. The whole file: about 3 minutes with `lake env lean` (187 s); `lake build HodgeLadder.Hodge.PairingProduct` built it in 168 s, against 114 s for `HodgeLadder.Hodge.DerivedTensorBounded`.
## rational-de-rham-complex: statement
Module `HodgeLadder/Hodge/RationalDeRhamComplex.lean` (`HodgeLadder.Hodge.RationalDeRhamComplex`). Section written for the statement red team; the posted state is in "rational-de-rham-complex: checked" below. Every declaration below elaborates and is proved, with the three standard axioms only (`#print axioms`, 2026-11-27). The file checks in about 40 s with `lake env lean`; `lake build HodgeLadder.Hodge.RationalDeRhamComplex` built it in 34 s. It imports `HodgeLadder.Cup.SheafTensor` and upstream's `Definitions.AlgebraicGeometry.Hodge.Filtration`, nothing from the in-flight `rational-hypercohomology-equiv`.
Construction. The `ℚ`-structure is restriction of scalars along `ℚ → ℂ`; the presheaf `U ↦ HolomorphicForm X d U p` of `ℚ`-vector spaces has upstream's `holomorphicDeRhamPresheaf X d p` as underlying presheaf of abelian groups, by `rfl`. Sheafify in `ModuleCat ℚ`; the comparison with upstream's sheaf is Mathlib's `sheafComposeNatIso` for `Cup.U` (sheafification commutes with forgetting, `Cup.preservesSheafification_U`). Differentials and the unit are sheafified presheaf maps, as upstream's, so each compatibility is a naturality square of the one isomorphism. Mathlib's `constantCommuteCompose`, which defines `Cup.forgetQX`, is built from the same `sheafComposeNatIso`; this is what makes the degree-zero unit compatibility exact.
| `holomorphicFormRatModule X d U p` | instance `Module ℚ (HolomorphicForm X d U p)`, `Module.compHom _ (algebraMap ℚ ℂ)` |
| `holomorphicForm_rat_smul_def` | `q • θ = algebraMap ℚ ℂ q • θ`, `rfl` |
| `holomorphicForm_isScalarTower` | instance `IsScalarTower ℚ ℂ (HolomorphicForm X d U p)` |
| `holomorphicFormRatModule_unique` | `inst = holomorphicFormRatModule X d U p` for every `inst : Module ℚ (HolomorphicForm X d U p)` (`Subsingleton.elim`, from `subsingleton_rat_module`) |
| `rationalHolomorphicFormPresheaf X d p` | `(Opens X(ℂ))ᵒᵖ ⥤ ModuleCat ℚ`, maps `(holomorphicFormRestriction X d i p).restrictScalars ℚ` |
| `rationalHolomorphicFormPresheaf_comp_forget` | `rationalHolomorphicFormPresheaf X d p ⋙ Cup.U = holomorphicDeRhamPresheaf X d p`, `rfl` |
| `rationalHolomorphicFormDifferential`, `_comp`, `whiskerRight_rationalHolomorphicFormDifferential` | `d` on presheaves, `d ≫ d = 0`, and `whiskerRight d Cup.U = holomorphicDeRhamDifferential X d p` (`rfl`) |
| `rationalConstantsToFormsPresheaf`, `_comp_differential` | `const ℚ ⟶ Ω⁰`, `q ↦ holomorphicFormOfConstant X d U (q : ℂ)`; `d ∘ [q] = 0` |
| `rationalHolomorphicFormSheaf X d p`, `rationalHolomorphicFormSheafDifferential` | `Ω^p_ℚ : Cup.ShQ X(ℂ)`, sheafification; sheafified `d` |
| `rationalHolomorphicFormSheaf_isZero_of_lt` | `d < p → IsZero (Ω^p_ℚ)` |
| `rationalHolomorphicDeRhamComplexNat X d`, `_d` | `CochainComplex.of` of the above, `ℕ`-indexed, as upstream's `holomorphicDeRhamComplex` |
| `forgetSheafifyNatIso X` | `sheafComposeNatIso (Cup.J X(ℂ)) Cup.U (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)` |
| `forgetRationalHolomorphicFormSheafIso X d p` | `(Cup.forgetSheaf X(ℂ)).obj (Ω^p_ℚ) ≅ holomorphicDeRhamSheaf X d p` |
| `forget_rationalHolomorphicFormSheafDifferential` | `forget.map d_ℚ ≫ e_{p+1}.hom = e_p.hom ≫ holomorphicDeRhamSheafDifferential X d p` |
| `forgetRationalHolomorphicDeRhamComplexNatIso` | `forget(Ω•_ℚ, ℕ) ≅ holomorphicDeRhamComplex X d`, `isoOfComponents` |
| `rationalDeRhamComplex X` | `Ω•_ℚ := (rationalHolomorphicDeRhamComplexNat X (dim X.left)).extend embeddingUpNat`, in `CochainComplex (Cup.ShQ X(ℂ)) ℤ` |
| instances | `(rationalDeRhamComplex X).IsStrictlyGE 0`, `rationalDeRhamComplex_isStrictlyLE : IsStrictlyLE (dim X.left)`; for `F^p` Mathlib's instances give `IsStrictlyGE p` and `IsStrictlyLE (dim X.left)` (checked in scratch) |
| `forgetRationalDeRhamIso X` | `((Cup.forgetSheaf X(ℂ)).mapHomologicalComplex (up ℤ)).obj (rationalDeRhamComplex X) ≅ Ω•(X)`: upstream's `mapExtendCanonicalIso`, then the extension of the `ℕ` comparison |
| `rationalHodgeFilteredComplex X p`, `rationalHodgeFilteredInclusion X p` | `F^p Ω•_ℚ := (rationalDeRhamComplex X).stupidTrunc (embeddingUpIntGE p)`, `stupidTruncInclusion`, as upstream's `hodgeFilteredDeRhamComplex`, `hodgeFilteredDeRhamInclusion` |
| `forgetRationalHodgeFilteredIso X p` | `forget(F^p Ω•_ℚ) ≅ F^p Ω•(X)`: `mapStupidTruncIso`, then `stupidTruncFunctor.mapIso (forgetRationalDeRhamIso X)` |
| `forget_rationalHodgeFilteredInclusion` | `forget.map (rationalHodgeFilteredInclusion X p) ≫ (forgetRationalDeRhamIso X).hom = (forgetRationalHodgeFilteredIso X p).hom ≫ hodgeFilteredDeRhamInclusion X p` |
| `rationalConstantsToFormsSheaf X d`, `_comp_differential` | `Cup.QX X(ℂ) ⟶ Ω⁰_ℚ`, sheafified `rationalConstantsToFormsPresheaf` |
| `forget_rationalConstantsToFormsSheaf` | `forget.map u⁰ ≫ (forgetRationalHolomorphicFormSheafIso X d 0).hom = (Cup.forgetQX _).hom ≫ fieldToComplexConstantSheaf ℚ X ≫ constantsToHolomorphicDeRhamZeroSheaf X d` |
| `rationalDeRhamUnit X` | `(CochainComplex.singleFunctor (Cup.ShQ X(ℂ)) 0).obj (Cup.QX X(ℂ)) ⟶ rationalDeRhamComplex X`, `homFromSingleExtend` of `rationalConstantsToFormsSheaf`; the source is the in-flight `rationalUnitComplex X` (an `abbrev` for this object) |
| `forget_rationalDeRhamUnit_unfolded` | `forget.map (rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom = (singleMapHomologicalComplex forgetSheaf (up ℤ) 0).app _ ≪≫ (singleFunctor _ 0).mapIso (Cup.forgetQX _) ≪≫ (constantFieldSheafComplexIntIsoSingle ℚ X).symm).hom ≫ fieldToHolomorphicDeRhamComplexInt ℚ X` |
Generic layer (any preadditive categories with zero objects, `F` additive): `homFromSingleExtend K u hu : A[0] ⟶ K.extend embeddingUpNat` with `_ext`, `_f_zero`, `single_map_comp_homFromSingleExtend`, `extendSingleIso_inv_comp_extendMap`, `single_map_comp_extendSingleIso_inv_comp`, `singleMap_trans_extendSingleIso_hom_comp`, `mapHomologicalComplex_homFromSingleExtend`; `mapRestrictionIso`, `mapStupidTruncIso`, `mapStupidTruncIso_inclusion` (a functor commutes with the stupid truncation, carrying inclusion to inclusion). Candidates for Mathlib (`docs/gaps.md` "To upstream" when the rung is posted).
**The unit goes through `forgetUnitComplexIso` (change 8 of the red team of `rational-hypercohomology-equiv`).** The right side of `forget_rationalDeRhamUnit_unfolded` is the body of `forgetUnitComplexIso` on the in-flight branch, verbatim. In scratch, with that branch's `forgetComplex`, `rationalUnitComplex` and `forgetUnitComplexIso` copied into a file importing this module, the recorded signature
```lean
theorem forget_rationalDeRhamUnit :
    (forgetComplex X).map (rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom =
      (forgetUnitComplexIso X).hom ≫ fieldToHolomorphicDeRhamComplexInt ℚ X :=
  forget_rationalDeRhamUnit_unfolded X
```
elaborates and checks with the standard axioms; the same holds for `forget_rationalHodgeFilteredInclusion` restated with `forgetComplex`. When `rational-hypercohomology-equiv` lands, add these two lines to this module (or to a consumer) and import its module; nothing is duplicated here.
**Signs and scalars.** None. Every isomorphism is `sheafComposeNatIso`, `mapExtendCanonicalIso`, `extendSingleIso`, `singleMapHomologicalComplex`, `Iso.refl` components, or their truncations; the unit is `q ↦ [q]`. No new convention for `docs/conventions.md`.
**Spelling.** Statements use the site spelling `Sheaf (Cup.J X(ℂ)) AddCommGrpCat` (the target of `Cup.forgetSheaf`) on the left and upstream's `TopCat.Sheaf AddCommGrpCat X(ℂ)` objects on the right; they are definitionally equal. `rw` and `simp` fail across the two (the motive is not type-correct at instance transparency), so the proofs combine generic lemmas by `Eq.trans` and `exact`, where the unifier works at default transparency. A consumer meets the same: prefer `exact`/`Eq.trans` with the generic lemmas over `rw` at the concrete space.
**Instance findings.** Instance search does not find `Cup.preservesSheafification_U` at `TopCat.of (ComplexPoint X)` in reasonable time (an unrestricted probe for `sheafComposeNatIso` ran past two minutes, then was stopped), and misses `Cup.forgetSheaf_additive` (as the red team of `rational-hypercohomology-equiv` found); both are local instances given as terms (`rdrPreservesSheafification`, `rdrForgetAdditive`). `HolomorphicForm X d U p` has no `Module ℚ` before this module (`infer_instance` fails, rechecked).
**Trivial proofs fail.** Checked in scratch: `rfl` fails on `forget_rationalConstantsToFormsSheaf`, `forget_rationalHodgeFilteredInclusion` and `forget_rationalDeRhamUnit_unfolded`; `simp` leaves the first two open; with the zero map in place of `rationalConstantsToFormsSheaf`, `simp` reduces the degree-zero statement to `0 = forgetQX.hom ≫ fieldToComplexConstantSheaf ℚ X ≫ constantsToHolomorphicDeRhamZeroSheaf X d` and stops. The unit compatibility pins `rationalDeRhamUnit` given `forgetRationalDeRhamIso`, since `forget` is faithful; it does not by itself pin the pair against a common automorphism of `Ω•_ℚ`, which the wedge compatibility of `wedge-sheafify` will.
Questions for the red team. (1) Is the site spelling of the statements acceptable, given that the analytic spelling needs `forgetComplex` from the in-flight branch? (2) Should `rationalDeRhamUnit` be defined through Mathlib's `extendSingleIso` and `fromSingle₀Equiv`, as upstream's `fieldToHolomorphicDeRhamComplexInt`, instead of `homFromSingleExtend` (the two agree by `extendSingleIso_inv_comp_extendMap`)? (3) Is a global `Module ℚ` instance on `HolomorphicForm` right, against a local one, given `holomorphicFormRatModule_unique`? (4) Does `wedge-sheafify` need more from this rung, for example a statement that `forgetSheafifyNatIso` is the one of `HodgeLadder.Cup.tensorLeftIso`?
## rational-de-rham-complex: checked
Checked 2026-11-27; imported from `HodgeLadder.lean`, ledger module `HodgeLadder.Hodge.RationalDeRhamComplex`. Red team `docs/sketches/rational-de-rham-complex.redteam.md`: pass with changes, implemented.
| Change | Implementation |
| 1 | the module imports `HodgeLadder.Hodge.RationalHypercohomology`; `forget_rationalDeRhamUnit : (forgetComplex X).map (rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom = (forgetUnitComplexIso X).hom ≫ fieldToHolomorphicDeRhamComplexInt ℚ X`, against `main`'s declarations, by `forget_rationalDeRhamUnit_unfolded` |
| 2 | `toSheafify_comp_forgetRationalHolomorphicFormSheafIso`: `whiskerRight (toSheafify J P_ℚ) Cup.U ≫ (sheafToPresheaf J _).map e_p.hom = toSheafify J (holomorphicDeRhamPresheaf X d p)`, from `sheafComposeIso_inv_fac`; it determines `e_p`, so no automorphism σ of `Ω•_ℚ` enters (module docstring, "Why the comparison is pinned") |
| 3 | `forgetRationalDeRhamIso`, `forgetRationalHodgeFilteredIso` and `forget_rationalHodgeFilteredInclusion` typed with `forgetComplex`; bodies unchanged |
| 4 | `hodgeFiltration_eq_range_rational : hodgeFiltration X p n = (hypercohomologyMap X ((forgetComplex X).map (rationalHodgeFilteredInclusion X p) ≫ (forgetRationalDeRhamIso X).hom) n).range` |
| 5 | one local instance `rdrForgetAdditive X` before both sections; `rationalDeRhamComplex_isStrictlyGE` named and documented |
| 6 | the `Module ℚ` instance stays global; it and the generic layer are in `docs/gaps.md`, "General lemmas kept local" (decision 0011), with the drift check |
| 7 | definition kept; `rationalDeRhamUnit_eq_extendSingleIso` records the agreement with upstream's shape |
| 8 | open test rung `de-rham-unit-nonzero` |
`wedge-sheafify` takes from here the `ℚ`-bilinear wedge `(holomorphicWedge X d U p q).restrictScalars₁₂ ℚ ℚ`, the presheaf `rationalHolomorphicFormPresheaf`, and the pin of change 2 (ledger note).

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

## rational-hypercohomology-equiv: statement

Date: 2026-11-26. Phase 1 of the sub-rung (statement and instance probe). Module `HodgeLadder.Hodge.RationalHypercohomology` (file `HodgeLadder/Hodge/RationalHypercohomology.lean`), not yet imported from `HodgeLadder.lean`; the ledger entry has no module yet. Phase 1 stops here for the statement red team.

### Statements

Notation below: `F = Cup.tensorQSheaf (TopCat.of (ComplexPoint X))`, `G = Cup.forgetSheaf (TopCat.of (ComplexPoint X))`, `F'`, `G'` their extensions to complexes, `F''`, `G''` to derived categories, `Q = DerivedCategory.Q`.

```lean
/-- Forgetting the rational structure, on complexes. -/
abbrev forgetComplex :
    CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ ⥤
      CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `ℚ_X[0]`. -/
abbrev rationalUnitComplex : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj (Cup.QX (TopCat.of (ComplexPoint X)))

def rationalHypercohomologyEquiv
    (C : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ) (n : ℤ) :
    ℍ^n(X; (forgetComplex X).obj C) ≃+
      ShiftedHom (DerivedCategory.Q.obj (rationalUnitComplex X)) (DerivedCategory.Q.obj C) n

theorem rationalHypercohomologyEquiv_naturality
    {C C' : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ} (f : C ⟶ C') (n : ℤ)
    (x : ℍ^n(X; (forgetComplex X).obj C)) :
    rationalHypercohomologyEquiv X C' n (hypercohomologyMap X ((forgetComplex X).map f) n x) =
      (rationalHypercohomologyEquiv X C n x).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map f)) (zero_add n)

def unitHypercohomologyEquiv (n : ℕ) :
    ℍ^n(X; (forgetComplex X).obj (rationalUnitComplex X)) ≃+ H^n(X; ℚ) :=
  (hypercohomologyMapIso X (forgetUnitComplexIso X) n).trans
    (hypercohomologyAddEquivConstantCohomology ℚ X n)

theorem rationalHypercohomologyEquiv_rationalUnitComplex (n : ℕ)
    (x : ℍ^n(X; (forgetComplex X).obj (rationalUnitComplex X))) :
    rationalHypercohomologyEquiv X (rationalUnitComplex X) n x =
      (Cup.rationalExtEquiv (TopCat.of (ComplexPoint X)) n (unitHypercohomologyEquiv X n x)).hom
```

The agreement is an equality in `ShiftedHom (Q.obj ℚ_X[0]) (Q.obj ℚ_X[0]) n`, with no scalar and no cast: Mathlib's `DerivedCategory.singleFunctor C 0` is `CochainComplex.singleFunctor C 0 ⋙ Q` by `Iso.refl` (`singleFunctorIsoCompQ`), so `Ext.hom` already has the target type of `rationalHypercohomologyEquiv` at `C = ℚ_X[0]`. `forgetUnitComplexIso : forget ℚ_X[0] ≅ constantFieldSheafComplexInt ℚ X` is `singleMapHomologicalComplex G` followed by `single(Cup.forgetQX)` and the inverse of upstream's `constantFieldSheafComplexIntIsoSingle`. Naturality is stated against upstream's `hypercohomologyMap`, in the `ShiftedHom.comp`/`mk₀` form upstream uses.

### Construction

| Step | Declaration | Content |
|---|---|---|
| 1 | `Adjunction.mapCochainComplex` | an adjunction of additive functors gives one on `ℤ`-indexed cochain complexes, degreewise (`Adjunction.mkOfHomEquiv`); Mathlib has no such declaration at the pin |
| 2 | `adjComplex`, `adjDerived` | `ℚ ⊗ − ⊣ forget` on complexes, then on derived categories by `Adjunction.localization`, with `CatCommSq` instances from `mapDerivedCategoryFactors.symm` |
| 3 | `hyperAddEquiv` | `SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) Q`, additive by upstream's `hypercohomologyEquiv_add` |
| 4 | `targetIso`, `sourceIso` | `Q(G'C)[n] ≅ G''((Q C)[n])` (factors, then `commShiftIso` of `G''`); `Q ℚ_X[0] ≅ F''(Q ℤ_X[0])` (upstream's `constantIntegerSheafComplexIntIsoSingleULift`, `singleMapHomologicalComplex F`, `Cup.tensorQSheafInt`, factors) |
| 5 | `rationalHypercohomologyEquiv` | `hyperAddEquiv`, then postcomposition with `targetIso`, then `adjDerived.homAddEquiv` inverted, then precomposition with `sourceIso` |

### What is checked (phase 1, `lake env lean` and `lake build` of the module)

| Declaration | Status |
|---|---|
| `rationalHypercohomologyEquiv` (an `AddEquiv`, data) | elaborates, no `sorry` |
| `rationalHypercohomologyEquiv_naturality` | proved |
| `Adjunction.mapCochainComplex`, `mapCochainComplex_unit_app_f`, `mapCochainComplex_counit_app_f`, `Adjunction.mapCochainComplex_commShift` | proved |
| `adjDerived_commShift : (adjDerived X).CommShift ℤ` | proved: the unit on complexes commutes with shifts degreewise, and `NatTrans.CommShift.liftNatTrans` lifts it |
| `hypercohomologyMap_id`, `hypercohomologyMapIso`, `unitHypercohomologyEquiv`, `unitHypercohomologyEquiv_hom` | proved |
| `rationalExtEquiv_hom` (`Cup.rationalExtEquiv` as a composite in `D(ShQ)`) | proved in a scratch module by one `simp only` over the unfolding lemmas (`Ext.comp_hom`, `Ext.mk₀_hom`, `Adjunction.extEquiv_symm_apply`, `Ext.mapExactFunctor_hom`, `ShiftedHom.mk₀_comp`, `ShiftedHom.comp_mk₀`, `ShiftedHom.map`); about five minutes, so kept out of the module |
| `rationalHypercohomologyEquiv_rationalUnitComplex` | stated, `sorry`; `rfl`, `simp` and `exact?` fail on it |

### Route for the agreement

`rationalExtEquiv_hom` gives the right side as `single(tensorQSheafInt⁻¹) ≫ (F.mapDerivedCategorySingleFunctor 0).inv ≫ F''(α.hom ≫ single(forgetQX⁻¹)[n]) ≫ (F''.commShiftIso n).hom ≫ (F.mapDerivedCategorySingleFunctor 0).hom[n] ≫ single(ε_{ℚ_X})[n]`, and `unitHypercohomologyEquiv_hom` gives `α.hom = Q(u⁻¹) ≫ h_x ≫ Q(e ≫ c)[n]`. On the left, `Adjunction.homEquiv_counit` and `adjDerived_commShift` (Mathlib's `commShiftIso_inv_app_counit_app` with `commShiftIso_comp_inv_app`) move the shift past the derived counit, after which the counit sits at `Q ℚ_X[0]` and `Adjunction.localization_counit_app` applies. Two shift-free identities are left:

1. `sourceIso.hom = single(tensorQSheafInt⁻¹) ≫ (F.mapDerivedCategorySingleFunctor 0).inv ≫ F''(Q u⁻¹)`, from Mathlib's `mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app` and naturality of the factors;
2. on complexes, `ε^{C}_{ℚ_X[0]} = F'(σ) ≫ singleMapHomologicalComplex F ≫ single(ε_{ℚ_X})` with `σ = singleMapHomologicalComplex G`, checked in degree `0` with `mapCochainComplex_counit_app_f`.

Every map in the route is a unit, a counit or a bookkeeping isomorphism; no scalar enters.

### Instance findings

1. **`HodgeLadder.Cup` instances are not found at `TopCat.of (ComplexPoint X)`.** `inferInstance` fails for `(Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).Additive`; the trace shows `Cup.tensorQSheaf_additive` missing from the candidate list, while the same search succeeds for a variable `Y : TopCat`. Workaround: six local instances given as explicit terms (`Additive`, `PreservesFiniteLimits`, `PreservesFiniteColimits` for `F` and `G`), two of them through general-`Y` theorems in the module.
2. **Two spellings of the sheaf category.** Upstream's `ℍ` takes complexes in `AnalyticAdditiveSheaf X = TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))`; `Cup.forgetSheaf` lands in `Sheaf (Opens.grothendieckTopology _) AddCommGrpCat`. With upstream's `local implicit_reducible` attributes the types unify, but a `CatCommSq` instance stated on one spelling is not found for the other, and `rw` steps that mix them report a term "not type-correct under the implicit transparency". Workaround: `forgetComplex` (analytic target, in the statements) and `forgetComplexSite` (site target, in the construction), `intUnitSite` for `ℤ_X[0]`, and `hyperAddEquivSite`; the pairs are definitionally equal and meet only through `change` or unfolding.
3. **`HasDerivedCategory` and `HasExt`.** Upstream's instances are `local`, so they are repeated: `HasDerivedCategory.standard (AnalyticAdditiveSheaf X)`, the site spelling defined as that instance (as in `HodgeLadder.Cup.ExtBridge`), `HasDerivedCategory.standard (Cup.ShQ _)` for the rational side, and `HasExt.{0}` for sheaves of abelian groups by `inferInstance`. The `ULift ℤ` source raised no issue: it enters only through upstream's `constantIntegerSheafComplexIntIsoSingleULift` and `Cup.tensorQSheafInt`.
4. **Liftings are synthesized, not read off.** `NatTrans.CommShift.liftNatTrans` synthesizes its `Lifting` arguments, and the lifting inside `Adjunction.Localization.ε` is a `letI`, so it is supplied by hand and its `CommShift` is proved from `CatCommSq.hComp` written out. The whiskered unit needs its `CommShift` stated with `F₁ := Q`: Mathlib's `whiskerRight` instance gives it on `𝟭 ⋙ Q`, which `liftNatTrans` does not accept.
5. **Rewriting under `AddEquiv` coercions times out.** `rw` with `rationalHypercohomologyEquiv_apply` or `hyperAddEquivSite_map` hits the heartbeat limit; `simp only` and `have`-then-`simp only` work. `rw [SmallShiftedHom.equiv_mk₀]` on upstream's comparison also times out; `simp only` works. A `pp.explicit` goal at one point failed to pretty-print (13 MB).
6. **No long instance search.** The five-minute synthesis reported for `HasTensor` on `CochainComplex (ShQ Y) ℤ` did not occur; every probe ran under `timeout` and none reached it.

### Timings

`lake env lean` on the module: 7 s for the skeleton, 15 s with the equivalence, about 55 s with naturality and the unit side, 75 to 95 s with `adjDerived_commShift` and `unitHypercohomologyEquiv_hom`. The kernel spends 13 to 14 s on each of `unitHypercohomologyEquiv` and the agreement statement (defeq of the two sheaf spellings). `lake build` of the module: 61 s before the unit-side lemmas. `rationalExtEquiv_hom` in the scratch module: about five minutes.

## rational-hypercohomology-equiv: checked

Date: 2026-11-27, after the statement red team (`docs/sketches/rational-hypercohomology-equiv.redteam.md`, pass with changes, all implemented). Modules `HodgeLadder.Hodge.RationalHypercohomology` and `HodgeLadder.Cup.RationalExtHom`, imported from `HodgeLadder.lean`.

| Declaration | Content |
|---|---|
| `rationalHypercohomologyEquiv_rationalUnitComplex` | the agreement with `Cup.rationalExtEquiv` on `ℚ_X[0]`, exact, no scalar |
| `rationalHypercohomologyEquiv_one` | the unit `Cup.one X` goes to `ShiftedHom.mk₀ 0 _ (𝟙 _)` |
| `rationalHypercohomologyEquiv_map` | naturality as `x ↦ x ≫ (Q.map f)⟦n⟧'` |
| `Cup.rationalExtEquiv_hom`, `Adjunction.extEquiv_symm_hom`, `Ext.postcompIsoAddEquiv_hom`, `Ext.precompIsoAddEquiv_hom` | `rationalExtEquiv` as a composite in the derived category, at a general space with the `HasDerivedCategory` instances as arguments |

Proof of the agreement, as planned: `Adjunction.shift_counit_app` with `adjDerived_commShift` moves the shift past the derived counit (`adjDerived_counit_shift`); the two shift-free identities are `sourceIso_hom_eq` and `adjDerived_counit_rationalUnitComplex`, the second reduced by `Adjunction.localization_counit_app` to the counit on complexes at `ℚ_X[0]` (`adjComplex_counit_rationalUnitComplex`, degree 0). Steps that cross the two sheaf spellings go through `refine`/`exact` with definitional unfolding; `rw` and `simp` do not match across them (findings in the statement section).

Consumer clause for `rational-de-rham-complex` (red team change 8). State the unit compatibility through exactly `forgetUnitComplexIso`, with names fixed by that rung:

```lean
theorem forget_rationalDeRhamUnit :
    (forgetComplex X).map (rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom =
      (forgetUnitComplexIso X).hom ≫ fieldToHolomorphicDeRhamComplexInt ℚ X
```

where `rationalDeRhamUnit X : rationalUnitComplex X ⟶ Ω•_ℚ` and `forgetRationalDeRhamIso X : (forgetComplex X).obj Ω•_ℚ ≅ Ω•(X)`. Another isomorphism `forget ℚ_X[0] ≅ constantFieldSheafComplexInt ℚ X` could insert an automorphism of `ℚ_X` between the bridge and `ι`.

## de-rham-unit-nonzero: statement

Module `HodgeLadder.Tests.DeRhamUnitNonzero`, imported from `HodgeLadder.lean` (checked 2026-11-27; red team `docs/sketches/de-rham-unit-nonzero.redteam.md`, pass with changes, implemented). Red team of `rational-de-rham-complex`, change 7, section 7b: the test that fails if `forget_rationalDeRhamUnit` holds because both units are zero.

```lean
theorem HodgeLadder.Tests.fieldToHolomorphicDeRhamComplexInt_point_ne_zero :
    fieldToHolomorphicDeRhamComplexInt ℚ HodgeLadder.Tests.point ≠ 0

theorem HodgeLadder.Tests.rationalDeRhamUnit_point_ne_zero :
    HodgeLadder.rationalDeRhamUnit HodgeLadder.Tests.point ≠ 0
```

Both are specializations of general forms in the same file, at `point = Spec ℂ` with the complex point `𝟙 _`:

| Declaration | Statement |
|---|---|
| `holomorphicFormOfConstant_ne_zero` | `holomorphicFormOfConstant X d U c ≠ 0` for `c ≠ 0` and `[Nonempty U.unop]` |
| `fieldToHolomorphicFormZeroSheaf_ne_zero` | `fieldToComplexConstantSheaf K X ≫ constantsToHolomorphicDeRhamZeroSheaf X d ≠ 0` for `[Nonempty (ComplexPoint X)]` |
| `fieldToHolomorphicDeRhamComplexInt_ne_zero` | `fieldToHolomorphicDeRhamComplexInt K X ≠ 0` for every field `K` with `[Algebra K ℂ]`, `[IsIntegral X.left] [Smooth X.hom] [Nonempty (ComplexPoint X)]` |
| `rationalDeRhamUnit_ne_zero` | `rationalDeRhamUnit X ≠ 0` under the same hypotheses |
| `nsmul_fieldToHolomorphicFormZeroSheaf_ne_zero`, `nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero` | the non-torsion forms `n • (…) ≠ 0` for `n : ℕ`, `n ≠ 0` (red team change 4) |
| `fieldToHolomorphicDeRhamComplexInt_ne_neg`, `rationalDeRhamUnit_ne_neg` | `ι ≠ −ι` and `rationalDeRhamUnit X ≠ −rationalDeRhamUnit X`, from `n = 2`: `forget_rationalDeRhamUnit` is false for the negated unit |

**Instances.** `HodgeLadder.Tests.point` carries `IsIntegral point.left` and `Smooth point.hom` (rung `nonvacuity-tests`), which are the instance arguments of both `fieldToHolomorphicDeRhamComplexInt` and `rationalDeRhamUnit`. No other space is needed.

**Proof route.**

1. Degree zero. `single_map_comp_extendSingleIso_inv_comp` (rung `rational-de-rham-complex`) with `a = 𝟙` writes upstream's unit, after isomorphisms, as `homFromSingleExtend` of `fieldToComplexConstantSheaf K X ≫ constantsToHolomorphicDeRhamZeroSheaf X d`; `homFromSingleExtend_f_zero` and cancelling `singleObjXSelf` reduce the complex statement to that sheaf map.
2. Presheaf level. The sheaf map is `(presheafToSheaf J _).map f'` with `f' : c ↦ [algebraMap K ℂ c]` on the constant presheaf. If it is zero, Mathlib's `toSheafify_naturality` gives `f' ≫ toSheafify J Ω⁰ₚ = 0`.
3. Stalks. On the stalk at a point `x`, `toSheafify` is an isomorphism (`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`), so the stalk map of `f'` is zero, and `stalkFunctor_map_germ_apply` says the germ at `x` of `[1]` on `⊤` vanishes. `germ_eq` gives an open `W ∋ x` on which the restriction of `[1]` is zero; by `holomorphicFormRestriction_ofConstant` that restriction is `[1]` on `W`.
4. Chart evaluation. `holomorphicFormOfConstant_ne_zero`: the chart evaluation of `[c]` at a point of `W` is `c` (upstream's `chartEvaluation_ofConstant`), so `[1] ≠ 0` on the nonempty `W`. This reproves the needed half of upstream's `private` `holomorphicFormOfConstant_injective`, with the same steps.
5. Corollary. From `forget_rationalDeRhamUnit`, `rationalDeRhamUnit X = 0` would give `(forgetUnitComplexIso X).hom ≫ fieldToHolomorphicDeRhamComplexInt ℚ X = 0`; cancelling the isomorphism contradicts step 3.

**Instance findings.** `(forgetComplex X).PreservesZeroMorphisms` is not found by search, even with `Cup.forgetSheaf_additive` in context (the two sheaf spellings again); it is given as a term, `Functor.preservesZeroMorphisms_of_additive` applied to Mathlib's `instAdditiveHomologicalComplexMapHomologicalComplex`. `Category.assoc` and `simp` do not rewrite the composite inside the `homFromSingleExtend` proof argument at `AnalyticAdditiveSheaf X`, so that proof is taken from the instantiated generic lemma.

**Axioms.** All ten declarations: `propext`, `Classical.choice`, `Quot.sound` (`#print axioms`, scratch). No placeholder proofs, `native_decide`, `axiom` or `unsafe` in the file; `python3 tools/check.py` checks all ten through the ledger.

**Upstream.** The test is a sanity check of upstream definitions (`fieldToHolomorphicDeRhamComplexInt`, `holomorphicFormOfConstant`). `holomorphicFormOfConstant_ne_zero` reproves half of upstream's `private` `holomorphicFormOfConstant_injective`; it is kept local (decision 0011) and listed in `docs/gaps.md` "General lemmas kept local".

**Path.** The module sits under `HodgeLadder/Tests/` next to `Witness` and `CodimensionZero`; the ledger's `module` field is `HodgeLadder.Tests.DeRhamUnitNonzero`, which replaces the generated path `HodgeLadder/De/Rham/Unit/Nonzero.lean`.

**Timings.** `lake env lean` on the file: 8 to 13 s wall for the six first declarations, 13 to 15 s with the four of change 4. `lake build HodgeLadder.Tests.DeRhamUnitNonzero`: 7.6 s for the module before change 4.

**Open follow-up.** `Nonempty (ComplexPoint X)` is an argument of the general forms; rung `complex-point-nonempty` (open) derives it from `IsIntegral X.left` and `Smooth X.hom` by the Nullstellensatz.

## wedge-sheafify: statement

Module `HodgeLadder/Hodge/WedgeSheafify.lean` (`HodgeLadder.Hodge.WedgeSheafify`). Section written for the statement red team; the posted state is in "wedge-sheafify: checked" below, and the verdict is `docs/sketches/wedge-sheafify.redteam.md`. `tools/next.py` derives `HodgeLadder/Wedge/Sheafify.lean` from the rung id, since the ledger had `module: null`; the module sits next to `WedgePresheaf` and `RationalDeRhamComplex`, and the ledger now names it. It imports `HodgeLadder.Hodge.WedgePresheaf` and `HodgeLadder.Hodge.RationalDeRhamComplex` (which already imports `RationalHypercohomology`). Every declaration below elaborates and is proved, with the three standard axioms only (`#print axioms` on all 17 declarations, 2026-11-27). No statement is open.

Construction. On an open `U`, `rationalWedgeBilin X d U p q := (holomorphicWedge X d U p q).restrictScalars₁₂ ℚ ℚ`, for the instance `holomorphicFormRatModule`. Its `TensorProduct.lift` on each open is the presheaf wedge; naturality is `holomorphicFormRestriction_holomorphicWedge` on pure tensors (`TensorProduct.ext'`). Sheafification `presheafToSheaf` is monoidal for `Sheaf.monoidalCategory` (Mathlib's instance, `Localization.Monoidal`); the sheaf wedge is its tensorator `μ` followed by the sheafified presheaf wedge. The defining square uses `toSheafifyTensor P Q := toSheafify (P ⊗ Q) ≫ δ`, where `δ = μ⁻¹`, and maps out of `sheafify P ⊗ sheafify Q` are determined after `toSheafifyTensor` (`δ` is an isomorphism, then `sheafify_hom_ext`).

### Statements

Generic layer, any `Y : TopCat`, `P Q R : Cup.PreQ Y`:

| Declaration | Statement |
|---|---|
| `toSheafifyTensor P Q` | `P ⊗ Q ⟶ (presheafQ Y).obj (sheafifyQ P ⊗ sheafifyQ Q)`, `toSheafify (J Y) (P ⊗ Q) ≫ (presheafQ Y).map (δ (sheafifyQ Y) P Q)` |
| `toSheafifyTensor_comp_μ` | `toSheafifyTensor P Q ≫ (presheafQ Y).map (μ (sheafifyQ Y) P Q) = toSheafify (J Y) (P ⊗ Q)` |
| `toSheafifyTensor_comp_map P Q R w` | `toSheafifyTensor P Q ≫ (presheafQ Y).map (μ ≫ (sheafifyQ Y).map w) = w ≫ toSheafify (J Y) R` for `w : P ⊗ Q ⟶ R` |
| `toSheafifyTensor_hom_ext` | `f g : sheafifyQ P ⊗ sheafifyQ Q ⟶ S`, equal after `toSheafifyTensor P Q ≫ (presheafQ Y).map _`, are equal |
| `toSheafifyTensor_naturality_left α Q` | `toSheafifyTensor P Q ≫ (presheafQ Y).map ((sheafifyQ Y).map α ▷ sheafifyQ Q) = (α ▷ Q) ≫ toSheafifyTensor P' Q` |
| `toSheafifyTensor_naturality_right P β` | `toSheafifyTensor P Q ≫ (presheafQ Y).map (sheafifyQ P ◁ (sheafifyQ Y).map β) = (P ◁ β) ≫ toSheafifyTensor P Q'` |

At `X(ℂ)`, with `P_p := rationalHolomorphicFormPresheaf X d p` and `Ω^p_ℚ := rationalHolomorphicFormSheaf X d p = sheafifyQ P_p`:

| Declaration | Statement | Proof |
|---|---|---|
| `analyticShQMonoidal X` | `MonoidalCategory (Cup.ShQ (TopCat.of (ComplexPoint X)))`, `Cup.sheafMonoidal _` (abbrev, local instance) | definition |
| `rationalWedgeBilin X d U p q` | `HolomorphicForm X d U p →ₗ[ℚ] HolomorphicForm X d U q →ₗ[ℚ] HolomorphicForm X d U (p + q)` | `restrictScalars₁₂ ℚ ℚ` |
| `rationalWedgePresheaf X d p q` | `P_p ⊗ P_q ⟶ P_{p+q}`, components `ModuleCat.ofHom (TensorProduct.lift (rationalWedgeBilin X d U p q))` | naturality from `holomorphicFormRestriction_holomorphicWedge` |
| `rationalWedgePresheaf_app_tmul` | `((rationalWedgePresheaf X d p q).app U).hom (a ⊗ₜ[ℚ] b) = holomorphicWedge X d U p q a b` | `rfl` |
| `wedgeSheaf X d p q` | `Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ`, `μ (sheafifyQ _) P_p P_q ≫ (sheafifyQ _).map (rationalWedgePresheaf X d p q)` | definition |
| `toSheafifyTensor_comp_wedgeSheaf` | `toSheafifyTensor P_p P_q ≫ (presheafQ _).map (wedgeSheaf X d p q) = rationalWedgePresheaf X d p q ≫ toSheafify (J _) P_{p+q}` | `toSheafifyTensor_comp_map` |
| `eq_wedgeSheaf_iff f` | `f = wedgeSheaf X d p q ↔ toSheafifyTensor P_p P_q ≫ (presheafQ _).map f = rationalWedgePresheaf X d p q ≫ toSheafify (J _) P_{p+q}` | the square, `toSheafifyTensor_hom_ext` |
| `toSheafifyTensor_comp_wedgeSheaf_apply` | on `a ⊗ₜ b` over `U`: `wedgeSheaf` of `toSheafifyTensor (a ⊗ₜ b)` is `toSheafify (J _) P_{p+q}` of `holomorphicWedge X d U p q a b` | `congrArg` |
| `forget_wedgeSheaf` | `whiskerRight (toSheafifyTensor P_p P_q ≫ (presheafQ _).map (wedgeSheaf X d p q)) Cup.U ≫ (sheafToPresheaf (J _) AddCommGrpCat).map (forgetRationalHolomorphicFormSheafIso X d (p + q)).hom = whiskerRight (rationalWedgePresheaf X d p q) Cup.U ≫ toSheafify (J _) (holomorphicDeRhamPresheaf X d (p + q))` | the square, then `toSheafify_comp_forgetRationalHolomorphicFormSheafIso` |
| `forget_wedgeSheaf_apply` | on sections: `e_{p+q}` of `wedgeSheaf (toSheafifyTensor (a ⊗ₜ b))` is upstream's `toSheafify (J _) (holomorphicDeRhamPresheaf X d (p + q))` of `holomorphicWedge X d U p q a b` | `congrArg` |
| `rationalWedgePresheaf_app_ne_zero U` | `(rationalWedgePresheaf X d 0 0).app U ≠ 0` for `[Nonempty U.unop]` | `holomorphicWedge_ofConstant_one_ne_zero` |

Signs and scalars. None. `μ`, `δ`, `toSheafify` and `sheafComposeNatIso` are Mathlib's; the wedge keeps the factor order `a ∧ b` of `holomorphicWedge`; `restrictScalars₁₂` and `TensorProduct.lift` change no value. The pin: `eq_wedgeSheaf_iff` determines the sheaf wedge from the presheaf wedge and Mathlib's tensorator, and `forget_wedgeSheaf` ties its forgotten image to upstream's sheafification map through the comparison that `toSheafify_comp_forgetRationalHolomorphicFormSheafIso` pins. A twist of the comparison by an automorphism σ of `Ω^{p+q}_ℚ` would change the left side of `forget_wedgeSheaf` and leave the right side fixed. No new row for `docs/conventions.md`; the row "Wedge product of holomorphic forms" covers the factor order.

Trivial proofs fail (scratch, 2026-11-27): `rfl` fails on `toSheafifyTensor_comp_wedgeSheaf` and on `forget_wedgeSheaf`; `simp` leaves both open; with `0` in place of `wedgeSheaf X d p q` in the square, `simp` stops at `toSheafifyTensor P_p P_q ≫ (presheafQ _).map 0 = toSheafify (J _) (P_p ⊗ P_q) ≫ sheafifyMap (J _) (rationalWedgePresheaf X d p q)`.

### Instance findings

1. **`Cup.sheafMonoidal` is not applied at `TopCat.of (ComplexPoint X)`.** `#synth MonoidalCategoryStruct (Cup.ShQ (TopCat.of (ComplexPoint X)))` fails with `attribute [local instance] Cup.sheafMonoidal`, and succeeds at a variable `Y`. Cause, read with `#discr_tree_key`: the key of `Cup.sheafMonoidal` contains `Opens _.1` (the `TopCat` carrier of a metavariable), while the concrete goal reduces at reducible transparency to `Opens (Quiver.Hom (Over.mk (𝟙 (Spec ℂ))) X)` (`TopCat.of` and `ComplexPoint` unfold), so the trie lookup misses. The same cause plausibly explains the misses of `Cup.preservesSheafification_U` and `Cup.forgetSheaf_additive` recorded for `rational-de-rham-complex` (not rechecked). Fix: `analyticShQMonoidal X`, an abbrev at the concrete space, as a local instance; consumers repeat the `attribute [local instance]` line. The `Functor.Monoidal` instance of `presheafToSheaf` is found at the concrete space with no help.
2. **Spelling.** `rw` does not cross `rationalHolomorphicFormSheaf X d p` and `(sheafifyQ _).obj P_p` (a `def`, motive not type-correct at implicit transparency), and the same holds for `Sheaf (Cup.J _) AddCommGrpCat` against upstream's `TopCat.Sheaf`. Proofs use `exact` and `Eq.trans` with the generic lemmas. A consumer check in scratch: `toSheafifyTensor P_p P_q ≫ (presheafQ _).map ((rationalHolomorphicFormSheafDifferential X d p ▷ Ω^q_ℚ) ≫ wedgeSheaf X d (p + 1) q) = (rationalHolomorphicFormDifferential X d p ▷ P_q) ≫ rationalWedgePresheaf X d (p + 1) q ≫ toSheafify (J _) P_{p+1+q}` fails at the first `rw [Functor.map_comp]` and closes in five `Eq.trans` steps with `toSheafifyTensor_naturality_left` and the square. This is the shape `wedge-sheaf-map` needs for the Leibniz check.
3. **No kernel cost.** Unlike the sheaf-level `tensorHom` of `docs/gaps.md` (Known weaknesses), no declaration here is slow: the statements name sheaf maps (`wedgeSheaf`, `▷`, `◁`) and write objects out.

### Timings

`lake env lean` on the module: 5 s for the skeleton, about 10 s in full; `lake build HodgeLadder.Hodge.WedgeSheafify` 4 to 5 s. Scratch tests 5 to 9 s each.

Questions for the red team. (1) Is `toSheafifyTensor` (sheafification map of `P ⊗ Q`, then `δ`) the right reference map for the defining square, against `(toSheafify P ⊗ toSheafify Q)` followed by a canonical map `F.obj ⊗ G.obj ⟶ (F ⊗ G).obj` for sheaves `F`, `G`? By `toSheafifyTensor_naturality_left`, `_right` and the triangle identity of the sheafification adjunction the two should agree; this is not stated or checked in Lean. (2) Should `analyticShQMonoidal` move to `HodgeLadder.Cup.SheafTensor` with the other ShQ structure, and should the concrete-space instances of `rational-de-rham-complex` be rechecked against the discrimination-tree cause? (3) Is presheaf-level nonvacuity enough, or should the rung carry `wedgeSheaf X d 0 0 ≠ 0` on a nonempty `X(ℂ)`? That needs `toSheafify` of `[1]` to be nonzero in upstream's sheaf (a stalk argument), and fits the open test rung `de-rham-unit-nonzero` better.

## wedge-sheafify: checked

Checked 2026-11-27; imported from `HodgeLadder.lean`, ledger module `HodgeLadder.Hodge.WedgeSheafify`, 24 declarations, standard axioms only. Red team `docs/sketches/wedge-sheafify.redteam.md`: pass with changes, implemented.

| Change | Implementation |
|---|---|
| 1 | import from `HodgeLadder.lean`; ledger `checked` with the 17 declarations of the statement section and the 7 below |
| 2 | `docs/gaps.md`, "General lemmas kept local": one row for `toSheafifyTensor` and its generic lemmas |
| 3 | the ledger-path sentence above, corrected |
| 4 | the row "Sheafified wedge and the sheaf tensor" of `docs/conventions.md` (red team) stays |
| 5 | the unit law in the module: `sheafifyQ_ε : Functor.LaxMonoidal.ε (Cup.sheafifyQ Y) = 𝟙 _ := rfl` (the pin), `toSheafifyTensor_leftUnitor` (the red team's text), helpers `toSheafify_comp_eqToHom`, `eqToHom_app_rationalHolomorphicFormPresheaf`, `rationalWedgePresheaf_unit_left`, and `wedgeSheaf_unit_left : (rationalConstantsToFormsSheaf X d ▷ Ω^q_ℚ) ≫ wedgeSheaf X d 0 q ≫ eqToHom (congrArg (rationalHolomorphicFormSheaf X d) (Nat.zero_add q)) = (λ_ Ω^q_ℚ).hom` |
| 6 | ledger notes of `wedge-sheaf-map` (chain-map route, the five-step Leibniz shape) and `de-rham-cup` (`S_c` and its tie to `scalarHolomorphicDeRhamComplexInt` owed; scalar laws derivable as in RT4) |
| 7 | `docs/gaps.md`, "Known weaknesses": the `Opens _.1` discrimination-tree cause and the `analyticShQMonoidal` workaround |
| 8 | `de-rham-unit-nonzero` had merged; the corollary is in this module instead: `wedgeSheaf_ne_zero : wedgeSheaf X (dim X.left) 0 0 ≠ 0` for `[Nonempty (ComplexPoint X)]`, from the unit law (a zero wedge makes `λ_ Ω⁰_ℚ` zero, so `Ω⁰_ℚ` is a zero object and `rationalDeRhamUnit X = 0`) and `Tests.rationalDeRhamUnit_ne_zero`, 14 lines; the module imports `HodgeLadder.Tests.DeRhamUnitNonzero` |

Proof of the unit law: `toSheafifyTensor_hom_ext` at `P = 𝟙_`, then `toSheafifyTensor_naturality_left` along `rationalConstantsToFormsPresheaf`, the defining square, the cast transport, and the presheaf law from `holomorphicWedge_ofConstant_left` and `holomorphicFormCast_trans`. The sheaf steps go by `Eq.trans`; the presheaf steps by `rw`. `lake env lean` on the module: about 10 s; `lake build HodgeLadder.Hodge.WedgeSheafify` 7 s.
## de-rham-rational-span: statement
Date: 2026-11-27. Phase 1 (statement and route), then the statement red team (`docs/sketches/de-rham-rational-span.redteam.md`, pass with changes, all implemented). Modules `HodgeLadder.Hodge.DeRhamRationalSpan` and `HodgeLadder.General.SimplicialCochainSpan`, imported from `HodgeLadder.lean`. Input of T1 (red team finding 10 of `cup-hodge-filtration`).
### Statement
```lean
def DeRhamRationalSpan : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ),
    Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤
theorem deRhamRationalSpan_of_simplicialComplexSpan (hS : SimplicialComplexSpan) :
    DeRhamRationalSpan
```
`ι = fieldToDeRhamCohomology ℚ X n : H^n(X; ℚ) →+ H_dR^n(X)` is upstream's map (row "Rational-to-de Rham map and the range of F^p" of `docs/conventions.md`). `H_dR^n(X)` carries upstream's `deRhamHypercohomologyComplexModule` (row "Complex structure on H_dR and on complex constant cohomology"). No sign or scalar enters: the statement is a span equality, insensitive to conjugating the action and to nonzero scalars on `ι`. It is the surjectivity half of `ℂ ⊗_ℚ H^n(X; ℚ) ≅ H_dR^n(X)`; the other half is rung `de-rham-rational-independent` (checked, red team finding 1). The rung is `stated`: `DeRhamRationalSpan` holds once `SimplicialComplexSpan` is checked.
### Finiteness, and why the route goes through singular cohomology
The change-of-coefficients map `H^n(Y; ℚ) ⊗_ℚ ℂ → H^n(Y; ℂ)` is an isomorphism when cohomology commutes with the direct sum `ℂ ≅ ⊕_I ℚ`; that holds on compact Hausdorff spaces (Godement, unverified) and fails on general topological spaces. A countable discrete space `D` is a counterexample to the tensor identity: `H^0(D; ℚ) = ℚ^ℕ`, `H^0(D; ℂ) = ℂ^ℕ`, and the ℂ-span of `ℚ^ℕ` misses every sequence whose entries span an infinite-dimensional ℚ-subspace of ℂ. `D` is no analytic space of a smooth variety, so it does not bear on the rung. The analytic space of a complex algebraic variety has finitely generated integral homology (triangulability of algebraic sets, unverified), so the statement is expected to hold for smooth separated integral `X` without projectivity; a later rung can drop `IsProjective` through `span_range_fieldToDeRhamCohomology_rat_of_simplicialComplexSpan`, which takes Hausdorffness, paracompact opens and finite generation of `H_n(X(ℂ); ℤ)` as hypotheses.
Neither upstream nor the port states the tensor form, flatness of constant-sheaf cohomology, or commutation with filtered colimits (grep for `TensorProduct`, `colimit`, `fieldToComplexCohomology`: only the injectivity `complexToFieldCohomology_leftInverse`). Finiteness is available: the port's `module_finite_singularHomology` gives `Module.Finite ℤ (H_n(X(ℂ); ℤ))` for smooth projective integral `X` (compact manifold). The route uses it through singular cohomology.
### Route
| Step | Declaration | Status |
| 1. Scaled classes | `ratScaled z : ℚ →+ ℂ`, `q ↦ z q`; `fieldToComplexConstantSheafComplexInt_comp_complexScalarComplexInt`: inclusion then `z` is `constantCoefficientSheafComplexIntMap X (ratScaled z)`; `smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt`: `z • ι' β` is the de Rham image of the class pushed along `ratScaled z`, exactly | checked |
| 2. Sheaf-side reduction | `span_range_fieldToDeRhamCohomology_rat_of_mem_closure`: if every `γ : ScalarCohomology X ℂ n` lies in `AddSubgroup.closure (⋃ z, Set.range (hypercohomologyMap X (constantCoefficientSheafComplexIntMap X (ratScaled z)) n))`, the span is `⊤` | checked |
| 3. Comparison, additive | the port's `scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange`, generalized from `f : R →+* S` to `f : R →+ S` (rung `betti-additive-naturality`) | checked |
| 4. Cochains | `SimplicialComplexSpan` (rung `simplicial-complex-span`), proved by `simplicialComplexSpan` | checked |
| 5. Assembly | `mem_closure_ratScaled`: 3 and 4, under explicit Hausdorff, paracompactness and finite-homology hypotheses, give the hypothesis of 2 | checked (unconditional through `deRhamRationalSpan`) |
| 6. Rung | `deRhamRationalSpan_of_simplicialComplexSpan`: `IsProjective` supplies `T2Space` (instance), `openParacompactSpace` and `module_finite_singularHomology`; then 2 and 5 | checked (unconditional through `deRhamRationalSpan`) |
Why the comparison must be natural in additive maps: before the generalization, the port proved naturality of `scalarCohomologyEquivOrdinarySingularCohomology` in ring maps only, and `ratScaled z` is not a ring map. Ring maps cannot replace it. A ring map into ℂ has a subring of ℂ as image; a subring that is finite-dimensional over ℚ is a number field, and the values of a complex cocycle on cycles (periods) are in general transcendental. So ring-map naturality alone reaches `ι(H^n(X; ℚ))` and no complex multiple of it; the dual-number trick (`ε ↦ zε` on `ℂ[ε]` is a ring map) needs the additive splitting `ℂ[ε] = ℂ ⊕ ℂε` on both sides, which is the same naturality.
### Sub-rungs
`betti-additive-naturality` (checked). The port's coefficient change was generalized in place: `(f : R →+* S)` became `(f : R →+ S)` in `SimplicialCochainCoefficientChange.lean`, `SingularCochainCoefficientChange.lean` and `BettiScalarNaturality.lean`, and `f.toAddMonoidHom` became `f` in the two constant-sheaf maps. The callers `SimplicialCochainDenominators.lean` and `IntegralDenominatorClearing.lean` pass `(Int.castRingHom ℚ).toAddMonoidHom`; two `simp only` calls in the first gained `RingHom.toAddMonoidHom_eq_coe`, `AddMonoidHom.coe_ofClass`, and the local `ordinarySingularCohomologyCoefficientChange_apply` in the second was generalized the same way. No proof in the three files uses `f` multiplicatively. The divergence from the upstream source is logged in `docs/port-lefschetz.md`.
`simplicial-complex-span` (checked; statement in `HodgeLadder.General.SimplicialCochainSpan`, proof in `HodgeLadder.General.SimplicialCochainSpanProof`, section "simplicial-complex-span: checked" below):
```lean
def SimplicialComplexSpan : Prop :=
  ∀ (Y : SSet.{0}) (n : ℕ) [Module.Finite ℤ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).homology n)]
    (α : (((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (Y.chainComplex (ModuleCat.of ℂ ℂ)).linearDualCochainComplex).homology n),
    α ∈ AddSubgroup.closure (⋃ z : ℂ, Set.range
      (HomologicalComplex.homologyMap (SSet.linearDualCoefficientChange (ratScaled z) Y) n).hom)
```
Proof plan, after the port's `SimplicialCochainDenominators.lean` with `ℤ ⊆ ℚ` replaced by `W ⊆ ℂ`. Represent `α` by a complex cocycle `c`. Its evaluation on integral cycles descends to `G : H_n(Y; ℤ) →ₗ[ℤ] ℂ`; put `W := Submodule.span ℚ (range G)`, finite-dimensional because `H_n(Y; ℤ)` is finitely generated. In degree `k + 1`, the map `q ∘ c` on integral chains, with `q : ℂ → ℂ ⧸ W`, vanishes on cycles, so it factors through the boundary; `ℂ ⧸ W` is divisible, so Baer's criterion (`Module.Baer.of_divisible`) extends it to `k`-chains, and subtracting the coboundary of a lift `e` gives a cocycle `c'` with values in `W` on every simplex (in degree 0 every chain is a cycle and `c' = c`). With a ℚ-basis `b` of `W`, the coordinates `aᵢ = b.repr ∘ c'` are rational cocycles (coordinates are additive, so they commute with the coboundary) and `c' = Σᵢ ratScaled (b i) ∘ aᵢ` on simplices. Hence `α = Σᵢ homologyMap (ratScaled (b i)) [aᵢ]`. Estimated 200 to 250 lines. The red team checked the plan degree by degree (finding 4).
### What is checked
`#print axioms`: `smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt`, `span_range_fieldToDeRhamCohomology_rat_of_mem_closure`, `mem_closure_ratScaled`, `span_range_fieldToDeRhamCohomology_rat_of_simplicialComplexSpan`, `deRhamRationalSpan_of_simplicialComplexSpan` and the generalized `scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange` use `[propext, Classical.choice, Quot.sound]`. The checker names them through the ledger.
Instance findings: `ScalarCohomology X ℚ n` and `ℍ^n(X; constantFieldSheafComplexInt ℚ X)` are definitionally equal but `rw` across them reports a term not type-correct under implicit transparency; the reduction goes through `congrArg` and `Eq.trans` on `hypercohomologyMap_comp_apply`. Upstream's `complexConstantCohomologyDeRhamAddEquiv_scalar` and `fieldToComplexConstantSheaf_scalar` are private, so the scalar identity is reproved at the presheaf level (`presheafToSheaf` maps, closed by `congr 1`). `IsProjective X.hom` supplies `T2Space (ComplexPoint X)` as an instance; paracompactness of opens comes from `openParacompactSpace X` as a local `let`.
### Measured result (in place of the earlier main risk)
The sketch estimated `betti-additive-naturality` at about 730 lines of copied bookkeeping. The red team measured the generalization: the three port files elaborate with only the type of `f` changed, in about 12 s, with the standard axioms. In place in the port the change is about ten lines in the three files and sixteen call sites in the two callers. Measured here: the port rebuild after the edits took 47 s wall (`lake build LefschetzPort`, after two failing passes of 23 s and 11 s that found the caller fixes), the full `lake build` 2 min 45 s, `lake build HodgeLadder.Hodge.DeRhamRationalSpan` 22 s, and `python3 tools/check.py` 20 s on the warm build. The remaining open work is `simplicial-complex-span`.
### Ledger entries
| Id | Kind | Status | Depends on | Declarations |
|---|---|---|---|---|
| `betti-additive-naturality` | foundation | checked | `lefschetz-port` | `AlgebraicGeometry.ComplexPoint.scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange` (generalized to `R →+ S`) |
| `simplicial-complex-span` | foundation | checked | | `HodgeLadder.simplicialComplexSpan`, `HodgeLadder.SimplicialComplexSpan` |
| `de-rham-rational-span` | foundation | checked | `betti-additive-naturality`, `simplicial-complex-span` | `HodgeLadder.deRhamRationalSpan`, `HodgeLadder.span_range_fieldToDeRhamCohomology_rat`, `HodgeLadder.DeRhamRationalSpan`, `HodgeLadder.deRhamRationalSpan_of_simplicialComplexSpan`, and the steps above |
| `de-rham-rational-independent` | foundation | checked | `betti-additive-naturality`, `de-rham-rational-span` | `HodgeLadder.Hodge.DeRhamRationalIndependent`: `linearIndependent_fieldToDeRhamCohomology_rat` and the three companion theorems |
| `de-rham-p2-top-rank` | test | open | `de-rham-rational-span`, `cycle-class-sign-test-p2`, `de-rham-injective` | `Module.finrank ℂ H_dR^4(projectivePlane) = 1` |

## de-rham-rational-independent: statement
Date: 2026-11-27. Phase 1 (statement and proof), then the red team (`docs/sketches/de-rham-rational-independent.redteam.md`, pass with changes, all implemented). Module `HodgeLadder.Hodge.DeRhamRationalIndependent`, imported from `HodgeLadder.lean`. Proposed by the red team of `de-rham-rational-span` (finding 1). Input of T1: with `de-rham-rational-span` it gives `ℂ ⊗_ℚ H^n(X; ℚ) ≅ H_dR^n(X)`, and so `dim_ℂ H^1_dR = dim_ℚ H^1(X; ℚ)` for the eigenspace count.
### Statement
```lean
theorem linearIndependent_fieldToDeRhamCohomology_rat (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (n : ℕ) {ι : Type} {v : ι → H^n(X; ℚ)}
    (hv : LinearIndependent ℚ v) :
    LinearIndependent ℂ (fieldToDeRhamCohomology ℚ X n ∘ v)
theorem injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    Function.Injective (LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n))
```
The first is the statement of record, verbatim from the ledger note. Both are corollaries of `_of_smooth` versions that drop `IsProjective` (and take `{ι : Type*}`). `ι` and the ℂ-structure on `H_dR^n(X)` are upstream's, as in `de-rham-rational-span`; the ℚ-structure on `H^n(X; ℚ)` is upstream's `fieldCohomologyModule` (change of coefficients along `q ↦ r q`). The statement is a linear independence, insensitive to conjugating the ℂ-action and to nonzero scalars on `ι`. The rung is proved outright, with no `Prop` and no conditional.
### Hypotheses
`IsIntegral X.left` and `Smooth X.hom` only, the ones upstream's `ι` needs to exist. `IsProjective` is unused: the proof stays in sheaf cohomology on `X(ℂ)`, so it needs no comparison with singular cohomology, no Hausdorffness, no paracompactness and no finiteness. This matches the expectation in red team finding 1. The independence half holds on any space; only the span half needs finiteness (the discrete-space example above breaks only the span).
### Route
| Step | Declaration | Status |
|---|---|---|
| 1. Functoriality | `constantCoefficientSheafMap_comp`, `constantCoefficientSheafComplexIntMap_comp`: change of coefficients along additive maps composes, on the constant sheaf and on the integer-indexed complex | checked |
| 2. Scalars | `constantCoefficientSheafComplexIntMap_mulLeft`: along `q ↦ r q` it is upstream's `fieldScalarComplex ℚ X r` (`rfl`); `toAddMonoidHom_comp_ratScaled`: for `φ : ℂ →ₗ[ℚ] ℚ`, `φ ∘ ratScaled z = (q ↦ φ z · q)` | checked |
| 3. Relation | `∑ zᵢ • ι vᵢ = 0` becomes `∑ (ratScaled zᵢ)_* vᵢ = 0` in complex constant cohomology, by `smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt` (step 1 of `de-rham-rational-span`) and injectivity of `complexConstantCohomologyDeRhamAddEquiv` | checked |
| 4. Retraction | push the relation along `φ_*` for every `φ : Module.Dual ℚ ℂ`: by 1 and 2 and `hypercohomologyAddEquivConstantCohomology_symm_smul`, `∑ φ(zᵢ) • vᵢ = 0` in `H^n(X; ℚ)`; independence gives `φ zᵢ = 0`; `Module.forall_dual_apply_eq_zero_iff` gives `zᵢ = 0` | checked |
| 5. Base change | `Module.Basis.ofVectorSpace ℚ H^n(X; ℚ)` base-changed to ℂ; `liftBaseChange` sends it to `ι ∘ b`, independent by 4; a linear map carrying a basis to an independent family is injective (`Finsupp.apply_linearCombination`, `linearCombination_repr`) | checked |
No choice of a ℚ-basis of the span of the `zᵢ` is needed: separating points of ℂ by ℚ-linear functionals does the same job. The proof does not use the comparison theorem of `betti-additive-naturality`; it uses that rung's generalization of `constantCoefficientSheafComplexIntMap` to additive maps, and the checked step 1 of `de-rham-rational-span`. Dependencies: `betti-additive-naturality`, `de-rham-rational-span`.
### What is checked
`#print axioms` on all eight declarations (`linearIndependent_fieldToDeRhamCohomology_rat{,_of_smooth}`, `injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat{,_of_smooth}`, `constantCoefficientSheafMap_comp`, `constantCoefficientSheafComplexIntMap_comp`, `toAddMonoidHom_comp_ratScaled`, `constantCoefficientSheafComplexIntMap_mulLeft`): `[propext, Classical.choice, Quot.sound]`. Trivial proofs fail: `simp` and `aesop` leave the goal open; `hv.map'` with `ker_fieldToDeRhamCohomologyLinear_rat` (injectivity over ℚ) gives only ℚ-independence and does not typecheck against the ℂ goal; `restrict_scalars'` goes the wrong way (needs `SMulWithZero ℂ ℚ`). After the red team, with the root import and the eight theorems named in the ledger (four for the rung, four conditional base-change forms), the full `python3 tools/check.py` accepts all of them with the standard axioms.
Instance findings: as in `de-rham-rational-span`, `ℍ^n(X; constantFieldSheafComplexInt ℚ X)` and `ℍ^n(X; constantCoefficientSheafComplexInt X ℚ)` agree only up to unfolding, so the main proof runs under `set_option backward.isDefEq.respectTransparency false` and closes one step by `rfl` after `rw`. The complex-level functoriality needs the same option; the sheaf-level one goes through the `presheafToSheaf` spelling and `congr 1`.
### Timings
`lake env lean` on the module: 19 s for the independence proof alone, 34 s with the base-change form. `lake build HodgeLadder.Hodge.DeRhamRationalIndependent`: 30 s for the module (36 s wall). `python3 tools/check.py --no-build`: 14 s; the full `python3 tools/check.py` after the root import: 68 s. 158 lines including docstrings at phase 1, 205 with the conditional base-change forms (the module then elaborates in 52 s).
### Base change, conditional (red team finding 7)
The module also holds the identity `ℂ ⊗_ℚ H^n(X; ℚ) ≅ H_dR^n(X)` in conditional form. `bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_span` and `finrank_deRham_eq_finrank_rat_of_span` take the span equality for one `X` and degree; the `_of_simplicialComplexSpan` versions take `hS : SimplicialComplexSpan` and `IsProjective`, through `deRhamRationalSpan_of_simplicialComplexSpan`. Surjectivity is `Submodule.span_le` on `1 ⊗ₜ x ↦ ι x`; the rank is `LinearEquiv.ofBijective` with `Module.finrank_baseChange`. They are named in this rung's ledger entry so the checker reads their axioms. The unconditional forms are the open rung `de-rham-rational-base-change` (depends on `de-rham-rational-independent` and `simplicial-complex-span`), which also records the optional `gm2` test of red team finding 7b and its missing input, ℚ-independence of the two winding classes in `H^1(gm2; ℚ)`.
### Ledger entry (proposed)
| Id | Kind | Status | Depends on | Module | Declarations |
|---|---|---|---|---|---|
| `de-rham-rational-independent` | foundation | checked (after the red team pass) | `betti-additive-naturality`, `de-rham-rational-span` | `HodgeLadder.Hodge.DeRhamRationalIndependent` | `HodgeLadder.linearIndependent_fieldToDeRhamCohomology_rat`, `HodgeLadder.linearIndependent_fieldToDeRhamCohomology_rat_of_smooth`, `HodgeLadder.injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat`, `HodgeLadder.injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_smooth` |

## simplicial-complex-span: checked
Date: 2026-11-27. Module `HodgeLadder.General.SimplicialCochainSpanProof` (380 lines, no elaborator options), imported from `HodgeLadder.lean`; `HodgeLadder.Hodge.DeRhamRationalSpan` now imports it and adds `deRhamRationalSpan : DeRhamRationalSpan` and `span_range_fieldToDeRhamCohomology_rat` (one `X`, one `n`). Rung `de-rham-rational-span` is checked with it. The type of `SimplicialComplexSpan` is unchanged; only its docstring status word moved.
### Proof structure
| Step | Declaration | Content |
| Evaluation | `cochainEval Y n c : C_n(Y; ℤ) →ₗ[ℤ] R` | an `R`-valued cochain on integral chains, any commutative ring `R`; the port's `ratEval` for general `R`, with `_sub`, `_zero`, `_dualMap_d`, `_d_eq_zero`, and `_dualCoefficientChange` (evaluation after coefficient change along `f : R →+ S` is `f` of the evaluation) |
| 1. Periods | `exists_finiteDimensional_cochainEval_mem` | a complex cocycle's evaluation on integral cycles descends to `G : H_n(Y; ℤ) →ₗ[ℤ] ℂ` (`descHomology`); `range G` is generated by a finite set `s` (`Module.finite_def`, `Submodule.FG.map`), and every value lies in `W := span ℚ s` (`Submodule.span_le_restrictScalars`), finite-dimensional by `FiniteDimensional.span_finset` |
| 2. Coordinates | `exists_sum_ratScaled_eq` | for `W` finite-dimensional, a left inverse `π : ℂ →ₗ[ℚ] W` of the inclusion (`LinearMap.exists_leftInverse_of_injective`) and `Module.finBasis ℚ W` give `λᵢ = coord i ∘ π : ℂ →+ ℚ`, `wᵢ = bᵢ` with `Σ ratScaled wᵢ (λᵢ x) = x` on `W` |
| 3. Baer | `exists_dualMap_d_eq_of_cochainEval` | a complex cochain `f` of degree `k + 1` vanishing on integral cycles is `δe`: `f` factors through `∂ : C_{k+1}(Y; ℤ) → B_k`, the factor extends to `C_k(Y; ℤ) →+ ℂ` by `Module.Baer.of_divisible` for `ℂ` (`divisibleByIntOfCharZero`), and `e` is its value on simplices; `δe = f` is checked simplex by simplex through the port's `intChainsLift_comp_d` |
| 4. Class fixed | `homologyMap_linearDualCoefficientChange_eq` | if `P : ℂ →+ ℂ` fixes the values of the cocycle on integral cycles, `(P)_*` fixes its class: `P ∘ c − c` vanishes on integral cycles, so it is `δe` by step 3 for `n = k + 1` and is `0` for `n = 0` (every chain is a cycle) |
| 5. Rung | `simplicialComplexSpan` | with `P = Σ ratScaled wᵢ ∘ λᵢ` from steps 1 and 2, `α = (P)_* α = Σ (ratScaled wᵢ)_* ((λᵢ)_* α)` by `linearDualCoefficientChange_add`, `_zero`, `_comp` and `HomologicalComplex.homologyMap_add`, `_zero`, `_comp` |
### Deviation from the plan
The plan of the statement section used the quotient `ℂ ⧸ W`, a Baer extension into it, a lift back to `ℂ`, and coordinates of the resulting `W`-valued cocycle. The proof replaces the quotient by a ℚ-linear projection `π` onto `W`: the coboundary step is then Baer into `ℂ` itself, with no lift, and the coordinates `λᵢ` are additive maps `ℂ → ℚ`, so the rational cocycles are the images `(λᵢ)_* c` under the port's coefficient change and need no separate cocycle proof. The finiteness hypothesis enters only in step 1, as the red team's finding 4 predicted.
`#print axioms` on `simplicialComplexSpan`, `deRhamRationalSpan`, `span_range_fieldToDeRhamCohomology_rat` and the four step theorems: `[propext, Classical.choice, Quot.sound]`. Trivial proofs fail: after `intro`, `simp` makes no progress on `SimplicialComplexSpan` and leaves the span goal of `DeRhamRationalSpan` open. Measured: `lake env lean` on the proof module 8 to 13 s wall; `lake build HodgeLadder` after the change 31 s; `python3 tools/check.py` 22 s on the warm build, all checks accepted.
### For the red team
Red team verdict: pass with changes (`docs/sketches/simplicial-complex-span.redteam.md`); the three `set_option backward.isDefEq.respectTransparency false` lines were measured unneeded and deleted, `cochainEval` and `linearDualCoefficientChange_zero` were added to the ledger, and the gaps row names the `SSet` ambiguity case. Attack points given to it: (a) the docstring claim that `SimplicialComplexSpan` is unchanged (diff of `SimplicialCochainSpan.lean` is docstrings only); (b) degree `0`, where the Baer step is skipped and `P ∘ c = c` is read from `ChainComplex.next_nat_zero` and the shape of the integral complex; (c) that `ratScaled (b i)` with `b i ∈ W ⊆ ℂ` is the posted `ratScaled z`, with no ring-map or ℚ-linearity assumption on `λᵢ`; (d) whether the general lemmas (`cochainEval`, the three `linearDualCoefficientChange` lemmas) clash with names in the port or upstream at the pin (`docs/gaps.md` row).
