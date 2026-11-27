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
| `wedge-descends` | `WedgeDescends`: `chartEvaluationKernel` is a two-sided ideal for `formWedge` | stated |
| `tensor-bounded-quasi-iso` | `TensorBoundedQuasiIso`: `QuasiIso (tensorHom f (𝟙 M))` for `M` strictly bounded, with `HasTensor` hypotheses | stated |
| `rational-de-rham-complex` | `Ω•_ℚ` with `forget(Ω•_ℚ) ≅ Ω•(X)`, truncations `F^p`, unit over `fieldToHolomorphicDeRhamComplexInt ℚ X` | open |
| `wedge-presheaf` | `formWedge` descends to `HolomorphicForm X d U`, natural under `holomorphicFormRestriction` | checked |
| `wedge-sheafify` | `Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ` through the monoidal sheafification | open |
| `wedge-sheaf-map` | `deRhamWedge` a morphism of complexes, `filteredWedge p q` compatible with inclusions, unit law | open |
| `derived-tensor-bounded` | additive `T_B` with `Q ⋙ T_B ≅ tensorRightComplex Y B ⋙ Q`, natural in `B`; generic unit iso | checked |
| `pairing-product` | `pairProduct`, naturality, biadditivity, `pairProduct λ x y = y.comp x` on `ℚ_X[0]` | open |
| `de-rham-injective` | `Function.Injective (fieldToDeRhamCohomology ℚ X n)` | open |
| `de-rham-cup` | `deRhamCup`, bilinearity, `fieldToDeRhamCohomology_cup` | open |
| `de-rham-cup-test-p2` | `deRhamCup (ι [L₀]) (ι [L₁]) 4 _ ≠ 0` on `projectivePlane` | open |
| `cup-hodge-filtration` | `deRhamCup_mem_hodgeFiltration`, statement (a) | open |
| `cup-hodge-classes` | `CupPreservesHodgeClasses`, `CupRespectsHodgeFiltrationRational` | stated |
| `cup-hodge-classes-test-p2` | `Tests.projectivePlane_exists_hodge_cup_ne_zero` | checked |
| `de-rham-cup-antisymm-h1` | antisymmetry of `deRhamCup` on `H¹_dR × H¹_dR` (T1 input) | open |
| `de-rham-rational-span` | `Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤`, X projective (T1 input) | open |

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
