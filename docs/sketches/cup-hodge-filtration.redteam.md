# Red team: `cup-hodge-filtration` (statement and plan)

Date: 2026-11-26. Worktree `cup-hodge-filtration` at base `6084c3a` (same commit as `main`), uncommitted `HodgeLadder/Hodge/CupFiltration.lean` and `docs/sketches/cup-hodge-filtration.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, unchanged from `main`.

Read: the ledger entries `cup-hodge-filtration`, `markman-statement`, `cup-product`, `cup-graded-commutative`, `cup-positive-degree-test-p2`, `lefschetz-1-1-equality`; the module and the sketch; decisions 0003, 0008, 0009; `docs/notes/2026-11-25-markman-inventory.md` (target T1); upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean`, `HolomorphicDeRham.lean`, `AnalyticDifferentialForms.lean`, `Mathlib/Algebra/Homology/StupidTruncation.lean`; Mathlib `ComplexShapeSigns.lean`, `BifunctorShift.lean`, `BifunctorHomotopy.lean`, `Monoidal.lean`, `DerivedCategory/Fractions.lean`, `Localization/CalculusOfFractions/Preadditive.lean`, `Shift/ShiftedHom.lean`; `docs/conventions.md`.

Scratch (inside the worktree, deleted afterwards): RT1 elaborates a copy of the module, prints axioms, and tries trivial proofs; RT2 proves `F^p = ⊤` for `p ≤ 0`; RT3 exhibits Hodge classes on ℙ² with a nonzero cup product; RT4 proves that every degree-zero class is a Hodge class. RT1 took about two minutes; the others under ten seconds each.

**Verdict: pass with changes** for the statements (b) `CupPreservesHodgeClasses` and (a_ℚ) `CupRespectsHodgeFiltrationRational`, for the proved reduction, and for the plan for (a). The rung cannot be posted in its present form. The module contains `sorry` and the checker rejects it (finding 3). The ledger title promises (a), and (b) alone does not deliver (a) (finding 2). Changes 1 to 6 below are required before the module lands; 7 to 10 are for the sub-rung plan.

## 1. Is this the statement the literature makes?

Sources: [`Voisin2002`] I, the Hodge filtration on de Rham cohomology of a compact Kähler manifold is multiplicative, and the Hodge classes form a graded subring of `⊕ H^{2k}(X; ℚ)` (section numbers unverified); [`Deligne1982`] uses the same ring (unverified page). The underlying mechanism is that the wedge product `F^p Ω• ⊗ F^q Ω• → F^{p+q} Ω•` is a map of filtered complexes.

| Literature | Lean | Check |
|---|---|---|
| X smooth projective over ℂ | `X : Over (Spec ↧ℂ)`, `[IsIntegral X.left]`, `[Smooth X.hom]`, no `IsProjective` | more general. Upstream's `F^p` on a non-projective X is the naive (stupid-truncation) filtration, which is multiplicative on every complex manifold, so (a), (a_ℚ) and (b) stay true there. No falsity from the extra generality |
| `H^k(X; ℚ)` with cup product | `H^a(X; ℚ)` (Mathlib `Sheaf.H` of the constant sheaf), `HodgeLadder.Cup.cup` | the checked Yoneda cup, pinned exactly against the singular cup (row "Cup product") |
| `F^p H^k(X; ℂ)` | `hodgeFiltration X p k`, the image of `ℍ^k(X; F^p Ω•) → ℍ^k(X; Ω•)` with `F^p Ω•` the stupid truncation in form degrees `≥ p` | the literature's definition through the holomorphic de Rham complex |
| `H^k(X; ℚ) → H^k(X; ℂ)` | `fieldToDeRhamCohomology ℚ X k`: `algebraMap ℚ ℂ`, then constants into 0-forms | no Tate twist and no conjugation. A twist by `(2πi)^p` would not change any membership statement here |
| `Hdg^p = H^{2p}(X; ℚ) ∩ H^{p,p}` | `hodgeClasses ℚ X p`: `ι α ∈ F^p ⊓ conj⁻¹(F^p)` | for projective X this is the literature's `H^{p,p}` condition (upstream docstring); for general X it is upstream's definition, and (b) holds for it |
| `F^p H^a ∪ F^q H^b ⊆ F^{p+q} H^{a+b}`, complex classes | (a), planned: `deRhamCup_mem_hodgeFiltration` | needs a product on `H_dR^*`, which the pin lacks (finding 4) |
| same, restricted to `ι` of rational classes | (a_ℚ) `CupRespectsHodgeFiltrationRational` | weaker than (a). Membership, so insensitive to the order of the factors and to any nonzero scalar |
| `Hdg^p ∪ Hdg^q ⊆ Hdg^{p+q}` | (b) `CupPreservesHodgeClasses` | the literature's statement at full strength. The unit is free: RT4 proves `Hdg^0(X; ℚ) = ⊤` in three lines from RT2 |

The reduction (b) ⇐ (a_ℚ) is sound. The rational part holds by the type of `Cup.cup`. The conjugate part follows from the filtration part through the checked `deRhamConj_fieldToDeRhamCohomology` (`mem_hodgeClasses_of_mem_hodgeFiltration`). The degree bookkeeping (`2 * (p + q)` as a natural number cast to ℤ, `p + q` cast as `↑p + ↑q`) is done by `Nat.cast_add` and elaborates. RT1: `mem_hodgeClasses_iff_mem_hodgeFiltration`, `cupPreservesHodgeClasses_of_rational`, `formWedge_differential`, `involute_of_mem_exteriorPower` and the instance `curriedTensor_additive` depend on `[propext, Classical.choice, Quot.sound]`; `cup_mem_hodgeClasses` depends on `sorryAx`.

## 2. Can the hypotheses be satisfied?

Yes, with a nonzero product. RT3, standard axioms, in the namespace `HodgeLadder.RT` of a scratch file importing `HodgeLadder.Divisor.LefschetzEquality` and `HodgeLadder.Tests.CupPositiveDegreeP2`:

```lean
theorem projectivePlane_exists_hodge_cup_ne_zero :
    ∃ α β : H^(2 * 1)(projectivePlane; ℚ), α ∈ Hdg^1(projectivePlane; ℚ) ∧
      β ∈ Hdg^1(projectivePlane; ℚ) ∧ Cup.cup α β (2 * (1 + 1)) (by ring) ≠ 0 :=
  ⟨_, _, cycleComponentSheafClass_mem_hodgeClasses_one _ _ (coheight_planeLine 0),
    cycleComponentSheafClass_mem_hodgeClasses_one _ _ (coheight_planeLine 1),
    planeLines_cup_ne_zero⟩
```

`projectivePlane` satisfies `IsIntegral` and `Smooth` (instances in `HodgeLadder.Tests.ProjectivePlane`). The open point in the sketch's kill risk 6 (whether the line classes are Hodge classes) is settled by the checked `cycleComponentSheafClass_mem_hodgeClasses_one`. (b) applied to this pair gives `[pt] = [L₀] ∪ [L₁] ∈ Hdg^2(ℙ²; ℚ)` (`planeLines_cup_eq_planeOrigin`), a codimension-two case of `CycleClassesAreHodge` that the ladder does not have. So (b) proves something new on the smallest test variety.

For (a_ℚ), any `X` and zero classes satisfy the hypotheses. The pair above satisfies them with `a = b = 2`, `p = q = 1`.

## 3. Is the conclusion trivially true?

Attempts that failed (RT1): `intro …; simp_all [hodgeClasses, hodgePiece]` on (b) leaves the filtration and conjugate goals; `simp_all [hodgeFiltration]` on (a_ℚ) leaves `∃ x, filteredToDeRhamCohomology X (p + q) n x = ι (α ∪ β)`; `exact?` finds no proof of (b) → (a_ℚ), so the two statements are not interchangeable by unfolding.

Degenerate cases found (RT2, RT4, standard axioms):

```lean
theorem hodgeFiltration_eq_top_of_nonpos (p : ℤ) (hp : p ≤ 0) (n : ℤ) :
    hodgeFiltration X p n = ⊤ := by
  have : Ω•(X).IsStrictlyGE p := CochainComplex.isStrictlyGE_of_ge Ω•(X) p 0 hp
  have hiso : IsIso (hodgeFilteredDeRhamInclusion X p) := by
    unfold hodgeFilteredDeRhamInclusion
    exact HomologicalComplex.stupidTruncInclusion_isIso (K := Ω•(X))
      (e := ComplexShape.embeddingUpIntGE p)
  rw [eq_top_iff]
  intro x _
  refine ⟨hypercohomologyMap X (inv (hodgeFilteredDeRhamInclusion X p)) n x, ?_⟩
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, IsIso.inv_hom_id]
  exact Localization.SmallShiftedHom.comp_mk₀_id _ _ _

theorem mem_hodgeClasses_zero (α : H^(2 * 0)(X; ℚ)) : α ∈ Hdg^0(X; ℚ) :=
  mem_hodgeClasses_of_mem_hodgeFiltration X 0 α
    (by rw [hodgeFiltration_eq_top_of_nonpos X _ (by simp)]; trivial)
```

So (a_ℚ) is trivial when `p + q ≤ 0`, and in (b) the hypothesis on a factor of codimension zero is automatic. In both cases the conclusion keeps content when the other index is positive. No definition unfolds to `True`, no index type is empty, both hypotheses are used. Mathematically `F^{k} H^{2k} = H^{2k}` whenever `h^{2k−j, j} = 0` for `j > k`, for example in top degree; on ℙ² every instance of (b) is true for that reason, though the ladder cannot see it. A Lean test on a variety where `F^{p+q} ≠ ⊤` needs Hodge theory and is out of reach. Recorded under 7b.

## 4. Interface rung?

No. The rung adds no structure and no axioms. The planned `deRhamCup` is a definition built from upstream objects and Mathlib, with the same status as `HodgeLadder.Cup.cup`; decision 0003 forbids structures that postulate a missing object with its properties, and a concrete definition is outside that ban. Two conditions keep it outside: no `sorry` in its body, and no `Classical.choose` of "a bilinear product satisfying …". Choice of resolutions or roofs is fine when the value is proved independent of the choice. Finding 4 adds the pinning that the definition needs.

## 5. Checker

`python3 tools/check.py --no-build` in the worktree: `REJECTED (sorry: HodgeLadder/Hodge/CupFiltration.lean:36, :53, :109, :169, :204)`. The scan is textual: lines 36 and 53 are the word in the module docstring, lines 109, 169 and 204 are proof terms. Every other ledger declaration is accepted with the three standard axioms. No checked rung is affected.

## 6. Conventions

| Convention | Used by | Truth depends on it? | Register |
|---|---|---|---|
| Cup product order (Yoneda, diagrammatic: `α ∪ β = α ≫ β⟦a⟧`, Mathlib `ShiftedHom.comp`) | (b), (a_ℚ), `fieldToDeRhamCohomology_cup` | (a_ℚ), (b): no (membership). The identity: yes | row "Cup product", present |
| Koszul sign of ℤ-indexed tensor, `ε₂(p, q) = (−1)^p` (`ComplexShape.ε_up_ℤ`) | `formWedge_differential` as a chain-map statement, `deRhamWedge` | yes for the chain-map property; a wedge with the wrong sign is not a chain map, so the kernel would catch it | new row "Tensor product of ℤ-indexed cochain complexes and its shifts" (the existing row cites `ComplexShape.down ℕ` only) |
| Shift of a tensor: first variable no sign (`mapBifunctorShift₁Iso`), second variable `(−1)^{p·y}` (`mapBifunctorShift₂Iso`) | the pairing `x ⋆ y` | the sign of `fieldToDeRhamCohomology_cup` | same new row |
| Wedge of algebraic forms, first factor on the left; Leibniz with `(−1)^p` | `formWedge`, `wedge-descends`, `wedge-sheaf-map` | identities between `deRhamCup` and form products | new row "Wedge product of algebraic forms" |
| de Rham cup order | `deRhamCup`, `fieldToDeRhamCohomology_cup`, T1 | identities only | new row "de Rham cup order (proposed)", finding 5 |
| `ι` normalization (no `(2πi)^p`), range of `F^p` (`⊤` for `p ≤ 0`) | all statements | membership: no; identities: yes | new row "Rational-to-de Rham map and the range of F^p" |
| Hodge filtration, Hodge classes | all | yes (which classes count) | rows present |
| Rational Ext normalization (`rationalExtEquiv`), `hypercohomologyAddEquivConstantCohomology`, `ext-derived-bridge` | sub-rung `rational-hypercohomology-equiv` | the scale of the identity: a non-unit scalar in the bridge would rescale `deRhamCup` against `Cup.cup` | rows present; the sub-rung must prove agreement on `ℚ_X[0]` with no scalar |

No borrowed result with an external sign is used. The one cited input, upstream's `extDeriv_mul`, is used as stated, and its `involute` sign is computed in `involute_of_mem_exteriorPower`.

## 7. Equality first

(a), (a_ℚ) and (b) are closure statements (membership in a subgroup). The identity in this rung is `fieldToDeRhamCohomology_cup`; it must be proved exactly, with no scalar and with the sign fixed by the definition (finding 5). The equality these statements serve is T1 of the Markman inventory, `W_K ≤ Hdg^1` on an abelian surface of Weil type and then `W_K ⊆ algebraicCycleClassSpan` through the checked `lefschetzOneOneEquality_holds`. T1 has no ledger rung yet, and nothing in the ledger depends on `cup-hodge-filtration`.

## 7b. Non-vacuity tests

| Statement | Smallest test | Exists? |
|---|---|---|
| (b) hypotheses | `projectivePlane_exists_hodge_cup_ne_zero` (section 2), from `HodgeLadder.cycleComponentSheafClass_mem_hodgeClasses_one`, `HodgeLadder.Tests.coheight_planeLine`, `HodgeLadder.Tests.planeLines_cup_ne_zero` | proved in scratch; add as `HodgeLadder.Tests.projectivePlane_exists_hodge_cup_ne_zero` |
| (b) conclusion | `planeOrigin_mem_hodgeClasses : cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin_add ∈ Hdg^(1 + 1)(projectivePlane; ℚ)` (the right side of `HodgeLadder.Tests.planeLines_cup_eq_planeOrigin`), from (b), the two line memberships and that identity | no; three lines once (b) is checked |
| `deRhamCup` is not the zero or square-zero product | `deRhamCup projectivePlane (ι [L₀]) (ι [L₁]) 4 _ ≠ 0`, from `fieldToDeRhamCohomology_cup`, `planeLines_cup_ne_zero` and injectivity of `ι` | no. Injectivity of `fieldToDeRhamCohomology ℚ X n` is small: a ℚ-linear retraction `ℂ → ℚ` gives a map of constant complexes whose composite with `fieldToComplexConstantSheafComplexInt ℚ X` is the identity, so `hypercohomologyMap` of the inclusion has a left inverse (`hypercohomologyMap_comp_apply`, `comp_mk₀_id`); `complexConstantCohomologyDeRhamEquiv` is a bijection |
| `F^{p+q} ≠ ⊤` somewhere (the conclusion of (a_ℚ) not automatic in positive degree) | a class outside `F^1 H^1` on an elliptic curve | no; needs Hodge theory. Recorded as a known weakness |

## 8. Pin drift

The worktree pin equals `main`'s (`lakefile.toml` rev `2ead713…`). No checked rung is involved. Nothing to diff.

## Findings

1. **(b) and (a_ℚ) are faithful** (section 1). (b) is the literature's ring statement at full strength, the unit being free (RT4). (a_ℚ) is weaker than the literature's (a); it is the right intermediate for (b). The reduction is proved with the standard axioms.

2. **Title against content.** The ledger title "F^p ∪ F^q ⊆ F^{p+q}, so products of Hodge classes are Hodge classes" names (a) first. (b) does not imply (a), and T1 needs (a) for complex classes (finding 10). The sketch's own recommendation (check the rung only with (a)) is right; implement it as separate ids (change 2).

3. **The module cannot land.** The checker rejects it (section 5). A sorried theorem on `main` is forbidden; a `stated` rung needs a sorry-free `Prop`. Even the word in a docstring trips the scan.

4. **`deRhamCup` is a legitimate local definition and needs pinning.** The zero product satisfies `deRhamCup_mem_hodgeFiltration` and ℂ-bilinearity, so (a) alone says nothing about the definition. `fieldToDeRhamCohomology_cup` pins it on the image of `ι`, bilinearity on the ℂ-span of that image, and the ℙ² test of 7b rules out the zero and square-zero products. Off the span, its only description is the construction. T1 uses (a) on complex classes inside the span, so T1 also needs the span statement (finding 10). Record `deRhamCup` and the pairing in `docs/gaps.md` under "General lemmas kept local" (decision 0011) when they land.

5. **Factor order: swap at the definition.** The construction gives `pairProduct μ x y = y ≫ (x ⊗ B)⟦b⟧`, which on `ℚ_X[0]` is `y.comp x`. Keep that primitive and define `deRhamCup x y := pairProduct μ y x`. Then `ι (α ∪ β) = deRhamCup (ι α) (ι β)` holds exactly with no sign, with the same proof as the sketch's reversed identity, and `deRhamCup` is in the diagrammatic order of `Cup.cup`. `ι` becomes a homomorphism, so T1's expansion of `w = Σ cᵢⱼ eᵢ ∪ eⱼ` maps term by term. The right-action variant gives the same function: on `ℚ_X[0]` the sign of `mapBifunctorShift₂Iso` is `(−1)^{0·b} = 1`, and on cochains it turns `θ ⊗ η` into `(−1)^{ab} θ ⊗ η`, the class of `η ∧ θ`. It only adds sign bookkeeping, so reject it. The resulting rule for the ladder: sheaf-side products (`Cup.cup`, `deRhamCup`) are diagrammatic; cochain and form products (`cupSing`, `relCupSing`, `formWedge`) are classical; comparisons between the two reverse the factors with no sign. Registered as the row "de Rham cup order (proposed)".

6. **Route: sound, and cheaper than the sketch says.** `Q : CochainComplex (ShQ Y) ℤ ⥤ DerivedCategory` is a localization at quasi-isomorphisms, so once `tensor-bounded-quasi-iso` holds, `T_B := Localization.lift (tensorRight B ⋙ Q) _ Q` exists with `Q ⋙ T_B ≅ tensorRight B ⋙ Q`. That removes the universe and lifting part of kill risk 1. The pairing applies `T_B` to unshifted objects only: it uses `Q`'s own `commShiftIso` and the no-sign iso `mapBifunctorShift₁Iso` on complexes, so `[T_B.CommShift ℤ]` is unnecessary. Drop it from `derived-tensor-bounded`. Additivity of `T_B`, needed for bilinearity, is the remaining real point. It follows from `Localization.functor_additive_iff` along `HomotopyCategory → DerivedCategory` (which has a calculus of fractions, `DerivedCategory/Fractions.lean`), after descending `tensorRight B` to the homotopy category with `mapBifunctorMapHomotopy₁` (`BifunctorHomotopy.lean`). The sketch's fallback through K-injective resolutions is weaker than this: Mathlib gives bounded roofs directly (`DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE`), and any roof-level definition must reprove independence of the roof, which the lift gives for free. Keep it as a last resort only.

7. **`quasiIso_tensorHom_id_of_bounded` is true as stated.** The cone of `f ⊗ 𝟙_M` is acyclic because the cone of `f` is, `M` has finitely many nonzero terms, and each `− ⊗ M^j` is exact (`tensor_exact`); the stupid-filtration induction in the docstring is the Lean form of this, and stalks are not needed. Strict boundedness of `M` is stronger than necessary over ℚ and holds for every use (`Ω•`, `F^p Ω•`, `ℚ_X[0]`). The mirror statement `tensorHom (𝟙 M) f` is not used by the route (only `− ⊗ B` is lifted; naturality in `B` is along chain maps); drop it unless a later step needs it.

8. **`wedge-descends` is true, and only half of it is stated.** Chart evaluation is `𝒪(U)`-linear, and at a fixed point it is multiplicative (it factors through `⋀ Ω_{𝒪(U)} → ⋀ (ℂ^d)^*` followed by `wedgeCovectors`), so a form that evaluates to zero everywhere wedges to one that does. The docstring derives the other side from graded commutativity of the exterior algebra, which Mathlib does not have at the pin for `⋀^p · ⋀^q` (the only commutation lemma found is `CliffordAlgebra.mul_ι_mul_ι_mul_comm`). State both sides; the same multiplicativity proves both.

9. **Sub-rung order and sizes.** Mostly right. Changes: (i) move `rational-hypercohomology-equiv` to the front. It is independent of the tensor, carries kill risk 4 (instance spellings: upstream's local `HasDerivedCategory.standard`, `HasExt.{0}`, the `ULift ℤ` source), and is the cheapest probe of whether the identity can be stated at all. (ii) Split `wedge-sheaf-map` into the presheaf wedge (descent plus naturality under `formRestriction`), its sheafification through the monoidal sheafification, and the chain-map check on `ιTensorObj` components with `formWedge_differential`. (iii) Add three small rungs: `hodge-filtration-nonpos` (RT2, checked in scratch), `de-rham-injective` (7b), and the ℙ² tests of 7b. (iv) `derived-tensor-bounded`: no `CommShift`, add `Additive` (finding 6).

10. **What T1 needs, beyond this rung.** (a) on complex classes; ℂ-bilinearity; `fieldToDeRhamCohomology_cup`; the Hodge decomposition `H^1_dR = F^1 ⊕ conj F^1` on an abelian surface (the sketch lists it); and two items the sketch omits. The first is antisymmetry of `deRhamCup` on `H^1 × H^1`, needed to cancel the `(0,1) ∪ (0,1)` part of a Weil class. It follows from `HodgeLadder.Cup.cup_gradedComm`, `fieldToDeRhamCohomology_cup` and bilinearity once the image of `ι` spans. The second is that span: `Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤`, a universal-coefficient statement for `H^n(X; ℚ) ⊗ ℂ → H^n(X; ℂ)` that needs compactness or finiteness of `X(ℂ)`. Both go on T1's list, with separate ids.

## Recommended changes

Required before the module lands:

1. Replace the three sorried theorems by `Prop` definitions and delete `cup_mem_hodgeClasses`. Exact text (inside the existing sections, which already open `CliffordAlgebra`, `MonoidalCategory Cup Limits` and the local instance `sheafMonoidal`):

```lean
/-- **Wedge descends** (sub-rung `wedge-descends`, open). A form whose chart evaluations vanish
wedges, on either side, with any form to a form whose chart evaluations vanish; so the wedge
product descends to upstream's holomorphic forms. -/
def WedgeDescends : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (U : (TopologicalSpace.Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p q : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    (η : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) q),
    (θ ∈ chartEvaluationKernel X d U p → formWedge θ η ∈ chartEvaluationKernel X d U (p + q)) ∧
      (η ∈ chartEvaluationKernel X d U q → formWedge θ η ∈ chartEvaluationKernel X d U (p + q))

/-- **Tensoring with a bounded complex preserves quasi-isomorphisms** (sub-rung
`tensor-bounded-quasi-iso`, open). -/
def TensorBoundedQuasiIso : Prop :=
  ∀ (Y : TopCat.{0}) (K L : CochainComplex (ShQ Y) ℤ) (f : K ⟶ L) [QuasiIso f]
    (M : CochainComplex (ShQ Y) ℤ) (a b : ℤ) [M.IsStrictlyGE a] [M.IsStrictlyLE b]
    [HomologicalComplex.HasTensor K M] [HomologicalComplex.HasTensor L M],
    QuasiIso (HomologicalComplex.tensorHom f (𝟙 M))
```

   Reword the module docstring so that the word `sorry` does not occur (for example "stated as `Prop`s below, open").

2. Ledger: keep `cup-hodge-filtration` for (a), add the rest. Exact entries:

```json
{"id": "cup-hodge-reduction", "title": "Products of Hodge classes are Hodge classes once rational classes in F^p and F^q have products in F^{p+q}", "status": "checked", "kind": "foundation", "module": "HodgeLadder.Hodge.CupFiltration", "declarations": ["HodgeLadder.mem_hodgeClasses_iff_mem_hodgeFiltration", "HodgeLadder.cupPreservesHodgeClasses_of_rational", "HodgeLadder.hodgeFiltration_eq_top_of_nonpos", "HodgeLadder.mem_hodgeClasses_zero"], "depends_on": ["cup-product", "chern-classes-are-hodge"], "contributors": [], "note": "The rational part holds by the type of Cup.cup; the conjugate part follows from deRhamConj_fieldToDeRhamCohomology. F^p = ⊤ for p ≤ 0, so Hdg^0 = ⊤ and the unit is a Hodge class. Red team 2026-11-26: docs/sketches/cup-hodge-filtration.redteam.md."}
{"id": "cup-hodge-classes", "title": "Products of Hodge classes are Hodge classes: Hdg^p ∪ Hdg^q ⊆ Hdg^{p+q} for upstream's hodgeClasses and the checked cup", "status": "stated", "kind": "foundation", "module": "HodgeLadder.Hodge.CupFiltration", "declarations": ["HodgeLadder.CupPreservesHodgeClasses", "HodgeLadder.CupRespectsHodgeFiltrationRational"], "depends_on": ["cup-hodge-reduction", "cup-hodge-filtration", "de-rham-cup"], "contributors": [], "note": "Membership statements: insensitive to the order of the factors and to nonzero scalars. Non-vacuity: on ℙ² the line classes are Hodge with nonzero product (Tests.projectivePlane_exists_hodge_cup_ne_zero); the statement then gives [pt] ∈ Hdg^2(ℙ²; ℚ)."}
```

   and replace the entry of `cup-hodge-filtration` by:

```json
{"id": "cup-hodge-filtration", "title": "The de Rham cup product respects the Hodge filtration: deRhamCup (F^p H_dR^a) (F^q H_dR^b) ⊆ F^{p+q} H_dR^{a+b}", "status": "open", "kind": "foundation", "module": null, "declarations": [], "depends_on": ["de-rham-cup", "wedge-sheaf-map"], "contributors": [], "note": "Statement (a) of docs/sketches/cup-hodge-filtration.md, for complex classes, as needed by T1. deRhamCup is a local definition (sub-rung de-rham-cup), pinned by fieldToDeRhamCohomology_cup, ι(α ∪ β) = deRhamCup (ι α) (ι β), exact, no sign (docs/conventions.md, row 'de Rham cup order'). The zero product also satisfies this statement; the pin and the ℙ² test deRhamCup (ι [L₀]) (ι [L₁]) ≠ 0 are what make it about the cup product."}
```

3. Add the test `HodgeLadder.Tests.projectivePlane_exists_hodge_cup_ne_zero` (section 2, exact text) to a test module, named in `cup-hodge-classes`.

4. Add `hodgeFiltration_eq_top_of_nonpos` and `mem_hodgeClasses_zero` (section 3, exact text) to the module. They are checked in scratch.

5. Fix the factor order of `deRhamCup` as in finding 5. Exact signatures for sub-rung `de-rham-cup`:

```lean
/-- The cup product on holomorphic de Rham hypercohomology, in the diagrammatic order of
`HodgeLadder.Cup.cup`: `deRhamCup x y` is `pairProduct (deRhamWedge X) y x`. Convention: row
"de Rham cup order" of `docs/conventions.md`. -/
def deRhamCup {a b : ℤ} (x : H_dR^a(X)) (y : H_dR^b(X)) (n : ℤ) (h : a + b = n) : H_dR^n(X)

theorem fieldToDeRhamCohomology_cup {a b n : ℕ} (h : a + b = n)
    (α : H^a(X; ℚ)) (β : H^b(X; ℚ)) :
    fieldToDeRhamCohomology ℚ X n (Cup.cup α β n h) =
      deRhamCup (fieldToDeRhamCohomology ℚ X a α) (fieldToDeRhamCohomology ℚ X b β) n
        (by omega)

theorem deRhamCup_mem_hodgeFiltration {a b n : ℤ} (h : a + b = n) {p q : ℤ}
    {x : H_dR^a(X)} {y : H_dR^b(X)}
    (hx : x ∈ hodgeFiltration X p a) (hy : y ∈ hodgeFiltration X q b) :
    deRhamCup x y n h ∈ hodgeFiltration X (p + q) n
```

   with `deRhamCup_add_left`, `deRhamCup_add_right`, `deRhamCup_smul_left (c : ℂ)`, `deRhamCup_smul_right (c : ℂ)` for upstream's complex structure on `H_dR^*` (`deRham_complex_smul_eq`).

6. State both sides of `wedge-descends` (finding 8), as in change 1.

For the plan:

7. `derived-tensor-bounded`: replace "`[CommShift ℤ]`" by "`Additive`, via `Localization.functor_additive_iff` on the homotopy category and `mapBifunctorMapHomotopy₁`"; build `T_B` with `Localization.lift`.
8. Reorder the sub-rung table: `rational-hypercohomology-equiv` first; split `wedge-sheaf-map` into three (finding 9).
9. Add sub-rungs `de-rham-injective` (`Function.Injective (fieldToDeRhamCohomology ℚ X n)`) and the test `deRhamCup (ι [L₀]) (ι [L₁]) ≠ 0` on `projectivePlane`, as a dependency of `cup-hodge-filtration`.
10. When T1 gets a ledger id, list `de-rham-rational-span` (`Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤` for projective X) and the antisymmetry of `deRhamCup` on `H^1` among its dependencies (finding 10).

## Not done

`docs/gaps.md` and the ledger are not edited (instructions). The `F^p H^n = 0` for `p > n` sanity lemma was not attempted in Lean; Mathlib's `DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE` is the expected route, subject to the instance spellings of kill risk 4.
