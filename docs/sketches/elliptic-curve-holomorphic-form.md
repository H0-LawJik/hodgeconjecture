# Sketch: `elliptic-curve-holomorphic-form`

Rung D5 of `docs/notes/2026-11-27-t1-plan.md` (issue #283). Thinker session 1. Pin: upstream `2ead713`, Lean and Mathlib `v4.35.0-rc4`, `main` at `33ef5c1`. Every Lean block below elaborated with `sorry` proofs in a scratch file importing `HodgeLadder.Tests.EllipticCurveWitness`, `HodgeLadder.Tests.EllipticCurvePoints`, `HodgeLadder.Hodge.FirstFiltration` and `LefschetzPort.AlgebraicGeometry.RegularFunctionsHolomorphic` (deleted afterwards). This is a plan, not a proof.

## Statement

**Plain words.** The first Hodge filtration of H¹_dR of the plane cubic E : y²z = x³ − xz² is nonzero. Pinned form: the global holomorphic 1-form ω = dx/y on E(ℂ) has a nonzero class in H¹_dR(E), and that class lies in F¹.

**What F¹H¹_dR is at the pin.** Upstream `hodgeFiltrationComplexSubmodule X 1 1` (notation `F^1 H_dR^1(X)`) is the range of `filteredToDeRhamCohomology X 1 1 : ℍ^1(X; F^1 Ω•(X)) →+ H_dR^1(X)`, where `hodgeFilteredDeRhamComplex X 1 = Ω•(X).stupidTrunc (embeddingUpIntGE 1)` and `ℍ^n(X; K)` is `SmallShiftedHom` from ℤ[0] to K in degree n (sheaves of abelian groups on X(ℂ)). The ladder's `mem_hodgeFiltration_one_iff` (`HodgeLadder/Hodge/FirstFiltration.lean`) adds: F¹ = ker(`deRhamToHolomorphicFunctionCohomology X n`). On a curve Ω^p = 0 for p ≥ 2 (upstream `holomorphicDeRhamSheaf_isZero_of_lt`), so F¹Ω• is Ω¹ in degree 1 and ℍ¹(F¹Ω•) should be Γ(Ω¹); this matches the literature's F¹H¹ = H⁰(Ω¹) for a compact curve ([Voisin2002], locator unverified).

**Upstream's Ω¹ differs from the literature's in one way that matters here.** `holomorphicDeRhamSheaf X d 1` is the sheafification of U ↦ `HolomorphicForm X d U 1` = Kähler 1-forms of 𝒪(U) modulo `chartEvaluationKernel`. On compact E the presheaf value at ⊤ is Kähler forms of the locally constant functions, expected to be zero; a global ω must be glued in the sheafification from local sections. Stalks agree with the literature's (upstream's own comparison, via `stalkFunctor_map_unit_toSheafify_isIso`).

```lean
theorem ellipticCurve_hodgeFiltration_one_ne_bot : F^1 H_dR^1(Tests.ellipticCurve) ≠ ⊥
theorem ellipticOmegaClass_ne_zero :
    filteredToDeRhamCohomology Tests.ellipticCurve 1 1
      (curveOneFormClass Tests.ellipticCurve Tests.dim_ellipticCurve ellipticOmega) ≠ 0
```

Membership of that class in `F^1 H_dR^1(Tests.ellipticCurve)` is `⟨_, rfl⟩` (elaborated). `curveOneFormClass` and `ellipticOmega` are new (sub-rungs S3, S5).

## Why the ladder needs it

D6 `elliptic-curve-h1-eigen` needs a nonzero `ellipticI`-stable F¹H¹(E) to find an eigenvector; F1 `weil-elliptic-square` then gets balance for f = [i] × [i]³ from pr₁^*ω and pr₂^*ω. Without D5 the Hodge route of the E × E instance stops (kill criterion, plan §7).

## Proof idea (route (a), recommended)

1. **Global holomorphic functions are locally constant.** E(ℂ) is compact (upstream instance `IsProjective.complexPoint_compactSpace`) and a complex manifold (upstream `isManifold_omega`); Mathlib's `MDifferentiable.isLocallyConstant` applies to any f ∈ 𝒪(⊤).
2. **δ = 0 in the long exact sequence.** For the triangle of `firstFiltrationShortComplex_shortExact` (0 → F¹Ω• → Ω• → 𝒪[0] → 0), exactness at ℍ¹(F¹) (`Functor.homologySequence_exact₁`) gives ker(ℍ¹(F¹) → H¹_dR) = im δ, and δ vanishes on the image of ℍ⁰(Ω•) → ℍ⁰(𝒪[0]) (`homologySequence_exact₃`). That map is onto: α ∈ ℍ⁰(𝒪[0]) is `mk₀` of a sheaf map ℤ_X → 𝒪 (`DerivedCategory.singleFunctor` is full), i.e. a global f (`constantSheafAdj`); f is locally constant (step 1), so it comes from ℂ_X (`constantSheafIsoLocallyConstantSheaf`), and ℂ_X → Ω• → 𝒪[0] is the inclusion of constants (port `constantsToHolomorphicDeRhamComplex_comp_toFunctions`). So `filteredToDeRhamCohomology X 1 1` is injective.
3. **Γ(Ω¹) ↪ ℍ¹(F¹Ω•) on a curve.** With dim X = 1, F¹Ω• ≅ (single 1).obj Ω¹ (all other terms zero), so ℍ¹(F¹Ω•) ≅ Hom_D(ℤ[0], Ω¹[0]) ≅ Hom(ℤ_X, Ω¹) ≅ Γ(Ω¹), the last two by full faithfulness of `singleFunctor` and `constantSheafAdj` (pattern: `HodgeLadder/Cup/RightMultClass.lean`).
4. **Coordinates as holomorphic functions.** x, y ∈ 𝒪(chart z ≠ 0) and u, w ∈ 𝒪(chart y ≠ 0) from port `regularFunctionsToHolomorphic` on `chartOpenScheme 2`, `chartOpenScheme 1`, evaluated through `ellipticAffineHomeomorph`, `ellipticInfinityHomeomorph`; y² = x³ − x and w = u³ − uw² hold in 𝒪 (ring hom of the chart relation); on the overlap u = x·y⁻¹, w = y⁻¹ (from `affinePoint_eq_infinityPoint`, pointwise, as 𝒪 is functions).
5. **Glue ω.** Opens V₁ = {z ≠ 0, y ≠ 0}, V₂ = {z ≠ 0, 3x² − 1 ≠ 0}, V₃ = {y ≠ 0, 1 + 2uw ≠ 0} cover E(ℂ) ([0 : 1 : 0] has u = w = 0, so lies in V₃; V₂ ∩ V₃ ⊆ V₁). Sections y⁻¹ dx, 2(3x² − 1)⁻¹ dy, −2(1 + 2uw)⁻¹ du (`Algebra.DeRham.mk ℂ _ 1 a ![v]`). Agreement holds already in Kähler forms of 𝒪(V ∩ V′), before the quotient: d(y² − x³ + x) = 0 gives 2y dy = (3x² − 1) dx; from u = x/y, w = 1/y one gets du = −x(x² + 1) y⁻³ dx and 1 + 2uw = (x³ + x) y⁻², so −2(1 + 2uw)⁻¹ du = y⁻¹ dx (hand computation, agrees with red team `elliptic-curve-points` finding 11: dx/y = −2 du at O). Glue by `TopCat.Sheaf.existsUnique_gluing` after `toSheafify`.
6. **ω ≠ 0.** By `stalkFunctor_map_unit_toSheafify_isIso` it suffices that the presheaf germ of y⁻¹ dx at some p ∈ V₁ is nonzero (`TopCat.Presheaf.germ_eq`), i.e. on every open W ∋ p the form is outside `chartEvaluationKernel`. Upstream's chart evaluation of a dx is a·D(x ∘ e⁻¹). If D(x ∘ e⁻¹) vanished on a ball in the chart (ℂ^1, as `dim_ellipticCurve`), x would be constant on an infinite open set; but each fibre of x on y² = x³ − x has at most two points and the chart homeomorphism is injective. The ladder's `DeRhamUnitNonzero` uses the same stalk pattern in degree 0.
7. **Assemble.** Steps 2, 3: on a compact curve, s ≠ 0 in Γ(Ω¹) gives a nonzero class in F¹H¹_dR. Apply to ω.

No uniformization, no b₁, no GAGA. The only analysis is Mathlib's maximum modulus on compact manifolds and a mean-value step in one chart.

## Route (b), compared

F¹ ≠ ⊥ iff H¹_dR → ℍ¹(𝒪[0]) has a kernel, which follows from dim H¹_dR = 2 > dim H¹(𝒪). Inputs: (i) finrank H¹(E; ℚ) = 2, through C2, C3, C6, C7 (two large rungs with kill criteria) and `finrank_deRham_eq_finrank_rat`; (ii) dim ℍ¹(E(ℂ); 𝒪[0]) ≤ 1 as a ℂ-space, with a ℂ-linear projection; (iii) for (ii): the port's `ComplexAnalytic.gaga₁` lives on Oka's X^an with `SheafOfModules` cohomology, and no bridge to upstream's `ComplexPoint` sheaf 𝒪 in `AnalyticAdditiveSheaf` was found; algebraic H¹ of an affine scheme vanishing for quasi-coherent sheaves was not found under `Mathlib/AlgebraicGeometry` by grep. The Čech part is easy: with A = ℂ[x, y]/(y² − x³ + x), B = ℂ[u, w]/(w − u³ + uw²), u = x/y, w = 1/y, the monomials x^i y^k (i ∈ {0, 1, 2}, k ∈ ℤ) form a basis of A[1/y] (their orders −2i − 3k at O are distinct); A spans k ≥ 0, B spans k ≤ −i, so A[1/y]/(A + B) = ℂ·[x²/y], dimension 1. Route (b) costs everything route (a) avoids; record it, do not dispatch it.

**Route (c).** Route (a) is the uniformization-free route. A period route (∫ω over a loop ≠ 0) needs integration of upstream forms against chains, absent at the pin.

## What Mathlib has

`MDifferentiable.isLocallyConstant` (`Mathlib/Geometry/Manifold/Complex.lean`); `DerivedCategory.triangleOfSES`, `triangleOfSES_distinguished`; `Functor.homologySequence_exact₁`, `homologySequence_exact₃`, `homologySequenceδ_comp`; `singleFunctor` `Full`/`Faithful` instances (`DerivedCategory/FullyFaithful.lean`); `constantSheafAdj`; `TopCat.Sheaf.existsUnique_gluing`; `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, `TopCat.Presheaf.germ_eq`. Upstream: `hodgeFiltrationComplexSubmodule`, `filteredToDeRhamCohomology`, `HolomorphicForm`, `chartEvaluationKernel`, `mem_chartEvaluationKernel_iff`, `holomorphicDeRhamSheaf`, `holomorphicDeRhamSheaf_isZero_of_lt`, `Algebra.DeRham.mk`, `IsProjective.complexPoint_compactSpace`, `isManifold_omega`. Port: `regularFunctionsToHolomorphic`, `holomorphicDeRhamToFunctionsComplexInt`, `deRhamToHolomorphicFunctionCohomology`, `constantsToHolomorphicDeRhamComplex_comp_toFunctions`. Ladder: `firstFiltrationShortComplex_shortExact`, `mem_hodgeFiltration_one_iff`, `constantSheafIsoLocallyConstantSheaf`, `Tests.ellipticAffineHomeomorph`, `Tests.ellipticInfinityHomeomorph`, `Tests.dim_ellipticCurve`.

## What is missing

The δ = 0 argument (steps 1, 2), the curve identification ℍ¹(F¹Ω•) ≅ Γ(Ω¹) (step 3), the coordinate functions (step 4), ω and its nonvanishing (steps 5, 6).

## Sub-rungs

| Id | Statement (elaborated) | Size | depends_on |
|---|---|---|---|
| S1 `compact-holomorphic-locally-constant` | `IsLocallyConstant` of every `f : C^ω⟮𝓘(ℂ, Fin (dim X.left) → ℂ), (⊤ : Opens (ComplexPoint X)); ℂ⟯` under `[CompactSpace (ComplexPoint X)]` | small | none (upstream, Mathlib) |
| S2a `de-rham-functions-surjective-zero` | `Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0)` under `[CompactSpace (ComplexPoint X)]` | medium | S1, `chern-classes-are-hodge` |
| S2b `filtered-one-injective` | `(Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0)) → Function.Injective (filteredToDeRhamCohomology X 1 1)` | small | `chern-classes-are-hodge` |
| S3 `curve-one-form-class` | `curveOneFormClass X (hX : dim X.left = 1) : (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.obj (op ⊤) →+ FilteredDeRhamHypercohomology X 1 1`, `curveOneFormClass_injective` | medium | none |
| S4 `elliptic-coordinate-functions` | `ellipticX ellipticY : C^ω⟮…, Tests.ellipticAffineOpen; ℂ⟯`, `ellipticU ellipticW` on `Tests.ellipticInfinityOpen`, `ellipticX_apply`, `ellipticY_apply`, `ellipticU_apply`, `ellipticY_sq : ellipticY ^ 2 = ellipticX ^ 3 - ellipticX`, `ellipticW_eq`, overlap identities | medium | `elliptic-curve-points`, `lefschetz-port` |
| S5 `elliptic-omega` | `ellipticOmega : (holomorphicDeRhamSheaf Tests.ellipticCurve (dim _) 1).presheaf.obj (op ⊤)`, `ellipticOmega_res` (restriction to V₁ is `toSheafify` of `mk ℂ _ 1 y⁻¹ ![x]`), `ellipticOmega_ne_zero` | medium to large; split into gluing and nonvanishing if released once | S4, `elliptic-curve-witness` |
| S6 `curve-hodge-filtration-section` | `hodgeFiltration_one_one_ne_bot_of_section X [CompactSpace _] (hX : dim X.left = 1) s (hs : s ≠ 0) : F^1 H_dR^1(X) ≠ ⊥`, with the pinned nonzero class | small | S2a, S2b, S3 |
| D5 (this rung) | the two theorems of the Statement | small | S5, S6, `elliptic-curve-witness` |

S1, S2a, S2b, S3, S6 hold for any compact smooth curve; they go to `docs/gaps.md` "General lemmas kept local" if they land in `HodgeLadder/General/`.

**First dispatch:** S4 (ready; it is the first test that upstream's 𝒪 carries the chart coordinates), with S1 and S2b in parallel. S3 is the bookkeeping long pole (stupid truncation, shift of `single`); give it to a prover only after S2b lands, since both work in the same triangle.

## Signs and normalizations

| Item | Value | Load-bearing |
|---|---|---|
| D5 itself | no sign, no scalar: a nonvanishing claim | no |
| ω on the charts | y⁻¹ dx = 2(3x² − 1)⁻¹ dy; at O, −2(1 + 2uw)⁻¹ du, value −2 du | the scalar is irrelevant to F¹ ≠ ⊥; it pins `ellipticOmega_res` |
| [i]^*ω for `ellipticI` = [−x : iy : z] | d(−x)/(iy) = i·dx/y, eigenvalue +i; [i]³ gives −i | D6 and F1 use only ±i (plan §3); the value +i holds for the pullback of forms, and equals the eigenvalue of `deRhamPullback` only after D3 |
| δ in the long exact sequence | sign irrelevant: only δ = 0 is used | no |
| `dim Tests.ellipticCurve.left` | equals 1 propositionally (`Tests.dim_ellipticCurve`); charts land in `Fin (dim _) → ℂ` | S3, S6 must take `hX : dim X.left = 1`, not a cast |

Proposed conventions row "Holomorphic form on E": ω = dx/y, [i]^*ω = iω.

## Kill criteria and fallback

This sketch states route (a) on upstream definitions; session count for the rung's criterion: 1. Per sub-rung: S3 released twice, or S5's nonvanishing released twice, without a stated replacement, ends route (a); route (b) stays recorded and is not a fallback (it needs C2, C3, C6, C7 and a GAGA bridge). Then the Hodge route of the E × E instance is dead and the divisor route of plan §3 (graph classes and intersection numbers on E × E, no rung yet) is the fallback.

## Sources

[Voisin2002] (F¹H¹ = H⁰(Ω¹) for compact curves; holomorphic functions on compact connected manifolds constant; locators unverified). [Silverman2009] (dx/y on a Weierstrass cubic is holomorphic and nowhere vanishing, ch. III; dim H¹(E, 𝒪) = 1 by Riemann–Roch, ch. II; locators unverified). [Serre1956] (GAGA, route (b)). [GriffithsHarris1978] (maximum principle, Čech H¹(𝒪); unverified locator). The Kähler identities of step 5 and the Čech basis of route (b) are hand computations here, unverified in Lean.
