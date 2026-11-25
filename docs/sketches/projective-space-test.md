# Sketch: `projective-space-test`

Rung: Hdg^1(ℙ^n; ℚ) = algebraicCycleClassSpan ℙ^n 1, both one-dimensional (n ≥ 1). Purpose: red-team finding I1 on `lefschetz-port` (`docs/sketches/lefschetz-port.redteam.md`): the checked `HodgeLadder.lefschetzOneOne_holds` has no degree-two non-vacuity test. The essential content is a nonzero cycle class in degree two on some smooth projective integral X; the dimension counts and the Hodge side come after it.

Inventory taken 2026-11-25 at the upstream pin `2ead713`. Verdict: multi-session. The rung is split into seven sub-rungs on ℙ¹, one of which is checked in this session (`forget-support-exact`). The proposed statements below elaborate at the pin with `sorry` bodies (checked in a scratch file, not committed).

## Inventory

### (i) ℙ¹ as `X : Over (Spec ↧ℂ)` with the three instances

| Need | At the pin | Missing |
|---|---|---|
| The object | upstream `ProjectiveSpace (Fin 2) (Spec ↧ℂ)`, a pullback of `Proj ℤ[x₀, x₁]` (coefficients `ULift ℤ`) over the terminal scheme; `toBase` | nothing |
| `IsProjective` | upstream `Presentation`; the identity is a closed immersion over the base | nothing (a few lines) |
| `Smooth`, `SmoothOfRelativeDimension 1` | Mathlib: `HasRingHomProperty @Smooth`, stable under base change and local on the source; staged Oka: `ℙₒ(n; R) = Proj R[X₀..Xₙ]`, `chart i : Spec R[Y] ⟶ ℙₒ(n; R)` open immersions with `⋃ U i = ⊤`, `UIIsoSpec`; Oka `ProjectiveSpace.isPullback_map` and `baseChangeIso` (`ℙₒ(n; A) = ℙₒ(n; R) ×_{Spec R} Spec A`) | Mathlib has no smoothness of `Proj`; the chart argument must be written. Identify upstream's ℙ(Fin 2; Spec ℂ) with `ℙₒ(1; ℂ)`: the Proj is the same (`ℙₒ(1; ULift ℤ)`), and `Spec (ULift ℤ)` is terminal (`specULiftZIsTerminal`) |
| `IsIntegral` | Mathlib: integral = irreducible + reduced | no integrality of `Proj` anywhere at the pin; reduced is local (charts are `Spec ℂ[t]`), irreducible from two irreducible opens that meet |

Estimate: one session. Rung `projective-line-witness`.

### (ii) The class of a point is nonzero in H²(ℙ¹; ℚ)

The cycle class is `forgetSupport` of the supported class (`cycleComponentSheafClass_eq_forgetSupport`). Upstream proves the supported class nonzero for every component (`cycleComponentSmoothSupportCoclassSection_ne_zero`, carried across by the normalization isomorphism, exactly as in the codimension-zero proof `cycleComponentSheafClass_genericPoint_eq_zero_iff`). Upstream proves `forgetSupport` injective only when Z is everything (`forgetSupport_injective_of_eq_top`).

For a point x on ℙ¹ the long exact sequence of the pair (X(ℂ), U), U = X(ℂ) ∖ {x},

H^1(U; ℚ) → H_[x]^2(X; ℚ) → H^2(X; ℚ) → H^2(U; ℚ),

makes `forgetSupport` injective once H^1(U; ℚ) = 0, and U ≅ ℂ.

| Step | At the pin | Missing |
|---|---|---|
| (a) a point x with `coheight x = 1` | `SmoothOfRelativeDimension.coheight_ne_of_lt` (coheight ≤ 1); generic point specializes to x (≥ 1); `cycleComponentSupport_eq_singleton_of_coheight_eq_dimension` | assembling it on ℙ¹ |
| (b) U = X(ℂ) ∖ {x} is homeomorphic to ℂ | upstream `openHomeomorph` (complex points of an open subscheme), `affineSpaceHomeomorph`, `affineSpecHomeomorph`; Oka `UIIsoSpec` | the scheme fact X ∖ D₊(x₀) = {x} for x = [0 : 1]; transport through the chart |
| (c) the pair sequence | upstream `Sheaf.relH`, `Sheaf.pairShortComplex_shortExact`; Mathlib `Ext.contravariant_sequence_exact₂/₃` | **checked this session**: `forget-support-exact` |
| (d) H'^q(U; ℚ_X) = 0 for q > 0 | Oka `TopCat.Sheaf.H'AddEquiv` (`H'^q(U, F) ≃ H^q(F|_U)`); upstream `constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis`, `contractibleOpenBasis_of_isOpenEmbedding`, `singularCochainComplex_exactAt_of_contractible`, `rationalCohomologyAddEquivSingularCohomology` (for complex points of smooth integral X; hypotheses T2 and paracompact opens) | restriction of the constant sheaf to U; a constant-sheaf/singular comparison on the open U (directly, or by applying the scheme-level comparison to `openScheme X U` through `openHomeomorph`, which needs integral and smooth instances on the open subscheme and transport of sheaf cohomology along a homeomorphism). Mathlib's `Sheaf.H'` docstring lists `H'(U) ≃ H(F.over U)` as a TODO; Oka supplies it for topological spaces |
| (e) assembly | the codimension-zero pattern | about a page |

Estimates: (a)+(b) one session (`projective-line-point`); (d) one to two sessions (`contractible-open-acyclic`, the hardest); (e) short (`projective-line-class-nonzero`).

A singular-cohomology route was considered and set aside: upstream's comparison of sheaf cohomology with support against relative singular cohomology is unfinished at the pin ("does not yet identify its global-section mapping cone with relative singular cohomology", `Other/AlgebraicGeometry/Cohomology/SupportSingularNaturality.lean`), and the cone model of the cycle class is not yet identified with `cycleComponentSheafClass` (`coneCycleComponentSheafClass` docstring). The sheaf-side pair sequence avoids both.

A general top-degree argument (the class of a point of any X is nonzero in H^{2d}) needs a fundamental class of a compact oriented manifold; upstream's Borel–Moore material constructs the point coclass and its supported class, and stops short of the ordinary class being nonzero. Set aside.

### (iii) dim H²(ℙ¹; ℚ) = 1, and the Hodge side

| Step | At the pin | Missing |
|---|---|---|
| H²(X) ≅ H_[x]²(X) | `forget-support-exact` with H'^1(U) = H'^2(U) = 0 | (d) |
| H_[x]²(X; ℚ) is one-dimensional | singular side: `span_analyticPointLocalCoclass_eq_top`; sheaf side: point normalization `cycleComponentSupportedInjectiveClass_point_normalization`, the normalization isomorphism onto sections of the local cohomology sheaf | the sheaf-side dimension count at a point |
| Hdg^1 ≤ span | `HodgeLadder.lefschetzOneOne_holds` | nothing |
| span ≤ Hdg^1 | `HodgeLadder.integralToRational_mem_hodgeClasses_iff` (rational image of α ∈ H²(X; ℤ) is Hodge iff α ↦ 0 in H²(𝒪)); `sheafCycleClassOnCycles_divisor_mem_hodgeClasses` (Cartier route) | either H²(ℙ¹(ℂ), 𝒪) = 0 plus the point class as the rational image of an integral class, or a unit extension for 𝒪(1) (part (b) of `prime-divisors-cartier`) with the divisor of x₀ equal to the point with multiplicity one |

General ℙⁿ, n ≥ 2, needs H² of ℙⁿ(ℂ) (Mayer–Vietoris on the standard cover or a cell argument) and a hyperplane in place of a point; it is out of scope until ℙ¹ is done. The rung `projective-space-test` keeps its ℙⁿ statement; the ℙ¹ case is the separate rung `projective-line-test` (a weaker statement gets its own rung).

## Sub-rungs

All statements on upstream definitions, in namespace `HodgeLadder.Tests`, with

```lean
/-- ℙ¹ over ℂ in upstream's sense. -/
noncomputable abbrev projectiveLine : Over (Spec ↧ℂ) :=
  Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
```

| Id | Kind | Depends on | Lean statement |
|---|---|---|---|
| `projective-line-witness` | test | `upstream-statement` | `instance : IsIntegral projectiveLine.left`, `instance : SmoothOfRelativeDimension 1 projectiveLine.hom`, `instance : Smooth projectiveLine.hom`, `instance : IsProjective projectiveLine.hom` |
| `projective-line-point` | test | `projective-line-witness` | `∃ (x : projectiveLine.left) (_ : coheight x = 1), ContractibleSpace ↥((cycleComponentSupport projectiveLine x)ᶜ)` |
| `forget-support-exact` | foundation | `upstream-statement` | **checked**: `forgetSupport_injective_of_subsingleton`, `forgetSupport_surjective_of_subsingleton` (below) |
| `contractible-open-acyclic` | foundation | `upstream-statement` | `∀ X [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (U : Opens (ComplexPoint X)) [ContractibleSpace U] (q : ℕ), 0 < q → Subsingleton (Sheaf.H' ℚ_X q U)` |
| `projective-line-class-nonzero` | test | `projective-line-point`, `forget-support-exact`, `contractible-open-acyclic` | `∃ (x : projectiveLine.left) (hx : coheight x = 1), cycleComponentSheafClass projectiveLine x hx ≠ 0` and `algebraicCycleClassSpan projectiveLine 1 ≠ ⊥` |
| `projective-line-h2` | test | `projective-line-class-nonzero` | `Module.finrank ℚ (H^(2 * 1)(projectiveLine; ℚ)) = 1` and `algebraicCycleClassSpan projectiveLine 1 = ⊤` |
| `projective-line-test` | test | `projective-line-h2`, `lefschetz-1-1`, `chern-classes-are-hodge` | `Hdg^1(projectiveLine; ℚ) = algebraicCycleClassSpan projectiveLine 1` and `Module.finrank ℚ (Hdg^1(projectiveLine; ℚ)) = 1` |

Here `ℚ_X` is `(TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)`, the coefficient sheaf of upstream's `H^n(X; ℚ)` and `H_[Z]^n(X; ℚ)`.

`projective-line-witness` and `contractible-open-acyclic` are independent and can run in parallel.

## Checked this session

`HodgeLadder.Tests.ForgetSupport` (rung `forget-support-exact`), for any `X : Over (Spec ↧ℂ)` and `Z : Closeds (ComplexPoint X)`:

```lean
theorem forgetSupport_injective_of_subsingleton (n : ℕ)
    (h : Subsingleton (Sheaf.H' ℚ_X n Z.compl)) :
    Function.Injective (forgetSupport ℚ X Z (n + 1))

theorem forgetSupport_surjective_of_subsingleton (n : ℕ)
    (h : Subsingleton (Sheaf.H' ℚ_X n Z.compl)) :
    Function.Surjective (forgetSupport ℚ X Z n)
```

Proof: upstream's `forgetSupport` is `H'.addEquivTerminal` composed with `relH.forget`, which is precomposition with the cokernel map of the pair short exact sequence `ℤ[U] → ℤ[X] → ℤ[X, U]`; Mathlib's `Ext.contravariant_sequence_exact₃` and `₂` give the two exactness statements. Axioms: the standard three.

## Red-team notes for the sub-rungs

- Vacuity: `projective-line-class-nonzero` is the test that answers I1; the witness instances must be on upstream's `ProjectiveSpace`, so the test is about the same `X` the upstream statements quantify over. A witness built on `ℙₒ` alone would need the identification with upstream's object as part of the rung.
- Sign: nonvanishing and dimension counts are sign-free. The identity Hdg^1 = span is sign-free as well (both are subspaces). The sign of the point class against c₁(𝒪(1)) enters only through the Cartier route of `projective-line-test`; `divisor-chern-exact` fixes it as `+`.
- Drift: the proof of `forget-support-exact` unfolds upstream's `forgetSupport` to `relH.forget`; a change of that definition upstream breaks the build here, which is the intended signal.

## Progress (2026-11-25)

All seven ℙ¹ sub-rungs are checked (standard axioms). Two results hold beyond ℙ¹: `cycleComponentSheafClass_ne_zero_of_subsingleton` (any smooth projective X, codimension one) and `finrank_H2_of_subsingleton` (curves). The step (iii) dimension count used upstream's identification of the supported group with relative singular cohomology and the point coclass spanning it, so no sheaf-side count was needed. The span inclusion on the Hodge side came from `lefschetz-1-1-equality`. `projective-space-test` (ℙⁿ, n ≥ 2) stays open.
