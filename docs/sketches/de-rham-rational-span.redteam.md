# Red team: de-rham-rational-span (statement and route)

Date: 2026-11-27. Branch `track/de-rham-rational-span`, base main `16f29dc`, upstream pin `2ead713`. Under review: `HodgeLadder/Hodge/DeRhamRationalSpan.lean` (two `sorry` bodies) and the section "de-rham-rational-span: statement" of `docs/sketches/cup-hodge-filtration.md`.

**Verdict: pass with changes.** The statement is the surjectivity half of the comparison the literature makes and the one T1's antisymmetry input needs. The route is sound. Sub-rung `betti-additive-naturality` is true and costs about ten edited lines: the port's three files elaborate unchanged with `f : R →+* S` replaced by `f : R →+ S` (finding 4). The module cannot land on main as written, because the checker rejects its two `sorry` bodies (finding 5).

## What was tried

| Attempt | Result |
|---|---|
| Read the module, the sketch section, upstream `Filtration.lean` (lines 60–130, 470–500, 640–720, 815–860) and `Lemmas/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean` (scalar actions) | step 1 pins the ℂ-action exactly; no conjugation (finding 3) |
| Scratch module: the port's `SimplicialCochainCoefficientChange.lean`, `SingularCochainCoefficientChange.lean`, `BettiScalarNaturality.lean` concatenated (809 lines), with `(f : R →+* S)` replaced by `(f : R →+ S)`, `f.toAddMonoidHom` by `f`, and `.toAddMonoidHom` added at the one `Int.castRingHom ℚ` call | elaborates with no error in about 12 s wall; `#print axioms` on the generalized `scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange`: `[propext, Classical.choice, Quot.sound]` |
| Same scratch, plus the module's `Simplicial` and `Singular` sections verbatim, with the sorried `scalarCohomologyEquivOrdinarySingularCohomology_addCoefficientChange` proved by `scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange X g n α` | accepted, standard axioms. The prover's exact sub-rung statement follows from the generalized port theorem by definitional unfolding |
| Scratch importing the built module: `#print axioms` on all nine named declarations; `example : IsIntegral projectivePlane.left ∧ Smooth projectivePlane.hom ∧ IsProjective projectivePlane.hom`; `example : ∃ y : H_dR^((2 * 2 : ℕ))(projectivePlane), y ≠ 0` from `projectivePlane_point_class_ne_zero` and `fieldToDeRhamCohomology_rat_injective`; the sibling statement of finding 1 with `sorry` | all accepted (axiom lines in finding 5) |
| Trivial proof of the rung (unfolding to `True`, a zero module, a degenerate action) | failed: `H_dR^4(ℙ²) ≠ 0` (row above) and the ℂ-action is multiplication on forms (finding 3); the conclusion carries the universal-coefficient content |
| Cheaper route through ring maps and ℚ-linearity (finding 4) | failed; any route needs the comparison to commute with one non-ring additive map |
| `python3 tools/check.py --no-build` in the worktree | `REJECTED (sorry: HodgeLadder/Hodge/DeRhamRationalSpan.lean:149, …:201)`; every other line accepted |

Scratch files were kept in the worktree root and deleted.

## Findings

1. **Is this the literature's statement? Yes, its surjectivity half.** Literature: for a compact space with finitely generated integral homology, `H^n(X; ℚ) ⊗_ℚ ℂ → H^n(X; ℂ)` is an isomorphism (universal coefficients, [Hatcher2002] §3.1, section unverified; the row lists §§3.2–3.3), and `H^n(X; ℂ) ≅ ℍ^n(X^an, Ω•)` by the holomorphic Poincaré lemma ([Voisin2002] vol. I, chapter unverified). Field by field:

   | Field | Literature | Lean |
   |---|---|---|
   | rational cohomology | Betti cohomology of X(ℂ) | upstream `H^n(X; ℚ)`: Mathlib sheaf cohomology of the constant sheaf ℚ on `ComplexPoint X` (analytic topology) |
   | complex cohomology | H^n(X; ℂ), or H^n_dR | upstream `H_dR^n(X)`: hypercohomology of the holomorphic de Rham complex `Ω•(X)` |
   | map | inclusion of constants, no twist | `fieldToDeRhamCohomology ℚ X n`: `algebraMap ℚ ℂ`, then constants into 0-forms; no (2πi)^p, no conjugation (conventions row "Rational-to-de Rham map") |
   | ℂ-structure | the usual one | `deRhamHypercohomologyComplexModule`: c acts by `scalarHolomorphicDeRhamComplexInt X c` (new row "Complex structure on H_dR") |
   | conclusion | `ℂ ⊗ H^n(ℚ) ≅ H^n_dR` | `span ℂ (range ι) = ⊤`, equivalent to surjectivity of `LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)` |

   For T1: antisymmetry of `deRhamCup` on `H^1` (`de-rham-cup-antisymm-h1`) needs only the span. T1's Weil-type argument is a different matter. It splits `H^1_dR` into the eigenspaces V_σ, V_σ̄ of K and uses dim V_σ = 2. That count comes from dim_ℂ H^1_dR = dim_ℚ H^1(X; ℚ), which needs both the span and ℂ-linear independence. `de-rham-injective` (#181) gives injectivity of ι over ℚ only. It does not give independence over ℂ (the map ℚ² → ℂ, (a, b) ↦ a + b√2, is injective with ℂ-span ℂ). Add a sibling rung `de-rham-rational-independent` (open). This statement typechecks against the current module:

   ```lean
   theorem linearIndependent_fieldToDeRhamCohomology_rat (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
       [Smooth X.hom] [IsProjective X.hom] (n : ℕ) {ι : Type} {v : ι → H^n(X; ℚ)}
       (hv : LinearIndependent ℚ v) :
       LinearIndependent ℂ (fieldToDeRhamCohomology ℚ X n ∘ v)
   ```

   (The form `Function.Injective (LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n))` also typechecks.) Proof route, the same machinery: a ℚ-linear functional λ : ℂ → ℚ is an additive map, so the generalized comparison of finding 4 carries a complex relation Σ zᵢ βᵢ = 0, with the zᵢ ℚ-independent, to λ_*(Σ zᵢ βᵢ) = βⱼ = 0. No finiteness of homology is used. `IsProjective` enters only through `T2Space` and `openParacompactSpace`. Whether T1 lists it is the thinker's call when T1 is stated.

2. **Hypotheses.** Satisfiable: ℙ² (`HodgeLadder.Tests.projectivePlane`) carries all three instances; the example is checked. `IsProjective` is the right input at this pin, because it supplies three things the route consumes: `T2Space (ComplexPoint X)` (an instance), `openParacompactSpace X` (upstream takes `[IsProjective X.hom]`) and `module_finite_singularHomology` (compact manifold). The sketch's counterexample (a countable discrete space) is a topological space, not the analytic space of a smooth integral variety, so it does not bear on the rung. The analytic space of a complex algebraic variety has finitely generated integral homology (triangulability of algebraic sets, unverified; no key in `docs/references.md`), so the statement is expected true for smooth separated integral X without projectivity. A later rung can drop `IsProjective` once three inputs exist for that class: Hausdorffness, hereditary paracompactness, and finite generation of `H_n(X(ℂ); ℤ)`. Required: reword the sketch paragraph so it names the counterexample as one to the tensor identity on general spaces and states the expectation above. Recommended: state the assembly with explicit hypotheses `[T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U] [Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ (TopCat.of (ComplexPoint X))).homology n)]`, so that the hook for dropping projectivity is a one-line corollary.

3. **Step 1 is correct and exact.** `deRham_complex_smul_eq` is `rfl`: `c • α = hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c) n α`. The presheaf map is `x ↦ c • x` on forms, and on constants `complexScalarPresheaf` is `DistribSMul.toAddMonoidHom ℂ c`. Conjugation lives separately in `deRhamConj`. `ratScaled z = (AddMonoidHom.mulLeft z).comp (algebraMap ℚ ℂ)` is `q ↦ z * q`. The local `fieldToComplexConstantSheaf_comp_complexScalarSheaf` closes at the presheaf level, so the identity `z • ι' β = e((ratScaled z)_* β)` holds exactly, with no scalar. Upstream's private `complexConstantCohomologyDeRhamAddEquiv_scalar` is reproved through `constantsToHolomorphicDeRhamComplexInt_scalar`, which is public. The reduction `span_range_fieldToDeRhamCohomology_rat_of_mem_closure` proves what its docstring says. It pulls the closure back along `e = hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n`, sends each generator to `z • ι(…)` in the span, and gets `⊤` from surjectivity of `complexConstantCohomologyDeRhamAddEquiv`. Even if the action were conjugated, the span would be the same set, so the rung's truth does not depend on this convention.

4. **Route soundness.**
   - `betti-additive-naturality` is true as stated, and the prover's claim holds: none of the three port files uses `f` multiplicatively. The port's own `dualCoefficientChange` is postcomposition `dualOfFun S X n (f ∘ dualToFun R X n φ)`. The one step that mentions `1` is `openCochainCoefficientChange_constantSingularZeroCochain`, where `f (r * 1) = f r * 1` holds for any function. Measured: replacing the type of `f` makes all 809 lines elaborate in about 12 s, not the 730-line manual copy the sketch estimates. The "main risk" paragraph of the sketch (elaboration cost) is refuted.
   - **Cheaper route (recommended): generalize the port in place.** Edits: `(f : R →+* S)` to `(f : R →+ S)` at `SimplicialCochainCoefficientChange.lean:29`, `SingularCochainCoefficientChange.lean:35,423`, `BettiScalarNaturality.lean:30,65`; `f.toAddMonoidHom` to `f` at `SingularCochainCoefficientChange.lean:105,111`; `(Int.castRingHom ℚ)` to `(Int.castRingHom ℚ).toAddMonoidHom` at `SingularCochainCoefficientChange.lean:454`. The callers (only `SimplicialCochainDenominators.lean` and `IntegralDenominatorClearing.lean`, by grep) pass `(Int.castRingHom ℚ).toAddMonoidHom`. These caller edits are untested here: they need a rebuild of the port. Reword the three module docstrings ("a ring homomorphism" to "an additive map"). Then delete the module's local copies (`dualAddCoefficientChange`, `linearDualAddCoefficientChange`, `ordinarySingularCohomologyAddCoefficientChange`, `constantCoefficientSheafComplexIntAddMap` and their `_ringHom` lemmas) and use the port names with `ratScaled z`. Record the divergence from the upstream source in `docs/port-lefschetz.md`. If the port must stay a snapshot, the fallback is the same sed copy under `namespace HodgeLadder` with renamed declarations, listed in `docs/gaps.md`.
   - Ring maps with ℚ-linearity do not suffice. Every additive map ℚ → ℂ is ℚ-linear, and the comparison `E_ℂ` is automatically ℚ-linear. But `(ratScaled z)_* β = z • (algebraMap)_* β`, and moving `z •` across `E_ℂ` is ℂ-linearity of `E_ℂ`, which is naturality along the additive map `mulLeft z : ℂ → ℂ`. Ring maps ℚ[t] → ℂ, ℂ[ε] → ℂ[ε] or products of rings move the problem without removing it, as the sketch says.
   - `simplicial-complex-span` is true as stated. For a ℚ-vector space A, `H^n(Y; A) ≅ Hom(H_n(Y; ℤ), A)`, because Ext into a divisible group vanishes. So only `H_n` needs to be finitely generated, which matches the hypothesis. The Baer plan checks out degree by degree. `W := span ℚ (range G)` is finite-dimensional because `range G` is a finitely generated group. `ℂ ⧸ W` is a ℚ-vector space, hence divisible, so `Module.Baer.of_divisible` applies. `c' = c − δe` takes values in W on every simplex, since `q(c(σ)) − g(∂σ) = 0`. Coordinates in a ℚ-basis of W commute with the coboundary, which is an alternating sum. In degree 0 every chain is a cycle, so `c' = c`. Finite generation is needed for the sum to be finite.

5. **Axioms and vacuity.** `#print axioms` (scratch, against the built module, olean newer than source): `smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt`, `span_range_fieldToDeRhamCohomology_rat_of_mem_closure`, `fieldToComplexConstantSheafComplexInt_comp_complexScalarComplexInt`, the three `_ringHom` lemmas and `constantCoefficientSheafComplexIntAddMap_algebraMap` use `[propext, Classical.choice, Quot.sound]`. `mem_closure_ratScaled` and `span_range_fieldToDeRhamCohomology_rat` add `sorryAx`. The checker rejects the module (`sorry` at lines 149 and 201), so it cannot merge as is. No hypothesis is unused: `IsProjective` feeds T2, paracompactness and finiteness. The conclusion is not vacuous: `H_dR^4(ℙ²) ≠ 0` is checked above.

6. **Conventions.** Row "Rational-to-de Rham map" (ℚ → ℂ by `algebraMap`, no twist, no conjugation) matches. Two rows were missing and are added to `docs/conventions.md`: "Complex structure on H_dR and on complex constant cohomology" and "Change of coefficients along an additive map". The singular coboundary row (δφ = φ ∘ ∂, no sign) is used by the Baer step. Every additive coordinate map commutes with it, whatever the sign. Truth of the rung is insensitive to all of these: it is a span statement, unchanged by conjugating the action and by nonzero scalars on ι. No cited result is assumed; the port's finiteness and comparison are checked Lean.

7. **Equality first.** The rung is an equality of submodules (`= ⊤`), exact, with no scalar. It is a step toward the identity `ℂ ⊗_ℚ H^n(X; ℚ) ≅ H_dR^n(X)` (bijectivity of `liftBaseChange`). The other half is the new sibling `de-rham-rational-independent` (finding 1); no rung for the full isomorphism exists yet.

7b. **Non-vacuity test.** Smallest existing check: `∃ y : H_dR^4(projectivePlane), y ≠ 0`, from `HodgeLadder.Tests.projectivePlane_point_class_ne_zero` and `HodgeLadder.fieldToDeRhamCohomology_rat_injective` (checked in scratch above, two lines). Sharper test, proposed as optional rung `de-rham-p2-top-rank`: `Module.finrank ℂ H_dR^4(projectivePlane) = 1`. It follows from this rung, `ι [pt] ≠ 0` and the degree isomorphism H⁴(ℙ²; ℚ) ≅ ℚ of `cycle-class-sign-test-p2`, and it fails if the span statement holds for a degenerate reason.

8. **Pin drift.** None. The branch is based on main `16f29dc` at pin `2ead713`, the same pin the upstream definitions were read at (`Filtration.lean`, `HolomorphicDeRham.lean`, `ProjectiveParacompact.lean`).

## Required changes

1. **No `sorry` on main.** Replace the two sorried theorems by `Prop` definitions, or close the first by the port generalization (finding 4) in the same pull request and replace only the second. Exact text for the second:

   ```lean
   /-- **Sub-rung `simplicial-complex-span`** (open). If the integral homology of a simplicial set
   is finitely generated in degree `n`, every degree-`n` complex cohomology class of its
   algebraic-dual cochain complex is a finite sum of classes pushed along `ratScaled z`. -/
   def SimplicialComplexSpan : Prop :=
     ∀ (Y : SSet.{0}) (n : ℕ) [Module.Finite ℤ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).homology n)]
       (α : (((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat).mapHomologicalComplex
         (ComplexShape.up ℕ)).obj
           (Y.chainComplex (ModuleCat.of ℂ ℂ)).linearDualCochainComplex).homology n),
       α ∈ AddSubgroup.closure (⋃ z : ℂ, Set.range
         (HomologicalComplex.homologyMap (linearDualAddCoefficientChange (ratScaled z) Y) n).hom)
   ```

   Give `mem_closure_ratScaled` the hypothesis `(hS : SimplicialComplexSpan)`. State the rung as

   ```lean
   /-- **Rung `de-rham-rational-span`** (stated). -/
   def DeRhamRationalSpan : Prop :=
     ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ),
       Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤

   theorem deRhamRationalSpan_of_simplicialComplexSpan (hS : SimplicialComplexSpan) :
       DeRhamRationalSpan
   ```

   When `simplicial-complex-span` is checked, add `span_range_fieldToDeRhamCohomology_rat` unconditionally and mark the rung `checked`. If the port is generalized, use the port's `SSet.linearDualCoefficientChange (ratScaled z) Y` in place of the local name. Keep the word `sorry` out of the module.

2. **Sketch corrections** (`docs/sketches/cup-hodge-filtration.md`, section "de-rham-rational-span: statement"). (a) The counterexample paragraph, as in finding 2. (b) Replace "Main risk" with the measured result of finding 4 and the in-place generalization. (c) Ledger table: as below.

3. **Ledger entries.**

   | Id | Kind | Status | Depends on | Module | Declarations |
   |---|---|---|---|---|---|
   | `betti-additive-naturality` | foundation | `checked` if the port generalization lands with the PR, else `stated` with a `Prop` | `lefschetz-port` | `LefschetzPort.AlgebraicGeometry.BettiScalarNaturality` | `AlgebraicGeometry.ComplexPoint.scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange` (generalized to `R →+ S`) |
   | `simplicial-complex-span` | foundation | `stated` | none | `HodgeLadder.General.SimplicialCochainSpan` (recommended; or the rung module) | `HodgeLadder.SimplicialComplexSpan` |
   | `de-rham-rational-span` | foundation | `stated` | `betti-additive-naturality`, `simplicial-complex-span` | `HodgeLadder.Hodge.DeRhamRationalSpan` | `HodgeLadder.DeRhamRationalSpan`, `HodgeLadder.deRhamRationalSpan_of_simplicialComplexSpan`, `HodgeLadder.span_range_fieldToDeRhamCohomology_rat_of_mem_closure`, `HodgeLadder.smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt` |
   | `de-rham-rational-independent` | foundation | `open` | `betti-additive-naturality` | none | none; statement in finding 1 |
   | `de-rham-p2-top-rank` (optional) | test | `open` | `de-rham-rational-span`, `cycle-class-sign-test-p2`, `de-rham-injective` | none | none; `Module.finrank ℂ H_dR^4(projectivePlane) = 1` |

   The ledger currently gives `de-rham-rational-span` the path `HodgeLadder/De/Rham/Rational/Span.lean`; set the module to `HodgeLadder.Hodge.DeRhamRationalSpan`. Note on `de-rham-rational-span`: "Span statement: insensitive to the ℂ-action's conjugation and to nonzero scalars on ι. Red team 2026-11-27: docs/sketches/de-rham-rational-span.redteam.md."

4. **General lemmas kept local** (decision 0011). Put `ratScaled` and `SimplicialComplexSpan` (later the theorem) in `HodgeLadder/General/SimplicialCochainSpan.lean` and add a row in `docs/gaps.md` "General lemmas kept local". Also add a row for the port generalization (or the renamed copy), so a pin bump can check it against any upstream additive version.

Recommended, not required: state the assembly with explicit Hausdorff, paracompactness and finiteness hypotheses (finding 2). Use the `Prop`-and-conditional pattern for `de-rham-rational-independent` too.
