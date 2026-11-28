# Red team: `elliptic-square-witness` (test, issue #274, T1 node E7)

Date: 2026-11-28. Worktree `elliptic-square-witness`, branch `track/elliptic-square-witness`, candidate commit `25b5025` on base `1ab3252` (`main` is now at `ab87174`). Upstream pin `2ead713`, unchanged on the branch and on `main`. Files: `HodgeLadder/Elliptic/Square/Witness.lean` (436 lines, namespace `HodgeLadder.Tests`) and `HodgeLadder/General/GeometricallyIntegralCover.lean` (149 lines, namespace `HodgeLadder.GeometricallyIntegralCover`).

**Verdict: pass with changes.** The mathematics is right. `GeometricallyIntegral ellipticCurve.hom` comes from a correct two-chart criterion fed by chart rings that stay domains over every field over ℂ; `E × E` is integral, smooth of relative dimension 2, projective, with dimension 2, by instances that are real theorems; every declaration builds with the three standard axioms. The Weil endomorphism `prod.map ellipticI (ellipticI ≫ ellipticI ≫ ellipticI)` is the signature-(1, 1) choice that `weil-elliptic-square` needs, and `prod.map ellipticI ellipticI` would be the signature-(2, 0) choice on which that rung is false. The changes: remove the General-on-Tests import, move the witness file to `HodgeLadder/Tests/`, add a test that separates the endomorphism from `[i] × [i]` and two `rfl` pins against the ℂ equations, correct two docstrings that claim no convention matters, and add the ledger entry, two gaps rows and one conventions row.

Read: ledger entries `elliptic-square-witness`, `elliptic-curve-witness`, `elliptic-curve-integral`, `elliptic-curve-cm`, `p1p1-witness`, `complex-points-prod`, `weil-elliptic-square`, `weil-elliptic-square-grpobj`; `python3 tools/next.py elliptic-square-witness`; `docs/notes/2026-11-27-t1-plan.md` nodes E7, D6, F1, F2 and the proposed unbalanced test; `HodgeLadder/Weil/Surface/Statement.lean` and `docs/sketches/weil-surface-statement.redteam.md` at `main`; `HodgeLadder/Weil/Space.lean`; `HodgeLadder/Tests/{EllipticCurveIntegral,EllipticCurveCM,ProjectivePlane,ProjectiveLine}.lean`; Mathlib `AlgebraicGeometry/Geometrically/{Basic,Integral,Irreducible}.lean`, `CategoryTheory/Monoidal/Grp.lean`, `AlgebraicGeometry/Group/Abelian.lean`; upstream `Definitions/Topology/Dimension/Basic.lean`, `Definitions/AlgebraicGeometry/Hodge/Filtration.lean`; `docs/conventions.md` rows "Plane cubic E and its charts", "Complex multiplication on E", "Weil space"; `docs/gaps.md`; `docs/sketches/{p1p1-witness,elliptic-curve-integral,segre-general}.redteam.md`.

Scratch: `scratch-rt-esw/Probe*.lean` and `CoverNoTests*.lean` under the worktree, compiled with `lake env lean`, deleted at the end.

## 1. The statement against the literature

E7 asks for an object, so the comparison is with the plan and with the consumers.

| Field | Plan E7 / consumer | Lean | Match |
|---|---|---|---|
| surface | `ellipticSquare := ellipticCurve ⨯ ellipticCurve` | `abbrev ellipticSquare : Over (Spec ↧ℂ) := ellipticCurve ⨯ ellipticCurve` | yes; `Limits.prod`, the spelling of `complex-points-prod` |
| hypotheses of the statements of record | `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]` | `#synth` finds `isIntegral_ellipticSquare`, `ComplexPointProd.smooth_prod`, `Segre.General.isProjective_prod` | yes |
| relative dimension | 2, as `1 + 1` | `inferInstanceAs (SmoothOfRelativeDimension (1 + 1) _)` | yes |
| dimension | `dim = 2` | `TopologicalSpace.dim ellipticSquare.left = 2` from upstream's `SmoothOfRelativeDimension.dim_eq` | yes; the value is 2, so the `toNat` default 0 of upstream's `dim` plays no part |
| endomorphism | `prod.map ellipticI (ellipticI ≫ ellipticI ≫ ellipticI)` | same, `ellipticWeilEndo` | yes |
| F1 needs | `weilSpace ellipticSquare ellipticWeilEndo 1`, `Cup.pullbackCoh ellipticWeilEndo 1`, `deRhamPullback ellipticWeilEndo 1`, `F^1 H_dR^1(ellipticSquare)` | all four elaborate against the candidate (scratch `Probe.lean`, `Probe4.lean`), including the balance intersection of `isWeilTypeSurface_iff` at `d = 1` | yes |

**Signature (the question asked first).** The choice is right. On E : y² = x³ − x, `ellipticI` is (x, y) ↦ (−x, iy) (conventions row "Complex multiplication on E"), so [i]^*(dx/y) = −dx/(iy) = i · dx/y, and ([i]³)^* = ([i]^*)³ acts on dx/y by i³ = −i. With H^{1,0}(E × E) = pr₁^*H^{1,0}(E) ⊕ pr₂^*H^{1,0}(E) (Künneth, planned in `elliptic-square-cohomology`), the Weil endomorphism has one line of H^{1,0} in each eigenspace V₊, V₋: signature (1, 1), so the balance condition of `IsWeilTypeSurface` holds at `d = 1`. The weight-2 check agrees: f^* on pr₁^*H¹ ∪ pr₂^*H¹ is A ⊗ A⁻¹ = −(A ⊗ A) with A = [i]^*, so the −1-eigenspace of f^* (`weilSpace … 1`) is the +1-eigenspace of A ⊗ A, that is H^{1,0} ⊗ H^{0,1} ⊕ H^{0,1} ⊗ H^{1,0}, all of type (1, 1); f^* is +1 on pr₁^*H² and pr₂^*H² (deg [i] = 1). For `prod.map ellipticI ellipticI`, f^* = A ⊗ A on that part, the −1-eigenspace is H^{2,0} ⊕ H^{0,2}, a rational plane with no nonzero Hodge class, so F1 would be false and balance fails (both lines of H^{1,0} in V₊). Swapping the factors, or i for −i throughout, gives (1, 1) again (`isBalanced_neg_iff`). The morphism-level tests cannot detect the signature; finding 3 adds the morphism-level separation from `[i] × [i]`.

## 2. Hypotheses satisfiable

This rung is the instance. `ellipticSquare_witness`, `hodgeConjecture_ellipticSquare`, `lefschetzOneOne_ellipticSquare`, `hodge_eq_span_zero_ellipticSquare` and `ellipticSquare_fundamentalClass_ne_zero` build. A complex point exists (`nonempty_complexPoint_ellipticSquare`, the pair of origins through `pointProdHomeomorph`).

## 3. Trivial truth

None found. Each conjunct of `ellipticSquare_witness` is a property of a specific scheme proved from real instances (integrality from Mathlib's `GeometricallyIntegral`, `Flat`, `UniversallyOpen` instance over an integral locally noetherian factor). The relations of `ellipticWeilEndo` are morphism equalities; the non-identity tests `ellipticWeilEndo_ne_id` and `ellipticWeilEndo_comp_self_ne_id` compose with the diagonal `prod.lift (𝟙 _) (𝟙 _)` and reduce to `ellipticI_ne_id` and `ellipticNeg_ne_id` of `elliptic-curve-cm`, which were checked against point evaluations there. They are honest. The second shows f ≠ f⁻¹.

## 4. Interface rung

Not an interface rung; no structure, no axiom.

## 5. Checker and axioms

`python3 tools/check.py --no-build` on the branch: `ACCEPTED: all checks passed` (the rung names no declarations yet). `#print axioms` in scratch for `geometricallyIntegral_of_cover`, `geometricallyIntegral_spec`, `isDomain_quotient_tensor`, `geometricallyIntegral_iso_comp`, `isPullback_restrict`, `geometricallyIntegral_ellipticCurve`, `ellipticSquare_witness`, `ellipticWeilEndo_ne_id`, `ellipticWeilEndo_comp_self_ne_id`, `hodgeConjecture_ellipticSquare`, `lefschetzOneOne_ellipticSquare`, `hodge_eq_span_zero_ellipticSquare`, `ellipticSquare_fundamentalClass_ne_zero`, `relativeDimension_ellipticSquare_eq`, `ellipticSquare_t2Space`, `ellipticSquare_openParacompactSpace`, `isIso_ellipticWeilEndo`, `nonempty_complexPoint_ellipticSquare`: `[propext, Classical.choice, Quot.sound]` for each.

## 6. Conventions

| Convention | Used where | In the register | Truth depends on it |
|---|---|---|---|
| Plane cubic y²z = x³ − xz² and its charts | the field-general equations `affineEquationField`, `infinityEquationField` (equal to the ℂ ones by `rfl`, checked in scratch) | row "Plane cubic E and its charts" | no: integrality holds for y² = x³ ± x |
| `ellipticI` = (x, y) ↦ (−x, iy), `ellipticNeg` = (x, y) ↦ (x, −y) | `ellipticWeilEndo`, its relations | row "Complex multiplication on E" | no for the relations (they hold with −i) |
| `Limits.prod` in `Over (Spec ↧ℂ)`, first factor `prod.fst` | `ellipticSquare`, `ellipticWeilEndo_fst`, `_snd` | missing: added by change 7 | no here; it is distinct from Mathlib's monoidal `⊗` (finding 6) |
| Second factor [i]³ = [i]⁻¹ | `ellipticWeilEndo` | missing: added by change 7 | yes for `weil-elliptic-square` and for the balance condition (section 1); no for (f^*)² = −1 on H¹ and for the rank 2 of F2 |
| Weil space eigenvalue −d | consumers | row "Weil space" | consumers only |

The module docstring's sentence "No sign or normalization convention enters this file" is true of this file's results and silent on the one choice in it that a later rung's truth rests on; change 4 rewrites it.

## 7. Equality first

Not an identity and not an inclusion: a witness. The equalities it serves are `hodge_eq_span_zero_ellipticSquare` (codimension zero, present) and, downstream, `weil-elliptic-square` (an inclusion, open) toward `Hdg^1 = algebraicCycleClassSpan 1` (checked as `lefschetzOneOneEquality_holds`). The relations `ellipticWeilEndo_comp_self` and `ellipticWeilEndo_pow_four` are exact morphism equalities with no scalar.

## 7b. Non-vacuity

Smallest test that fails on a degenerate endomorphism: `HodgeLadder.Tests.ellipticWeilEndo_ne_id` (present) and `ellipticWeilEndo_comp_self_ne_id` (present). Missing: a test that fails if the cube on the second factor is simplified away, `ellipticWeilEndo_ne_prodMap_ellipticI` (change 3, compiled in scratch). For the surface: `ellipticSquare_fundamentalClass_ne_zero` (present, upstream's `cycleComponentSheafClass_genericPoint_ne_zero`).

## 8. Pin drift

None. Branch and `main` both pin upstream `2ead713` and Mathlib `v4.35.0-rc4`; `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are identical between `25b5025` and `main`. `main` has moved by `weil-surface-statement` (#277); the branch needs a rebase (change 8).

## Findings

1. **Cover lemma: correct, and its overlap hypothesis is necessary.** For a field point `Spec K ⟶ S` the preimages of `U`, `V`, `U ⊓ V` in `Z = X ×_S Spec K` are base changes of the charts (`isPullback_restrict` pastes `isPullback_morphismRestrict`), so they are integral and the overlap one is nonempty by surjectivity; reducedness is local on the two-set cover; irreducibility follows from two irreducible opens that meet. Mathlib's `GeometricallyIntegral` is `geometrically IsIntegral`: integrality of every base change to a field, which includes nonemptiness, so this is the definition used. The surjectivity of `(U ⊓ V).ι ≫ f` cannot be dropped: if `X ⟶ S` is geometrically integral, every fibre is irreducible, and the fibres of `U` and `V` are nonempty (each chart is surjective, Mathlib's low-priority instance), so they meet. Given the chart hypotheses, the lemma is an equivalence.
2. **Mathlib equivalents.** None at the pin. Mathlib has the converse direction for irreducibility only (instance: an open `U ⊆ X` surjecting onto `S` is geometrically irreducible if `X` is) and no ring-level geometrically-integral class (`Algebra.IsGeometricallyReduced` exists, no integral analogue). `geometricallyIntegral_iso_comp`: `MorphismProperty.RespectsIso @GeometricallyIntegral` is not found by instance search at the pin, so `RespectsIso.precomp` and `cancel_left_of_respectsIso` both fail in scratch; the local lemma stands.
3. **Placement of the General module.** `HodgeLadder.General.GeometricallyIntegralCover` imports `HodgeLadder.Tests.ProjectivePlane` (layer 6, 30 downstream modules, pulling upstream's projective Hausdorff and paracompact files) for one ten-line topological lemma. No module under `HodgeLadder/General/` imports a Tests module on `main` (`git grep` on `main`); the modules outside `Tests/` that import a Tests module are `Segre/General.lean`, `Hodge/DeRhamScalarSheaf.lean` and `Hodge/WedgeSheafify.lean`, none of them General. With the two-open lemma inlined (change 1, compiled as a module in scratch) the module imports Mathlib only and drops from layer 7 to layer 0, the layer of its neighbours `General.ComplexPointProd`, `General.HypersurfaceSmooth`.
4. **Placement of the witness.** `HodgeLadder/Elliptic/Square/Witness.lean` is `next.py`'s fallback from the rung id. Its namespace is `HodgeLadder.Tests`, and every sibling witness (`Tests/P1p1Witness.lean`, `Tests/EllipticCurveWitness.lean`, `Tests/ProjectivePlane.lean`) lives in `HodgeLadder/Tests/`; the `elliptic-curve-integral` red team made the same call for the curve witness. Nothing in the ledger, notes or tools refers to `HodgeLadder.Elliptic`. Move it (change 2).
5. **Duplication with `elliptic-curve-integral`.** The field-general section duplicates the ℂ root checks. The ℂ declarations are the field ones at `K := ℂ` by `rfl` (scratch: `affineEquationField ℂ = affineEquation`, `infinityEquationField ℂ = infinityEquation`, `bivariateEquivSwapField ℂ = bivariateEquivSwap`, `bivariateEquiv = bivariateEquivField ℂ`, and `@sq_ne_X_pow_three_sub_X_field ℂ _ = sq_ne_X_pow_three_sub_X`). `HodgeLadder.Tests.EllipticCurveIntegral` has 2 downstream modules, so collapsing the copy there is cheap, but it edits a checked rung's module; this pass requires two `rfl` pins that break the build if the two copies diverge (change 3) and a gaps row (change 6), and leaves the collapse optional (O1).
6. **`⨯` against `⊗` for the GrpObj rung.** `ellipticSquare` is `Limits.prod`; Mathlib's `CartesianMonoidalCategory` product on `Over (Spec ↧ℂ)` is `ellipticCurve ⊗ ellipticCurve`, and the two are not definitionally equal (`rfl` fails in scratch). This blocks nothing: given `[GrpObj ellipticCurve]`, Mathlib gives `GrpObj (ellipticCurve ⊗ ellipticCurve)` and
   `GrpObj.ofIso (G := ellipticCurve ⊗ ellipticCurve) ((CartesianMonoidalCategory.tensorProductIsBinaryProduct ellipticCurve ellipticCurve).conePointUniqueUpToIso (limit.isLimit _))` is a `GrpObj ellipticSquare` (compiled in scratch). Mathlib's `isCommMonObj_of_isProper_of_geometricallyIntegral` takes `[GeometricallyIntegral G.hom]`, which this rung now supplies for E. Recorded for `weil-elliptic-square-grpobj` (O2).
7. **Docstring claims beyond the checked content.** The docstring of `ellipticWeilEndo` says the endomorphism acts on "H¹ = H¹(E) ⊕ H¹(E)" with "the balanced signature"; Künneth and the eigenvalues on H^{1,0} are unchecked at the pin (nodes C8, D6). Change 4 says so.
8. **Instances as upstream needs them.** Upstream's `HodgeConjecture` specializes at `ellipticSquare` with its instance arguments found (`hodgeConjecture_ellipticSquare`). Two `Smooth` instances exist (`smooth_prod` and the one through `SmoothOfRelativeDimension`); `Smooth` is a `Prop`, so no diamond. `isIntegral_pullback_ellipticSquare` restates a Mathlib instance as a named instance; harmless.
9. **Signs.** None in the relations: `ellipticI_cube_comp_self`, `ellipticWeilEndo_comp_self`, `ellipticWeilEndo_pow_four` hold for [−i] in place of [i]. `pullbackCoh` is contravariant, which is immaterial for powers of one map. The (f^*)² = −1 on H¹ of `IsWeilTypeSurface` needs [−1]^* = −1 on H¹(E) (node C7), not this rung.

## Required changes

1. `HodgeLadder/General/GeometricallyIntegralCover.lean`:
   - delete the line `public import HodgeLadder.Tests.ProjectivePlane`;
   - before the docstring of `geometricallyIntegral_of_cover`, insert:

     ```lean
     /-- A space covered by two irreducible opens that meet is irreducible. -/
     theorem irreducibleSpace_of_two_opens {Z : Type*} [TopologicalSpace Z] {U V : Set Z}
         (hU : IsOpen U) (hUi : IsIrreducible U) (hVi : IsIrreducible V)
         (hcov : U ∪ V = Set.univ) (hUV : (U ∩ V).Nonempty) : IrreducibleSpace Z := by
       have h1 : V ⊆ closure U :=
         (subset_closure_inter_of_isPreirreducible_of_isOpen hVi.2 hU
           (by rw [Set.inter_comm]; exact hUV)).trans (closure_mono Set.inter_subset_right)
       have h2 : closure U = Set.univ :=
         Set.eq_univ_of_univ_subset (hcov ▸ Set.union_subset subset_closure h1)
       have h3 := hUi.closure
       rw [h2] at h3
       exact (irreducibleSpace_def Z).mpr h3
     ```

   - replace the whole `have hirr : IrreducibleSpace Z := by` block (through the line before `exact isIntegral_of_irreducibleSpace_of_isReduced Z`) by:

     ```lean
       have hirr : IrreducibleSpace Z := by
         refine irreducibleSpace_of_two_opens (fst ⁻¹ᵁ U).isOpen
           (isIrreducible_iff_irreducibleSpace.mpr
             (inferInstanceAs (IrreducibleSpace (fst ⁻¹ᵁ U).toScheme)))
           (isIrreducible_iff_irreducibleSpace.mpr
             (inferInstanceAs (IrreducibleSpace (fst ⁻¹ᵁ V).toScheme))) ?_
           ⟨(fst ⁻¹ᵁ (U ⊓ V)).ι w, hw.1, hw.2⟩
         have := congrArg (fun W : Z.Opens => (W : Set Z)) hcov
         simpa using this
     ```

   - in the module docstring replace "(`irreducibleSpace_of_cover` of `p2-witness`)." by "(`irreducibleSpace_of_two_opens`, the two-open case of `HodgeLadder.Tests.irreducibleSpace_of_cover`, kept here so that this module imports Mathlib only).", and add `` * `HodgeLadder.GeometricallyIntegralCover.irreducibleSpace_of_two_opens` `` first under "Main results".

   The file with these edits compiled as a module in scratch.

2. Move `HodgeLadder/Elliptic/Square/Witness.lean` to `HodgeLadder/Tests/EllipticSquareWitness.lean` (module `HodgeLadder.Tests.EllipticSquareWitness`), delete the empty `HodgeLadder/Elliptic/` directory, and replace `public import HodgeLadder.Elliptic.Square.Witness` in `HodgeLadder.lean` by `public import HodgeLadder.Tests.EllipticSquareWitness`.

3. In the witness file, add after `ellipticWeilEndo_comp_self_ne_id`:

   ```lean
   /-- **The Weil endomorphism is not `[i] × [i]`**: on the second factor `[i]³ ≠ [i]`, since
   otherwise `[−1] = [i]⁴ = 𝟙`. `prod.map ellipticI ellipticI` has signature `(2, 0)` and fails the
   balance condition of `IsWeilTypeSurface`. -/
   theorem ellipticWeilEndo_ne_prodMap_ellipticI :
       ellipticWeilEndo ≠ prod.map ellipticI ellipticI := by
     intro h
     have h1 := congrArg (· ≫ prod.snd) h
     simp only [ellipticWeilEndo, prod.map_snd] at h1
     have h2 := congrArg (prod.lift (𝟙 ellipticCurve) (𝟙 ellipticCurve) ≫ ·) h1
     simp only [prod.lift_snd_assoc, Category.id_comp] at h2
     have h3 : ellipticI ≫ ellipticI ≫ ellipticI ≫ ellipticI = ellipticI ≫ ellipticI := by
       rw [h2]
     rw [ellipticI_pow_four, ellipticI_comp_self] at h3
     exact ellipticNeg_ne_id h3.symm
   ```

   and after `map_infinityEquation`:

   ```lean
   /-- The field-general affine equation at `K = ℂ` is that of `elliptic-curve-integral`. -/
   theorem affineEquationField_complex : affineEquationField ℂ = affineEquation := rfl

   /-- The field-general equation at infinity at `K = ℂ` is that of `elliptic-curve-integral`. -/
   theorem infinityEquationField_complex : infinityEquationField ℂ = infinityEquation := rfl
   ```

   Add `ellipticWeilEndo_ne_prodMap_ellipticI` to the Weil bullet and `affineEquationField_complex`, `infinityEquationField_complex` to "Main results". All three compiled in scratch with the standard axioms.

4. Docstrings in the witness file.
   - Module docstring: replace the paragraph beginning "No sign or normalization convention enters this file" by: "No sign or normalization convention enters the truth of this file: integrality holds for `y² = x³ ± x`, and the relations of `ellipticWeilEndo` are those of `elliptic-curve-cm` (`ellipticI_comp_self`, `ellipticI_pow_four`, `ellipticNeg_comp_self`) read factorwise, true with `−i` in place of `i`. One choice here is load-bearing downstream: the cube on the second factor. With `[i]^*(dx/y) = i · dx/y`, `[i] × [i]³` puts one line of `H^{1,0}(E × E)` in each eigenspace (signature `(1, 1)`), which `weil-elliptic-square` needs; `prod.map ellipticI ellipticI` has signature `(2, 0)`, where that rung is false (`ellipticWeilEndo_ne_prodMap_ellipticI`; `docs/conventions.md`, row "Abelian surface E × E and the Weil endomorphism")."
   - Docstring of `ellipticWeilEndo`: replace "On `H¹ = H¹(E) ⊕ H¹(E)` it acts as `[i]^*` on the first summand and `([i]^*)³ = ([i]^*)⁻¹` on the second, the balanced signature of `weil-elliptic-square`." by "Through Künneth, `H¹(E × E) = pr₁^*H¹(E) ⊕ pr₂^*H¹(E)` (planned in `elliptic-square-cohomology`), it acts as `[i]^*` on the first summand and `([i]^*)³ = ([i]^*)⁻¹` on the second; on `H^{1,0}` that is `i` and `−i` (read from the literature, node D6), the signature `(1, 1)` that `weil-elliptic-square` needs. Not checkable at the pin."
   - "Main results": `ellipticSquare_t2Space` is listed; add `ellipticAffineChart_ι_hom`, `ellipticInfinityChart_ι_hom`, `ellipticI_cube_comp_self`.

5. `ledger/ladder.json`, entry `elliptic-square-witness`: `"status": "checked"`, `"module": "HodgeLadder.Tests.EllipticSquareWitness"`, `"contributors": ["claude-code"]`, `"declarations"`: every `theorem`, `def`, `instance` and `abbrev` of both files, at least `HodgeLadder.GeometricallyIntegralCover.irreducibleSpace_of_two_opens`, `isPullback_restrict`, `geometricallyIntegral_of_cover`, `geometricallyIntegral_iso_comp`, `geometricallyIntegral_spec`, `isDomain_quotient_tensor`, and `HodgeLadder.Tests.` `geometricallyIntegral_ellipticCurve`, `geometricallyIntegral_affineChartSpec`, `geometricallyIntegral_infinityChartSpec`, `geometricallyIntegral_ellipticAffineChart`, `geometricallyIntegral_ellipticInfinityChart`, `surjective_ellipticChartInter`, `ellipticAffineChart_ι_hom`, `ellipticInfinityChart_ι_hom`, `irreducible_affineEquationField`, `irreducible_infinityEquationField`, `isPrime_span_map_affineEquation`, `isPrime_span_map_infinityEquation`, `affineEquationField_complex`, `infinityEquationField_complex`, `ellipticSquare`, `isIntegral_ellipticSquare`, `smoothOfRelativeDimension_ellipticSquare`, `smooth_ellipticSquare`, `isProjective_ellipticSquare`, `ellipticSquare_t2Space`, `nonempty_complexPoint_ellipticSquare`, `ellipticSquare_openParacompactSpace`, `dim_ellipticSquare`, `relativeDimension_ellipticSquare_eq`, `ellipticI_cube_comp_self`, `ellipticWeilEndo`, `ellipticWeilEndo_fst`, `ellipticWeilEndo_snd`, `ellipticWeilEndo_comp_self`, `ellipticWeilEndo_pow_four`, `ellipticWeilIso`, `isIso_ellipticWeilEndo`, `ellipticWeilEndo_ne_id`, `ellipticWeilEndo_comp_self_ne_id`, `ellipticWeilEndo_ne_prodMap_ellipticI`, `ellipticSquare_witness`, `hodgeConjecture_ellipticSquare`, `lefschetzOneOne_ellipticSquare`, `hodge_eq_span_zero_ellipticSquare`, `ellipticSquare_fundamentalClass_ne_zero`. `"note"`: "Checked 2026-11-28. Plan: docs/notes/2026-11-27-t1-plan.md, node E7. E is geometrically integral over ℂ (geometricallyIntegral_ellipticCurve): both chart rings stay domains over every field K over ℂ (field-general root checks, equal to those of elliptic-curve-integral at K = ℂ by rfl; (ℂ[σ] ⧸ (g)) ⊗[ℂ] K ≃ K[σ] ⧸ (g)), and the charts meet at (i, 1 − i) (general geometricallyIntegral_of_cover, geometricallyIntegral_spec, isDomain_quotient_tensor in HodgeLadder.General.GeometricallyIntegralCover). E × E = ellipticCurve ⨯ ellipticCurve is integral by Mathlib's instance for a geometrically integral, flat, universally open factor over an integral locally noetherian one; smooth of relative dimension 1 + 1, projective (isProjective_prod), T2 complex points, paracompact opens, dim 2. ellipticWeilEndo = [i] × [i]³: square [−1] × [−1], fourth power 𝟙, an isomorphism, ≠ 𝟙, square ≠ 𝟙, ≠ [i] × [i]. Upstream HodgeConjecture, Lefschetz (1,1) and codimension zero at E × E; the class of E × E is nonzero. No sign enters; the cube on the second factor is load-bearing for weil-elliptic-square (signature (1, 1); [i] × [i] has (2, 0)). No GrpObj instance (open rung weil-elliptic-square-grpobj). Red team: pass with changes (docs/sketches/elliptic-square-witness.redteam.md)." Bump `updated`. In `docs/roadmap.md`, row `elliptic-square-witness`: status `checked`, and in the last column replace "T2 from `pointProdHomeomorph`; integral needs E geometrically integral over ℂ (the `p1p1-witness` route)" by "T2 from upstream's projective instance; integral from E geometrically integral over ℂ (two geometrically integral charts that meet, `HodgeLadder.General.GeometricallyIntegralCover`)".

6. `docs/gaps.md`, category "Algebraic geometry and commutative algebra", insert after the `HodgeLadder.General.HypersurfaceSmooth` row (layer 0):

   `| HodgeLadder.GeometricallyIntegralCover.geometricallyIntegral_of_cover (X ⟶ S is geometrically integral when two opens covering X are, and their overlap maps onto S), isPullback_restrict, geometricallyIntegral_iso_comp, geometricallyIntegral_spec (Spec A ⟶ Spec R is geometrically integral when A ⊗[R] K is a domain for every field K over R), isDomain_quotient_tensor ((R[σ] ⧸ (g)) ⊗[R] K is a domain when (g) stays prime in K[σ]), irreducibleSpace_of_two_opens (two irreducible opens that meet; the two-open case of HodgeLadder.Tests.irreducibleSpace_of_cover, kept so the module imports Mathlib only) | HodgeLadder.General.GeometricallyIntegralCover | 0 | Mathlib at the pin has GeometricallyIntegral, its base-change and product instances, and the open-subscheme direction for GeometricallyIrreducible, and no criterion for a scheme to be geometrically integral from charts or for a ring; no RespectsIso instance for GeometricallyIntegral is found at the pin; at a bump check Mathlib AlgebraicGeometry/Geometrically/ for a local-on-source criterion and RingTheory/ for an Algebra.IsGeometricallyIntegral class; rung elliptic-square-witness | 2026-11-28 |`

   (with the declaration names in backticks, as in the neighbouring rows), and after the `HodgeLadder.Tests.EllipticCurveCM` row:

   `| HodgeLadder.Tests.sq_ne_X_pow_three_sub_X_field, pow_three_sub_X_sq_mul_sub_X_ne_zero_field, irreducible_affinePoly_field, irreducible_infinityPoly_field, bivariateEquivSwapField, bivariateEquivField, affineEquationField, infinityEquationField, irreducible_affineEquationField, irreducible_infinityEquationField (the root checks and irreducibility of elliptic-curve-integral over any field) | HodgeLadder.Tests.EllipticSquareWitness | 47 | duplicates of the ℂ declarations of HodgeLadder.Tests.EllipticCurveIntegral (2 downstream modules), equal to them at K = ℂ by rfl (affineEquationField_complex, infinityEquationField_complex pin the equations); a later touch of that module can derive its ℂ forms from these; rung elliptic-square-witness | 2026-11-28 |`

   Recompute both layers with `python3 tools/pinwalk.py` after changes 1 and 2 and write the printed values.

7. `docs/conventions.md`, new row after "Complex multiplication on E":

   `| Abelian surface E × E and the Weil endomorphism | this repository, HodgeLadder.Tests.ellipticSquare, ellipticWeilEndo, ellipticWeilEndo_fst, ellipticWeilEndo_snd, ellipticWeilEndo_comp_self, ellipticWeilEndo_ne_prodMap_ellipticI (HodgeLadder/Tests/EllipticSquareWitness.lean, rung elliptic-square-witness) | ellipticSquare is Limits.prod ellipticCurve ellipticCurve in Over (Spec ↧ℂ) (the spelling of complex-points-prod), first factor prod.fst; it is isomorphic to Mathlib's monoidal ellipticCurve ⊗ ellipticCurve and not definitionally equal to it (a GrpObj transports along tensorProductIsBinaryProduct by GrpObj.ofIso). ellipticWeilEndo = prod.map ellipticI (ellipticI ≫ ellipticI ≫ ellipticI) = [i] × [i]⁻¹, square [−1] × [−1]; with [i]^*(dx/y) = i · dx/y (row "Complex multiplication on E") the factors act on H^{1,0} by i and −i, signature (1, 1) | weil-elliptic-square (F1) and the balance condition of IsWeilTypeSurface at (ellipticSquare, ellipticWeilEndo, 1): true for [i] × [i]⁻¹, false for prod.map ellipticI ellipticI (signature (2, 0): weilSpace ⊗ ℂ = H^{2,0} ⊕ H^{0,2}, nonzero with no Hodge class); none for (f^*)² = −1 on H¹ or for rank 2 of weil-elliptic-square-nonzero (both hold for either choice); swapping factors or i for −i is immaterial (isBalanced_neg_iff) | read from source; ellipticWeilEndo ≠ prod.map ellipticI ellipticI checked; the signature argued from the literature (Künneth, node C8; eigenvalue on dx/y, node D6), not checkable at the pin; red team 2026-11-28, elliptic-square-witness |`

   (declaration names in backticks, as in the neighbouring rows).

8. Rebase `track/elliptic-square-witness` onto `main` (`ab87174` or later); resolve the tails of `HodgeLadder.lean`, `ledger/ladder.json`, `docs/gaps.md`, `docs/conventions.md`, `docs/roadmap.md` by keeping both sides. Rerun `python3 tools/check.py` and confirm the axioms line for every declaration of change 5.

## Not required

- O1. In `HodgeLadder/Tests/EllipticCurveIntegral.lean` (2 downstream modules), prove the ℂ root checks as `sq_ne_X_pow_three_sub_X_field` etc. at `K := ℂ`, or move the field section to a small module both files import. Drop the second gaps row of change 6 when done.
- O2. In the ledger note of `weil-elliptic-square-grpobj`, append: "E × E is Limits.prod; given GrpObj ellipticCurve, GrpObj.ofIso along CartesianMonoidalCategory.tensorProductIsBinaryProduct gives GrpObj ellipticSquare (checked in scratch, red team of elliptic-square-witness); geometricallyIntegral_ellipticCurve feeds Mathlib's isCommMonObj_of_isProper_of_geometricallyIntegral."
- O3. The plan's unbalanced test (f' = [i] × [i], weilSpace ⊓ Hdg^1 = ⊥) stays unposted for the reason the plan gives; `ellipticWeilEndo_ne_prodMap_ellipticI` is only its morphism-level shadow.

## Tried and failed

- `MorphismProperty.RespectsIso.precomp` and `cancel_left_of_respectsIso` for `geometricallyIntegral_iso_comp`: no `RespectsIso @GeometricallyIntegral` instance found at the pin.
- `rfl : ellipticCurve ⊗ ellipticCurve = ellipticSquare`: fails (finding 6).
- `GrpObj.ofIso` with the cone-point iso without naming `G`: instance search fails on the `BinaryFan.mk` cone point; naming `G := ellipticCurve ⊗ ellipticCurve` fixes it.
- A short proof of any conjunct of `ellipticSquare_witness` that avoids geometric integrality or the product instances: none found; integrality of the product needs the geometric hypothesis on one factor in Mathlib's instance.
