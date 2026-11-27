# Red team: `p2-point-class-nonzero` (statement and proof)

Date: 2026-11-26. Worktree `p2-point-class-nonzero`, base `b709544`, uncommitted `HodgeLadder/Tests/ProjectivePlanePoint.lean` and the section "p2-point-class-nonzero: statement" of `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713` (package checkout `rev-parse HEAD` and `lake-manifest.json` agree), Lean and Mathlib `v4.35.0-rc4`.

Targets: `projectivePlane_point_class_ne_zero`, `cycleComponentSheafClass_ne_zero_of_subsingleton_three`, `subsingleton_H'_three_compl_planeOrigin`, `planeOrigin_support_compl`, `planeChartOpen_zero_inf_one`, `contractibleSpace_planeChartOpen`, `contractibleSpace_planeChartZeroOpen`, `contractibleSpace_of_starConvex_image`, and the helpers of the file (`mem_projectiveChart_source_iff`, `mem_projectiveChart_source_iff_of_mem`, the four chart sets with openness, star-convexity, union and intersection lemmas, the `planeChartZeroOpen` lattice lemmas).

Read at the pin: upstream `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean` (`cycleComponentSupportedClassNormalizationIso`, `cycleComponentSupportedInjectiveClass`, `cycleComponentSheafClass`), `Other/AlgebraicGeometry/Cycle/FundamentalClass.lean` (`cycleComponentSupportedInjectiveClass_normalization`, `cycleComponentSheafClass_eq_forgetSupport`, an `rfl`), `Other/AlgebraicGeometry/Hodge/CodimensionZeroNonvanishing.lean` (`cycleComponentSmoothSupportCoclassSection_ne_zero`), `Other/AlgebraicGeometry/Cycle/BorelMooreClass.lean` (`maximalCodimensionBorelMooreFundamentalClass_ne_zero`); the port's `Oka/Topology/Sheaves/Cohomology/Dimension.lean` (`TopCat.Sheaf.subsingleton_H'_bot`, `subsingleton_H'_sup`, from Mathlib's `mayerVietorisSequence_exact`); this repository's `Tests/ClassNonzero.lean`, `Tests/ForgetSupport.lean`, `Tests/ContractibleAcyclic.lean`, `Tests/ProjectiveChart.lean`, `Tests/ProjectivePlaneLines.lean`, `Normalization/AffineChart.lean`.

Scratch files (inside the worktree, deleted afterwards). The new module has no `.olean`, so RT-A is a verbatim copy of the file with commands appended; RT-B imports the built `ProjectivePlaneLines`, `ClassNonzero` and `ContractibleAcyclic`.

| File | What | Result |
|---|---|---|
| RT-A | copy of the file plus `#print axioms` of all 25 declarations | compiles, 20 s wall, default heartbeats; every declaration prints `[propext, Classical.choice, Quot.sound]` |
| RT-B1 | trivial proofs of the rung: `simp`; `intro h; simp [cycleComponentSheafClass] at h`; the codimension-one criterion at the point | all fail (section 3) |
| RT-B2 | `Subsingleton (H'³ of the complement)` by `infer_instance` | fails |
| RT-B3 | the criterion in every positive codimension, `cycleComponentSheafClass_ne_zero_of_subsingleton_odd`, and both existing criteria as its cases p = 0 and p = 1 | compiles, standard axioms (change 4) |

`python3 tools/check.py --no-build` in the worktree, scratch deleted: `ACCEPTED: all checks passed`. The new module is imported neither by `HodgeLadder.lean` nor named by the ledger, so this run neither builds nor scans it; RT-A is the evidence for its axioms until change 1 lands.

**Verdict: pass with changes.** The statement is the nonvanishing that `cup-positive-degree-test-p2` needs, against the exact right side of `cycle-class-multiplicative-p2`. The Mayer–Vietoris computation is correct in every degree, every piece is star-convex in a standard chart in the analytic topology the sheaf lives on, and the criterion is general and uses its hypothesis. No sign or normalization can change the truth of the result. Changes: bookkeeping for the ledger, root import and roadmap (required, text below); `depends_on` gains `contractible-open-acyclic` and `lefschetz-port` (required); one sentence of the module docstring (recommended); the all-codimension criterion (recommended, exact Lean below, checked); conventions row (done).

## 1. Is this the statement the literature makes?

Literature: for X smooth projective over ℂ of dimension n and a point P, the class [P] generates H^{2n}(X; ℚ) ≅ ℚ; on ℙ² it is the generator of H⁴(ℙ²; ℚ) and is dual to the class of a line squared [`Hatcher2002` §3.2, cohomology ring of ℂPⁿ; `Fulton1998` ch. 19 for the cycle map, numbering unverified]. The rung asks for the weaker nonvanishing.

| Literature object | Lean | Comparison |
|---|---|---|
| H⁴(ℙ²(ℂ); ℚ) | `H^(2 * 2)(projectivePlane; ℚ)`, upstream sheaf cohomology of the constant sheaf ℚ on `TopCat.of (ComplexPoint projectivePlane)` | the type of `cycleComponentSheafClass` with p = 2 |
| [pt], pt = [0 : 0 : 1] | `cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin` | `planeOrigin` and `coheight_planeOrigin : coheight planeOrigin = ↑2` are the declarations of the checked `p2-lines-transversal`; its red team confirmed the point is [0 : 0 : 1] and coheight is codimension |
| [pt] ≠ 0 | `≠ 0` | exact |

**Right input for `cup-positive-degree-test-p2`.** The sketch's instantiation check (section "p2-lines-transversal", line 593 of the sketch) elaborates `cycle-class-multiplicative-p2` as `cup [L₀] [L₁] (2 * (1 + 1)) _ = cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin`. The right side is syntactically this rung's left side, so the test closes as `h ▸ projectivePlane_point_class_ne_zero` with no transport. The square-zero product satisfies the checked cup laws and would make [L₀] ∪ [L₁] = 0; combined with the equality, this rung rules it out. Even if the equality acquired a nonzero rational scalar or a sign, nonvanishing would survive, but decision 0004 wants the equality exact and its sketch states it exactly.

## 2. Can the hypotheses be satisfied?

The rung has no hypotheses. The criterion `cycleComponentSheafClass_ne_zero_of_subsingleton_three` has the instances of upstream's `cycleComponentSheafClass` (`IsIntegral`, `Smooth`, `IsProjective`), a coheight-two point and an H³ vanishing; all are met by `projectivePlane`, `planeOrigin`, `coheight_planeOrigin`, `subsingleton_H'_three_compl_planeOrigin`, which is the rung's proof. `contractibleSpace_planeChartZeroOpen` is applied to four nonempty star-convex sets with explicit centers; `contractibleSpace_of_starConvex_image` has a nonemptiness hypothesis, which Mathlib's `StarConvex.contractibleSpace` needs.

## 3. Trivial truth

- The conclusion is a nonvanishing in a group that upstream builds from Ext of the constant sheaf; nothing unfolds to `True`. `simp` leaves `¬cycleComponentSheafClass … = 0`; unfolding the definition leaves `forgetSupport … 4 (cycleComponentSupportedInjectiveClass …) = 0 ⊢ False` (RT-B1).
- The codimension-one criterion does not apply (`coheight planeOrigin = ↑2` against `↑1`, and the H¹ instance is not found): the degree bookkeeping is live.
- `infer_instance` fails on the H³ vanishing (RT-B2). The method is specific to the degree: applied to H¹ of {v₀ ≠ 0}, the same Mayer–Vietoris lemma would ask for H⁰ of the two half-spaces to vanish, which is false (ℚ²) and has no proof.
- Every hypothesis is used: `h` feeds `forgetSupport_injective_of_subsingleton`; the four `ContractibleSpace` instances feed `contractibleOpen_subsingleton_H'`; the cover lemmas feed the three `rw` steps.
- The proof reaches nonvanishing only through upstream's `cycleComponentSmoothSupportCoclassSection_ne_zero` (the normalized local class is nonzero on the smooth locus) and the normalization isomorphism. A degenerate model of `Sheaf.H'` (if every H' vanished) would make the H³ input free but could not make the conclusion false or vacuous: it is about the global class, and `forgetSupport` is upstream's map. So the rung is a genuine non-vacuity witness for H⁴(ℙ²; ℚ) in upstream's model.
- No `ℕ∞` trap: `hx : coheight x = ((2 : ℕ) : ℕ∞)` fixes p = 2 and the degree `2 * 2`, which meets `3 + 1` of `forgetSupport_injective_of_subsingleton` at n = 3 by evaluation.

## 4. Interface axioms

Not an interface rung; no structure, no `Prop` input. The only cited inputs are checked declarations (port, Mathlib, this ladder, upstream `Other`).

## 5. Axioms and declarations

RT-A prints `[propext, Classical.choice, Quot.sound]` for all 25 declarations of the file. The ledger currently names none (status `open`, `declarations: []`); change 1 lists them. `check.py --no-build` passes on the tree as it stands, but it does not see the file (see the table above).

## 6. Conventions

| Convention | Used where | Truth depends on it? |
|---|---|---|
| Fundamental-class normalization (local class 1 on complex orientations) | `cycleComponentSmoothSupportCoclassSection_ne_zero`, the normalization isomorphism | no: any nonzero scalar or a sign keeps the class nonzero |
| Coheight as codimension (scheme order `a ≤ b ↔ b ⤳ a`) | `coheight_planeOrigin`, the degree 2 · 2 | yes for the degree: with height in its place the point would have p = 0 and the class would live in H⁰. Row "Cycle components", checked by `p2-lines-transversal` |
| Chart coordinates: chart i has coordinate m equal to x_{i.succAbove m} / xᵢ, inverse chart at v is `Fin.insertNth i 1 v` | `planeChartOpen_zero_inf_one` (x₁ ≠ 0 in the chart x₀ ≠ 0 is v₀ ≠ 0), `planeOrigin_support_compl` (the point lies in neither x₀ ≠ 0 nor x₁ ≠ 0, via chart 2 at 0) | the cover identities are proved from `projectiveChart_symm_mem_U_iff`, so a wrong reading would fail to compile; the vanishing of H³ is insensitive to coordinate order. Row "Algebraic affine chart", extended |
| `Sheaf.H'` of an open and Mayer–Vietoris | `subsingleton_H'_sup` (degrees q, q + 1, q + 1), `subsingleton_H'_bot`, `contractibleOpen_subsingleton_H'` | vanishing statements only, insensitive to the sign of the connecting map; new row |
| Analytic topology on `ComplexPoint` | contractibility of the chart pieces, the sheaf `planeConst` | `projectiveChart` is an `OpenPartialHomeomorph` for upstream's analytic topology (`affineChart`, built from `affineSpaceHomeomorph`), the same topology as `TopCat.of (ComplexPoint projectivePlane)`; recorded in the new row |

Sign: none enters. The rung is a nonvanishing, insensitive to sign and to nonzero rational scalars.

## 7. Equality first

Not an identity. It is the nonvanishing half of `cup-positive-degree-test-p2`; the equality it pairs with is `cycle-class-multiplicative-p2` (exists, `open`; instance check in the sketch), whose general form is `cycle-class-multiplicative` (exists, `open`). An exact computation [pt] = generator would need a degree map H⁴ → ℚ, which the pin lacks (the sketch's "Route chosen" paragraph; `integralCompactificationFundamentalClass` takes existence as a hypothesis). `maximalCodimensionBorelMooreFundamentalClass_ne_zero` in `Other` was checked as a possible shortcut: it is a statement about Borel–Moore homology of the cycle itself, a local group, and does not reach H⁴(ℙ²).

## 7b. Non-vacuity

The rung is itself the non-vacuity input of `cup-positive-degree-test-p2`. The smallest test that would fail if upstream's H⁴ class were degenerate is this theorem; the smallest test that would fail if the H³ hypothesis of the criterion were free is a positive-degree nonvanishing of `Sheaf.H'`, for instance `Nontrivial (Sheaf.H' planeConst 1 (planeChartOpen 0 ⊓ planeChartOpen 1))` (H¹ of ℂ* × ℂ). It does not exist on the ladder (grep for `Nontrivial` over `HodgeLadder/`: none on sheaf cohomology). Its absence does not affect this rung (section 3, fifth item); it would matter for a rung that claims a cohomology group is nonzero by computing it.

## 8. Pin drift

Checked against the current pin `2ead713`; the worktree base `b709544` is `main`. No drift. Upstream declarations the proof depends on, for the next bump: `cycleComponentSheafClass`, `cycleComponentSupportedInjectiveClass`, `cycleComponentSupportedClassNormalizationIso`, `cycleComponentSheafClass_eq_forgetSupport` (must stay `rfl`), `cycleComponentSupportedInjectiveClass_normalization`, `cycleComponentSmoothSupportCoclassSection_ne_zero`, `cycleComponentAnalyticClosedSupport`, `forgetSupport`, `Point.analyticTopology` on `ComplexPoint`, `affineSpaceHomeomorph`; Mathlib `Sheaf.H'`, `mayerVietorisSequence_exact`, `Complex.starConvex_one_slitPlane`, `StarConvex.contractibleSpace`, `OpenPartialHomeomorph.homeomorphOfImageSubsetSource`. The `Other` lemmas are outside upstream's statement-import guard, as for `projective-line-class-nonzero`.

## The Mayer–Vietoris computation, checked by hand

Exact segment used (`subsingleton_H'_sup` at q): H^q(A ∩ B) → H^{q+1}(A ∪ B) → H^{q+1}(A) ⊕ H^{q+1}(B). If the outer terms vanish, so does the middle.

| Step | q | A ∪ B | A, B (contractible) | A ∩ B | input |
|---|---|---|---|---|---|
| 3 | 2 | U = ℙ²(ℂ) ∖ [0 : 0 : 1] = {x₀ ≠ 0} ∪ {x₁ ≠ 0} | the two charts, each ≅ ℂ² | {x₀x₁ ≠ 0} = {v₀ ≠ 0} in chart 0, ≅ ℂ* × ℂ | H² of ℂ* × ℂ |
| 2 | 1 | {v₀ ≠ 0} | v₀ ∈ ℂ ∖ (−∞, 0], about (1, 1); −v₀ ∈ ℂ ∖ (−∞, 0], about (−1, −1) | {Im v₀ ≠ 0} | H¹ of two half-spaces |
| 1 | 0 | {Im v₀ ≠ 0} | Im v₀ > 0, about (i, i); Im v₀ < 0, about (−i, −i) | ∅ | H⁰(∅) = 0 |

Each row is right. Cover: a point off both charts has x₀ = x₁ = 0, so it is [0 : 0 : 1] (proved through chart 2 and `exists_mem_U`). Intersection: in chart 0 the point with coordinates v has homogeneous coordinates (1, v₀, v₁), so x₁ ≠ 0 iff v₀ ≠ 0. Slits: their union misses exactly v₀ = 0 (v₀ is in (−∞, 0] and in [0, ∞) only at 0); their intersection is v₀ ∉ ℝ, that is Im v₀ ≠ 0. Star-convexity: `Complex.starConvex_one_slitPlane` pulled back along the ℝ-linear projection v ↦ v₀ (center maps to 1, as `StarConvex.linear_preimage` needs), the negated copy, and half-spaces that are convex with the center inside. The second coordinate v₁ is unconstrained, so each set is (star-convex in ℂ) × ℂ. Topology: the answer H³(U) = 0 agrees with U ≃ S² (U retracts onto the line x₂ = 0), and H²(ℂ* × ℂ) = 0, H¹(two contractible components) = 0 agree with the homotopy types.

`contractibleOpen_subsingleton_H'` needs paracompactness, Hausdorffness and a contractible open basis; it derives all three internally from `X` smooth projective (`openParacompactSpace`, `exists_contractibleOpen_le`), so its only instance argument is `[ContractibleSpace U]`, supplied here.

## Recommended changes

1. **Bookkeeping (required).** Add `public import HodgeLadder.Tests.ProjectivePlanePoint` to `HodgeLadder.lean`, so `lake build` and the checker see the file. Ledger entry:
   - `status`: `checked`; `module`: `HodgeLadder.Tests.ProjectivePlanePoint`;
   - `declarations`: `HodgeLadder.Tests.projectivePlane_point_class_ne_zero`, `HodgeLadder.Tests.cycleComponentSheafClass_ne_zero_of_subsingleton_three`, `HodgeLadder.Tests.subsingleton_H'_three_compl_planeOrigin`, `HodgeLadder.Tests.planeOrigin_support_compl`, `HodgeLadder.Tests.planeChartOpen_zero_inf_one`, `HodgeLadder.Tests.contractibleSpace_planeChartOpen`, `HodgeLadder.Tests.contractibleSpace_planeChartZeroOpen`, `HodgeLadder.Tests.contractibleSpace_of_starConvex_image`;
   - `note`: "Checked 2026-11-26. General criterion (any smooth projective integral X, codimension two): the class is nonzero when H³ of the support complement vanishes, from upstream's nonzero supported class (normalization isomorphism) and forget-support-exact at n = 3. On ℙ² the complement of [0 : 0 : 1] is {x₀ ≠ 0} ∪ {x₁ ≠ 0}; three Mayer–Vietoris steps (the port's TopCat.Sheaf.subsingleton_H'_sup and subsingleton_H'_bot) over pieces that are star-convex in the chart x₀ ≠ 0 (contractible-open-acyclic) give H³ = 0. This replaces the retraction onto a line of the earlier note, since the ladder compares Sheaf.H' with singular cohomology only on contractible opens. Red team: docs/sketches/p2-point-class-nonzero.redteam.md."
   - Roadmap row 142: status `checked`, module named.
2. **`depends_on` (required).** Add `contractible-open-acyclic` (used for every piece) and `lefschetz-port` (the Mayer–Vietoris lemmas live in the port), next to `p2-lines-transversal` and `forget-support-exact`. `projective-line-class-nonzero` lists `contractible-open-acyclic` the same way.
3. **Module docstring (recommended).** "the pin has no homotopy invariance of sheaf cohomology" is broader than what was checked. Replace with: "the ladder compares `Sheaf.H'` with singular cohomology only on contractible opens (`contractible-open-acyclic`), so the planned deformation retraction of `U` onto a line is replaced by three Mayer–Vietoris steps". The same wording fits the sketch's "Route chosen" paragraph.
4. **All codimensions (recommended; a stronger statement, not a weakening).** The criterion holds in every positive codimension with the same proof, and the two existing criteria are its cases p = 0 and p = 1 (RT-B3, standard axioms). `p1p1-point-class-nonzero` and any later point or curve test can then cite one lemma. Suggested in `ClassNonzero.lean` or in this file, keeping both existing names:

```lean
/-- The class of a point of coheight `p + 1` is nonzero when the complement of its support has
no rational cohomology in degree `2 p + 1`. -/
theorem cycleComponentSheafClass_ne_zero_of_subsingleton_odd (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) (p : ℕ)
    (hx : coheight x = ((p + 1 : ℕ) : ℕ∞))
    (h : Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) (2 * p + 1) (cycleComponentAnalyticClosedSupport X x).compl)) :
    cycleComponentSheafClass X x hx ≠ 0 := by
  intro h0
  rw [cycleComponentSheafClass_eq_forgetSupport] at h0
  have hinj := forgetSupport_injective_of_subsingleton X (cycleComponentAnalyticClosedSupport X x)
    (2 * p + 1) h
  have hs : cycleComponentSupportedInjectiveClass X x hx = 0 :=
    hinj (h0.trans (map_zero _).symm)
  apply cycleComponentSmoothSupportCoclassSection_ne_zero X x hx
  rw [← cycleComponentSupportedInjectiveClass_normalization X x hx, hs]
  exact AddEquiv.map_zero _
```

   with `cycleComponentSheafClass_ne_zero_of_subsingleton_three X x hx h := cycleComponentSheafClass_ne_zero_of_subsingleton_odd X x 1 hx h` (elaborates as written: `↑2` meets `↑(1 + 1)` and `3` meets `2 * 1 + 1` by evaluation).

## What was tried and failed

- Trivial proofs of the rung (`simp`, unfolding plus `simp`), the codimension-one criterion at the point, and `infer_instance` for the H³ vanishing: all fail as recorded in section 3.
- A shortcut through `maximalCodimensionBorelMooreFundamentalClass_ne_zero`: the class is local (Borel–Moore homology of the cycle), no map to H⁴(ℙ²) at the pin.
- A name-clash scan of the 22 new names against `HodgeLadder/` and `port/`: no clash, so the root import of change 1 adds no duplicate declaration.
