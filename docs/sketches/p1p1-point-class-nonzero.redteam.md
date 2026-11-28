# Red team: `p1p1-point-class-nonzero` (statement and proof)

Date: 2026-11-27. Worktree `p1p1-point-class-nonzero`, branch `track/p1p1-point-class-nonzero`, candidate commit `a5d8497` (one file, `HodgeLadder/Tests/P1p1PointClassNonzero.lean`, 479 lines) on base `a568e7b`. Pin: `Paul-Lez/HodgeConjecture@2ead713` (package `rev-parse HEAD`, `lakefile.toml` and `lake-manifest.json` agree), Lean and Mathlib `v4.35.0-rc4`. `main` is at `d41e05d`, one commit ahead of the base; that commit touches only the de Rham cup files and text (ledger, gaps, roadmap, conventions), none in this module's import closure.

Targets: `p1p1_point_class_ne_zero`, `p1p1Fibres_cup_ne_zero`, `subsingleton_H'_three_compl_p1p1Corner`, `subsingleton_H'_two_chartPreOpen_coord_ne_zero`, the cover lemmas `p1p1Corner_support_compl`, `p1p1StdOpen_inf_one_zero`, `p1p1StdOpen_sup_inf_zero_one`, the chart lemmas (`mem_projectiveChart_source_iff_underlying`, `mem_projectiveChart_source_iff_coord`, `exists_mem_projectiveChart_source`, `mem_projectiveChart_one_source_iff`), `chartPreOpen` and its lattice lemmas, `contractibleSpace_chartPreOpen`, the four `coord*` sets, `coordProj`, `p1p1StdChart`, `p1p1StdOpen`, `p1p1Const` and their lemmas.

Read: the candidate; `HodgeLadder/Tests/ProjectivePlanePoint.lean` and `docs/sketches/p2-point-class-nonzero.redteam.md`; `HodgeLadder/Tests/P1p1Fibres.lean` (`inftyPoint`, `lineChart`, `p1p1CornerPoint`, `p1p1Corner`, `coheight_p1p1Corner`, `coheight_p1p1Corner_add`, `p1p1Corner_support_eq_singleton`); `HodgeLadder/Tests/CycleClassMultiplicativeP1p1.lean`; the port's `Oka/Topology/Sheaves/Cohomology/Dimension.lean` (`subsingleton_H'_sup` at lines 67 to 71); `HodgeLadder/Tests/ContractibleAcyclic.lean` (`contractibleOpen_subsingleton_H'`); upstream `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean` (`cycleComponentSheafClass` at line 88); `docs/sketches/cycle-class-multiplicative.md` (rung table, line 181); `docs/sketches/p1p1-fibres-transversal.redteam.md`; `docs/conventions.md`; `docs/gaps.md`; issue #219.

Scratch files (under the worktree, removed before the commit). The module has a current `.olean` (`lake build HodgeLadder.Tests.P1p1PointClassNonzero`: rebuilt in 9.7 s, no warning from the file), so every probe imports it.

| File | What | Result |
|---|---|---|
| RT-A | `#print axioms` of the rung, the corollary, the H³ and H² lemmas, the cover and chart lemmas, the contractibility lemmas and three set lemmas (19 declarations) | every one prints `[propext, Classical.choice, Quot.sound]` |
| RT-B | the elaborated statement; the same class with `coheight_p1p1Corner`; the `rfl` unfolding to `forgetSupport`; `p1p1Fibres_cup_ne_zero` paired with `p1p1Fibres_cup_eq_p1p1Corner` on identical terms; `p1p1Corner`, `inftyPoint`, `lineChart` by `rfl` | all compile (finding 1) |
| RT-C | trivial proofs and wrong-degree applications (C1 to C7) | all fail, except `exact?`, which finds the rung itself (finding 3) |
| RT-D | lines 59 to 95 and 118 to 320 of the file (the general lemmas) over `import HodgeLadder.Tests.ProjectivePlanePoint` alone, plus the ℙ² H² step rederived from the general lemma | compiles, 9.6 s (recommended change R1) |

`python3 tools/check.py --no-build` in the worktree, scratch removed: `ACCEPTED: all checks passed`. The module is neither imported by `HodgeLadder.lean` nor named by the ledger, so that run does not cover it; RT-A is the axiom evidence until required change 1 lands.

**Verdict: pass with changes.** The statement is upstream's class of the closed point (∞, ∞) in H⁴, exactly the right side of the checked identity `p1p1Fibres_cup_eq_p1p1Corner`, and the corollary is literally that identity's left side. The cover of the complement by three product charts is right, both Mayer–Vietoris steps are in the right degrees, the generalized H² lemma is the ℙ² argument with the coordinate made a parameter, and every hypothesis is used. No sign, orientation or scalar can change the truth of a nonvanishing. Nothing other than Mathlib's conventions enters, and no −1 appears. Changes: ledger, root import, roadmap, the note of `cycle-class-multiplicative-p1p1`, `depends_on`, gaps rows and conventions text (required, exact text below; a rebase on `main` first); a split of the general lemmas into a low-layer module and a `coheight_p1p1Corner` form (recommended).

## Findings

### 1. The statement against the literature

Literature: for X smooth projective over ℂ of complex dimension n and a closed point P, the cycle class [P] spans H^{2n}(X; ℚ) ≅ ℚ; on ℙ¹ × ℙ¹ (n = 2) the Künneth decomposition gives H⁴ = H²(ℙ¹) ⊗ H²(ℙ¹), spanned by pr₁*[pt] ∪ pr₂*[pt], which is the class of a point [`Hatcher2002` §3.2, cross product and Künneth formula; `Fulton1998` ch. 19 for the cycle map; section and chapter numbering unverified]. The rung asks for the nonvanishing half.

| Literature object | Lean | Comparison |
|---|---|---|
| H⁴((ℙ¹ × ℙ¹)(ℂ); ℚ) | `H^(2 * p)(p1p1; ℚ)` with `p` elaborated as `(fun x1 x2 => x1 + x2) 1 1` (RT-B `#check`), the upstream sheaf cohomology of the constant sheaf ℚ on `TopCat.of (ComplexPoint p1p1)` | definitionally 2 · 2 = 4; RT-B accepts `cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner ≠ 0` (degree `2 * 2`) by the rung's own proof term |
| the point (∞, ∞), ∞ = [1 : 0] | `p1p1Corner = p1p1CornerPoint.underlying`, `p1p1CornerPoint = prod.lift inftyPoint inftyPoint`, `inftyPoint = lineChart.symm 0`, `lineChart = projectiveChart 1 0` (all `rfl` in RT-B) | the checked `p1p1-fibres-transversal` fixes these; its red team confirmed ∞ = [1 : 0] and coheight 2 = codimension |
| [P] | upstream `cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner_add`, which is `forgetSupport ℚ p1p1 (cycleComponentAnalyticClosedSupport …) (2 * 2) (cycleComponentSupportedInjectiveClass …)` by `rfl` (RT-B) | the upstream definition of record (`FundamentalClass.lean:88`), no local restatement |
| [P] ≠ 0 | `≠ 0` | exact |
| [{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] ≠ 0 | `p1p1Fibres_cup_ne_zero` | RT-B builds `⟨p1p1Fibres_cup_ne_zero, p1p1Fibres_cup_eq_p1p1Corner⟩` against one written-out left side, so the corollary's term is the identity's left side with the same factor order ({∞} × ℙ¹ first), the same degree proof `(by ring)` and the same coheight proofs |

The odd form `(fun x1 x2 => x1 + x2) 1 1` for p comes from unifying `↑?p` with `↑1 + ↑1` through `ℕ∞`'s addition; it is inherited from the checked `coheight_p1p1Corner_add` and the identity, and the rung must keep it to match that identity syntactically. It is harmless (RT-B, second example); R2 records the `2 * 2` reading as a checked `example`.

Issue #219 states "The class of the point (∞, ∞) is nonzero in H⁴(ℙ¹ × ℙ¹; ℚ)"; the Lean is that statement.

### 2. Hypotheses can be satisfied

The rung has no hypotheses. The criterion `cycleComponentSheafClass_ne_zero_of_subsingleton_odd` (from `p2-point-class-nonzero`) is applied at `X = p1p1`, whose `IsIntegral`, `Smooth` and `IsProjective` instances come from `p1p1-witness`, with p = 1, `hx := coheight_p1p1Corner_add` and the H³ vanishing that the file proves. `contractibleSpace_chartPreOpen` needs a nonempty star-convex set and a chart with target everything; each use supplies an explicit center inside the set (`fun _ => 1`, `-1`, `I`, `-I`, `0`) and `p1p1StdChart_target`. `subsingleton_H'_two_chartPreOpen_coord_ne_zero` takes `k : Fin n`, so n ≥ 1 is forced by the type; it is used at n = 2, k = 1 and k = 0.

### 3. Trivial truth

- Nothing unfolds to `True`. `simp` leaves `¬cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner_add = 0` (C1). Unfolding leaves `forgetSupport ℚ p1p1 … 4 (cycleComponentSupportedInjectiveClass …) = 0 ⊢ False` (C2). `exact?` (C3) returns `p1p1_point_class_ne_zero`, the rung itself, and nothing shorter.
- `infer_instance` on `Subsingleton (Sheaf.H' p1p1Const 3 (…).compl)` fails (C4): the H³ vanishing is computed.
- The degree bookkeeping is live. The criterion at p = 0 with an H¹ hypothesis fails to typecheck against `coheight_p1p1Corner_add` (C5). The criterion at p = 1 with an H² hypothesis fails (C6): it demands degree 3. This matters on ℙ¹ × ℙ¹, where H² of the complement is ℚ² (the complement retracts onto the 2-skeleton S² ∨ S²), so an off-by-one would have asked for a false input.
- The machinery cannot reach false statements by accident. Trying H² of {x₁ ≠ 0} × ℙ¹ by the same Mayer–Vietoris step at q = 1 asks for H¹ of the intersection ℂ* × ℂ, which is ℚ; passing the H² lemma there fails to typecheck (C7).
- Every hypothesis is used: the H³ vanishing feeds `forgetSupport_injective_of_subsingleton` inside the criterion; the `ContractibleSpace` instances feed `contractibleOpen_subsingleton_H'`; the cover and intersection lemmas feed each `rw`.
- Nonvanishing reaches the class only through upstream's `cycleComponentSmoothSupportCoclassSection_ne_zero` and the normalization isomorphism, as on ℙ². A degenerate `Sheaf.H'` that vanished everywhere would make the H³ input free, yet the conclusion would stay true and nonvacuous, since it is about upstream's global class and upstream's `forgetSupport` (same argument as finding 3 of the ℙ² red team).
- No `ℕ∞` trap: `coheight_p1p1Corner_add` is derived from `coheight_p1p1Corner : coheight p1p1Corner = ↑2`, which `p1p1-fibres-transversal` proves from the chain (∞, ∞) < fibre < ⊤ and upstream's `coheight_le_complex` at d = 2.

### 4. Interface axioms

Not an interface rung. No structure, no `Prop` input; every cited input is a checked declaration of this ladder, the port, Mathlib or upstream.

### 5. Axioms and declarations

RT-A: `[propext, Classical.choice, Quot.sound]` for all 19 declarations probed (the rung, the corollary, both cohomology lemmas, the three cover lemmas, the four chart lemmas, both contractibility lemmas, `eq_p1p1CornerPoint_iff`, `mem_p1p1StdOpen_iff`, `p1p1StdChart_target`, three `coord*` set lemmas). The file contains no `sorry`, `native_decide`, `axiom`, `unsafe` or heartbeat override. A word-match scan of all 45 declared names of the file over `HodgeLadder/` and `port/` finds no clash, so the root import of change 1 adds no duplicate. The ledger names nothing yet; change 1 lists the declarations.

### 6. The Mayer–Vietoris computation, checked by hand

`subsingleton_H'_sup` at q (port, `Dimension.lean:67`): H^q(A ⊓ B) = 0, H^{q+1}(A) = 0, H^{q+1}(B) = 0 give H^{q+1}(A ⊔ B) = 0. Write U₀ = {x₀ ≠ 0}, U₁ = {x₁ ≠ 0} on ℙ¹, so U₁ = ℙ¹ ∖ {∞} (`mem_projectiveChart_one_source_iff`, proved through `lineChart` and `underlying_eq_infty_iff`).

| Step | q | A ∪ B | A, B | A ∩ B | input |
|---|---|---|---|---|---|
| outer | 2 | U = (U₁ × U₀ ∪ U₁ × U₁) ∪ U₀ × U₁ | U₁ × ℙ¹; U₀ × U₁ ≅ ℂ² | (U₀ ∩ U₁) × U₁ = {v₀ ≠ 0} in chart (0, 1), ≅ ℂ* × ℂ | H³(U₁ × ℙ¹) = 0 (next row), H² of ℂ* × ℂ |
| inner | 2 | U₁ × ℙ¹ | U₁ × U₀, U₁ × U₁, each ≅ ℂ² | U₁ × (U₀ ∩ U₁) = {v₁ ≠ 0} in chart (1, 0), ≅ ℂ × ℂ* | H² of ℂ × ℂ* |
| H² lemma | 1 | {v_k ≠ 0} | v_k ∈ ℂ ∖ (−∞, 0] about 1; −v_k ∈ ℂ ∖ (−∞, 0] about −1 | {Im v_k ≠ 0} | H¹ of two half-spaces |
| H² lemma | 0 | {Im v_k ≠ 0} | Im v_k > 0 about I; Im v_k < 0 about −I | ∅ | H⁰(∅) = 0 (`subsingleton_H'_bot`) |

Each row checks.

- **Cover.** z ≠ (∞, ∞) iff some projection differs from ∞. If pr₁ z ≠ ∞ then z ∈ U₁ × ℙ¹ = U₁ × U₀ ∪ U₁ × U₁. Otherwise pr₂ z ≠ ∞ and pr₁ z = ∞ ∈ U₀, so z ∈ U₀ × U₁. Conversely (∞, ∞) lies in none of the three. The Lean proof is the case split over `exists_mem_projectiveChart_source` and `mem_projectiveChart_one_source_iff`, with `p1p1Corner_support_eq_singleton` for the support.
- **Intersections.** Chart (i, j) is `prodChart` of `projectiveChart 1 i` and `projectiveChart 1 j`, first factor first (`p1p1StdChart_apply_zero`, `_one`). In chart 0 of ℙ¹ the coordinate is x₁ / x₀, nonzero exactly on U₁ (`mem_projectiveChart_source_iff_coord 1 0 1`, which unfolds `Fin.insertNth 0 1 v` at index 1 to `v 0`). So U₁ × U₀ ∩ U₁ × U₁ is {v₁ ≠ 0} in chart (1, 0), and (U₁ × ℙ¹) ∩ U₀ × U₁ is {v₀ ≠ 0} in chart (0, 1). The intermediate union is used as `p1p1StdOpen 1 0 ⊔ p1p1StdOpen 1 1` throughout, so no identification of it with U₁ × ℙ¹ is needed in Lean.
- **Pieces.** Each chart has target `Set.univ` (`p1p1StdChart_target` from `affineChart_target`), so `chartPreOpen φ S` is homeomorphic to S, and S is star-convex with a center in S. The slit and half-space sets constrain one coordinate and leave the rest free, as on ℙ²; union and intersection identities (`coordSlitPos_union_coordSlitNeg`, `coordSlitPos_inter_coordSlitNeg`, `coordHalfPos_inter_coordHalfNeg`) are the ℙ² ones with `0` replaced by `k`.
- **Topology.** The answer agrees with the homotopy types: U ≃ S² ∨ S² (H³ = 0), U₁ × ℙ¹ ≃ S² (H³ = 0), ℂ* × ℂ ≃ S¹ (H² = 0). No finiteness is hidden: the cover is three explicit opens and the induction is unrolled by hand.
- **Analytic topology.** Contractibility is taken in the subspace topology of `TopCat.of (ComplexPoint p1p1)`, the space the constant sheaf lives on; `prodChart` is an `OpenPartialHomeomorph` for that topology (rung `complex-points-prod`).
- `contractibleOpen_subsingleton_H'` derives paracompactness, Hausdorffness and a contractible basis from `p1p1` smooth projective; its only instance argument is `[ContractibleSpace U]`.

### 7. Conventions

| Convention | Used where | Truth depends on it? | Row |
|---|---|---|---|
| Fundamental-class normalization | inside the criterion (`cycleComponentSmoothSupportCoclassSection_ne_zero`, normalization isomorphism) | no: any nonzero scalar or sign keeps the class nonzero | "Fundamental-class normalization", present |
| Coheight as codimension | `coheight_p1p1Corner_add`, the degree 2 · (1 + 1) | yes for the degree (read as height, the point would sit in H⁰); fixed and tested by `p1p1-fibres-transversal` | "Cycle components", present |
| ∞ = [1 : 0] and the chart x₁ ≠ 0 of ℙ¹ is ℙ¹ ∖ {∞} | `mem_projectiveChart_one_source_iff`, the cover | no for the truth (any closed point gives the same statement); the cover lemmas are proved from `projectiveChart_symm_mem_U_iff`, so a misreading would fail to compile | "Point ∞ of ℙ¹ …" and "Algebraic affine chart …", present; change 6 adds the facts used here |
| Standard chart coordinates of ℙⁿ, any n: chart i, coordinate m is x_{i.succAbove m} / xᵢ | `mem_projectiveChart_source_iff_coord`, `exists_mem_projectiveChart_source` | no: vanishing of H³ is invariant under coordinate order | "Algebraic affine chart …", present; change 6 extends it to general n |
| Product charts first factor first | `p1p1StdChart`, `p1p1StdChart_apply_zero`, `_one` | no for this rung (a swap exchanges the two intersections, both ℂ* × ℂ) | "Complex points of a product …", present; change 6 adds the rung |
| Mayer–Vietoris and `Sheaf.H'` of an open | `subsingleton_H'_sup` at q = 2, 2 and, inside the H² lemma, 1, 0; `subsingleton_H'_bot` | no: vanishing only, the connecting map's sign is irrelevant | "Cohomology of an open, Mayer–Vietoris, analytic topology", present; change 6 adds the rung |

Sign: none enters, and no convention other than Mathlib's is forced; nothing in the file is a −1. Koszul signs (−1)^p do not arise: the proof uses no product. The corollary inherits the identity's sign + without using it, since `≠ 0` is insensitive to sign. Cited inputs: the criterion (from `p2-point-class-nonzero`) is stated against upstream's `cycleComponentSheafClass` and `Sheaf.H'` of the same constant sheaf `(TopCat.Sheaf.constantFunctor …).obj (AddCommGrpCat.of ℚ)` that `p1p1Const` abbreviates, so the spellings match by `abbrev`.

### 8. Equality first

Not an identity. It is the nonvanishing input that makes the checked identity `cycle-class-multiplicative-p1p1` ([{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)], exact, sign +) non-vacuous, and an input of the open `cup-positive-degree-test` (pr₁*[∞] ∪ pr₂*[∞] ≠ 0), which still needs `fibre-class-pullback` and `cup-pullback`. Before this rung, that identity held as 0 = 0 in every model where upstream's H⁴ class vanished, and it held for the square-zero product; with both sides now nonzero, it excludes both on ℙ¹ × ℙ¹. What it still does not test: the sign + against an independent number. ℙ² has `planeDegree` (rung `cycle-class-sign-test-p2`); ℙ¹ × ℙ¹ has no degree map on H⁴ at the pin. That is a different, stronger statement and would be a new rung (it would also need H⁴ of the complement to vanish, which this file does not prove); this verdict does not require it.

### 9. Non-vacuity

The rung is itself the non-vacuity witness for `cycle-class-multiplicative-p1p1`. The smallest test that would fail if the H³ input were free for a degenerate reason is a positive-degree nonvanishing of `Sheaf.H'` on ℙ¹ × ℙ¹, for instance `Nontrivial (Sheaf.H' p1p1Const 1 (chartPreOpen (p1p1StdChart 1 0) {v | v 1 ≠ 0} (isOpen_coord_ne_zero 1)))` (H¹ of ℂ × ℂ* is ℚ) or `Nontrivial (Sheaf.H' p1p1Const 2 (cycleComponentAnalyticClosedSupport p1p1 p1p1Corner).compl)` (ℚ²). Neither exists: a grep for `Nontrivial (Sheaf.H'` and `¬Subsingleton (Sheaf.H'` over `HodgeLadder/` and `port/` returns nothing. As on ℙ², its absence does not affect this rung (finding 3, sixth item); it would matter for a rung that claims a group is nonzero by computing it.

### 10. Pin drift

Checked against the current pin `2ead713`; base `a568e7b` and `main` `d41e05d` have the same `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`. No drift. Upstream and Mathlib declarations this rung depends on, for the next bump (in addition to the ℙ² list in `p2-point-class-nonzero.redteam.md` section 8): `AlgebraicGeometry.ProjectiveSpace.iSup_U`, `ProjectiveSpace.U`, `Scheme.Hom.apply_mem_image_iff`, `Point.underlying_map`, `openEquiv`, `OpenPartialHomeomorph.isOpen_inter_preimage`, `Complex.slitPlane`, `Complex.mem_slitPlane_iff`, `convex_halfSpace_im_gt`, `convex_halfSpace_im_lt`, `StarConvex.linear_preimage`; this ladder's `prodChart`, `prodChart_source`, `prodChart_target`, `prodChart_apply`, `eq_prodLift`, `projectiveChart_symm_mem_U_iff`, `projectiveChartOpen_eq`, `affineChart_source`, `affineChart_target`. Mathlib at the pin has no `Opens` bundling of `φ.source ∩ φ ⁻¹' S` and no lemma that `slitPlane ∪ −slitPlane = {z ≠ 0}` (grep of `Mathlib/Topology/OpenPartialHomeomorph/` and of every `slitPlane` use), so the local copies are justified; `pinwalk.py --clash` should be rerun on them at the next bump (change 5).

### 11. Path and module layout

Keep `HodgeLadder/Tests/P1p1PointClassNonzero.lean`. `tools/next.py` prints `HodgeLadder/P1p1/Point/Class/Nonzero.lean` because the ledger's `module` is null and the default is derived from the id; every analogue (`ProjectivePlanePoint`, `P1p1Fibres`, `CycleClassMultiplicativeP1p1`) lives in `HodgeLadder/Tests/`, and the ledger `module` field set by change 1 removes the mismatch.

The module sits at layer 28 (`python3 tools/pinwalk.py --hubs`), because it imports `CycleClassMultiplicativeP1p1` (layer 27) for the corollary alone. The general lemmas need only `ProjectivePlanePoint` (layer 9): RT-D compiles them over that single import. Left in place, any later user of `subsingleton_H'_two_chartPreOpen_coord_ne_zero` or the ℙⁿ chart lemmas imports the transversal cup stack. R1 moves them.

The ℙ² proof duplicates the generalized lemmas: `planeChartZeroOpen S hS` is `chartPreOpen (projectiveChart 2 0) S hS` by `rfl`, `mem_projectiveChart_source_iff` is `mem_projectiveChart_source_iff_underlying 2` by `rfl`, and the H² step of `subsingleton_H'_three_compl_planeOrigin` follows from `subsingleton_H'_two_chartPreOpen_coord_ne_zero projectivePlane (projectiveChart 2 0) _ 0` after `rw [planeChartOpen_zero_inf_one]` (RT-D). Pointing the ℙ² proof at the new lemmas would mean editing `ProjectivePlanePoint`, which has 9 downstream modules, or making it import a higher module. Leave it; record the duplication in gaps (change 5) and, if R1 is taken, put the rederivation in the new module as an `example` so a later consolidation has a checked bridge.

## Required changes

1. **Rebase, root import, ledger.** Rebase `track/p1p1-point-class-nonzero` on `main` (`d41e05d`) before editing the ledger, gaps, roadmap or conventions, which that commit changed. Add `public import HodgeLadder.Tests.P1p1PointClassNonzero` to `HodgeLadder.lean` directly after `public import HodgeLadder.Tests.CycleClassMultiplicativeP1p1`. Ledger entry `p1p1-point-class-nonzero`:
   - `status`: `checked`; `module`: `HodgeLadder.Tests.P1p1PointClassNonzero`; `contributors`: `claude-code`;
   - `declarations`: `HodgeLadder.Tests.p1p1_point_class_ne_zero`, `HodgeLadder.Tests.p1p1Fibres_cup_ne_zero`, `HodgeLadder.Tests.subsingleton_H'_three_compl_p1p1Corner`, `HodgeLadder.Tests.subsingleton_H'_two_chartPreOpen_coord_ne_zero`, `HodgeLadder.Tests.p1p1Corner_support_compl`, `HodgeLadder.Tests.p1p1StdOpen_inf_one_zero`, `HodgeLadder.Tests.p1p1StdOpen_sup_inf_zero_one`, `HodgeLadder.Tests.mem_projectiveChart_source_iff_underlying`, `HodgeLadder.Tests.mem_projectiveChart_source_iff_coord`, `HodgeLadder.Tests.exists_mem_projectiveChart_source`, `HodgeLadder.Tests.mem_projectiveChart_one_source_iff`, `HodgeLadder.Tests.contractibleSpace_chartPreOpen`, `HodgeLadder.Tests.contractibleSpace_p1p1StdOpen`, `HodgeLadder.Tests.p1p1StdChart_target`, `HodgeLadder.Tests.eq_p1p1CornerPoint_iff`;
   - `note`: "Checked 2026-11-27. p1p1_point_class_ne_zero: cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner_add ≠ 0 in H⁴(ℙ¹ × ℙ¹; ℚ), ∞ = [1 : 0], by cycleComponentSheafClass_ne_zero_of_subsingleton_odd at p = 1 (p2-point-class-nonzero; forget-support-exact at n = 3) from H³((ℙ¹ × ℙ¹)(ℂ) ∖ (∞, ∞); ℚ) = 0 (subsingleton_H'_three_compl_p1p1Corner). The complement is the union of the product charts {x₁ ≠ 0} × {x₀ ≠ 0}, {x₁ ≠ 0} × {x₁ ≠ 0} and {x₀ ≠ 0} × {x₁ ≠ 0} (p1p1StdChart, each onto ℂ²); two Mayer–Vietoris steps at q = 2 (the port's TopCat.Sheaf.subsingleton_H'_sup) reduce H³ to H² of {v₁ ≠ 0} in the first chart and {v₀ ≠ 0} in the third, copies of ℂ* × ℂ, which vanishes by subsingleton_H'_two_chartPreOpen_coord_ne_zero (any chart onto ℂⁿ, any coordinate: slit pieces, then half-spaces, q = 1, 0); every piece is star-convex in a chart (contractible-open-acyclic). p1p1Fibres_cup_ne_zero: the left side of p1p1Fibres_cup_eq_p1p1Corner is nonzero, so cycle-class-multiplicative-p1p1 is a non-vacuous identity. A nonvanishing: no sign or scalar enters. Red team: docs/sketches/p1p1-point-class-nonzero.redteam.md."
   - Bump the ledger `updated` date if it is not already 2026-11-27.
2. **`depends_on` (required).** Set to `p1p1-fibres-transversal`, `forget-support-exact`, `cycle-class-multiplicative-p1p1` (the corollary), `p2-point-class-nonzero` (the criterion and `contractibleSpace_of_starConvex_image`), `contractible-open-acyclic` (every piece), `lefschetz-port` (the Mayer–Vietoris lemmas), `complex-points-prod` (`prodChart`), `affine-chart-analytic` (`projectiveChart`, `affineChart_target`). All eight ids exist; none depends on this rung, so no cycle.
3. **Note of `cycle-class-multiplicative-p1p1` (required).** In its ledger note, replace the sentence "The identity holds for [(∞, ∞)] = 0 as well; it becomes a non-vacuous test once p1p1-point-class-nonzero is checked." with: "Non-vacuous since p1p1-point-class-nonzero (checked 2026-11-27): [(∞, ∞)] ≠ 0 (p1p1_point_class_ne_zero), so both sides are nonzero (p1p1Fibres_cup_ne_zero) and the identity excludes the square-zero product on ℙ¹ × ℙ¹ in degrees (2, 2). The sign + is fixed against upstream's normalization alone: ℙ¹ × ℙ¹ has no degree map on H⁴ at the pin (ℙ² has planeDegree, cycle-class-sign-test-p2)." In `docs/roadmap.md` row `cycle-class-multiplicative-p1p1`, replace "a non-vacuous test once `p1p1-point-class-nonzero` is checked" with "non-vacuous: both sides nonzero by `p1p1-point-class-nonzero`".
4. **Roadmap row (required).** Replace the `p1p1-point-class-nonzero` row of `docs/roadmap.md` with:
   `| \`p1p1-point-class-nonzero\` | test | checked | \`p1p1-fibres-transversal\`, \`forget-support-exact\`, \`cycle-class-multiplicative-p1p1\`, \`p2-point-class-nonzero\`, \`contractible-open-acyclic\`, \`lefschetz-port\`, \`complex-points-prod\`, \`affine-chart-analytic\` | [(∞, ∞)] ≠ 0 in H⁴(ℙ¹ × ℙ¹; ℚ), and [{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] ≠ 0: H³ of the complement vanishes by two Mayer–Vietoris steps over three product charts and the generalized H² lemma for ℂ* × ℂ; \`HodgeLadder.Tests.P1p1PointClassNonzero\`; \`docs/sketches/p1p1-point-class-nonzero.redteam.md\` |`
5. **Gaps rows (required).** In `docs/gaps.md`, "General lemmas kept local". Layer 28 is the module's value from `python3 tools/pinwalk.py --hubs` on 2026-11-27; if R1 is taken, use the new module name and rerun pinwalk for its layer (10 expected: one above `ProjectivePlanePoint`).
   - Under "Manifolds, charts and analytic functions", after the `ProductChart` row:
     `| \`HodgeLadder.Tests.mem_projectiveChart_source_iff_underlying\`, \`mem_projectiveChart_source_iff_coord\` (a point of the chart xᵢ ≠ 0 of ℙⁿ lies in xⱼ ≠ 0 iff coordinate j of \`Fin.insertNth i 1 (φᵢ z)\` is nonzero), \`exists_mem_projectiveChart_source\` (the standard charts cover ℙⁿ(ℂ)), \`chartPreOpen\` with \`chartPreOpen_inf\`, \`_sup\`, \`_empty\`, \`_congr\` (the open φ.source ∩ φ⁻¹(S) of a partial homeomorphism, bundled as \`Opens\`), \`contractibleSpace_chartPreOpen\` (a nonempty star-convex open of the model space cuts out a contractible open when the target is everything) | \`HodgeLadder.Tests.P1p1PointClassNonzero\` | 28 | the any-n forms of the ℙ² chart lemmas (\`mem_projectiveChart_source_iff\`, \`mem_projectiveChart_source_iff_of_mem\`, \`planeChartZeroOpen\` and its lattice lemmas, \`contractibleSpace_planeChartZeroOpen\` in \`HodgeLadder.Tests.ProjectivePlanePoint\`, equal at n = 2 by \`rfl\`), which stay in place because that module has 9 downstream modules; Mathlib at the pin has \`OpenPartialHomeomorph.isOpen_inter_preimage\` and no \`Opens\` bundling; rung \`p1p1-point-class-nonzero\` | 2026-11-27 |`
   - Under "Topology", after the `irreducibleSpace_of_cover` row:
     `| \`HodgeLadder.Tests.coordSlitPos\`, \`coordSlitNeg\`, \`coordHalfPos\`, \`coordHalfNeg\`, \`coordProj\` with openness, star-convexity, \`coordSlitPos_union_coordSlitNeg\` ({v_k ∈ slitPlane} ∪ {−v_k ∈ slitPlane} = {v_k ≠ 0}), \`coordSlitPos_inter_coordSlitNeg\`, \`coordHalfPos_inter_coordHalfNeg\`; \`HodgeLadder.Tests.subsingleton_H'_two_chartPreOpen_coord_ne_zero\` (H² of {v_k ≠ 0} in a chart onto ℂⁿ vanishes, on smooth projective integral X) | \`HodgeLadder.Tests.P1p1PointClassNonzero\` | 28 | the coordinate-k forms of \`chartSlitPos\`, \`chartSlitNeg\`, \`chartHalfPos\`, \`chartHalfNeg\` and the H² step of \`subsingleton_H'_three_compl_planeOrigin\` (\`HodgeLadder.Tests.ProjectivePlanePoint\`), kept duplicated for the same reason; Mathlib at the pin has \`Complex.slitPlane\` and \`Complex.starConvex_one_slitPlane\` and no union lemma with its negative; rung \`p1p1-point-class-nonzero\` | 2026-11-27 |`
6. **Conventions text (required; the red team was read-only on this pass).** In `docs/conventions.md`:
   - Row "Algebraic affine chart and the standard chart of ℙⁿ", column "Results whose truth depends on it", append: "`p1p1-point-class-nonzero`: for every n, a point of chart i lies in xⱼ ≠ 0 iff coordinate j of `Fin.insertNth i 1 (φᵢ z)` is nonzero (`mem_projectiveChart_source_iff_coord`), and on ℙ¹ the chart x₁ ≠ 0 is ℙ¹ ∖ {∞} (`mem_projectiveChart_one_source_iff`); both proved from `projectiveChart_symm_mem_U_iff`, and the vanishing of H³ they feed is insensitive to coordinate order." In its status column append "; `p1p1-point-class-nonzero` (red team 2026-11-27)".
   - Row "Complex points of a product and product charts", same column, append: "`p1p1-point-class-nonzero`: `p1p1StdChart i j` = `prodChart` of `projectiveChart 1 i` and `projectiveChart 1 j`, coordinate 0 from the first factor; a factor swap exchanges the two intersections {v₀ ≠ 0} and {v₁ ≠ 0}, both ℂ* × ℂ, so the result does not depend on the order."
   - Row "Cohomology of an open, Mayer–Vietoris, analytic topology", same column, replace "`p2-point-class-nonzero` (H³ of ℙ²(ℂ) ∖ pt in three steps, degrees q = 2, 1, 0)" with "`p2-point-class-nonzero` (H³ of ℙ²(ℂ) ∖ pt in three steps, degrees q = 2, 1, 0); `p1p1-point-class-nonzero` (H³ of (ℙ¹ × ℙ¹)(ℂ) ∖ pt over three product charts, two steps at q = 2, then `subsingleton_H'_two_chartPreOpen_coord_ne_zero` at q = 1, 0)"; status column append "; `p1p1-point-class-nonzero` (red team 2026-11-27)".

## Recommended changes

- **R1. Split the general lemmas below the cup stack.** Move lines 59 to 95 (ℙⁿ chart lemmas) and 118 to 320 (`chartPreOpen` through `subsingleton_H'_two_chartPreOpen_coord_ne_zero`) to a new module `HodgeLadder/Tests/ChartCohomology.lean` with `public import HodgeLadder.Tests.ProjectivePlanePoint` as its only import, namespace `HodgeLadder.Tests`, and `public import HodgeLadder.Tests.ChartCohomology` in the rung file. RT-D compiles exactly this text. Add at its end, as a checked bridge to the ℙ² proof (compiles in RT-D):

```lean
/-- The `H²` step of `subsingleton_H'_three_compl_planeOrigin` is the case `n = 2`, `k = 0` of
`subsingleton_H'_two_chartPreOpen_coord_ne_zero` (`planeChartZeroOpen` is `chartPreOpen` of the
chart `x₀ ≠ 0` by `rfl`). -/
example : Subsingleton (Sheaf.H' planeConst 2 (planeChartOpen 0 ⊓ planeChartOpen 1)) := by
  rw [planeChartOpen_zero_inf_one]
  exact subsingleton_H'_two_chartPreOpen_coord_ne_zero projectivePlane (projectiveChart 2 0)
    (by rw [projectiveChart, affineChart_target]) 0
```

  The ledger `module` stays `HodgeLadder.Tests.P1p1PointClassNonzero` (the checker imports it and reaches the moved names); add `public import HodgeLadder.Tests.ChartCohomology` to `HodgeLadder.lean` before the rung's import, and use the new module name in the gaps rows of change 5.
- **R2. The `2 * 2` reading.** Add after `p1p1_point_class_ne_zero`:

```lean
/-- The rung with the coheight in the form `↑2`, in degree `2 * 2`. -/
example : cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner ≠ 0 :=
  p1p1_point_class_ne_zero
```

  (compiles in RT-B), so the degree is stated against `coheight_p1p1Corner` in the file and the odd elaborated `p` of finding 1 is pinned to 2.

## What was tried and failed

- Trivial proofs of the rung: `simp` (C1), unfolding plus `simp` (C2), `infer_instance` for the H³ vanishing (C4); all fail as recorded in finding 3. `exact?` returns only the rung itself.
- The criterion at the wrong codimension (p = 0 with H¹, C5) and at the wrong degree (p = 1 with H², C6): both fail to typecheck.
- H² of {x₁ ≠ 0} × ℙ¹ through the same Mayer–Vietoris step with the H² lemma in place of the missing H¹ input (C7): type mismatch, as it should be (that H² is ℚ, so a proof would signal an error).
- A shortcut through upstream's `maximalCodimensionBorelMooreFundamentalClass_ne_zero`, rechecked: it is about the Borel–Moore homology of the cycle, with no map to H⁴(ℙ¹ × ℙ¹) at the pin (as found for ℙ²).
- A Mathlib or upstream equivalent of `chartPreOpen`, of the slit-plane union, or of the any-n chart cover: none found (finding 10).
- A first form of the RT-D bridge with an underscore for the right side of `mem_projectiveChart_source_iff_underlying 2 i z` failed to elaborate (placeholder); the `rfl` comparison with `mem_projectiveChart_source_iff` compiles.
