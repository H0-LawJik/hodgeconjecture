# Red team: `p2-witness` (ℙ² over ℂ satisfies the hypotheses of the statements of record)

Date: 2026-11-26. Branch `track/p2-witness` at base `8b3a2fa`, uncommitted file `HodgeLadder/Tests/ProjectivePlane.lean` (two integrality bodies `sorry`) and the section "p2-witness: statement" of `docs/sketches/cycle-class-multiplicative.md`. The prover's sorry-free copy of the same file was read and rebuilt with probes. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Targets: `projectiveSpace`, `projectivePlane`, `projectivePlane_eq`, the instances `smoothOfRelativeDimension_projectiveSpace`, `smooth_projectiveSpace`, `isProjective_projectiveSpace`, `isIntegral_okaProjectiveSpace`, `isIntegral_projectiveSpace`, and `dim_projectiveSpace`, `projectivePlane_witness`, `projectivePlane_t2Space`, `projectivePlane_openParacompactSpace`, `okaIsoSpace`, `irreducibleSpace_of_cover`.

**Verdict: pass with changes.** The object is upstream's ℙ² in the spelling upstream itself uses, the four instances are honest, the relative dimension is exactly 2 and is the only one, and the integrality route is sound: a sorry-free copy with the probes below prints the three standard axioms for every target. The changes are small: docstrings on four helper declarations, two named lemmas for `okaIsoSpace`, and one wrong sentence in the sketch (findings 3, 5, 9).

## Method

Scratch file `RTScratchP2.lean` in the worktree (deleted afterwards): the prover's sorry-free copy with its `#print axioms` lines removed, three extra imports (`HodgeConjecture.Statement`, `HodgeConjecture.Variants`, `HodgeLadder.Cup.SupportedPair`), and the probes P1 to P9 below. It does not import `HodgeLadder.Tests.ProjectivePlane`, so instance search cannot reach the sorried instances of the worktree file (the trap the prover reported). `lake env lean RTScratchP2.lean`: 15 s wall, no errors.

| Probe | Statement | Result |
|---|---|---|
| P1 | `(h : HodgeConjecture) (p : ℕ) : Hdg^p(projectivePlane; ℚ) ≤ algebraicCycleClassSpan projectivePlane p := h projectivePlane p` | elaborates: every instance argument of the statement of record is found on the plane |
| P2 | `TopologicalSpace.dim projectivePlane.left = 2` | `dim_projectiveSpace 2` |
| P3 | `Nonempty projectivePlane.left` | `inferInstance` |
| P4 | `projectiveLine = projectiveSpace 1`; `SmoothOfRelativeDimension 1 (projectiveSpace 1).hom` | `rfl`; `inferInstance` |
| P5 | `dim projectivePlane.left ≠ dim projectiveLine.left` | rewrite by the two `dim_eq`, `decide` |
| P6 | `(d : ℕ) [SmoothOfRelativeDimension d projectivePlane.hom] : d = 2` | from upstream `SmoothOfRelativeDimension.dim_eq` and P2 |
| P7 | `(okaIsoSpace n).hom ≫ (projectiveSpace n).hom = ProjectiveSpace.toSpec n ℂ` | `(isPullback_projectiveSpace n).isoPullback_hom_fst` (first try `simp [okaIsoSpace, toBase]` left the goal open) |
| P8 | `(okaIsoSpace n).hom ≫ pullback.snd _ _ = ProjectiveSpace.map (n := n) intToComplex` | `isoPullback_hom_snd` (first try `simp [okaIsoSpace]` failed the same way) |
| P9 | with `projectivePlane_openParacompactSpace` as a local instance, `cup_singular_comparison projectivePlane x y` and `cup_singular_comparison_supported_pair projectivePlane Z α β` | both elaborate |
| axioms | `projectivePlane_witness`, `projectivePlane_openParacompactSpace`, `dim_projectiveSpace`, `okaIsoSpace`, `isIntegral_projectiveSpace`, `projectivePlane_t2Space`, `smoothOfRelativeDimension_projectiveSpace`, `isProjective_projectiveSpace` | `[propext, Classical.choice, Quot.sound]` for all eight |
| synth | `T2Space (ComplexPoint projectivePlane)` | `ComplexProjectiveSpace.instT2SpaceProjectiveSpaceComplexPoint 2` (upstream) |

## 1. Is this the statement the literature makes?

Source: upstream's docstring on `ProjectiveSpace` ("For `n = Fin (d+1)`, this is the usual `d`-dimensional projective space `ℙ^d_S`") and on `IsProjective` ("there exist a natural number `d` and a closed immersion `X → ℙ^d_T` whose composite with the projection to `T` is `f`"). That is the H-projective definition of `Stacks` (tag 01W8, tag unverified); over a field it agrees with the other standard definitions. The statement of record, `ClayDeligne`, asks for a nonsingular complex projective variety; upstream renders this as `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`.

| Literature | Lean | Comment |
|---|---|---|
| ℙ² over ℂ | `Over.mk (ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ))` | the base change to `Spec ℂ` of `Proj ULift ℤ[x₀, x₁, x₂]`, every variable in degree one. Same spelling as `projectiveLine` (with `Fin 2`) and as upstream's own Hausdorff instance (`Fin (n + 1)`), so upstream lemmas stated on that spelling fire (synth row above) |
| variety (integral) | `IsIntegral projectivePlane.left` | upstream's hypothesis, literally |
| nonsingular | `Smooth projectivePlane.hom`, with `SmoothOfRelativeDimension 2` | Mathlib's smoothness of the structure morphism; over ℂ this is nonsingularity |
| projective | `IsProjective projectivePlane.hom` | upstream's class |
| dimension 2 | `dim_projectiveSpace 2` | upstream's `TopologicalSpace.dim`, the dimension the charted space and the codimension bookkeeping use |

Field by field the plane is the object the statements of record quantify over: P1 specializes `HodgeConjecture` to it with no extra argument. `cycle-class-multiplicative-p2` and its inputs will bind the same four instances and `{d} [SmoothOfRelativeDimension d X.hom]` at d = 2 (P6 shows no other d is possible). Their coordinate lines live on this object: by P8 and the port's `map_preimage_U`, Oka's `U i = D₊(xᵢ)` on `ℙₒ(2; ℂ)` corresponds under `okaIsoSpace 2` to the same coordinate on upstream's object, so L₀ = {x₀ = 0} means the same thing on both sides.

`projectivePlane` and `projectiveSpace 2` are two reducible spellings of one term (`projectivePlane_eq` by `rfl`; `Fin 3` against `Fin (?n + 1)` unifies by Nat literal offset, as the instance search shows). Downstream statements should use one of them throughout; the sketch picks `projectivePlane`, which is fine.

## 2. Can the hypotheses be satisfied?

This rung is the satisfiability witness for ℙ²: `projectivePlane_witness` is the instance, checked with the standard axioms in the sorry-free copy. For every n the instances hold on `projectiveSpace n`; n = 0 is Spec ℂ again (dimension 0), consistent with the codimension-zero witness.

## 3. Is anything trivially true for an unrelated reason?

Attempts, all on the definitions:

- `IsProjective` by the identity presentation with `ambientDimension := n`. This is the intent of the definition: the identity of ℙⁿ_T is a closed immersion into ℙⁿ_T over T, which is how ℙⁿ is projective in every textbook. It is not a loophole because `Presentation` forces the ambient space to be `ℙ(Fin (d + 1); T)` and the map to be a closed immersion over T; upstream derives `IsProper` from it (`IsProjective.isProper`), so the class fails for 𝔸¹ or any non-proper scheme. The same presentation is used for ℙ¹ (checked rung `projective-line-witness`).
- The relative dimension. `smooth_terminal_space` composes `smoothOfRelativeDimension_toSpec n` (Oka's charts are `Spec R[Y₁, …, Yₙ]`, relative dimension n by Mathlib) with the isomorphism `Spec (ULift ℤ) ≅ ⊤` (relative dimension 0, written `n + 0`), then base-changes along `Spec ℂ ⟶ ⊤`; `pullback.fst (terminal.from S) (terminal.from Proj)` is indeed the base change of the second map. No offset: n + 1 homogeneous coordinates give relative dimension n. P6 shows 2 is the unique relative dimension on the plane, so a wrong number could not hide behind a second instance.
- `dim_projectiveSpace` is upstream's `SmoothOfRelativeDimension.dim_eq`, which needs `[IsIntegral X]`; in the worktree it resolves through the sorried instance, in the sorry-free copy through the proved one (axioms row).
- Integrality. The sorry-free copy proves `IsReduced ℙₒ(n; ℂ)` from the affine cover by `Spec ℂ[Y₁, …, Yₙ]`, irreducibility from `irreducibleSpace_of_cover` with U = `U n ℂ 0`, each `U n ℂ i` irreducible as the image of an irreducible spectrum, the point of chart 0 with all coordinates 1 in every `U i`, and the cover `iSup_U`. Every hypothesis of `irreducibleSpace_of_cover` is used; the lemma is true for an empty index type too (then X is empty and `hUi` is false). Transport is `isIntegral_of_isOpenImmersion (okaIsoSpace n).inv` with `Nonempty` supplied explicitly from `Classical.arbitrary ℙₒ(n; ℂ)`, whose `Nonempty` instance now comes from the proved `IrreducibleSpace`.
- No hypothesis is unused, no definition unfolds to `True`, no `ℕ∞` coercion is involved (`dim` is compared with a natural number cast, and P5 separates 2 from 1).

Conclusion: nothing here is vacuous.

## 4. Interface rung

Not applicable: no structure, no axioms (decision 0003).

## 5. Checker

`python3 tools/check.py --no-build` in the worktree rejects, as expected for the statement phase: the sorry scan flags `ProjectivePlane.lean:94` and `:114`, and the axioms step fails because the worktree build lacks `HodgeLadder.Normalization.ChartStep.olean` (a stale worktree build, unrelated to this rung). The axioms line for the eight targets was read from the scratch build instead (table above). The ledger entry has `declarations: []` and `module: null`; when the proof lands it should name at least `projectivePlane_witness`, `dim_projectiveSpace`, `isIntegral_projectiveSpace`, `okaIsoSpace`, `smooth_terminal_space`, `projectivePlane_openParacompactSpace`, and `irreducibleSpace_of_cover`, so that the checker prints axioms for the integrality chain explicitly.

## 6. Conventions

| Convention | Where | Depends on it | Register |
|---|---|---|---|
| ℙⁿ is `ProjectiveSpace (Fin (n + 1))`, variables in degree one, coefficients `ULift ℤ` | upstream `ProjectiveSpace` | the dimension count; which polynomial is "x₀" | new row "Projective space: coordinates, grading, dimension, projectivity" |
| relative dimension of a smooth morphism | Mathlib `SmoothOfRelativeDimension` (standard smooth presentations) | `dim = n`; the chart model `Fin (dim X.left) → ℂ` of upstream's charted space (ℂ² here) | same row |
| projective = H-projective | upstream `Presentation`, `IsProjective` | none for truth (over ℂ all definitions agree) | same row |
| `okaIsoSpace` direction and compatibility | `isPullback_projectiveSpace`, P7, P8 | identification of coordinate lines in `p2-lines-transversal` | same row |
| `ULift ℤ → ℂ` | `intToComplex` (from the ℙ¹ file) | none: it is the unique ring map | not needed |

No sign enters this rung. Nothing here is an equality of classes, so decision 0004's exactness requirement has nothing to bite on; the row exists so that the coordinate indexing used by `cycle-class-multiplicative-p2` (which line is L₀, which chart is x₂ ≠ 0) is fixed in one place.

## 7. Equality first

The rung is a test witness. It is a step toward the identity `cycle-class-multiplicative-p2` ([L₀] ∪ [L₁] = [pt], open) and the nonvanishing `cup-positive-degree-test-p2` (open); both rungs exist in the ledger.

## 7b. Non-vacuity

The smallest test that fails if the object were degenerate is `dim_projectiveSpace 2 : TopologicalSpace.dim projectivePlane.left = 2`, present in the file; an empty scheme or a point would give 0. P5 (plane differs from line) and P6 (unique relative dimension) are stronger and one line each; adding P6 as a named theorem would give downstream rungs the `obtain rfl` step of the cycle-class sketch (red team RT5, change I there) for free. Nonemptiness of the complex points, `Nonempty (ComplexPoint projectivePlane)`, is not in the file; `p2-lines-transversal` will need specific points, and upstream's `ComplexProjectiveSpace.vectorToComplexPoint` (`Lemmas/AlgebraicGeometry/ComplexPoint/Projective.lean:724`) supplies points of this object from nonzero vectors.

## 8. Pin drift

The rung is built at the current pin `2ead713`; there is no other commit to diff. Upstream declarations used, for the next drift check: `ProjectiveSpace`, `ProjectiveSpace.toBase`, `ProjectiveSpace.Presentation` (fields `ambientDimension`, `immersion`, `isClosedImmersion`, `immersion_toBase`), `AlgebraicGeometry.IsProjective`, `IsProjective.complexPoint_t2Space`, `ComplexProjectiveSpace.instT2SpaceProjectiveSpaceComplexPoint`, `ComplexPoint.openParacompactSpace`, `SmoothOfRelativeDimension.dim_eq`, `SmoothOfRelativeDimension.of_isIntegral` (an instance on the same goal shape; consistent by P6), `specULiftZIsTerminal`, and the statement `HodgeConjecture` (P1). From the port: `OkaProjectiveSpace` (`ℙₒ`), `ProjectiveSpace.toSpec`, `chart`, `U`, `affineOpenCover`, `iSup_U`, `opensRange_chart`, `chart_base_evalPoint_mem_U_iff`, `evalPoint`, `dehomogenizeVec`, `ProjectiveSpace.map`, `isPullback_map`, `map_preimage_U`. From Mathlib: `IsReduced.of_openCover`, `isIntegral_of_irreducibleSpace_of_isReduced`, `isIntegral_of_isOpenImmersion`, `subset_closure_inter_of_isPreirreducible_of_isOpen`, `IsPullback.isoPullback`.

## 9. Findings

1. The object is upstream's ℙ², spelled as upstream and the ℙ¹ witness spell it; the statement of record specializes to it with every instance found (P1). No change.
2. `IsProjective` by the identity presentation is the definition's intent and is not a loophole (section 3). No change.
3. `okaIsoSpace` is the right comparison: an isomorphism over `Spec ℂ` whose second projection is Oka's coefficient change, so standard opens and coordinate hyperplanes correspond (P7, P8). Change: add both facts as named lemmas, for example `okaIsoSpace_hom_toBase` and `okaIsoSpace_hom_snd`, one line each; `p2-lines-transversal` needs them to move the lines L₀, L₁ and the chart x₂ ≠ 0 from Oka's side to upstream's.
4. Relative dimension exactly 2 and `dim = n` are correct, and the relative dimension is unique (P6). Optional change: add P6 as a theorem.
5. Integrality is sound: with the sorried instances absent, all eight targets print the three standard axioms. Change: the helpers `chart_zero_inter_nonempty`, `isReduced_okaProjectiveSpace`, `isIrreducible_U_space`, `irreducibleSpace_okaProjectiveSpace` in the sorry-free copy have no docstrings; the project requires one on every public declaration.
6. `projectivePlane_t2Space` and `projectivePlane_openParacompactSpace` restate upstream (two T2 instances reach the goal, both propositions, no diamond). They are all the cup comparison needs: P9 elaborates `cup_singular_comparison` and `cup_singular_comparison_supported_pair` on the plane. No change.
7. The instances are consistent: they are propositions, the ℙ¹ instances are the n = 1 case (P4), and upstream's `SmoothOfRelativeDimension.of_isIntegral` agrees with them by P6. ℙ² is nonempty as a scheme (P3) and has dimension 2. Its complex points are not shown nonempty here; that belongs to `p2-lines-transversal` (section 7b).
8. Name check: `HodgeLadder.Tests.projectiveSpace` shares its short name with the port's `ComplexAnalytic.projectiveSpace` (GAGA). The two collide only in a file that opens both `ComplexAnalytic` and `HodgeLadder.Tests`; none does today. No change; worth a line in the module docstring if a GAGA consumer appears.
9. Sketch error: the section "p2-witness: statement" says "The ledger entry currently names `HodgeLadder/P2/Witness.lean`". The ledger has `"module": null` for `p2-witness`, and no file in `ledger/` or `docs/` names that path. Change: delete that sentence or replace it with "the ledger's `module` field is empty".
10. Ledger, when checked: set `module` to `HodgeLadder.Tests.ProjectivePlane` and list the integrality chain among the declarations (section 5), so `tools/check.py` prints axioms for `isIntegral_projectiveSpace` and `okaIsoSpace` by name as well as through `projectivePlane_witness`.

## What was tried and failed

- `simp [okaIsoSpace, _root_.ProjectiveSpace.toBase]` and `simp [okaIsoSpace]` for P7, P8: the goal stays as `isoPullback.hom ≫ pullback.fst … = toSpec n ℂ`; `IsPullback.isoPullback_hom_fst` and `isoPullback_hom_snd` close them.
- Searched upstream for an existing `IsProjective`, `Smooth` or `IsIntegral` instance on `ProjectiveSpace.toBase`: none at the pin, so the local instances do not duplicate upstream.
- Not attempted: a `Nonempty (ComplexPoint projectivePlane)` proof; building the worktree's missing `ChartStep` olean (out of scope, and the checker's axioms step would otherwise run on the sorried file).
