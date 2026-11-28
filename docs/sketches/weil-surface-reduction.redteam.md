# Red team: `weil-surface-reduction`

Date: 2026-11-28. Candidate: WIP commit `cb3d23c` on `track/weil-surface-reduction`, file `HodgeLadder/Weil/Surface/Reduction.lean` (module `HodgeLadder.Weil.Surface.Reduction`, namespace `HodgeLadder.Weil`, five declarations), root-imported from `HodgeLadder.lean`; ledger entry still `open`. Base `ab87174` (`main`); pin upstream `2ead713`, Lean and Mathlib `v4.35.0-rc4`; `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` identical on base and branch (`git diff ab87174..cb3d23c` touches only the new module and its root import).

Read: `python3 tools/next.py weil-surface-reduction`; ledger entries `weil-surface-reduction`, `weil-surface-rank`, `weil-space`, `weil-eigen-algebra`, `weil-elliptic-square`, `elliptic-square-cohomology`, `weil-surface`; plan `docs/notes/2026-11-27-t1-plan.md` §3 node B; decision 0013; red-team files `weil-surface-statement`, `weil-space`, `weil-eigen-algebra`, `de-rham-pullback`, `cup-hodge-filtration-checked`; `docs/conventions.md` rows "Weil space", "Weil type (balance) and the root i√d", "Hodge filtration", "Hodge classes", "de Rham cup order", "Complex structure on H_dR", "Pullback on de Rham cohomology"; upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (`deRhamConj`, `deRhamConj_smul`, `deRhamConjSemilinear`, `conjHodgeFiltrationComplexSubmodule`, `hodgePiece`, `hodgeClasses`, `fieldToDeRhamCohomology_smul`); this repository's `HodgeLadder/Weil/Surface/Statement.lean`, `HodgeLadder/Hodge/{Conjugation,DeRhamPullback,DeRhamCup,DeRhamCupGradedComm}.lean`, `HodgeLadder/General/EigenProducts.lean`; `docs/references.md` key `Mumford1970`.

Scratch: `rt-wsr-scratch/` in the worktree (`Ax.lean`, `Triv.lean`, `Model.lean`, `Model31.lean`, `RedCopy.lean`), each run with `lake env lean` against the built `.olean`; deleted after the pass. Every Lean claim marked "scratch" below elaborated there with no error and no warning.

**Verdict: pass with changes.** The five declarations are what the rung claims, with standard axioms: on upstream's `Hdg^1(A; ℚ)` (rational classes whose de Rham image lies in `F¹ ∩ conj⁻¹ F¹`) and the ladder's checked `weilSpace`, the rank and span hypotheses give the inclusion exactly, with the sign −d entering once through `weilRoot_sq` and the Koszul sign once through `deRhamCup_self_of_odd`. The statement is stronger than the ledger title (no dimension hypothesis; span only, no injectivity of `∧²H¹ → H²`). A concrete model of the abstract lemma's hypotheses on `ℂ⁴`, `ℂ⁶ = ∧²ℂ⁴` compiles, and its conclusion is nontrivial there; the same model with the signature-`(2, 0)` plane meets every hypothesis except balance and the conclusion fails, and a second model with eigenspaces of rank 3 and 1 meets every hypothesis except the conjugation pair and the conclusion fails (optional O1). No change to any statement is required. The changes are the model as a checked test in the file, two docstring corrections, the ledger entry, two gaps rows and three conventions entries.

## Findings

1. **Fidelity: the conclusion is upstream's Hodge classes and the ladder's Weil space.** Literature ([Weil1977]; [vanGeemen1994] §5; locators unverified): on a complex abelian surface A with K = ℚ(√−d) acting with signature (1, 1), W_K ⊂ H²(A; ℚ) consists of Hodge classes, the argument being that W_K ⊗ ℂ = ∧²V₊ ⊕ ∧²V₋ and each ∧²V± is a line a± ∧ b± with a± ∈ H^{1,0}, hence in H^{1,1} (plan §1). Field by field against `cb3d23c` (`#check`/`#print` in scratch `Ax.lean`):

   | Field | Literature | Lean | Match |
   |---|---|---|---|
   | variety | complex abelian surface | `A : Over (Spec ↧ℂ)`, `[IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]`, no `GrpObj`, no `dim` | stronger: the theorem holds for every smooth projective integral A meeting the three hypotheses; the module docstring says so, the ledger title says "surface" (change 4) |
   | K-action and signature | f with f² = [−d], signature (1, 1) | `IsWeilTypeSurface A f d` (rung `weil-surface-statement`, stated, red team pass with changes) | yes, as checked there |
   | b₁ = 4 | rank H¹(A; ℚ) = 4 | `finrank ℂ H_dR^1(A) = 4`, upstream's `deRhamHypercohomologyComplexModule` | yes: `deRhamBaseChangeEquiv` (rung `de-rham-rational-base-change`) gives ℂ ⊗ H¹(A; ℚ) ≅ H¹_dR, so this is b₁ = 4 |
   | H² = ∧²H¹ | the cup map ∧²H¹ → H² is an isomorphism | `Submodule.span ℂ (Set.image2 (fun x y => deRhamCup x y 2 _) univ univ) = ⊤` | weaker hypothesis (surjectivity only), so a stronger theorem; `deRhamCup` extends the rational cup product exactly (`fieldToDeRhamCohomology_cup`) and is nonzero and sign-separated (`deRhamCup_one_one_ne_zero`, `_ne_neg`), so the hypothesis is the literature's surjectivity and is no condition on a degenerate product |
   | W_K | ∧²_K H¹ | `weilSpace A f d = ker (pullbackCohLinear f 2 + d • id)`, the −d-eigenspace (`#print`), `d : ℕ` cast to ℚ | yes (rung `weil-space`, row "Weil space") |
   | conclusion | W_K ⊂ Hdg^1 | `weilSpace A f ↑d ≤ Hdg^1(A; ℚ)`, i.e. `hodgeClasses ℚ A 1 = ((hodgePiece A 1 1 2).restrictScalars ℚ).comap (fieldToDeRhamCohomologyLinear ℚ A 2)`, `hodgePiece A 1 1 2 = F¹ ⊓ (F¹).comap (deRhamConjSemilinear A 2)` | yes; algebraic form by `weilSpace_le_algebraic_iff_le_hodge` (Lefschetz (1,1) as an equality, checked) |
   | corollary | T1 | `(∀ abelian surface A, rank 4 ∧ span) → WeilClassesAlgebraicSurface`, the binder of `h` copied from `WeilClassesAlgebraicSurface` (`[GrpObj A]`, `dim A.left = 2 →`) | yes; the proof is `intro` and one application, so the corollary adds nothing beyond the Hodge form and Lefschetz (1,1) |

   The proof follows plan node B with one simplification: it uses no f-stability of F¹ (open rung `hodge-filtration-pullback`), since V₊ has rank 2 and contains a nonzero a ∈ F¹, so every product in V₊ × V₊ is a combination of a ∪ a, a ∪ b, b ∪ a, b ∪ b, and the first three lie in F¹ and the last vanishes. This is correct mathematics and matches the Lean proof (`pairs`).

2. **The conjugate condition in `Hdg^1` is handled, and by the right lemma.** Upstream's `Hdg^1` requires both `ι w ∈ F¹H²` and `deRhamConj (ι w) ∈ F¹H²`. The candidate discharges the second with `mem_hodgeClasses_of_mem_hodgeFiltration` (`HodgeLadder/Hodge/Conjugation.lean`, the module of `deRhamConj_fieldToDeRhamCohomology`, rung `chern-classes-are-hodge`): `deRhamConj` fixes `ι w` for rational `w`, so the second condition is the first. It does not go through `cup-hodge-reduction`; from that rung it uses only `hodgeFiltration_eq_top_of_nonpos` (F⁰ = ⊤) in `hF`. The abstract lemma's `G` is `F^1 H_dR^2(A) = hodgeFiltration A 1 2`, and its `hF` is `deRhamCup_mem_hodgeFiltration` at `p = 1`, `q = 0` (`x ∈ F¹H¹`, `y ∈ F⁰H¹ = ⊤`, product in `F^{1+0}`, rewritten by `add_zero`). The degree spellings (`2 * 1`, `((2 : ℕ) : ℤ)`, `2`) unify as elaborated.

3. **The conjugation hypotheses at the de Rham instance.** `J = deRhamConjSemilinear A 1` (upstream), conjugate-linear by upstream's `deRhamConj_smul`. Injectivity comes from the new `deRhamConj_deRhamConj`: the composite of two `starRingEnd`-semilinear maps is ℂ-linear, and it agrees with `id` on the ℚ-span of `ι`-images, which spans (`span_range_fieldToDeRhamCohomology_rat`, rung `de-rham-rational-span`); the proof is sound and needs projectivity only through that span lemma. `hTJ` is `(deRhamPullback_conj f 1 x).symm` (rung `de-rham-pullback`), the same direction. `hconj : conj (i√d) = −i√d` holds by `simp [weilRoot, Complex.conj_ofReal]`, using that `√d` has zero imaginary part (`Real.sqrt` cast to ℂ). In the abstract lemma `J` is used only to bound ranks (`rk`: an injective conjugate-linear map from `ker (T − s)` into `ker (T + s)` and back), which forces both eigenspaces to rank 2; any injective semilinear `J` commuting with `T` would do, and the conjugation inside `Hdg^1` is separately upstream's `deRhamConj`. So the rung does not depend on which conjugation is used here.

4. **Non-vacuity of the abstract lemma: a compiled model (scratch `Model.lean`, then `RedCopy.lean` inside a copy of the module).** V = ℂ⁴, W = ℂ⁶ with basis e01, e02, e03, e12, e13, e23 and `B = ∧²` written out, `T = modelEndo` (`J ⊕ J`, real entries, from `weil-surface-statement`), `S = ∧²T` computed as `w ↦ (w₀, w₄, −w₃, −w₂, w₁, w₅)`, `s = i`, `J` coordinatewise conjugation, `F = span {(1, −i, 0, 0), (0, 0, 1, i)}` (the plane of `isBalanced_model_one_one`), `G = F ∧ V`, written as the kernel of `w ↦ w₁ + i w₂ − i w₃ + w₄` (computed from the two functionals `i x₀ + x₁`, `−i x₂ + x₃` vanishing on F). Every hypothesis is discharged with no `sorry`, and:
   - the conclusion holds (`ker_modelWedgeEndo_le_one_one`, an application of `ker_sub_smul_le_of_isBalanced`);
   - `ker (S + 1) ≠ ⊥` (contains `e02 − e13`), `≠ ⊤` (`e02 ∉`), and `G ≠ ⊤` (`e02 ∉ G`). Here `ker (S + 1) = {(0, a, b, b, −a, 0)}` has rank 2, the expected rank of W_K ⊗ ℂ;
   - **balance is load-bearing:** with the signature-(2, 0) plane `F' = span {(1, −i, 0, 0), (0, 0, 1, −i)}` and `G' = F' ∧ V` (kernel of `w ↦ −w₁ + i w₂ + i w₃ + w₄`), every hypothesis except `hbal` holds (`modelWedge_mem_two_zero`; `not_isBalanced_model_two_zero` is already checked) and the conclusion fails: `e03 + e12 ∈ ker (S + 1)`, `∉ G'` (`not_ker_modelWedgeEndo_le_two_zero`). This is the Hodge-theoretic counterexample of plan §1 in the model;
   - **the conjugation pair is load-bearing** (scratch `Model31.lean`; text in O1): `T = diag (i, i, i, −i)`, `S = ∧²T = diag (−1, −1, 1, −1, 1, 1)`, `F = span {e0, e3}` (balanced), `G = F ∧ V = ker (w ↦ w₃)`; `hS`, `hT`, `hB`, `hF`, `hbal`, rank 4 and span all hold, and `e12 ∈ ker (S + 1)`, `e12 ∉ G`. No injective conjugate-linear `J` commutes with this `T`, since it would embed a rank-3 eigenspace into a rank-1 one;
   - the span hypothesis is load-bearing by the same construction with a seventh coordinate on which `S = −1` and `B` vanishes (pen and paper, not compiled);
   - rank 4 is load-bearing (pen and paper): in rank 6 with a 3 + 3 split swapped by `J` and `F ∩ V₋` a line, `V₋` contains a plane meeting `F` in 0, and the product of its two basis vectors lies in `ker (S − s²)` and need not lie in `G`. This is the abelian threefold of signature (2, 1) of the statement red team (finding 3 there): `∧²V₋` contains a class of type (0, 2), and the inclusion is false.

   Every hypothesis of `ker_sub_smul_le_of_isBalanced` appears in its proof: `hS`, `hspan` in the call to `ker_sub_smul_le_span_of_eigen`; `hT`, `hs` in `isCompl_ker_sub_smul_ker_add_smul` and `hne`; `hconj`, `hTJ` in `JP`, `JN`; `hJ` in `rk`; `hrank` in `hP2`, `hN2`; `hB` in `hF'` and `pairs`; `hF`, `hbal` in `pairs`.

5. **Not trivially true.** Scratch `Triv.lean`: after `intro w hw; apply mem_hodgeClasses_of_mem_hodgeFiltration A 1 w`, `simp` leaves `(fieldToDeRhamCohomology ℚ A 2) w ∈ hodgeFiltration A 1 2`; `exact?` fails on `F^1 H_dR^2(A) = ⊤` for a general `A`, and fails on the reduction with the balance hypothesis removed. No definition unfolds to `True`, no `ℕ∞` coercion, no empty index type. Mathematically, F¹H² ≠ H² on every abelian surface (H^{2,0} ≠ 0), so a short proof would signal an error in upstream's `F^p`; none exists. The one way the theorem could hold for a reason unrelated to the mathematics is `F^1 H_dR^2(X) = ⊤` for all X at the pin, which nothing proves and which no test can refute until an X with h^{2,0} ≠ 0 is built (gaps, Known weaknesses, row "No test exhibits a nonzero product landing in a proper F^{p+q}"). The hypotheses are jointly consistent in the model; on schemes, E × E with f = [i] × [i]⁻¹ satisfies them mathematically.

6. **Signs and normalizations.** Each convention the statement or proof uses:

   | Convention | Where | Truth depends on it? | Check |
   |---|---|---|---|
   | eigenvalue −d on H² | `weilSpace`, row "Weil space" | yes (with +d the theorem is false on a balanced surface) | the proof reads `mem_weilSpace_iff` as `f^* w = −d • w` and matches it to `s * s` through `← sq, weilRoot_sq : (i√d)² = −d`; the step `(−(d : ℚ)) • ι w = (−(d : ℂ)) • ι w` uses upstream's `fieldToDeRhamCohomology_smul` (ℚ-scalars by restriction of ℂ-scalars) and `Nat.cast_smul_eq_nsmul`, no scalar enters |
   | `(f^*)² = −d` on `H¹_dR` | `IsWeilTypeSurface.deRhamPullback_sq` | yes (it is `hT`) | `hT` is `deRhamPullback_sq`, `← sq`, `weilRoot_sq`; exact |
   | root i√d and conj(i√d) = −i√d | `weilRoot`, row "Weil type (balance) and the root i√d" | no for the root (`isBalanced_neg_iff`); the conj identity is a fact about `weilRoot`, true for either root | `Complex.conj_ofReal`; new in this rung, change 6a |
   | Koszul sign (−1)^{1·1} on H¹ × H¹ | `deRhamCup_self_of_odd`, row "de Rham cup order" | used by the proof (`hB`: x ∪ x = 0; `hF'`: y ∪ x = −x ∪ y from `hB` at x + y); the statement does not depend on it, since the product appears only in the span hypothesis, which is invariant under a sign or nonzero scalar | checked rung `de-rham-cup-antisymm-h1`; change 6b |
   | Hodge filtration, F⁰ = ⊤ | upstream `hodgeFiltration`, `hodgeFiltration_eq_top_of_nonpos`; row "Hodge filtration" | yes (the conclusion) | statement of record; membership statements are sign-insensitive |
   | conjugation on H_dR | upstream `deRhamConj`, `deRhamConjSemilinear`; no row | yes for `Hdg^1` (statement of record); no for `hJ`, which any injective semilinear J commuting with T satisfies | new row, change 6c |
   | ℂ-action on H_dR | row "Complex structure on H_dR" | yes for the eigenspace argument (row "Pullback on de Rham cohomology" names this rung) | one instance throughout: the abstract lemma is applied at `[Module ℂ H_dR^1(A)]` found by instance search, and the application elaborates against `deRhamPullback`, `deRhamCupBilinear` and `deRhamConjSemilinear`, whose types carry `deRhamHypercohomologyComplexModule` |

   No sign other than −d and the Koszul sign enters. `hne : s * −s ≠ s * s` uses only `s ≠ 0` and `2 ≠ 0` in ℂ. No new instance, attribute, notation or `set_option` in the file (grep: none).

7. **Equality first (decision 0004).** The rung is an inclusion. Its equality partners: `Hdg^1 = algebraicCycleClassSpan 1` (`lefschetz-1-1-equality`, checked), used for the algebraic form; and the companion identity that the inclusion holds on a nonzero space, `finrank ℚ (weilSpace A f d) = 2` under the same hypotheses plus `finrank ℂ H_dR^2(A) = 6` (rung `weil-surface-rank`, open, with the rank-6 hypothesis justified in its note). At the linear-algebra level the eigenspace identity `ker_sub_smul_eq_span_of_eigen` (checked, `weil-eigen-algebra`) already gives the equality ker (S − s²) = span of B(V₊, V₊) ∪ B(V₋, V₋); the model's `ker_modelWedgeEndo_ne_bot` is its non-vacuity in the model.

7b. **Smallest non-vacuity test in upstream's API.** On schemes: `∃ A f d, IsWeilTypeSurface A f d ∧ finrank ℂ H_dR^1(A) = 4 ∧ (span hypothesis) ∧ weilSpace A f d ≠ ⊥`, with `AlgebraicGeometry.ComplexPoint.hodgeClasses` the target; it is the conjunction of `elliptic-square-cohomology`, `weil-elliptic-square` (its IsWeilTypeSurface step) and `weil-elliptic-square-nonzero`, all open. A test that the inclusion is not trivially true for every X would be `¬ weilSpace X f d ≤ Hdg^1(X; ℚ)` for E × E with f = [i] × [i] (signature (2, 0)); it needs an X with h^{2,0} ≠ 0 at the pin and has no rung (optional change O3). Before either, the abstract model of finding 4 is the checked guard, and change 1 adds it.

8. **Vacuity at the pin, honestly stated.** At the pin no smooth projective X has a checked b₁ ≠ 0, so the hypothesis `hrank` holds for no known scheme and the two reduction theorems apply to none; the module docstring says so. The corollary's hypothesis `h` quantifies over every abelian surface; it is the literature's b₁ = 4 and H*(A; ℚ) = ∧*H¹(A; ℚ) for a complex torus of dimension 2 ([Mumford1970] §1; [GriffithsHarris1978] ch. 2 §6; locators unverified), reached on the ladder through `abelian-surface-uniformization` and `torus-singular-cohomology` (rung `weil-surface`). The planned instance `E × E` (rungs `elliptic-square-cohomology`, `weil-elliptic-square`) discharges the hypotheses of the two reduction theorems and leaves `h` open, since `h` is universal; the module docstring's "The planned first instance is `E × E` ..." does not say which theorem it instantiates (change 2). Two phrases are loose: "no smooth projective `X` is known to have `b₁ ≠ 0`" (the elliptic curve of `elliptic-curve-witness` has b₁ = 2 mathematically; its H¹ is not computed), and "the inclusion in `F¹` would be unproved" (in rank 6 it is false in general). Change 2 gives exact text.

9. **Checker and axioms.** `python3 tools/check.py --no-build` exits 0 on the branch (`ACCEPTED: all checks passed`), without covering this rung, since the ledger names no declaration yet. Scratch `Ax.lean`: `#print axioms` on `ker_sub_smul_le_of_isBalanced`, `deRhamConj_deRhamConj`, `weilSpace_le_hodge_of_rank_span`, `weilSpace_le_algebraic_of_rank_span`, `weilClassesAlgebraicSurface_of_rank_span` gives `[propext, Classical.choice, Quot.sound]` for each; the same for the model declarations (`Model.lean`). No `sorry`, `native_decide` or `axiom` in the file. `lake build HodgeLadder.Weil.Surface.Reduction` is current; `lake env lean` on the file takes about 47 s, and with the model section about 48 s.

10. **Pin drift.** None: the rung and every rung it uses are at upstream `2ead713`; the definitions read (`hodgeClasses`, `hodgePiece`, `conjHodgeFiltrationComplexSubmodule`, `deRhamConj`, `deRhamConjSemilinear`, `fieldToDeRhamCohomology_smul`) are the ones at that commit.

11. **Placement and bookkeeping.**
    - `python3 tools/pinwalk.py` graph: `HodgeLadder.Weil.Surface.Reduction` is layer 49 (imports `HodgeLadder.Weil.Surface.Statement`, layer 48, and `HodgeLadder.Hodge.CupHodgeFiltration`, layer 24).
    - `ker_sub_smul_le_of_isBalanced` is general linear algebra over ℂ with no Mathlib counterpart; it needs `IsBalanced` (layer 48), so it stays in this module with a gaps row in "Linear algebra: eigenspaces" (change 5a).
    - `deRhamConj_deRhamConj` is a fact about upstream's `deRhamConj` that upstream could add at a bump; gaps row in "De Rham complex and holomorphic forms" (change 5b). It would sit naturally beside `deRhamPullback_conj` in `HodgeLadder.Hodge.DeRhamPullback` (layer 25, same proof pattern, already imports the span lemma); optional O2. `HodgeLadder.Hodge.Conjugation` (layer 0) cannot hold it without a new import.
    - Ledger `depends_on` lists `rational-cohomology-finite-dimensional`, which the proof does not use (finite dimensionality comes from `finrank = 4` through `Module.finite_of_finrank_pos`), and omits `de-rham-rational-span` (`span_range_fieldToDeRhamCohomology_rat` in `deRhamConj_deRhamConj`) and `chern-classes-are-hodge` (`mem_hodgeClasses_of_mem_hodgeFiltration`, `deRhamConj_fieldToDeRhamCohomology`). The ledger title says "surface"; the Lean has no dimension hypothesis (change 4).
    - `docs/roadmap.md` row `weil-surface-reduction` carries the same `depends_on` list and must follow the ledger (change 7).

## Required changes

1. `HodgeLadder/Weil/Surface/Reduction.lean`: insert the section below immediately before `end HodgeLadder.Weil` (compiled in scratch `RedCopy.lean`, a copy of `cb3d23c` with this section appended, no error, no warning, about 48 s for the whole file). In the module docstring, add a section before "## Conventions":

   "## Checks

   `ker_sub_smul_le_of_isBalanced` is checked non-vacuous on a model: `V = ℂ⁴`, `W = ∧²ℂ⁴ = ℂ⁶`, `T = modelEndo`, `s = i`, `J` coordinatewise conjugation, `F` the signature-`(1, 1)` plane of `isBalanced_model_one_one`, `G = F ∧ V`. The conclusion holds (`ker_modelWedgeEndo_le_one_one`), the eigenspace is neither `⊥` nor `⊤` and `G ≠ ⊤` (`ker_modelWedgeEndo_ne_bot`, `ker_modelWedgeEndo_ne_top`, `modelWedgeHodgeOneOne_ne_top`). With the signature-`(2, 0)` plane every hypothesis except balance holds and the conclusion fails (`not_ker_modelWedgeEndo_le_two_zero`)."

   and append to "## Main results": "* `HodgeLadder.Weil.ker_modelWedgeEndo_le_one_one`, `ker_modelWedgeEndo_ne_bot`, `ker_modelWedgeEndo_ne_top`, `modelWedgeHodgeOneOne_ne_top`, `not_ker_modelWedgeEndo_le_two_zero`: the model checks."

```lean
section Checks

/-! ### Non-vacuity of `ker_sub_smul_le_of_isBalanced`

A model of its hypotheses on `V = ℂ⁴`, `W = ℂ⁶ = ∧²ℂ⁴` (basis `e01, e02, e03, e12, e13, e23`),
`T = modelEndo` (`J ⊕ J`, rung `weil-surface-statement`), `s = i`, `J` coordinatewise
conjugation, `F` the balanced plane of `isBalanced_model_one_one` and `G = F ∧ V`. The conclusion
holds there and is not trivial (`ker_modelWedgeEndo_ne_bot`, `ker_modelWedgeEndo_ne_top`,
`modelWedgeHodgeOneOne_ne_top`), and it fails for the signature-`(2, 0)` plane, which meets every
hypothesis except balance (`not_ker_modelWedgeEndo_le_two_zero`). -/

/-- `∧² : ℂ⁴ × ℂ⁴ → ℂ⁶` in the basis `e01, e02, e03, e12, e13, e23`. -/
def modelWedge : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) :=
  LinearMap.mk₂ ℂ
    (fun x y => ![x 0 * y 1 - x 1 * y 0, x 0 * y 2 - x 2 * y 0, x 0 * y 3 - x 3 * y 0,
      x 1 * y 2 - x 2 * y 1, x 1 * y 3 - x 3 * y 1, x 2 * y 3 - x 3 * y 2])
    (fun x x' y => by funext i; fin_cases i <;> simp <;> ring)
    (fun c x y => by funext i; fin_cases i <;> simp <;> ring)
    (fun x y y' => by funext i; fin_cases i <;> simp <;> ring)
    (fun c x y => by funext i; fin_cases i <;> simp <;> ring)

/-- `∧² modelEndo` in the same basis: `e01 ↦ e01`, `e02 ↦ e13`, `e03 ↦ −e12`, `e12 ↦ −e03`,
`e13 ↦ e02`, `e23 ↦ e23`. -/
def modelWedgeEndo : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun w := ![w 0, w 4, -(w 3), -(w 2), w 1, w 5]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp

/-- Coordinatewise conjugation on `ℂ⁴`. -/
def modelConj : (Fin 4 → ℂ) →ₛₗ[starRingEnd ℂ] (Fin 4 → ℂ) where
  toFun v i := starRingEnd ℂ (v i)
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

/-- The signature-`(1, 1)` plane `span {(1, −i, 0, 0), (0, 0, 1, i)}`. -/
def modelHodgeOneOne : Submodule ℂ (Fin 4 → ℂ) :=
  Submodule.span ℂ {![1, -Complex.I, 0, 0], ![0, 0, 1, Complex.I]}

/-- `modelHodgeOneOne ∧ ℂ⁴`, as the kernel of `w ↦ w₁ + i w₂ − i w₃ + w₄`. -/
def modelWedgeHodgeOneOne : Submodule ℂ (Fin 6 → ℂ) :=
  LinearMap.ker (({ toFun := fun w => w 1 + Complex.I * w 2 - Complex.I * w 3 + w 4
                    map_add' := fun v w => by simp; ring
                    map_smul' := fun c v => by simp; ring } : (Fin 6 → ℂ) →ₗ[ℂ] ℂ))

/-- The signature-`(2, 0)` plane `span {(1, −i, 0, 0), (0, 0, 1, −i)}`. -/
def modelHodgeTwoZero : Submodule ℂ (Fin 4 → ℂ) :=
  Submodule.span ℂ {![1, -Complex.I, 0, 0], ![0, 0, 1, -Complex.I]}

/-- `modelHodgeTwoZero ∧ ℂ⁴`, as the kernel of `w ↦ −w₁ + i w₂ + i w₃ + w₄`. -/
def modelWedgeHodgeTwoZero : Submodule ℂ (Fin 6 → ℂ) :=
  LinearMap.ker (({ toFun := fun w => -w 1 + Complex.I * w 2 + Complex.I * w 3 + w 4
                    map_add' := fun v w => by simp; ring
                    map_smul' := fun c v => by simp; ring } : (Fin 6 → ℂ) →ₗ[ℂ] ℂ))

/-- `hS` in the model: `∧² modelEndo` is multiplicative on `modelWedge`. -/
theorem modelWedgeEndo_modelWedge (x y : Fin 4 → ℂ) :
    modelWedgeEndo (modelWedge x y) = modelWedge (modelEndo x) (modelEndo y) := by
  funext i; fin_cases i <;> simp [modelWedge, modelWedgeEndo, modelEndo] <;> ring

/-- `hT` in the model, with `s = i`. -/
theorem modelEndo_modelEndo_I (x : Fin 4 → ℂ) :
    modelEndo (modelEndo x) = (Complex.I * Complex.I) • x := by
  funext i; fin_cases i <;> simp [modelEndo]

/-- `hTJ` in the model: `modelEndo` has real entries, so it commutes with conjugation. -/
theorem modelEndo_modelConj (x : Fin 4 → ℂ) :
    modelEndo (modelConj x) = modelConj (modelEndo x) := by
  funext i; fin_cases i <;> simp [modelEndo, modelConj]

/-- `hJ` in the model. -/
theorem modelConj_injective : Function.Injective modelConj := fun x y h => by
  funext i
  exact (starRingEnd ℂ).injective (congrFun h i)

/-- `hB` in the model: `modelWedge` is alternating. -/
theorem modelWedge_self (x : Fin 4 → ℂ) : modelWedge x x = 0 := by
  funext i; fin_cases i <;> simp [modelWedge] <;> ring

/-- `hF` in the model: `x ∈ F` gives `x ∧ y ∈ G`. -/
theorem modelWedge_mem_one_one (x y : Fin 4 → ℂ) (hx : x ∈ modelHodgeOneOne) :
    modelWedge x y ∈ modelWedgeHodgeOneOne := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp only [modelWedgeHodgeOneOne, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
    modelWedge, LinearMap.mk₂_apply]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `hF` for the signature-`(2, 0)` plane. -/
theorem modelWedge_mem_two_zero (x y : Fin 4 → ℂ) (hx : x ∈ modelHodgeTwoZero) :
    modelWedge x y ∈ modelWedgeHodgeTwoZero := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp only [modelWedgeHodgeTwoZero, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
    modelWedge, LinearMap.mk₂_apply]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `hspan` in the model: `e_i ∧ e_j` is the `ij` basis vector. -/
theorem span_modelWedge :
    Submodule.span ℂ (Set.image2 (fun x y => modelWedge x y) Set.univ Set.univ) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℂ (Fin 6)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact ⟨Pi.single 0 1, trivial, Pi.single 1 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩
  · exact ⟨Pi.single 0 1, trivial, Pi.single 2 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩
  · exact ⟨Pi.single 0 1, trivial, Pi.single 3 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩
  · exact ⟨Pi.single 1 1, trivial, Pi.single 2 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩
  · exact ⟨Pi.single 1 1, trivial, Pi.single 3 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩
  · exact ⟨Pi.single 2 1, trivial, Pi.single 3 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩

/-- **The linear-algebra step holds in the model**, every hypothesis discharged. -/
theorem ker_modelWedgeEndo_le_one_one :
    LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) ≤
      modelWedgeHodgeOneOne := by
  have hbal : IsBalanced modelHodgeOneOne modelEndo Complex.I := by
    have h := isBalanced_model_one_one
    rw [weilRoot_one] at h
    exact h
  exact ker_sub_smul_le_of_isBalanced modelWedge modelEndo modelWedgeEndo modelConj
    modelWedgeEndo_modelWedge modelEndo_modelEndo_I Complex.I_ne_zero Complex.conj_I
    modelConj_injective modelEndo_modelConj modelWedge_self modelWedge_mem_one_one hbal
    (Module.finrank_fin_fun ℂ) span_modelWedge

/-- The `−1`-eigenspace of `∧² modelEndo` is nonzero: it contains `e02 − e13`. -/
theorem ker_modelWedgeEndo_ne_bot :
    LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨![0, 1, 0, 0, -1, 0], ?_, ?_⟩
  · rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [modelWedgeEndo]
  · intro h; have := congrFun h 1; simp at this

/-- The `−1`-eigenspace of `∧² modelEndo` is proper: `e02` is not in it. -/
theorem ker_modelWedgeEndo_ne_top :
    LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) ≠ ⊤ := by
  intro h
  have h1 : (![0, 1, 0, 0, 0, 0] : Fin 6 → ℂ) ∈
      LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) := h ▸ trivial
  rw [LinearMap.mem_ker] at h1
  have := congrFun h1 1
  simp [modelWedgeEndo] at this

/-- `G = F ∧ V` is proper in the model: `e02 ∉ G`. -/
theorem modelWedgeHodgeOneOne_ne_top : modelWedgeHodgeOneOne ≠ ⊤ := by
  intro h
  have h1 : (![0, 1, 0, 0, 0, 0] : Fin 6 → ℂ) ∈ modelWedgeHodgeOneOne := h ▸ trivial
  simp [modelWedgeHodgeOneOne] at h1

/-- **Balance is load-bearing.** The signature-`(2, 0)` plane meets every other hypothesis
(`modelWedge_mem_two_zero` with the same `B`, `T`, `S`, `J`, rank and span), and the conclusion
fails: `e03 + e12` lies in the `−1`-eigenspace and not in `modelHodgeTwoZero ∧ ℂ⁴`. -/
theorem not_ker_modelWedgeEndo_le_two_zero :
    ¬ LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) ≤
      modelWedgeHodgeTwoZero := by
  intro h
  have h1 : (![0, 0, 1, 1, 0, 0] : Fin 6 → ℂ) ∈
      LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) := by
    rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [modelWedgeEndo]
  have h2 := h h1
  simp [modelWedgeHodgeTwoZero] at h2

end Checks

```

2. Module docstring of `HodgeLadder/Weil/Surface/Reduction.lean`:
   - section "Vacuity": replace the whole paragraph by: "At the pin no smooth projective `X` has a checked `b₁ ≠ 0` (the elliptic curve of rung `elliptic-curve-witness` has `b₁ = 2` in the literature; its `H¹` is not computed), so hypothesis 1 holds for no known scheme and both reduction theorems apply to none. Their planned first instance is `E × E` with `f = [i] × [i]⁻¹` and `d = 1`: rank and span from rung `elliptic-square-cohomology`, the Weil-type condition and the conclusion in rung `weil-elliptic-square`. The hypothesis of `weilClassesAlgebraicSurface_of_rank_span` quantifies over every abelian surface; that instance leaves it open, and rung `weil-surface` discharges it through `abelian-surface-uniformization`."
   - section "The argument", last paragraph: replace "Rank 4 is used: with `V₊` of rank 3 a product of two classes of `V₊` outside `F¹` would lie in the `−d`-eigenspace and the inclusion in `F¹` would be unproved." by "Rank 4 is used: in rank 6 with `F¹ ∩ V₋` a line, `V₋` holds a plane meeting `F¹` in 0, the product of its basis lies in the `−d`-eigenspace, and on an abelian threefold of signature `(2, 1)` it has type `(0, 2)`, so the inclusion is false there. Without the conjugation hypotheses the eigenspaces can have ranks 3 and 1, and the conclusion fails in a model of that shape (red team, `docs/sketches/weil-surface-reduction.redteam.md`)."
   - docstring of `weilClassesAlgebraicSurface_of_rank_span`: replace "([Mumford1970] §1, locator unverified)" by "([Mumford1970] §1; [GriffithsHarris1978] ch. 2 §6; locators unverified)".

3. Docstring of `ker_sub_smul_le_of_isBalanced`: append "The conjugation is used only to force both eigenspaces to rank 2; any injective conjugate-linear `J` commuting with `T` serves, and at the de Rham instance it is upstream's `deRhamConjSemilinear`."

4. `ledger/ladder.json`, rung `weil-surface-reduction`:
   - `title`: "T1's linear-algebra step: on a smooth projective integral A over ℂ (no dimension hypothesis) with IsWeilTypeSurface A f d, finrank ℂ H_dR^1(A) = 4 and H_dR^2(A) spanned by deRhamCup of H¹ classes, weilSpace A f d ≤ Hdg^1(A; ℚ), hence ≤ algebraicCycleClassSpan A 1; so WeilClassesAlgebraicSurface follows from rank 4 and span on every abelian surface"
   - `status` `checked`; `kind` `reduction`; `module` `HodgeLadder.Weil.Surface.Reduction`;
   - `declarations`: `HodgeLadder.Weil.ker_sub_smul_le_of_isBalanced`, `HodgeLadder.Weil.deRhamConj_deRhamConj`, `HodgeLadder.Weil.weilSpace_le_hodge_of_rank_span`, `HodgeLadder.Weil.weilSpace_le_algebraic_of_rank_span`, `HodgeLadder.Weil.weilClassesAlgebraicSurface_of_rank_span`, `HodgeLadder.Weil.ker_modelWedgeEndo_le_one_one`, `HodgeLadder.Weil.ker_modelWedgeEndo_ne_bot`, `HodgeLadder.Weil.ker_modelWedgeEndo_ne_top`, `HodgeLadder.Weil.modelWedgeHodgeOneOne_ne_top`, `HodgeLadder.Weil.not_ker_modelWedgeEndo_le_two_zero`;
   - `depends_on`: `weil-space`, `weil-eigen-algebra`, `de-rham-pullback`, `cup-hodge-filtration`, `cup-hodge-reduction`, `de-rham-cup-antisymm-h1`, `de-rham-rational-span`, `chern-classes-are-hodge`, `weil-surface-statement` (drop `rational-cohomology-finite-dimensional`, unused);
   - `note`: "Checked 2026-11-28. Conditional theorem on upstream definitions, no dimension hypothesis: IsWeilTypeSurface A f d, finrank ℂ H_dR^1(A) = 4 and the span of deRhamCup on H¹ × H¹ give weilSpace A f d ≤ Hdg^1(A; ℚ) exactly, the conjugate condition of Hdg^1 through mem_hodgeClasses_of_mem_hodgeFiltration; algebraic form by Lefschetz (1,1) as an equality; WeilClassesAlgebraicSurface from rank and span on every abelian surface (literature b₁ = 4, H² = ∧²H¹; Mumford1970 §1, locators unverified). Linear algebra in ker_sub_smul_le_of_isBalanced (abstract ℂ-spaces); injectivity of conjugation from deRhamConj_deRhamConj. Signs: −d through weilRoot_sq, Koszul (−1)^(1·1) through deRhamCup_self_of_odd, nothing else. Model checks on ℂ⁴, ∧²ℂ⁴: conclusion nontrivial, fails for signature (2, 0); a rank-(3, 1) model without conjugation also fails (red team). Vacuous at the pin: no X with a checked b₁ ≠ 0; instance planned on E × E (elliptic-square-cohomology, weil-elliptic-square). Companion rank identity: weil-surface-rank (open). Red team docs/sketches/weil-surface-reduction.redteam.md."

5. `docs/gaps.md`, "General lemmas kept local":
   - a. "Linear algebra: eigenspaces", new row after the `IsBalanced` row: "| `HodgeLadder.Weil.ker_sub_smul_le_of_isBalanced` (B alternating bilinear on a rank-4 ℂ-space V with products spanning W, `S (B x y) = B (T x) (T y)`, `T² = s²`, `s ≠ 0`, an injective conjugate-linear `J` commuting with `T` with `conj s = −s`, `F` balanced and `B x y ∈ G` for `x ∈ F`: `ker (S − s² • id) ≤ G`) | `HodgeLadder.Weil.Surface.Reduction` | 49 | no Mathlib counterpart (Mathlib has eigenspace independence, no statement on products of eigenvectors against a filtration); needs `IsBalanced`; rung `weil-surface-reduction` | 2026-11-28 |"
   - b. "De Rham complex and holomorphic forms", new row after the `deRhamPullback` row: "| `HodgeLadder.Weil.deRhamConj_deRhamConj` (upstream's `deRhamConj X n` is an involution on smooth projective integral X, from `deRhamConj_fieldToDeRhamCohomology` and `span_range_fieldToDeRhamCohomology_rat`) | `HodgeLadder.Weil.Surface.Reduction` | 49 | upstream has `deRhamConj_smul` and no involution lemma at the pin; a bump that adds one replaces this row; rung `weil-surface-reduction` | 2026-11-28 |"

6. `docs/conventions.md`:
   - a. row "Weil type (balance) and the root i√d", column "Status": append "; `conj (i√d) = −i√d` (`Complex.conj_ofReal`, √d real) used by `weil-surface-reduction` to swap V₊ and V₋ under `deRhamConj`, true for either root (red team 2026-11-28, `docs/sketches/weil-surface-reduction.redteam.md`)".
   - b. row "de Rham cup order", column "Results whose truth depends on it": append "; `weil-surface-reduction` uses the Koszul sign in its proof only (`deRhamCup_self_of_odd`); its statement involves `deRhamCup` only through a span hypothesis, insensitive to a sign or nonzero scalar".
   - c. new row after "Hodge classes": "| Conjugation on H_dR | upstream `deRhamConj`, `deRhamConj_smul`, `deRhamConjSemilinear` (`Definitions/AlgebraicGeometry/Hodge/Filtration.lean`); this repository `HodgeLadder.deRhamConj_fieldToDeRhamCohomology` (`HodgeLadder/Hodge/Conjugation.lean`), `HodgeLadder.deRhamPullback_conj`, `HodgeLadder.Weil.deRhamConj_deRhamConj` | conjugation of constant complex coefficients transported through `H^n(X(ℂ); ℂ) ≃ H_dR^n(X)`; conjugate-linear for upstream's ℂ-action (`deRhamConj (c • α) = conj c • deRhamConj α`); fixes ι-images of rational classes; an involution on smooth projective integral X; commutes with `deRhamPullback` | `hodgeClasses` (statement of record, the conjugate filtration); `weil-surface-reduction` uses it for rank counting only, where any injective semilinear map commuting with the pullback serves | read from source; involution and pullback compatibility checked (red team 2026-11-28, `docs/sketches/weil-surface-reduction.redteam.md`) |"

7. `docs/roadmap.md`, row `weil-surface-reduction`: status `checked`, the `depends_on` list of change 4, and the module `HodgeLadder.Weil.Surface.Reduction` with this red-team file.

## Optional changes

- O1. Append the rank-(3, 1) model after the section of change 1, as the checked guard that the conjugation hypotheses are load-bearing (compiled in scratch `RedCopy.lean` together with change 1, no error, no warning), and add `HodgeLadder.Weil.not_ker_model31WedgeEndo_le` to the ledger declarations:

```lean
section Checks31

/-- `T = diag (i, i, i, −i)` on `ℂ⁴`: `T² = −1`, eigenspaces of rank 3 and 1, so no injective
conjugate-linear map commutes with it. -/
def model31Endo : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun x := ![Complex.I * x 0, Complex.I * x 1, Complex.I * x 2, -(Complex.I * x 3)]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp <;> ring

/-- `∧² model31Endo`, diagonal `(−1, −1, 1, −1, 1, 1)` in the basis of `modelWedge`. -/
def model31WedgeEndo : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun w := ![-(w 0), -(w 1), w 2, -(w 3), w 4, w 5]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp

/-- The balanced plane `span {e0, e3}` for `model31Endo`. -/
def model31Hodge : Submodule ℂ (Fin 4 → ℂ) := Submodule.span ℂ {![1, 0, 0, 0], ![0, 0, 0, 1]}

/-- `model31Hodge ∧ ℂ⁴`, the kernel of the `e12` coordinate. -/
def model31WedgeHodge : Submodule ℂ (Fin 6 → ℂ) :=
  LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 6 => ℂ) 3)

/-- `hS` for the rank-`(3, 1)` model. -/
theorem model31WedgeEndo_modelWedge (x y : Fin 4 → ℂ) :
    model31WedgeEndo (modelWedge x y) = modelWedge (model31Endo x) (model31Endo y) := by
  funext i
  fin_cases i <;> simp [modelWedge, model31WedgeEndo, model31Endo] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/-- `hT` for the rank-`(3, 1)` model, with `s = i`. -/
theorem model31Endo_model31Endo (x : Fin 4 → ℂ) :
    model31Endo (model31Endo x) = (Complex.I * Complex.I) • x := by
  funext i; fin_cases i <;> simp [model31Endo, ← mul_assoc, Complex.I_mul_I]

/-- `hF` for the rank-`(3, 1)` model. -/
theorem modelWedge_mem_model31 (x y : Fin 4 → ℂ) (hx : x ∈ model31Hodge) :
    modelWedge x y ∈ model31WedgeHodge := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp [model31WedgeHodge, modelWedge]

/-- `hbal` for the rank-`(3, 1)` model: `e0` and `e3` are eigenvectors for `i` and `−i`. -/
theorem isBalanced_model31 : IsBalanced model31Hodge model31Endo Complex.I := by
  constructor
  · rw [Submodule.ne_bot_iff]
    refine ⟨![1, 0, 0, 0], Submodule.mem_inf.mpr ⟨Submodule.subset_span (by simp), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [model31Endo]
    · intro h; have := congrFun h 0; simp at this
  · rw [Submodule.ne_bot_iff]
    refine ⟨![0, 0, 0, 1], Submodule.mem_inf.mpr ⟨Submodule.subset_span (by simp), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [model31Endo]
    · intro h; have := congrFun h 3; simp at this

/-- **The conjugation hypotheses are load-bearing.** Every hypothesis of
`ker_sub_smul_le_of_isBalanced` except `hJ` and `hTJ` holds for `modelWedge`, `model31Endo`,
`model31WedgeEndo`, `model31Hodge`, `model31WedgeHodge` (with `modelWedge_self`,
`span_modelWedge` and rank 4), and the conclusion fails: `e12 ∈ ker (S + 1)`, `e12 ∉ G`. -/
theorem not_ker_model31WedgeEndo_le :
    ¬ LinearMap.ker (model31WedgeEndo - (Complex.I * Complex.I) • LinearMap.id) ≤
      model31WedgeHodge := by
  intro h
  have h1 : (![0, 0, 0, 1, 0, 0] : Fin 6 → ℂ) ∈
      LinearMap.ker (model31WedgeEndo - (Complex.I * Complex.I) • LinearMap.id) := by
    rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [model31WedgeEndo]
  have h2 := h h1
  simp [model31WedgeHodge] at h2

end Checks31
```

- O2. Move `deRhamConj_deRhamConj` to `HodgeLadder.Hodge.DeRhamPullback` beside `deRhamPullback_conj` (layer 25; same proof pattern), in the namespace `HodgeLadder`, and update the gaps row of change 5b.
- O3. New rung (test, open) once an X with h^{2,0} ≠ 0 exists: `¬ weilSpace ellipticSquare (ellipticI × ellipticI) 1 ≤ Hdg^1(ellipticSquare; ℚ)` (signature (2, 0)), the scheme-level guard that the inclusion is not trivially true; depends on `elliptic-square-cohomology`, `elliptic-curve-h1-eigen`, `hodge-filtration-pullback` and a nonzero holomorphic 2-form.
- O4. `docs/references.md`, row `Mumford1970`, scope column: append "; cohomology ring of a complex torus, H*(X; ℤ) ≅ ∧*H¹ (§1, locator unverified)".

## Attempts that failed

- A short proof of `weilSpace A f d ≤ Hdg^1(A; ℚ)` with no hypotheses: after `mem_hodgeClasses_of_mem_hodgeFiltration`, `simp` leaves the F¹ membership; `exact?` finds no proof of `F^1 H_dR^2(A) = ⊤`; the same with every hypothesis except balance, `exact?` fails. As they should.
- `simpa [weilRoot_one] using isBalanced_model_one_one` against the model plane: `simpa` normalizes `Fin 4` to `Fin (Nat.succ 0).succ.succ.succ` in the instance and the types mismatch; `rw [weilRoot_one] at h; exact h` works (the text of change 1 uses it).
- `simpa [conj4]` for injectivity of coordinatewise conjugation: leaves `conj (x i) = conj (y i)`; `(starRingEnd ℂ).injective` closes it.
- A Lean-level contradiction among the hypotheses: none found; the model satisfies all of them together, and E × E satisfies them mathematically.
