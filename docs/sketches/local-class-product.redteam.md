# Red team: `local-class-product` (statement and proof)

Date: 2026-11-26. Worktree branch `track/local-class-product` from `62a6c1d`, uncommitted `HodgeLadder/Local/ClassProduct.lean` (namespace `HodgeLadder.LocalClassProduct`), `HodgeLadder/Tests/ClassProduct.lean` and the section "local-class-product: statement" of `docs/sketches/local-class-product.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same pin as `main`. The prover finished statement and proof in one phase, so this pass covers both.

Read: the ledger entries `local-class-product`, `cycle-class-multiplicative`, `cross-orientation`, `cap-cross-evaluation(-test)`; both Lean files; the sketch (plan, sub-rungs, the new section); `docs/sketches/cycle-class-multiplicative.md` (statement with `htr`, proof idea steps 3 to 7, glue statements, `cycle-class-germ`); the verdicts `cap-cross-evaluation.redteam.md`, `cross-orientation.redteam.md`, `triad-relative-cup-cap.redteam.md`, `triad-relative-cup-naturality.redteam.md`; `docs/conventions.md`; `docs/references.md`; the checked statements `cross_orientation_orient`, `orient`, `setA`, `setB`, `union_eq`, `complexAppendMap` (`HodgeLadder/Local/CrossOrientation.lean`), `cap_cross_evaluation` (`HodgeLadder/Cup/CapCrossEvaluation.lean`), `relCup2_eval_eq_eval_triadCap` (`HodgeLadder/Cup/TriadCupCap.lean`), `relCup2_naturality`, `relCup2_restrict`, `restrictToNeighborhood`, `isOpen_neighborhoodComplement` (`HodgeLadder/Cup/TriadCupNaturality.lean`); at the pin `neighborhoodSupportComplementPair`, `puncturedPair` (`Definitions/AlgebraicTopology/LocalHomology/FundamentalClass.lean`, both `abbrev`), `chartNormalProjectionPair`, `chartNormalProjectionCoclass` (`Definitions/.../NormalProjectionCoclass.lean`), `normalizedRelativeCoclass` (`Definitions/AlgebraicGeometry/Cycle/Local/Purity.lean`), `standardComplexLocalClass` (`ComplexClass.lean`), `TopPair.isoOfSubset` (`Mathlib/Topology/Category/TopPair.lean`), `chartNormalProjectionCoclass_apply_normalClass`, `relativeHomologyMap_complexMatrix_standardComplexLocalClass`.

Scratch: four files in `Scratch/` inside the worktree, checked with `lake env lean` against the worktree build after `lake build HodgeLadder.Local.ClassProduct HodgeLadder.Tests.ClassProduct` (the rung olean was older than its source; only that module rebuilt, 3.9 s; `lake build --no-build` showed nothing else out of date), then deleted. Nothing under `.lake/packages` was touched and no upstream or Mathlib module was built.

| File | Content | Result |
|---|---|---|
| RT1 | `#print axioms` on all 25 declarations of both files; (A) the model is not equal to minus its right side; (B) the consumer's planned `unionComplIsoNeighborhood V hT` (Closeds form, cycle-class-multiplicative sketch) equals `chartUnionIso V h` by `rfl`; (C) step 6 of the consumer in its own spellings: `relCup2_restrict`, two chart-coclass hypotheses, then the chart form, with Z W T : `Closeds Y` and a `by ring` degree proof | standard axioms on all 25; (A), (B), (C) compile |
| RT2 | trivial proofs of `relCup2_model` (`rfl`; `simp [relCup2, u, unionIso, projA, projB]`; `apply normalizedRelativeCoclass_unique <;> simp`) and of `relCup2_model_eval_orient` (`simp [orient, u]`) | all four fail |
| RT3 | the consumer's coordinates from `htr` (`φ z ⟨i, _⟩`, `φ z ⟨a + j, _⟩`) against `Fin.castAdd b`, `Fin.natAdd a` | both identities `rfl` |
| RT4 | the recommended corollary `chartNormalProjectionCoclass_eq_relCup2` and test `relCup2_model_ne_neg` (exact Lean in section 10) | compile, standard axioms |

`python3 tools/check.py --no-build` exits 0 with both files present (they are not imported from the root, so the checker reads them only in its sorry scan).

**The sign is +, exactly, for every a, b ≥ 0, and the statement does not force it.** The identity lives in a one-dimensional space, H^{2(a+b)}(ℂ^{a+b}, A ∪ B; ℚ), so the left side is λ times the right side for some λ ∈ ℚ, and the proof computes λ by pairing with the orientation class: `relCup2_model_eval_orient` is the kernel-checked value 1. A − anywhere in the inputs would make the stated equality false, not vacuous (the right side is nonzero, `relCup2_model_ne_zero`). I found no convention that hides a −1. In the complex setting every candidate sign is (−1)^{(2a)(2b)} = 1 except two, a real-parts-first identification ((−1)^{ab}) and a conjugated normal coordinate in one chart only ((−1)^a or (−1)^b); upstream uses neither, and the hypotheses `hnZ`, `hnW` rule out the second (section 6).

**Verdict: pass with changes.** Both forms are the literature's statement at full strength for the local model, exact, sign-visible, not trivially provable, and proved with the standard axioms. The chart form fits `cycle-class-multiplicative` step 6 with the checked `relCup2_restrict` in the consumer's Closeds spelling (RT1 C). The changes are posting records, one sign-separation test, one optional corollary in the direction the consumer reads, and a note to the consumer sketch (section 10).

## 1. Is this the statement the literature makes?

Source. [`MilnorStasheff1974`; section numbers unverified]: the Thom class of a product of oriented bundles is the cross product of the Thom classes, for the product orientation; the canonical orientation of a complex vector space comes from the real basis (v₁, iv₁, v₂, iv₂, …), so the complex orientation of a direct sum is the product orientation. [`Hatcher2002` §3.2]: the relative cup H^k(X, A) × H^l(X, B) → H^{k+l}(X, A ∪ B) for A, B open, and the relative cross product a × b = p₁*a ⌣ p₂*b in H^*(X × Y, A × Y ∪ X × B). For trivial bundles over a point, with ℂ^a × ℂ^b = ℂ^{a+b} and (ℂ^a × ℂ^b) ∖ 0 = (ℂ^a ∖ 0) × ℂ^b ∪ ℂ^a × (ℂ^b ∖ 0), the statement reads u_a × u_b = u_{a+b}.

Model form, field by field:

| Field | Literature | Lean | Match |
|---|---|---|---|
| local Thom class u_k | the generator of H^{2k}(ℂ^k, ℂ^k ∖ 0) that is 1 on the complex orientation | `u k = normalizedRelativeCoclass (standardComplexLocalClass ℚ k) _`, upstream's definition, the same class `chartNormalProjectionCoclass` pulls back (it uses `standardComplexLocalClass_ne_zero_for_chart`, a proof of the same `Prop`) | yes. Upstream's orientation class is the complex orientation: consecutive (Re, Im) coordinates, reference simplex sign (−1)^{2k} = + (register row "Complex orientation of ℂ^p") |
| identification ℂ^a × ℂ^b = ℂ^{a+b} | (z', z'') ↦ (z', z'') | `Fin.append`; `projA` reads `Fin.castAdd b` (first block), `projB` reads `Fin.natAdd a` (last block) | yes, first factor first, the order of `cross-orientation` and of `htr` |
| A, B | (ℂ^a ∖ 0) × ℂ^b, ℂ^a × (ℂ^b ∖ 0) | `setA = {z' ≠ 0}`, `setB = {z'' ≠ 0}`, open (`isOpen_setA`, `isOpen_setB`) | yes |
| cross product | p₁*u_a ⌣ p₂*u_b, relative cup | `relCup2 (cx a b) (setA a b) (setB a b) _ _ (projA^* u a) (projB^* u b)`, A factor first | yes; `relCup2` is Hatcher's relative cup (register row "Triad relative cup product", `forgetRel_relCup2`) |
| target pair | (ℂ^{a+b}, ℂ^{a+b} ∖ 0) | `(unionIso a b).inv^* (u (a + b))` on (ℂ^{a+b}, setA ∪ setB); `unionIso` is `isoOfSubset (Homeomorph.refl _)` | yes; the same map `orient` uses |
| degree | 2a + 2b = 2(a + b) | `2 * (a + b)` with `(Nat.mul_add 2 a b).symm` as the `Prop` argument of `relCup2` | yes, no cast on either side |
| sign | + | equality, no scalar | yes |

Full strength. For the local model this is the literature's identity, exact, for every a, b ≥ 0 including a = 0 or b = 0 (then A or B is empty and u_0 pulls back to the unit). A stronger statement exists: the real form u^ℝ_m × u^ℝ_n = u^ℝ_{m+n} in every pair of real dimensions, where factor order is sign-visible ((−1)^{mn}). `cross_orientation_real` holds the homology half of it. The ladder does not need it; it could be a new optional rung if a later consumer wants an odd-degree test of `relCup2`'s factor order.

Chart form. The literature's form is "in local holomorphic coordinates adapted to transversal Z and W, the local class of Z ∩ W is the product of the local classes". The Lean form takes three charts eZ, eW, eT in upstream's `E × (Fin c → ℂ)` shape, each adapted to its set on its own source (upstream's `hS`, verbatim), and ties their normal coordinates on V: z' = first a of eT's, z'' = last b of eT's. It concludes `relCup2` of the two chart coclasses = `(chartUnionIso V _).hom^*` of the chart coclass of T. That is the literature's statement transported along the normal projection w ↦ (eT w).2; it assumes less (no holomorphy, V any subset, T arbitrary off V) and concludes the same identity.

## 2. Can the hypotheses be satisfied?

The model form has no hypotheses. The chart form: `HodgeLadder.Tests.coordinate_hyps` meets every hypothesis on M = ℂ^{a+b} with Mathlib's `Fin.appendHomeomorph`, `Homeomorph.prodComm`, `Homeomorph.uniqueProd`, Z = {z' = 0}, W = {z'' = 0}, T = {0}, all by `rfl`; `coordinate_chartForm_ne_zero` instantiates the chart form's right side on upstream's `flattenedSupportNeighborhood` of 0 (which contains 0 ∈ T ∩ V) and shows it is nonzero through upstream's `chartNormalProjectionCoclass_apply_normalClass`. In the consumer, the three charts come from the single chart φ of `htr`; RT3 checks that φ's coordinate pattern (`⟨i, _⟩`, `⟨a + j, _⟩`) matches `Fin.castAdd b`, `Fin.natAdd a` definitionally, so `hnZ`, `hnW` are `rfl` there once eT's normal coordinate is k ↦ φ z ⟨k, _⟩.

## 3. Is the conclusion trivially true?

No.

- Both sides live in a nonzero space and the right side is nonzero (`relCup2_model_ne_zero`, `coordinate_chartForm_ne_zero`). RT1 (A) proves the model is not equal to minus its right side.
- RT2: `rfl`, `simp` with all local definitions unfolded, and `normalizedRelativeCoclass_unique` closed by `simp` each fail on `relCup2_model`; `simp [orient, u]` fails on `relCup2_model_eval_orient`. The prover reports `rfl`, `simp`, `aesop`, `decide`, `trivial`, `norm_num`, `grind`, `exact?` failing on all three statements.
- No hypothesis is unused: `hT` types the T coclass and feeds `chart_mem_iff`; `hVT` types it; `hnZ`, `hnW` give the three pair-map identities; `hA`, `hB` type `relCup2`. No `ℕ∞`, no empty index type: `Fin 0` occurs only as the tangential factor of the test chart for T, where it is correct.
- `eval_relCup2_degree` is a degree transport proved by `subst`; it carries no scalar. `relativeCohomologyMap_normalizedRelativeCoclass` is a genuine lemma (its `hz` is implied by `hfz`, harmless).

## 4. Interface rung?

No. The rung adds no structure and no axioms; it proves theorems about upstream's definitions (decision 0003).

## 5. Axioms and names

`#print axioms` (RT1) on every declaration of both files: `cx`, `isOpen_setA`, `isOpen_setB`, `projA`, `projB`, `u`, `unionIso`, `relCup2_model_eval_orient`, `eval_relCup2_degree`, `relativeCohomologyMap_normalizedRelativeCoclass`, `relCup2_model`, `chartUnionIso`, `chart_mem_iff`, `isOpen_chart_notMem`, `relCup2_chartNormalProjectionCoclass` (namespace `HodgeLadder.LocalClassProduct`) and `relCup2_model_ne_zero`, `Cab`, `chartZ`, `chartW`, `chartT`, `setZ`, `setW`, `setT`, `coordinate_hyps`, `coordinate_chartForm_ne_zero` (namespace `HodgeLadder.Tests`): `[propext, Classical.choice, Quot.sound]` on every one. The ledger entry names no declarations yet (status `open`); the posting change C1 lists them. `check.py --no-build` exits 0 but reads axioms only for ledger-named declarations of imported modules, so it does not yet cover these.

The test helpers `Cab`, `setZ`, `setW`, `setT`, `chartZ`, `chartW`, `chartT` are short names in `HodgeLadder.Tests`; a grep of `HodgeLadder/Tests/` finds no clash at `62a6c1d`.

## 6. Conventions and the sign

Independent recomputation from the statements of the checked inputs (each step read off the Lean type, none carries a sign):

| Step | Statement used | Sign |
|---|---|---|
| orient a b = append_*(s_a × s_b) | `cross_orientation_orient` | + |
| ⟨c, f_* z⟩ = ⟨f^* c, z⟩ | upstream `relativeCohomologyEquivDualHomology_relativeCohomologyMap` | none |
| append^* relCup2 = relCup2 of the pullbacks | `relCup2_naturality` (A factor first on both sides) | none |
| append ≫ projA = pr₁, append ≫ projB = pr₂ as maps of pairs | `Fin.append_left`, `Fin.append_right`, on points | identity |
| ⟨relCup2 φ ψ, z⟩ = ⟨ψ, φ ⌢ z⟩ | `relCup2_eval_eq_eval_triadCap` | none |
| ⟨pr₂^*ψ, pr₁^*φ ⌢ (x × y)⟩ = ⟨φ, x⟩⟨ψ, y⟩ | `cap_cross_evaluation` | none |
| ⟨u_k, s_k⟩ = 1 | upstream `normalizedRelativeCoclass_pairing_self` | 1 |
| uniqueness in a line | upstream `normalizedRelativeCoclass_unique`, `span_standardComplexLocalClass_eq_top_for_chart` | none |
| chart form | `relCup2_naturality` along w ↦ (eT w).2, three pair-map identities on points | none |

Product: 1 · 1 = 1. Independently, by the literature's conventions: with Hatcher's unsigned cup, ⟨p₁*φ ⌣ p₂*ψ, x × y⟩ = φ(x)ψ(y); a Koszul evaluation would insert (−1)^{|ψ||x|} = (−1)^{(2b)(2a)} = 1. The Thom class of a product is the cross product for the product orientation, and the complex orientation of ℂ^{a+b} in consecutive (Re, Im) coordinates is the product orientation of ℂ^a × ℂ^b. So + on both readings.

**Is a −1 hidden by a choice?** Each choice the rung makes, and what flipping it would do:

| Choice | Flip | Effect on the identity |
|---|---|---|
| Z factor first in `relCup2` | W first | (−1)^{(2a)(2b)} = 1 by graded commutativity; harmless, though `relCup2` graded commutativity is not at the pin, so a W-first statement would need a new lemma. The consumer forms cupSing(Ψ[Z], Ψ[W]) with Z first, matching |
| z' = first block (`Fin.castAdd`), z'' = last (`Fin.natAdd`) | blocks swapped in the T chart | a ℂ-linear permutation of ℂ^{a+b}: upstream `relativeHomologyMap_complexMatrix_standardComplexLocalClass` leaves s_{a+b} fixed, so the T coclass is unchanged; on real coordinates it is a block swap of sign (−1)^{(2a)(2b)} = 1 |
| identity shuffle and `Fin.append`, both first-factor-first | only one of them flipped | (−1)^{mn} with m = 2a, n = 2b: 1 |
| consecutive (Re, Im) coordinates (upstream) | real parts first | each u_k changes by (−1)^{k(k−1)/2}, the product formula by (−1)^{ab}: the one odd sign. Upstream does not use it |
| holomorphic normal coordinates | conjugate one coordinate of eZ only | (−1) on the Z coclass alone; excluded, since `hnZ` makes eZ's normal coordinate literally the first block of eT's |
| u_k normalized against upstream's s_k | s_k = ε_k · (true orientation) | the identity holds for both if ε is multiplicative (ε_a ε_b = ε_{a+b}); upstream's real reference sign (−1)^d is multiplicative and is + in even d anyway |

So the statement does not silently force +: the proof computes the sign, and every convention it fixes is either the literature's or invisible in even degrees. What this rung does not test: the factor order of `relCup2` (invisible here); that is tested at A = B = ∅ by `torusEval_cupSing_winding_swap` (row "Triad relative cup naturality").

Register: the rows "Complex orientation of ℂ^p", "Fundamental-class normalization", "Cross product of complex orientations", "Cap–cross evaluation", "Cup–cap adjunction (triad)", "Triad relative cup product", "Triad relative cup naturality", "Universal-coefficient evaluation", "Pair spellings of (X, X ∖ Z)" and "Holomorphic adapted chart" cover every input. One row was missing and is added: "Product of local classes (model and chart)". The identity is an equality, so its truth depends on all of these; a span statement would not.

Holomorphy. The chart form assumes none, and that is right: the identity is topological, a pullback of the model along the normal projection, and it holds for any three charts whose normal coordinates agree in the stated way. Holomorphy enters only in the consumer, where `cycle-class-germ` identifies each restricted cycle class with the chart coclass of a holomorphic adapted chart. The three charts the consumer builds from φ (φ followed by a ℂ-linear coordinate splitting) are holomorphic and satisfy `hnZ`, `hnW` by `rfl` (RT3), so the consumer meets both rungs' hypotheses with the same charts. One consumer seam to watch: when T is a point, the sketch proposes upstream's point form (`analyticComponentPointSupportedInjectiveCoclass_relative`) for T in place of `cycle-class-germ`. That class must then be matched with `chartNormalProjectionCoclass ET (a + b) eT T _` for the eT built from φ; the match is an orientation statement (upstream's `exists_open_chartNormalProjectionCoclass_eq` for two holomorphic charts) and belongs to `cycle-class-multiplicative`.

## 7. Equality first

Both forms are identities, proved exactly: no "up to a scalar", the sign + in the docstrings and in the register. The degree identity is a `Prop` argument, so no cast scalar can enter (`eval_relCup2_degree` by `subst`).

## 7b. Non-vacuity

Smallest test lemma that fails if the statement were trivially true: `HodgeLadder.Tests.relCup2_model_ne_zero` (exists, checked here with the standard axioms): `relativeCohomologyMap ℚ (2 * (a + b)) (unionIso a b).inv (u (a + b)) ≠ 0`, from upstream's `normalizedRelativeCoclass_pairing_self` and `relativeCohomologyEquivDualHomology_relativeCohomologyMap`. For the chart form, `HodgeLadder.Tests.coordinate_chartForm_ne_zero` (exists), from upstream's `chartNormalProjectionCoclass_apply_normalClass`. The sign test `relCup2_model_ne_neg` (RT4, change C2) makes the separation of + from − a named lemma; it is a three-line consequence of the two above, kept because the ledger should be able to cite it.

## 8. Pin drift

Checked at `2ead713`, the current pin; no drift. Drift list for the next bump (add to the sketch's list): upstream `chartNormalProjectionPair` (the `rfl` steps of `hpT` and the point identities of `hpA`, `hpB` read its body `fun w => (e w.1).2`), `chartNormalProjectionCoclass` (unfolded by `rw [eA, eB, …]`), `neighborhoodSupportComplementPair` and `puncturedPair` (both `abbrev`; the statement types `relCup2`'s arguments through them), `TopPair.isoOfSubset`, `TopPair.ofSubsetHom`, `normalizedRelativeCoclass`, `normalizedRelativeCoclass_unique`, `normalizedRelativeCoclass_pairing_self`, `standardComplexLocalClass`, `standardComplexLocalClass_ne_zero`, `standardComplexLocalClass_ne_zero_for_chart`, `span_standardComplexLocalClass_eq_top_for_chart`, `relativeCohomologyEquivDualHomology_relativeCohomologyMap`, `relativeCohomologyMap_comp`, `relativeCohomologyMap_id`, `relativeHomologyMap_comp`, `relativeHomologyMap_id`; for the tests `flattenedSupportNeighborhood`, `flattenedSupportNeighborhood_subset_source`, `flattenedSupportNormalClass`, `chartNormalProjectionCoclass_apply_normalClass`; Mathlib `Fin.appendHomeomorph`, `Homeomorph.prodComm`, `Homeomorph.uniqueProd`, `Fin.append_left`, `Fin.append_right`. A change that could alter truth: upstream renormalizing `standardComplexLocalClass` by a non-multiplicative factor, or changing the normal projection in `chartNormalProjectionPair`; both break the build here or in `cross-orientation` first.

## 9. Spelling seams for the consumer

RT1 (C) runs `cycle-class-multiplicative` step 6 in the consumer's own spellings: Z W T : `Closeds Y`, classes typed on `TopPair.ofSubset (Z.compl : Set Y)` (register row "Pair spellings", spelling (1)), `relCup2` with `Z.compl.isOpen` and a `by ring` degree proof. `rw [relCup2_restrict, hα, hβ, relCup2_chartNormalProjectionCoclass …]` fires: the restricted pairs `{w : V | w.1 ∉ (Z : Set Y)}` are syntactically the chart form's with Z := (Z : Set Y), the openness proofs `isOpen_neighborhoodComplement V Z` unify with the arguments `hA`, `hB`, and the degree proof unifies by proof irrelevance. The planned glue `unionComplIsoNeighborhood V hT` (Closeds form, `hT : T = Z ⊓ W`) is `chartUnionIso V h` by `rfl` (RT1 B), so the consumer can use `chartUnionIso` directly and drop that definition, or keep it with an `rfl` bridge.

## Answers to the prover's questions

1. **Three charts or one.** Three. `cycle-class-germ` delivers each class for a chart adapted to that component alone, so three charts is the shape the consumer has; one chart into E × ℂ^a × ℂ^b would force the consumer to rebuild the Z and W charts from it anyway, and the three-chart form is more general (it holds with no relation between eZ, eW, eT off V). If a one-chart corollary is wanted, it belongs to the consumer.
2. **`hA`, `hB` as arguments.** Keep them as arguments. Any proof the consumer has (`isOpen_neighborhoodComplement`, `isOpen_chart_notMem`) unifies; RT1 (C) uses the one `relCup2_restrict` produces.
3. **T as a parameter with `hT`.** Right. The consumer's T is its own `Closeds` (`cycleComponentAnalyticClosedSupport X t`), equal to Z ∩ W only through its `hT`; a statement with T := Z ∩ W would force a rewrite inside a dependent type. `chart_mem_iff` supplies the iso's proof, and the consumer's own proof is the same term up to proof irrelevance (RT1 B). Cosmetic: the chart form's `hT` (adapted chart) and the consumer's `hT` (T = Z ⊓ W) share a name; harmless, since they are positional.
4. **Degree.** `2 * (a + b)` with `(Nat.mul_add 2 a b).symm` is right: it is the degree of `chartNormalProjectionCoclass ET (a + b)` and of the consumer's `cup … (2 * (a + b)) (by ring)`, and needs no cast on either side.
5. **Test rung.** Yes: `local-class-product-test`, module `HodgeLadder.Tests.ClassProduct`, as for `cap-cross-evaluation-test` and `cross-orientation-test`.
6. **File name.** `HodgeLadder/Local/ClassProduct.lean`, matching the flat `HodgeLadder/Local/` (`CrossOrientation.lean`, `RealAffineOrientation.lean`); `HodgeLadder/Tests/ClassProduct.lean` likewise. The `Local/Class/Product.lean` hint occurs only in the prover's own note in the sketch (grep of the tree), so only that note changes.

## 10. Changes

| Id | Change | Kind |
|---|---|---|
| C1 | Post: import `HodgeLadder.Local.ClassProduct` and `HodgeLadder.Tests.ClassProduct` from `HodgeLadder.lean`; ledger `local-class-product` checked, module `HodgeLadder.Local.ClassProduct`, declarations the 15 of the rung file (section 5) plus C3 if adopted, register row "Product of local classes (model and chart)", red-team file; new rung `local-class-product-test` (kind test, depends on `local-class-product`), module `HodgeLadder.Tests.ClassProduct`, declarations the 10 of the test file plus C2; roadmap row; then rerun `python3 tools/check.py` so the axioms line covers them | required |
| C2 | Add the sign test below to `HodgeLadder/Tests/ClassProduct.lean` | required |
| C3 | Add the `inv` corollary below to the rung file: it is the form step 6 reads, the class on `neighborhoodSupportComplementPair V T` | optional |
| C4 | Consumer sketch (`docs/sketches/cycle-class-multiplicative.md`, glue statements): replace `unionComplIsoNeighborhood V hT` by `chartUnionIso V _` from this rung (equal by `rfl`), or keep it with an `rfl` lemma; state `unionComplIso_restrict` against it; note the point-form seam of section 6 | required before `cycle-class-multiplicative` |
| C5 | `docs/gaps.md`, "To upstream": `relativeCohomologyMap_normalizedRelativeCoclass` (a statement about upstream's `normalizedRelativeCoclass` alone; destination upstream, next to `normalizedRelativeCoclass_unique`) | required |
| C6 | Sketch: the plan paragraph "Chart form (the rung id `local-class-product` itself)" in section "Statement" describes one chart with T = Z ∩ W; add one line pointing to the stated three-chart form; add section 8's drift list to "Pins and drift"; module docstring of the rung file: cite the new register row next to the four it already cites | required |

C2 (RT4, compiles, standard axioms):

```lean
/-- The model form separates `+` from `-`: the model product is not minus `u_{a+b}`. -/
theorem relCup2_model_ne_neg (a b : ℕ) :
    relCup2 (cx a b) (setA a b) (setB a b) (isOpen_setA a b) (isOpen_setB a b)
        (relativeCohomologyMap ℚ (2 * a) (projA a b) (u a))
        (relativeCohomologyMap ℚ (2 * b) (projB a b) (u b)) (2 * (a + b))
        (Nat.mul_add 2 a b).symm ≠
      -relativeCohomologyMap ℚ (2 * (a + b)) (unionIso a b).inv (u (a + b)) := by
  rw [relCup2_model]
  intro h
  have h2 : (2 : ℚ) • relativeCohomologyMap ℚ (2 * (a + b)) (unionIso a b).inv (u (a + b)) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact relCup2_model_ne_zero a b ((smul_eq_zero.mp h2).resolve_left two_ne_zero)
```

C3 (RT4, compiles, standard axioms; in `section Charts` of the rung file, same variables):

```lean
/-- The chart form read on `(V, V ∖ T)`: the pullback along `chartUnionIso.inv` of the triad
relative cup of the chart coclasses of `Z` and `W` is the chart coclass of `T`. Sign `+`. -/
theorem chartNormalProjectionCoclass_eq_relCup2
    (eZ : OpenPartialHomeomorph M (EZ × (Fin a → ℂ)))
    (eW : OpenPartialHomeomorph M (EW × (Fin b → ℂ)))
    (eT : OpenPartialHomeomorph M (ET × (Fin (a + b) → ℂ)))
    (Z W T : Set M)
    (hZ : ∀ y ∈ eZ.source, y ∈ Z ↔ (eZ y).2 = 0)
    (hW : ∀ y ∈ eW.source, y ∈ W ↔ (eW y).2 = 0)
    (hT : ∀ y ∈ eT.source, y ∈ T ↔ (eT y).2 = 0)
    (V : Set M) (hVZ : V ⊆ eZ.source) (hVW : V ⊆ eW.source) (hVT : V ⊆ eT.source)
    (hnZ : ∀ y ∈ V, (eZ y).2 = fun i => (eT y).2 (Fin.castAdd b i))
    (hnW : ∀ y ∈ V, (eW y).2 = fun j => (eT y).2 (Fin.natAdd a j))
    (hA : IsOpen {w : V | w.1 ∉ Z}) (hB : IsOpen {w : V | w.1 ∉ W})
    (h : ∀ y ∈ V, y ∈ T ↔ y ∈ Z ∧ y ∈ W) :
    relativeCohomologyMap ℚ (2 * (a + b)) (chartUnionIso V h).inv
        (relCup2 (TopCat.of V) {w : V | w.1 ∉ Z} {w : V | w.1 ∉ W} hA hB
          (chartNormalProjectionCoclass EZ a eZ Z hZ V hVZ)
          (chartNormalProjectionCoclass EW b eW W hW V hVW) (2 * (a + b))
          (Nat.mul_add 2 a b).symm) =
      chartNormalProjectionCoclass ET (a + b) eT T hT V hVT := by
  rw [relCup2_chartNormalProjectionCoclass eZ eW eT Z W T hZ hW hT V hVZ hVW hVT hnZ hnW,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp, Iso.inv_hom_id,
    relativeCohomologyMap_id, LinearMap.id_apply]
```

The `h` argument lets the consumer pass its own proof from `hT : T = Z ⊓ W`; `chartUnionIso V h` is the same term for every `h`.

## What I tried that did not break it

- Making the model false or trivial: the trivial tactics of RT2; uniqueness without the pairing input (fails, the pairing is the content).
- Making the sign depend on an order: each row of the table in section 6. Only the real-parts-first identification and a one-chart conjugation give an odd sign; the first is not upstream's, the second is excluded by `hnZ`, `hnW`.
- Breaking the consumer seam: Closeds spellings, the `by ring` degree proof, the openness proofs of `relCup2_restrict`, the planned `unionComplIsoNeighborhood` (RT1 B, C); all go through.
- Finding an unused hypothesis or a degenerate index: none (section 3).
