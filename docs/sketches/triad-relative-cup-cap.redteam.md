# Red team: `triad-relative-cup-cap` (statement)

Date: 2026-11-26. Worktree branch `track/triad-relative-cup-cap` at base `c486870`, uncommitted `HodgeLadder/Cup/TriadCapPins.lean`, `HodgeLadder/Cup/TriadCupCap.lean` and the section "triad-relative-cup-cap: statement" of `docs/sketches/local-class-product.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713` (`lakefile.toml`; the package source in `.lake/packages` is at the same commit), Lean and Mathlib `v4.35.0-rc4`. `main` is one commit ahead (`d89ec00`, `relative-cross-triad-naturality`), with the same pin.

Read: the ledger entries `triad-relative-cup-cap`, `triad-relative-cup`, `local-class-product`, and on `main` `triad-cap-naturality`, `local-class-cross-model`; both Lean files; the sketch section and the statement of `local_class_cross_cap` in the same sketch; findings 3 and 8 of `docs/sketches/triad-relative-cup.redteam.md`; hand computation 5 and section 8 of `docs/sketches/cycle-class-multiplicative.redteam.md`; `docs/conventions.md`; `docs/references.md`; the checked `HodgeLadder/Cup/TriadCup.lean` and `HodgeLadder/Tests/TriadCupTorus.lean`; at the pin `Other/AlgebraicTopology/Singular/Cap/Simplicial.lean` (`frontInclusion`, `backInclusion`, `frontFace`, `backFace`, `chainOfSimplex`, `capHom`, `cap`, `iota_capHom`, `cap_chainOfSimplex`), `Cap/Relative.lean` (`relativeCohomologyCycleToCocycle`, `RelativeCochainCohomology`, `relativeCochainCohomologyEquiv`), `Cap/Triad.lean` (all of it), `Definitions/Algebra/Homology/LinearDual.lean` (`linearDualCochainComplex`, `linearDualCochainComplexScIso`, `linearDualMap`, both `linearDualHomologyEquiv`), `Lemmas/Algebra/Homology/LinearDualNaturality.lean`, `Definitions/AlgebraicTopology/Singular/Cohomology.lean` (`RelativeCochainComplex`, `relativeCohomologyEquivDualHomology`), `Lemmas/AlgebraicGeometry/Cycle/Local/Purity.lean` (`normalizedRelativeCoclass_unique`); Tau Ceti's `cochainValuesEquiv_cupCochain_alexanderWhitneyDiagonal`, `iCycles_cupCycles`; the port's `LefschetzPort/AlgebraicTopology/LinearDualConnecting.lean`.

Scratch (inside the worktree in `RTScratch/`, deleted afterwards): RT1, RT2 prove the open sub-lemma `triadEval_relCup2` and rederive the adjunction from it; RT3 elaborates six more pins; RT4 proves a non-vacuity corollary from the checked torus test; RT5 is `TriadCupCap.lean` with the `sorry` replaced by the proof of Appendix A, compiled sorry-free; RT6 prints its axioms; RT7 tries trivial closers.

**Verdict: pass with changes.** The adjunction is Hatcher's relative cup–cap identity at full strength for rational coefficients: every p, q, every open A, B, every class, no sign, with the A factor capping on the front face. The open sub-lemma `triadEval_relCup2` is true: it is proved in scratch along the sketch's route, standard axioms, and with it the whole file is sorry-free (Appendix A), so the rung can land as `checked` in one step. The pins are faithful. The changes: put the proof in, add six pins (two of them the ones the sketch asks about), list the declarations, fix two sentences of the sketch and the `Hatcher2002` row, optionally add a non-vacuity corollary, and rebase on `main`.

## 1. Is this the statement the literature makes?

Source: [`Hatcher2002` §3.3; section recalled, page and statement numbers not re-read, and `docs/references.md` lists the key with §3.2 only, see change 6]. Hatcher writes the cap with the chain on the left, C_k(X; R) × C^l(X; R) → C_{k−l}(X; R), σ ⌢ φ = φ(σ|[v₀, …, v_l]) σ|[v_l, …, v_k], and proves ψ(σ ⌢ φ) = (φ ⌣ ψ)(σ) for φ ∈ C^l, ψ ∈ C^{k−l}, σ : Δ^k → X, with the cup front face times back face (§3.2). For A, B open the same formulas give the relative cap H_n(X, A ∪ B; R) × H^l(X, A; R) → H_{n−l}(X, B; R) through C_n(X, A + B), and the identity holds on homology.

| Hatcher | Lean | Check |
|---|---|---|
| R a commutative ring | ℚ | narrower, forced: `relCup2` is defined over ℚ and `relativeCohomologyEquivDualHomology` needs a field |
| φ ∈ H^l(X, A), the capping class | `φ : RelativeCohomology ℚ (TopPair.ofSubset A) p`, first argument of `relCup2` and of the cap | same; the A factor caps and is the first cup factor |
| ψ ∈ H^{n−l}(X, B), the evaluating class | `ψ : RelativeCohomology ℚ (TopPair.ofSubset B) q` | same |
| σ ∈ H_n(X, A ∪ B) | `z : RelativeHomology ℚ (TopPair.ofSubset (A ∪ B)) (p + q)` | same; degree `p + q` with `relCup2 … (p + q) rfl` |
| σ ⌢ φ = φ(front l-face) · back face | upstream `capHom`: x ↦ φ(chainOfSimplex (frontFace x)) • chainOfSimplex (backFace x); `frontInclusion` i ↦ i, `backInclusion` i ↦ p + i | same formula; upstream writes the cochain on the left, which changes notation only |
| φ ⌣ ψ = φ(front) · ψ(back) | Tau Ceti AW cup with `subinterval 0 p`, `subinterval p q` (register row "Singular cup product") | same faces: `frontInclusion_eq_subinterval`, `backInclusion_eq_subinterval` (proved) |
| ψ(σ ⌢ φ) = (φ ⌣ ψ)(σ) on chains | `cupCochain_eq_capLift` on C_{p+q}(X) | same identity, proved in the file |
| C_n(X, A + B) and excision for A, B open | upstream `triadRelativeChainComplex` (cokernel of C(A) ⊞ C(B) → C(X)), `triadToUnionRelativeChainMap_quasiIso_of_isOpen` | same complex and same comparison, induced by the identity of C(X) |
| pairing ⟨[c], [x]⟩ = c(x) | upstream `relativeCohomologyEquivDualHomology` = `linearDualHomologyEquiv` on (X, A ∪ B) and on (X, B) | same, no sign (port lemma `HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply`, used in Appendix A) |

The statement quantifies over all p, q, φ, ψ, z and all open A, B in any `X : TopCat.{0}`, so it is Hatcher's identity at full strength over ℚ. It is the left-cap version (the A factor caps, evaluated on front faces) because that is the cap upstream defines; the right-cap identity ⟨φ ⌣ ψ, z⟩ = ⟨φ, z ⌢ ψ⟩ would need a back-face cap upstream does not have, and the consumer does not need it. The sum-relative sub-lemma `triadEval_relCup2` keeps the openness hypotheses only because `relCup2` needs them; that is harmless.

## 2. Can the hypotheses be satisfied?

Yes, for every space: A = B = ∅ with `isOpen_empty`; the theorem quantifies over all classes, with no other hypothesis. On the consumer's spaces A = `setA a b`, B = `setB a b` (open, `isOpen_setA`, `isOpen_setB` in the sketch), and on the cup-side route of `local-class-cross-model` (`main`) the product space `TopCat.of (Fin a → ℂ) ⊗ TopCat.of (Fin b → ℂ)` with `leftProdSet`, `rightProdSet`; both are `TopCat.{0}` objects with open subsets, so the theorem applies as stated. A non-vacuous instance (RT4, compiled): with A = B = ∅ and p = q = 1, the checked torus test `torusEval_relCup2_winding` gives a z with ⟨relCup2 a₁ a₂, z⟩ ≠ 0 (Appendix C), so both sides of the adjunction are nonzero there.

## 3. Is the conclusion trivially true for a reason unrelated to the mathematics?

No. RT7: `rfl`, `with_reducible rfl`, `unfold relCup2 triadCapCohomologyLinear; rfl` and `simp [relCup2, triadCapCohomologyLinear, relativeCohomologyEquivDualHomology]` fail on `triadEval_relCup2`, and `rfl` fails on the adjunction; the sketch reports `simp`, `aesop`, `exact?`, `decide`, `norm_num` failing. The proof that works (Appendix A, about 120 lines with its helper) uses content at every step: representatives for both classes and the homology class, the cocycle formula of `relCup2`, the epimorphism C(X) → C(X)/(C(A) + C(B)), Tau Ceti's Alexander–Whitney formula, upstream's `iota_capHom`, and the short-complex descent of the cap. No definition unfolds to `True`, no index type is empty, no `ℕ∞` appears, and `hA`, `hB` are used (in `relCup2` and in excision). The identity is not vacuous by both sides vanishing: Appendix C.

One structural observation, which does not make the statement trivial: the adjunction is insensitive to a nonzero scalar on the excision comparison `triadToUnionRelativeChainMap`, since that map enters both sides only through its inverse (in `triadExcisionCoh⁻¹` on the left and in `triadUnionExcisionHomologyEquiv.symm` on the right). The comparison's normalization is fixed elsewhere: by `forgetRel_relCup2` (checked) and by the value 1 of `local_class_cross_cap`. Recorded in the new register row.

## 4. Interface rung

Not applicable: no structure, no axioms (decision 0003). The rung is an identity between upstream's cap and this repository's `relCup2`.

## 5. Checker

The rung is not checked. `python3 tools/check.py --no-build` in the worktree: one failure, `REJECTED (sorry: HodgeLadder/Cup/TriadCupCap.lean:124)`, the statement-phase `sorry` in `triadEval_relCup2`; everything else accepted. `#print axioms` in scratch: `frontInclusion_eq_subinterval`, `backInclusion_eq_subinterval`, `cupCochain_eq_capLift` and the pins `cap_chainOfSimplex_eq`, `triadCapShortComplexHom_τ₂_eq`, `triadRelativeChainProjection_triadCapHom_eq`, `unionRelativeTriadCapCohomologyLinear_apply_eq` depend on `[propext, Classical.choice, Quot.sound]`; `relCup2_eval_eq_eval_triadCap` adds `sorryAx` (through the sub-lemma), as expected. In RT5/RT6, with Appendix A in place, `triadEval_relCup2`, `relCup2_eval_eq_eval_triadCap`, `relCup2_dual_eq` and the two helpers depend on the three standard axioms only. The declarations are the ones the ledger title means: `unionRelativeTriadCapCohomologyLinear` is upstream's customary triad cap, and the pairings are upstream's `relativeCohomologyEquivDualHomology`. The ledger's `module` is `null` and `declarations` is empty, to be filled when the rung lands (change 3).

## 6. Conventions

| Convention | Where | Check | Truth depends on it? |
|---|---|---|---|
| cap formula φ(front p-face) • back q-face, no sign | upstream `capHom`, `cap_chainOfSimplex` | pinned (`capHom_eq`, `cap_chainOfSimplex_eq`) | yes: a sign (−1)^{pq} or (−1)^p, or front and back swapped, makes the identity false in odd degrees |
| front face vertices 0, …, p; back face p, …, p + q | upstream `frontInclusion`, `backInclusion`; Mathlib `subinterval 0 p`, `subinterval p q` in Tau Ceti's AW | pinned (`frontInclusion_val`, `backInclusion_val`) and identified (`frontInclusion_eq_subinterval`, `backInclusion_eq_subinterval`, proved) | yes |
| cup: A factor first, front times back, μ = `(λ_ _).hom` | `relCup2` (row "Triad relative cup product") | `triadProj_cupCochain` (checked) with `cupCochain_eq_capLift` | yes |
| homology map of the cap reads τ₂ only | upstream `triadCapShortComplexHom`, `triadCapShortComplexHom_τ₂` | pinned (`triadCapShortComplexHom_τ₂_eq`); the proof in Appendix A uses only `ShortComplex.cyclesMap_i` and τ₂, so the (−1)^p of τ₁, τ₃ (`triadCapShortComplexHomSucc_τ₁_eq`, `_τ₃_eq`, and τ₁ of `triadCapShortComplexHomZero`) does not enter. The (−1)^p is the one Hatcher's ∂(σ ⌢ φ) = (−1)^p (∂σ ⌢ φ − σ ⌢ δφ) forces on the outer maps | yes, through τ₂ |
| short-complex model of relative cohomology | upstream `relativeCochainCohomologyEquiv` = homology of `linearDualCochainComplexScIso` (`isoSc'`, identities on components), `relativeCohomologyCycleToCocycle` (same cochain) | pinned (`relativeCochainCohomologyEquiv_symm_eq`, `relativeCohomologyCycleToCocycle_val`); identities on representatives (Appendix A, `hc`, closed by `rfl` after `cyclesMap_i`) | yes; no sign or scalar |
| universal-coefficient evaluation ⟨[c], [x]⟩ = c(x) | upstream `linearDualHomologyEquiv`; port `HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply` | row "Universal-coefficient evaluation"; used on both sides | yes, but the same map on both sides |
| upstream cochains to Tau Ceti cochains | `dualIsoYoneda` (componentwise `homLinearEquiv.symm`) | no degree sign (row "Triad relative cup product") | yes |
| excision comparison induced by 𝟙 of C(X) | upstream `triadToUnionRelativeChainMap` | restated lemma pin proposed (change 2); the identity is insensitive to a scalar here (section 3) | no, for this identity; yes for its consumers |

Borrowed results: `HomologicalComplex.linearDualHomologyEquiv_naturality` (upstream, a naturality statement with no sign, used in the reduction), `triadToUnionRelativeChainMap_quasiIso_of_isOpen` (a quasi-isomorphism statement about the very map used), `TopCat.cochainValuesEquiv_cupCochain_alexanderWhitneyDiagonal` (Tau Ceti, front times back, row "Singular cup product"), `Simplicial.iota_capHom` (upstream `Other`, the cap formula itself), `HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply` (port, evaluation, proved from upstream's definitions). Each states its convention against the same definitions the theorem uses. Register: new row "Cup–cap adjunction (triad)" added to `docs/conventions.md` after "Universal-coefficient evaluation" (kept clear of the rows `main` edited in `d89ec00`, to avoid a merge conflict). The row "Triad relative cup product" still says "kernel check pending in the rung" although `triad-relative-cup` is checked; it is adjacent to the row `main` edited, so update it after the rebase (change 8).

**Consumer degrees.** `local-class-product` uses p = 2a, q = 2b. There (−1)^p = (−1)^q = (−1)^{pq} = 1, so a sign of any of these shapes in either product would be invisible to the consumer. The statement is stronger than the consumer needs, and the proof for all p, q is what excludes those signs; keep it at full strength.

## 7. Equality first

The adjunction is an identity of rational numbers for all inputs, proved exactly in scratch (Appendix A), with no scalar and no sign; `relCup2_dual_eq` is the same identity as linear forms. It is the step that turns `local_class_cross_cap` (cap form, value 1) into the hypothesis `hβ : relativeCohomologyEquivDualHomology R X n β z = 1` of upstream's `normalizedRelativeCoclass_unique`, which gives the equality `relCup2 … = normalizedRelativeCoclass (orient a b) _` of `local-class-product`; that rung and `cycle-class-multiplicative` ([Z] ∪ [W] = [T]) exist, both open. Degree check: with p = 2 * a, q = 2 * b the left side is `relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (setA a b ∪ setB a b)) (2 * a + 2 * b) (relCup2 … (2 * a + 2 * b) rfl) (orient a b)`, the degree of `orient a b` syntactically, and the excision term of the right side is `triadToUnionRelativeChainMap_quasiIso_of_isOpen _ _ _ (isOpen_setA a b) (isOpen_setB a b)`, the term of `local_class_cross_cap` (and any other proof of `QuasiIso` is equal by proof irrelevance).

## 7b. Non-vacuity

Smallest test that fails if the statement were trivially true (both sides identically 0): `exists_eval_relCup2_ne_zero` (Appendix C, compiled in RT4), in `HodgeLadder.Tests`, from the checked `HodgeLadder.Tests.torusEval_relCup2_winding`, `HodgeLadder.Cup.forgetRel_relCup2`, and upstream's `relativeCohomologyEquivDualHomology` (a `LinearEquiv`, so injective) and `isOpen_empty`. It does not exist yet (change 5, optional). It covers A = B = ∅ and odd degrees p = q = 1. The sign-visible test with both subspaces nonempty remains `local-class-cross-model` at a = b = 1 (open).

## 8. Pin drift

Not applicable as a diff: the rung has no checked version, and the worktree, `main` and the package source are all at `2ead713`. The pins module is the drift guard for upstream's unguarded `Other` cap. It guards, by `rfl` (23 pins) or by restating an upstream lemma with its right side written out (3 pins), the following, so that a change of any of them breaks the build in this repository:

| Step | Guarded declarations |
|---|---|
| simplex cap | `frontInclusion`, `backInclusion` (vertex maps), `frontFace`, `backFace`, `capHom` (body), `cap`, `cap_chainOfSimplex` (statement) |
| relative cap | `relativeCochainToAbsolute`, `relativeCapLift` |
| triad chain level | `triadCapLiftHom`, `triadCap`, `triadCap_projection_apply` (statement; with the epimorphism this fixes `triadCapHom`) |
| signs | `triadCapShortComplexHom_τ₂` (statement), τ₁ and τ₃ of `triadCapShortComplexHomSucc` |
| descent | `triadCapHomologyMap`, `triadCapCocycleHomologyLinear`, `triadCapCochainCohomologyLinear`, `triadCapCohomologyExplicitLinear` (on `mk`), `relativeCohomologyCycleToCocycle` (value), `triadCapCohomologyLinear`, `relativeCochainCohomologyEquiv` (inverse) |
| excision inverse | `triadToUnionRelativeHomologyMap`, `triadUnionExcisionHomologyEquiv` (inverse), `unionRelativeTriadCapCohomologyLinear` |

Not guarded, and proposed (change 2, all compiled in RT3): `triadSubspaceChainMap`, `triadRelativeChainComplex`, `triadRelativeChainProjection`, `triadToUnionRelativeChainMap` (by `rfl` and by restating `triadRelativeChainProjection_triadToUnionRelativeChainMap`), τ₁ of `triadCapShortComplexHomZero`, and `chainOfSimplex`. On `main`, `HodgeLadder.Relative.triadSubspaceChainMap_eq` (rung `relative-cross-triad-naturality`) already pins `triadSubspaceChainMap` for ℚ in the `singChainFunctor` spelling; the proposed pin is general in `R` and lives in `HodgeLadder.Cup.TriadCapPins`, so the names do not collide, though opening both namespaces would make `triadSubspaceChainMap_eq` ambiguous. A change of `triadToUnionRelativeChainMap` away from "induced by the identity" would leave this identity true (section 3) and change its consumers; the restated lemma pin is the guard that matters. Once the rung is checked, the proof itself breaks on any change of the definitions it unfolds; the pins add a named failure and a record of the convention. Add the six pinned names to the drift list for the next bump.

## Findings

1. **The statement is the literature's** (section 1): Hatcher's relative cup–cap identity over ℚ, all degrees, the A factor capping on the front face, no sign. No change.
2. **The open sub-lemma is true and the planned route is sound.** `triadEval_relCup2` is proved in scratch (Appendix A), standard axioms, following steps 2 to 4 of the sketch's route. One simplification: the bridge lemma of step 1 is needed only once, on the cap side (`relativeCochainCohomologyEquiv_symm_homologyπ`, one term); both pairings go through the port's `HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply`, which evaluates `linearDualHomologyEquiv` on `homologyπ` classes directly. Change 1.
3. **Sign rechecked independently.** By hand on σ : Δ² → X with p = q = 1: (φ ⌣ ψ)(σ) = φ([v₀, v₁]) ψ([v₁, v₂]) and ψ(φ ⌢ σ) = ψ(φ([v₀, v₁]) [v₁, v₂]), equal; for p = 0 both are φ(v₀) ψ(σ), for q = 0 both are φ(σ) ψ(v_p). In Lean, `cupCochain_eq_capLift` proves the chain identity for all p, q, and Appendix A shows that the homology map of the cap reads only τ₂ = `triadCapHom`; the (−1)^p on τ₁, τ₃ does not enter. No sign anywhere.
4. **Consumer fit** (section 7): degree `2 * a + 2 * b` syntactically, the same excision term as `local_class_cross_cap`, and the left side is exactly `hβ` of `normalizedRelativeCoclass_unique`. The theorem also applies on the product space of the cup-side route recorded on `main`. No change.
5. **Pins are faithful.** Each of the 23 `rfl` pins restates upstream's definition body (or its `rfl` lemma: `frontInclusion_val` is upstream's `frontInclusion_apply`, `backInclusion_val` is `backInclusion_apply`); `cap_chainOfSimplex_eq` restates `cap_chainOfSimplex` with `frontFace`, `backFace` unfolded; `triadRelativeChainProjection_triadCapHom_eq` restates `triadCap_projection_apply` with `triadCapLift` unfolded to `relativeChainProjection … (Simplicial.cap … (dualMap φ) c)`; `triadCapShortComplexHom_τ₂_eq` is upstream's `triadCapShortComplexHom_τ₂` verbatim. All elaborate, standard axioms. No change.
6. **Pins to add** (section 8): `triadSubspaceChainMap`, `triadToUnionRelativeChainMap` (yes to the sketch's check iii), and four more. Change 2.
7. **Ledger.** `triadEval_relCup2` should be listed (check ii: yes; it is the sum-relative form and the natural input for a later version without openness), with the two helpers, the face lemmas, the chain identity and the pins. Change 3.
8. **Sketch errors.** The section says "The ledger's `file` field (`HodgeLadder/Triad/Relative/Cup/Cap.lean`) predates …"; the ledger entry has no `file` field (the same slip as finding 7 of the `triad-relative-cup` red team). It calls `local_class_cross_cap` "posted"; it is a sketch statement of the open rung `local-class-cross-model`. Change 4.
9. **Citation.** `docs/references.md` gives `Hatcher2002` with §3.2 only, and the statement cites §3.3. Change 6.
10. **Import.** Appendix A needs `LefschetzPort.AlgebraicTopology.LinearDualConnecting` (port library, already in the build closure through `HodgeLadder.Cup.SingularCup`); a plain `import` suffices, since only proofs use it. The lemma `HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply` is general and belongs upstream next to `linearDualHomologyEquiv_class_apply_class`; check whether `docs/gaps.md` lists it, and add it if not.
11. **Rebase.** `main` (`d89ec00`) inserted a section at the same place in `docs/sketches/local-class-product.md` (after the `cross-orientation` C1 paragraph) and edited the "Triad cap product" row of the register; rebase before the pull request and keep both sketch sections. Change 7.

## Recommended changes

1. `HodgeLadder/Cup/TriadCupCap.lean`: add `import LefschetzPort.AlgebraicTopology.LinearDualConnecting` after the two `public import` lines; replace `triadEval_relCup2` and its docstring by the block of Appendix A (two helper theorems, then the unchanged statement with its proof) (RT5 is exactly this file and compiles sorry-free, standard axioms). Update the module docstring: drop "Statement phase … Open: the sum-relative form `triadEval_relCup2`", mark `triadEval_relCup2` proved, and add the two helpers to "Main results".
2. `HodgeLadder/Cup/TriadCapPins.lean`: add the pins of Appendix B, the first six in section `Triad`, `chainOfSimplex_eq` in section `Simplicial` (it needs the section's `R`, `u`); add them to the module docstring and to the sketch's pins table.
3. Ledger, when the rung lands: `module` `HodgeLadder.Cup.TriadCupCap`; `declarations`: `HodgeLadder.Cup.relCup2_eval_eq_eval_triadCap`, `HodgeLadder.Cup.relCup2_dual_eq`, `HodgeLadder.Cup.triadEval_relCup2`, `HodgeLadder.Cup.relativeCochainCohomologyEquiv_symm_homologyπ`, `HodgeLadder.Cup.relativeCohomologyEquivDualHomology_triadCapCohomologyLinear_homologyπ`, `HodgeLadder.Cup.cupCochain_eq_capLift`, `HodgeLadder.Cup.frontInclusion_eq_subinterval`, `HodgeLadder.Cup.backInclusion_eq_subinterval`, and the pins `HodgeLadder.Cup.TriadCapPins.*` (all 26 plus the 7 of change 2); note: "Exact, no sign; red team docs/sketches/triad-relative-cup-cap.redteam.md". Import both modules from `HodgeLadder.lean`.
4. Sketch, section "triad-relative-cup-cap: statement", first paragraph: replace "The ledger's `file` field (`HodgeLadder/Triad/Relative/Cup/Cap.lean`) predates the `Cup/` layout of `triad-relative-cup`; set `module`" with "The ledger's `module` is `null`; set it"; second paragraph: replace "the term of the posted `local_class_cross_cap`" with "the term in the statement of `local_class_cross_cap` (rung `local-class-cross-model`, open)". Replace the "Stated, proof open" block and the route by a pointer to this verdict once change 1 lands.
5. Optional test: Appendix C in `HodgeLadder/Tests/TriadCupTorus.lean` (same variables; no new import is needed) or in a new `HodgeLadder/Tests/TriadCupCap.lean` importing `HodgeLadder.Tests.TriadCupTorus`.
6. `docs/references.md`, row `Hatcher2002`: add "the cap product σ ⌢ φ = φ(σ|[v₀, …, v_l]) σ|[v_l, …, v_k], the identity ψ(σ ⌢ φ) = (φ ⌣ ψ)(σ), and the relative cap H_n(X, A ∪ B) × H^l(X, A) → H_{n−l}(X, B) for open A, B (§3.3; recalled, unverified)".
7. Rebase on `main` before the pull request (finding 11).
8. After the rebase, in `docs/conventions.md` row "Triad relative cup product", replace "kernel check pending in the rung" with "checked (`triad-relative-cup`)", and set the status of the new row "Cup–cap adjunction (triad)" to checked when the rung lands.

## What was tried

- Trivial closers (RT7): `rfl`, `with_reducible rfl`, unfold-then-`rfl`, `simp` with the three definitions, on the sub-lemma; `rfl` on the adjunction. All fail.
- The proof of the sub-lemma (RT1, RT2). First attempt: `rw [ModuleCat.hom_comp, LinearMap.comp_apply]` on `ConcreteCategory.hom (f ≫ g) x` found no pattern; `ConcreteCategory.comp_apply` works. The pin name `triadCapCohomologyExplicitLinear_mk` needs its namespace `TriadCapPins`. `erw [moduleCatCyclesIso_hom_i …]` failed on the subtype coercion; rewriting the composite in the hypothesis and closing by `Eq.trans` works, since `moduleCatLeftHomologyData.i` is the subtype inclusion by definition. With these, the proof closes; the last step is `exact` of `cupCochain_eq_capLift` after `triadProj_cupCochain`, up to definitional unfolding of `dualIsoYoneda`.
- A sign on the outer maps reaching homology: excluded, the proof uses only τ₂.
- A counterfeit cap satisfying the identity: any change of the cap by a scalar breaks it unless `relCup2` changes by the same scalar, which `forgetRel_relCup2` (checked) excludes; a common scalar on the excision comparison is the only change that both sides absorb (section 3).
- Non-vacuity (RT4): the corollary of Appendix C. `push_neg` is deprecated at this Mathlib; `push Not` works. The first `rw [map_zero]` on `torusEval hT₁ hT₂ 0` failed (the coercion is `ConcreteCategory.hom`); `erw [map_zero]` works.

## Appendix A: proof of `triadEval_relCup2` (compiled as RT5)

Add `import LefschetzPort.AlgebraicTopology.LinearDualConnecting` after the `public import` lines. The block below replaces everything from the docstring of `triadEval_relCup2` to the end of its proof (the statement is unchanged; the two helpers come first).

```lean
set_option backward.isDefEq.respectTransparency false in
/-- The inverse of upstream's `relativeCochainCohomologyEquiv` on the class of a cocycle is the
short-complex class of the same cocycle (both identifications are identities on cochains). -/
theorem relativeCochainCohomologyEquiv_symm_homologyπ {p : ℕ} (P : TopPair.{0})
    (c : (RelativeCochainComplex ℚ P).cycles p) :
    (relativeCochainCohomologyEquiv ℚ P p).symm
        ((RelativeCochainComplex ℚ P).homologyπ p c) =
      (((relativeChainFunctor ℚ).obj P).sc p).linearDual.homologyπ
        (ShortComplex.cyclesMap (HomologicalComplex.linearDualCochainComplexScIso
          ((relativeChainFunctor ℚ).obj P) p).hom c) :=
  ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality
    (HomologicalComplex.linearDualCochainComplexScIso ((relativeChainFunctor ℚ).obj P) p).hom) c

set_option backward.isDefEq.respectTransparency false in
/-- **The triad cap on representatives, evaluated**: for a relative cocycle `c` on `(X, A)`,
`d` on `(X, B)` and a cycle `x` of the triad complex, `⟨[d], [c] ⌢ [x]⟩ = d(c ⌢ x)`, with the
chain-level triad cap `triadCap`; no sign. -/
theorem relativeCohomologyEquivDualHomology_triadCapCohomologyLinear_homologyπ {p q : ℕ}
    (c : (RelativeCochainComplex ℚ (TopPair.ofSubset A)).cycles p)
    (d : (RelativeCochainComplex ℚ (TopPair.ofSubset B)).cycles q)
    (x : (triadChains X A B).cycles (p + q)) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) q
        ((RelativeCochainComplex ℚ (TopPair.ofSubset B)).homologyπ q d)
        (triadCapCohomologyLinear ℚ X A B p q
          ((RelativeCochainComplex ℚ (TopPair.ofSubset A)).homologyπ p c)
          ((triadChains X A B).homologyπ (p + q) x)) =
      (show Module.Dual ℚ _ from (RelativeCochainComplex ℚ (TopPair.ofSubset B)).iCycles q d)
        (triadCap ℚ X A B p q
          ((RelativeCochainComplex ℚ (TopPair.ofSubset A)).iCycles p c)
          ((triadChains X A B).iCycles (p + q) x)) := by
  rw [triadCapCohomologyLinear, LinearMap.comp_apply]
  erw [relativeCochainCohomologyEquiv_symm_homologyπ]
  rw [triadCapCochainCohomologyLinear, LinearMap.comp_apply]
  have h1 := ConcreteCategory.congr_hom (ShortComplex.π_moduleCatCyclesIso_hom
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).sc p).linearDual)
  erw [h1]
  rw [ConcreteCategory.comp_apply]
  erw [TriadCapPins.triadCapCohomologyExplicitLinear_mk]
  rw [TriadCapPins.triadCapCocycleHomologyLinear_eq, TriadCapPins.triadCapHomologyMap_eq]
  have h2 := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality
    (triadCapShortComplexHom ℚ X A B p q _
      (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset A) p
        ((ShortComplex.moduleCatCyclesIso _).hom ((ShortComplex.cyclesMap
          (HomologicalComplex.linearDualCochainComplexScIso
            ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)) p).hom) c))).2)) x
  erw [h2]
  unfold relativeCohomologyEquivDualHomology
  erw [HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply]
  have hi := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i
    (triadCapShortComplexHom ℚ X A B p q _
      (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset A) p
        ((ShortComplex.moduleCatCyclesIso _).hom ((ShortComplex.cyclesMap
          (HomologicalComplex.linearDualCochainComplexScIso
            ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)) p).hom) c))).2)) x
  erw [hi]
  rw [ConcreteCategory.comp_apply, triadCapShortComplexHom_τ₂]
  have hc : ((relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset A) p
        ((ShortComplex.moduleCatCyclesIso _).hom ((ShortComplex.cyclesMap
          (HomologicalComplex.linearDualCochainComplexScIso
            ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)) p).hom) c)) :
          RelativeCocycle ℚ (TopPair.ofSubset A) p) : RelativeCochain ℚ (TopPair.ofSubset A) p) =
      (RelativeCochainComplex ℚ (TopPair.ofSubset A)).iCycles p c := by
    rw [TriadCapPins.relativeCohomologyCycleToCocycle_val]
    have h3 := ConcreteCategory.congr_hom (ShortComplex.moduleCatCyclesIso_hom_i
      (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).sc p).linearDual)
      ((ShortComplex.cyclesMap (HomologicalComplex.linearDualCochainComplexScIso
            ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)) p).hom) c)
    rw [ConcreteCategory.comp_apply] at h3
    refine Eq.trans h3 ?_
    have h4 := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i
      (HomologicalComplex.linearDualCochainComplexScIso
            ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)) p).hom) c
    erw [h4]
    rfl
  rw [hc]
  rfl

/-- **The adjunction on the sum-relative model**, before excision: for `w` in the homology of
`C(X)/(C(A) + C(B))`, pairing the pullback `triadExcisionCoh (relCup2 φ ψ)` with `w` (upstream's
`linearDualHomologyEquiv` of the triad complex) equals pairing `ψ` with upstream's sum-relative
triad cap `triadCapCohomologyLinear φ w`. No sign. -/
theorem triadEval_relCup2 (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (φ : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (ψ : RelativeCohomology ℚ (TopPair.ofSubset B) q)
    (w : TriadRelativeHomology ℚ X A B (p + q)) :
    (triadChains X A B).linearDualHomologyEquiv (p + q)
        ((triadExcisionCoh X A B hA hB (p + q)).hom (relCup2 X A B hA hB φ ψ (p + q) rfl)) w =
      relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) q ψ
        (triadCapCohomologyLinear ℚ X A B p q φ w) := by
  obtain ⟨c, rfl⟩ :=
    (RelativeCochainComplex ℚ (TopPair.ofSubset A)).moduleCat_homologyπ_surjective p φ
  obtain ⟨d, rfl⟩ :=
    (RelativeCochainComplex ℚ (TopPair.ofSubset B)).moduleCat_homologyπ_surjective q ψ
  obtain ⟨x, rfl⟩ := (triadChains X A B).moduleCat_homologyπ_surjective (p + q) w
  rw [triadExcisionCoh_relCup2_homologyπ,
    relativeCohomologyEquivDualHomology_triadCapCohomologyLinear_homologyπ,
    HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply]
  let π := (triadRelativeChainProjection ℚ X A B).f (p + q)
  have : Epi π := Cofork.IsColimit.epi
    (triadRelativeChainProjectionComponentIsCokernel ℚ X A B (p + q))
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance
    ((triadChains X A B).iCycles (p + q) x)
  rw [← hy]
  erw [triadCap_projection_apply]
  unfold triadCupCycles
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (dualIsoYoneda (triadChains X A B)).inv (p + q))
  erw [hi]
  rw [ConcreteCategory.comp_apply]
  erw [TauCeti.ChainComplex.iCycles_cupCycles]
  have hiA := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (dualIsoYoneda ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A))).hom p) c
  have hiB := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (dualIsoYoneda ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B))).hom q) d
  erw [hiA, hiB]
  have key := cupCochain_eq_capLift X A B
    ((RelativeCochainComplex ℚ (TopPair.ofSubset A)).iCycles p c)
    ((RelativeCochainComplex ℚ (TopPair.ofSubset B)).iCycles q d)
  rw [triadProj_cupCochain] at key
  have hk := ConcreteCategory.congr_hom key y
  rw [ConcreteCategory.comp_apply] at hk
  exact hk
```

## Appendix B: additional pins (compiled as RT3)

In section `Triad` of `HodgeLadder/Cup/TriadCapPins.lean`:

```lean
/-- Pin: the subspace map `C(A) ⊞ C(B) → C(X)` is `biprod.desc` of the two inclusions. -/
theorem triadSubspaceChainMap_eq :
    triadSubspaceChainMap R X A B =
      biprod.desc ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom
        ((chainPairFunctor R).obj (TopPair.ofSubset B)).hom :=
  rfl

/-- Pin: the triad complex is the cokernel of the subspace map. -/
theorem triadRelativeChainComplex_eq :
    triadRelativeChainComplex R X A B = cokernel (triadSubspaceChainMap R X A B) :=
  rfl

/-- Pin: the triad projection is the cokernel projection. -/
theorem triadRelativeChainProjection_eq :
    triadRelativeChainProjection R X A B = cokernel.π (triadSubspaceChainMap R X A B) :=
  rfl

/-- Pin: the excision comparison is the cokernel descent of the projection to `C(X, A ∪ B)`. -/
theorem triadToUnionRelativeChainMap_eq :
    triadToUnionRelativeChainMap R X A B =
      (cokernelIsCokernel (triadSubspaceChainMap R X A B)).desc
        (CokernelCofork.ofπ (relativeChainProjection R (TopPair.ofSubset (A ∪ B)))
          (triadSubspaceChainMap_unionRelativeChainProjection_eq_zero R X A B)) :=
  rfl

/-- **The excision comparison is induced by the identity of `C(X)`**: after the triad
projection it is the projection `C(X) → C(X, A ∪ B)` (upstream
`triadRelativeChainProjection_triadToUnionRelativeChainMap`, restated). -/
theorem triadRelativeChainProjection_triadToUnionRelativeChainMap_eq :
    triadRelativeChainProjection R X A B ≫ triadToUnionRelativeChainMap R X A B =
      relativeChainProjection R (TopPair.ofSubset (A ∪ B)) :=
  triadRelativeChainProjection_triadToUnionRelativeChainMap R X A B

/-- Pin: in the degree-zero morphism the left map carries `(-1)^p`. -/
theorem triadCapShortComplexHomZero_τ₁_eq (p : ℕ)
    (φ : RelativeCochain R (TopPair.ofSubset A) p)
    (hφ : relativeCoboundary R (TopPair.ofSubset A) p φ = 0) :
    (triadCapShortComplexHomZero R X A B p φ hφ).τ₁ =
      ModuleCat.ofHom (((-1 : R) ^ p) • triadCap R X A B p 1 φ) :=
  rfl
```

In section `Simplicial`:

```lean
/-- Pin: the chain of a simplex is the generator `1` of its summand. -/
theorem chainOfSimplex_eq {Y : SSet.{u}} {n : ℕ} (x : Y _⦋n⦌) :
    Simplicial.chainOfSimplex R x = (Y.ιChainComplex (R := ModuleCat.of R R) x).hom 1 :=
  rfl
```

## Appendix C: non-vacuity corollary (compiled as RT4)

With the variables of `HodgeLadder/Tests/TriadCupTorus.lean`, in namespace `HodgeLadder.Tests`:

```lean
include hT₁ hT₂ h₁ h₂ in
/-- **Non-vacuity of the adjunction** (`A = B = ∅`, `p = q = 1`): some `z` pairs nonzero with
`relCup2 a₁ a₂`, so both sides of `relCup2_eval_eq_eval_triadCap` are nonzero there. -/
theorem exists_eval_relCup2_ne_zero
    (a₁ a₂ : RelativeCohomology ℚ (TopPair.ofSubset (∅ : Set Y)) 1)
    (ha₁ : forgetRel _ 1 a₁ = windingClass g₁ hg₁) (ha₂ : forgetRel _ 1 a₂ = windingClass g₂ hg₂) :
    ∃ z, relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset ((∅ : Set Y) ∪ ∅)) (1 + 1)
      (relCup2 Y ∅ ∅ isOpen_empty isOpen_empty a₁ a₂ (1 + 1) rfl) z ≠ 0 := by
  by_contra hz
  push Not at hz
  have h0 : relCup2 Y ∅ ∅ isOpen_empty isOpen_empty a₁ a₂ (1 + 1) rfl = 0 :=
    (relativeCohomologyEquivDualHomology ℚ _ _).injective (by ext z; simpa using hz z)
  have h1 := torusEval_relCup2_winding hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂ a₁ a₂ ha₁ ha₂
  rw [h0, map_zero] at h1
  erw [map_zero] at h1
  exact zero_ne_one h1
```
