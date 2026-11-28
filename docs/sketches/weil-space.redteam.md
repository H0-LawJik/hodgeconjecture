# Red team: `weil-space`

Date: 2026-11-28. Candidate: WIP commit `bab3380` on `track/weil-space`, file `HodgeLadder/Weil/Space.lean` (module `HodgeLadder.Weil.Space`, namespace `HodgeLadder.Weil`), not yet root-imported or in the ledger. Base `19a4bda`; pin upstream `2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same as `main` (`d1c59da`), which changes neither `HodgeLadder/Pullback/Functorial.lean` nor `HodgeLadder/Divisor/LefschetzEquality.lean`. Issue #256, plan node A3 of `docs/notes/2026-11-27-t1-plan.md`. No thinker sketch exists for this rung.

Read: the ledger entries `weil-space`, `weil-surface-statement`, `weil-surface-reduction`, `weil-elliptic-square`, `weil-elliptic-square-nonzero`, `weil-eigen-algebra`, `pullback-functorial`; plan §§1, 3, 4 (A3, B, G1); decision 0013; `docs/sketches/weil-eigen-algebra.redteam.md`; `docs/sketches/pullback-functorial.redteam.md` (finding 9, kernel cost); upstream `HodgeConjecture/Statement.lean`, `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (`fieldCohomologyModule`, `hodgeClasses`), `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean` (`algebraicCycleClassSpan`); `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`.

Scratch: `rtscratch-weilspace/` in the worktree (files `A`, `B*`, `C*`, `S0` to `S4`, `P` to `P3`), each a `lake env lean` run against the built `.olean`; deleted after the pass. Every Lean claim marked "scratch" below elaborated there. Kernel times are from `trace.profiler` with `Elab.async false`, serial within a file, three files at a time on the machine.

**Verdict: pass with changes.** The definition is the literature's Weil space for abelian surfaces, with the sign right and the sign pinned; the three theorems are exact and carry standard axioms. The changes: say in the docstring that the eigenspace description is specific to surfaces, replace an unproved docstring claim by two checked bridge lemmas, add the positive companion of the vacuity guard and its ℙ¹ test, the conventions row, a reference key, and the ledger, roadmap and gaps bookkeeping.

## Findings

1. **The statement is the literature's W_K, for abelian surfaces only.** The general definition ([Weil1977]; B. van Geemen, An introduction to the Hodge conjecture for abelian varieties, LNM 1594 (1994), §5, key `vanGeemen1994` proposed in change 5, locator unverified): A an abelian variety of dimension 2n, K = ℚ(√−d) ⊂ End⁰(A) with d > 0, H¹(A; ℚ) a K-vector space of dimension 2n, H¹ ⊗ ℂ = V_σ ⊕ V_σ̄ for the two embeddings σ, σ̄ of K, and W_K := ∧^{2n}_K H¹(A; ℚ) ⊂ H^{2n}(A; ℚ), the rational subspace whose complexification is ∧^{2n} V_σ ⊕ ∧^{2n} V_σ̄. Weil type (each embedding with multiplicity n on the tangent space) is what makes W_K consist of Hodge classes; it is no part of the definition of W_K. Field by field at n = 1:

   | Field | Literature (recalled, locators unverified) | Lean (`bab3380`) | Match |
   |---|---|---|---|
   | ambient | H²(A; ℚ) = ∧²_ℚ H¹(A; ℚ) ([Mumford1970] §1, locator unverified) | `H^2(X; ℚ)`, upstream's constant-sheaf cohomology with upstream's ℚ-structure `fieldCohomologyModule ℚ X 2` | yes; the identification H² = ∧²H¹ is an input of `weil-surface-reduction` (its span and rank hypotheses), absent here by design |
   | the K-action | √−d acts through an f ∈ End⁰(A) with f² = −d | `f : X ⟶ X`, acting by `pullbackCohLinear f 2` (contravariant, row "Pullback of cohomology") | yes; K is commutative, so the anti-homomorphism End(A) → End(H¹) given by pullback is a homomorphism on ℚ[f] |
   | the subspace | complexification ∧²V_σ ⊕ ∧²V_σ̄ | `ker (f^* + d • id)` on H² | yes at n = 1: on ∧²(V₊ ⊕ V₋) the pullback ∧²φ acts by (i√d)² = −d on ∧²V₊ and ∧²V₋ and by (i√d)(−i√d) = d on V₊ ∧ V₋; d ≠ 0 separates the two, so the −d-eigenspace has complexification ∧²V₊ ⊕ ∧²V₋, of ℚ-dimension 1 + 1 = 2 inside the 6-dimensional H² (the count in issue #256, confirmed) |
   | d | d > 0, K depends on the squarefree part of d | `d : ℚ`, unrestricted | yes for the definition; the theorem needs 0 < d, which `IsWeilTypeSurface` carries (plan G1). If √−d ∈ End⁰(A) lies in End(A) only as m√−d, the endomorphism m√−d has (f^*)² = −m²d on H¹ and the Weil space is `weilSpace A f (m² d)`, the same subspace (∧²(mφ) = m² ∧²φ). So d must stay a general positive number, with no squarefree condition, and `d : ℚ` with G1's `(d : ℕ)` cast is the right shape (scratch `P`: `weilSpace A f d` elaborates at `d : ℕ`) |
   | balance | Weil type: signature (1, 1) | absent | correct: plan §1 shows the (2, 0) case f = [i] × [i] gives a nonzero W with W ∩ Hdg^1 = 0; balance belongs to the theorem (G1), and the definition must not carry it |

   **Scope limit (new).** The eigenvalue description does not extend to n ≥ 2. On ∧^{2n}(V₊ ⊕ V₋) a product of a vectors from V₊ and b from V₋ (a + b = 2n) has eigenvalue (i√d)^a (−i√d)^b = (−d)^n (−1)^b, so the (−d)^n-eigenspace collects every even b. For a fourfold (n = 2, dim V± = 4) it has complex dimension 1 + 36 + 1 = 38 (b = 0, 2, 4), against 2 for W_K. `weilSpace` is the Weil space of a surface and nothing more; T3 and T4 need another definition (change 1).

2. **The hypotheses can be satisfied.** The definition has none. `weilSpace_le_algebraic_iff_le_hodge` needs a smooth projective integral X over ℂ: ℙ¹, ℙⁿ and ℙ¹ × ℙ¹ are checked witnesses (`nonvacuity-tests`, `p1p1-witness`). Any `f : X ⟶ X` and any `d` qualify; `𝟙 X` is the instance used below.

3. **No trivial proof.** Attempts (scratch `P`): `simp [weilSpace]` for `weilSpace X f d = ⊥` and for `= ⊤` both stop at `Subsingleton H^2(X; ℚ)` (typeclass timeout); `rfl` for `weilSpace X (𝟙 X) 1 = ⊥` is a type mismatch. No definition unfolds to `True`; there is no `ℕ∞` coercion and no index type. Every hypothesis is used: the three instances of the iff are needed to form `Hdg^1` and `algebraicCycleClassSpan` and for `lefschetzOneOneEquality_holds`. The iff holds for every submodule S of H^2(X; ℚ), with nothing specific to `weilSpace`; it is a convenience corollary of the checked Lefschetz equality and carries no Weil content (optional change O1 states the general form). Degree bookkeeping: `Hdg^1` lives in `H^(2 * 1)(X; ℚ)`, and the rewrite closes because `2 * 1` and `2` agree definitionally; the module compiles, so no transport is hidden.

4. **Interface axioms.** Not an interface rung: no structure, no assumed `Prop`.

5. **Checker and axioms.** `python3 tools/check.py --no-build` exits 0 on the branch (`ACCEPTED: all checks passed`), but it does not cover this rung yet: the module is not root-imported and the ledger names no declaration. `lake env lean HodgeLadder/Weil/Space.lean` compiles the file as committed with no message (133 s wall). In a verbatim copy (scratch `S0`) `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all four declarations (`weilSpace`, `mem_weilSpace_iff` in scratch `A`; `weilSpace_id_one`, `weilSpace_le_algebraic_iff_le_hodge` in `S0`). The names are the ones the ledger title describes; the ledger entry is still empty (change 6). Robustness: `weilSpace_id_one` goes through `smul_eq_zero`, which needs `Module.IsTorsionFree ℚ H^2(X; ℚ)`; in a `module` file the search succeeds even at `synthInstance.maxHeartbeats 5000` (scratch `B5`), while in a plain non-module file it times out at 20,000 and at 200,000 heartbeats (scratch `C`, `C2`). Every ladder file is a module, so this is acceptable; record it in the docstring of the proof only if a consumer copies the proof into a non-module file.

6. **Conventions.** The statement uses four conventions, none of them registered yet:

   | Convention | Where fixed | Truth depends on it? |
   |---|---|---|
   | pullback direction: f acts by f^* = `pullbackCoh f 2` | row "Pullback of cohomology", rung `pullback-functorial` | no for the Weil space of a surface: for an isogeny with (f^*)² = −d on H¹, deg f = det φ = d², f_* f^* = deg f, so f_* = d² (f^*)⁻¹ on H², with eigenvalues d²/(−d) = −d and d²/d = d; the two directions give the same eigenspaces (computation in this pass, at the pin there is no pushforward) |
   | sign of the eigenvalue: −d, written `+ d • id` inside the kernel | this rung | yes: the +d-eigenspace is V₊ ∧ V₋, of ℚ-dimension 4; on a balanced surface with a ∈ V₊ ∩ H^{1,0} and c ∈ V₋ ∩ H^{1,0}, the product a ∧ c spans H^{2,0}, so T1 stated with +d is false on every balanced abelian surface |
   | the root i√d (which eigenspace of φ is V₊) | plan G1 (`IsWeilTypeSurface`), not this rung | no: φ and −φ give the same ∧²φ, so `weilSpace` is the same for both roots; G1's balance condition is symmetric in the two eigenspaces |
   | the scale of f (f acting as m√−d) | this rung (d is the square of the eigenvalue of f^* on H¹, up to sign) | yes for which d to pass: the Weil space of f is `weilSpace A f (m² d)`; with the wrong d the space is 0 |
   | cup order on H¹ ⊗ H¹ | row "Cup product" | no: membership in an eigenspace is unchanged by the scalar −1 of a swap; the explicit elements of `weil-elliptic-square-nonzero` stay in the space in either order |

   Cited inputs: the only borrowed result is `lefschetzOneOneEquality_holds` (`Hdg^1(X; ℚ) = algebraicCycleClassSpan X 1`), an equality of submodules of the same upstream type with no sign or scalar; its conventions (exponential sequence, divisor class sign, row "Lefschetz (1,1)") enter only through span statements, which are insensitive to sign. The discriminant row of `docs/conventions.md` ("to check before any Weil-class rung") does not bear on this rung: the definition of W_K for n = 1 uses no Hermitian form. It stays open for T2 to T5.

   The sign is pinned by tests, which no change of the definition's sign could pass. `weilSpace_id_one` (identity, d = 1 gives ⊥) is the guard against ⊤; under the swapped convention `ker (f^* − d • id)` it would read `⊤ = ⊥` on every X, false on ℙ¹. The guard against an always-⊥ definition is missing: scratch `P2` checks the companion

   ```lean
   theorem weilSpace_id_neg_one (X : Over (Spec ↧ℂ)) : weilSpace X (𝟙 X) (-1) = ⊤ := by
     refine Submodule.eq_top_iff'.mpr fun w => ?_
     rw [mem_weilSpace_iff, pullbackCoh_id, neg_neg, one_smul]
   ```

   (kernel 7.7 s) and the nonzero instance on ℙ¹, through the checked `class_infty_ne_zero_of acyclic_compl_infty` (rung `projective-line-class-nonzero`), kernel 7.2 s, standard axioms:

   ```lean
   theorem projectiveLine_weilSpace_id_neg_one_ne_bot :
       weilSpace projectiveLine (𝟙 _) (-1) ≠ ⊥ := by
     rw [weilSpace_id_neg_one]
     intro h
     apply class_infty_ne_zero_of acyclic_compl_infty
     have : cycleComponentSheafClass projectiveLine infty coheight_infty' ∈
         (⊤ : Submodule ℚ H^2(projectiveLine; ℚ)) := Submodule.mem_top
     rw [h] at this
     exact (Submodule.mem_bot ℚ).mp this
   ```

   Together the two pin the sign at the pin: the same f gives ⊥ at d = 1 and a nonzero space at d = −1 on ℙ¹, and a definition with either sign swapped or always ⊥ fails one of them (change 2).

7. **Equality first.** `mem_weilSpace_iff` and `weilSpace_le_algebraic_iff_le_hodge` are exact iffs; `weilSpace_id_one` is an exact equality of submodules; no scalar enters. The rung is a foundation for an inclusion: T1 is `weilSpace A f d ≤ algebraicCycleClassSpan A 1` (`weil-surface-statement`, open), which the iff turns into `weilSpace ≤ Hdg^1` through the checked equality `lefschetz-1-1-equality`; the reduction `weil-surface-reduction` (open) proves the Hodge form. The equality rung on the instance side is `weil-elliptic-square-nonzero` (`finrank ℚ (weilSpace ellipticSquare ellipticWeilEndo 1) = 2`, open). Its two explicit elements are in the −1-eigenspace for either orientation of the basis x₁, x₂ of H¹(E) under [i]^* (checked by hand in this pass: with [i]^* x₁ = ±x₂, [i]^* x₂ = ∓x₁ and f = [i] × [i]³, both elements map to their negatives; pr₁^*[pt] and pr₂^*[pt] have eigenvalue +1 since [i] has degree 1), so the dimension 2 there matches finding 1.

7b. **Non-vacuity.** The smallest test that fails if the definition were trivially ⊥ is `HodgeLadder.Tests.projectiveLine_weilSpace_id_neg_one_ne_bot` above, stated in upstream's API (`cycleComponentSheafClass`, `H^2(·; ℚ)`); it does not exist yet (change 2). The smallest test that fails if it were trivially ⊤, or carried the opposite sign, is `HodgeLadder.Weil.weilSpace_id_one`, which exists. Both use the identity; the first nonzero Weil space of a non-identity endomorphism is `weil-elliptic-square-nonzero`, which needs `elliptic-square-cohomology`. A cheaper non-identity test at the pin would be the factor swap of ℙ¹ × ℙ¹ at d = 1 (−1-eigenspace spanned by [pt × ℙ¹] − [ℙ¹ × pt]); it needs the pullback values of the fibre classes along the swap, which no rung supplies yet (rung `fibre-class-pullback` is open), so it is noted here without a rung.

8. **Pin drift.** None: the candidate was built against `2ead713`, the pin in `lakefile.toml` on the branch and on `main`. The upstream definitions it depends on (`fieldCohomologyModule`, `hodgeClasses`, `algebraicCycleClassSpan`, the notations `H^n(X; K)` and `Hdg^p(X; K)`) are pinned by `HodgeLadder/CycleClass/Pins.lean` (`hodgeClasses_eq`, `algebraicCycleClassSpan_eq` accepted by the checker run of finding 5).

9. **Kernel cost, and what a shortcut instance would save here.** The four declarations cost 119.1 s of kernel time (scratch `S0`): `weilSpace` 39.3 s (with its auxiliary `_proof_5`, `_proof_7`), `mem_weilSpace_iff` 29.4 s, `weilSpace_id_one` 12.7 s, `weilSpace_le_algebraic_iff_le_hodge` 37.7 s; elaboration under 2.2 s each. Kernel diagnostics on the iff (scratch `S3`) are dominated by the additive structure of `Ext`, with no `Module.ofMinimalAxioms` among the top entries: `Functor.obj` 312,863 unfoldings, `AddCommGrpCat.str` 246,678, `AddGroup.toSubNegMonoid` 232,809, `DFunLike.coe` 232,074, `HSMul.hSMul` 178,777, `Preadditive.homGroup` 26,017, `Function.Injective.addCommGroup` 24,828. Measured spellings (same four declarations):

   | Variant (scratch) | Four declarations | Change |
   |---|---|---|
   | as committed (`S0`) | 119.1 s | baseline |
   | `Module ℚ` shortcut `instance (priority := high) shortQ X n : Module ℚ (H^n(X; ℚ)) := fieldCohomologyModule ℚ X n` (3.3 s once), imported `pullbackCohLinear` (`S1a`) | 95.3 s | −20% |
   | the same, with the linear map rebundled under the shortcut, as if `Pullback.Functorial` were rebuilt with it (`S1b`; the rebundled map 41.6 s, charged to that module) | 79.5 s | −33% |
   | additive and module shortcuts, `shortG X n : AddCommGroup (H^n(X; ℚ)) := inferInstance` then `shortQ` over it, rebundled map (`S2`; shortcuts 8.7 s once, map 29.7 s) | 57.7 s: `weilSpace` 4.9, `mem_weilSpace_iff` 6.4, `weilSpace_id_one` 3.9, the iff 42.5 | −52% overall; −81% on the three ladder-internal declarations, +13% on the iff |

   So a `Module ℚ` shortcut alone saves a fifth to a third here; the larger share needs a second shortcut on the additive group, and no ladder instance helps a declaration that compares a ladder-typed submodule with upstream's `Hdg^p` or `algebraicCycleClassSpan` (the iff gets slower, since the kernel then compares the ladder path with upstream's). The re-elaborated body of upstream's statement costs 13.0 s of kernel time with or without any shortcut (`S0`, `S2`, a `def` equal to `HodgeConjecture`'s body).

   **The risk, measured.** In one file (scratch `S4`), the same three terms elaborated before and after declaring `shortQ`:

   | Term | Before = after (`Expr` equality) | Mentions `shortQ` after |
   |---|---|---|
   | upstream's `HodgeConjecture` body, re-elaborated (`∀ X …, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p`) | yes | no |
   | `Hdg^p(X; ℚ)` ascribed `Submodule ℚ (H^(2 * p)(X; ℚ))` | value yes, type no | type yes |
   | `Module.finrank ℚ H^2(X; ℚ)` | no | yes |

   Upstream constants are compiled terms and cannot change. In a re-elaborated upstream statement the `Module` instance comes by unification from the types of `hodgeClasses` and `algebraicCycleClassSpan`, so the shortcut leaves it unchanged. Every ladder-written type that synthesizes `Module ℚ H^n(X; ℚ)` (a `Submodule ℚ H^n(X; ℚ)` ascription, `→ₗ[ℚ]`, `finrank`, `⊤`, `⊥`) changes: it mentions a ladder constant, definitionally equal to upstream's (`hcRe1 = HodgeConjecture`, `hcRe0 = hcRe1`, `rk0 = rk1` all close by `rfl`, scratch `S4`). Without any shortcut the re-elaborated body already differs from upstream's stored value as an `Expr` (scratch `S0`, `S1a`, `S1b`: `false`), so the ladder has no syntactic identity with upstream terms to lose. The additive shortcut `shortG` would in addition change every `0`, `+` and `≠ 0` on H^n in ladder statements; its effect on re-elaborated upstream bodies was not tested. Neither shortcut is adopted here; record the measurement (change 7) for the decision that the `pullback-functorial` red team deferred.

10. **Names.** The plan writes `mem_weilSpace` and `weilSpace_le_algebraic_iff`; the candidate writes `mem_weilSpace_iff` and `weilSpace_le_algebraic_iff_le_hodge`. Keep the candidate's names: the nearest Mathlib analog is `Module.End.mem_eigenspace_iff : x ∈ eigenspace f μ ↔ f x = μ • x`, and the second name says which side the iff lands on. `LinearMap.mem_ker` is the Mathlib counterexample without `_iff`; either is admissible. The plan is a dated note and stays as written; the ledger and roadmap carry the final names (change 6), and `weil-surface-reduction`'s brief should cite them.

11. **Placement.** `HodgeLadder/Weil/Space.lean` sits at layer 47 (`tools/pinwalk.py` graph: `Pullback.Functorial` 5, `Divisor.LefschetzEquality` 46), only because of the iff. `weil-elliptic-square-nonzero` and `weil-surface-reduction` need the definition and its bridges; only the final step of T1 needs the iff. Optional change O1 drops the layer to 6. The definition is ladder-specific (no Mathlib or upstream equivalent at the pin; upstream states `HodgeConjectureForAbelianVarieties` and defines no Weil class), so a pin bump should check upstream for a Weil-class definition (change 8).

12. **A docstring claim that is not a proof.** The module docstring says the eigenspace form `ker (f^* − (−d) • id)` follows "by `rw [neg_smul, sub_neg_eq_add]`". In scratch `P` that `rw` followed by unfolding `weilSpace` times out at `whnf` (200,000 heartbeats); `rw [neg_smul, sub_neg_eq_add]; rfl` closes it (scratch `P2`, 25.0 s). The Mathlib form `Module.End.eigenspace` needs `ext` (scratch `P3`, 10.7 s; the `rw [Module.End.eigenspace_def, …]` route times out at `isDefEq`). `weil-surface-reduction` consumes `ker (S − c • id)` (`ker_sub_smul_le_span_of_eigen`, `isCompl_ker_sub_smul_ker_add_smul`), so both bridges belong in this rung (change 3).

## Required changes

1. Module docstring: replace the paragraph beginning "Convention (row "Weil space")." with:

   > Convention (row "Weil space" in `docs/conventions.md`). The map is the pullback `f^*` of rung `pullback-functorial` (contravariant: `f : X ⟶ X` acts on `H²(X; ℚ)` by `pullbackCoh f 2`). The eigenvalue is `−d`, written with `+ d • id` inside the kernel; `weilSpace_eq_ker_sub` and `weilSpace_eq_eigenspace` give the forms `ker (f^* − (−d) • id)` and `Module.End.eigenspace f^* (−d)`. No condition on `d` is imposed: on an abelian surface A with `(f^*)² = −d` on `H¹` and `d > 0`, the eigenvalues of `f^*` on `H¹ ⊗ ℂ` are `±i√d`, each with a 2-dimensional eigenspace `V±`, and on `H² = ∧²H¹` the `−d`-eigenspace has complexification `∧²V₊ ⊕ ∧²V₋`, the complexification of Weil's `W_K = ∧²_K H¹` for `K = ℚ(√−d)` ([Weil1977]; [vanGeemen1994] §5, locators unverified). If `f` acts as `m√−d`, pass `m² d`. The space is the same for `f` and for an endomorphism acting by `−f^*` on `H¹`. Positivity of `d` and the Weil-type (balance) condition are hypotheses of the theorem (`IsWeilTypeSurface`, rung `weil-surface-statement`), not of this definition. The eigenspace description is specific to surfaces: on `H^{2n}` of an abelian `2n`-fold with `n ≥ 2` the `(−d)^n`-eigenspace is strictly larger than `W_K` (dimension 38 against 2 for `n = 2`), so this definition does not serve T3 or T4. This file uses none of the surface facts.

   and add to "Main results":

   > * `HodgeLadder.Weil.weilSpace_id_neg_one`: `weilSpace X (𝟙 X) (−1) = ⊤`, the companion guard.
   > * `HodgeLadder.Weil.weilSpace_eq_ker_sub`, `HodgeLadder.Weil.weilSpace_eq_eigenspace`: the forms `ker (f^* − (−d) • id)` and `Module.End.eigenspace f^* (−d)`.

2. Add to `HodgeLadder/Weil/Space.lean`, after `weilSpace_id_one` (scratch `P2`, kernel 7.7 s):

   ```lean
   /-- **Companion guard**: for the identity and `d = −1` the Weil space is everything, since
   `(𝟙 X)^* w = w = −(−1) • w`. With `weilSpace_id_one` this pins the sign of the eigenvalue. -/
   theorem weilSpace_id_neg_one (X : Over (Spec ↧ℂ)) : weilSpace X (𝟙 X) (-1) = ⊤ := by
     refine Submodule.eq_top_iff'.mpr fun w => ?_
     rw [mem_weilSpace_iff, pullbackCoh_id, neg_neg, one_smul]
   ```

   and a test module `HodgeLadder/Tests/WeilSpace.lean` (`module`; `public import HodgeLadder.Weil.Space`, `public import HodgeLadder.Tests.ProjectiveLineTest`; namespace `HodgeLadder.Tests`; `open CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder.Weil`) with `projectiveLine_weilSpace_id_neg_one_ne_bot` exactly as in finding 6 (scratch `P2`, kernel 7.2 s), docstring: "The Weil space of the identity at `d = −1` is nonzero on ℙ¹: it is all of `H²(ℙ¹; ℚ)`, which holds the nonzero point class. Fails if `weilSpace` were always `⊥`."

3. Add to `HodgeLadder/Weil/Space.lean` (scratch `P2`, `P3`; kernel 25.0 s and 10.7 s):

   ```lean
   /-- The Weil space in the form `ker (S − c • id)` that `ker_sub_smul_le_span_of_eigen` and
   `isCompl_ker_sub_smul_ker_add_smul` consume, with `c = −d`. -/
   theorem weilSpace_eq_ker_sub (X : Over (Spec ↧ℂ)) (f : X ⟶ X) (d : ℚ) :
       weilSpace X f d = LinearMap.ker (pullbackCohLinear f 2 - (-d) • LinearMap.id) := by
     rw [neg_smul, sub_neg_eq_add]
     rfl

   /-- The Weil space is Mathlib's eigenspace of `f^*` for the eigenvalue `−d`. -/
   theorem weilSpace_eq_eigenspace (X : Over (Spec ↧ℂ)) (f : X ⟶ X) (d : ℚ) :
       weilSpace X f d = Module.End.eigenspace (pullbackCohLinear f 2) (-d) := by
     ext w
     rw [Module.End.mem_eigenspace_iff, mem_weilSpace_iff, pullbackCohLinear_apply]
   ```

4. `docs/conventions.md`, new row after "de Rham cup order" (columns Convention | Fixed where | Choice | Results whose truth depends on it | Status):

   > | Weil space | this repository, `HodgeLadder.Weil.weilSpace`, `mem_weilSpace_iff`, `weilSpace_eq_ker_sub`, `weilSpace_eq_eigenspace`, `weilSpace_id_one`, `weilSpace_id_neg_one` (`HodgeLadder/Weil/Space.lean`, rung `weil-space`); test `HodgeLadder.Tests.projectiveLine_weilSpace_id_neg_one_ne_bot`; literature [Weil1977], [vanGeemen1994] §5 (locators unverified) | `weilSpace X f d := ker (pullbackCohLinear f 2 + d • id)`, the `−d`-eigenspace of the pullback `f^* = pullbackCoh f 2` on `H²(X; ℚ)` (contravariant, row "Pullback of cohomology"); `d : ℚ` with no positivity or squarefree condition (`0 < d` and balance are hypotheses of `IsWeilTypeSurface`). On an abelian surface with `(f^*)² = −d` on `H¹`, `H¹ ⊗ ℂ = V₊ ⊕ V₋` with `V± = ker (f^* ∓ i√d)`, and the `−d`-eigenspace on `H² = ∧²H¹` has complexification `∧²V₊ ⊕ ∧²V₋`, the complexification of `W_K = ∧²_K H¹`, `K = ℚ(√−d)`; an `f` acting as `m√−d` needs `m² d`. Invariant under the choice of root (`φ` and `−φ` give `∧²φ`), under pullback against pushforward (`f_* = d² (f^*)⁻¹` on `H²` has the same eigenvalues `±d`), and under the cup order. Valid for surfaces only: for abelian `2n`-folds with `n ≥ 2` the `(−d)ⁿ`-eigenspace on `H^{2n}` is larger than `W_K` | the sign: T1 (`weil-surface-statement`, `weil-surface-reduction`, `weil-elliptic-square`, `weil-surface`) and `weil-elliptic-square-nonzero`; with `+d` the space is `V₊ ∧ V₋`, of rank 4, which contains `H^{2,0}` on a balanced surface, and T1 is false. The scale of `d`: the same rungs (a wrong `d` gives 0). Not the iff `weilSpace_le_algebraic_iff_le_hodge` (any submodule) | sign pinned at the pin: `weilSpace_id_one` (⊥ at `d = 1`) and `projectiveLine_weilSpace_id_neg_one_ne_bot` (nonzero at `d = −1`); surface identification read from the literature, unverified locators (red team 2026-11-28) |

5. `docs/references.md`, new row immediately before `vanGeemen1996`:

   > | `vanGeemen1994` | B. van Geemen, An introduction to the Hodge conjecture for abelian varieties, in: Algebraic Cycles and Hodge Theory (Torino, 1993), LNM 1594, Springer 1994, pp. 233–252 (pages unverified) | Weil classes: W_K = ∧^{2n}_K H¹(A; ℚ) for an abelian 2n-fold with K = ℚ(√−d) acting, complexification ∧^{2n}V_σ ⊕ ∧^{2n}V_σ̄, Hodge for Weil type (§5, locator unverified) |

6. `ledger/ladder.json`, entry `weil-space`:
   - `"status"`: `"checked"`; `"module"`: `"HodgeLadder.Weil.Space"`;
   - `"declarations"`: `["HodgeLadder.Weil.weilSpace", "HodgeLadder.Weil.mem_weilSpace_iff", "HodgeLadder.Weil.weilSpace_eq_ker_sub", "HodgeLadder.Weil.weilSpace_eq_eigenspace", "HodgeLadder.Weil.weilSpace_id_one", "HodgeLadder.Weil.weilSpace_id_neg_one", "HodgeLadder.Weil.weilSpace_le_algebraic_iff_le_hodge", "HodgeLadder.Tests.projectiveLine_weilSpace_id_neg_one_ne_bot"]`;
   - `"depends_on"`: add `"projective-line-class-nonzero"` (the test);
   - `"note"`: "Checked 2026-11-28. weilSpace X f d := ker (pullbackCohLinear f 2 + d • id), the −d-eigenspace of f^* on H²(X; ℚ), d : ℚ unrestricted; mem_weilSpace_iff (f^* w = −d • w), the bridges weilSpace_eq_ker_sub and weilSpace_eq_eigenspace, weilSpace_id_one (⊥ at d = 1) and weilSpace_id_neg_one (⊤ at d = −1), with projectiveLine_weilSpace_id_neg_one_ne_bot pinning the sign at the pin; weilSpace_le_algebraic_iff_le_hodge by lefschetzOneOneEquality_holds. On an abelian surface this is W_K = ∧²_K H¹ (Weil1977, vanGeemen1994 §5, locators unverified); the eigenspace description is specific to surfaces. Names differ from plan §4 A3 (mem_weilSpace_iff, weilSpace_le_algebraic_iff_le_hodge). Conventions row \"Weil space\". Kernel about 120 s for the four original declarations (docs/gaps.md, Known weaknesses). Red team docs/sketches/weil-space.redteam.md.";
   - `"contributors"`: the prover's handle.
   Root import `public import HodgeLadder.Weil.Space` and `public import HodgeLadder.Tests.WeilSpace` in `HodgeLadder.lean`. `docs/roadmap.md` row `weil-space`: status `checked`, depends column adds `projective-line-class-nonzero`, notes "−d-eigenspace of `pullbackCohLinear f 2`; bridges to `ker (S − c • id)` and `Module.End.eigenspace`; sign pinned by `weilSpace_id_one` and the ℙ¹ test; surfaces only; `HodgeLadder.Weil.Space`; `docs/sketches/weil-space.redteam.md`".

7. `docs/gaps.md`, Known weaknesses, row "Kernel cost of upstream's `Module ℚ` instance": append to the description "`HodgeLadder.Weil.Space` (red team `weil-space`, 2026-11-28): `weilSpace` 39.3 s, `mem_weilSpace_iff` 29.4 s, `weilSpace_id_one` 12.7 s, `weilSpace_le_algebraic_iff_le_hodge` 37.7 s; kernel diagnostics on the last are dominated by `Ext`'s additive structure (`Functor.obj` 312,863 unfoldings, `AddCommGrpCat.str` 246,678, `AddGroup.toSubNegMonoid` 232,809). Measured on these four (serial `trace.profiler` kernel times): a `Module ℚ` shortcut takes the total from 119.1 s to 95.3 s (79.5 s with `pullbackCohLinear` rebuilt under it); an additive plus module shortcut takes the three ladder-internal declarations from 81.4 s to 15.2 s and the iff, which compares with upstream's `Hdg^1`, from 37.7 s to 42.5 s. With `shortQ` the re-elaborated body of `HodgeConjecture` is `Expr`-equal to the one without; ladder types that synthesize the instance (`Submodule ℚ H^n(X; ℚ)`, `finrank`) mention it, `rfl`-equal to upstream's", and to the consequence column "a decision on a shortcut should weigh the additive instance, since the `Module` instance alone recovers at most a third".

8. `docs/gaps.md`, "General lemmas kept local", category "Linear algebra: eigenspaces", new row: "| `HodgeLadder.Weil.weilSpace`, `mem_weilSpace_iff`, `weilSpace_eq_ker_sub`, `weilSpace_eq_eigenspace`, `weilSpace_id_one`, `weilSpace_id_neg_one`, `weilSpace_le_algebraic_iff_le_hodge` (the −d-eigenspace of f^* on H²(X; ℚ), Weil's W_K for an abelian surface) | `HodgeLadder.Weil.Space` | 47 (6 with O1) | no Weil-class definition in Mathlib or upstream at the pin; a bump checks upstream for one (`HodgeConjectureForAbelianVarieties` neighbourhood) and for `Module.End.eigenspace` renames; rung `weil-space` | 2026-11-28 |". Re-run `python3 tools/pinwalk.py` for the layer value after the edit.

## Optional

- O1. Move the iff out of the Weil module: add to `HodgeLadder/Divisor/LefschetzEquality.lean` `theorem le_algebraicCycleClassSpan_one_iff (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (S : Submodule ℚ H^(2 * 1)(X; ℚ)) : S ≤ algebraicCycleClassSpan X 1 ↔ S ≤ Hdg^1(X; ℚ) := by rw [lefschetzOneOneEquality_holds X]`, and keep `weilSpace_le_algebraic_iff_le_hodge` in a second file `HodgeLadder/Weil/Algebraic.lean` that imports both. `HodgeLadder.Weil.Space` then sits at layer 6, and the T1 consumers that need only the definition stop depending on the Lefschetz stack. The ledger's single `module` field then names `HodgeLadder.Weil.Space`, and the note names the second file.
- O2. A non-identity nonvanishing test before `weil-elliptic-square-nonzero`: the factor swap σ of ℙ¹ × ℙ¹ at d = 1, `weilSpace p1p1 σ 1 ≠ ⊥`, from σ^*[pt × ℙ¹] = [ℙ¹ × pt] and the independence of the two fibre classes. It waits on `fibre-class-pullback`; post it as a test rung if that rung moves first.

## Attempts that failed or were set aside

- Scratch `A`, `C`, `C2`: the committed proof of `weilSpace_id_one` copied into a non-module file fails (`Module.IsTorsionFree ℚ H^2(X; ℚ)` times out at 20,000 and 200,000 heartbeats); in module files it passes at 5,000 (`B5`), 10,000, 15,000.
- Scratch `P`: `simp [weilSpace]` for `= ⊥` and `= ⊤`, and `rfl` for `weilSpace_id_one`, all fail (finding 3); `(Submodule.eq_top_iff' _).mpr` is a spelling error (the iff takes no explicit argument), fixed in `P2`.
- Scratch `P`, `P2`: `rw [neg_smul, sub_neg_eq_add, weilSpace]` (whnf timeout) and `rw [Module.End.eigenspace_def, neg_smul, sub_neg_eq_add, Module.End.one_eq_id, weilSpace]` (isDefEq timeout) for the bridges; the working spellings are in change 3.
- Scratch `S1a`, `S1b`, `S2`, `S4`: the shortcut instances of finding 9, measured and set aside.
