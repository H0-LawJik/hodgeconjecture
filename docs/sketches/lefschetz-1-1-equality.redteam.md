# Red team: `lefschetz-1-1-equality`

Date: 2026-11-25. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean/Mathlib `v4.35.0-rc4`. Target: `HodgeLadder.lefschetzOneOneEquality_holds : HodgeLadder.LefschetzOneOneEquality` (`HodgeLadder.Divisor.LefschetzEquality`).

## 1. Is this the statement of the literature?

`GriffithsHarris1978` (Ch. 1 §2, the Lefschetz theorem on (1,1)-classes) and `Lefschetz1924`: on a smooth projective complex variety, every integral class of type (1,1) is the first Chern class of a line bundle, hence of a divisor. Over ℚ this gives Hdg^1(X; ℚ) equal to the ℚ-span of divisor classes. The Lean statement, field by field:

| Literature | Lean |
|---|---|
| smooth projective complex variety | `X : Over (Spec ↧ℂ)`, `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`, the upstream hypotheses of `LefschetzOneOne` (`Variants.lean:45`) |
| rational (1,1)-classes | `Hdg^1(X; ℚ)` = upstream `hodgeClasses ℚ X 1` (rational classes with de Rham image in F^1 ∩ conj F^1) |
| ℚ-span of divisor classes | upstream `algebraicCycleClassSpan X 1`: sSup of `span {cycleComponentSheafClass X x hx}` over points of coheight one, i.e. prime divisors |
| equality | `=`, by `le_antisymm` of upstream `LefschetzOneOne` (≤) and `CycleClassesAreHodgeOne` (≥) |

The statement restates no upstream object; it composes upstream `Prop`s through `lefschetzOneOneEquality_iff`. It is the rational form. The integral form (surjectivity of c₁ from Pic onto integral (1,1)-classes) is stronger and is not claimed; see the proposal below.

## 2. Are the hypotheses satisfiable?

Yes: rung `nonvacuity-tests` (checked) gives Spec ℂ with all three instances. That instance is degenerate in degree two: Spec ℂ has no point of coheight one, so both sides are ⊥ there. A witness with H² ≠ 0 (ℙ¹) is rung `projective-line-witness`, open.

## 3. Trivially true?

Attempts, all failed (scratch file, not committed):
- `intro X _ _ _; simp [algebraicCycleClassSpan]` on the equality: leaves `Hdg^1(X; ℚ) = sSup {…}`.
- `simp [algebraicCycleClassSpan]` on `algebraicCycleClassSpan X 1 = ⊥`: leaves a goal about each component class.
- `simp` on `Hdg^1(X; ℚ) = ⊥`: no progress.

Neither side unfolds to ⊥ or ⊤, and the coheight is compared in `ℕ∞` against the cast `↑1`, which is the intended value. The proof uses every hypothesis: `IsProjective` gives Noetherianity and Oka coherence (part A of `unit-extension-of-invertible`), `Smooth` gives the analytic space and local factoriality, `IsIntegral` the function field for `Scheme.ord`. What this section cannot exclude is a definition bug that makes H²(X; ℚ) zero for every X, so that the equality reads ⊥ = ⊥. That is item 7b.

## 4. Interface axioms

Not an interface rung; no structure with axioms is involved (decision 0003).

## 5. Checker

`python3 tools/check.py --no-build`: ACCEPTED. `HodgeLadder.lefschetzOneOneEquality_holds`, `cycleClassesAreHodgeOne_holds`, `cycleComponentSheafClass_mem_hodgeClasses_one`, `exists_unitExtension_of_isInvertible` depend on `[propext, Classical.choice, Quot.sound]`. The ledger names these declarations and the module `HodgeLadder.Divisor.LefschetzEquality`, whose imports cover all of them. The stack's unproved `AnalytificationGenerates` and `SectionSheafDeterminesClass` appear in no dependency of these declarations (they are `Prop` definitions and none of these theorems takes them as a hypothesis).

## 6. Conventions

| Convention | Row in `docs/conventions.md` | Does truth depend on it? |
|---|---|---|
| Divisor–Chern identity, sign `+` | "Divisor–Chern identity" | No. The ≥ direction needs only membership of [D] in a ℚ-subspace |
| Ideal sheaf 𝓘_D = 𝒪(−D), divisor `single ξ (−1)` | "Ideal sheaf of a prime divisor" (added in this pass) | No: −[D] ∈ Hdg^1 ⇔ [D] ∈ Hdg^1 (`neg_mem`) |
| Transition convention of the unit extension | "Unit extension of a line bundle" | No: the iso L^an ≅ E.section is a checked term, so E is the bundle the divisor–Chern hypothesis asks for; a sign there would also be absorbed by `neg_mem` |
| Exponential sequence, connecting-map sign, integer-to-rational map | existing rows | No for this span statement; c₁ enters only through Hodge-class membership |
| Hodge filtration, Hodge classes, fundamental-class normalization | existing rows | Only up to a nonzero scalar on each component class, which a span absorbs |
| Cycle-class model (Ext against injective model) | "Cycle-class model" | No: the port bridge is an equality at the pin, and any nonzero scalar would not change a span |

The October 2026 failure mode (`LekiliSheridan2026`) was a sign error in a cited result used for an identity. Here every borrowed sign feeds a membership in a subspace, so none of them can change the truth of the equality. They would matter for the integral form and for any degree or intersection-number statement built on this rung.

## 7. Equality first

The rung is an equality, proved exactly (`le_antisymm`), not up to a scalar. It is the checkpoint of decision 0004.

## 7b. Non-vacuity

The smallest test that fails if H² vanishes identically: `cycleComponentSheafClass ℙ¹ x hx ≠ 0` for a point `x` of ℙ¹, which is rung `projective-line-class-nonzero` (open; depends on `projective-line-witness`, `projective-line-point`, `contractible-open-acyclic`, and the checked `forget-support-exact`). It does not exist yet. Until it is checked, the repository has no proof that the codimension-one equality is about a nonzero space for any X.

## 8. Pin drift

All of the rung's dependencies were checked at the current pin `2ead713`; the port (`lefschetz-port`) was rebuilt at this pin and its own drift pass is `docs/sketches/lefschetz-port.redteam.md`. No drift to diff.

## 9. Verdict

**pass with changes.**

1. Done in this pass: add the conventions row "Ideal sheaf of a prime divisor".
2. Public copy (README, site, ledger note) describes the equality as checked and says that non-vacuity in degree two is pending `projective-line-class-nonzero`. It does not describe the equality as non-vacuous before that rung is checked.
3. Run `projective-line-test` (the ℙ¹ chain) next, before the Markman inventory. This makes the equality non-vacuous.
4. Proposed new rung (not required for this verdict): `lefschetz-1-1-integral`. Every integral class in H²(X; ℤ) whose rational image is Hodge is c₁ of an algebraic line bundle. The port's `exists_holomorphicUnitExtension_of_integral_hodgeClass` gives the analytic half. The algebraic half needs GAGA for line bundles. That rung is sign-sensitive and would need its own convention pass.
