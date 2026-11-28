# Sketch: `weierstrass-two-to-one`

Thinker sketch, 2026-11-28, `main` at `33ef5c1` (Lean and Mathlib `v4.35.0-rc4`). Issue #229, node C2 of `docs/notes/2026-11-27-t1-plan.md`. This is a plan of attack; it proves nothing. Every Lean statement below elaborated with `sorry` proofs in a scratch file importing only Mathlib (`lake env lean`, about 5 s, file deleted afterwards).

## Statement

In words: for the Weierstrass function ℘ of a lattice Λ and z, w off Λ, ℘ z = ℘ w exactly when z ≡ w or z ≡ −w mod Λ; every complex number is a value of ℘ at a point off Λ. The hypotheses z, w ∉ Λ and the requirement z ∉ Λ in the second theorem carry weight: Mathlib's ℘ has the junk value 0 on Λ (`PeriodPair.weierstrassP_coe`), so without them c = 0 would be hit trivially and ℘ l = ℘ l' would hold for all l, l' ∈ Λ.

```lean
theorem HodgeLadder.weierstrassP_eq_iff (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) :
    L.weierstrassP z = L.weierstrassP w ↔ z - w ∈ L.lattice ∨ z + w ∈ L.lattice
theorem HodgeLadder.weierstrassP_surjOn (L : PeriodPair) (c : ℂ) :
    ∃ z ∉ L.lattice, L.weierstrassP z = c
```

These are the plan's statements unchanged, for every `PeriodPair`. Mathlib's ℘ is the literature's ℘ (Σ over l ∈ Λ of (z − l)⁻² − l⁻², the l = 0 term reading z⁻² because 0⁻¹ = 0), with `g₂ = 60 G₄`, `g₃ = 140 G₆`, matching [Silverman2009] ch. VI (locator unverified).

## Why the ladder needs it

`elliptic-curve-uniformization` (C3) needs Φ z = [℘ z : ℘′ z / 2 : 1] to be a bijection ℂ/Λ → E(ℂ). Surjectivity of Φ is `weierstrassP_surjOn` plus the sign choice ±z for the y-coordinate. Injectivity of Φ is the forward direction of `weierstrassP_eq_iff`: if Φ z = Φ w and z ≡ −w then ℘′ w = −℘′ w, so 2w ∈ Λ and z ≡ w. The reverse direction is two lines (`weierstrassP_sub_coe`, `weierstrassP_neg`). C3 uses only the lattice c·ℤ[i] with c > 0 real (g₂ = 4), but the statement costs one small extra rung (normalization, sub-rung 6) in general, so it stays general.

## Proof idea

Recommended route: the argument principle on a period rectangle, the literature's route ([Silverman2009] ch. VI; Ahlfors, Complex Analysis, ch. 7, unverified).

1. **Surjectivity by Liouville (no counting).** If ℘ − c had no zero off Λ, then g = (℘ − c)⁻¹ off Λ, 0 on Λ, is entire: off Λ by `analyticOnNhd_weierstrassP`, at l ∈ Λ because ℘ − c has order −2 (`order_weierstrassP`), so g has order 2 and value 0. g is Λ-periodic, hence bounded (`IsZLattice.isCompact_range_of_periodic`), hence constant (`Differentiable.apply_eq_apply_of_bounded`), equal to g 0 = 0, against g z ≠ 0 off Λ. This is the pattern of Mathlib's own proof of `derivWeierstrassP_sq`.
2. **Winding on a rectangle.** For a in the open rectangle with corners z, w, Mathlib's boundary expression of (p − a)⁻¹ equals 2πi. Each side is a log difference by the fundamental theorem of calculus: bottom, top and right sides stay in the slit plane, so log(p − a) is a primitive; on the left side use log(a − p). The four terms telescope to log(−p₀₀) − log p₀₀ + log p₀₁ − log(−p₀₁) with p₀₀ = z − a in the lower half-plane and p₀₁ in the upper one, which is iπ + iπ by `arg_neg_eq_arg_add_pi_of_im_neg` and `arg_neg_eq_arg_sub_pi_of_im_pos`.
3. **Argument principle on a rectangle.** For f meromorphic, nowhere locally zero, analytic and nonzero on the boundary: on an open rectangle U slightly larger than R, `MeromorphicOn.extract_zeros_poles` gives f = ∏ (· − u)^{d u} · g codiscretely with g analytic and zero-free on U (the divisor is finite by `divisor_support_finite_of_subset` on the compact closure). Near each boundary point both sides are analytic, so they agree on a neighbourhood and logDeriv f = Σ d u · (· − u)⁻¹ + logDeriv g there (`logDeriv_mul`, `MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq`). Integrate: step 2 for u inside R, Cauchy-Goursat (`integral_boundary_rect_eq_zero_of_differentiableOn`) for u outside R and for logDeriv g; no u lies on ∂R since d u = 0 there.
4. **Periodic integrand.** If h(p + 1) = h p and h(p + τ) = h p, the boundary integral over the rectangle from a to a + 1 + (Im τ)i is 0. The vertical sides cancel by h(p + 1) = h p; the top side is the bottom side shifted by τ − Re τ, and `Function.Periodic.intervalIntegral_add_eq` absorbs the shift Re τ. No integrability hypothesis is needed for these two identities.
5. **Fundamental rectangle.** For L with ω₁ = 1 and Im ω₂ > 0 and a countable S, choose a so that ∂R(a) misses S + Λ (only countably many bad a.re and a.im); every z has exactly one representative mod Λ in the half-open rectangle (`toIcoDiv` in the imaginary direction with period Im ω₂, then in the real direction with period 1). Representatives of points of S lie in the open rectangle.
6. **Counting.** Take S = Λ ∪ (℘ − c)⁻¹(0) (countable: the divisor of a meromorphic function on ℂ has locally finite support). logDeriv(℘ − c) is Λ-periodic, so steps 3 and 4 give Σ of orders over the open rectangle = 0. The open rectangle holds exactly one lattice point, of order −2, so the c-points in it have total order 2.
7. **Normalization.** Swap ω₁, ω₂ if Im(ω₂/ω₁) < 0 (same lattice, same ℘) and rescale by μ = ω₁⁻¹: ℘ of μΛ at μz is μ⁻²℘(z) (reindex the `tsum` along l ↦ μl). Both statements transfer.
8. **Two-to-one.** Let ℘ w = c. If 2w ∈ Λ then ℘′ w = 0 (odd and periodic), so the order of ℘ − c at w is at least 2 (`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`); otherwise w and −w are two distinct classes of order at least 1. Either way they use up the total 2 of step 6, so any z off Λ with ℘ z = c is ≡ ±w.

Fallback route (topological, recorded, no rung yet). Φ : ℂ/Λ → E(ℂ) for the T1 lattice only. E(ℂ) is path-connected as the image of the torus once step 1 gives surjectivity of Φ. If Φ is a local homeomorphism, then `isLocalHomeomorph_iff_isCoveringMap` (compact T2 source) makes it a covering, `IsCoveringMap.monodromy_bijective` makes all fibres equinumerous, and the fibre over O is the single class of 0, so Φ is bijective. The forward direction of step 8 for this lattice then follows from ℘′² = 4℘³ − 4℘. Local homeomorphy needs three inverse-function arguments: in x where ℘′ ≠ 0; in y at zeros of ℘′, using ℘″ = 6℘² − 2 ∈ {−2, 4} at the roots 0, ±1; and at 0 in the chart u = 2℘/℘′ = −z + O(z³). It avoids steps 2 to 6. The costs: ℘″ and the Laurent data of ℘/℘′ at 0 (Mathlib has neither), the implicit-function step on the curve in all three charts, and a result only for g₂ = 4, g₃ = 0. That result would be a new, weaker rung, so this route cannot close the rung as posted. Comparable size; route A is preferred for literature fidelity and for general lemmas (steps 2, 3) that the ladder can reuse.

## What Mathlib has

Checked by `grep` in `.lake/packages/mathlib`:

| Need | Declaration |
|---|---|
| ℘, ℘′, lattice, periodicity, parity, zeros of junk | `PeriodPair`, `PeriodPair.lattice`, `weierstrassP`, `derivWeierstrassP`, `weierstrassP_add_coe`, `weierstrassP_sub_coe`, `weierstrassP_neg`, `derivWeierstrassP_neg`, `derivWeierstrassP_add_coe`, `weierstrassP_coe`, `deriv_weierstrassP` |
| analyticity, poles | `analyticOnNhd_weierstrassP`, `analyticOnNhd_derivWeierstrassP`, `meromorphic_weierstrassP`, `order_weierstrassP` (= −2 on Λ), `ite_eq_one_sub_sq_mul_weierstrassP` |
| differential equation | `derivWeierstrassP_sq` (℘′² = 4℘³ − g₂℘ − g₃, g₂ = 60 G₄) |
| Liouville, compact range | `Differentiable.apply_eq_apply_of_bounded`, `IsZLattice.isCompact_range_of_periodic` |
| rectangles | `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`, `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` |
| divisors, factorization, log-derivatives | `MeromorphicOn.divisor`, `MeromorphicOn.divisor_support_finite_of_subset`, `MeromorphicOn.extract_zeros_poles`, `MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq`, `logDeriv_mul`, `MeromorphicOn.divisor_sub_const_self` |
| orders | `meromorphicOrderAt`, `tendsto_zero_of_meromorphicOrderAt_pos`, `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` |
| log, arg, periodic integrals | `Complex.log`, `arg_neg_eq_arg_add_pi_of_im_neg`, `arg_neg_eq_arg_sub_pi_of_im_pos`, `Function.Periodic.intervalIntegral_add_eq`, `toIcoDiv` |
| fallback only | `isLocalHomeomorph_iff_isCoveringMap`, `IsCoveringMapOn.of_isLocalHomeomorphOn`, `IsCoveringMap.monodromy_bijective`, `HasStrictFDerivAt.toOpenPartialHomeomorph`, `Polynomial.isCoveringMapOn_eval` (template) |

## What is missing

No residue theorem, argument principle or winding number for rectangles (grep for `residue`, `argument principle` in `Mathlib/Analysis` finds none); no zero counting for elliptic functions; no homogeneity of ℘ under scaling of Λ; no ℘″; no `CompactSpace (ℂ ⧸ L.lattice.toAddSubgroup)` instance (C3's need, untouched here).

## Sub-rungs

`R` abbreviates `[[a.re, a.re + 1]] ×ℂ [[a.im, a.im + L.ω₂.im]]`, `R°` its `Ioo ×ℂ Ioo`. `rectIntegral f z w` is a local `def` equal by definition to the left side of `integral_boundary_rect_eq_zero_of_differentiableOn` (elaborated; `example` closes by that theorem).

| # | Id | Lean statement (proof omitted) | Size | Depends on |
|---|---|---|---|---|
| 1 | `weierstrass-surjective` | `weierstrassP_surjOn (L : PeriodPair) (c : ℂ) : ∃ z ∉ L.lattice, L.weierstrassP z = c` | small | none |
| 2 | `rect-winding` | `rectIntegral_sub_inv {z w a : ℂ} (h₁ : z.re < a.re) (h₂ : a.re < w.re) (h₃ : z.im < a.im) (h₄ : a.im < w.im) : rectIntegral (fun p ↦ (p - a)⁻¹) z w = 2 * π * I` | medium | none |
| 3 | `rect-argument-principle` | `rectIntegral_logDeriv {f : ℂ → ℂ} (hf : Meromorphic f) (hord : ∀ u, meromorphicOrderAt f u ≠ ⊤) {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im) (hbd : ∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (Ioo z.re w.re ×ℂ Ioo z.im w.im), AnalyticAt ℂ f p ∧ f p ≠ 0) : rectIntegral (logDeriv f) z w = 2 * π * I * ∑ᶠ u ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im, ((divisor f univ u : ℤ) : ℂ)` | medium to large | 2 |
| 4 | `rect-periodic` | `rectIntegral_eq_zero_of_periodic {h : ℂ → ℂ} {τ : ℂ} (h₁ : ∀ p, h (p + 1) = h p) (hτ : ∀ p, h (p + τ) = h p) (a : ℂ) : rectIntegral h a (a + 1 + τ.im * I) = 0` | small | none |
| 5 | `lattice-fundamental-rectangle` | `exists_fundamental_rect (L : PeriodPair) (h₁ : L.ω₁ = 1) (h₂ : 0 < L.ω₂.im) {S : Set ℂ} (hS : S.Countable) : ∃ a : ℂ, (∀ p ∈ R \ R°, ∀ l ∈ L.lattice, p + l ∉ S) ∧ ∀ z : ℂ, ∃! l : L.lattice, z + l ∈ Ico a.re (a.re + 1) ×ℂ Ico a.im (a.im + L.ω₂.im)` | medium | none |
| 6 | `period-pair-normalize` | `exists_normalized (L : PeriodPair) : ∃ (L' : PeriodPair) (μ : ℂ), μ ≠ 0 ∧ L'.ω₁ = 1 ∧ 0 < L'.ω₂.im ∧ (∀ z, μ * z ∈ L'.lattice ↔ z ∈ L.lattice) ∧ ∀ z, L'.weierstrassP (μ * z) = μ⁻¹ ^ 2 * L.weierstrassP z` | small to medium | none |
| 7 | `weierstrass-order-sum` | `weierstrassP_sub_order_sum (L : PeriodPair) (h₁ : L.ω₁ = 1) (h₂ : 0 < L.ω₂.im) (c : ℂ) : ∃ F : Finset ℂ, (∀ u ∈ F, u ∉ L.lattice ∧ L.weierstrassP u = c) ∧ (∀ u ∈ F, ∀ v ∈ F, u - v ∈ L.lattice → u = v) ∧ (∀ z ∉ L.lattice, L.weierstrassP z = c → ∃ u ∈ F, z - u ∈ L.lattice) ∧ ∑ u ∈ F, divisor (fun p ↦ L.weierstrassP p - c) univ u = 2` | medium | 3, 4, 5 |
| 8 | `weierstrass-two-to-one` | the Statement, with `two_le_divisor_of_two_mul_mem (L) (hw : w ∉ L.lattice) (h2 : 2 * w ∈ L.lattice) : 2 ≤ divisor (fun p ↦ L.weierstrassP p - L.weierstrassP w) univ w` and the test `weierstrassP_half_ne (L) : L.weierstrassP (L.ω₁ / 2) ≠ L.weierstrassP (L.ω₂ / 2)` | medium | 1, 6, 7 |

Sub-rung 7 is the stated counting sub-rung the inherited kill criterion asks for, an exact equality (decision 0004). Sub-rungs 2, 3, 4 are general complex analysis kept local (decision 0011; rows for `docs/gaps.md`). Estimate: eight prover sessions, 900 to 1300 lines in total, with 3 as the main risk. Dispatch `rect-winding` first (head of the critical path 2 → 3 → 7 → 8); `weierstrass-surjective`, `rect-periodic`, `lattice-fundamental-rectangle` and `period-pair-normalize` have no dependency and can run in parallel.

### Kill criteria

- Inherited (`cup-odd-degree-test`, plan §7): this rung released twice without a stated counting sub-rung ends the elliptic route. Posting sub-rung 7 as `stated` after the red team meets it.
- `rect-argument-principle` released twice: open a thinker session on the fallback route (a new rung for the T1 lattice, `elliptic-curve-covering`), and leave this rung `open`.
- Both `rect-argument-principle` and the fallback released twice each: the elliptic route is dead; T1 stays at `weil-surface-reduction`.

### Sign and normalization risks

- **Orientation of the rectangle.** Mathlib's expression is counterclockwise (bottom − top + i·right − i·left); sub-rung 2 gives +2πi. A reversed orientation flips the signs of 2 and 3 but leaves 7 unchanged (zeros minus poles = 0 either way). The red team should add a test that 2's value differs from −2πi.
- **Lattice basis (c, ic) versus (c, −ic).** The Statement depends only on the set Λ; both bases give the same `lattice` (sub-rung 6 swaps ω₁, ω₂ when Im(ω₂/ω₁) < 0, which keeps the lattice and ℘). The basis orientation enters C3 and `elliptic-curve-cohomology` (row "Winding-class pullback and the rotation of T²"), and sub-rung 6 records which swap it makes so C3 does not inherit a hidden choice. Done in period-pair-normalize: (c, −ic) is swapped to (−ic, c) with μ = i c⁻¹; see its red team, finding 7.
- **g₂ = 4 for y² = x³ − x.** Not used here. With Mathlib's g₂ = 60 G₄, g₃ = 140 G₆, the pair (℘, ℘′/2) lies on y² = x³ − x exactly when g₂ = 4 and g₃ = 0 (red team of `elliptic-curve-points`, finding 10); g₂(cΛ) = c⁻⁴ g₂(Λ) follows from the homogeneity in sub-rung 6 (G₄ scales by μ⁻⁴), which C1 or C3 can reuse to fix c.
- **Junk values.** ℘ = 0 and ℘′ = 0 on Λ; every statement above excludes Λ where it matters. `weierstrassP_half_ne` fails if the forward direction were dropped.

## Sources

- [Silverman2009] ch. VI: ℘, its differential equation, the count of values of an elliptic function on a period parallelogram (locators unverified).
- Ahlfors, Complex Analysis, ch. 7, and the argument principle: unverified (no key in `docs/references.md`).
- Mathlib declarations: as listed, at the pin.
- The fallback covering argument: unverified as a literature citation; it is standard topology assembled here.
