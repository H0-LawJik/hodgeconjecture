# Red team: `period-pair-normalize`

Date: 2026-11-28. Branch `track/period-pair-normalize` at `1042790`, worktree off `a509ee0` (equal to `main`). Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean `v4.35.0-rc4`. Mathlib only; the rung reads no upstream declaration. Probes in a scratch file under the worktree (deleted), compiled with `lake env lean` against the built module.

**Verdict: pass with changes.** No exponent and no orientation is off. `weierstrassP_smul` (μ⁻²), `derivWeierstrassP_smul` (μ⁻³), `G_smul` (μ⁻ⁿ), `g₂_smul` (μ⁻⁴), `g₃_smul` (μ⁻⁶) are the literature's weights, proved exactly for every μ ≠ 0 and every z; the lattice transport runs in the direction the statement needs; `oriented` gives Im τ > 0 and `normalize_of_pos`, `normalize_of_neg` record the swap. The changes: tests that separate each load-bearing exponent and the transport direction from their inverses (the posted ℤ[i] tests use μ ∈ {1, i}, where μ⁻² = μ² and iℤ[i] = ℤ[i] hide both); explicit normalization of the bases (c, ic) and (c, −ic); ledger, conventions and gaps bookkeeping; notes on the two consumers C1 and C3.

## Findings

1. **Signs first (attack 6).** Nothing is off. Independent computation: with Λ' = μΛ and l' = μl, ℘_{Λ'}(μz) = Σ_l [1/(μz − μl)² − 1/(μl)²] = μ⁻²℘_Λ(z); ℘′ = −Σ 2/(z − l)³ gives μ⁻³; G_n = Σ (lⁿ)⁻¹ gives μ⁻ⁿ; g₂ = 60G₄, g₃ = 140G₆ give μ⁻⁴, μ⁻⁶. The junk values agree: the term l = z (z ∈ Λ) is 1/0 = 0 on both sides, the term l = 0 of G is 0⁻¹ = 0 on both sides, so the identities hold for every z, as the docstrings say. `tsum_mul_left` holds without summability in a division ring, so no summability hypothesis is hidden. Orientation: for Im(ω₂/ω₁) < 0 the swapped ratio is ω₁/ω₂ = (ω₂/ω₁)⁻¹ and Im(w⁻¹) = −Im w/|w|² > 0, the computation in `im_div_oriented_pos`.

2. **Literature (attack 1).** `Silverman2009` ch. VI (locators unverified, as in `docs/references.md`): ℘(z; Λ) = z⁻² + Σ' [(z − λ)⁻² − λ⁻²], G_{2k}(Λ) = Σ' λ^{−2k}, g₂ = 60G₄, g₃ = 140G₆, homogeneity ℘(cz; cΛ) = c⁻²℘(z; Λ), G_{2k}(cΛ) = c^{−2k}G_{2k}(Λ), and the normal form Λ = ℤ + ℤτ with τ in the upper half-plane. Field by field against Mathlib `PeriodPair` at the pin: `ω₁`, `ω₂` with `indep : LinearIndependent ℝ ![ω₁, ω₂]` (no orientation field, so the swap is needed); `lattice = span ℤ {ω₁, ω₂}`; `weierstrassP` sums over all of Λ with the l = 0 term equal to z⁻² (since 1/0² = 0), Silverman's z⁻² + Σ'; `G` is Σ' through the junk 0⁻¹ = 0; `g₂`, `g₃` match. `exists_normalized` is the statement posted in the sketch, row 6, verbatim.

3. **Hypotheses satisfiable (attack 2).** The only hypothesis is `L : PeriodPair`; `gaussianPair` and `conjGaussianPair` inhabit it. `normalize_ω₁` and `exists_normalized` hold for both.

4. **Trivial truth (attack 3).** Tried and failed: the existential cannot be met by a degenerate witness. The transport clause forces `L'.lattice = μ · L.lattice` (w ∈ Λ' ↔ μ⁻¹w ∈ Λ), so `L'.weierstrassP` is fixed by `weierstrassP_congr` and the ℘ clause is a genuine homogeneity claim. It would be trivially true only if ℘ were identically 0; probe P1 refutes that on every lattice in five lines from Mathlib's `not_continuousAt_weierstrassP` at 0. No `ℕ∞` coercion, no empty index, no unused hypothesis (μ ≠ 0 is used by `smulLatticeEquiv`).

5. **The exponent tests (attack 1, brief).** The posted test `weierstrassP_gaussianPair_I_mul` uses μ = i, where i⁻² = i² = −1, so it holds with the wrong weight +2 as well. Probe P2 (μ = 2 on every lattice): `¬ ∀ z, ℘_{2Λ}(2z) = 2² ℘_Λ(z)`, from P1 and 1/4 ≠ 4; P2′ restates the posted value ℘_{2Λ}(2z) = ℘_Λ(z)/4. For ℘′ the μ = i test does separate: i⁻³ = i and i³ = −i, and probe P7 proves ℘′_{ℤ[i]}(iz) = i℘′_{ℤ[i]}(z) from `derivWeierstrassP_smul` with a local `derivWeierstrassP_congr`. This is the sign C3 consumes (`ellipticI` is (x, y) ↦ (−x, iy), row "Complex multiplication on E"; weight +3 would give [−i]). The separation needs ℘′ ≢ 0 on ℤ[i], standard (a pole of order 3) and not formalized here. For G_n, g₂, g₃ a separating test needs G_n(Λ) ≠ 0 for some Λ; g₂(ℤ[i]) ≠ 0 is the content of the open rung `weierstrass-lattice-i` and has no cheap proof at the pin (it needs the discriminant or an estimate of Σ' l⁻⁴), so the structural argument of finding 1 stands for those weights. Probe P5 proves g₃(ℤ[i]) = 0 from `G_smul` at μ = i (i⁻⁶ = −1), a conjunct of `weierstrass-lattice-i`.

6. **Lattice transport (attack 3).** `mem_smul_lattice`: μz ∈ (smul μ L).lattice ↔ z ∈ L.lattice, the direction for L' = μΛ. The posted tests have μ ∈ {1, i} and iℤ[i] = ℤ[i], where both directions hold. Probe P3 refutes the reversed direction (z ∈ L' ↔ μz ∈ L) for μ = 2 on every lattice: ω₁ would lie in 2Λ, so ω₁/2 ∈ Λ, against Mathlib's `ω₁_div_two_notMem_lattice`.

7. **Orientation and the consumers (attack 2).** Probes P4a, P4b, P4c, P6, for any L with ω₂ = ±iω₁ (c := ω₁ ≠ 0 arbitrary):
   - (c, ic): kept, μ = c⁻¹, τ = i.
   - (c, −ic): swapped to (−ic, c), μ = (−ic)⁻¹ = i c⁻¹, τ = c/(−ic) = i. Then ℘_{(1,i)}(μz) = μ⁻²℘_Λ(z) = −c²℘_Λ(z) and ℘′_{(1,i)}(μz) = μ⁻³℘′_Λ(z) = i c³ ℘′_Λ(z).
   - In both cases the oriented basis satisfies ω₂ = iω₁ (P4c), so multiplication by i acts on its coordinates (s, t) as `rot`, (s, t) ↦ (−t, s), in both cases (row "Winding-class pullback and the rotation of T²"). The swap removes the (c, −ic) case at the level of the basis.
   - `oriented (swap L) = oriented L` (P6): the oriented basis depends only on the unordered pair. (ic, c) normalizes like (c, ic) with μ = c⁻¹; (−ic, c) is kept and equals the oriented form of (c, −ic).
   - The hazard is the scale: a consumer that starts from (c, −ic) and composes with z ↦ μz picks up μ = i c⁻¹, which negates the x-coordinate ℘ and multiplies ℘′ by i, the automorphism [i] of y² = x³ − x. C3 should build Φ on (c, ic) with c > 0 real, where μ = c⁻¹ > 0 (P4a). `swap` also permutes Mathlib's `latticeBasis` and `latticeEquivProd`, which C3 and C7 read for coordinates.

8. **Mathlib equivalents (attack 4).** `grep` of `.lake/packages/mathlib/Mathlib` at the pin: `PeriodPair` occurs only in `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`, with no `swap`, `smul`, scaling or homogeneity lemma for `weierstrassP`, `derivWeierstrassP` or `G`. The Eisenstein-series homogeneity in `NumberTheory/ModularForms/EisensteinSeries/` is the slash action in τ on a different object. No upstream or port file mentions `PeriodPair`. All 37 declarations are local and new.

9. **Interface rung (question 4).** Not applicable: no structure, no axiom.

10. **Checker (question 5).** `python3 tools/check.py --no-build` in the worktree: `ACCEPTED: all checks passed`; each of the 37 ledger names `HodgeLadder.Period.*` reports `[Classical.choice, Quot.sound, propext]`. The ledger's names are the file's declarations, one for one. The probes P1 to P7 also report the three standard axioms.

11. **Conventions (question 6).** Used: Mathlib's `PeriodPair` without orientation; Σ' through junk 0⁻¹ = 0; g₂ = 60G₄, g₃ = 140G₆; the orientation choice Im τ > 0; the scale μ = ω₁⁻¹ of the oriented basis; the transport direction μΛ. None is in `docs/conventions.md`; a row is required (change R4). Truth dependence: `exists_normalized` depends only on Im τ > 0 (the lattice and ℘ are basis-free); the homogeneity identities are equalities with exact weights and hold under either junk convention; the g₂, g₃ weights are independent of the factors 60, 140. Consumers depend on more: C3's g₂ = 4 needs Mathlib's 60G₄ (row "Plane cubic E and its charts", finding 10 of `elliptic-curve-points`), and C3, C7 need the basis (c, ic).

12. **Equality first (question 7).** Every identity is exact, no scalar. `exists_normalized` is an existence statement whose components are equalities and an iff; no inclusion is involved.

13. **Non-vacuity (question 7b).** Smallest tests that fail if the rung were trivial: P1 `∃ z, L.weierstrassP z ≠ 0` (fails if ℘ ≡ 0) and P2 (fails if the weight were +2). Neither exists in the candidate; change R1 adds them.

14. **Pin drift (question 8).** Checked at the current pin; no drift. On a Mathlib bump, a change of `weierstrassP` to an explicit z⁻² + Σ' form, or of `G` to a sum over Λ ∖ {0}, keeps every statement true and may break proofs; a change of `g₂` away from 60G₄ keeps `g₂_smul` true and breaks C3's g₂ = 4.

15. **Placement (attack 5).** `HodgeLadder/Period/Pair/Normalize.lean`, layer 0, no downstream module (`python3 tools/pinwalk.py --hubs`). Keep it; it is `next.py`'s fallback, and the other `weierstrass-two-to-one` sub-rungs about `PeriodPair` (`lattice-fundamental-rectangle`, `weierstrass-order-sum`) fit under `HodgeLadder/Period/`. `swap` and `smul` are short names inside `HodgeLadder.Period`; with `open Function` a bare `swap` is ambiguous. Harmless at present; no rename required.

## Required changes

**R1. Tests in `HodgeLadder/Period/Pair/Normalize.lean`.** Add after `weierstrassP_gaussianPair_I_mul` (all compiled in scratch against the module, standard axioms):

```lean
/-- `℘` is not identically zero: it is discontinuous at `0`. Guards the homogeneity statements
against vacuity. -/
theorem exists_weierstrassP_ne_zero (L : PeriodPair) : ∃ z, L.weierstrassP z ≠ 0 := by
  by_contra h
  push Not at h
  have : L.weierstrassP = fun _ => 0 := funext h
  exact L.not_continuousAt_weierstrassP 0 (zero_mem _) (by rw [this]; exact continuousAt_const)

/-- Test at `μ = 2`: `℘_{2Λ}(2 z) = ℘_Λ(z) / 4`. -/
theorem weierstrassP_smul_two (L : PeriodPair) (z : ℂ) :
    (smul 2 two_ne_zero L).weierstrassP (2 * z) = L.weierstrassP z / 4 := by
  rw [weierstrassP_smul]; ring

/-- Test: the weight `+2` fails at `μ = 2` on every lattice, so `weierstrassP_smul` separates
`μ⁻²` from `μ²` (the `μ = i` test cannot). -/
theorem not_weierstrassP_smul_two_sq (L : PeriodPair) :
    ¬ ∀ z, (smul 2 two_ne_zero L).weierstrassP (2 * z) = 2 ^ 2 * L.weierstrassP z := by
  intro h
  obtain ⟨z, hz⟩ := exists_weierstrassP_ne_zero L
  have h1 := h z
  rw [weierstrassP_smul] at h1
  apply hz
  have : ((2:ℂ)⁻¹ ^ 2 - 2 ^ 2) * L.weierstrassP z = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · norm_num at h0
  · exact h0

/-- Test: the reversed transport `z ∈ μΛ ↔ μ z ∈ Λ` fails at `μ = 2` on every lattice. -/
theorem not_forall_mem_smul_two_iff_two_mul_mem (L : PeriodPair) :
    ¬ ∀ z, z ∈ (smul 2 two_ne_zero L).lattice ↔ 2 * z ∈ L.lattice := by
  intro h
  have h1 : L.ω₁ ∈ (smul 2 two_ne_zero L).lattice :=
    (h L.ω₁).2 (by
      have := L.lattice.add_mem L.ω₁_mem_lattice L.ω₁_mem_lattice
      rwa [← two_mul] at this)
  have h2 : 2 * (L.ω₁ / 2) ∈ (smul 2 two_ne_zero L).lattice := by
    rwa [mul_div_cancel₀ _ two_ne_zero]
  exact L.ω₁_div_two_notMem_lattice ((mem_smul_lattice 2 two_ne_zero L _).1 h2)

/-- A basis `(c, i c)` is kept: scale `c⁻¹`, `τ = i`. -/
theorem normalize_of_eq_I_mul (L : PeriodPair) (h : L.ω₂ = Complex.I * L.ω₁) :
    oriented L = L ∧ normalizeScale L = L.ω₁⁻¹ ∧ (normalize L).ω₂ = Complex.I := by
  have hp : 0 < (L.ω₂ / L.ω₁).im := by
    rw [h, mul_div_cancel_right₀ _ (ω₁_ne_zero L)]; simp
  refine ⟨oriented_of_pos hp, (normalize_of_pos hp).1, ?_⟩
  rw [(normalize_of_pos hp).2, h, mul_div_cancel_right₀ _ (ω₁_ne_zero L)]

/-- A basis `(c, -i c)` is swapped to `(-i c, c)`: scale `i c⁻¹`, `τ = i`. -/
theorem normalize_of_eq_neg_I_mul (L : PeriodPair) (h : L.ω₂ = -Complex.I * L.ω₁) :
    oriented L = swap L ∧ normalizeScale L = Complex.I * L.ω₁⁻¹ ∧
      (normalize L).ω₂ = Complex.I := by
  have h1 := ω₁_ne_zero L
  have hn : (L.ω₂ / L.ω₁).im < 0 := by
    rw [h, mul_div_cancel_right₀ _ h1]; simp
  refine ⟨oriented_of_neg hn, ?_, ?_⟩
  · rw [(normalize_of_neg hn).1, h, mul_inv, inv_neg, Complex.inv_I, neg_neg]
  · rw [(normalize_of_neg hn).2, h]; field_simp; rw [Complex.I_sq]

/-- For `(c, ± i c)` the oriented basis satisfies `ω₂ = i ω₁`, so multiplication by `i` acts on
its coordinates as `rot` (row "Winding-class pullback and the rotation of T²"). -/
theorem oriented_ω₂_eq_I_mul (L : PeriodPair)
    (h : L.ω₂ = Complex.I * L.ω₁ ∨ L.ω₂ = -Complex.I * L.ω₁) :
    (oriented L).ω₂ = Complex.I * (oriented L).ω₁ := by
  rcases h with h | h
  · rw [(normalize_of_eq_I_mul L h).1, h]
  · rw [(normalize_of_eq_neg_I_mul L h).1]; simp only [swap]; rw [h, ← mul_assoc]; simp

/-- The oriented basis depends only on the unordered pair `{ω₁, ω₂}`. -/
theorem oriented_swap (L : PeriodPair) : oriented (swap L) = oriented L := by
  rcases lt_or_gt_of_ne (im_div_ne_zero L) with h | h
  · rw [oriented_of_neg h]
    apply oriented_of_pos
    show 0 < (L.ω₁ / L.ω₂).im
    rw [← inv_div, Complex.inv_im]
    exact div_pos (neg_pos.mpr h)
      (Complex.normSq_pos.mpr (div_ne_zero (ω₂_ne_zero L) (ω₁_ne_zero L)))
  · rw [oriented_of_pos h]
    have hn : ((swap L).ω₂ / (swap L).ω₁).im < 0 := by
      show (L.ω₁ / L.ω₂).im < 0
      rw [← inv_div, Complex.inv_im]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos h)
        (Complex.normSq_pos.mpr (div_ne_zero (ω₂_ne_zero L) (ω₁_ne_zero L)))
    rw [oriented_of_neg hn]
    rfl

/-- `℘′` depends only on the lattice. -/
theorem derivWeierstrassP_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.derivWeierstrassP = L'.derivWeierstrassP := by
  funext z
  unfold PeriodPair.derivWeierstrassP
  congr 1
  exact (Equiv.subtypeEquivProp (by rw [h])).tsum_eq _ |>.symm.trans rfl

/-- Test of the weight `-3`: `℘′_{ℤ[i]}(i z) = i ℘′_{ℤ[i]}(z)`, since `i⁻³ = i` (the weight `+3`
would give `-i`, the automorphism `[-i]`). -/
theorem derivWeierstrassP_gaussianPair_I_mul (z : ℂ) :
    gaussianPair.derivWeierstrassP (Complex.I * z) =
      Complex.I * gaussianPair.derivWeierstrassP z := by
  have h := derivWeierstrassP_smul Complex.I Complex.I_ne_zero gaussianPair z
  rw [derivWeierstrassP_congr smul_I_gaussianPair_lattice] at h
  rw [h, Complex.inv_I]
  linear_combination (-Complex.I * gaussianPair.derivWeierstrassP z) * Complex.I_sq
```

Move `derivWeierstrassP_congr` next to `weierstrassP_congr` if preferred. In the module docstring, replace the `Tests` bullet with:

```
* Tests: `(1, i)` is normalized with scale `1`; `(1, -i)` is swapped, scale `i`, `τ = i`;
  `(c, i c)` is kept with scale `c⁻¹` and `(c, -i c)` swapped to `(-i c, c)` with scale `i c⁻¹`,
  both with `τ = i` and oriented basis `ω₂ = i ω₁`; `℘_{ℤ[i]}(i z) = -℘_{ℤ[i]}(z)` and
  `℘′_{ℤ[i]}(i z) = i ℘′_{ℤ[i]}(z)`; at `μ = 2` the weight `+2` and the reversed lattice transport
  fail on every lattice (`℘ ≢ 0`).
```

**R2. Ledger, `period-pair-normalize`.** Append to `declarations`: `HodgeLadder.Period.exists_weierstrassP_ne_zero`, `HodgeLadder.Period.weierstrassP_smul_two`, `HodgeLadder.Period.not_weierstrassP_smul_two_sq`, `HodgeLadder.Period.not_forall_mem_smul_two_iff_two_mul_mem`, `HodgeLadder.Period.normalize_of_eq_I_mul`, `HodgeLadder.Period.normalize_of_eq_neg_I_mul`, `HodgeLadder.Period.oriented_ω₂_eq_I_mul`, `HodgeLadder.Period.oriented_swap`, `HodgeLadder.Period.derivWeierstrassP_congr`, `HodgeLadder.Period.derivWeierstrassP_gaussianPair_I_mul`. In `note`, replace `Red team: pending.` with:

`Red team: pass with changes (docs/sketches/period-pair-normalize.redteam.md). Tests separate μ⁻² from μ² (μ = 2, ℘ ≢ 0: not_weierstrassP_smul_two_sq), μ⁻³ from μ³ (℘′(iz) = i℘′(z) on ℤ[i]) and the transport direction (not_forall_mem_smul_two_iff_two_mul_mem). (c, ic) is kept with μ = c⁻¹; (c, −ic) is swapped to (−ic, c) with μ = i c⁻¹; both give τ = i and an oriented basis with ω₂ = iω₁, on which multiplication by i is rot. Row "Period-pair normalization and homogeneity of ℘" in docs/conventions.md.`

**R3. Ledger notes on the consumers.** Append to the `note` of `elliptic-curve-uniformization`:

`Basis (red team period-pair-normalize, finding 7): build Φ on the PeriodPair (c, ic) with c > 0 real; normalize keeps it with μ = c⁻¹ (normalize_of_eq_I_mul). From (c, −ic), normalize swaps to (−ic, c) with μ = i c⁻¹, and ℘, ℘′ pick up −c² and i c³ (the automorphism [i]). Fix c through g₂_smul: g₂(cℤ[i]) = c⁻⁴ g₂(ℤ[i]).`

Append to the `note` of `weierstrass-lattice-i`:

`Three conjuncts follow in a few lines from period-pair-normalize: ℘(iz) = −℘(z) is weierstrassP_gaussianPair_I_mul, ℘′(iz) = i℘′(z) is derivWeierstrassP_gaussianPair_I_mul, and g₃ = 0 follows from G_smul at μ = i (i⁻⁶ = −1; checked in the red team's scratch). The content left is g₂(ℤ[i]) ≠ 0.`

**R4. `docs/conventions.md`.** Add after the row "Complex multiplication on E":

```
| Period-pair normalization and homogeneity of ℘ | this repository, `HodgeLadder.Period.swap`, `smul`, `oriented`, `oriented_swap`, `normalizeScale`, `normalize`, `normalize_of_pos`, `normalize_of_neg`, `normalize_of_eq_I_mul`, `normalize_of_eq_neg_I_mul`, `oriented_ω₂_eq_I_mul`, `mem_smul_lattice`, `weierstrassP_smul`, `derivWeierstrassP_smul`, `G_smul`, `g₂_smul`, `g₃_smul` (`HodgeLadder/Period/Pair/Normalize.lean`, rung `period-pair-normalize`); Mathlib `PeriodPair`, `PeriodPair.lattice`, `weierstrassP`, `derivWeierstrassP`, `G`, `g₂`, `g₃` (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`) | Mathlib's `PeriodPair` carries no orientation; ℘ sums over all of Λ with the l = 0 term z⁻² (1/0 = 0), `G n` is Σ' l⁻ⁿ through 0⁻¹ = 0, `g₂ = 60 G 4`, `g₃ = 140 G 6`, ℘′ = −Σ 2/(z − l)³, the normalizations of `Silverman2009` ch. VI (locator unverified). `oriented L` keeps (ω₁, ω₂) when Im(ω₂/ω₁) > 0 and swaps to (ω₂, ω₁) when Im(ω₂/ω₁) < 0, and depends only on the unordered pair; `normalize L = μ · oriented L = (1, τ)` with μ = `normalizeScale L` = ω₁⁻¹ of the oriented basis and τ = ω₂/ω₁ of the oriented basis, Im τ > 0. Transport μz ∈ μΛ ↔ z ∈ Λ. Weights, exact for every μ ≠ 0 and every z: ℘_{μΛ}(μz) = μ⁻²℘_Λ(z), ℘′ μ⁻³, G_n μ⁻ⁿ, g₂ μ⁻⁴, g₃ μ⁻⁶. For c ≠ 0: (c, ic) is kept, μ = c⁻¹, τ = i; (c, −ic) is swapped to (−ic, c), μ = i c⁻¹, τ = i, so ℘_{(1,i)}(μz) = −c²℘_Λ(z) and ℘′_{(1,i)}(μz) = i c³℘′_Λ(z). Both oriented bases have ω₂ = iω₁, on whose coordinates multiplication by i is `rot` (row "Winding-class pullback and the rotation of T²") | `exists_normalized` depends only on Im τ > 0 (lattice and ℘ are basis-free, `weierstrassP_congr`); `swap` permutes Mathlib's `latticeBasis` and `latticeEquivProd`. Load-bearing for C3 `elliptic-curve-uniformization` (Φ on (c, ic) with c > 0 real, μ = c⁻¹; g₂ = 4 needs Mathlib's 60G₄) and C1 `weierstrass-lattice-i` (℘(iz) = −℘(z) from i⁻² = −1, ℘′(iz) = i℘′(z) from i⁻³ = i; weight +3 would give [−i]) | checked at the pin: `not_weierstrassP_smul_two_sq` separates μ⁻² from μ² (℘ ≢ 0 by `exists_weierstrassP_ne_zero`), `derivWeierstrassP_gaussianPair_I_mul` separates μ⁻³ from μ³ given ℘′ ≢ 0 (standard, not formalized), `not_forall_mem_smul_two_iff_two_mul_mem` the transport direction (red team 2026-11-28) |
```

**R5. `docs/gaps.md`, "General lemmas kept local".** Add a category before `### Port-specific`:

```
### Complex analysis and elliptic functions

Diff at a bump: Mathlib `Analysis/SpecialFunctions/Elliptic/`, `Analysis/Complex/`, `NumberTheory/ModularForms/EisensteinSeries/`.

| Local declaration | Module | Layer | Why local | Opened |
|---|---|---|---|---|
| `HodgeLadder.Period.swap`, `smul`, `swap_lattice`, `mem_smul_lattice`, `smulLatticeEquiv`, `weierstrassP_congr`, `derivWeierstrassP_congr`, `weierstrassP_smul`, `derivWeierstrassP_smul`, `G_smul`, `g₂_smul`, `g₃_smul`, `ω₁_ne_zero`, `ω₂_ne_zero`, `im_div_ne_zero`, `oriented`, `oriented_swap`, `normalizeScale`, `normalize` and their lemmas (basis swap and scaling of Mathlib's `PeriodPair`, the oriented basis with Im(ω₂/ω₁) > 0, the normalized pair (1, τ), homogeneity of ℘, ℘′, G_n, g₂, g₃, `exists_weierstrassP_ne_zero`) | `HodgeLadder.Period.Pair.Normalize` | 0 | Mathlib at the pin has `PeriodPair` and ℘ with no basis change, no scaling and no homogeneity lemma (`PeriodPair` occurs only in `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`); they belong next to `PeriodPair.weierstrassP`; at a bump check that file for a `PeriodPair.smul`, a homogeneity lemma for `weierstrassP` or `G`, or a lattice-only `weierstrassP`; rung `period-pair-normalize` | 2026-11-28 |
```

**R6. Handoff.** In `docs/handoffs/2026-11-28-period-pair-normalize.md`, replace `- Red team: pending.` with `- Red team: pass with changes (docs/sketches/period-pair-normalize.redteam.md): exponent and transport-direction tests at μ = 2, ℘′(iz) = i℘′(z), the bases (c, ±ic) normalized; conventions and gaps rows.`

## Optional

- O1. `tools/pinwalk.py` `PHRASES`: add `"Complex analysis and elliptic functions": [r"PeriodPair\.\w*(smul|swap|orient|normaliz)", r"weierstrassP\w*(smul|homog)", r"PeriodPair\.G\w*smul"]`, so the new category gets clash candidates at a bump.
- O2. `docs/sketches/weierstrass-two-to-one.md`, bullet "Lattice basis (c, ic) versus (c, −ic)": append `Done in period-pair-normalize: (c, −ic) is swapped to (−ic, c) with μ = i c⁻¹; see its red team, finding 7.`

## What was tried

- P1 `∃ z, ℘ z ≠ 0` from `not_continuousAt_weierstrassP`: compiles. P2, P2′ at μ = 2: compile. P3 reversed transport refuted: compiles. P4a, P4b, P4c, P6 orientation: compile (first P4b attempt with `div_neg` failed on the goal `-1 = I ^ 2`; closed by `Complex.I_sq`). P5 g₃(ℤ[i]) = 0: compiles (`Complex.I_pow_six` absent at the pin; `pow_mul` twice). P7 ℘′(iz) = i℘′(z): compiles via `linear_combination`.
- A vacuity proof of `exists_normalized` in under ten lines without homogeneity: failed, as expected (finding 4).
- A cheap proof of g₂(ℤ[i]) ≠ 0 or G₄(ℤ[i]) ≠ 0: abandoned; it is the open content of `weierstrass-lattice-i`.
- A cheap proof of ℘′ ≢ 0: abandoned (needs the pole order of ℘′ or an argument through `derivWeierstrassP_sq`).
