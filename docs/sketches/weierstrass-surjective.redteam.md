# Red team: `weierstrass-surjective` (foundation, issue #284, sub-rung 1 of `weierstrass-two-to-one`)

Date: 2026-11-28. Worktree `weierstrass-surjective`, branch `track/weierstrass-surjective`, candidate commit `93e194d` on base `d670df6`. File: `HodgeLadder/Weierstrass/Surjective.lean` (81 lines, one theorem), imported from the root, ledger entry `checked`. Pins: Lean `v4.35.0-rc4`, Mathlib `1f41440`, upstream `Paul-Lez/HodgeConjecture@2ead713`, the same at base and candidate (the candidate touches no pin file).

**Verdict: pass with changes.**

The theorem is the classical surjectivity of ℘ onto ℂ, stated off the lattice so that Mathlib's junk value ℘ = 0 on Λ cannot discharge it. The proof is the Liouville argument of Mathlib's own `derivWeierstrassP_sq`, uses standard axioms only and has no sign or normalization to get wrong. The changes are about records and placement: the module moves to `General/` (Mathlib only, layer 0), the gaps row moves to the head of its table and its category's bump line gains the Mathlib files the proof uses, the conventions register gains a row for Mathlib's ℘, and the ledger and handoff follow the move.

Read: `python3 tools/next.py weierstrass-surjective`; the ledger entries `weierstrass-surjective`, `weierstrass-two-to-one`, `elliptic-curve-uniformization`, `weil-eigen-algebra`; `docs/sketches/weierstrass-two-to-one.md` (step 1, sub-rung table, sign risks); `docs/sketches/weil-eigen-algebra.redteam.md` item 9 and `docs/sketches/elliptic-curve-points.redteam.md` items 6 and 10 (placement precedent, the ℘ normalization for C3); `docs/references.md`; `docs/conventions.md`; `docs/gaps.md` header and "Manifolds, charts and analytic functions"; Mathlib `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (all 1081 lines surveyed, definitions at lines 60, 79, 268, 519, 945 to 960 read), `Analysis/Meromorphic/Order.lean`, `Analysis/Complex/Liouville.lean`, `Algebra/Module/ZLattice/Basic.lean`. No sketch `docs/sketches/weierstrass-surjective.md` exists; the statement is sub-rung 1 of the parent sketch, unchanged.

Scratch (directory `rt-scratch-wsurj-redteam/` in the worktree, deleted afterwards): one file `Probe.lean` importing the candidate module and `Mathlib.LinearAlgebra.Complex.Module`, checked by `lake env lean` in about 5 s.

| Probe | What it tried | Result |
|---|---|---|
| A | the square period pair `sqPair := ⟨1, I, _⟩` from `Complex.basisOneI.linearIndependent` and `coe_basisOneI`; `∃ L : PeriodPair, L.ω₁ = 1 ∧ L.ω₂ = I` | checks |
| B | without `z ∉ Λ`: `∃ z, ℘ z = 0` by `⟨0, weierstrassP_zero⟩`; `℘ l = 0` for `l ∈ Λ` by `weierstrassP_coe` | checks: the dropped clause would make c = 0 trivial |
| C | `simp`, `aesop` and `⟨ω₁ / 2, ω₁_div_two_notMem_lattice, rfl⟩` on the statement, each under `fail_if_success` | all three fail; the theorem closes it |
| D | `(L.lattice : Set ℂ)ᶜ.Nonempty` from `ω₁_div_two_notMem_lattice` | checks for every `L` |
| E | consequence: `∃ z w, z ∉ Λ ∧ w ∉ Λ ∧ ℘ z ≠ ℘ w` from the theorem at c = 0 and c = 1 | checks |
| F | consequence: `∃ z ≠ 0, ℘ z = 0`, a zero of ℘ other than the junk zero at 0 | checks |
| G | `Set.SurjOn L.weierstrassP (L.lattice : Set ℂ)ᶜ Set.univ` in one line from the theorem | checks |
| H | the theorem at `sqPair` and c = 10 ^ 100 | checks |
| axioms | `#print axioms HodgeLadder.weierstrassP_surjOn` | `[propext, Classical.choice, Quot.sound]` |

`lake build HodgeLadder.Weierstrass.Surjective`: up to date, success. `python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`, with `ACCEPTED (axioms: HodgeLadder.weierstrassP_surjOn [Classical.choice, Quot.sound, propext])`. `python3 tools/pinwalk.py`: layer 0, no downstream module; `python3 tools/pinwalk.py --clash .lake/packages/mathlib/Mathlib`: no candidate for `weierstrassP_surjOn`.

## Findings

1. **Statement against the literature.** `Silverman2009` ch. VI §3 defines ℘(z; Λ) = 1/z² + Σ over ω ∈ Λ, ω ≠ 0 of (1/(z − ω)² − 1/ω²) for a lattice Λ ⊂ ℂ, and ch. VI §2 shows that a nonconstant elliptic function takes every value of ℂ (locators unverified; the parent sketch cites the same chapter).

   | Literature | Lean | Match |
   |---|---|---|
   | lattice Λ = ℤω₁ + ℤω₂, ω₁, ω₂ ℝ-linearly independent | `PeriodPair` with field `indep : LinearIndependent ℝ ![ω₁, ω₂]`; `PeriodPair.lattice = Submodule.span ℤ {L.ω₁, L.ω₂}` (Weierstrass.lean lines 60 to 79) | yes; every lattice of ℂ has this form, and the instance `IsZLattice ℝ L.lattice` holds |
   | ℘(z) = 1/z² + Σ_{ω ≠ 0} (1/(z − ω)² − 1/ω²) | `weierstrassP z = ∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / l ^ 2)` (line 268) | yes: the term l = 0 reads 1/z² − 1/0 = 1/z² because 1/0 = 0 in Lean |
   | ℘ has double poles at Λ | `order_weierstrassP : meromorphicOrderAt ℘ l₀ = -2` for `l₀ ∈ Λ` | yes |
   | value at a pole | none (℘ is undefined there) | Lean's junk `℘ l = 0` (`weierstrassP_coe`); the statement excludes Λ, so the junk value cannot supply a witness |
   | ℘ : ℂ ∖ Λ → ℂ is onto | `∃ z ∉ L.lattice, L.weierstrassP z = c` for every `c : ℂ` | yes |

   The statement is the classical one, for every period pair, with no extra hypothesis.

2. **Hypotheses satisfiable.** The theorem takes a `PeriodPair` and a complex number. Probe A builds `sqPair` = (1, i) from Mathlib's `Complex.basisOneI`, and probe H applies the theorem there. The complement of Λ is inhabited for every `L` (probe D, ω₁/2), so `z ∉ Λ` is a real constraint and the lattice is a proper subset of ℂ.

3. **No triviality.** Nothing unfolds to `True`; no `ℕ∞`, coercion or empty index type enters. The clause `z ∉ L.lattice` carries the weight: without it c = 0 holds at z = 0 by `weierstrassP_zero` (probe B). With it, `simp`, `aesop` and the half-period witness all fail (probe C). The only hypothesis of the proof by contradiction (`hne : ∀ z ∉ Λ, ℘ z ≠ c`) is used twice: for analyticity of (℘ − c)⁻¹ off Λ and for the final contradiction at ω₁/2. Not an interface rung, so item 4 of the template does not apply.

4. **Proof soundness.** Read line by line.
   - At l ∈ Λ, g equals (℘ − c)⁻¹ on a punctured neighbourhood: `compl_lattice_sdiff_singleton_mem_nhds` keeps the other lattice points away, and `self_mem_nhdsWithin` removes l itself.
   - The order of ℘ − c at l is −2: `meromorphicOrderAt_add_eq_left_of_lt` against the constant −c, whose order is 0 (c ≠ 0) or ⊤ (c = 0), both above −2 (the `split_ifs <;> decide` covers both cases). Then `fun_meromorphicOrderAt_inv` (generated by `@[to_fun]` on `meromorphicOrderAt_inv`) gives order 2, and `AnalyticAt.of_meromorphicOrderAt_pos` with g l = 0 gives analyticity at l.
   - Off Λ, `analyticOnNhd_weierstrassP` and ℘ x − c ≠ 0 give analyticity of the inverse; g agrees with it on the open complement of Λ (`isClosed_lattice`).
   - Periodicity: `weierstrassP_add_coe` and `add_mem_cancel_right` (membership in Λ is translation invariant, so the `if` branch is preserved).
   - Bounded by `IsZLattice.isCompact_range_of_periodic`, constant by `Differentiable.apply_eq_apply_of_bounded`, so g(ω₁/2) = g 0 = 0, against (℘(ω₁/2) − c)⁻¹ ≠ 0.

   This is the structure of Mathlib's `relation_eq_zero` (`analyticAt_relation` and `relation_eq_zero`, Weierstrass.lean lines 1051 to 1072). The kernel accepts it with the three standard axioms.

5. **Mathlib duplicates at the pin.** `PeriodPair` and `weierstrassP` occur in one Mathlib file only (`grep -rl` over `Mathlib/`), and upstream does not mention them. That file has no `SurjOn`, `range`, `Surjective` or value-distribution lemma for ℘ (`grep`); its `range` hits are `Set.range L.basis` and `Finset.sum_range_succ`. The clash scan finds nothing. A local copy is justified (decision 0011).

6. **Drift risk.** Mathlib's Weierstrass file is recent (last change at the pin: `9194f40`, 2026-10-05) and has a TODO to connect `G` with `ModularForm`. The proof depends on these names: `PeriodPair.lattice`, `weierstrassP`, `weierstrassP_add_coe`, `order_weierstrassP`, `analyticOnNhd_weierstrassP`, `compl_lattice_sdiff_singleton_mem_nhds`, `isClosed_lattice`, `ω₁_div_two_notMem_lattice` (Weierstrass.lean); `meromorphicOrderAt_congr`, `fun_meromorphicOrderAt_inv`, `meromorphicOrderAt_add_eq_left_of_lt`, `meromorphicOrderAt_const`, `AnalyticAt.of_meromorphicOrderAt_pos` (`Analysis/Meromorphic/Order.lean`); `Differentiable.apply_eq_apply_of_bounded` (`Analysis/Complex/Liouville.lean`); `IsZLattice.isCompact_range_of_periodic` (`Algebra/Module/ZLattice/Basic.lean`). A rename breaks the build, which is harmless. Two changes could alter the truth of the statement: a change of the junk value of ℘ on Λ (the statement stays true, though a nonzero junk value would make the `z ∉ Λ` clause carry less weight), and a change of `PeriodPair` (for example dropping `indep`, which would allow ω₂ = 0 and degenerate lattices where Λ is not discrete). The gaps category line names none of these files today (change 2).

7. **Placement.** The module imports only Mathlib (`pinwalk.py` layer 0) and names no ladder object. The directory `Weierstrass/` comes from `next.py`'s fallback for an id with no `module`. The #212 layout keeps Mathlib-only general lemmas under `HodgeLadder/General/` with a gaps row (precedent: `weil-eigen-algebra` red team item 9, which moved `Weil/Eigen/` to `General/EigenProducts.lean`). The namespace `HodgeLadder` and the declaration name stay, so the ledger's `declarations` list is unchanged. The later Mathlib-only sub-rungs of `weierstrass-two-to-one` (`rect-winding`, `rect-periodic`, `rect-argument-principle`, `lattice-fundamental-rectangle`, `period-pair-normalize`, `weierstrass-order-sum`) should follow the same layout. Change 1.

8. **Gaps row.** The row exists, in "Manifolds, charts and analytic functions", with Layer 0 and the right reason. It sits last, after rows of layer 1, 1 and 10, against the header rule that rows within a category run by layer. The category's bump line names Mathlib `Geometry/Manifold/` and `Analysis/Analytic/` only. Change 2.

9. **Conventions (item 6 of the template).** Conventions used: the definition of ℘ as the `tsum` above with 1/0 = 0 for the l = 0 term; the junk value ℘ = 0 on Λ; the lattice as the ℤ-span of an ℝ-independent pair. No sign, orientation or scalar enters. The truth of this rung is insensitive to them: the statement is about the range of ℘ off Λ, unchanged under ℘ ↦ a℘ + b with a ≠ 0, and unchanged by the basis choice (only the set Λ enters). The register has no row for Mathlib's ℘; the next rungs need one (`weierstrass-two-to-one` compares values of ℘, C3 needs g₂ = 4, g₃ = 0 against Mathlib's g₂ = 60 G₄, g₃ = 140 G₆, already flagged in row "Plane cubic E and its charts"). No cited result is assumed. Change 3 adds the row.

10. **Equality first (item 7).** Not an identity between classes and not an inclusion: an existence statement. It is a step toward the bijection ℂ/Λ → E(ℂ) of `elliptic-curve-uniformization` (open), through `weierstrass-two-to-one` (open). It supplies the surjectivity half of Φ z = [℘ z : ℘′ z / 2 : 1], with the sign of y fixed by the choice ±z.

11. **Non-vacuity (item 7b).** The smallest test that would fail if the theorem only returned the junk point is probe F, `∃ z ≠ 0, L.weierstrassP z = 0`; probe E (℘ nonconstant off Λ) is the next. Neither exists in Mathlib or the ladder; Mathlib's nearest fact is `not_continuousAt_weierstrassP` (poles at Λ). The statement already carries `z ∉ Λ`, so it is its own non-junk form and both probes follow in three lines; no test is required for this rung. The parent sketch's `weierstrassP_half_ne` (sub-rung 8) is the planned test for the two-to-one direction.

12. **Pin drift (item 8).** Checked at the current pin; base and candidate share every pin file. No drift to diff.

13. **Name.** `weierstrassP_surjOn` states the `∃` form; Mathlib's `Set.SurjOn` form is one line from it (probe G). If Mathlib later adds `PeriodPair.weierstrassP_surjOn`, a file that opens both `PeriodPair` and `HodgeLadder` gets an ambiguous name; the bump line of change 2 covers the check. Recorded only.

## Required changes

1. **Move the module.** Rename `HodgeLadder/Weierstrass/Surjective.lean` to `HodgeLadder/General/WeierstrassSurjective.lean` (contents unchanged; remove the empty `Weierstrass/` directory). In `HodgeLadder.lean` replace `public import HodgeLadder.Weierstrass.Surjective` by `public import HodgeLadder.General.WeierstrassSurjective`. In `ledger/ladder.json`, entry `weierstrass-surjective`, set `"module": "HodgeLadder.General.WeierstrassSurjective"`. In `docs/handoffs/2026-11-28-weierstrass-surjective.md` replace `HodgeLadder/Weierstrass/Surjective.lean` by `HodgeLadder/General/WeierstrassSurjective.lean`.

2. **Gaps.** In `docs/gaps.md`, section "Manifolds, charts and analytic functions":
   - replace the bump line by
     `Diff at a bump: Mathlib `Geometry/Manifold/`, `Analysis/Analytic/`, `Analysis/Meromorphic/Order.lean`, `Analysis/Complex/Liouville.lean`, `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (`PeriodPair` and its field `indep`, `lattice`, `weierstrassP`, the junk value `weierstrassP_coe`, `order_weierstrassP`, and any new value or surjectivity lemma for ℘), `Algebra/Module/ZLattice/Basic.lean` (`IsZLattice.isCompact_range_of_periodic`); upstream `HodgeConjecture/{Definitions,Lemmas}/AlgebraicGeometry/ComplexPoint/`, `Other/Geometry/Manifold/`.`
   - move the `HodgeLadder.weierstrassP_surjOn` row to the first row of the table (layer 0 before layer 1), with Module column `` `HodgeLadder.General.WeierstrassSurjective` ``; the other columns stay.

3. **Conventions.** Add this row to the register in `docs/conventions.md`, after row "Plane cubic E and its charts":

   `| Weierstrass ℘ of a period pair | Mathlib `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`: `PeriodPair` (ω₁, ω₂ with `indep : LinearIndependent ℝ ![ω₁, ω₂]`), `PeriodPair.lattice = Submodule.span ℤ {ω₁, ω₂}`, `weierstrassP`, `derivWeierstrassP`, `G`, `g₂`, `g₃`; used by `HodgeLadder.weierstrassP_surjOn` (`HodgeLadder/General/WeierstrassSurjective.lean`, rung `weierstrass-surjective`) | ℘ z = Σ' over l ∈ Λ of (1/(z − l)² − 1/l²), the term l = 0 reading 1/z² because 1/0 = 0, which is `Silverman2009`'s 1/z² + Σ over l ≠ 0 of (1/(z − l)² − 1/l²); junk values ℘ = 0 and ℘′ = 0 on Λ (`weierstrassP_coe`, `derivWeierstrassP_coe`); ℘′ z = −Σ' 2/(z − l)³; G n = Σ' l⁻ⁿ (the term l = 0 is 0), g₂ = 60 G₄, g₃ = 140 G₆; ℘′² = 4℘³ − g₂℘ − g₃ off Λ (`derivWeierstrassP_sq`) | none for `weierstrass-surjective` (a statement about the range of ℘ off Λ, unchanged under ℘ ↦ a℘ + b with a ≠ 0 and under a change of basis of Λ); the junk value is why every statement excludes Λ (without z ∉ Λ, c = 0 is hit at z = 0). Load-bearing for `weierstrass-two-to-one` (equalities of values of ℘ off Λ) and for C3 `elliptic-curve-uniformization` through g₂ = 4, g₃ = 0 (row "Plane cubic E and its charts") | read from source at the pin; the clause z ∉ Λ shown necessary and the theorem applied at the period pair (1, i), in scratch (red team 2026-11-28, `weierstrass-surjective`) |`

4. **Ledger note.** In `ledger/ladder.json`, entry `weierstrass-surjective`, append to `note`: ` Red team: pass with changes (docs/sketches/weierstrass-surjective.redteam.md).`

No change to the statement, the proof, the docstrings or `docs/roadmap.md` (its row names no module).
