module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.Liouville

/-!
# The Weierstrass function takes every value off the lattice

For a period pair `L` with lattice `Λ` and every `c : ℂ`, Mathlib's `℘ = L.weierstrassP`
takes the value `c` at a point off `Λ`. The proof is Liouville's theorem: if `℘ z ≠ c` for all
`z ∉ Λ`, the function equal to `(℘ − c)⁻¹` off `Λ` and to `0` on `Λ` is entire (at a lattice
point `℘ − c` has order `−2` by `PeriodPair.order_weierstrassP`, so the inverse has order `2`
and value `0`), `Λ`-periodic, hence bounded by `IsZLattice.isCompact_range_of_periodic`, hence
constant, equal to its value `0` at the origin; at the half period `ω₁ / 2` it is nonzero.
This follows the pattern of Mathlib's proof of `PeriodPair.derivWeierstrassP_sq`.

The condition `z ∉ Λ` carries weight: Mathlib's `℘` has the junk value `0` on `Λ`
(`PeriodPair.weierstrassP_coe`), so for `c = 0` the statement without it holds at `z = 0`.
No sign or normalization enters.

## Main results

* `HodgeLadder.weierstrassP_surjOn`: `∃ z ∉ L.lattice, L.weierstrassP z = c`.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace HodgeLadder

/-- Every complex number `c` is a value of the Weierstrass function `℘` of `L` at a point off
the lattice: `∃ z ∉ Λ, ℘ z = c`. Sub-rung 1 of `weierstrass-two-to-one`. -/
theorem weierstrassP_surjOn (L : PeriodPair) (c : ℂ) :
    ∃ z ∉ L.lattice, L.weierstrassP z = c := by
  classical
  by_contra hne
  push Not at hne
  set g : ℂ → ℂ := fun z => if z ∈ L.lattice then 0 else (L.weierstrassP z - c)⁻¹ with hg
  have hana : ∀ x, AnalyticAt ℂ g x := by
    intro x
    by_cases hx : x ∈ L.lattice
    · have heq : g =ᶠ[𝓝[≠] x] fun z => (L.weierstrassP z - c)⁻¹ := by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
          (L.compl_lattice_sdiff_singleton_mem_nhds x)] with w hw hw'
        have : w ∉ L.lattice := by simp_all
        simp [hg, this]
      refine AnalyticAt.of_meromorphicOrderAt_pos ?_ (by simp [hg, hx])
      rw [meromorphicOrderAt_congr heq, fun_meromorphicOrderAt_inv]
      have hsub : meromorphicOrderAt (fun z => L.weierstrassP z - c) x = -2 := by
        have h1 : (fun z => L.weierstrassP z - c) = L.weierstrassP + fun _ => -c := by
          funext z; simp [sub_eq_add_neg]
        rw [h1, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const _ _),
          L.order_weierstrassP x hx]
        rw [L.order_weierstrassP x hx, meromorphicOrderAt_const]
        split_ifs <;> decide
      rw [hsub]
      decide
    · have h1 : AnalyticAt ℂ (fun z => (L.weierstrassP z - c)⁻¹) x := by
        have := L.analyticOnNhd_weierstrassP x hx
        have hc : L.weierstrassP x - c ≠ 0 := sub_ne_zero.mpr (hne x hx)
        fun_prop (disch := exact hc)
      apply h1.congr
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hx] with w hw
      simp_all
  have hdiff : Differentiable ℂ g := fun x => (hana x).differentiableAt
  have hper : ∀ z, ∀ w ∈ L.lattice, g (z + w) = g z := by
    intro z w hw
    lift w to L.lattice using hw
    have hmem : z + w ∈ L.lattice ↔ z ∈ L.lattice :=
      L.lattice.toAddSubgroup.add_mem_cancel_right w.2
    simp only [hg, hmem, L.weierstrassP_add_coe]
  have hbdd := (IsZLattice.isCompact_range_of_periodic L.lattice _ hdiff.continuous hper).isBounded
  have hz := L.ω₁_div_two_notMem_lattice
  have h0 := hdiff.apply_eq_apply_of_bounded hbdd (L.ω₁ / 2) 0
  have hc : L.weierstrassP (L.ω₁ / 2) - c ≠ 0 := sub_ne_zero.mpr (hne _ hz)
  simp [hg, hz, L.lattice.zero_mem] at h0
  exact hc h0

end HodgeLadder
