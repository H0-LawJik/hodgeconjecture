module

public import HodgeLadder.Divisor.LocalGenerator
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Length

/-!
# Orders of vanishing of a local equation of a prime divisor

Let `ξ` be a point of coheight one and `Z` its closure. A section `π` that vanishes on `Z` and
divides the vanishing ideal at every point of its open has order `1` at `ξ` and is a unit at the
codimension-one points other than `ξ`. These are the orders that make the Cartier data built from
such sections have divisor `-[Z]` (rung `prime-divisor-ideal-sheaf`).

## Main results

* `HodgeLadder.eq_of_specializes_of_coheight`
* `HodgeLadder.isUnit_germ_of_dividesVanishingAt`
* `HodgeLadder.maximalIdeal_eq_span_germ`
* `HodgeLadder.ord_germToFunctionField_eq_one`
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing Order

universe u

namespace HodgeLadder

variable {S : Scheme.{u}}

/-- A point of coheight one that specializes from another point of coheight one is that point. -/
lemma eq_of_specializes_of_coheight {ξ x : S} (hξ : coheight ξ = 1) (hx : coheight x = 1)
    (h : ξ ⤳ x) : x = ξ := by
  by_contra hne
  have hlt : x < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.2 h)
    (fun h' => hne (Specializes.antisymm (Scheme.le_iff_specializes.1 h') h).eq)
  have := Order.coheight_strictAnti hlt (by rw [hξ]; exact ENat.one_lt_top)
  rw [hξ, hx] at this
  exact lt_irrefl _ this

/-- Off a closed set `Z`, a section dividing the vanishing ideal of `Z` has invertible germ. -/
lemma isUnit_germ_of_dividesVanishingAt {Z : Set S} (hZ : IsClosed Z) {U : S.Opens}
    {π : Γ(S, U)} {x : S} (hx : x ∈ U) (hxZ : x ∉ Z)
    (h : DividesVanishingAt (Z := Z) π x hx) : IsUnit (S.presheaf.germ U x hx π) := by
  let V : S.Opens := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  obtain ⟨r, hr⟩ := h V inf_le_left 1 ⟨hx, hxZ⟩ (fun y hy hz => absurd hz hy.2)
  rw [map_one] at hr
  exact ⟨⟨_, r, by rw [mul_comm]; exact hr.symm, hr.symm⟩, rfl⟩

/-- At the generic point of `Z`, a dividing section generates the maximal ideal. -/
lemma maximalIdeal_eq_span_germ {ξ : S} {U : S.Opens} (hξU : ξ ∈ U) {π : Γ(S, U)}
    (hπ : π ∈ vanishingIdealSections (closure {ξ}) U)
    (h : DividesVanishingAt (Z := closure {ξ}) π ξ hξU) :
    maximalIdeal (S.presheaf.stalk ξ) = Ideal.span {S.presheaf.germ U ξ hξU π} := by
  apply le_antisymm
  · intro g hg
    obtain ⟨V, hξV, s, rfl⟩ := S.presheaf.exists_germ_eq g
    have hs : S.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s ∈
        vanishingIdealSections (closure {ξ}) (V ⊓ U) := by
      intro x hx hz
      rw [S.presheaf.germ_res_apply, mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_nonunits_iff.1 hg)
        (isUnit_germ_of_specializes (specializes_iff_mem_closure.2 hz) hx.1 s hu)
    have hξVU : ξ ∈ V ⊓ U := ⟨hξV, hξU⟩
    obtain ⟨r, hr⟩ := h (V ⊓ U) inf_le_right _ hξVU hs
    rw [S.presheaf.germ_res_apply (homOfLE (inf_le_left : V ⊓ U ≤ V)) ξ hξVU s] at hr
    rw [hr, Ideal.mem_span_singleton']
    exact ⟨r, rfl⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hπ ξ hξU (subset_closure rfl)

variable [IsIntegral S] [IsLocallyNoetherian S]

/-- **Order one at the generic point.** -/
theorem ord_germToFunctionField_eq_one {ξ : S} (hξ : coheight ξ = 1) {U : S.Opens} [Nonempty U]
    (hξU : ξ ∈ U) {π : Γ(S, U)} (hπ : π ∈ vanishingIdealSections (closure {ξ}) U)
    (h : DividesVanishingAt (Z := closure {ξ}) π ξ hξU) (hπ0 : π ≠ 0) :
    S.ord (S.germToFunctionField U π) ξ = 1 := by
  have hm := maximalIdeal_eq_span_germ hξU hπ h
  have : Ring.KrullDimLE 1 (S.presheaf.stalk ξ) := krullDimLE_of_coheight_le hξ.le
  have hne : S.germToFunctionField U π ≠ 0 :=
    (map_ne_zero_iff _ (Scheme.germToFunctionField_injective S U)).2 hπ0
  have hg0 : S.presheaf.germ U ξ hξU π ≠ 0 := fun h0 =>
    hπ0 (germ_injective_of_isIntegral S ξ hξU (by rw [h0, map_zero]))
  rw [Scheme.ord_eq_iff hξ hne]
  unfold Scheme.ordHom
  rw [← S.algebraMap_germ_eq_germToFunctionField hξU, Ring.ordFrac_eq_ord _ hg0]
  apply Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hg0)
  change Module.length _ (_ ⧸ Ideal.span {S.presheaf.germ U ξ hξU π}) = ((1 : ℕ) : ℕ∞)
  rw [← hm, Nat.cast_one]
  have : IsSimpleModule (S.presheaf.stalk ξ) (S.presheaf.stalk ξ ⧸ maximalIdeal (S.presheaf.stalk ξ)) :=
    isSimpleModule_iff_quot_maximal.2 ⟨_, maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩
  exact Module.length_eq_one _ _

end HodgeLadder
