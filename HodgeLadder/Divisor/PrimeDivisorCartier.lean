module

public import HodgeLadder.Divisor.Order
public import HodgeLadder.Divisor.Invertible
public import LefschetzPort.AlgebraicGeometry.CartierDataRepresents
public import LefschetzPort.AlgebraicGeometry.DivisorOfRationalSection

/-!
# The ideal sheaf of a prime divisor is invertible, with divisor `-D`

Let `S` be an integral locally Noetherian scheme whose space is Jacobson and whose local rings at
closed points are UFDs, and `ξ` a point of coheight one with closure `D`. Then the vanishing
ideal sheaf of `D` is invertible, and Cartier data with local equations `πᵢ⁻¹` (for local
generators `πᵢ`) represent it and have divisor `-D`. Rung `prime-divisor-ideal-sheaf`.

## Main results

* `HodgeLadder.exists_primeDivisor_cartierData`
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing Order Scheme.Modules

open scoped Classical

universe u

namespace HodgeLadder

variable {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]

/-- The order of an inverse. -/
lemma ord_inv {f : S.functionField} (hf : f ≠ 0) (x : S) : S.ord f⁻¹ x = -S.ord f x := by
  have h := Scheme.ord_mul (x := x) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf] at h
  have h1 : S.ord (1 : S.functionField) x = 0 := by
    have : Nonempty (⊤ : S.Opens) := ⟨⟨x, trivial⟩⟩
    have := Scheme.ord_of_isUnit (U := ⊤) (f := (1 : Γ(S, ⊤))) isUnit_one (x := x) trivial
    rwa [map_one] at this
  omega

omit [IsLocallyNoetherian S] in
/-- The function-field image of a restriction. -/
lemma germToFunctionField_res {U V : S.Opens} (h : V ≤ U) [Nonempty V] [Nonempty U]
    (f : Γ(S, U)) :
    S.germToFunctionField V (S.presheaf.map (homOfLE h).op f) = S.germToFunctionField U f :=
  S.presheaf.germ_res_apply (homOfLE h) _ _ f

/-- **The order of a local equation.** At a codimension-one point `x` of its open, a local
equation of the prime divisor `D = closure {ξ}` has order `1` if `x = ξ` and `0` otherwise. -/
lemma ord_local_equation {ξ : S} (hξ : coheight ξ = 1) {U : S.Opens} [Nonempty U]
    {π : Γ(S, U)} (hπ : π ∈ vanishingIdealSections (closure {ξ}) U) (hπ0 : π ≠ 0)
    (hdiv : ∀ x (hx : x ∈ U), DividesVanishingAt (Z := closure {ξ}) π x hx)
    {x : S} (hx : x ∈ U) (hx1 : coheight x = 1) :
    S.ord (S.germToFunctionField U π) x = if x = ξ then 1 else 0 := by
  split_ifs with hxξ
  · subst hxξ
    exact ord_germToFunctionField_eq_one hξ hx hπ (hdiv x hx) hπ0
  · have hxZ : x ∉ closure ({ξ} : Set S) := fun h =>
      hxξ (eq_of_specializes_of_coheight hξ hx1 (specializes_iff_mem_closure.2 h))
    have hu := isUnit_germ_of_dividesVanishingAt isClosed_closure hx hxZ (hdiv x hx)
    obtain ⟨W, iWU, hxW, hW⟩ :=
      RingedSpace.isUnit_res_of_isUnit_germ S.toRingedSpace U π x hx hu
    have : Nonempty W := ⟨⟨x, hxW⟩⟩
    rw [← germToFunctionField_res iWU.le π]
    exact Scheme.ord_of_isUnit hW hxW

/-- **The ideal sheaf of a prime divisor.** On an integral locally Noetherian scheme with Jacobson
underlying space and factorial local rings at closed points, the vanishing ideal sheaf of
`D = closure {ξ}` (`coheight ξ = 1`) is invertible and is represented by Cartier data whose
divisor is `-D`. -/
theorem exists_primeDivisor_cartierData [IsNoetherian S] [JacobsonSpace S] {ξ : S} (hξ : coheight ξ = 1)
    (hUFD : ∀ q ∈ closedPoints S, UniqueFactorizationMonoid (S.presheaf.stalk q)) :
    TauCeti.SheafOfModules.IsInvertible.{u} (vanishingIdealSheaf (closure ({ξ} : Set S))) ∧
      ∃ c : S.CartierData, c.Represents (vanishingIdealSheaf (closure ({ξ} : Set S))) ∧
        c.divisor = codimensionCycleSubgroup.single ξ hξ (-1) := by
  set Z := closure ({ξ} : Set S) with hZ
  have hdata : ∀ q : closedPoints S, ∃ (U : S.Opens) (_ : q.1 ∈ U) (π : Γ(S, U)),
      π ∈ vanishingIdealSections Z U ∧ π ≠ 0 ∧
        ∀ x (hx : x ∈ U), DividesVanishingAt (Z := Z) π x hx := by
    intro q
    by_cases hqZ : q.1 ∈ Z
    · have := hUFD q.1 q.2
      exact exists_local_generator ξ q.1 hξ (specializes_iff_mem_closure.2 hqZ)
    · let U : S.Opens := ⟨Zᶜ, isClosed_closure.isOpen_compl⟩
      have : Nonempty U := ⟨⟨q.1, hqZ⟩⟩
      obtain ⟨h1, h2, h3⟩ := one_generator_of_disjoint Z U disjoint_compl_left
      exact ⟨U, hqZ, 1, h1, h2, h3⟩
  choose U hqU π hπ hπ0 hdiv using hdata
  have hne : ∀ q, Nonempty (U q) := fun q => ⟨⟨q.1, hqU q⟩⟩
  have hgen : ∀ q, Generates (L := vanishingIdealSheaf Z)
      (show Γ(vanishingIdealSheaf Z, U q) from ⟨π q, hπ q⟩) := fun q =>
    generates_of_dividesVanishingAt (π q) (hπ q) (hπ0 q) (hdiv q)
  refine ⟨isInvertible_of_generates_closedPoints (vanishingIdealSheaf Z) U hqU _ hgen, ?_⟩
  have hcov : ∀ x : S, ∃ q : closedPoints S, x ∈ U q := by
    intro x
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := closure {x})
      ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    exact ⟨⟨y, hyc⟩, (specializes_iff_mem_closure.2 hy).mem_open (U _).isOpen (hqU _)⟩
  let fn : closedPoints S → S.functionField := fun q =>
    haveI := hne q; (S.germToFunctionField (U q) (π q))⁻¹
  have hfn0 : ∀ q, haveI := hne q; S.germToFunctionField (U q) (π q) ≠ 0 := fun q =>
    haveI := hne q; (map_ne_zero_iff _ (Scheme.germToFunctionField_injective S (U q))).2 (hπ0 q)
  have hord : ∀ q x, x ∈ U q → S.ord (fn q) x = if coheight x = 1 ∧ x = ξ then -1 else 0 := by
    intro q x hx
    have := hne q
    change S.ord (S.germToFunctionField (U q) (π q))⁻¹ x = _
    by_cases hx1 : coheight x = 1
    · rw [ord_inv (hfn0 q), ord_local_equation hξ (hπ q) (hπ0 q) (hdiv q) hx hx1]
      by_cases hxξ : x = ξ <;> simp [hxξ, hx1, hξ]
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx1]
      simp [hx1]
  let c : S.CartierData :=
    { ι := closedPoints S
      opens := U
      nonempty := hne
      covers := hcov
      fn := fn
      fn_ne_zero := fun q => inv_ne_zero (hfn0 q)
      ord_eq := fun i j x hi hj => by rw [hord i x hi, hord j x hj] }
  refine ⟨c, ⟨fun q => ⟨π q, hπ q⟩, hgen, ?_⟩, ?_⟩
  · intro i j u _ heq
    haveI := c.nonempty_inf i j
    haveI := hne i
    haveI := hne j
    have hval := congrArg Subtype.val heq
    change u * S.presheaf.map (homOfLE inf_le_left).op (π i) =
      S.presheaf.map (homOfLE inf_le_right).op (π j) at hval
    have hK := congrArg (S.germToFunctionField (U i ⊓ U j)) hval
    rw [map_mul, germToFunctionField_res, germToFunctionField_res] at hK
    change S.germToFunctionField (U i ⊓ U j) u * (S.germToFunctionField (U j) (π j))⁻¹ =
      (S.germToFunctionField (U i) (π i))⁻¹
    rw [← hK, mul_inv, ← mul_assoc, mul_inv_cancel₀, one_mul]
    intro h0
    rw [h0, zero_mul] at hK
    exact hfn0 j hK.symm
  · ext x
    change S.ord (fn (c.index x)) x = _
    rw [hord _ x (c.mem_opens_index x)]
    have hs := codimensionCycleSubgroup.single_apply ξ hξ (-1) x
    by_cases hxξ : x = ξ
    · subst hxξ
      rw [if_pos ⟨hξ, rfl⟩]
      exact (hs.trans (if_pos rfl)).symm
    · rw [if_neg (fun h => hxξ h.2)]
      exact (hs.trans (if_neg hxξ)).symm

end HodgeLadder
