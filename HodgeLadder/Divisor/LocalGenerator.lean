module

public import HodgeLadder.Divisor.IdealSheaf
public import HodgeLadder.Algebra.HeightOneGenerator
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# A local equation of a prime divisor near a point with factorial local ring

Let `S` be an integral locally Noetherian scheme, `ξ` a point of coheight one, `Z` its closure,
and `q ∈ Z` a point whose local ring is a UFD. Then on a neighbourhood `U` of `q` there is a
nonzero section `π` vanishing on `Z` that divides the vanishing ideal of `Z` at every point of
`U`. With `HodgeLadder.generates_of_dividesVanishingAt` it generates the vanishing ideal sheaf
on `U`. Part of rung `prime-divisor-ideal-sheaf`.

On an affine open `U₀ ∋ q` with `A = Γ(S, U₀)`, the prime `𝔭` of `ξ` has height one (the local
ring at `ξ` is `A_𝔭`, of dimension `coheight ξ`), so `HodgeLadder.exists_generator_of_height_eq_one`
gives `π ∈ 𝔭` and `T ∉ 𝔮` with `T 𝔭 ⊆ π A`; take `U = D(T)`.

## Main results

* `HodgeLadder.exists_local_generator`
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing Order

universe u

namespace HodgeLadder

variable {S : Scheme.{u}}

/-- On an affine open, membership in the prime of a point is non-invertibility of the germ. -/
lemma mem_primeIdealOf_iff {U : S.Opens} (hU : IsAffineOpen U) (x : S) (hx : x ∈ U)
    (b : Γ(S, U)) :
    b ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔
      S.presheaf.germ U x hx b ∈ maximalIdeal (S.presheaf.stalk x) := by
  let := S.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (S.presheaf.stalk x) _ b).symm

/-- A unit germ at a specialization is a unit germ at the generic point. -/
lemma isUnit_germ_of_specializes {U : S.Opens} {ξ x : S} (h : ξ ⤳ x) (hx : x ∈ U)
    (b : Γ(S, U)) (hb : IsUnit (S.presheaf.germ U x hx b)) :
    IsUnit (S.presheaf.germ U ξ (h.mem_open U.isOpen hx) b) :=
  (S.mem_basicOpen b ξ _).1 (h.mem_open (S.basicOpen b).isOpen ((S.mem_basicOpen b x hx).2 hb))

variable [IsIntegral S] [IsLocallyNoetherian S]

/-- **A local equation of a prime divisor.** -/
theorem exists_local_generator (ξ q : S) (hξ : coheight ξ = 1) (hq : ξ ⤳ q)
    [UniqueFactorizationMonoid (S.presheaf.stalk q)] :
    ∃ (U : S.Opens) (_ : q ∈ U) (π : Γ(S, U)),
      π ∈ vanishingIdealSections (closure {ξ}) U ∧ π ≠ 0 ∧
        ∀ x (hx : x ∈ U), DividesVanishingAt (Z := closure {ξ}) π x hx := by
  obtain ⟨U₀, hU₀, hqU₀, -⟩ := exists_isAffineOpen_mem_and_subset (show q ∈ (⊤ : S.Opens) from trivial)
  have hξU₀ : ξ ∈ U₀ := hq.mem_open U₀.isOpen hqU₀
  have : IsNoetherianRing Γ(S, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  have : Nonempty U₀ := ⟨⟨q, hqU₀⟩⟩
  set 𝔭 := (hU₀.primeIdealOf ⟨ξ, hξU₀⟩).asIdeal with h𝔭
  set 𝔮 := (hU₀.primeIdealOf ⟨q, hqU₀⟩).asIdeal with h𝔮
  have hvan : ∀ b ∈ 𝔭, ∀ x (hx : x ∈ U₀), ξ ⤳ x →
      S.presheaf.germ U₀ x hx b ∈ maximalIdeal (S.presheaf.stalk x) := by
    intro b hb x hx hξx
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (mem_primeIdealOf_iff hU₀ ξ hξU₀ b).1 hb
    rw [mem_maximalIdeal, mem_nonunits_iff] at this
    exact this (isUnit_germ_of_specializes hξx hx b hu)
  have h𝔭𝔮 : 𝔭 ≤ 𝔮 := fun b hb => (mem_primeIdealOf_iff hU₀ q hqU₀ b).2 (hvan b hb q hqU₀ hq)
  have h1 : 𝔭.height = 1 := by
    let := S.presheaf.algebra_section_stalk (⟨ξ, hξU₀⟩ : U₀)
    have := hU₀.isLocalization_stalk ⟨ξ, hξU₀⟩
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 (S.presheaf.stalk ξ)
    rw [ringKrullDim_stalk_eq_coheight, hξ] at h
    exact_mod_cast h.symm
  let := S.presheaf.algebra_section_stalk (⟨q, hqU₀⟩ : U₀)
  have := hU₀.isLocalization_stalk ⟨q, hqU₀⟩
  obtain ⟨π, hπ𝔭, T, hT𝔮, hTπ⟩ :=
    exists_generator_of_height_eq_one 𝔭 𝔮 h𝔭𝔮 h1 (S.presheaf.stalk q)
  have hT0 : T ≠ 0 := fun h => hT𝔮 (h ▸ 𝔮.zero_mem)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    apply Ideal.ne_bot_of_height_eq_one h1
    rw [Submodule.eq_bot_iff]
    intro b hb
    obtain ⟨e, he⟩ := hTπ b hb
    rw [mul_zero] at he
    exact (mul_eq_zero.1 he).resolve_left hT0
  have hqT : q ∈ S.basicOpen T := by
    refine (S.mem_basicOpen T q hqU₀).2 ?_
    have := (mem_primeIdealOf_iff hU₀ q hqU₀ T).not.1 hT𝔮
    rwa [mem_maximalIdeal, mem_nonunits_iff, not_not] at this
  have hUU₀ : S.basicOpen T ≤ U₀ := S.basicOpen_le T
  -- germs at a point `x` of the stalk-specialization map
  have hsp : ∀ {W : S.Opens} {x : S} (hxW : x ∈ W) (h : ξ ⤳ x) (a : Γ(S, W)),
      S.presheaf.stalkSpecializes h (S.presheaf.germ W x hxW a) =
        S.presheaf.germ W ξ (h.mem_open W.isOpen hxW) a := fun hxW h a => by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  refine ⟨S.basicOpen T, hqT, S.presheaf.map (homOfLE hUU₀).op π, ?_, ?_, ?_⟩
  · intro x hx hz
    rw [S.presheaf.germ_res_apply]
    exact hvan π hπ𝔭 x _ (specializes_iff_mem_closure.2 hz)
  · intro h
    have : Nonempty (S.basicOpen T) := ⟨⟨q, hqT⟩⟩
    exact hπ0 (map_injective_of_isIntegral S (homOfLE hUU₀) (by rw [h, map_zero]))
  · intro x hx V hVU s hxV hs
    have hxU₀ : x ∈ U₀ := hUU₀ hx
    rw [S.presheaf.germ_res_apply]
    have hTu : IsUnit (S.presheaf.germ U₀ x hxU₀ T) := (S.mem_basicOpen T x hxU₀).1 hx
    by_cases hξx : ξ ⤳ x
    · let := S.presheaf.algebra_section_stalk (⟨x, hxU₀⟩ : U₀)
      have := hU₀.isLocalization_stalk ⟨x, hxU₀⟩
      obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.mk'_surjective
        (hU₀.primeIdealOf ⟨x, hxU₀⟩).asIdeal.primeCompl (S.presheaf.germ V x hxV s)
      dsimp only at hbt
      have hspec : S.presheaf.germ V x hxV s * S.presheaf.germ U₀ x hxU₀ t =
          S.presheaf.germ U₀ x hxU₀ b := by
        have h := IsLocalization.mk'_spec (S.presheaf.stalk x) b t
        rw [hbt] at h
        exact h
      have htu : IsUnit (S.presheaf.germ U₀ x hxU₀ t) :=
        IsLocalization.map_units (S.presheaf.stalk x) t
      have hb𝔭 : b ∈ 𝔭 := by
        rw [mem_primeIdealOf_iff hU₀ ξ hξU₀]
        have hs' := hs ξ (hξx.mem_open V.isOpen hxV) (subset_closure rfl)
        have h' := congrArg (S.presheaf.stalkSpecializes hξx) hspec
        rw [map_mul, hsp, hsp, hsp] at h'
        rw [← h']
        exact Ideal.mul_mem_right _ _ hs'
      obtain ⟨e, he⟩ := hTπ b hb𝔭
      have he' := congrArg (S.presheaf.germ U₀ x hxU₀) he
      rw [map_mul, map_mul] at he'
      refine ⟨↑((hTu.mul htu).unit⁻¹) * S.presheaf.germ U₀ x hxU₀ e, ?_⟩
      rw [mul_assoc, Units.eq_inv_mul_iff_mul_eq, IsUnit.unit_spec, ← he', ← hspec]
      ring
    · -- away from `Z`, the germ of `π` is a unit
      have hxN : x ∈ (closure ({ξ} : Set S))ᶜ := fun h => hξx (specializes_iff_mem_closure.2 h)
      let N : S.Opens := ⟨(closure ({ξ} : Set S))ᶜ, isClosed_closure.isOpen_compl⟩
      obtain ⟨g, hgN, hxg⟩ := hU₀.exists_basicOpen_le (V := N) ⟨x, hxN⟩ hxU₀
      have hg𝔭 : g ∈ 𝔭 := by
        rw [mem_primeIdealOf_iff hU₀ ξ hξU₀, mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact hgN ((S.mem_basicOpen g ξ hξU₀).2 hu) (subset_closure rfl)
      obtain ⟨e, he⟩ := hTπ g hg𝔭
      have he' := congrArg (S.presheaf.germ U₀ x hxU₀) he
      rw [map_mul, map_mul] at he'
      have hgu : IsUnit (S.presheaf.germ U₀ x hxU₀ g) := (S.mem_basicOpen g x hxU₀).1 hxg
      have hπu : IsUnit (S.presheaf.germ U₀ x hxU₀ π) :=
        isUnit_of_mul_isUnit_right (he' ▸ hTu.mul hgu)
      refine ⟨S.presheaf.germ V x hxV s * ↑hπu.unit⁻¹, ?_⟩
      rw [mul_assoc]
      nth_rewrite 2 [← hπu.unit_spec]
      rw [Units.inv_mul, mul_one]

omit [IsIntegral S] [IsLocallyNoetherian S] in
/-- **Away from `Z` the generator is `1`.** On a nonempty open disjoint from `Z`, the section `1`
vanishes on `Z`, is nonzero, and divides the vanishing ideal at every point. -/
theorem one_generator_of_disjoint (Z : Set S) (U : S.Opens) [Nonempty U]
    (hUZ : Disjoint (U : Set S) Z) :
    (1 : Γ(S, U)) ∈ vanishingIdealSections Z U ∧ (1 : Γ(S, U)) ≠ 0 ∧
      ∀ x (hx : x ∈ U), DividesVanishingAt (Z := Z) (1 : Γ(S, U)) x hx := by
  refine ⟨fun x hx hz => absurd hz (Set.disjoint_left.1 hUZ hx), one_ne_zero, ?_⟩
  intro x hx V _ s hxV _
  exact ⟨S.presheaf.germ V x hxV s, by rw [map_one, mul_one]⟩

end HodgeLadder
