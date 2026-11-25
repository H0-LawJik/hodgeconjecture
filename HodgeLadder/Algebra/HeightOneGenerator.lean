module

public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# A generator for a height-one prime, after inverting one element

Let `A` be a Noetherian domain, `𝔭 ⊆ 𝔮` primes with `ht 𝔭 = 1`, and suppose the localization
`B` of `A` at `𝔮` is a UFD. Then `𝔭 B` is a height-one prime of a UFD, so it is principal; its
generator can be taken in `𝔭`, and one denominator `T ∉ 𝔮` clears all of `𝔭`: `T 𝔭 ⊆ π A`.
This is the algebra behind a local equation of a prime divisor near a point (rung
`prime-divisor-ideal-sheaf`).

## Main results

* `HodgeLadder.exists_generator_of_height_eq_one`
-/

@[expose] public section

namespace HodgeLadder

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- **A height-one prime is principal after inverting one element outside a larger prime whose
localization is a UFD.** -/
theorem exists_generator_of_height_eq_one (𝔭 𝔮 : Ideal A) [𝔭.IsPrime] [𝔮.IsPrime] (h𝔭𝔮 : 𝔭 ≤ 𝔮)
    (h1 : 𝔭.height = 1) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.AtPrime B 𝔮]
    [UniqueFactorizationMonoid B] :
    ∃ π ∈ 𝔭, ∃ T ∉ 𝔮, ∀ b ∈ 𝔭, ∃ e : A, T * b = e * π := by
  have hdisj : Disjoint (𝔮.primeCompl : Set A) (𝔭 : Set A) := by
    rw [Set.disjoint_left]; intro a ha hp; exact ha (h𝔭𝔮 hp)
  have hB : IsDomain B := IsLocalization.isDomain_of_atPrime B 𝔮
  set P := 𝔭.map (algebraMap A B) with hP
  have hPprime : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔮.primeCompl B 𝔭 ‹_› hdisj
  have hPh : P.height = 1 := by
    rw [hP, IsLocalization.height_map_of_disjoint 𝔮.primeCompl 𝔭 hdisj, h1]
  obtain ⟨g, hg⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hPh
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl g
  -- the generator can be taken to be `a`
  have hgmem : IsLocalization.mk' B a s ∈ P := hg ▸ Submodule.mem_span_singleton_self _
  have haP : algebraMap A B a ∈ P := by
    rw [← IsLocalization.mk'_spec B a s]
    exact P.mul_mem_right _ hgmem
  have ha : a ∈ 𝔭 := by
    have := IsLocalization.under_map_of_isPrime_disjoint 𝔮.primeCompl B ‹𝔭.IsPrime› hdisj
    rw [← this]
    exact haP
  have hPa : P = Ideal.span {algebraMap A B a} := by
    rw [hg, Ideal.submodule_span_eq, ← IsLocalization.mk'_spec B a s]
    exact Ideal.span_singleton_eq_span_singleton.2 (associated_mul_unit_right _ _
      (IsLocalization.map_units B s))
  have hinj : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B (Ideal.primeCompl_le_nonZeroDivisors 𝔮)
  -- clear the denominators of a finite generating family of `𝔭`
  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    ((isNoetherianRing_iff_ideal_fg A).1 ‹_› 𝔭)
  have hk : ∀ k, ∃ (u : 𝔮.primeCompl) (c : A), (u : A) * x k = c * a := by
    intro k
    have hxk : algebraMap A B (x k) ∈ P :=
      Ideal.mem_map_of_mem _ (hx ▸ Submodule.subset_span ⟨k, rfl⟩)
    rw [hPa, Ideal.mem_span_singleton'] at hxk
    obtain ⟨c', hc'⟩ := hxk
    obtain ⟨⟨c, u⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl c'
    refine ⟨u, c, hinj ?_⟩
    rw [map_mul, map_mul, ← hc', ← mul_assoc, mul_comm (algebraMap A B (u : A)),
      IsLocalization.mk'_spec]
  choose u c hu using hk
  refine ⟨a, ha, ∏ k, (u k : A), ?_, ?_⟩
  · exact (Submonoid.prod_mem 𝔮.primeCompl fun k _ => (u k).2)
  · intro b hb
    rw [← hx] at hb
    induction hb using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        refine ⟨(∏ j ∈ Finset.univ.erase k, (u j : A)) * c k, ?_⟩
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_assoc, hu k, mul_assoc]
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
        obtain ⟨e₁, h₁⟩ := hy
        obtain ⟨e₂, h₂⟩ := hz
        exact ⟨e₁ + e₂, by rw [mul_add, h₁, h₂, add_mul]⟩
    | smul r y _ hy =>
        obtain ⟨e, he⟩ := hy
        exact ⟨r * e, by rw [smul_eq_mul, mul_left_comm, he, mul_assoc]⟩

end HodgeLadder
