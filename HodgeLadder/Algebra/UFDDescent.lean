module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.RingTheory.Nakayama

/-!
# Unique factorization descends along faithfully flat local homomorphisms

Let `A → B` be a faithfully flat local homomorphism, with `A` a Noetherian local domain and `B`
a UFD. Then `A` is a UFD. This is the case of Mori's theorem the ladder needs (rung
`ufd-descent`, `docs/sketches/prime-divisors-cartier.md`): local rings of a smooth complex variety
are UFDs because their analytic stalks are.

The proof uses Mathlib's criterion (`UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`).
For a height-one prime `P` of `A` and `0 ≠ a ∈ P`, the double colon `(aA : (aA : P))` becomes
principal in `B` (colons by finitely generated ideals commute with flat base change, by the
equational criterion; in a UFD, double colons of principal ideals are principal). Rank-one descent
makes it principal in `A`, say `tA`, and `P ⊆ tA`. Since `P` is associated to `A/aA`, `t` is not a
unit; if `t ∉ P` then `P = tP`, which Nakayama forbids; so `P = tA`.

## Main results

* `HodgeLadder.mem_map_colon_of_flat`: colons by finitely many elements commute with flat base
  change.
-/

@[expose] public section

open Ideal

namespace HodgeLadder

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- **Colons commute with flat base change.** If `B` is flat over `A` and `y ∈ B` satisfies
`y · xᵢ ∈ aB` for finitely many `xᵢ ∈ A`, then `y` lies in the extension of the colon ideal
`(aA : {xᵢ})`. -/
theorem mem_map_colon_of_flat [Module.Flat A B] (a : A) {n : ℕ} (x : Fin n → A) (y : B)
    (hy : ∀ i, ∃ z : B, y * algebraMap A B (x i) = algebraMap A B a * z) :
    y ∈ ((Ideal.span {a}).colon (Set.range x)).map (algebraMap A B) := by
  choose z hz using hy
  let X : (Fin (n + 1) →₀ A) →ₗ[A] B := Finsupp.linearCombination A (Fin.cons y z : Fin (n + 1) → B)
  let f : (Fin n →₀ A) →ₗ[A] (Fin (n + 1) →₀ A) :=
    Finsupp.linearCombination A (fun i => Finsupp.single 0 (x i) - Finsupp.single i.succ a)
  have hXf : X ∘ₗ f = 0 := by
    ext i
    simp only [X, f, LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.linearCombination_single,
      one_smul, map_sub, Fin.cons_zero, Fin.cons_succ, LinearMap.zero_apply,
      Algebra.smul_def]
    rw [mul_comm, hz i, sub_self]
  obtain ⟨k, α, β, hX, hαf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hXf
  have hy' : y = X (Finsupp.single 0 1) := by
    simp [X]
  -- every coordinate of `α e₀` lies in the colon ideal
  have hcoord : ∀ j, α (Finsupp.single 0 1) j ∈ (Ideal.span {a}).colon (Set.range x) := by
    intro j
    rw [Submodule.mem_colon]
    rintro _ ⟨i, rfl⟩
    have h0 := congrArg (fun v => v j) (LinearMap.congr_fun hαf (Finsupp.single i 1))
    simp only [LinearMap.comp_apply, f, Finsupp.linearCombination_single, one_smul, map_sub,
      LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply] at h0
    rw [show Finsupp.single (0 : Fin (n + 1)) (x i) = x i • Finsupp.single 0 1 by simp,
      show Finsupp.single i.succ a = a • Finsupp.single i.succ 1 by simp,
      map_smul, map_smul] at h0
    simp only [Finsupp.smul_apply, smul_eq_mul] at h0
    rw [smul_eq_mul, Ideal.mem_span_singleton]
    exact ⟨α (Finsupp.single i.succ 1) j, by rw [mul_comm]; exact sub_eq_zero.mp h0⟩
  rw [hy', hX, LinearMap.comp_apply]
  rw [← Finsupp.sum_single (α (Finsupp.single 0 1))]
  rw [map_finsuppSum]
  refine Submodule.sum_mem _ fun j _ => ?_
  dsimp only
  rw [show Finsupp.single j (α (Finsupp.single 0 1) j) =
      α (Finsupp.single 0 1) j • Finsupp.single j 1 by simp, map_smul, Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcoord j))

/-- **Colons by finitely generated ideals commute with flat base change.** -/
theorem map_colon_eq_of_flat [Module.Flat A B] (a : A) (J : Ideal A) (hJ : J.FG) :
    ((Ideal.span {a}).colon (J : Set A)).map (algebraMap A B) =
      (Ideal.span {algebraMap A B a}).colon ((J.map (algebraMap A B) : Ideal B) : Set B) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.map, Ideal.colon_span, Submodule.mem_colon]
    rintro _ ⟨j, hj, rfl⟩
    have := (Submodule.mem_colon.mp hr) j hj
    rw [smul_eq_mul, Ideal.mem_span_singleton] at this ⊢
    obtain ⟨c, hc⟩ := this
    exact ⟨algebraMap A B c, by rw [← map_mul, hc, map_mul]⟩
  · obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
    intro y hy
    have hcol : (Ideal.span {a}).colon (J : Set A) = (Ideal.span {a}).colon (Set.range x) := by
      rw [← hx, Ideal.colon_span]
    rw [hcol]
    refine mem_map_colon_of_flat a x y fun i => ?_
    have hxi : algebraMap A B (x i) ∈ J.map (algebraMap A B) :=
      Ideal.mem_map_of_mem _ (hx ▸ Submodule.subset_span ⟨i, rfl⟩)
    have := (Submodule.mem_colon.mp hy) _ hxi
    rw [smul_eq_mul, Ideal.mem_span_singleton] at this
    exact this

section UFD

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-- In a UFD, the colon of a nonzero principal ideal by one element is principal. -/
theorem isPrincipal_colon_singleton (a x : R) (ha : a ≠ 0) :
    ((Ideal.span {a}).colon ({x} : Set R)).IsPrincipal := by
  classical
  let := UniqueFactorizationMonoid.toGCDMonoid R
  obtain ⟨a', x', ea, ex, hu⟩ := extract_gcd a x
  have hg : gcd a x ≠ 0 := fun h => ha ((gcd_eq_zero_iff a x).1 h).1
  set g := gcd a x with hgdef
  have hrel : IsRelPrime a' x' := (gcd_isUnit_iff_isRelPrime).1 hu
  refine ⟨a', ?_⟩
  ext r
  rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton,
    Submodule.mem_span_singleton]
  constructor
  · intro h
    rw [ea, ex, show r * (g * x') = g * (r * x') by ring] at h
    have h' : a' ∣ r * x' := (mul_dvd_mul_iff_left hg).1 h
    obtain ⟨c, hc⟩ := hrel.dvd_of_dvd_mul_right h'
    exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩
  · rintro ⟨c, rfl⟩
    rw [ea, ex, smul_eq_mul]
    exact ⟨c * x', by ring⟩

omit [IsDomain R] in
/-- In a UFD, the intersection of two principal ideals is principal. -/
theorem isPrincipal_inf_of_isPrincipal {I J : Ideal R} (hI : I.IsPrincipal) (hJ : J.IsPrincipal) :
    (I ⊓ J).IsPrincipal := by
  classical
  let := UniqueFactorizationMonoid.toGCDMonoid R
  obtain ⟨b, rfl⟩ := hI
  obtain ⟨c, rfl⟩ := hJ
  refine ⟨lcm b c, ?_⟩
  ext r
  simp only [Submodule.mem_inf, Submodule.mem_span_singleton, ] at *
  rw [show (∃ a, a • b = r) ↔ b ∣ r from ⟨fun ⟨a, h⟩ => ⟨a, by rw [← h, smul_eq_mul, mul_comm]⟩,
      fun ⟨a, h⟩ => ⟨a, by rw [h, smul_eq_mul, mul_comm]⟩⟩,
    show (∃ a, a • c = r) ↔ c ∣ r from ⟨fun ⟨a, h⟩ => ⟨a, by rw [← h, smul_eq_mul, mul_comm]⟩,
      fun ⟨a, h⟩ => ⟨a, by rw [h, smul_eq_mul, mul_comm]⟩⟩,
    show (∃ a, a • lcm b c = r) ↔ lcm b c ∣ r from ⟨fun ⟨a, h⟩ => ⟨a, by rw [← h, smul_eq_mul, mul_comm]⟩,
      fun ⟨a, h⟩ => ⟨a, by rw [h, smul_eq_mul, mul_comm]⟩⟩]
  exact lcm_dvd_iff.symm

/-- In a UFD, the colon of a nonzero principal ideal by a finitely generated ideal is
principal. -/
theorem isPrincipal_colon_of_fg (a : R) (ha : a ≠ 0) (J : Ideal R) (hJ : J.FG) :
    ((Ideal.span {a}).colon (J : Set R)).IsPrincipal := by
  classical
  obtain ⟨s, rfl⟩ := hJ
  rw [Ideal.colon_span]
  induction s using Finset.induction_on with
  | empty => simp only [Finset.coe_empty, Submodule.colon_empty]; exact ⟨1, by simp⟩
  | insert x s _ ih =>
      rw [Finset.coe_insert, Set.insert_eq, Submodule.colon_union]
      exact isPrincipal_inf_of_isPrincipal (isPrincipal_colon_singleton a x ha) ih

end UFD

/-- **Principality descends along faithfully flat local homomorphisms to a domain.** If the
extension of an ideal `I` to a local domain `B`, faithfully flat over `A`, is principal, then `I`
is principal. -/
theorem isPrincipal_of_isPrincipal_map [Module.FaithfullyFlat A B] [IsLocalRing B] [IsDomain B]
    (I : Ideal A) (hI : (I.map (algebraMap A B)).IsPrincipal) : I.IsPrincipal := by
  obtain ⟨g, hg⟩ := hI
  have key : ∃ i ∈ I, I.map (algebraMap A B) = Ideal.span {algebraMap A B i} := by
    by_cases hg0 : g = 0
    · exact ⟨0, I.zero_mem, by rw [hg, hg0, map_zero]⟩
    have hgmem : g ∈ Submodule.span B ((algebraMap A B) '' I) := by
      change g ∈ I.map (algebraMap A B)
      rw [hg]; exact Submodule.mem_span_singleton_self g
    obtain ⟨n, b, v, hv⟩ := Submodule.mem_span_set'.1 hgmem
    have hdiv : ∀ k, ∃ c : B, (v k : B) = g * c := by
      intro k
      obtain ⟨i, hi, hik⟩ := (v k).2
      have : algebraMap A B i ∈ I.map (algebraMap A B) := Ideal.mem_map_of_mem _ hi
      rw [hg, Submodule.mem_span_singleton] at this
      obtain ⟨c, hc⟩ := this
      exact ⟨c, by rw [← hik, ← hc, smul_eq_mul, mul_comm]⟩
    choose c hc using hdiv
    have hone : ∑ k, b k * c k = 1 := by
      apply mul_left_cancel₀ hg0
      rw [mul_one, Finset.mul_sum]
      conv_rhs => rw [← hv]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, hc k]; ring
    obtain ⟨k, hk⟩ : ∃ k, IsUnit (c k) := by
      by_contra hno
      push Not at hno
      have : (1 : B) ∈ IsLocalRing.maximalIdeal B := by
        rw [← hone]
        exact Submodule.sum_mem _ fun k _ =>
          Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hno k))
      exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 this)
    obtain ⟨i, hi, hik⟩ := (v k).2
    refine ⟨i, hi, ?_⟩
    rw [hg, hik, hc k]
    exact (Ideal.span_singleton_eq_span_singleton).2 (associated_mul_unit_right g (c k) hk)
  obtain ⟨i, hi, hmap⟩ := key
  refine ⟨i, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).2 hi)⟩
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I, hmap,
    show Ideal.span {algebraMap A B i} = (Ideal.span {i}).map (algebraMap A B) by
      rw [Ideal.map_span, Set.image_singleton],
    Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- A height-one prime `P` of a Noetherian domain and `0 ≠ a ∈ P`: some `y ∉ aA` has `P y ⊆ aA`. -/
theorem exists_mem_colon_not_mem_of_height_eq_one [IsNoetherianRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) (a : A) (haP : a ∈ P) (ha : a ≠ 0) :
    ∃ y, y ∈ (Ideal.span {a}).colon (P : Set A) ∧ y ∉ Ideal.span {a} := by
  have hle : Ideal.span {a} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 haP
  have hmin : P ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨‹_›, hle⟩, fun Q hQ hQP => ?_⟩
    obtain ⟨hQprime, hQle⟩ := hQ
    by_contra hne
    have hlt : Q < P := lt_of_le_of_ne hQP (fun h => hne (h ▸ le_rfl))
    have hbot : (⊥ : Ideal A) < Q := bot_lt_iff_ne_bot.2 fun h => ha <| by
      have := hQle (Ideal.mem_span_singleton_self a)
      rwa [h, Submodule.mem_bot] at this
    have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hP] at h2
    have : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add_left (le_trans (by simp) h1) 1) h2
    exact absurd this (by norm_num)
  have hann : Module.annihilator A (A ⧸ Ideal.span {a}) = Ideal.span {a} :=
    Ideal.annihilator_quotient
  have hass : P ∈ associatedPrimes A (A ⧸ Ideal.span {a}) :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A (A ⧸ Ideal.span {a}) (by rw [hann]; exact hmin)
  obtain ⟨-, m, hm⟩ := (Submodule.isAssociatedPrime_iff).1 hass
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨y, ?_, ?_⟩
  · rw [Submodule.mem_colon]
    intro p hp
    have : p ∈ Submodule.colon (⊥ : Submodule A (A ⧸ Ideal.span {a})) {Ideal.Quotient.mk _ y} :=
      hm ▸ hp
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at this
    rw [smul_eq_mul, mul_comm]; exact this
  · intro hy
    have : (1 : A) ∈ P := by
      rw [hm, Submodule.mem_colon_singleton, Submodule.mem_bot, one_smul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one P).2 this)

/-- **Mori's descent, local case.** Let `A → B` be faithfully flat, with `A` a Noetherian local
domain and `B` a local domain that is a UFD. Then `A` is a UFD. -/
theorem uniqueFactorizationMonoid_of_faithfullyFlat [IsNoetherianRing A] [IsDomain A]
    [IsLocalRing A] [Module.FaithfullyFlat A B] [IsLocalRing B] [IsDomain B]
    [UniqueFactorizationMonoid B] : UniqueFactorizationMonoid A := by
  refine UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one fun P _ hP => ?_
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.ne_bot_of_height_eq_one hP)
  have ha' : algebraMap A B a ≠ 0 := fun h => ha (hinj (by rw [h, map_zero]))
  obtain ⟨y, hyK, hya⟩ := exists_mem_colon_not_mem_of_height_eq_one P hP a haP ha
  set K := (Ideal.span {a}).colon (P : Set A) with hK
  set Istar := (Ideal.span {a}).colon (K : Set A) with hIstar
  have hPI : P ≤ Istar := by
    intro p hp
    rw [hIstar, Submodule.mem_colon]
    intro k hk
    have hk' := Submodule.mem_colon.1 (show k ∈ (Ideal.span {a}).colon (P : Set A) from hk) p hp
    rw [smul_eq_mul, mul_comm]
    rw [smul_eq_mul] at hk'
    exact hk'
  have hItop : Istar ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ Istar := h ▸ Submodule.mem_top
    rw [hIstar, Submodule.mem_colon] at h1
    exact hya (by simpa using h1 y hyK)
  have hfgP : P.FG := (isNoetherianRing_iff_ideal_fg A).1 ‹_› P
  have hfgK : K.FG := (isNoetherianRing_iff_ideal_fg A).1 ‹_› K
  have hmapI : (Istar.map (algebraMap A B)).IsPrincipal := by
    rw [hIstar, map_colon_eq_of_flat a K hfgK, hK, map_colon_eq_of_flat a P hfgP]
    obtain ⟨c, hc⟩ := isPrincipal_colon_of_fg (algebraMap A B a) ha' (P.map (algebraMap A B))
      (hfgP.map _)
    rw [hc, Ideal.submodule_span_eq, Ideal.colon_span]
    exact isPrincipal_colon_singleton _ c ha'
  obtain ⟨t, ht⟩ := isPrincipal_of_isPrincipal_map Istar hmapI
  have hspan : Istar = Ideal.span {t} := ht
  have htP : t ∈ P := by
    by_contra htP
    have hle : P ≤ Ideal.span {t} • P := by
      intro p hp
      have : p ∈ Ideal.span {t} := hspan ▸ hPI hp
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 this
      have hr : r ∈ P := (Ideal.IsPrime.mem_or_mem ‹_› hp).resolve_right htP
      rw [Ideal.smul_eq_mul, mul_comm r t]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self t) hr
    have hjac : Ideal.span {t} ≤ (⊥ : Ideal A).jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal (hspan ▸ hItop)
    exact Ideal.ne_bot_of_height_eq_one hP
      (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ P hfgP hle hjac)
  refine ⟨t, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem P).2 htP)⟩
  exact (show Ideal.span {t} = Submodule.span A {t} from rfl) ▸ hspan ▸ hPI

end HodgeLadder
