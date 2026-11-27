module

public import HodgeLadder.Markman.Chevalley
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating

/-!
# The half-spin form of Chevalley's theorem

Let `M` be a finite free module over a commutative ring `R`, and let
`spinAction R M : CliffordAlgebra (QuadraticForm.dualProd R M) →ₐ[R]
Module.End R (ExteriorAlgebra R M)` be the action by contraction plus wedge (rung
`clifford-exterior-spin`), bijective by Chevalley's theorem (rung `clifford-exterior-chevalley`).
This module proves that the bijection matches the two `ZMod 2` gradings, and that the even
Clifford algebra is the product of the endomorphism algebras of the two half-spin modules
`∧^ev M` and `∧^odd M` ([GolyshevLuntsOrlov2001] §3.5.1 and §4.3.6, "Cl^+ onto H^ev"; rung
`clifford-exterior-half-spin`).

1. **Parity, equality form.** `x ∈ evenOdd (dualProd R M) i` if and only if `spinAction x` maps
   the parity-`j` part of `∧M` into the parity-`(j + i)` part for every `j`. Equivalently, the
   image of `evenOdd (dualProd R M) i` under `spinAction` is exactly the submodule
   `parityShift R M i` of parity-`i` endomorphisms.
2. **Half-spin decomposition.** Restriction to the two parity parts is an algebra isomorphism
   `CliffordAlgebra.even (dualProd R M) ≃ₐ[R]
   Module.End R (exteriorParity R M 0) × Module.End R (exteriorParity R M 1)`.

## Main definitions

* `HodgeLadder.parityShift`: the endomorphisms of `∧M` of parity `i`.
* `HodgeLadder.spinActionParity`: an even element acting on one parity part.
* `HodgeLadder.spinActionEven`: the even Clifford algebra acting on both parity parts.
* `HodgeLadder.spinEquivEven`: the half-spin isomorphism.

## Main results

* `HodgeLadder.spinAction_mem_evenOdd_iff_of_injective`: parity of a Clifford element is read
  off its action whenever the action is faithful; `HodgeLadder.injective_spinAction_iff`: the
  criterion for all `i` is equivalent to faithfulness.
* `HodgeLadder.spinAction_mem_evenOdd_iff`, `HodgeLadder.spinAction_mem_evenOdd_zero_iff`,
  `HodgeLadder.spinAction_mem_evenOdd_one_iff`: the criterion for `M` finite free.
* `HodgeLadder.map_evenOdd_dualProd_eq_parityShift`: `spinAction` maps `evenOdd i` onto
  `parityShift i`; `HodgeLadder.evenOdd_dualProd_eq_comap_parityShift`: the preimage form.
* `HodgeLadder.spinActionEven_bijective`, `HodgeLadder.spinEquivEven_apply`,
  `HodgeLadder.spinEquivEven_apply_fst`, `HodgeLadder.spinEquivEven_apply_snd`: the half-spin
  isomorphism and its values; `HodgeLadder.spinActionParity_surjective`: each component alone
  is surjective.
* Tests: `HodgeLadder.spinActionEven_int_zmod_two_not_surjective` (`ZMod 2` over `ℤ`) and
  `HodgeLadder.evenOdd_one_iff_zmod_four_fails`,
  `HodgeLadder.spinActionEven_zmod_four_not_injective`, `HodgeLadder.not_free_zmodFourIdeal`
  (the ideal `(2)` of `ZMod 4`): `Module.Free` is needed;
  `HodgeLadder.ι_vec_not_mem_evenOdd_zero_int`: the even condition rejects a generator.
-/

@[expose] public section

namespace HodgeLadder

open CliffordAlgebra

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The endomorphisms of the exterior algebra of parity `i`: those that map the parity-`j` part
`exteriorParity R M j` into the parity-`(j + i)` part for every `j : ZMod 2`. -/
def parityShift (i : ZMod 2) : Submodule R (Module.End R (ExteriorAlgebra R M)) :=
  ⨅ j : ZMod 2, Submodule.compatibleMaps (exteriorParity R M j) (exteriorParity R M (j + i))

/-- Membership in `parityShift`. -/
theorem mem_parityShift {i : ZMod 2} {f : Module.End R (ExteriorAlgebra R M)} :
    f ∈ parityShift R M i ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        f y ∈ exteriorParity R M (j + i) := by
  simp only [parityShift, Submodule.mem_iInf]
  rfl

/-- For any quadratic form, `evenOdd Q k` and `evenOdd Q (k + 1)` are complementary. -/
theorem evenOdd_isCompl_add_one {N : Type*} [AddCommGroup N] [Module R N]
    (Q : QuadraticForm R N) (k : ZMod 2) : IsCompl (evenOdd Q k) (evenOdd Q (k + 1)) := by
  fin_cases k
  · exact evenOdd_isCompl Q
  · exact (evenOdd_isCompl Q).symm

/-- The parity parts `exteriorParity R M k` and `exteriorParity R M (k + 1)` are complementary. -/
theorem exteriorParity_isCompl_add_one (k : ZMod 2) :
    IsCompl (exteriorParity R M k) (exteriorParity R M (k + 1)) := by
  rw [exteriorParity_eq_evenOdd, exteriorParity_eq_evenOdd]
  exact evenOdd_isCompl_add_one R (0 : QuadraticForm R M) k

/-- The even and the odd part of the exterior algebra are complementary. -/
theorem exteriorParity_isCompl : IsCompl (exteriorParity R M 0) (exteriorParity R M 1) :=
  exteriorParity_isCompl_add_one R M 0

/-- Two endomorphisms of `∧M` that agree on the even and on the odd part are equal. -/
theorem ext_exteriorParity {f g : Module.End R (ExteriorAlgebra R M)}
    (h0 : ∀ y ∈ exteriorParity R M 0, f y = g y) (h1 : ∀ y ∈ exteriorParity R M 1, f y = g y) :
    f = g := by
  refine LinearMap.ext fun y => ?_
  have hy : y ∈ exteriorParity R M 0 ⊔ exteriorParity R M 1 := by
    rw [(exteriorParity_isCompl R M).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, map_add, h0 a ha, h1 b hb]

/-- **Parity is read off the action, for a faithful action.** If `spinAction R M` is
injective, an element `x` of the Clifford algebra of the split form lies in
`evenOdd (dualProd R M) i` if and only if `spinAction x` maps the parity-`j` part of `∧M` into
the parity-`(j + i)` part for every `j`. The forward direction holds with no hypothesis
(`spinAction_mem_exteriorParity`). -/
theorem spinAction_mem_evenOdd_iff_of_injective (hinj : Function.Injective (spinAction R M))
    (i : ZMod 2) (x : CliffordAlgebra (QuadraticForm.dualProd R M)) :
    x ∈ evenOdd (QuadraticForm.dualProd R M) i ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        spinAction R M x y ∈ exteriorParity R M (j + i) := by
  constructor
  · intro hx j y hy
    rw [add_comm]
    exact spinAction_mem_exteriorParity R M hx hy
  · intro h
    have hx : x ∈ evenOdd (QuadraticForm.dualProd R M) i ⊔
        evenOdd (QuadraticForm.dualProd R M) (i + 1) := by
      rw [(evenOdd_isCompl_add_one R _ i).sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    have hP : ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        spinAction R M b y = 0 := by
      intro j y hy
      have h1 : spinAction R M b y ∈ exteriorParity R M (j + i) := by
        have ha' := spinAction_mem_exteriorParity R M ha hy
        rw [add_comm i j] at ha'
        have := Submodule.sub_mem _ (h j y hy) ha'
        rwa [map_add, LinearMap.add_apply, add_sub_cancel_left] at this
      have h2 : spinAction R M b y ∈ exteriorParity R M (j + i + 1) := by
        have := spinAction_mem_exteriorParity R M hb hy
        rwa [show i + 1 + j = j + i + 1 by ring] at this
      exact (Submodule.disjoint_def.mp (exteriorParity_isCompl_add_one R M (j + i)).disjoint)
        _ h1 h2
    have hb0 : b = 0 := hinj (by
      rw [map_zero]
      exact ext_exteriorParity R M (fun y hy => hP 0 y hy) (fun y hy => hP 1 y hy))
    rwa [hb0, add_zero]

/-- **The parity criterion is equivalent to faithfulness.** The criterion of
`spinAction_mem_evenOdd_iff_of_injective` holds for every `i` and `x` exactly when `spinAction`
is injective: an element acting by zero satisfies the criterion in both parities. -/
theorem injective_spinAction_iff :
    Function.Injective (spinAction R M) ↔
      ∀ (i : ZMod 2) (x : CliffordAlgebra (QuadraticForm.dualProd R M)),
        (x ∈ evenOdd (QuadraticForm.dualProd R M) i ↔
          ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
            spinAction R M x y ∈ exteriorParity R M (j + i)) := by
  refine ⟨fun hinj => spinAction_mem_evenOdd_iff_of_injective R M hinj, fun h => ?_⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hmem : ∀ i, z ∈ evenOdd (QuadraticForm.dualProd R M) i := fun i =>
    (h i z).mpr fun j y _ => by rw [hz, LinearMap.zero_apply]; exact Submodule.zero_mem _
  exact (Submodule.disjoint_def.mp (evenOdd_isCompl _).disjoint) _ (hmem 0) (hmem 1)

/-- **Parity is read off the action.** For `M` finite free, an element `x` of the Clifford
algebra of the split form lies in `evenOdd (dualProd R M) i` if and only if `spinAction x`
maps the parity-`j` part of `∧M` into the parity-`(j + i)` part for every `j`. -/
theorem spinAction_mem_evenOdd_iff [Module.Free R M] [Module.Finite R M] (i : ZMod 2)
    (x : CliffordAlgebra (QuadraticForm.dualProd R M)) :
    x ∈ evenOdd (QuadraticForm.dualProd R M) i ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        spinAction R M x y ∈ exteriorParity R M (j + i) :=
  spinAction_mem_evenOdd_iff_of_injective R M (spinAction_bijective R M).1 i x

/-- **Even elements are those that preserve parity.** For `M` finite free, `x` is even if and
only if `spinAction x` maps each parity part of `∧M` into itself. -/
theorem spinAction_mem_evenOdd_zero_iff [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra (QuadraticForm.dualProd R M)) :
    x ∈ evenOdd (QuadraticForm.dualProd R M) 0 ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        spinAction R M x y ∈ exteriorParity R M j := by
  simpa using spinAction_mem_evenOdd_iff R M 0 x

/-- **Odd elements are those that swap parity.** For `M` finite free, `x` is odd if and only
if `spinAction x` maps the parity-`j` part of `∧M` into the parity-`(j + 1)` part. -/
theorem spinAction_mem_evenOdd_one_iff [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra (QuadraticForm.dualProd R M)) :
    x ∈ evenOdd (QuadraticForm.dualProd R M) 1 ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        spinAction R M x y ∈ exteriorParity R M (j + 1) :=
  spinAction_mem_evenOdd_iff R M 1 x

/-- **The grading, equality form.** For `M` finite free, `spinAction` maps the parity-`i` part
of the Clifford algebra onto the parity-`i` endomorphisms of `∧M`. -/
theorem map_evenOdd_dualProd_eq_parityShift [Module.Free R M] [Module.Finite R M]
    (i : ZMod 2) :
    (evenOdd (QuadraticForm.dualProd R M) i).map (spinAction R M).toLinearMap =
      parityShift R M i := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_parityShift R M).mpr ((spinAction_mem_evenOdd_iff R M i x).mp hx)
  · intro hf
    obtain ⟨x, rfl⟩ := (spinAction_bijective R M).2 f
    exact ⟨x, (spinAction_mem_evenOdd_iff R M i x).mpr ((mem_parityShift R M).mp hf), rfl⟩

/-- **The grading, preimage form.** For `M` finite free, the parity-`i` part of the Clifford
algebra is the preimage under `spinAction` of the parity-`i` endomorphisms of `∧M`. -/
theorem evenOdd_dualProd_eq_comap_parityShift [Module.Free R M] [Module.Finite R M]
    (i : ZMod 2) :
    evenOdd (QuadraticForm.dualProd R M) i =
      (parityShift R M i).comap (spinAction R M).toLinearMap := by
  ext x
  rw [Submodule.mem_comap, mem_parityShift]
  exact spinAction_mem_evenOdd_iff R M i x

/-- An even element of the Clifford algebra maps each parity part of `∧M` into itself (no
hypothesis on `M`). -/
theorem spinAction_mem_exteriorParity_of_mem_even
    {x : CliffordAlgebra (QuadraticForm.dualProd R M)}
    (hx : x ∈ CliffordAlgebra.even (QuadraticForm.dualProd R M)) {j : ZMod 2}
    {y : ExteriorAlgebra R M} (hy : y ∈ exteriorParity R M j) :
    spinAction R M x y ∈ exteriorParity R M j := by
  have hx' : x ∈ evenOdd (QuadraticForm.dualProd R M) 0 := by
    rw [← even_toSubmodule]; exact hx
  simpa using spinAction_mem_exteriorParity R M hx' hy

/-- An even element of the Clifford algebra acting on the parity-`j` part of `∧M`: the
restriction of `spinAction`. -/
def spinActionParity (j : ZMod 2) :
    CliffordAlgebra.even (QuadraticForm.dualProd R M) →ₐ[R]
      Module.End R (exteriorParity R M j) where
  toFun x := (spinAction R M x).restrict
    (fun _ hy => spinAction_mem_exteriorParity_of_mem_even R M x.2 hy)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' r := by ext; simp

/-- The value of `spinActionParity`: the action of `x` on `∧M`. -/
@[simp]
theorem spinActionParity_apply (j : ZMod 2) (x : CliffordAlgebra.even (QuadraticForm.dualProd R M))
    (y : exteriorParity R M j) :
    (spinActionParity R M j x y : ExteriorAlgebra R M) = spinAction R M x y := rfl

/-- The even Clifford algebra acting on the even and the odd part of `∧M`. -/
def spinActionEven :
    CliffordAlgebra.even (QuadraticForm.dualProd R M) →ₐ[R]
      Module.End R (exteriorParity R M 0) × Module.End R (exteriorParity R M 1) :=
  (spinActionParity R M 0).prod (spinActionParity R M 1)

/-- **Half-spin form of Chevalley's theorem, bijectivity.** For `M` finite free, the even
Clifford algebra acts on `∧^ev M × ∧^odd M` bijectively onto the product of the two
endomorphism algebras. -/
theorem spinActionEven_bijective [Module.Free R M] [Module.Finite R M] :
    Function.Bijective (spinActionEven R M) := by
  constructor
  · intro x x' h
    have h0 := congrArg Prod.fst h
    have h1 := congrArg Prod.snd h
    refine Subtype.ext ((spinAction_bijective R M).1 (ext_exteriorParity R M ?_ ?_))
    · intro y hy
      exact congrArg (fun f => (f ⟨y, hy⟩ : ExteriorAlgebra R M)) h0
    · intro y hy
      exact congrArg (fun f => (f ⟨y, hy⟩ : ExteriorAlgebra R M)) h1
  · rintro ⟨f₀, f₁⟩
    have hc := exteriorParity_isCompl R M
    let g : Module.End R (ExteriorAlgebra R M) :=
      (exteriorParity R M 0).subtype ∘ₗ f₀ ∘ₗ (exteriorParity R M 0).projectionOnto _ hc +
        (exteriorParity R M 1).subtype ∘ₗ f₁ ∘ₗ (exteriorParity R M 1).projectionOnto _ hc.symm
    have hg0 : ∀ (y : ExteriorAlgebra R M) (hy : y ∈ exteriorParity R M 0),
        g y = f₀ ⟨y, hy⟩ := by
      intro y hy
      simp only [g, LinearMap.add_apply, LinearMap.comp_apply,
        Submodule.projectionOnto_apply_of_mem_left hc hy,
        Submodule.projectionOnto_apply_right hc.symm ⟨y, hy⟩, map_zero, Submodule.subtype_apply,
        add_zero]
    have hg1 : ∀ (y : ExteriorAlgebra R M) (hy : y ∈ exteriorParity R M 1),
        g y = f₁ ⟨y, hy⟩ := by
      intro y hy
      simp only [g, LinearMap.add_apply, LinearMap.comp_apply,
        Submodule.projectionOnto_apply_of_mem_left hc.symm hy,
        Submodule.projectionOnto_apply_right hc ⟨y, hy⟩, map_zero, Submodule.subtype_apply,
        zero_add]
    obtain ⟨x, hx⟩ := spinAction_surjective R M g
    have hxe : x ∈ evenOdd (QuadraticForm.dualProd R M) 0 := by
      rw [spinAction_mem_evenOdd_zero_iff]
      intro j y hy
      rw [hx]
      fin_cases j
      · rw [hg0 y hy]; exact (f₀ ⟨y, hy⟩).2
      · rw [hg1 y hy]; exact (f₁ ⟨y, hy⟩).2
    refine ⟨⟨x, by rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]; exact hxe⟩, ?_⟩
    refine Prod.ext (LinearMap.ext fun y => Subtype.ext ?_) (LinearMap.ext fun y => Subtype.ext ?_)
    · change spinAction R M x y = _
      rw [hx, hg0 y y.2]
    · change spinAction R M x y = _
      rw [hx, hg1 y y.2]

/-- **The half-spin isomorphism.** For `M` finite free over a commutative ring, the even Clifford
algebra of the split form is isomorphic, by restriction of `spinAction` to the two parity
parts, to `Module.End R (∧^ev M) × Module.End R (∧^odd M)` ([GolyshevLuntsOrlov2001] §3.5.1,
§4.3.6). -/
noncomputable def spinEquivEven [Module.Free R M] [Module.Finite R M] :
    CliffordAlgebra.even (QuadraticForm.dualProd R M) ≃ₐ[R]
      Module.End R (exteriorParity R M 0) × Module.End R (exteriorParity R M 1) :=
  AlgEquiv.ofBijective (spinActionEven R M) (spinActionEven_bijective R M)

/-- **Each half-spin component is surjective.** For `M` finite free, every endomorphism of
`exteriorParity R M j` is the action of an even element of the Clifford algebra. -/
theorem spinActionParity_surjective [Module.Free R M] [Module.Finite R M] (j : ZMod 2) :
    Function.Surjective (spinActionParity R M j) := by
  intro f
  fin_cases j
  · obtain ⟨x, hx⟩ := (spinActionEven_bijective R M).2 (f, 1)
    exact ⟨x, congrArg Prod.fst hx⟩
  · obtain ⟨x, hx⟩ := (spinActionEven_bijective R M).2 (1, f)
    exact ⟨x, congrArg Prod.snd hx⟩

/-- `spinEquivEven` is the pair of restrictions of `spinAction`. -/
@[simp]
theorem spinEquivEven_apply [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra.even (QuadraticForm.dualProd R M)) :
    spinEquivEven R M x = (spinActionParity R M 0 x, spinActionParity R M 1 x) := rfl

/-- On the even part, `spinEquivEven x` acts as `spinAction x`. -/
theorem spinEquivEven_apply_fst [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra.even (QuadraticForm.dualProd R M)) (y : exteriorParity R M 0) :
    ((spinEquivEven R M x).1 y : ExteriorAlgebra R M) = spinAction R M x y := rfl

/-- On the odd part, `spinEquivEven x` acts as `spinAction x`. -/
theorem spinEquivEven_apply_snd [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra.even (QuadraticForm.dualProd R M)) (y : exteriorParity R M 1) :
    ((spinEquivEven R M x).2 y : ExteriorAlgebra R M) = spinAction R M x y := rfl

/-- Sanity check: the even generator `ι v * ι w` acts on the even part as
`spinGen v ∘ spinGen w`. -/
theorem spinEquivEven_ι_mul_ι_fst [Module.Free R M] [Module.Finite R M]
    (v w : Module.Dual R M × M) (y : exteriorParity R M 0) :
    ((spinEquivEven R M ((even.ι _).bilin v w)).1 y : ExteriorAlgebra R M) =
      spinGen R M v (spinGen R M w y) := by
  rw [spinEquivEven_apply_fst]
  change spinAction R M (ι _ v * ι _ w) y = _
  rw [map_mul, Module.End.mul_apply, spinAction_ι, spinAction_ι]

section Tests

/-- **`Module.Free` cannot be dropped from the half-spin isomorphism.** For the finite, non-free
`ℤ`-module `ZMod 2` the even Clifford algebra does not act surjectively on the two parity parts:
`(0, 1)` is not in the range, because every element acts by left multiplication by its value
on `1 ∈ ∧^ev`. -/
theorem spinActionEven_int_zmod_two_not_surjective :
    ¬ Function.Surjective (spinActionEven ℤ (ZMod 2)) := by
  intro hs
  obtain ⟨x, hx⟩ := hs (0, 1)
  have h1 : (1 : ExteriorAlgebra ℤ (ZMod 2)) ∈ exteriorParity ℤ (ZMod 2) 0 := by
    rw [exteriorParity_eq_evenOdd]
    exact Submodule.one_le.mp (one_le_evenOdd_zero _)
  have hι : ExteriorAlgebra.ι ℤ (1 : ZMod 2) ∈ exteriorParity ℤ (ZMod 2) 1 := by
    rw [exteriorParity_eq_evenOdd]
    exact ι_mem_evenOdd_one _ _
  have h0 : spinAction ℤ (ZMod 2) x 1 = 0 := by
    have := congrArg (fun p => (p.1 ⟨1, h1⟩ : ExteriorAlgebra ℤ (ZMod 2))) hx
    simpa [spinActionEven] using this
  have h2 : spinAction ℤ (ZMod 2) x (ExteriorAlgebra.ι ℤ 1) = ExteriorAlgebra.ι ℤ 1 := by
    have := congrArg (fun p => (p.2 ⟨_, hι⟩ : ExteriorAlgebra ℤ (ZMod 2))) hx
    simpa [spinActionEven] using this
  rw [spinAction_int_zmod_two_apply, h0, zero_mul, eq_comm, ExteriorAlgebra.ι_eq_zero_iff] at h2
  exact absurd h2 (by decide)

/-- Sanity check: the generator `ι (0, 1)` over `ℤ` is not even; it sends `1` to `ι 1`. -/
theorem ι_vec_not_mem_evenOdd_zero_int :
    ι (QuadraticForm.dualProd ℤ ℤ) (0, 1) ∉ evenOdd (QuadraticForm.dualProd ℤ ℤ) 0 := by
  intro h
  have h1 : (1 : ExteriorAlgebra ℤ ℤ) ∈ exteriorParity ℤ ℤ 0 := by
    rw [exteriorParity_eq_evenOdd]
    exact Submodule.one_le.mp (one_le_evenOdd_zero _)
  have := spinAction_mem_exteriorParity_of_mem_even ℤ ℤ
    (by rw [← even_toSubmodule] at h; exact h) h1
  rw [spinAction_ι_one] at this
  exact ι_not_mem_exteriorParity_zero ℤ ℤ (by simp) this

/-- The ideal `(2)` of `ZMod 4`, a finite `ZMod 4`-module that is not free. -/
abbrev zmodFourIdeal : Submodule (ZMod 4) (ZMod 4) := Submodule.span (ZMod 4) {2}

/-- The generator `2` of `zmodFourIdeal`. -/
abbrev zmodFourGen : zmodFourIdeal := ⟨2, Submodule.mem_span_singleton_self 2⟩

/-- The inclusion of `zmodFourIdeal`, a covector with value `2` on the generator. -/
abbrev zmodFourCovector : Module.Dual (ZMod 4) zmodFourIdeal := zmodFourIdeal.subtype

/-- `zmodFourCovector m • zmodFourGen = 0` for every `m`: the covector takes values in `(2)`. -/
theorem zmodFourCovector_smul_gen (m : zmodFourIdeal) :
    zmodFourCovector m • zmodFourGen = 0 := by
  obtain ⟨m, hm⟩ := m
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
  ext
  simp only [Submodule.subtype_apply, SetLike.mk_smul_mk, smul_eq_mul, Submodule.coe_zero]
  clear hm; revert c; decide

/-- The even element `ι (0, 2) * ι (incl, 0)` acts by zero on `∧ zmodFourIdeal`. -/
theorem spinAction_zmodFour_kernel :
    spinAction (ZMod 4) zmodFourIdeal
      (ι _ (0, zmodFourGen) * ι _ (zmodFourCovector, 0)) = 0 := by
  refine LinearMap.ext fun y => ?_
  rw [map_mul, Module.End.mul_apply, spinAction_ι_dual, spinAction_ι_vec, LinearMap.zero_apply]
  induction y using CliffordAlgebra.left_induction with
  | algebraMap r => rw [contractLeft_algebraMap, mul_zero]
  | add a b ha hb => rw [map_add, mul_add, ha, hb, add_zero]
  | ι_mul y m hy =>
    rw [contractLeft_ι_mul, mul_sub, mul_smul_comm, ← smul_mul_assoc, ← map_smul,
      zmodFourCovector_smul_gen, map_zero, zero_mul, zero_sub, ← mul_assoc,
      eq_neg_of_add_eq_zero_left
        (ExteriorAlgebra.ι_add_mul_swap (R := ZMod 4) zmodFourGen m),
      neg_mul, mul_assoc]
    change -(-(ExteriorAlgebra.ι (ZMod 4) m *
      (ExteriorAlgebra.ι (ZMod 4) zmodFourGen * contractLeft zmodFourCovector y))) = 0
    rw [hy, mul_zero, neg_zero, neg_zero]

/-- The bilinear form `(v, w) ↦ w.1 v.2` on `Dual × M` for `M = zmodFourIdeal`. -/
def zmodFourPairing :
    LinearMap.BilinForm (ZMod 4) (Module.Dual (ZMod 4) zmodFourIdeal × zmodFourIdeal) :=
  ((LinearMap.applyₗ).comp (LinearMap.snd (ZMod 4) _ _)).compl₂ (LinearMap.fst (ZMod 4) _ _)

/-- Changing the form by `-zmodFourPairing` takes `dualProd` to the zero form. -/
theorem zmodFourPairing_toQuadraticMap :
    (-zmodFourPairing).toQuadraticMap = 0 - QuadraticForm.dualProd (ZMod 4) zmodFourIdeal := by
  ext v
  simp [zmodFourPairing]

/-- The alternating pairing `(v 0).1 (v 1).2 − (v 1).1 (v 0).2` on `Dual × M`. -/
def zmodFourAlt :
    (Module.Dual (ZMod 4) zmodFourIdeal × zmodFourIdeal) [⋀^Fin 2]→ₗ[ZMod 4] ZMod 4 where
  toFun v := (v 0).1 (v 1).2 - (v 1).1 (v 0).2
  map_update_add' v i x y := by fin_cases i <;> simp <;> ring
  map_update_smul' v i c x := by fin_cases i <;> simp <;> ring
  map_eq_zero_of_eq' v i j h hij := by fin_cases i <;> fin_cases j <;> simp_all

/-- `zmodFourAlt` in degree two, zero in the other degrees. -/
def zmodFourAlts :
    ∀ i, (Module.Dual (ZMod 4) zmodFourIdeal × zmodFourIdeal) [⋀^Fin i]→ₗ[ZMod 4] ZMod 4
  | 2 => zmodFourAlt
  | _ => 0

/-- The kernel element is nonzero: change the form to `0` and evaluate the degree-two part. -/
theorem zmodFour_kernel_ne_zero :
    (ι _ (0, zmodFourGen) * ι _ (zmodFourCovector, 0) :
      CliffordAlgebra (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z => ExteriorAlgebra.liftAlternating zmodFourAlts
    (changeForm zmodFourPairing_toQuadraticMap z)) h
  simp only [changeForm_ι_mul_ι, map_zero, map_sub] at h1
  rw [ExteriorAlgebra.liftAlternating_algebraMap, ExteriorAlgebra.liftAlternating_ι_mul,
    ExteriorAlgebra.liftAlternating_ι] at h1
  change zmodFourAlt ![(0, zmodFourGen), (zmodFourCovector, 0)] - _ • (0 : ZMod 4) = 0 at h1
  simp [zmodFourAlt] at h1
  revert h1; decide

/-- **`Module.Free` cannot be dropped from the injectivity of `spinAction`.** -/
theorem spinAction_zmodFour_not_injective :
    ¬ Function.Injective (spinAction (ZMod 4) zmodFourIdeal) :=
  fun hinj => zmodFour_kernel_ne_zero (hinj (by rw [spinAction_zmodFour_kernel, map_zero]))

/-- So `zmodFourIdeal` is not free (through Chevalley's theorem). -/
theorem not_free_zmodFourIdeal : ¬ Module.Free (ZMod 4) zmodFourIdeal := fun _ =>
  spinAction_zmodFour_not_injective (spinAction_bijective (ZMod 4) zmodFourIdeal).1

/-- **`Module.Free` cannot be dropped from the parity iff.** For the finite module
`zmodFourIdeal` a nonzero even element acts by zero, so it shifts parity by one without
being odd. -/
theorem evenOdd_one_iff_zmod_four_fails :
    ¬ ∀ x : CliffordAlgebra (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal),
      x ∈ evenOdd (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal) 1 ↔
        ∀ (j : ZMod 2) (y : ExteriorAlgebra (ZMod 4) zmodFourIdeal),
          y ∈ exteriorParity (ZMod 4) zmodFourIdeal j →
            spinAction (ZMod 4) zmodFourIdeal x y ∈
              exteriorParity (ZMod 4) zmodFourIdeal (j + 1) := by
  intro h
  have h1 := (h (ι _ (0, zmodFourGen) * ι _ (zmodFourCovector, 0))).mpr (fun j y _ => by
    rw [spinAction_zmodFour_kernel, LinearMap.zero_apply]; exact Submodule.zero_mem _)
  have h0 := ι_mul_ι_mem_evenOdd_zero (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)
    (0, zmodFourGen) (zmodFourCovector, 0)
  exact zmodFour_kernel_ne_zero
    ((Submodule.disjoint_def.mp (evenOdd_isCompl _).disjoint) _ h0 h1)

/-- **`Module.Free` cannot be dropped from the injectivity of `spinActionEven`.** -/
theorem spinActionEven_zmod_four_not_injective :
    ¬ Function.Injective (spinActionEven (ZMod 4) zmodFourIdeal) := by
  intro hinj
  have h : spinActionEven (ZMod 4) zmodFourIdeal
      ((even.ι (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)).bilin
        (0, zmodFourGen) (zmodFourCovector, 0)) = 0 := by
    have hk : (((even.ι (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)).bilin
        (0, zmodFourGen) (zmodFourCovector, 0) :
          even (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)) :
            CliffordAlgebra (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)) =
          ι _ (0, zmodFourGen) * ι _ (zmodFourCovector, 0) := rfl
    ext y <;> simp [spinActionEven, hk, spinAction_zmodFour_kernel]
  exact zmodFour_kernel_ne_zero (congrArg Subtype.val (hinj (h.trans (map_zero _).symm)))

end Tests

end HodgeLadder
