module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.QuadraticForm.Dual

/-!
# The spin module of the split form: the Clifford action on the exterior algebra

Let `M` be a module over a commutative ring `R` and `V = Module.Dual R M × M` with the split
quadratic form `QuadraticForm.dualProd R M`, `Q (f, x) = f x`. The pair `(f, x)` acts on the
exterior algebra `∧M = ExteriorAlgebra R M` by contraction with `f` plus left multiplication by
`ι x`. This operator squares to `Q (f, x)` times the identity, with sign `+` and no factor `2`,
so the universal property of the Clifford algebra gives an algebra homomorphism
`CliffordAlgebra (dualProd R M) →ₐ[R] Module.End R (ExteriorAlgebra R M)`. For a torus with
`M = H¹(A, ℚ)` this is the action of `Cl(H ⊕ H^∨)` on `H*(A, ℚ) = ∧*H` used in Markman's
construction (research note 2026-11-24, §1; rung `clifford-exterior-spin`).

The action respects parity: an element of `evenOdd (dualProd R M) i` maps the parity-`j` part
of `∧M` (the span of the `⋀[R]^k M` with `k ≡ j mod 2`) into the parity-`(i + j)` part.

Mathlib has `CliffordAlgebra.contractLeft` and the `ZMod 2` grading `CliffordAlgebra.evenOdd`;
it has no Clifford action of the split form on the exterior algebra under another name
(searched `Mathlib/LinearAlgebra/CliffordAlgebra/` and `Mathlib/LinearAlgebra/ExteriorAlgebra/`
at the pin). Chevalley's theorem, that the action is an isomorphism for `M` finite free, is a
separate rung (`clifford-exterior-chevalley`).

## Main definitions

* `HodgeLadder.exteriorParity`: the parity-`j` part of the exterior algebra.
* `HodgeLadder.spinGen`: the operator `contractLeft f + ι x * ·` attached to `(f, x)`.
* `HodgeLadder.spinAction`: the algebra homomorphism from the Clifford algebra of the split form
  to the endomorphisms of the exterior algebra.

## Main results

* `HodgeLadder.contractLeft_mem_range_ι_pow`: contraction lowers the filtration degree by one.
* `HodgeLadder.contractLeft_mem_evenOdd`: contraction is odd.
* `HodgeLadder.exteriorParity_eq_evenOdd`: the parity parts are the `evenOdd` parts of
  `ExteriorAlgebra R M = CliffordAlgebra 0`.
* `HodgeLadder.spinGen_mul_self`: `(spinGen v)² = Q v`.
* `HodgeLadder.spinAction_ι`, `HodgeLadder.spinAction_ι_apply`, `HodgeLadder.spinAction_ι_dual`,
  `HodgeLadder.spinAction_ι_vec`: values on generators.
* `HodgeLadder.spinAction_mem_evenOdd`, `HodgeLadder.spinAction_mem_exteriorParity`: parity.
-/

@[expose] public section

namespace HodgeLadder

open CliffordAlgebra

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- **Contraction lowers degree.** For any quadratic form `Q`, contraction by `d` maps the
`(n + 1)`-st power of the range of `ι Q` into the `n`-th power. For `Q = 0` this says
`contractLeft d` maps `⋀[R]^(n+1) M` into `⋀[R]^n M`. -/
theorem contractLeft_mem_range_ι_pow {Q : QuadraticForm R M} (d : Module.Dual R M) (n : ℕ)
    {y : CliffordAlgebra Q} (hy : y ∈ LinearMap.range (ι Q) ^ (n + 1)) :
    contractLeft d y ∈ LinearMap.range (ι Q) ^ n := by
  induction n generalizing y with
  | zero =>
    rw [zero_add, pow_one] at hy
    obtain ⟨m, rfl⟩ := hy
    rw [contractLeft_ι, pow_zero]
    exact Submodule.algebraMap_mem _
  | succ n ih =>
    rw [pow_succ'] at hy
    induction hy using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      obtain ⟨m, rfl⟩ := ha
      rw [contractLeft_ι_mul]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) ?_
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) (ih hb)
    | add x _ y _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- **Contraction is odd.** For any quadratic form `Q`, contraction by `d` maps the parity-`i`
part `evenOdd Q i` into the parity-`(i + 1)` part. -/
theorem contractLeft_mem_evenOdd {Q : QuadraticForm R M} (d : Module.Dual R M) (i : ZMod 2)
    {y : CliffordAlgebra Q} (hy : y ∈ evenOdd Q i) :
    contractLeft d y ∈ evenOdd Q (i + 1) := by
  induction hy using Submodule.iSup_induction' with
  | mem k y hy =>
    obtain ⟨n, hn⟩ := k
    cases n with
    | zero =>
      rw [pow_zero] at hy
      obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hy
      rw [contractLeft_algebraMap]
      exact Submodule.zero_mem _
    | succ n =>
      refine Submodule.mem_iSup_of_mem ⟨n, ?_⟩ (contractLeft_mem_range_ι_pow R M d n hy)
      subst hn
      push_cast
      rw [add_assoc, (by decide : (1 : ZMod 2) + 1 = 0), add_zero]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- The parity-`j` part of the exterior algebra: the supremum of the exterior powers
`⋀[R]^k M` over the `k : ℕ` with `k ≡ j mod 2`. `exteriorParity R M 0` is the even part and
`exteriorParity R M 1` the odd part. -/
def exteriorParity (j : ZMod 2) : Submodule R (ExteriorAlgebra R M) :=
  ⨆ (k : ℕ) (_ : (k : ZMod 2) = j), ⋀[R]^k M

/-- The parity parts of `ExteriorAlgebra R M = CliffordAlgebra 0` are its `evenOdd` parts. -/
theorem exteriorParity_eq_evenOdd (j : ZMod 2) :
    exteriorParity R M j = evenOdd (0 : QuadraticForm R M) j := by
  rw [exteriorParity, evenOdd, iSup_subtype']

/-- The operator attached to `(f, x) : Module.Dual R M × M` on the exterior algebra:
`y ↦ contractLeft f y + ι x * y`, contraction by `f` plus left wedge with `x`. -/
def spinGen : Module.Dual R M × M →ₗ[R] Module.End R (ExteriorAlgebra R M) :=
  (contractLeft (Q := (0 : QuadraticForm R M))).comp (LinearMap.fst R _ _) +
    (LinearMap.mul R (ExteriorAlgebra R M)).comp ((ExteriorAlgebra.ι R).comp (LinearMap.snd R _ _))

/-- The value of `spinGen` on an element. -/
@[simp]
theorem spinGen_apply (v : Module.Dual R M × M) (y : ExteriorAlgebra R M) :
    spinGen R M v y = contractLeft v.1 y + ExteriorAlgebra.ι R v.2 * y := rfl

/-- **The generator squares to the split form.** `(spinGen (f, x))² = f x • id`, that is
`algebraMap R _ (QuadraticForm.dualProd R M (f, x))`, with sign `+`. -/
theorem spinGen_mul_self (v : Module.Dual R M × M) :
    spinGen R M v * spinGen R M v = algebraMap R _ (QuadraticForm.dualProd R M v) := by
  ext y
  rw [Module.End.mul_apply, spinGen_apply, spinGen_apply, map_add, contractLeft_contractLeft,
    contractLeft_ι_mul, mul_add, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, add_zero,
    zero_add, sub_add_cancel, Module.algebraMap_end_apply, QuadraticForm.dualProd_apply]

/-- **The spin action.** The algebra homomorphism from the Clifford algebra of the split form
on `Module.Dual R M × M` to the endomorphisms of the exterior algebra of `M`, sending `ι (f, x)`
to contraction by `f` plus left wedge with `x`. -/
def spinAction :
    CliffordAlgebra (QuadraticForm.dualProd R M) →ₐ[R] Module.End R (ExteriorAlgebra R M) :=
  CliffordAlgebra.lift _ ⟨spinGen R M, spinGen_mul_self R M⟩

/-- `spinAction` on a generator is `spinGen`. -/
@[simp]
theorem spinAction_ι (v : Module.Dual R M × M) :
    spinAction R M (ι _ v) = spinGen R M v :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- `spinAction (ι (f, x))` is contraction by `f` plus left wedge with `x`. -/
theorem spinAction_ι_apply (v : Module.Dual R M × M) (y : ExteriorAlgebra R M) :
    spinAction R M (ι _ v) y = contractLeft v.1 y + ExteriorAlgebra.ι R v.2 * y := by
  simp

/-- A covector `f` acts by contraction. -/
@[simp]
theorem spinAction_ι_dual (f : Module.Dual R M) (y : ExteriorAlgebra R M) :
    spinAction R M (ι _ (f, 0)) y = contractLeft f y := by
  simp

/-- A vector `x` acts by left wedge with `x`. -/
@[simp]
theorem spinAction_ι_vec (x : M) (y : ExteriorAlgebra R M) :
    spinAction R M (ι _ (0, x)) y = ExteriorAlgebra.ι R x * y := by
  simp

/-- Sanity check: `ι (f, x)` sends the unit `1 ∈ ⋀⁰` to `ι x ∈ ⋀¹`. -/
theorem spinAction_ι_one (v : Module.Dual R M × M) :
    spinAction R M (ι _ v) 1 = ExteriorAlgebra.ι R v.2 := by
  rw [spinAction_ι_apply, contractLeft_one, mul_one, zero_add]

/-- Sanity check: a covector `f` sends `ι m ∈ ⋀¹` to the scalar `f m ∈ ⋀⁰`. -/
theorem spinAction_ι_dual_ι (f : Module.Dual R M) (m : M) :
    spinAction R M (ι _ (f, 0)) (ExteriorAlgebra.ι R m) = algebraMap R _ (f m) := by
  rw [spinAction_ι_dual, contractLeft_ι]

/-- A generator of the Clifford algebra is odd: it maps the parity-`j` part of the exterior
algebra into the parity-`(1 + j)` part. -/
theorem spinAction_ι_mem_evenOdd (v : Module.Dual R M × M) {j : ZMod 2}
    {y : ExteriorAlgebra R M} (hy : y ∈ evenOdd (0 : QuadraticForm R M) j) :
    spinAction R M (ι _ v) y ∈ evenOdd (0 : QuadraticForm R M) (1 + j) := by
  rw [spinAction_ι_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [add_comm]; exact contractLeft_mem_evenOdd R M v.1 j hy
  · exact SetLike.mul_mem_graded (ι_mem_evenOdd_one _ v.2) hy

/-- **The spin action respects parity** (`evenOdd` form). An element of
`evenOdd (dualProd R M) i` maps `evenOdd 0 j` of `ExteriorAlgebra R M = CliffordAlgebra 0` into
`evenOdd 0 (i + j)`. -/
theorem spinAction_mem_evenOdd {i j : ZMod 2} {x : CliffordAlgebra (QuadraticForm.dualProd R M)}
    (hx : x ∈ evenOdd (QuadraticForm.dualProd R M) i) {y : ExteriorAlgebra R M}
    (hy : y ∈ evenOdd (0 : QuadraticForm R M) j) :
    spinAction R M x y ∈ evenOdd (0 : QuadraticForm R M) (i + j) := by
  have key : ∀ n : ℕ, ∀ x ∈ LinearMap.range (ι (QuadraticForm.dualProd R M)) ^ n,
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ evenOdd (0 : QuadraticForm R M) j →
        spinAction R M x y ∈ evenOdd (0 : QuadraticForm R M) (n + j) := by
    intro n
    induction n with
    | zero =>
      intro x hx j y hy
      rw [pow_zero] at hx
      obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
      rw [AlgHom.commutes, Module.algebraMap_end_apply, Nat.cast_zero, zero_add]
      exact Submodule.smul_mem _ _ hy
    | succ n ih =>
      intro x hx j y hy
      rw [pow_succ'] at hx
      induction hx using Submodule.mul_induction_on' with
      | mem_mul_mem a ha b hb =>
        obtain ⟨v, rfl⟩ := ha
        rw [map_mul, Module.End.mul_apply]
        have h := spinAction_ι_mem_evenOdd R M v (ih b hb j y hy)
        convert h using 2
        push_cast
        ring
      | add x _ y' _ hx hy' =>
        rw [map_add, LinearMap.add_apply]
        exact Submodule.add_mem _ hx hy'
  induction hx using Submodule.iSup_induction' with
  | mem k x hx =>
    obtain ⟨n, rfl⟩ := k
    exact key n x hx j y hy
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add x x' _ _ hx hx' => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hx'

/-- **The spin action respects parity.** An element of `evenOdd (dualProd R M) i` maps the
parity-`j` part of the exterior algebra (the span of the `⋀[R]^k M` with `k ≡ j mod 2`) into the
parity-`(i + j)` part. -/
theorem spinAction_mem_exteriorParity {i j : ZMod 2}
    {x : CliffordAlgebra (QuadraticForm.dualProd R M)}
    (hx : x ∈ evenOdd (QuadraticForm.dualProd R M) i) {y : ExteriorAlgebra R M}
    (hy : y ∈ exteriorParity R M j) :
    spinAction R M x y ∈ exteriorParity R M (i + j) := by
  rw [exteriorParity_eq_evenOdd] at hy ⊢
  exact spinAction_mem_evenOdd R M hx hy

end HodgeLadder
