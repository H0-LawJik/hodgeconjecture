module

public import HodgeLadder.Weil.Algebraic
public import HodgeLadder.Hodge.DeRhamPullback
public import HodgeConjecture.Variants
public import HodgeLadder.General.EigenProducts

/-!
# T1 stated: Weil classes on abelian surfaces of Weil type

Rung `weil-surface-statement` (plan `docs/notes/2026-11-27-t1-plan.md`, node G1; decision 0013).
This file states T1 on upstream definitions and proves no case of it. T1 is the statement that
on a complex abelian surface `A` with `K = ℚ(√−d)` (`d > 0`) acting with signature `(1, 1)` on
`H^{1,0}(A)`, the Weil space `W_K ⊂ H²(A; ℚ)` consists of algebraic classes ([Weil1977];
[vanGeemen1994] §5, locators unverified).

## The statement

An abelian surface is upstream's abelian variety (`HodgeConjectureForAbelianVarieties`): an
integral smooth projective group object `[GrpObj A]` of `Over (Spec ℂ)`, here with
`dim A.left = 2`. The action of `K` is recorded by one endomorphism `f : A ⟶ A` with
`(f^*)² = −d` on `H¹(A; ℚ)`, where `f^* = Cup.pullbackCoh f 1`. The Weil space is
`weilSpace A f d`, the `−d`-eigenspace of `f^*` on `H²(A; ℚ)` (rung `weil-space`, row "Weil
space" of `docs/conventions.md`). `IsWeilTypeSurface A f d` carries three conditions:

1. `0 < d`;
2. `f^* (f^* x) = −d • x` for every `x ∈ H¹(A; ℚ)`;
3. balance: `F¹H¹_dR(A)` meets both eigenspaces `V± = ker (f^* ∓ i√d)` of the de Rham pullback
   `deRhamPullback f 1` (rung `de-rham-pullback`) in a nonzero subspace (`IsBalanced`).

On an abelian surface `F¹H¹_dR = H^{1,0}` has dimension 2 and the two intersections are
independent (`IsBalanced.exists_linearIndependent`), so condition 3 says that each eigenspace
meets `H^{1,0}` in a line: signature `(1, 1)`. Signature `(2, 0)`, `F¹H¹_dR = V₊`, fails
condition 3, as it must: there `W_K ⊗ ℂ = H^{2,0} ⊕ H^{0,2}`, so `W_K ≠ 0` and
`W_K ∩ Hdg^1 = 0`, and the inclusion is false (plan §1, §6 item 4).

`WeilClassesAlgebraicSurface` is T1 in the form `weilSpace A f d ≤ algebraicCycleClassSpan A 1`;
`WeilClassesHodgeSurface` is the form `weilSpace A f d ≤ Hdg^1(A; ℚ)`. They are equivalent
(`weilClassesAlgebraicSurface_iff_hodge`) through Lefschetz (1,1) as an equality
(`weilSpace_le_algebraic_iff_le_hodge`).

## Conventions

The eigenvalue on `H²` is `−d` (row "Weil space"); with `+d` the statement is false on every
balanced abelian surface. The root is `weilRoot d = i√d`, with `weilRoot_sq : (i√d)² = −d`
matching condition 2. The choice of root is immaterial: `IsBalanced F φ (−c) ↔ IsBalanced F φ c`
(`isBalanced_neg_iff`). The degree `d` is a natural number, cast to `ℚ` for `weilSpace` and to
`ℂ` through `ℝ` for the root; an endomorphism acting as `m√−d` is passed with `m² d`.

## Checks, and what cannot be checked at the pin

Checked here: the predicate holds in a linear-algebra model with signature `(1, 1)` and fails in
the same model with signature `(2, 0)` (`isBalanced_model_one_one`,
`not_isBalanced_model_two_zero`, on `ℂ⁴` with the complexified rational map `J ⊕ J`,
`J² = −1`); it fails for the identity on every smooth projective integral `X`
(`not_isWeilTypeSurface_id`); it forces `(deRhamPullback f 1)² = −d` and
`H¹_dR = V₊ ⊕ V₋` (`IsWeilTypeSurface.deRhamPullback_sq`, `IsWeilTypeSurface.isCompl`), and two
independent classes in `F¹H¹_dR` (`IsWeilTypeSurface.exists_linearIndependent`).

Not checkable at the pin: the pin has no abelian surface, and no smooth projective `X` is known
to have `b₁ ≠ 0` (the elliptic curve of rung `elliptic-curve-witness` exists, its `H¹` is not
computed), so no scheme is known to satisfy `IsWeilTypeSurface`, and the quantifier of
`WeilClassesAlgebraicSurface` ranges over a domain with no known element. The first instance of
the conclusion is planned as `weil-elliptic-square` (`E × E`, `f = [i] × [i]⁻¹`, `d = 1`), which
also establishes `IsWeilTypeSurface` for that pair; it instantiates `WeilClassesAlgebraicSurface`
only once `E × E` carries a `GrpObj` instance, and no rung supplies one (open rung
`weil-elliptic-square-grpobj`). The identification of
`weilSpace` with `W_K` and of `F¹H¹_dR` with `H^{1,0}` is read from the literature.

## Main definitions

* `HodgeLadder.Weil.IsBalanced`: `F` meets `ker (φ − c)` and `ker (φ + c)` nontrivially.
* `HodgeLadder.Weil.weilRoot`: `i√d`.
* `HodgeLadder.Weil.IsWeilTypeSurface`: the three conditions above.
* `HodgeLadder.Weil.WeilClassesAlgebraicSurface`: T1, algebraic form.
* `HodgeLadder.Weil.WeilClassesHodgeSurface`: T1, Hodge form.

## Main results

* `HodgeLadder.Weil.weilClassesAlgebraicSurface_iff_hodge`
* `HodgeLadder.Weil.isWeilTypeSurface_iff`: the predicate unfolded, with `i√d` written out.
* `HodgeLadder.Weil.IsBalanced.finrank_inf_eq_one`: with `finrank F = 2`, balance gives two
  lines, signature `(1, 1)`.
* `HodgeLadder.Weil.IsWeilTypeSurface.deRhamPullback_sq`, `IsWeilTypeSurface.isCompl`,
  `IsWeilTypeSurface.exists_linearIndependent`, `not_isWeilTypeSurface_id`
* `HodgeLadder.Weil.isBalanced_model_one_one`, `not_isBalanced_model_two_zero`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLadder.Weil

/-- **Balance.** For a `ℂ`-linear `φ` and `c : ℂ`, the subspace `F` meets both
`ker (φ − c • id)` and `ker (φ + c • id)` in a nonzero subspace. At `F = F¹H¹_dR(A)`,
`φ = deRhamPullback f 1` and `c = i√d` this is signature `(1, 1)` (module docstring). -/
def IsBalanced {V : Type*} [AddCommGroup V] [Module ℂ V] (F : Submodule ℂ V)
    (φ : V →ₗ[ℂ] V) (c : ℂ) : Prop :=
  F ⊓ LinearMap.ker (φ - c • LinearMap.id) ≠ ⊥ ∧ F ⊓ LinearMap.ker (φ + c • LinearMap.id) ≠ ⊥

/-- **The root** `i√d` of `−d` (`weilRoot_sq`), the eigenvalue of the de Rham pullback on
`V₊`. -/
def weilRoot (d : ℕ) : ℂ := Complex.I * (Real.sqrt d : ℂ)

/-- **Endomorphism of Weil type on a surface.** For `f : A ⟶ A` and `d : ℕ`: `0 < d`,
`(f^*)² = −d` on `H¹(A; ℚ)` with `f^* = Cup.pullbackCoh f 1`, and balance of
`F¹H¹_dR(A)` against the eigenspaces `ker (deRhamPullback f 1 ∓ i√d)`. The balance condition
excludes signature `(2, 0)`, where T1 fails. -/
def IsWeilTypeSurface (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom]
    [IsProjective A.hom] (f : A ⟶ A) (d : ℕ) : Prop :=
  0 < d ∧ (∀ x : H^1(A; ℚ), Cup.pullbackCoh f 1 (Cup.pullbackCoh f 1 x) = -(d : ℚ) • x) ∧
    IsBalanced (F^1 H_dR^1(A)) (deRhamPullback f 1) (weilRoot d)

/-- **T1, algebraic form.** For every abelian surface `A` (upstream's integral smooth projective
group object over `Spec ℂ`, with `dim A.left = 2`) and every endomorphism `f` of Weil type for
`d`, the Weil space `weilSpace A f d` (the `−d`-eigenspace of `f^*` on `H²(A; ℚ)`) lies in the
span of algebraic classes. Here `f` is any morphism `A ⟶ A` over `Spec ℂ`; by rigidity
([Mumford1970] §4, locator unverified) it is a homomorphism followed by a translation, and
translations act trivially on cohomology, so this is the statement for homomorphisms. With `f` a
homomorphism, `(f^*)² = −d` on `H¹` is `f² = [−d]` in `End(A)`, by faithfulness of the rational
representation. Open. -/
def WeilClassesAlgebraicSurface : Prop :=
  ∀ (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] [GrpObj A],
    dim A.left = 2 → ∀ (f : A ⟶ A) (d : ℕ), IsWeilTypeSurface A f d →
      weilSpace A f d ≤ algebraicCycleClassSpan A 1

/-- **T1, Hodge form.** The hypotheses of `WeilClassesAlgebraicSurface` with conclusion
`weilSpace A f d ≤ Hdg^1(A; ℚ)`. Equivalent to the algebraic form
(`weilClassesAlgebraicSurface_iff_hodge`). Open. -/
def WeilClassesHodgeSurface : Prop :=
  ∀ (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] [GrpObj A],
    dim A.left = 2 → ∀ (f : A ⟶ A) (d : ℕ), IsWeilTypeSurface A f d →
      weilSpace A f d ≤ Hdg^1(A; ℚ)

/-- The two forms of T1 are equivalent: for each `A`, `f`, `d`, the inclusions in
`algebraicCycleClassSpan A 1` and in `Hdg^1(A; ℚ)` agree by Lefschetz (1,1) as an equality
(`weilSpace_le_algebraic_iff_le_hodge`). -/
theorem weilClassesAlgebraicSurface_iff_hodge :
    WeilClassesAlgebraicSurface ↔ WeilClassesHodgeSurface := by
  constructor
  · intro h A _ _ _ _ hA f d hW
    exact (weilSpace_le_algebraic_iff_le_hodge A f d).mp (h A hA f d hW)
  · intro h A _ _ _ _ hA f d hW
    exact (weilSpace_le_algebraic_iff_le_hodge A f d).mpr (h A hA f d hW)

/-- `IsWeilTypeSurface` unfolded: the root written as `Complex.I * √d` and balance as the two
intersections with `F¹H¹_dR(A)`. Holds by `Iff.rfl`. -/
theorem isWeilTypeSurface_iff (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom]
    [IsProjective A.hom] (f : A ⟶ A) (d : ℕ) :
    IsWeilTypeSurface A f d ↔
      0 < d ∧ (∀ x : H^1(A; ℚ), Cup.pullbackCoh f 1 (Cup.pullbackCoh f 1 x) = -(d : ℚ) • x) ∧
        F^1 H_dR^1(A) ⊓ LinearMap.ker (deRhamPullback f 1 -
            (Complex.I * (Real.sqrt d : ℂ)) • LinearMap.id) ≠ ⊥ ∧
        F^1 H_dR^1(A) ⊓ LinearMap.ker (deRhamPullback f 1 +
            (Complex.I * (Real.sqrt d : ℂ)) • LinearMap.id) ≠ ⊥ :=
  Iff.rfl

section Checks

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **Root invariance.** Balance at `−c` is balance at `c`: the two conditions swap. So the
choice of `i√d` against `−i√d` does not matter. -/
theorem isBalanced_neg_iff (F : Submodule ℂ V) (φ : V →ₗ[ℂ] V) (c : ℂ) :
    IsBalanced F φ (-c) ↔ IsBalanced F φ c := by
  simp only [IsBalanced, neg_smul, sub_neg_eq_add, ← sub_eq_add_neg]
  exact And.comm

/-- Balance with `c ≠ 0` gives `a, b ∈ F` with `φ a = c • a`, `φ b = −c • b` and `a, b`
linearly independent. So balance needs `F` of dimension at least 2. -/
theorem IsBalanced.exists_linearIndependent {F : Submodule ℂ V} {φ : V →ₗ[ℂ] V} {c : ℂ}
    (h : IsBalanced F φ c) (hc : c ≠ 0) :
    ∃ a b : V, a ∈ F ∧ b ∈ F ∧ φ a = c • a ∧ φ b = -c • b ∧ LinearIndependent ℂ ![a, b] := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.1
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.2
  rw [Submodule.mem_inf] at ha hb
  have ha' : φ a = c • a := by
    have := LinearMap.mem_ker.mp ha.2
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at this
  have hb' : φ b = -c • b := by
    have := LinearMap.mem_ker.mp hb.2
    rwa [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg,
      ← neg_smul] at this
  refine ⟨a, b, ha.1, hb.1, ha', hb', ?_⟩
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hsa : s • a ∈ LinearMap.ker (φ - c • LinearMap.id) := Submodule.smul_mem _ s ha.2
  have htb : -(t • b) ∈ LinearMap.ker (φ + c • LinearMap.id) :=
    Submodule.neg_mem _ (Submodule.smul_mem _ t hb.2)
  have heq : s • a = -(t • b) := eq_neg_of_add_eq_zero_left hst
  have h0 : s • a = 0 :=
    Submodule.disjoint_def.mp (disjoint_ker_sub_smul_ker_add_smul φ hc two_ne_zero) _ hsa (heq ▸ htb)
  have h1 : t • b = 0 := by rw [h0, eq_comm, neg_eq_zero] at heq; exact heq
  exact ⟨(smul_eq_zero.mp h0).resolve_right ha0, (smul_eq_zero.mp h1).resolve_right hb0⟩

/-- With `finrank F = 2` and `c ≠ 0`, balance is signature `(1, 1)`: each intersection is a
line. On an abelian surface `F¹H¹_dR` has rank 2 (literature), so `IsWeilTypeSurface` is the
signature-`(1, 1)` condition. -/
theorem IsBalanced.finrank_inf_eq_one {F : Submodule ℂ V} {φ : V →ₗ[ℂ] V} {c : ℂ}
    [FiniteDimensional ℂ F] (h : IsBalanced F φ c) (hc : c ≠ 0)
    (hF : Module.finrank ℂ F = 2) :
    Module.finrank ℂ (F ⊓ LinearMap.ker (φ - c • LinearMap.id) : Submodule ℂ V) = 1 ∧
    Module.finrank ℂ (F ⊓ LinearMap.ker (φ + c • LinearMap.id) : Submodule ℂ V) = 1 := by
  set P := F ⊓ LinearMap.ker (φ - c • LinearMap.id)
  set Q := F ⊓ LinearMap.ker (φ + c • LinearMap.id)
  have hPF : P ≤ F := inf_le_left
  have hQF : Q ≤ F := inf_le_left
  have : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le hPF
  have : FiniteDimensional ℂ Q := Submodule.finiteDimensional_of_le hQF
  have hdisj : Disjoint P Q :=
    (disjoint_ker_sub_smul_ker_add_smul φ hc two_ne_zero).mono inf_le_right inf_le_right
  have hP : 0 < Module.finrank ℂ P :=
    Nat.pos_of_ne_zero fun h0 => h.1 (Submodule.finrank_eq_zero.mp h0)
  have hQ : 0 < Module.finrank ℂ Q :=
    Nat.pos_of_ne_zero fun h0 => h.2 (Submodule.finrank_eq_zero.mp h0)
  have hsum : Module.finrank ℂ P + Module.finrank ℂ Q ≤ Module.finrank ℂ F := by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq, hdisj.eq_bot, finrank_bot, add_zero]
    exact Submodule.finrank_mono (sup_le hPF hQF)
  omega

/-- The identity is not balanced at any `c ≠ 1`: `ker (id − c • id) = ⊥`. -/
theorem not_isBalanced_id (F : Submodule ℂ V) {c : ℂ} (hc : c ≠ 1) :
    ¬ IsBalanced F LinearMap.id c := by
  intro h
  apply h.1
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  have hv' := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hv).2
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv'
  have h1 : (1 - c) • v = 0 := by rw [sub_smul, one_smul]; exact hv'
  exact (smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (Ne.symm hc))

/-- **Sign check.** `(i√d)² = −d`, the eigenvalue of `(f^*)²` in condition 2. -/
theorem weilRoot_sq (d : ℕ) : weilRoot d ^ 2 = -(d : ℂ) := by
  rw [weilRoot, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring

/-- `i√d ≠ 0` for `d > 0`. -/
theorem weilRoot_ne_zero {d : ℕ} (hd : 0 < d) : weilRoot d ≠ 0 :=
  mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd)))

/-- `i√d` is purely imaginary. -/
theorem weilRoot_re (d : ℕ) : (weilRoot d).re = 0 := by
  simp [weilRoot]

/-- `i√d ≠ 1`, from the real parts. -/
theorem weilRoot_ne_one (d : ℕ) : weilRoot d ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [weilRoot_re, Complex.one_re] at this
  exact zero_ne_one this

/-- `i√1 = i`. -/
theorem weilRoot_one : weilRoot 1 = Complex.I := by
  simp [weilRoot]

/-- An endomorphism of Weil type gives two linearly independent classes in `F¹H¹_dR(A)`,
eigenvectors of `deRhamPullback f 1` for `i√d` and `−i√d`. So `IsWeilTypeSurface` fails whenever
`F¹H¹_dR(A)` has dimension below 2. -/
theorem IsWeilTypeSurface.exists_linearIndependent {A : Over (Spec ↧ℂ)} [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] {f : A ⟶ A} {d : ℕ} (h : IsWeilTypeSurface A f d) :
    ∃ a b : H_dR^1(A), a ∈ F^1 H_dR^1(A) ∧ b ∈ F^1 H_dR^1(A) ∧
      deRhamPullback f 1 a = weilRoot d • a ∧ deRhamPullback f 1 b = -weilRoot d • b ∧
      LinearIndependent ℂ ![a, b] :=
  h.2.2.exists_linearIndependent (weilRoot_ne_zero h.1)


/-- **Coherence of conditions 2 and 3.** The rational condition `(f^*)² = −d` on `H¹(A; ℚ)` gives
`(deRhamPullback f 1)² = −d` on `H¹_dR(A)`, since rational classes span (`deRhamPullback` is
the `ℂ`-linear extension of `f^*`). The eigenvalues in condition 3 are its two square roots. -/
theorem IsWeilTypeSurface.deRhamPullback_sq {A : Over (Spec ↧ℂ)} [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] {f : A ⟶ A} {d : ℕ} (h : IsWeilTypeSurface A f d)
    (x : H_dR^1(A)) :
    deRhamPullback f 1 (deRhamPullback f 1 x) = -(d : ℂ) • x := by
  have key : deRhamPullback f 1 ∘ₗ deRhamPullback f 1 = (-(d : ℂ)) • LinearMap.id := by
    refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat A 1) ?_
    rintro _ ⟨α, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      deRhamPullback_fieldToDeRhamCohomology, deRhamPullback_fieldToDeRhamCohomology, h.2.1 α,
      fieldToDeRhamCohomology_smul]
    simp only [neg_smul, Nat.cast_smul_eq_nsmul]
  exact LinearMap.congr_fun key x

/-- For an endomorphism of Weil type, `H¹_dR(A) = V₊ ⊕ V₋` with
`V± = ker (deRhamPullback f 1 ∓ i√d)`,
by `isCompl_ker_sub_smul_ker_add_smul` (rung `weil-eigen-algebra`). -/
theorem IsWeilTypeSurface.isCompl {A : Over (Spec ↧ℂ)} [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] {f : A ⟶ A} {d : ℕ} (h : IsWeilTypeSurface A f d) :
    IsCompl (LinearMap.ker (deRhamPullback f 1 - weilRoot d • LinearMap.id))
      (LinearMap.ker (deRhamPullback f 1 + weilRoot d • LinearMap.id)) :=
  isCompl_ker_sub_smul_ker_add_smul _ _ (weilRoot_ne_zero h.1) two_ne_zero fun x => by
    rw [h.deRhamPullback_sq, ← sq, weilRoot_sq]

/-- **Vacuity guard.** The identity is of Weil type for no `d`, on every smooth projective
integral `X`: `deRhamPullback (𝟙 X) 1 = id` and `i√d ≠ 1`. -/
theorem not_isWeilTypeSurface_id (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (d : ℕ) : ¬ IsWeilTypeSurface X (𝟙 X) d := by
  intro h
  have hb := h.2.2
  rw [deRhamPullback_id] at hb
  exact not_isBalanced_id _ (weilRoot_ne_one d) hb

/-- **Linear-algebra model.** The map `J ⊕ J` on `ℂ⁴`, `J (x, y) = (−y, x)`, the
complexification of a rational map with square `−1` (`modelEndo_modelEndo`). Its `i`-eigenspace
contains `(1, −i, 0, 0)` and `(0, 0, 1, −i)`; its `−i`-eigenspace contains `(0, 0, 1, i)`. -/
def modelEndo : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := ![-(v 1), v 0, -(v 3), v 2]
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp

/-- In the model, `(J ⊕ J)² = −1`, condition 2 with `d = 1`. -/
theorem modelEndo_modelEndo (v : Fin 4 → ℂ) : modelEndo (modelEndo v) = -((1 : ℕ) : ℂ) • v := by
  funext i
  fin_cases i <;> simp [modelEndo]

/-- **Signature (1, 1) in the model.** `F = span {(1, −i, 0, 0), (0, 0, 1, i)}` meets both
eigenspaces of `J ⊕ J`: balance holds, so condition 3 is satisfiable. -/
theorem isBalanced_model_one_one :
    IsBalanced (Submodule.span ℂ {![1, -Complex.I, 0, 0], ![0, 0, 1, Complex.I]}) modelEndo
      (weilRoot 1) := by
  rw [weilRoot_one]
  constructor
  · rw [Submodule.ne_bot_iff]
    refine ⟨![1, -Complex.I, 0, 0], Submodule.mem_inf.mpr ⟨Submodule.subset_span (by simp), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]
      funext i
      fin_cases i <;> simp [modelEndo]
    · intro h
      have := congrFun h 0
      simp at this
  · rw [Submodule.ne_bot_iff]
    refine ⟨![0, 0, 1, Complex.I], Submodule.mem_inf.mpr ⟨Submodule.subset_span (by simp), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]
      funext i
      fin_cases i <;> simp [modelEndo]
    · intro h
      have := congrFun h 2
      simp at this

/-- **Signature (2, 0) in the model.** `F = span {(1, −i, 0, 0), (0, 0, 1, −i)}` lies in the
`i`-eigenspace and meets the `−i`-eigenspace in `0`: balance fails, as it must in the
counterexample of plan §1. -/
theorem not_isBalanced_model_two_zero :
    ¬ IsBalanced (Submodule.span ℂ {![1, -Complex.I, 0, 0], ![0, 0, 1, -Complex.I]}) modelEndo
      (weilRoot 1) := by
  rw [weilRoot_one]
  intro h
  apply h.2
  have hle : Submodule.span ℂ {![1, -Complex.I, 0, 0], ![0, 0, 1, -Complex.I]} ≤
      LinearMap.ker (modelEndo - Complex.I • LinearMap.id) := by
    rw [Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · show _ = _
      funext i
      fin_cases i <;> simp [modelEndo]
    · show _ = _
      funext i
      fin_cases i <;> simp [modelEndo]
  exact eq_bot_iff.mpr fun v hv => (Submodule.disjoint_def.mp
    (disjoint_ker_sub_smul_ker_add_smul modelEndo Complex.I_ne_zero two_ne_zero) v
    (hle (Submodule.mem_inf.mp hv).1) (Submodule.mem_inf.mp hv).2)

end Checks

end HodgeLadder.Weil
