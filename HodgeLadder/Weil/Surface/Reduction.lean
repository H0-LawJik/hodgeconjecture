module

public import HodgeLadder.Weil.Surface.Statement
public import HodgeLadder.Hodge.CupHodgeFiltration

/-!
# T1 reduced to the rank and the span of `H_dR^*` on a surface

Rung `weil-surface-reduction` (plan `docs/notes/2026-11-27-t1-plan.md`, node B). For a smooth
projective integral `A` over `Spec ℂ` and an endomorphism `f` of Weil type for `d`
(`IsWeilTypeSurface A f d`, rung `weil-surface-statement`), two statements on upstream
definitions,

1. `finrank ℂ H_dR^1(A) = 4`, and
2. `H_dR^2(A)` is spanned over `ℂ` by the products `deRhamCup x y` of classes `x, y ∈ H_dR^1(A)`,

give `weilSpace A f d ≤ Hdg^1(A; ℚ)` (`weilSpace_le_hodge_of_rank_span`), hence
`weilSpace A f d ≤ algebraicCycleClassSpan A 1` by Lefschetz (1,1) as an equality
(`weilSpace_le_algebraic_of_rank_span`). This is a conditional theorem: the two statements are
hypotheses, checked for no scheme here. No dimension hypothesis on `A` is used; the rank and span
hypotheses carry what the surface case needs. As a consequence, T1 in the form
`WeilClassesAlgebraicSurface` follows from the two statements for every abelian surface
(`weilClassesAlgebraicSurface_of_rank_span`).

## Vacuity

At the pin no smooth projective `X` has a checked `b₁ ≠ 0` (the elliptic curve of rung
`elliptic-curve-witness` has `b₁ = 2` in the literature; its `H¹` is not computed), so
hypothesis 1 holds for no known scheme and both reduction theorems apply to none. Their planned
first instance is `E × E` with `f = [i] × [i]⁻¹` and `d = 1`: rank and span from rung
`elliptic-square-cohomology`, the Weil-type condition and the conclusion in rung
`weil-elliptic-square`. The hypothesis of `weilClassesAlgebraicSurface_of_rank_span` quantifies
over every abelian surface; that instance leaves it open, and rung `weil-surface` discharges it
through `abelian-surface-uniformization`.

## The argument

The linear algebra sits in `ker_sub_smul_le_of_isBalanced`, stated for abstract `ℂ`-vector
spaces so that the kernel checks it once on generic types. Write `T = deRhamPullback f 1`,
`s = i√d`, `V± = ker (T ∓ s)`:

* `T² = s² = −d` (`IsWeilTypeSurface.deRhamPullback_sq`, `weilRoot_sq`), so
  `H_dR^1 = V₊ ⊕ V₋` (`isCompl_ker_sub_smul_ker_add_smul`);
* conjugation `deRhamConj` commutes with `T` (`deRhamPullback_conj`), is injective
  (`deRhamConj_deRhamConj`, in `HodgeLadder.Hodge.DeRhamPullback`) and sends `s` to `−s`, so
  it maps `V₊` into `V₋` and back; with rank 4, both have rank 2;
* by balance each `V±` contains a nonzero `a± ∈ F¹H¹_dR`; complete it to a basis `{a±, b±}`;
* the `−d`-eigenspace of `deRhamPullback f 2` lies in the span of the products of eigenvectors
  whose eigenvalues multiply to `s² = −d` (`ker_sub_smul_le_span_of_eigen`, with the span
  hypothesis through `span_range_prod_eq_top_of_span`); since `s · (−s) = d ≠ −d`, these are
  the products inside `V₊` and inside `V₋`;
* inside `V±`, `x ∪ x = 0` (`deRhamCup_self_of_odd`), and `a± ∪ b±`, `b± ∪ a±` lie in
  `F¹H²_dR` (`deRhamCup_mem_hodgeFiltration` with `F⁰ = ⊤`), so every such product does;
* a rational `w` in the Weil space has `ι w` in that eigenspace (`deRhamPullback` extends
  `f^*`), so `ι w ∈ F¹H²_dR` and `w ∈ Hdg^1(A; ℚ)` (`mem_hodgeClasses_of_mem_hodgeFiltration`).

Rank 4 is used: in rank 6 with `F¹ ∩ V₋` a line, `V₋` holds a plane meeting `F¹` in 0, the
product of its basis lies in the `−d`-eigenspace, and on an abelian threefold of signature
`(2, 1)` it has type `(0, 2)`, so the inclusion is false there. Without the conjugation
hypotheses the eigenspaces can have ranks 3 and 1, and the conclusion fails in a model of that
shape (`not_ker_model31WedgeEndo_le`; red team, `docs/sketches/weil-surface-reduction.redteam.md`).

## Checks

`ker_sub_smul_le_of_isBalanced` is checked non-vacuous on a model: `V = ℂ⁴`,
`W = ∧²ℂ⁴ = ℂ⁶`, `T = modelEndo`, `s = i`, `J` coordinatewise conjugation, `F` the
signature-`(1, 1)` plane of `isBalanced_model_one_one`, `G = F ∧ V`. The conclusion holds
(`ker_modelWedgeEndo_le_one_one`), the eigenspace is neither `⊥` nor `⊤` and `G ≠ ⊤`
(`ker_modelWedgeEndo_ne_bot`, `ker_modelWedgeEndo_ne_top`, `modelWedgeHodgeOneOne_ne_top`).
With the signature-`(2, 0)` plane every hypothesis except balance holds and the conclusion fails
(`not_ker_modelWedgeEndo_le_two_zero`). With `T = diag (i, i, i, −i)`, eigenspaces of rank 3
and 1, every hypothesis except the two on `J` holds and the conclusion fails
(`not_ker_model31WedgeEndo_le`).

## Conventions

The eigenvalue on `H²` is `−d` (row "Weil space" of `docs/conventions.md`), entering as
`s * s` with `s = weilRoot d` and `weilRoot_sq : (i√d)² = −d`. The only other sign is the
graded-commutativity sign `(−1)^(1·1) = −1` on `H¹ × H¹`, Mathlib's Koszul sign, used through
`deRhamCup_self_of_odd`. No scalar enters: every identity used is exact.

## Main results

* `HodgeLadder.Weil.ker_sub_smul_le_of_isBalanced`: the linear-algebra step, on abstract spaces.
* `HodgeLadder.Weil.weilSpace_le_hodge_of_rank_span`
* `HodgeLadder.Weil.weilSpace_le_algebraic_of_rank_span`
* `HodgeLadder.Weil.weilClassesAlgebraicSurface_of_rank_span`
* `HodgeLadder.Weil.ker_modelWedgeEndo_le_one_one`, `ker_modelWedgeEndo_ne_bot`,
  `ker_modelWedgeEndo_ne_top`, `modelWedgeHodgeOneOne_ne_top`,
  `not_ker_modelWedgeEndo_le_two_zero`: the model checks.
* `HodgeLadder.Weil.not_ker_model31WedgeEndo_le`: the rank-`(3, 1)` model, where the conclusion
  fails without the conjugation hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Module

namespace HodgeLadder.Weil

/-- **The linear-algebra step of T1.** Let `B : V × V → W` be `ℂ`-bilinear and alternating,
`T` on `V` and `S` on `W` with `S (B x y) = B (T x) (T y)`, `T² = s²` with `s ≠ 0`, and `J` an
injective conjugate-linear map on `V` commuting with `T`, with `conj s = −s`. If
`finrank V = 4`, the products `B x y` span `W`, `F ⊆ V` meets both `ker (T ∓ s)` nontrivially,
and `B x y ∈ G` whenever `x ∈ F`, then the `s²`-eigenspace of `S` lies in `G`. At
`V = H_dR^1(A)`, `B = deRhamCup`, `T = deRhamPullback f 1`, `S = deRhamPullback f 2`,
`J = deRhamConj`, `s = i√d`, `F = F¹H¹_dR` and `G = F¹H²_dR` this is node B of the T1 plan.
The conjugation is used only to force both eigenspaces to rank 2; any injective conjugate-linear
`J` commuting with `T` serves, and at the de Rham instance it is upstream's
`deRhamConjSemilinear`. -/
theorem ker_sub_smul_le_of_isBalanced {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (B : V →ₗ[ℂ] V →ₗ[ℂ] W) (T : V →ₗ[ℂ] V) (S : W →ₗ[ℂ] W)
    (J : V →ₛₗ[starRingEnd ℂ] V) {s : ℂ} {F : Submodule ℂ V} {G : Submodule ℂ W}
    (hS : ∀ x y, S (B x y) = B (T x) (T y)) (hT : ∀ x, T (T x) = (s * s) • x)
    (hs : s ≠ 0) (hconj : starRingEnd ℂ s = -s) (hJ : Function.Injective J)
    (hTJ : ∀ x, T (J x) = J (T x)) (hB : ∀ x, B x x = 0) (hF : ∀ x y, x ∈ F → B x y ∈ G)
    (hbal : IsBalanced F T s) (hrank : finrank ℂ V = 4)
    (hspan : Submodule.span ℂ (Set.image2 (fun x y => B x y) Set.univ Set.univ) = ⊤) :
    LinearMap.ker (S - (s * s) • LinearMap.id) ≤ G := by
  set P := LinearMap.ker (T - s • LinearMap.id) with hP
  set N := LinearMap.ker (T + s • LinearMap.id) with hN
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_pos (by omega)
  have hPN : IsCompl P N := isCompl_ker_sub_smul_ker_add_smul T s hs two_ne_zero hT
  have memP : ∀ x, x ∈ P ↔ T x = s • x := fun x => by
    rw [hP, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
  have memN : ∀ x, x ∈ N ↔ T x = -s • x := fun x => by
    rw [hN, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      add_eq_zero_iff_eq_neg, neg_smul]
  have JP : ∀ x ∈ P, J x ∈ N := fun x hx => by
    rw [memN, hTJ, (memP x).mp hx, LinearMap.map_smulₛₗ, hconj]
  have JN : ∀ x ∈ N, J x ∈ P := fun x hx => by
    rw [memP, hTJ, (memN x).mp hx, LinearMap.map_smulₛₗ, map_neg, hconj, neg_neg]
  -- an injective conjugate-linear map between subspaces bounds the rank
  have rk : ∀ U U' : Submodule ℂ V, (∀ x ∈ U, J x ∈ U') → finrank ℂ U ≤ finrank ℂ U' := by
    intro U U' hU
    let j : U →+ U' :=
      { toFun := fun x => ⟨J x, hU x x.2⟩
        map_zero' := by ext; simp
        map_add' := fun x y => by ext; simp }
    have hj : Function.Injective j := fun x y hxy => by
      have := congrArg Subtype.val hxy
      exact Subtype.ext (hJ this)
    have h := rank_le_of_injective_injectiveₛ (starRingEnd ℂ) j (starRingEnd ℂ).injective hj
      (fun r m => by ext; simp [j])
    exact finrank_le_finrank_of_rank_le_rank (by simpa using h) (Module.rank_lt_aleph0 ℂ U')
  have hsum := Submodule.finrank_add_eq_of_isCompl hPN
  have h1 := rk P N JP
  have h2 := rk N P JN
  have hP2 : finrank ℂ P = 2 := by omega
  have hN2 : finrank ℂ N = 2 := by omega
  -- products inside a rank-2 subspace meeting `F`
  have hF' : ∀ x y, y ∈ F → B x y ∈ G := fun x y hy => by
    have h0 := hB (x + y)
    simp only [map_add, LinearMap.add_apply, hB, zero_add, add_zero] at h0
    rw [eq_neg_of_add_eq_zero_right h0]
    exact G.neg_mem (hF y x hy)
  have pairs : ∀ U : Submodule ℂ V, finrank ℂ U = 2 → F ⊓ U ≠ ⊥ →
      ∀ x ∈ U, ∀ y ∈ U, B x y ∈ G := by
    intro U hU hFU
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hFU
    rw [Submodule.mem_inf] at ha
    have ha0' : (⟨a, ha.2⟩ : U) ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    obtain ⟨b, hab⟩ :=
      exists_linearIndependent_pair_of_one_lt_finrank (R := ℂ) (by rw [hU]; norm_num) ha0'
    have hspanU := hab.span_eq_top_of_card_eq_finrank' (by rw [hU, Fintype.card_fin])
    rw [Matrix.range_cons_cons_empty] at hspanU
    have hcomb : ∀ z ∈ U, ∃ α β : ℂ, α • a + β • (b : V) = z := fun z hz => by
      have hz' : (⟨z, hz⟩ : U) ∈ Submodule.span ℂ {(⟨a, ha.2⟩ : U), b} := by
        rw [hspanU]; trivial
      obtain ⟨α, β, h⟩ := Submodule.mem_span_pair.mp hz'
      exact ⟨α, β, congrArg Subtype.val h⟩
    intro x hx y hy
    obtain ⟨α, β, rfl⟩ := hcomb x hx
    obtain ⟨γ, δ, rfl⟩ := hcomb y hy
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hB, smul_zero,
      add_zero, zero_add]
    refine G.add_mem ?_ ?_ <;> refine G.smul_mem _ (G.smul_mem _ ?_)
    · exact hF' _ _ ha.1
    · exact hF _ _ ha.1
  let e : P ⊕ N → V := Sum.elim (fun x => (x : V)) (fun y => (y : V))
  let μ : P ⊕ N → ℂ := Sum.elim (fun _ => s) (fun _ => -s)
  have he : ∀ i, T (e i) = μ i • e i := by
    rintro (x | y)
    · exact (memP x).mp x.2
    · exact (memN y).mp y.2
  have hrange : Submodule.span ℂ (Set.range e) = ⊤ := by
    rw [eq_top_iff, ← hPN.sup_eq_top, sup_le_iff]
    constructor
    · intro x hx; exact Submodule.subset_span ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · intro y hy; exact Submodule.subset_span ⟨Sum.inr ⟨y, hy⟩, rfl⟩
  refine (ker_sub_smul_le_span_of_eigen B T S hS e μ he
    (span_range_prod_eq_top_of_span B e hrange hspan) (s * s)).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨⟨i, j⟩, hij, rfl⟩
  have hne : s * -s ≠ s * s := fun h => hs (by
    have h2 : (2 : ℂ) * (s * s) = 0 := by linear_combination -h
    simpa using h2)
  rcases i with x | x <;> rcases j with y | y
  · exact pairs P hP2 hbal.1 x x.2 y y.2
  · exact absurd hij hne
  · exact absurd ((mul_comm s (-s)).trans hij) hne
  · exact pairs N hN2 hbal.2 x x.2 y y.2

/-- **T1 reduced to rank and span, Hodge form.** On a smooth projective integral `A` over
`Spec ℂ` with an endomorphism `f` of Weil type for `d`, if `finrank ℂ H_dR^1(A) = 4` and the
products `deRhamCup x y` of classes in `H_dR^1(A)` span `H_dR^2(A)`, then the Weil space (the
`−d`-eigenspace of `f^*` on `H²(A; ℚ)`) consists of Hodge classes. Vacuous at the pin: no `A` is
known to satisfy the rank hypothesis. -/
theorem weilSpace_le_hodge_of_rank_span (A : Over (Spec ↧ℂ)) [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] (f : A ⟶ A) (d : ℕ) (hW : IsWeilTypeSurface A f d)
    (hrank : finrank ℂ H_dR^1(A) = 4)
    (hspan : Submodule.span ℂ
      (Set.image2 (fun x y : H_dR^1(A) => deRhamCup x y 2 (by norm_num)) Set.univ Set.univ) = ⊤) :
    weilSpace A f d ≤ Hdg^1(A; ℚ) := by
  intro w hw
  apply mem_hodgeClasses_of_mem_hodgeFiltration A 1 w
  have hS : ∀ x y : H_dR^1(A), deRhamPullback f 2 (deRhamCupBilinear A 1 1 2 (by norm_num) x y) =
      deRhamCupBilinear A 1 1 2 (by norm_num) (deRhamPullback f 1 x) (deRhamPullback f 1 y) :=
    fun x y => LinearMap.congr_fun₂
      (deRhamPullback_cupBilinear f (a := 1) (b := 1) (n := 2) rfl) x y
  have hT : ∀ x : H_dR^1(A), deRhamPullback f 1 (deRhamPullback f 1 x) =
      (weilRoot d * weilRoot d) • x := fun x => by
    rw [hW.deRhamPullback_sq x, ← sq, weilRoot_sq]
  have hconj : starRingEnd ℂ (weilRoot d) = -weilRoot d := by
    simp [weilRoot, Complex.conj_ofReal]
  have hJ : Function.Injective (deRhamConjSemilinear A 1) :=
    Function.LeftInverse.injective (deRhamConj_deRhamConj A 1)
  have hTJ : ∀ x : H_dR^1(A), deRhamPullback f 1 (deRhamConjSemilinear A 1 x) =
      deRhamConjSemilinear A 1 (deRhamPullback f 1 x) := fun x =>
    (deRhamPullback_conj f 1 x).symm
  have hB : ∀ x : H_dR^1(A), deRhamCupBilinear A 1 1 2 (by norm_num) x x = 0 := fun x =>
    deRhamCup_self_of_odd A odd_one rfl x
  have hF : ∀ x y : H_dR^1(A), x ∈ F^1 H_dR^1(A) →
      deRhamCupBilinear A 1 1 2 (by norm_num) x y ∈ F^1 H_dR^2(A) := fun x y hx => by
    have hy : y ∈ hodgeFiltration A 0 1 := by
      rw [hodgeFiltration_eq_top_of_nonpos A 0 le_rfl 1]; trivial
    have := deRhamCup_mem_hodgeFiltration (by norm_num : (1 : ℤ) + 1 = 2) hx hy
    rwa [add_zero] at this
  have key := ker_sub_smul_le_of_isBalanced (deRhamCupBilinear A 1 1 2 (by norm_num))
    (deRhamPullback f 1) (deRhamPullback f 2) (deRhamConjSemilinear A 1) hS hT
    (weilRoot_ne_zero hW.1) hconj hJ hTJ hB hF hW.2.2 hrank hspan
  refine key ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    deRhamPullback_fieldToDeRhamCohomology, (mem_weilSpace_iff A f d w).mp hw,
    fieldToDeRhamCohomology_smul, ← sq, weilRoot_sq, sub_eq_zero]
  simp only [neg_smul, Nat.cast_smul_eq_nsmul]

/-- **T1 reduced to rank and span, algebraic form.** The hypotheses of
`weilSpace_le_hodge_of_rank_span` give `weilSpace A f d ≤ algebraicCycleClassSpan A 1`, through
Lefschetz (1,1) as an equality (`weilSpace_le_algebraic_iff_le_hodge`). -/
theorem weilSpace_le_algebraic_of_rank_span (A : Over (Spec ↧ℂ)) [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] (f : A ⟶ A) (d : ℕ) (hW : IsWeilTypeSurface A f d)
    (hrank : finrank ℂ H_dR^1(A) = 4)
    (hspan : Submodule.span ℂ
      (Set.image2 (fun x y : H_dR^1(A) => deRhamCup x y 2 (by norm_num)) Set.univ Set.univ) = ⊤) :
    weilSpace A f d ≤ algebraicCycleClassSpan A 1 :=
  (weilSpace_le_algebraic_iff_le_hodge A f d).mpr
    (weilSpace_le_hodge_of_rank_span A f d hW hrank hspan)

/-- **T1 from two cohomological facts about abelian surfaces.** If every abelian surface `A`
(upstream's binder: integral smooth projective `[GrpObj A]` over `Spec ℂ` with `dim A.left = 2`)
has `finrank ℂ H_dR^1(A) = 4` and `H_dR^2(A)` spanned by products of `H¹` classes, then
`WeilClassesAlgebraicSurface` holds. Both facts are open at the pin; they are the classical
`b₁ = 4` and `H² = ∧²H¹` of a complex torus of dimension 2 ([Mumford1970] §1;
[GriffithsHarris1978] ch. 2 §6; locators unverified). -/
theorem weilClassesAlgebraicSurface_of_rank_span
    (h : ∀ (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
      [GrpObj A], dim A.left = 2 →
        finrank ℂ H_dR^1(A) = 4 ∧
          Submodule.span ℂ (Set.image2 (fun x y : H_dR^1(A) => deRhamCup x y 2 (by norm_num))
            Set.univ Set.univ) = ⊤) :
    WeilClassesAlgebraicSurface := by
  intro A _ _ _ _ hA f d hW
  exact weilSpace_le_algebraic_of_rank_span A f d hW (h A hA).1 (h A hA).2

section Checks

/-! ### Non-vacuity of `ker_sub_smul_le_of_isBalanced`

A model of its hypotheses on `V = ℂ⁴`, `W = ℂ⁶ = ∧²ℂ⁴` (basis `e01, e02, e03, e12, e13, e23`),
`T = modelEndo` (`J ⊕ J`, rung `weil-surface-statement`), `s = i`, `J` coordinatewise
conjugation, `F` the balanced plane of `isBalanced_model_one_one` and `G = F ∧ V`. The conclusion
holds there and is not trivial (`ker_modelWedgeEndo_ne_bot`, `ker_modelWedgeEndo_ne_top`,
`modelWedgeHodgeOneOne_ne_top`), and it fails for the signature-`(2, 0)` plane, which meets every
hypothesis except balance (`not_ker_modelWedgeEndo_le_two_zero`). -/

/-- `∧² : ℂ⁴ × ℂ⁴ → ℂ⁶` in the basis `e01, e02, e03, e12, e13, e23`. -/
def modelWedge : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) :=
  LinearMap.mk₂ ℂ
    (fun x y => ![x 0 * y 1 - x 1 * y 0, x 0 * y 2 - x 2 * y 0, x 0 * y 3 - x 3 * y 0,
      x 1 * y 2 - x 2 * y 1, x 1 * y 3 - x 3 * y 1, x 2 * y 3 - x 3 * y 2])
    (fun x x' y => by funext i; fin_cases i <;> simp <;> ring)
    (fun c x y => by funext i; fin_cases i <;> simp <;> ring)
    (fun x y y' => by funext i; fin_cases i <;> simp <;> ring)
    (fun c x y => by funext i; fin_cases i <;> simp <;> ring)

/-- `∧² modelEndo` in the same basis: `e01 ↦ e01`, `e02 ↦ e13`, `e03 ↦ −e12`, `e12 ↦ −e03`,
`e13 ↦ e02`, `e23 ↦ e23`. -/
def modelWedgeEndo : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun w := ![w 0, w 4, -(w 3), -(w 2), w 1, w 5]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp

/-- Coordinatewise conjugation on `ℂ⁴`. -/
def modelConj : (Fin 4 → ℂ) →ₛₗ[starRingEnd ℂ] (Fin 4 → ℂ) where
  toFun v i := starRingEnd ℂ (v i)
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

/-- The signature-`(1, 1)` plane `span {(1, −i, 0, 0), (0, 0, 1, i)}`. -/
def modelHodgeOneOne : Submodule ℂ (Fin 4 → ℂ) :=
  Submodule.span ℂ {![1, -Complex.I, 0, 0], ![0, 0, 1, Complex.I]}

/-- `modelHodgeOneOne ∧ ℂ⁴`, as the kernel of `w ↦ w₁ + i w₂ − i w₃ + w₄`. -/
def modelWedgeHodgeOneOne : Submodule ℂ (Fin 6 → ℂ) :=
  LinearMap.ker (({ toFun := fun w => w 1 + Complex.I * w 2 - Complex.I * w 3 + w 4
                    map_add' := fun v w => by simp; ring
                    map_smul' := fun c v => by simp; ring } : (Fin 6 → ℂ) →ₗ[ℂ] ℂ))

/-- The signature-`(2, 0)` plane `span {(1, −i, 0, 0), (0, 0, 1, −i)}`. -/
def modelHodgeTwoZero : Submodule ℂ (Fin 4 → ℂ) :=
  Submodule.span ℂ {![1, -Complex.I, 0, 0], ![0, 0, 1, -Complex.I]}

/-- `modelHodgeTwoZero ∧ ℂ⁴`, as the kernel of `w ↦ −w₁ + i w₂ + i w₃ + w₄`. -/
def modelWedgeHodgeTwoZero : Submodule ℂ (Fin 6 → ℂ) :=
  LinearMap.ker (({ toFun := fun w => -w 1 + Complex.I * w 2 + Complex.I * w 3 + w 4
                    map_add' := fun v w => by simp; ring
                    map_smul' := fun c v => by simp; ring } : (Fin 6 → ℂ) →ₗ[ℂ] ℂ))

/-- `hS` in the model: `∧² modelEndo` is multiplicative on `modelWedge`. -/
theorem modelWedgeEndo_modelWedge (x y : Fin 4 → ℂ) :
    modelWedgeEndo (modelWedge x y) = modelWedge (modelEndo x) (modelEndo y) := by
  funext i; fin_cases i <;> simp [modelWedge, modelWedgeEndo, modelEndo] <;> ring

/-- `hT` in the model, with `s = i`. -/
theorem modelEndo_modelEndo_I (x : Fin 4 → ℂ) :
    modelEndo (modelEndo x) = (Complex.I * Complex.I) • x := by
  funext i; fin_cases i <;> simp [modelEndo]

/-- `hTJ` in the model: `modelEndo` has real entries, so it commutes with conjugation. -/
theorem modelEndo_modelConj (x : Fin 4 → ℂ) :
    modelEndo (modelConj x) = modelConj (modelEndo x) := by
  funext i; fin_cases i <;> simp [modelEndo, modelConj]

/-- `hJ` in the model. -/
theorem modelConj_injective : Function.Injective modelConj := fun x y h => by
  funext i
  exact (starRingEnd ℂ).injective (congrFun h i)

/-- `hB` in the model: `modelWedge` is alternating. -/
theorem modelWedge_self (x : Fin 4 → ℂ) : modelWedge x x = 0 := by
  funext i; fin_cases i <;> simp [modelWedge] <;> ring

/-- `hF` in the model: `x ∈ F` gives `x ∧ y ∈ G`. -/
theorem modelWedge_mem_one_one (x y : Fin 4 → ℂ) (hx : x ∈ modelHodgeOneOne) :
    modelWedge x y ∈ modelWedgeHodgeOneOne := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp only [modelWedgeHodgeOneOne, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
    modelWedge, LinearMap.mk₂_apply]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `hF` for the signature-`(2, 0)` plane. -/
theorem modelWedge_mem_two_zero (x y : Fin 4 → ℂ) (hx : x ∈ modelHodgeTwoZero) :
    modelWedge x y ∈ modelWedgeHodgeTwoZero := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp only [modelWedgeHodgeTwoZero, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
    modelWedge, LinearMap.mk₂_apply]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `hspan` in the model: `e_i ∧ e_j` is the `ij` basis vector. -/
theorem span_modelWedge :
    Submodule.span ℂ (Set.image2 (fun x y => modelWedge x y) Set.univ Set.univ) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℂ (Fin 6)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact ⟨Pi.single 0 1, trivial, Pi.single 1 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩
  · exact ⟨Pi.single 0 1, trivial, Pi.single 2 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩
  · exact ⟨Pi.single 0 1, trivial, Pi.single 3 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩
  · exact ⟨Pi.single 1 1, trivial, Pi.single 2 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩
  · exact ⟨Pi.single 1 1, trivial, Pi.single 3 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩
  · exact ⟨Pi.single 2 1, trivial, Pi.single 3 1, trivial, by
      funext i; fin_cases i <;> simp [modelWedge]⟩

/-- **The linear-algebra step holds in the model**, every hypothesis discharged. -/
theorem ker_modelWedgeEndo_le_one_one :
    LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) ≤
      modelWedgeHodgeOneOne := by
  have hbal : IsBalanced modelHodgeOneOne modelEndo Complex.I := by
    have h := isBalanced_model_one_one
    rw [weilRoot_one] at h
    exact h
  exact ker_sub_smul_le_of_isBalanced modelWedge modelEndo modelWedgeEndo modelConj
    modelWedgeEndo_modelWedge modelEndo_modelEndo_I Complex.I_ne_zero Complex.conj_I
    modelConj_injective modelEndo_modelConj modelWedge_self modelWedge_mem_one_one hbal
    (Module.finrank_fin_fun ℂ) span_modelWedge

/-- The `−1`-eigenspace of `∧² modelEndo` is nonzero: it contains `e02 − e13`. -/
theorem ker_modelWedgeEndo_ne_bot :
    LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨![0, 1, 0, 0, -1, 0], ?_, ?_⟩
  · rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [modelWedgeEndo]
  · intro h; have := congrFun h 1; simp at this

/-- The `−1`-eigenspace of `∧² modelEndo` is proper: `e02` is not in it. -/
theorem ker_modelWedgeEndo_ne_top :
    LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) ≠ ⊤ := by
  intro h
  have h1 : (![0, 1, 0, 0, 0, 0] : Fin 6 → ℂ) ∈
      LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) := h ▸ trivial
  rw [LinearMap.mem_ker] at h1
  have := congrFun h1 1
  simp [modelWedgeEndo] at this

/-- `G = F ∧ V` is proper in the model: `e02 ∉ G`. -/
theorem modelWedgeHodgeOneOne_ne_top : modelWedgeHodgeOneOne ≠ ⊤ := by
  intro h
  have h1 : (![0, 1, 0, 0, 0, 0] : Fin 6 → ℂ) ∈ modelWedgeHodgeOneOne := h ▸ trivial
  simp [modelWedgeHodgeOneOne] at h1

/-- **Balance is load-bearing.** The signature-`(2, 0)` plane meets every other hypothesis
(`modelWedge_mem_two_zero` with the same `B`, `T`, `S`, `J`, rank and span), and the conclusion
fails: `e03 + e12` lies in the `−1`-eigenspace and not in `modelHodgeTwoZero ∧ ℂ⁴`. -/
theorem not_ker_modelWedgeEndo_le_two_zero :
    ¬ LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) ≤
      modelWedgeHodgeTwoZero := by
  intro h
  have h1 : (![0, 0, 1, 1, 0, 0] : Fin 6 → ℂ) ∈
      LinearMap.ker (modelWedgeEndo - (Complex.I * Complex.I) • LinearMap.id) := by
    rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [modelWedgeEndo]
  have h2 := h h1
  simp [modelWedgeHodgeTwoZero] at h2

end Checks

section Checks31

/-- `T = diag (i, i, i, −i)` on `ℂ⁴`: `T² = −1`, eigenspaces of rank 3 and 1, so no injective
conjugate-linear map commutes with it. -/
def model31Endo : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun x := ![Complex.I * x 0, Complex.I * x 1, Complex.I * x 2, -(Complex.I * x 3)]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp <;> ring

/-- `∧² model31Endo`, diagonal `(−1, −1, 1, −1, 1, 1)` in the basis of `modelWedge`. -/
def model31WedgeEndo : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun w := ![-(w 0), -(w 1), w 2, -(w 3), w 4, w 5]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp

/-- The balanced plane `span {e0, e3}` for `model31Endo`. -/
def model31Hodge : Submodule ℂ (Fin 4 → ℂ) := Submodule.span ℂ {![1, 0, 0, 0], ![0, 0, 0, 1]}

/-- `model31Hodge ∧ ℂ⁴`, the kernel of the `e12` coordinate. -/
def model31WedgeHodge : Submodule ℂ (Fin 6 → ℂ) :=
  LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 6 => ℂ) 3)

/-- `hS` for the rank-`(3, 1)` model. -/
theorem model31WedgeEndo_modelWedge (x y : Fin 4 → ℂ) :
    model31WedgeEndo (modelWedge x y) = modelWedge (model31Endo x) (model31Endo y) := by
  funext i
  fin_cases i <;> simp [modelWedge, model31WedgeEndo, model31Endo] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/-- `hT` for the rank-`(3, 1)` model, with `s = i`. -/
theorem model31Endo_model31Endo (x : Fin 4 → ℂ) :
    model31Endo (model31Endo x) = (Complex.I * Complex.I) • x := by
  funext i; fin_cases i <;> simp [model31Endo, ← mul_assoc, Complex.I_mul_I]

/-- `hF` for the rank-`(3, 1)` model. -/
theorem modelWedge_mem_model31 (x y : Fin 4 → ℂ) (hx : x ∈ model31Hodge) :
    modelWedge x y ∈ model31WedgeHodge := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp [model31WedgeHodge, modelWedge]

/-- `hbal` for the rank-`(3, 1)` model: `e0` and `e3` are eigenvectors for `i` and `−i`. -/
theorem isBalanced_model31 : IsBalanced model31Hodge model31Endo Complex.I := by
  constructor
  · rw [Submodule.ne_bot_iff]
    refine ⟨![1, 0, 0, 0], Submodule.mem_inf.mpr ⟨Submodule.subset_span (by simp), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [model31Endo]
    · intro h; have := congrFun h 0; simp at this
  · rw [Submodule.ne_bot_iff]
    refine ⟨![0, 0, 0, 1], Submodule.mem_inf.mpr ⟨Submodule.subset_span (by simp), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [model31Endo]
    · intro h; have := congrFun h 3; simp at this

/-- **The conjugation hypotheses are load-bearing.** Every hypothesis of
`ker_sub_smul_le_of_isBalanced` except `hJ` and `hTJ` holds for `modelWedge`, `model31Endo`,
`model31WedgeEndo`, `model31Hodge`, `model31WedgeHodge` (with `modelWedge_self`,
`span_modelWedge` and rank 4), and the conclusion fails: `e12 ∈ ker (S + 1)`, `e12 ∉ G`. -/
theorem not_ker_model31WedgeEndo_le :
    ¬ LinearMap.ker (model31WedgeEndo - (Complex.I * Complex.I) • LinearMap.id) ≤
      model31WedgeHodge := by
  intro h
  have h1 : (![0, 0, 0, 1, 0, 0] : Fin 6 → ℂ) ∈
      LinearMap.ker (model31WedgeEndo - (Complex.I * Complex.I) • LinearMap.id) := by
    rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [model31WedgeEndo]
  have h2 := h h1
  simp [model31WedgeHodge] at h2

end Checks31

end HodgeLadder.Weil
