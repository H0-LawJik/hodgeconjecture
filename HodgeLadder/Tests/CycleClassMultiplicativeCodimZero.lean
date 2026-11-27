module

public import HodgeLadder.Cycle.Multiplicative
public import HodgeLadder.Tests.FundamentalClassUnit
public import Other.AlgebraicGeometry.Hodge.CodimensionZeroComparison

/-!
# `[X] ∪ [X] = [X]` from the transversal theorem

Rung `cycle-class-multiplicative-codim-zero` (decision 0010; red team finding 11 on
`cycle-class-multiplicative`). For every smooth integral projective `X` over `ℂ`, the generic
point `η` taken as `x = w = t` with `a = b = 0` and `d = dim X` meets every hypothesis of
`HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal`, so
`[X] ∪ [X] = [X]` in `H^{2(0+0)}(X; ℚ) = H⁰(X; ℚ)`, exact, sign `+`. It is the cheapest instance
showing that the hypotheses of the transversal theorem can be met in Lean on every `X`.

Hypotheses, one by one:

* `hx`, `hw`: upstream `coheight_genericPoint_eq_zero`; `ht` in the form `↑0 + ↑0`
  (`coheight_genericPoint_eq_zero_add_zero`); `hd : 0 + 0 ≤ dim X`.
* `hT`: `Z(ℂ) = Z(ℂ) ∩ Z(ℂ)` for `Z` the support of `η`, by `Set.inter_self`
  (`genericPoint_support_eq_inter`).
* `hxreg`, `hwreg`: the missing lemma `cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top`.
  Route: `closure {η} = X`, so the vanishing ideal of the reduced closure is the nilradical, which
  is `⊥` on the reduced `X` (Mathlib `vanishingIdeal_top`, `nilradical_eq_bot`); the closed
  immersion `cycleComponentι X η` is then an isomorphism (`isIso_subschemeι_iff_eq_bot`), its
  composite with `X → Spec ℂ` is smooth, the singular locus `Z_sing` is empty, and
  `X(ℂ) ∖ Z_sing(ℂ) = X(ℂ)`.
* `htr`: `chartAt y` of upstream's charted space, in Mathlib's maximal atlas
  (`IsManifold.chart_mem_maximalAtlas`, `mem_chart_source`). At `a = b = 0` the coordinate
  conditions are empty conjunctions and both supports are `X(ℂ)`, so only the atlas membership is
  tested here.

Two routes to `[X] = 1`. `fundamental-class-unit` proves `[X] = 1` by evaluating the degree-`0`
chart coclass on upstream's standard local class (`forgetRel_chartNormalProjectionCoclass_zero`);
with the unit law `one_cup` it gives `[X] ∪ [X] = [X]` at once. The transversal theorem gives the
same identity through relative cup products, `local-class-product` at `a = b = 0` and uniqueness
of supported classes; its import closure does not contain `fundamental-class-unit`. The routes
share `cycle-class-germ` (`transport_supportedClass_eq_chartNormalProjectionCoclass`), the
comparison `cup_singular_comparison`, `one_cup` and the line `[X] = c • 1`, `c ≠ 0`
(`exists_cycleComponentSheafClass_genericPoint_eq_smul_one`, with the helper
`exists_mem_cycleComponentSmoothSupportAmbientOpen`); they differ only in the last step,
evaluation of the degree-`0` coclass against its idempotence under `relCup2`. Conversely, from the
transversal route, `c² = c` and `c ≠ 0` give `c = 1`:
`cycleComponentSheafClass_genericPoint_eq_one_of_cup_self` recovers `fundamental-class-unit`
without `forgetRel_chartNormalProjectionCoclass_zero`. Both sides of the identity are nonzero
(upstream `cycleComponentSheafClass_genericPoint_ne_zero`). The instance detects a sign of the
transversal theorem only if it is `−1` at `a = b = 0`; `(−1)^{ab}` and `(−1)^a` are `1` there,
and no checked instance detects them yet (rung `cycle-class-sign-test-p2`; `docs/conventions.md`,
row "Transversal product of cycle classes").

## Main results

* `HodgeLadder.Tests.cycleComponentSheafClass_genericPoint_cup_self`: the rung.
* `HodgeLadder.Tests.cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top`: the missing
  lemma, `X(ℂ) ∖ Z_sing(ℂ) = X(ℂ)` for `Z = X`.
* `HodgeLadder.Tests.isIso_cycleComponentι_genericPoint`: the reduced closure of `η` is `X`.
* `HodgeLadder.Tests.genericPoint_support_eq_inter`,
  `genericPoint_support_subset_smoothSupportAmbientOpen`, `genericPoint_transversal`,
  `coheight_genericPoint_eq_zero_add_zero`: the hypotheses.
* `HodgeLadder.Tests.cycleComponentSheafClass_genericPoint_eq_one_of_cup_self`: `[X] = 1` by the
  transversal route.
* `HodgeLadder.Tests.cycleComponentSheafClass_genericPoint_cup_self_ne_neg`: the sign test
  `[X] ∪ [X] ≠ −[X]`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff

namespace HodgeLadder.Tests

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLadder.Cup

/-- The reduced closure of the generic point of an integral scheme is the scheme: the closed
immersion `cycleComponentι X η` is an isomorphism. `closure {η} = X`, and the vanishing ideal of
`X` is the nilradical, which is `⊥` since `X` is reduced. -/
theorem isIso_cycleComponentι_genericPoint (X : Over (Spec ↧ℂ)) [IsIntegral X.left] :
    IsIso (cycleComponentι X.left (genericPoint X.left)) := by
  have hcl : (⟨closure {genericPoint X.left}, isClosed_closure⟩ : Closeds X.left) = ⊤ :=
    SetLike.coe_injective (genericPoint_closure (α := X.left))
  change IsIso (Scheme.IdealSheafData.vanishingIdeal
    (X := X.left) ⟨closure {genericPoint X.left}, isClosed_closure⟩).subschemeι
  rw [Scheme.isIso_subschemeι_iff_eq_bot, hcl,
    Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]

/-- **The missing lemma** (red team finding 11): for the generic point `η` of a smooth integral
projective `X`, the reduced closure `Z = X` has empty singular locus, so upstream's smooth ambient
open `X(ℂ) ∖ Z_sing(ℂ)` is all of `X(ℂ)`. -/
theorem cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤ := by
  have := isIso_cycleComponentι_genericPoint X
  have hsm : Smooth (cycleComponentι X.left (genericPoint X.left) ≫ X.hom) := inferInstance
  have hS : cycleComponentSingularClosedFiltration X (genericPoint X.left) 0 = ⊥ := by
    apply SetLike.coe_injective
    change (((cycleComponentι X.left (genericPoint X.left) ≫ X.hom).smoothLocus :
      Set (cycleComponent X.left (genericPoint X.left)))ᶜ) = ∅
    rw [Scheme.Hom.smoothLocus_eq_top]
    simp
  apply Opens.ext
  change (Point.underlying ⁻¹' (cycleComponentι X.left (genericPoint X.left) ''
    (cycleComponentSingularClosedFiltration X (genericPoint X.left) 0 : Set _)))ᶜ = Set.univ
  rw [hS]
  simp

/-- The coheight of the generic point in the form `↑a + ↑b` with `a = b = 0`, as the transversal
theorem asks for it (hypothesis `ht`). -/
theorem coheight_genericPoint_eq_zero_add_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left] :
    Order.coheight (genericPoint X.left) = ((0 : ℕ) : ℕ∞) + ((0 : ℕ) : ℕ∞) := by
  rw [coheight_genericPoint_eq_zero X]; rfl

/-- Hypothesis `hT` at `x = w = t = η`: `X(ℂ) = X(ℂ) ∩ X(ℂ)`. -/
theorem genericPoint_support_eq_inter (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    (cycleComponentAnalyticClosedSupport X (genericPoint X.left) : Set (ComplexPoint X)) =
      (cycleComponentAnalyticClosedSupport X (genericPoint X.left) : Set (ComplexPoint X)) ∩
        cycleComponentAnalyticClosedSupport X (genericPoint X.left) :=
  (Set.inter_self _).symm

/-- Hypotheses `hxreg`, `hwreg` at `x = w = t = η`, from
`cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top`. -/
theorem genericPoint_support_subset_smoothSupportAmbientOpen (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    (cycleComponentAnalyticClosedSupport X (genericPoint X.left) : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) := by
  rw [cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top]
  exact Set.subset_univ _

/-- Hypothesis `htr` at `x = w = t = η`, `a = b = 0`: at every `y`, the chart `chartAt y` lies in
Mathlib's maximal analytic atlas and contains `y`; the coordinate conditions are empty and both
supports are `X(ℂ)` (upstream `cycleComponentAnalyticClosedSupport_genericPoint_eq_top`). -/
theorem genericPoint_transversal (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ∀ y ∈ (cycleComponentAnalyticClosedSupport X (genericPoint X.left) : Set (ComplexPoint X)),
      ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X), y ∈ φ.source ∧
        ∀ z ∈ φ.source,
          (z ∈ cycleComponentAnalyticClosedSupport X (genericPoint X.left) ↔
            ∀ i : Fin 0, φ z ⟨i, by omega⟩ = 0) ∧
          (z ∈ cycleComponentAnalyticClosedSupport X (genericPoint X.left) ↔
            ∀ j : Fin 0, φ z ⟨0 + j, by omega⟩ = 0) := by
  intro y _
  refine ⟨chartAt _ y, IsManifold.chart_mem_maximalAtlas y, mem_chart_source _ y, fun z _ => ?_⟩
  rw [cycleComponentAnalyticClosedSupport_genericPoint_eq_top]
  exact ⟨⟨fun _ i => i.elim0, fun _ => trivial⟩, ⟨fun _ j => j.elim0, fun _ => trivial⟩⟩

/-- **`[X] ∪ [X] = [X]`** (rung `cycle-class-multiplicative-codim-zero`): for every smooth
integral projective `X` over `ℂ`, the Yoneda cup of upstream's cycle class of the generic point
with itself, in degree `2 * (0 + 0)`, is the cycle class of the generic point. Exact, sign `+`
(`(−1)^{(2·0)(2·0)} = 1`). Obtained from
`HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal` at `x = w = t = η`, `a = b = 0`,
`d = dim X`, every hypothesis discharged. Since `fundamental-class-unit` shows `[X] = 1`, this is
a consistency check of two routes that share `cycle-class-germ`, Ψ and `[X] = c • 1` and differ
in the last step: evaluation of the degree-`0` chart coclass, against its idempotence under
`relCup2`. -/
theorem cycleComponentSheafClass_genericPoint_cup_self (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cup (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (2 * (0 + 0)) (by ring) =
      cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero_add_zero X) :=
  HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal X (d := dim X.left)
    (genericPoint X.left) (genericPoint X.left) (genericPoint X.left)
    (coheight_genericPoint_eq_zero X) (coheight_genericPoint_eq_zero X)
    (coheight_genericPoint_eq_zero_add_zero X) (Nat.zero_le _)
    (genericPoint_support_eq_inter X)
    (genericPoint_support_subset_smoothSupportAmbientOpen X)
    (genericPoint_support_subset_smoothSupportAmbientOpen X)
    (genericPoint_transversal X (dim X.left))

/-- `(c • 1) ∪ (e • 1) = (c e) • 1` in degree `2 * (0 + 0)`: additivity of the cup in each factor
(`add_cup`, `cup_add`) gives `ℚ`-linearity, and `one_cup`. -/
theorem cup_smul_one_smul_one (X : Over (Spec ↧ℂ)) (c e : ℚ) :
    cup (c • (one X : H^(2 * 0)(X; ℚ))) (e • (one X : H^(2 * 0)(X; ℚ))) (2 * (0 + 0))
        (by ring) =
      (c * e) • (one X : H^(2 * 0)(X; ℚ)) := by
  let L : H^(2 * 0)(X; ℚ) →+ H^(2 * (0 + 0))(X; ℚ) :=
    AddMonoidHom.mk' (fun α => cup α (e • one X) (2 * (0 + 0)) (by ring))
      (fun α α' => add_cup α α' _ _ _)
  let R : H^(2 * 0)(X; ℚ) →+ H^(2 * (0 + 0))(X; ℚ) :=
    AddMonoidHom.mk' (fun β => cup (one X : H^(2 * 0)(X; ℚ)) β (2 * (0 + 0)) (by ring))
      (fun β β' => cup_add _ β β' _ _)
  have h1 : L (c • one X) = c • L (one X) := map_rat_smul L c _
  have h2 : R (e • one X) = e • R (one X) := map_rat_smul R e _
  have h3 : R (one X) = one X := one_cup _
  change L (c • one X) = _
  rw [h1]
  change c • R (e • one X) = _
  rw [h2, h3, smul_smul]

/-- **`[X] = 1` by the transversal route.** From `[X] ∪ [X] = [X]`
(`cycleComponentSheafClass_genericPoint_cup_self`) and `[X] = c • 1` with `c ≠ 0`
(`exists_cycleComponentSheafClass_genericPoint_eq_smul_one`, upstream inputs only), `c² = c`, so
`c = 1`. The same statement as `cycleComponentSheafClass_genericPoint_eq_one`
(`fundamental-class-unit`), proved without `forgetRel_chartNormalProjectionCoclass_zero`; it
still uses `cycle-class-germ` through the transversal theorem. -/
theorem cycleComponentSheafClass_genericPoint_eq_one_of_cup_self (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) =
      (one X : H^(2 * 0)(X; ℚ)) := by
  obtain ⟨c, hc0, hc⟩ := exists_cycleComponentSheafClass_genericPoint_eq_smul_one X
  have h' : (c * c) • (one X : H^(2 * 0)(X; ℚ)) = c • one X := by
    refine (cup_smul_one_smul_one X c c).symm.trans ?_
    refine (congrArg (fun α => cup α α (2 * (0 + 0)) (by ring)) hc).symm.trans ?_
    exact (cycleComponentSheafClass_genericPoint_cup_self X).trans hc
  have hne : (one X : H^(2 * 0)(X; ℚ)) ≠ 0 := by
    have : Nonempty (ComplexPoint X) :=
      ⟨(exists_mem_cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left)).choose⟩
    rw [one_eq_fieldCohomologyUnit]
    exact rationalCohomologyUnit_ne_zero X
  have h2 : (c * c - c) • (one X : H^(2 * 0)(X; ℚ)) = 0 := by
    rw [sub_smul, h', sub_self]
  have h3 : c * (c - 1) = 0 := by
    rw [mul_sub, mul_one]; exact (smul_eq_zero.mp h2).resolve_right hne
  rw [hc, sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hc0), one_smul]

/-- Sign test for `cycle-class-multiplicative-codim-zero`: the opposite sign is false,
`[X] ∪ [X] ≠ −[X]`, from the rung and upstream's `cycleComponentSheafClass_genericPoint_ne_zero`
alone (no use of `fundamental-class-unit`). -/
theorem cycleComponentSheafClass_genericPoint_cup_self_ne_neg (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cup (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (2 * (0 + 0)) (by ring) ≠
      -cycleComponentSheafClass X (genericPoint X.left)
        (coheight_genericPoint_eq_zero_add_zero X) := by
  rw [cycleComponentSheafClass_genericPoint_cup_self]
  intro h
  have h2 : (2 : ℚ) • cycleComponentSheafClass X (genericPoint X.left)
      (coheight_genericPoint_eq_zero_add_zero X) = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  rcases smul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact cycleComponentSheafClass_genericPoint_ne_zero X h3

end HodgeLadder.Tests
