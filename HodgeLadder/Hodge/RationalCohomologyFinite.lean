module

public import HodgeLadder.Hodge.DeRhamRationalBaseChange

/-!
# Rational cohomology of a smooth projective variety is finite-dimensional

Rung `rational-cohomology-finite-dimensional` (red team of `de-rham-rational-base-change`,
finding 8, change F), an input of target T1 of the Markman inventory
(`docs/sketches/cup-hodge-filtration.md`). For a smooth projective integral scheme `X` over `ℂ`
and every degree `n`, upstream's rational constant-sheaf cohomology `H^n(X(ℂ); ℚ)` is a
finite-dimensional `ℚ`-vector space, and with `deRhamBaseChangeEquiv` so is `H_dR^n(X)` over `ℂ`.
Together with `finrank_deRham_eq_finrank_rat` the rank equality is then a count of dimensions in
every degree: `Module.finrank` is `0` on a module that is not finite, and both sides are finite
here.

The route goes through cochains, without the universal coefficient theorem.

1. Topology (port, `module_finite_singularHomology`): `H_n(X(ℂ); ℤ)` is finitely generated.
2. Cochains (`exists_injective_homology_linearDual_rat`, a general lemma kept local): for a
   simplicial set `Y` with `H_n(Y; ℤ)` finitely generated, choose integral cycles `z₁, …, z_k`
   whose classes generate `H_n(Y; ℤ)`. Evaluation `[c] ↦ (c(z₁), …, c(z_k))` is a well-defined
   additive map from the degree-`n` cohomology of the rational algebraic-dual cochain complex to
   `ℚ^k`. It is injective: if `c` vanishes on the `zᵢ`, its evaluation on integral cycles
   factors through `H_n(Y; ℤ)` and vanishes on generators, hence on every integral cycle; a
   rational cochain of positive degree vanishing on integral cycles is a coboundary
   (`exists_dualMap_d_eq_of_cochainEval_rat`, Baer's criterion for the divisible group `ℚ`), and
   in degree `0`, where every chain is a cycle, it is `0`.
3. Comparison (upstream's `rationalCohomologyAddEquivSingularCohomology`, called Ψ, and the
   port's `ordinaryForgottenSingularCochainHomologyIso`): `H^n(X(ℂ); ℚ)` is additively equivalent
   to that cochain cohomology for `Y = X(ℂ)`.
4. Linearity: the composite `H^n(X(ℂ); ℚ) → ℚ^k` is additive and injective. An additive map
   between `ℚ`-vector spaces is `ℚ`-linear (`AddMonoidHom.toRatLinearMap`), so no scalar
   compatibility of Ψ is needed, and `Module.Finite.of_injective` concludes.

## Main results

* `HodgeLadder.exists_dualMap_d_eq_of_cochainEval_rat`: the Baer step over `ℚ`.
* `HodgeLadder.exists_injective_homology_linearDual_rat`: the cochain embedding into `ℚ^k`.
* `HodgeLadder.finiteDimensional_rationalCohomology`: `FiniteDimensional ℚ H^n(X; ℚ)`.
* `HodgeLadder.finiteDimensional_deRham`: `FiniteDimensional ℂ H_dR^n(X)`.
* `HodgeLadder.finiteDimensional_rationalHomology`: `FiniteDimensional ℚ H_n(X(ℂ); ℚ)` (rung
  `rational-homology-finite-dimensional`), from the first, Ψ and upstream's universal
  coefficients over `ℚ`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry ComplexPoint
open scoped Simplicial

namespace HodgeLadder

open SSet

variable (Y : SSet.{0})

/-- Evaluation of a rational cochain on integral chains is additive in the cochain. -/
lemma cochainEval_add_rat (n : ℕ)
    (c c' : Module.Dual ℚ ((Y.chainComplex (ModuleCat.of ℚ ℚ)).X n)) :
    cochainEval Y n (c + c') = cochainEval Y n c + cochainEval Y n c' :=
  intChains_hom_ext Y n fun x ↦ by simp [cochainEval_chainOfSimplex]

/-- **Baer step over `ℚ`.** A rational cochain of degree `k + 1` vanishing on integral cycles is
the coboundary of a rational cochain of degree `k`. The proof is that of
`exists_dualMap_d_eq_of_cochainEval` with the divisible group `ℚ` in place of `ℂ`. -/
theorem exists_dualMap_d_eq_of_cochainEval_rat (k : ℕ)
    (f : Module.Dual ℚ ((Y.chainComplex (ModuleCat.of ℚ ℚ)).X (k + 1)))
    (hf : ∀ z, ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k).hom z = 0 →
      cochainEval Y (k + 1) f z = 0) :
    ∃ e : Module.Dual ℚ ((Y.chainComplex (ModuleCat.of ℚ ℚ)).X k),
      ((Y.chainComplex (ModuleCat.of ℚ ℚ)).d (k + 1) k).hom.dualMap e = f := by
  obtain ⟨d, hd⟩ : ∃ d, d = ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k).hom := ⟨_, rfl⟩
  rw [← hd] at hf
  let φ : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1) →+ ℚ :=
    (cochainEval Y (k + 1) f).toAddMonoidHom
  let dA := d.toAddMonoidHom
  have hker : dA.ker ≤ φ.ker := fun z hz ↦ hf z hz
  let g₀ : dA.range →+ ℚ := (QuotientAddGroup.lift dA.ker φ hker).comp
    (QuotientAddGroup.quotientKerEquivRange dA).symm.toAddMonoidHom
  have hmem : ∀ z, d z ∈ dA.range := fun z ↦ AddMonoidHom.mem_range.mpr ⟨z, rfl⟩
  have hg₀ : ∀ z, g₀ ⟨d z, hmem z⟩ = φ z := by
    intro z
    have h1 : (QuotientAddGroup.quotientKerEquivRange dA).symm ⟨d z, hmem z⟩ =
        QuotientAddGroup.mk z := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    simp only [g₀, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h1,
      QuotientAddGroup.lift_mk]
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℚ).extension_property_addMonoidHom
    dA.range.subtype Subtype.val_injective g₀
  have hg' : ∀ z, g (d z) = φ z := by
    intro z
    have := congrArg (fun h ↦ h ⟨d z, hmem z⟩) hg
    simpa using this.trans (hg₀ z)
  refine ⟨dualOfFun ℚ Y k (fun x ↦ g (chainOfSimplex ℤ Y k x)), ?_⟩
  have hgl : intChainsLift Y k (fun x ↦ g (chainOfSimplex ℤ Y k x)) = g.toIntLinearMap' :=
    intChains_hom_ext Y k fun x ↦ by
      rw [intChainsLift_chainOfSimplex]
      rfl
  apply dualToFun_injective ℚ Y (k + 1)
  funext x
  rw [dualToFun_dualMap_d, dualToFun_dualOfFun]
  have h2 := LinearMap.congr_fun (intChainsLift_comp_d Y k
    (fun x ↦ g (chainOfSimplex ℤ Y k x))) (chainOfSimplex ℤ Y (k + 1) x)
  rw [intChainsLift_chainOfSimplex, LinearMap.comp_apply, hgl, ← hd] at h2
  rw [← h2, dualToFun_apply, ← cochainEval_chainOfSimplex]
  exact hg' _

set_option hygiene false in
/-- The forgotten algebraic-dual rational cochain complex of `Y`. -/
local notation "Dℚ" => ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat).mapHomologicalComplex
  (ComplexShape.up ℕ)).obj (Y.chainComplex (ModuleCat.of ℚ ℚ)).linearDualCochainComplex

/-- A rational coboundary vanishes on integral cycles. -/
lemma cochainEval_d_iCycles_rat (i n : ℕ) (e : (Dℚ).X i)
    (ζ : (Y.chainComplex (ModuleCat.of ℤ ℤ)).cycles n) :
    cochainEval Y n (forgetDualElem (Y.chainComplex (ModuleCat.of ℚ ℚ)) n (((Dℚ).d i n).hom e))
      (((Y.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n).hom ζ) = 0 := by
  by_cases h : i + 1 = n
  · subst h
    have h0 : forgetDualElem (Y.chainComplex (ModuleCat.of ℚ ℚ)) (i + 1)
        (((Dℚ).d i (i + 1)).hom e) =
        ((Y.chainComplex (ModuleCat.of ℚ ℚ)).d (i + 1) i).hom.dualMap e :=
      forgetDual_d_apply _ i e
    rw [h0]
    have h1 := LinearMap.congr_fun (cochainEval_dualMap_d (R := ℚ) Y i e)
      (((Y.chainComplex (ModuleCat.of ℤ ℤ)).iCycles (i + 1)).hom ζ)
    rw [h1, LinearMap.comp_apply]
    have h2 : ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d (i + 1) i).hom
        (((Y.chainComplex (ModuleCat.of ℤ ℤ)).iCycles (i + 1)).hom ζ) = 0 := by
      exact ConcreteCategory.congr_hom
        ((Y.chainComplex (ModuleCat.of ℤ ℤ)).iCycles_d (i + 1) i) ζ
    rw [h2]
    exact map_zero _
  · rw [(Dℚ).shape i n (by simpa using h)]
    change cochainEval Y n 0 _ = 0
    rw [cochainEval_zero]
    rfl

/-- **General lemma (kept local, decision 0011).** If the integral homology of a simplicial set
`Y` is finitely generated in degree `n`, the degree-`n` cohomology of the forgotten
algebraic-dual rational cochain complex of `Y` embeds additively into `ℚ^k` for some `k`. The
embedding evaluates a cocycle on integral cycles representing generators of `H_n(Y; ℤ)`; it is
injective because a rational cocycle vanishing on all integral cycles is a coboundary (Baer
step, `exists_dualMap_d_eq_of_cochainEval_rat`, and directly in degree `0`). -/
theorem exists_injective_homology_linearDual_rat (n : ℕ)
    [Module.Finite ℤ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).homology n)] :
    ∃ (k : ℕ) (f : (Dℚ).homology n →+ (Fin k → ℚ)), Function.Injective f := by
  let Kℤ := Y.chainComplex (ModuleCat.of ℤ ℤ)
  let Kℚ := Y.chainComplex (ModuleCat.of ℚ ℚ)
  let D := ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj Kℚ.linearDualCochainComplex
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Kℤ.homology n)
  have hπℤ := (ModuleCat.epi_iff_surjective (Kℤ.homologyπ n)).mp inferInstance
  choose ζ hζ using fun i ↦ hπℤ (s i)
  let ev : D.cycles n → Module.Dual ℚ (Kℚ.X n) := fun w ↦ forgetDualElem Kℚ n ((D.iCycles n).hom w)
  let Ψ₀ : D.cycles n →+ (Fin k → ℚ) :=
    { toFun w i := cochainEval Y n (ev w) ((Kℤ.iCycles n).hom (ζ i))
      map_zero' := by
        funext i
        simp only [ev, map_zero]
        change cochainEval Y n 0 _ = 0
        rw [cochainEval_zero]
        rfl
      map_add' w w' := by
        funext i
        simp only [ev, map_add]
        change cochainEval Y n (forgetDualElem Kℚ n _ + forgetDualElem Kℚ n _) _ = _
        rw [cochainEval_add_rat]
        rfl }
  have hΨ₀ : (D.sc n).toCycles ≫ AddCommGrpCat.ofHom Ψ₀ = 0 := by
    ext e i
    have h1 : (D.sc n).iCycles.hom ((D.sc n).toCycles.hom e) = (D.sc n).f.hom e :=
      ConcreteCategory.congr_hom (D.sc n).toCycles_i e
    change cochainEval Y n (forgetDualElem Kℚ n ((D.sc n).iCycles.hom
      ((D.sc n).toCycles.hom e))) _ = 0
    rw [h1]
    exact cochainEval_d_iCycles_rat Y _ n e (ζ i)
  let f : D.homology n →+ (Fin k → ℚ) :=
    ((D.sc n).descHomology (AddCommGrpCat.ofHom Ψ₀) hΨ₀).hom
  have hf : ∀ w, f ((D.homologyπ n).hom w) = Ψ₀ w := fun w ↦
    ConcreteCategory.congr_hom ((D.sc n).π_descHomology (AddCommGrpCat.ofHom Ψ₀) hΨ₀) w
  refine ⟨k, f, (injective_iff_map_eq_zero f).mpr fun x hx ↦ ?_⟩
  obtain ⟨w, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (D.homologyπ n)).mp inferInstance x
  rw [hf] at hx
  let c := ev w
  have hc : (Kℚ.d (n + 1) n).hom.dualMap c = 0 := by
    have := ConcreteCategory.congr_hom (D.iCycles_d n (n + 1)) w
    rw [← forgetDual_d_apply]
    exact this
  -- the evaluation of `c` on integral cycles descends to `H_n(Y; ℤ)` and vanishes there
  let F : Kℤ.cycles n →ₗ[ℤ] ℚ := cochainEval Y n c ∘ₗ (Kℤ.iCycles n).hom
  have hF : (Kℤ.sc n).toCycles ≫ ModuleCat.ofHom F = 0 := by
    ext y
    have h1 : (Kℤ.sc n).iCycles.hom ((Kℤ.sc n).toCycles.hom y) = (Kℤ.sc n).f.hom y :=
      ConcreteCategory.congr_hom (Kℤ.sc n).toCycles_i y
    change cochainEval Y n c ((Kℤ.sc n).iCycles.hom ((Kℤ.sc n).toCycles.hom y)) = 0
    rw [h1]
    exact cochainEval_d_eq_zero Y n c hc _ (ChainComplex.prev ℕ n) y
  let G : Kℤ.homology n →ₗ[ℤ] ℚ := ((Kℤ.sc n).descHomology (ModuleCat.ofHom F) hF).hom
  have hG : ∀ z, G ((Kℤ.homologyπ n).hom z) = F z := fun z ↦
    ConcreteCategory.congr_hom ((Kℤ.sc n).π_descHomology (ModuleCat.ofHom F) hF) z
  have hG0 : G = 0 := LinearMap.ext_on_range hs fun i ↦ by
    rw [← hζ i, hG]
    exact congrFun hx i
  have hcyc : ∀ z : Kℤ.cycles n, cochainEval Y n c ((Kℤ.iCycles n).hom z) = 0 := fun z ↦ by
    rw [← LinearMap.comp_apply, ← hG z, hG0, LinearMap.zero_apply]
  -- so `c` is a coboundary
  have key : ∃ v : D.cycles n, (D.homologyπ n).hom v = 0 ∧ ev v = c := by
    cases n with
    | zero =>
      refine ⟨0, map_zero _, ?_⟩
      simp only [ev, map_zero]
      apply dualToFun_injective ℚ Y 0
      funext x
      obtain ⟨z, hz⟩ := exists_cycles_of_d_eq_zero Kℤ 0 0 ChainComplex.next_nat_zero
        (chainOfSimplex ℤ Y 0 x) (by rw [Kℤ.shape 0 0 (by simp)]; rfl)
      have := hcyc z
      rw [hz, cochainEval_chainOfSimplex] at this
      change _ = c (chainOfSimplex ℚ Y 0 x)
      rw [this]
      rfl
    | succ j =>
      obtain ⟨e, he⟩ := exists_dualMap_d_eq_of_cochainEval_rat Y j c fun z hz ↦ by
        obtain ⟨z', hz'⟩ := exists_cycles_of_d_eq_zero Kℤ (j + 1) j
          (ChainComplex.next_nat_succ j) z hz
        rw [← hz']
        exact hcyc z'
      refine ⟨(D.toCycles j (j + 1)).hom e,
        ConcreteCategory.congr_hom (D.toCycles_comp_homologyπ j (j + 1)) e, ?_⟩
      have := ConcreteCategory.congr_hom (D.toCycles_i j (j + 1)) e
      rw [forgetDual_d_apply] at this
      exact this.trans he
  obtain ⟨v, hv, hvc⟩ := key
  have hwv : w = v := (AddCommGrpCat.mono_iff_injective (D.iCycles n)).mp inferInstance hvc.symm
  rw [hwv, hv]

variable (X : Over (Spec ↧ℂ))

/-- **Rung `rational-cohomology-finite-dimensional`.** For a smooth projective integral scheme
`X` over `ℂ` and every degree `n`, upstream's rational constant-sheaf cohomology
`H^n(X(ℂ); ℚ)` is a finite-dimensional `ℚ`-vector space, with upstream's
`fieldCohomologyModule`. -/
theorem finiteDimensional_rationalCohomology [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (n : ℕ) : FiniteDimensional ℚ H^n(X; ℚ) := by
  let : ∀ U : Opens (ComplexPoint X), ParacompactSpace U := openParacompactSpace X
  let Yt := TopCat.of (ComplexPoint X)
  let : Module.Finite ℤ (((TopCat.toSSet.obj Yt).chainComplex (ModuleCat.of ℤ ℤ)).homology n) :=
    module_finite_singularHomology X n
  obtain ⟨k, f, hf⟩ := exists_injective_homology_linearDual_rat (TopCat.toSSet.obj Yt) n
  let Ψ := rationalCohomologyAddEquivSingularCohomology X n
  let F := (AlgebraicTopology.Singular.ordinaryForgottenSingularCochainHomologyIso ℚ Yt n)
    |>.addCommGroupIsoToAddEquiv
  let g : H^n(X; ℚ) →+ (Fin k → ℚ) :=
    f.comp (F.symm.toAddMonoidHom.comp Ψ.toAddMonoidHom)
  have hg : Function.Injective g := hf.comp (F.symm.injective.comp Ψ.injective)
  exact Module.Finite.of_injective g.toRatLinearMap hg

/-- **Rung `rational-cohomology-finite-dimensional`, de Rham form.** For a smooth projective
integral scheme `X` over `ℂ` and every degree `n`, `H_dR^n(X)` is a finite-dimensional
`ℂ`-vector space with upstream's `ℂ`-module structure, through
`deRhamBaseChangeEquiv : ℂ ⊗[ℚ] H^n(X; ℚ) ≃ₗ[ℂ] H_dR^n(X)`. -/
theorem finiteDimensional_deRham [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (n : ℕ) : FiniteDimensional ℂ H_dR^n(X) := by
  have := finiteDimensional_rationalCohomology X n
  exact Module.Finite.equiv (deRhamBaseChangeEquiv X n)

/-- **Rung `rational-homology-finite-dimensional`.** For a smooth projective integral scheme `X`
over `ℂ` and every degree `n`, rational singular homology `H_n(X(ℂ); ℚ)` is a
finite-dimensional `ℚ`-vector space. Ψ is upgraded to a `ℚ`-linear equivalence by
`map_rat_smul`, upstream's universal coefficients over a field,
`cohomologyEquivDualHomology ℚ X(ℂ) n : H^n(X(ℂ); ℚ) ≃ₗ[ℚ] Module.Dual ℚ (H_n(X(ℂ); ℚ))`, make
the dual finite, and `Module.finite_dual_iff` concludes. -/
theorem finiteDimensional_rationalHomology [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (n : ℕ) :
    FiniteDimensional ℚ
      (AlgebraicTopology.Singular.Homology ℚ (TopCat.of (ComplexPoint X)) n) := by
  let : ∀ U : Opens (ComplexPoint X), ParacompactSpace U := openParacompactSpace X
  have := finiteDimensional_rationalCohomology X n
  let Ψ := rationalCohomologyAddEquivSingularCohomology X n
  have : FiniteDimensional ℚ
      (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint X)) n) :=
    Module.Finite.equiv (Ψ.toLinearEquiv (map_rat_smul Ψ))
  have : FiniteDimensional ℚ (Module.Dual ℚ
      (AlgebraicTopology.Singular.Homology ℚ (TopCat.of (ComplexPoint X)) n)) :=
    Module.Finite.equiv
      (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint X)) n)
  exact (Module.finite_dual_iff ℚ).mp this

end HodgeLadder
