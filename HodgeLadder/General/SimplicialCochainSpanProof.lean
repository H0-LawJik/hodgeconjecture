module

public import HodgeLadder.General.SimplicialCochainSpan
public import LefschetzPort.AlgebraicTopology.SimplicialCochainDenominators

/-!
# Complex simplicial cohomology is spanned by rational classes

Rung `simplicial-complex-span`: a proof of `HodgeLadder.SimplicialComplexSpan`, a general lemma
kept local (decision 0011). Let `Y` be a simplicial set whose integral homology is finitely
generated in degree `n`. Every degree-`n` cohomology class of the algebraic-dual complex cochain
complex of `Y` is a finite sum of rational classes pushed along `ratScaled z : q ↦ z q`.

The proof follows the port's `SimplicialCochainDenominators` with `ℤ ⊆ ℚ` replaced by
`W ⊆ ℂ`, and uses a projection in place of the quotient `ℂ ⧸ W`.

1. `exists_finiteDimensional_cochainEval_mem`: the values of a complex cocycle `c` on integral
   cycles factor through the finitely generated group `H_n(Y; ℤ)`, so they lie in a
   finite-dimensional `ℚ`-subspace `W ⊆ ℂ`.
2. `exists_sum_ratScaled_eq`: on `W` the identity is `x ↦ Σᵢ wᵢ λᵢ(x)` for finitely many
   additive `λᵢ : ℂ → ℚ` (coordinates in a `ℚ`-basis of `W` after a `ℚ`-linear projection onto
   `W`) and `wᵢ ∈ ℂ` (the basis vectors). Call the sum `P : ℂ →+ ℂ`.
3. `exists_dualMap_d_eq_of_cochainEval`: a complex cochain of positive degree that vanishes on
   integral cycles is a coboundary. It factors through the integral boundary, and the factor
   extends from boundaries to all chains one degree down because `ℂ` is divisible (Baer's
   criterion, `Module.Baer.of_divisible`).
4. `homologyMap_linearDualCoefficientChange_eq`: `P ∘ c - c` vanishes on integral cycles, so by
   3 (and directly in degree `0`, where every chain is a cycle) change of coefficients along `P`
   fixes the class of `c`.
5. `simplicialComplexSpan`: change of coefficients is additive and functorial in the coefficient
   map (`linearDualCoefficientChange_add`, `_comp`), so the class of `c` is
   `Σᵢ (ratScaled wᵢ)_* (λᵢ)_* [c]`.

No universal coefficient theorem and no freeness of subgroups of free abelian groups is used.

## Main definitions

* `HodgeLadder.cochainEval`: evaluation of an `R`-valued cochain on integral chains.

## Main results

* `HodgeLadder.exists_dualMap_d_eq_of_cochainEval`: the Baer step.
* `HodgeLadder.homologyMap_linearDualCoefficientChange_eq`: coefficient change along a map
  fixing the periods fixes the class.
* `HodgeLadder.simplicialComplexSpan : SimplicialComplexSpan`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

namespace HodgeLadder

open SSet

variable (Y : SSet.{0})

section Eval

variable {R : Type} [CommRing R] (n : ℕ)

/-- Evaluation of an `R`-valued cochain on integral chains. -/
def cochainEval (c : Module.Dual R ((Y.chainComplex (ModuleCat.of R R)).X n)) :
    (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ] R :=
  intChainsLift Y n (dualToFun R Y n c)

/-- On a single simplex, evaluation is the value of the cochain on the corresponding chain. -/
lemma cochainEval_chainOfSimplex (c : Module.Dual R ((Y.chainComplex (ModuleCat.of R R)).X n))
    (x : Y _⦋n⦌) :
    cochainEval Y n c (chainOfSimplex ℤ Y n x) = c (chainOfSimplex R Y n x) :=
  intChainsLift_chainOfSimplex Y n _ x

/-- Evaluation is additive in the cochain (difference form). -/
lemma cochainEval_sub (c c' : Module.Dual R ((Y.chainComplex (ModuleCat.of R R)).X n)) :
    cochainEval Y n (c - c') = cochainEval Y n c - cochainEval Y n c' :=
  intChains_hom_ext Y n fun x ↦ by simp [cochainEval_chainOfSimplex]

/-- The zero cochain evaluates to zero. -/
lemma cochainEval_zero : cochainEval Y n (0 : Module.Dual R ((Y.chainComplex
    (ModuleCat.of R R)).X n)) = 0 :=
  intChains_hom_ext Y n fun x ↦ by simp [cochainEval_chainOfSimplex]

/-- Evaluation intertwines the coboundary and the integral boundary. -/
lemma cochainEval_dualMap_d (c : Module.Dual R ((Y.chainComplex (ModuleCat.of R R)).X n)) :
    cochainEval Y (n + 1) (((Y.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom.dualMap c) =
      cochainEval Y n c ∘ₗ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom := by
  unfold cochainEval
  rw [intChainsLift_comp_d]
  congr 1
  funext x
  exact dualToFun_dualMap_d Y n c x

/-- A cocycle vanishes on integral boundaries. -/
lemma cochainEval_d_eq_zero (c : Module.Dual R ((Y.chainComplex (ModuleCat.of R R)).X n))
    (hc : ((Y.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom.dualMap c = 0)
    (i : ℕ) (hi : i = n + 1) (y : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X i) :
    cochainEval Y n c (((Y.chainComplex (ModuleCat.of ℤ ℤ)).d i n).hom y) = 0 := by
  subst hi
  have h := LinearMap.congr_fun (cochainEval_dualMap_d Y n c) y
  rw [hc, cochainEval_zero] at h
  exact h.symm

/-- Evaluation after change of coefficients along an additive map `f` is `f` of the
evaluation. -/
lemma cochainEval_dualCoefficientChange {S : Type} [CommRing S] (f : R →+ S)
    (c : Module.Dual R ((Y.chainComplex (ModuleCat.of R R)).X n))
    (z : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) :
    cochainEval Y n (dualCoefficientChange f Y n c) z = f (cochainEval Y n c z) := by
  have : (cochainEval Y n (dualCoefficientChange f Y n c)).toAddMonoidHom =
      f.comp (cochainEval Y n c).toAddMonoidHom :=
    intChains_addHom_ext Y n fun x ↦ by
      simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.comp_apply,
        cochainEval_chainOfSimplex]
      have h := congrFun (dualToFun_dualCoefficientChange f Y n c) x
      simp only [dualToFun_apply, Function.comp_apply] at h
      exact h
  exact DFunLike.congr_fun this z

end Eval

section Baer

/-- **Baer step.** A complex cochain of degree `k + 1` vanishing on integral cycles is the
coboundary of a complex cochain of degree `k`. -/
theorem exists_dualMap_d_eq_of_cochainEval (k : ℕ)
    (f : Module.Dual ℂ ((Y.chainComplex (ModuleCat.of ℂ ℂ)).X (k + 1)))
    (hf : ∀ z, ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k).hom z = 0 →
      cochainEval Y (k + 1) f z = 0) :
    ∃ e : Module.Dual ℂ ((Y.chainComplex (ModuleCat.of ℂ ℂ)).X k),
      ((Y.chainComplex (ModuleCat.of ℂ ℂ)).d (k + 1) k).hom.dualMap e = f := by
  obtain ⟨d, hd⟩ : ∃ d, d = ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k).hom := ⟨_, rfl⟩
  rw [← hd] at hf
  let φ : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1) →+ ℂ :=
    (cochainEval Y (k + 1) f).toAddMonoidHom
  let dA := d.toAddMonoidHom
  have hker : dA.ker ≤ φ.ker := fun z hz ↦ hf z hz
  let g₀ : dA.range →+ ℂ := (QuotientAddGroup.lift dA.ker φ hker).comp
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
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℂ).extension_property_addMonoidHom
    dA.range.subtype Subtype.val_injective g₀
  have hg' : ∀ z, g (d z) = φ z := by
    intro z
    have := congrArg (fun h ↦ h ⟨d z, hmem z⟩) hg
    simpa using this.trans (hg₀ z)
  refine ⟨dualOfFun ℂ Y k (fun x ↦ g (chainOfSimplex ℤ Y k x)), ?_⟩
  have hgl : intChainsLift Y k (fun x ↦ g (chainOfSimplex ℤ Y k x)) = g.toIntLinearMap' :=
    intChains_hom_ext Y k fun x ↦ by
      rw [intChainsLift_chainOfSimplex]
      rfl
  apply dualToFun_injective ℂ Y (k + 1)
  funext x
  rw [dualToFun_dualMap_d, dualToFun_dualOfFun]
  have h2 := LinearMap.congr_fun (intChainsLift_comp_d Y k
    (fun x ↦ g (chainOfSimplex ℤ Y k x))) (chainOfSimplex ℤ Y (k + 1) x)
  rw [intChainsLift_chainOfSimplex, LinearMap.comp_apply, hgl, ← hd] at h2
  rw [← h2, dualToFun_apply, ← cochainEval_chainOfSimplex]
  exact hg' _

end Baer

section Finite

/-- If integral homology is finitely generated in degree `n`, the values of a complex cocycle on
integral cycles lie in a finite-dimensional `ℚ`-subspace of `ℂ`. -/
theorem exists_finiteDimensional_cochainEval_mem (n : ℕ)
    [Module.Finite ℤ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).homology n)]
    (c : Module.Dual ℂ ((Y.chainComplex (ModuleCat.of ℂ ℂ)).X n))
    (hc : ((Y.chainComplex (ModuleCat.of ℂ ℂ)).d (n + 1) n).hom.dualMap c = 0) :
    ∃ W : Submodule ℚ ℂ, FiniteDimensional ℚ W ∧
      ∀ ζ : (Y.chainComplex (ModuleCat.of ℤ ℤ)).cycles n,
        cochainEval Y n c (((Y.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n).hom ζ) ∈ W := by
  let F : (Y.chainComplex (ModuleCat.of ℤ ℤ)).cycles n →ₗ[ℤ] ℂ :=
    cochainEval Y n c ∘ₗ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n).hom
  have hF : ((Y.chainComplex (ModuleCat.of ℤ ℤ)).sc n).toCycles ≫ ModuleCat.ofHom F = 0 := by
    ext y
    have h1 : ((Y.chainComplex (ModuleCat.of ℤ ℤ)).sc n).iCycles.hom
        (((Y.chainComplex (ModuleCat.of ℤ ℤ)).sc n).toCycles.hom y) =
        ((Y.chainComplex (ModuleCat.of ℤ ℤ)).sc n).f.hom y :=
      ConcreteCategory.congr_hom ((Y.chainComplex (ModuleCat.of ℤ ℤ)).sc n).toCycles_i y
    change cochainEval Y n c (((Y.chainComplex (ModuleCat.of ℤ ℤ)).sc n).iCycles.hom
      (((Y.chainComplex (ModuleCat.of ℤ ℤ)).sc n).toCycles.hom y)) = 0
    rw [h1]
    exact cochainEval_d_eq_zero Y n c hc _ (ChainComplex.prev ℕ n) y
  let G : (Y.chainComplex (ModuleCat.of ℤ ℤ)).homology n →ₗ[ℤ] ℂ :=
    (((Y.chainComplex (ModuleCat.of ℤ ℤ)).sc n).descHomology (ModuleCat.ofHom F) hF).hom
  have hG : ∀ ζ, G (((Y.chainComplex (ModuleCat.of ℤ ℤ)).homologyπ n).hom ζ) = F ζ := fun ζ ↦
    ConcreteCategory.congr_hom
      (((Y.chainComplex (ModuleCat.of ℤ ℤ)).sc n).π_descHomology (ModuleCat.ofHom F) hF) ζ
  obtain ⟨s, hs⟩ := (Module.finite_def.mp (inferInstance :
    Module.Finite ℤ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).homology n))).map G
  refine ⟨Submodule.span ℚ (s : Set ℂ), inferInstance, fun ζ ↦ ?_⟩
  apply Submodule.span_le_restrictScalars ℤ ℚ (s : Set ℂ)
  rw [hs]
  exact ⟨_, Submodule.mem_top, hG ζ⟩

/-- On a finite-dimensional `ℚ`-subspace `W ⊆ ℂ` the identity is a finite sum of additive maps
`ℂ → ℚ` followed by `ratScaled`. -/
theorem exists_sum_ratScaled_eq (W : Submodule ℚ ℂ) [FiniteDimensional ℚ W] :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℂ) (l : ι → (ℂ →+ ℚ)),
      ∀ x ∈ W, ∑ i, ratScaled (w i) (l i x) = x := by
  let b := Module.finBasis ℚ W
  obtain ⟨π, hπ⟩ := W.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype W)
  refine ⟨_, inferInstance, fun i ↦ (b i : ℂ), fun i ↦ ((b.coord i).comp π).toAddMonoidHom,
    fun x hx ↦ ?_⟩
  have hπx : π x = ⟨x, hx⟩ := LinearMap.congr_fun hπ ⟨x, hx⟩
  have h := congrArg W.subtype (b.sum_repr ⟨x, hx⟩)
  simp only [map_sum, map_smul, Submodule.subtype_apply] at h
  simp only [ratScaled_apply, LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp,
    Function.comp_apply, hπx, Module.Basis.coord_apply]
  conv_rhs => rw [← h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Rat.smul_def, mul_comm]

end Finite

section CoefficientChange

/-- Change of coefficients along a composite is the composite of the changes. -/
lemma linearDualCoefficientChange_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+ S) (g : S →+ T) :
    linearDualCoefficientChange (g.comp f) Y =
      linearDualCoefficientChange f Y ≫ linearDualCoefficientChange g Y := by
  ext n φ
  apply dualToFun_injective T Y n
  change dualToFun T Y n (dualCoefficientChange (g.comp f) Y n φ) =
    dualToFun T Y n (dualCoefficientChange g Y n (dualCoefficientChange f Y n φ))
  simp only [dualToFun_dualCoefficientChange]
  rfl

/-- Change of coefficients is additive in the coefficient map. -/
lemma linearDualCoefficientChange_add {R S : Type} [CommRing R] [CommRing S]
    (f g : R →+ S) :
    linearDualCoefficientChange (f + g) Y =
      linearDualCoefficientChange f Y + linearDualCoefficientChange g Y := by
  ext n φ
  apply dualToFun_injective S Y n
  change dualToFun S Y n (dualCoefficientChange (f + g) Y n φ) =
    dualToFun S Y n (dualCoefficientChange f Y n φ + dualCoefficientChange g Y n φ)
  simp only [map_add, dualToFun_dualCoefficientChange]
  rfl

/-- Change of coefficients along the zero map is zero. -/
lemma linearDualCoefficientChange_zero {R S : Type} [CommRing R] [CommRing S] :
    linearDualCoefficientChange (0 : R →+ S) Y = 0 := by
  ext n φ
  apply dualToFun_injective S Y n
  change dualToFun S Y n (dualCoefficientChange (0 : R →+ S) Y n φ) = dualToFun S Y n 0
  simp only [map_zero, dualToFun_dualCoefficientChange]
  rfl

end CoefficientChange

section Homology

set_option hygiene false in
/-- The forgotten algebraic-dual complex cochain complex of `Y`. -/
local notation "Dℂ" => ((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat).mapHomologicalComplex
  (ComplexShape.up ℕ)).obj (Y.chainComplex (ModuleCat.of ℂ ℂ)).linearDualCochainComplex

/-- If an additive map `P : ℂ →+ ℂ` fixes the values of a complex cocycle on integral cycles,
change of coefficients along `P` fixes its cohomology class. -/
theorem homologyMap_linearDualCoefficientChange_eq (n : ℕ) (P : ℂ →+ ℂ)
    (ζ : (Dℂ).cycles n)
    (hP : ∀ z : (Y.chainComplex (ModuleCat.of ℤ ℤ)).cycles n,
      P (cochainEval Y n (forgetDualElem (Y.chainComplex (ModuleCat.of ℂ ℂ)) n
        ((HomologicalComplex.iCycles Dℂ n).hom ζ))
          (((Y.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n).hom z)) =
      cochainEval Y n (forgetDualElem (Y.chainComplex (ModuleCat.of ℂ ℂ)) n
        ((HomologicalComplex.iCycles Dℂ n).hom ζ))
          (((Y.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n).hom z)) :
    (HomologicalComplex.homologyMap (linearDualCoefficientChange P Y) n).hom
      ((HomologicalComplex.homologyπ Dℂ n).hom ζ) = (HomologicalComplex.homologyπ Dℂ n).hom ζ := by
  let Kℤ := Y.chainComplex (ModuleCat.of ℤ ℤ)
  let Kℂ := Y.chainComplex (ModuleCat.of ℂ ℂ)
  let D := ((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj Kℂ.linearDualCochainComplex
  let θ : D ⟶ D := linearDualCoefficientChange P Y
  let c : Module.Dual ℂ (Kℂ.X n) := forgetDualElem Kℂ n ((D.iCycles n).hom ζ)
  let f : Module.Dual ℂ (Kℂ.X n) := dualCoefficientChange P Y n c - c
  have hf : ∀ z : Kℤ.cycles n, cochainEval Y n f ((Kℤ.iCycles n).hom z) = 0 := by
    intro z
    change cochainEval Y n (dualCoefficientChange P Y n c - c) _ = 0
    rw [cochainEval_sub, LinearMap.sub_apply, cochainEval_dualCoefficientChange]
    exact sub_eq_zero.mpr (hP z)
  have key : ∃ w : D.cycles n, (D.homologyπ n).hom w = 0 ∧
      forgetDualElem Kℂ n ((D.iCycles n).hom w) = f := by
    cases n with
    | zero =>
      refine ⟨0, map_zero _, ?_⟩
      rw [map_zero]
      apply dualToFun_injective ℂ Y 0
      funext x
      obtain ⟨z, hz⟩ := exists_cycles_of_d_eq_zero Kℤ 0 0 ChainComplex.next_nat_zero
        (chainOfSimplex ℤ Y 0 x) (by rw [Kℤ.shape 0 0 (by simp)]; rfl)
      have := hf z
      rw [hz, cochainEval_chainOfSimplex] at this
      change _ = f (chainOfSimplex ℂ Y 0 x)
      rw [this]
      rfl
    | succ k =>
      obtain ⟨e, he⟩ := exists_dualMap_d_eq_of_cochainEval Y k f fun z hz ↦ by
        obtain ⟨z', hz'⟩ := exists_cycles_of_d_eq_zero Kℤ (k + 1) k
          (ChainComplex.next_nat_succ k) z hz
        rw [← hz']
        exact hf z'
      refine ⟨(D.toCycles k (k + 1)).hom e,
        ConcreteCategory.congr_hom (D.toCycles_comp_homologyπ k (k + 1)) e, ?_⟩
      have := ConcreteCategory.congr_hom (D.toCycles_i k (k + 1)) e
      rw [forgetDual_d_apply] at this
      exact this.trans he
  obtain ⟨w, hw, hwf⟩ := key
  have h1 : (HomologicalComplex.homologyMap θ n).hom ((D.homologyπ n).hom ζ) =
      (D.homologyπ n).hom ((HomologicalComplex.cyclesMap θ n).hom ζ) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality θ n) ζ
  have h2 : (HomologicalComplex.cyclesMap θ n).hom ζ = ζ + w := by
    apply (AddCommGrpCat.mono_iff_injective (D.iCycles n)).mp inferInstance
    have := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i θ n) ζ
    change (D.iCycles n).hom ((HomologicalComplex.cyclesMap θ n).hom ζ) =
      (θ.f n).hom ((D.iCycles n).hom ζ) at this
    rw [this, map_add]
    change dualCoefficientChange P Y n c = c + forgetDualElem Kℂ n ((D.iCycles n).hom w)
    rw [hwf]
    exact (add_sub_cancel c _).symm
  change (HomologicalComplex.homologyMap θ n).hom ((D.homologyπ n).hom ζ) = _
  rw [h1, h2, map_add, hw, add_zero]

end Homology

/-- **Rung `simplicial-complex-span`.** If the integral homology of a simplicial set is finitely
generated in degree `n`, every degree-`n` complex cohomology class of its algebraic-dual cochain
complex is a finite sum of classes pushed along `ratScaled z`. -/
theorem simplicialComplexSpan : SimplicialComplexSpan := by
  intro Y n _ α
  let Kℂ := Y.chainComplex (ModuleCat.of ℂ ℂ)
  let D := ((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj Kℂ.linearDualCochainComplex
  obtain ⟨ζ, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (D.homologyπ n)).mp inferInstance α
  let c : Module.Dual ℂ (Kℂ.X n) := forgetDualElem Kℂ n ((D.iCycles n).hom ζ)
  have hc : (Kℂ.d (n + 1) n).hom.dualMap c = 0 := by
    have := ConcreteCategory.congr_hom (D.iCycles_d n (n + 1)) ζ
    rw [← forgetDual_d_apply]
    exact this
  obtain ⟨W, _, hW⟩ := exists_finiteDimensional_cochainEval_mem Y n c hc
  obtain ⟨ι, _, w, l, hwl⟩ := exists_sum_ratScaled_eq W
  let P : ℂ →+ ℂ := ∑ i, (ratScaled (w i)).comp (l i)
  have hP := homologyMap_linearDualCoefficientChange_eq Y n P ζ fun z ↦ by
    simp only [P, AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply]
    exact hwl _ (hW z)
  let Φ : (ℂ →+ ℂ) →+ D.homology n :=
    { toFun Q := (HomologicalComplex.homologyMap (linearDualCoefficientChange Q Y) n).hom
        ((D.homologyπ n).hom ζ)
      map_zero' := by
        rw [linearDualCoefficientChange_zero, HomologicalComplex.homologyMap_zero]
        rfl
      map_add' Q Q' := by
        rw [linearDualCoefficientChange_add, HomologicalComplex.homologyMap_add]
        rfl }
  rw [← hP]
  change Φ P ∈ _
  simp only [P, map_sum]
  refine AddSubgroup.sum_mem _ fun i _ ↦
    AddSubgroup.subset_closure (Set.mem_iUnion.mpr ⟨w i, ?_⟩)
  refine ⟨(HomologicalComplex.homologyMap (linearDualCoefficientChange (l i) Y) n).hom
    ((D.homologyπ n).hom ζ), ?_⟩
  change _ = (HomologicalComplex.homologyMap
    (linearDualCoefficientChange ((ratScaled (w i)).comp (l i)) Y) n).hom _
  rw [linearDualCoefficientChange_comp, HomologicalComplex.homologyMap_comp]
  rfl

end HodgeLadder
