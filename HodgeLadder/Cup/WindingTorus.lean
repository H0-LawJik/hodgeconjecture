module

public import HodgeLadder.Cup.TorusPairing
public import HodgeLadder.Cup.TorusCycle
public import LefschetzPort.AlgebraicGeometry.ChernWindingRationalCochain

/-!
# A nonzero cup product of two winding classes

Rung `winding-torus-cup` (front `cup`, sub-rung of `cup-odd-degree-test`). Let `Y` be a space
with two nowhere vanishing continuous functions `g₁ g₂ : Y → ℂ` and a continuous map
`T : ℝ × ℝ → Y`, of period `1` in each variable, such that

  `g₁ (T (s, t)) = exp (2πi s)` and `g₂ (T (s, t)) = exp (2πi t)`.

The rational winding cocycles of `g₁` and `g₂` (`ChernWinding.rationalWindingCochain`, the
winding number `(1/2πi) ∮ d log g` read through a `ℚ`-linear retraction `ℂ → ℚ`) give classes
`a₁ a₂ ∈ H¹(Y; ℚ)` in upstream's singular cohomology. On the torus cycle `T ∘ (lower − upper)`
(`HodgeLadder.Cup.torusPairing`),

  `⟨cupSing a₁ a₂, T⟩ = 1` and `⟨cupSing a₂ a₁, T⟩ = −1`.

So `cupSing a₁ a₂ ≠ 0`, and `cupSing a₂ a₁ ≠ cupSing a₁ a₂`: in degrees `(1, 1)` the sign
`(−1)^{pq} = −1` of `cupSing_gradedComm` is visible on these classes. The edge values are
computed exactly: along the front edge `g₁` winds once and `g₂` not at all, along the back edge
the reverse.

## Main definitions

* `HodgeLadder.Cup.cocycleOf`, `HodgeLadder.Cup.windingTC`, `HodgeLadder.Cup.windingClassTC`,
  `HodgeLadder.Cup.windingClass`, `HodgeLadder.Cup.torusEval`

## Main results

* `HodgeLadder.Cup.torusEval_cupSing`, `HodgeLadder.Cup.torusEval_cupSing_winding`,
  `HodgeLadder.Cup.torusEval_cupSing_winding_swap`, `HodgeLadder.Cup.cupSing_winding_ne_zero`,
  `HodgeLadder.Cup.cupSing_winding_swap_ne`
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Simplicial ChernWinding

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}}

/-- A cocycle of Tau Ceti's cochain complex, from a cochain with zero coboundary. -/
def cocycleOf {n : ℕ} (φ : (tcCochains Y).X n) (hφ : (tcCochains Y).d n (n + 1) φ = 0) :
    (tcCochains Y).cycles n :=
  (tcCochains Y).cyclesMk φ (n + 1) (by simp) hφ

/-- The underlying cochain of `cocycleOf φ hφ` is `φ`. -/
theorem iCycles_cocycleOf {n : ℕ} (φ : (tcCochains Y).X n)
    (hφ : (tcCochains Y).d n (n + 1) φ = 0) :
    (tcCochains Y).iCycles n (cocycleOf φ hφ) = φ := by
  unfold cocycleOf
  exact (tcCochains Y).i_cyclesMk φ (n + 1) (by simp) hφ

/-- The rational winding cochain of `g`, as a Tau Ceti cochain. -/
def windingTC (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) : (tcCochains Y).X 1 :=
  rationalWindingCochain g hg

/-- The rational winding cochain is a cocycle. -/
theorem d_windingTC (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) :
    (tcCochains Y).d 1 2 (windingTC g hg) = 0 :=
  d_comp_rationalWindingCochain g hg

/-- The value of the rational winding cochain on a singular `1`-simplex. -/
theorem val_windingTC (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    val (windingTC g hg) σ = rationalProjection (simplexIncrement g hg σ / twoPiI) := by
  unfold val
  erw [TauCeti.cochainValuesEquiv_apply]
  change ((TopCat.toSSet.obj Y).ιChainComplex σ ≫ windingCochain g hg ≫ rationalProjection) 1 = _
  rw [ιChainComplex_comp_windingCochain_assoc]
  simp [LinearMap.toSpanSingleton]

/-- A rational increment `2πi q` gives the winding value `q`. -/
theorem val_windingTC_of_increment (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (ε : (TopCat.toSSet.obj Y) _⦋1⦌) (q : ℚ) (hq : simplexIncrement g hg ε = twoPiI * (q : ℂ)) :
    val (windingTC g hg) ε = q := by
  rw [val_windingTC, hq, mul_div_cancel_left₀ _ twoPiI_ne_zero, rationalProjection_rat]

variable {T : C(ℝ × ℝ, Y)}

/-- The logarithmic increment of `g` along a simplex `T ∘ γ`, when `g ∘ T = exp (2πi π)` for a
continuous real function `π`: it is `2πi` times the change of `π` along `γ`. -/
theorem simplexIncrement_torus (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (π : ℝ × ℝ → ℝ)
    (hπ : Continuous π) (hgT : ∀ p, g (T p) = Complex.exp (twoPiI * (π p : ℂ)))
    (γ : C(Convexity.StdSimplex ℝ (Fin 2), ℝ × ℝ)) (ε : (TopCat.toSSet.obj Y) _⦋1⦌)
    (hε : ∀ z, simplexMap ε z = T (γ z)) :
    simplexIncrement g hg ε =
      twoPiI * ((π (γ (Convexity.StdSimplex.single 1)) -
        π (γ (Convexity.StdSimplex.single 0)) : ℝ) : ℂ) := by
  unfold simplexIncrement
  have hf : Continuous fun z => twoPiI * (π (γ z) : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (hπ.comp γ.continuous))
  rw [logIncrement_of_exp ⟨fun z => twoPiI * (π (γ z) : ℂ), hf⟩ _ _ (fun z => by
    change Complex.exp _ = g (simplexMap ε z)
    rw [hε, hgT]; rfl)]
  simp only [ContinuousMap.coe_mk]
  push_cast
  ring

section Winding

variable (g₁ g₂ : C(Y, ℂ)) (hg₁ : ∀ y, g₁ y ≠ 0) (hg₂ : ∀ y, g₂ y ≠ 0)
  (h₁ : ∀ p, g₁ (T p) = Complex.exp (twoPiI * (p.1 : ℂ)))
  (h₂ : ∀ p, g₂ (T p) = Complex.exp (twoPiI * (p.2 : ℂ)))

include h₁ in
/-- `g₁` winds once along the front edge. -/
theorem val_frontEdge_fst : val (windingTC g₁ hg₁) (frontEdge T) = 1 := by
  refine val_windingTC_of_increment _ _ _ 1 ?_
  rw [simplexIncrement_torus g₁ hg₁ Prod.fst continuous_fst h₁ (lowerFace 2) _
    (simplexMap_δ_lower T 2), lowerFace_single, lowerFace_single, lowerTriangle_single,
    lowerTriangle_single]
  have e0 : (2 : Fin 3).succAbove 0 = 0 := by decide
  have e1 : (2 : Fin 3).succAbove 1 = 1 := by decide
  simp [e0, e1]

include h₁ in
/-- `g₁` does not wind along the back edge. -/
theorem val_backEdge_fst : val (windingTC g₁ hg₁) (backEdge T) = 0 := by
  refine val_windingTC_of_increment _ _ _ 0 ?_
  rw [simplexIncrement_torus g₁ hg₁ Prod.fst continuous_fst h₁ (lowerFace 0) _
    (simplexMap_δ_lower T 0), lowerFace_single, lowerFace_single, lowerTriangle_single,
    lowerTriangle_single]
  have e0 : (0 : Fin 3).succAbove 0 = 1 := by decide
  have e1 : (0 : Fin 3).succAbove 1 = 2 := by decide
  simp [e0, e1]

include h₂ in
/-- `g₂` does not wind along the front edge. -/
theorem val_frontEdge_snd : val (windingTC g₂ hg₂) (frontEdge T) = 0 := by
  refine val_windingTC_of_increment _ _ _ 0 ?_
  rw [simplexIncrement_torus g₂ hg₂ Prod.snd continuous_snd h₂ (lowerFace 2) _
    (simplexMap_δ_lower T 2), lowerFace_single, lowerFace_single, lowerTriangle_single,
    lowerTriangle_single]
  have e0 : (2 : Fin 3).succAbove 0 = 0 := by decide
  have e1 : (2 : Fin 3).succAbove 1 = 1 := by decide
  simp [e0, e1]

include h₂ in
/-- `g₂` winds once along the back edge. -/
theorem val_backEdge_snd : val (windingTC g₂ hg₂) (backEdge T) = 1 := by
  refine val_windingTC_of_increment _ _ _ 1 ?_
  rw [simplexIncrement_torus g₂ hg₂ Prod.snd continuous_snd h₂ (lowerFace 0) _
    (simplexMap_δ_lower T 0), lowerFace_single, lowerFace_single, lowerTriangle_single,
    lowerTriangle_single]
  have e0 : (0 : Fin 3).succAbove 0 = 1 := by decide
  have e1 : (0 : Fin 3).succAbove 1 = 2 := by decide
  simp [e0, e1]

end Winding

/-- The Tau Ceti class of the rational winding cocycle of `g`. -/
def windingClassTC (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) : tcCoh Y 1 :=
  (tcCochains Y).homologyπ 1 (cocycleOf (windingTC g hg) (d_windingTC g hg))

/-- **The winding class** of `g` in upstream's singular cohomology `H¹(Y; ℚ)`. -/
def windingClass (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) :
    AlgebraicTopology.Singular.Cohomology ℚ Y 1 :=
  (cohIso Y 1).inv (windingClassTC g hg)

section Pairing

variable (hT₁ : ∀ t, T (1, t) = T (0, t)) (hT₂ : ∀ s, T (s, 1) = T (s, 0))

/-- **Evaluation of upstream's `H²(Y; ℚ)` on the torus cycle** `T ∘ (lower − upper)`. -/
def torusEval : AlgebraicTopology.Singular.Cohomology ℚ Y 2 →ₗ[ℚ] ℚ :=
  (torusPairing (lowerSimplex T) (upperSimplex T) (torus_h0 hT₁) torus_h1 (torus_h2 hT₂)).comp
    (cohIso Y 2).hom.hom

/-- The torus evaluation of the cup product of two winding classes, as a determinant of edge
values. -/
theorem torusEval_cupSing (g g' : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hg' : ∀ y, g' y ≠ 0) :
    torusEval hT₁ hT₂ (cupSing Y (windingClass g hg) (windingClass g' hg') 2 rfl) =
      val (windingTC g hg) (frontEdge T) * val (windingTC g' hg') (backEdge T) -
        val (windingTC g hg) (backEdge T) * val (windingTC g' hg') (frontEdge T) := by
  simp only [torusEval, LinearMap.coe_comp, Function.comp_apply, cupSing, windingClass]
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, windingClassTC,
    windingClassTC, torusPairing_tcCup, iCycles_cocycleOf, iCycles_cocycleOf]

variable (g₁ g₂ : C(Y, ℂ)) (hg₁ : ∀ y, g₁ y ≠ 0) (hg₂ : ∀ y, g₂ y ≠ 0)
  (h₁ : ∀ p, g₁ (T p) = Complex.exp (twoPiI * (p.1 : ℂ)))
  (h₂ : ∀ p, g₂ (T p) = Complex.exp (twoPiI * (p.2 : ℂ)))

include h₁ h₂ in
/-- **`⟨a₁ ⌣ a₂, T⟩ = 1`** for the winding classes of `g₁` and `g₂`. -/
theorem torusEval_cupSing_winding :
    torusEval hT₁ hT₂ (cupSing Y (windingClass g₁ hg₁) (windingClass g₂ hg₂) 2 rfl) = 1 := by
  rw [torusEval_cupSing, val_frontEdge_fst g₁ hg₁ h₁, val_backEdge_fst g₁ hg₁ h₁,
    val_frontEdge_snd g₂ hg₂ h₂, val_backEdge_snd g₂ hg₂ h₂]
  norm_num

include h₁ h₂ in
/-- **`⟨a₂ ⌣ a₁, T⟩ = −1`** for the winding classes of `g₁` and `g₂`. -/
theorem torusEval_cupSing_winding_swap :
    torusEval hT₁ hT₂ (cupSing Y (windingClass g₂ hg₂) (windingClass g₁ hg₁) 2 rfl) = -1 := by
  rw [torusEval_cupSing, val_frontEdge_fst g₁ hg₁ h₁, val_backEdge_fst g₁ hg₁ h₁,
    val_frontEdge_snd g₂ hg₂ h₂, val_backEdge_snd g₂ hg₂ h₂]
  norm_num

include hT₁ hT₂ h₁ h₂ in
/-- **The cup product of the two winding classes is nonzero.** -/
theorem cupSing_winding_ne_zero :
    cupSing Y (windingClass g₁ hg₁) (windingClass g₂ hg₂) 2 rfl ≠ 0 := by
  intro h
  have := torusEval_cupSing_winding hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂
  rw [h, map_zero] at this
  exact zero_ne_one this

include hT₁ hT₂ h₁ h₂ in
/-- **The two orders differ**: `cupSing a₂ a₁ ≠ cupSing a₁ a₂`, so the sign in
`cupSing_gradedComm` is `−1` on these classes. -/
theorem cupSing_winding_swap_ne :
    cupSing Y (windingClass g₂ hg₂) (windingClass g₁ hg₁) 2 rfl ≠
      cupSing Y (windingClass g₁ hg₁) (windingClass g₂ hg₂) 2 rfl := by
  intro h
  have h1 := torusEval_cupSing_winding hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂
  have h2 := torusEval_cupSing_winding_swap hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂
  rw [h, h1] at h2
  norm_num at h2

end Pairing

end HodgeLadder.Cup
