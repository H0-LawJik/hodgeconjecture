module

public import HodgeLadder.Cup.SingularCup

/-!
# Evaluating degree-two singular classes on a torus cycle

Rung `torus-cycle-pairing` (front `cup`, sub-rung of `cup-odd-degree-test`). Two singular
`2`-simplices `σ₁`, `σ₂` of a space `Y` whose faces match as on the square model of the torus,

  `δ₀ σ₁ = δ₂ σ₂`, `δ₁ σ₁ = δ₁ σ₂`, `δ₂ σ₁ = δ₀ σ₂`,

form a `2`-cycle `σ₁ − σ₂`. Evaluation on it, `φ ↦ φ(σ₁) − φ(σ₂)`, kills coboundaries and so
descends to a linear functional on Tau Ceti's `H²(Y; ℚ)`. On the cup product of two degree-one
classes it is a determinant: with `e = δ₂ σ₁` (the front edge) and `f = δ₀ σ₁` (the back edge),

  `⟨a ⌣ b, σ₁ − σ₂⟩ = a(e) b(f) − a(f) b(e)`.

The right-hand side changes sign when `a` and `b` are swapped, so this functional detects the
sign `(−1)^{pq} = −1` of graded commutativity in degrees `(1, 1)`. The cup product is Tau Ceti's
(front face times back face, no sign; conventions row "Singular cup product").

## Main definitions

* `HodgeLadder.Cup.tcCochains`, `HodgeLadder.Cup.val`, `HodgeLadder.Cup.torusEv`,
  `HodgeLadder.Cup.torusPairing`

## Main results

* `HodgeLadder.Cup.torusEv_d`, `HodgeLadder.Cup.torusPairing_homologyπ`,
  `HodgeLadder.Cup.torusPairing_tcCup`
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Simplicial

namespace HodgeLadder.Cup

/-- Tau Ceti's rational singular cochain complex of `Y`, whose cohomology is `tcCoh Y`. -/
abbrev tcCochains (Y : TopCat.{0}) : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  Y.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))

variable {Y : TopCat.{0}}

/-- The value of a rational singular cochain on a singular simplex. -/
def val {n : ℕ} (φ : (tcCochains Y).X n) (σ : (TopCat.toSSet.obj Y) _⦋n⦌) : ℚ :=
  TauCeti.cochainValuesEquiv ℚ (ModuleCat.of ℚ ℚ) (TopCat.toSSet.obj Y) n φ σ

/-- `val` is homogeneous. -/
theorem val_smul {n : ℕ} (r : ℚ) (φ : (tcCochains Y).X n) (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    val (r • φ) σ = r * val φ σ := by
  unfold val; erw [TauCeti.cochainValuesEquiv_apply, TauCeti.cochainValuesEquiv_apply]
  rfl

/-- `val` is additive. -/
theorem val_add {n : ℕ} (φ ψ : (tcCochains Y).X n) (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    val (φ + ψ) σ = val φ σ + val ψ σ := by
  unfold val; erw [TauCeti.cochainValuesEquiv_apply, TauCeti.cochainValuesEquiv_apply,
    TauCeti.cochainValuesEquiv_apply]
  rfl

/-- Evaluation of a `2`-cochain on the chain `σ₁ − σ₂`. -/
def torusEv (σ₁ σ₂ : (TopCat.toSSet.obj Y) _⦋2⦌) : (tcCochains Y).X 2 →ₗ[ℚ] ℚ where
  toFun φ := val φ σ₁ - val φ σ₂
  map_add' φ ψ := by simp only [val_add]; ring
  map_smul' r φ := by simp only [val_smul, RingHom.id_apply, smul_eq_mul]; ring

/-- **`σ₁ − σ₂` is a cycle**: evaluation on it kills coboundaries when the faces match. -/
theorem torusEv_d (σ₁ σ₂ : (TopCat.toSSet.obj Y) _⦋2⦌)
    (h0 : (TopCat.toSSet.obj Y).δ 0 σ₁ = (TopCat.toSSet.obj Y).δ 2 σ₂)
    (h1 : (TopCat.toSSet.obj Y).δ 1 σ₁ = (TopCat.toSSet.obj Y).δ 1 σ₂)
    (h2 : (TopCat.toSSet.obj Y).δ 2 σ₁ = (TopCat.toSSet.obj Y).δ 0 σ₂)
    (η : (tcCochains Y).X 1) : torusEv σ₁ σ₂ ((tcCochains Y).d 1 2 η) = 0 := by
  change val (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d 2 1 ≫ η) σ₁ -
    val (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d 2 1 ≫ η) σ₂ = 0
  unfold val; erw [TauCeti.cochainValuesEquiv_d_two_one, TauCeti.cochainValuesEquiv_d_two_one,
    h0, h1, h2]
  ring

section Pair

variable (σ₁ σ₂ : (TopCat.toSSet.obj Y) _⦋2⦌)

/-- The descent of `torusEv` to cohomology, with its defining property. -/
def torusPairingAux (h0 : (TopCat.toSSet.obj Y).δ 0 σ₁ = (TopCat.toSSet.obj Y).δ 2 σ₂)
    (h1 : (TopCat.toSSet.obj Y).δ 1 σ₁ = (TopCat.toSSet.obj Y).δ 1 σ₂)
    (h2 : (TopCat.toSSet.obj Y).δ 2 σ₁ = (TopCat.toSSet.obj Y).δ 0 σ₂) :
    {l : tcCoh Y 2 ⟶ ModuleCat.of ℚ ℚ // (tcCochains Y).homologyπ 2 ≫ l =
      (tcCochains Y).iCycles 2 ≫ ModuleCat.ofHom (torusEv σ₁ σ₂)} :=
  Limits.CokernelCofork.IsColimit.desc' ((tcCochains Y).homologyIsCokernel 1 2 (by simp))
    ((tcCochains Y).iCycles 2 ≫ ModuleCat.ofHom (torusEv σ₁ σ₂)) (by
      ext η
      change torusEv σ₁ σ₂ ((tcCochains Y).iCycles 2 ((tcCochains Y).toCycles 1 2 η)) = 0
      erw [TauCeti.ChainComplex.linearYonedaObj_iCycles_toCycles_apply]
      exact torusEv_d σ₁ σ₂ h0 h1 h2 η)

variable (h0 : (TopCat.toSSet.obj Y).δ 0 σ₁ = (TopCat.toSSet.obj Y).δ 2 σ₂)
    (h1 : (TopCat.toSSet.obj Y).δ 1 σ₁ = (TopCat.toSSet.obj Y).δ 1 σ₂)
    (h2 : (TopCat.toSSet.obj Y).δ 2 σ₁ = (TopCat.toSSet.obj Y).δ 0 σ₂)

/-- **Evaluation on the torus cycle** `σ₁ − σ₂`, a linear functional on `H²(Y; ℚ)`. -/
def torusPairing : tcCoh Y 2 →ₗ[ℚ] ℚ := (torusPairingAux σ₁ σ₂ h0 h1 h2).1.hom

/-- On the class of a cocycle, the pairing is the value of the cocycle on `σ₁ − σ₂`. -/
theorem torusPairing_homologyπ (a : (tcCochains Y).cycles 2) :
    torusPairing σ₁ σ₂ h0 h1 h2 ((tcCochains Y).homologyπ 2 a) =
      torusEv σ₁ σ₂ ((tcCochains Y).iCycles 2 a) :=
  ConcreteCategory.congr_hom (torusPairingAux σ₁ σ₂ h0 h1 h2).2 a

/-- **The pairing of a cup product of degree-one classes is a determinant**:
`⟨a ⌣ b, σ₁ − σ₂⟩ = a(e) b(f) − a(f) b(e)` with `e = δ₂ σ₁` and `f = δ₀ σ₁`. -/
theorem torusPairing_tcCup (a b : (tcCochains Y).cycles 1) :
    torusPairing σ₁ σ₂ h0 h1 h2 (tcCup Y 1 1 2 rfl ((tcCochains Y).homologyπ 1 a)
        ((tcCochains Y).homologyπ 1 b)) =
      val ((tcCochains Y).iCycles 1 a) ((TopCat.toSSet.obj Y).δ 2 σ₁) *
          val ((tcCochains Y).iCycles 1 b) ((TopCat.toSSet.obj Y).δ 0 σ₁) -
        val ((tcCochains Y).iCycles 1 a) ((TopCat.toSSet.obj Y).δ 0 σ₁) *
          val ((tcCochains Y).iCycles 1 b) ((TopCat.toSSet.obj Y).δ 2 σ₁) := by
  rw [tcCup, TopCat.singularCup_homologyπ, torusPairing_homologyπ]
  change val _ σ₁ - val _ σ₂ = _
  unfold val
  rw [TauCeti.ChainComplex.iCycles_cupCycles]
  erw [TopCat.cochainValuesEquiv_cupCochain_one_one, TopCat.cochainValuesEquiv_cupCochain_one_one]
  rw [← h0, ← h2]

end Pair

end HodgeLadder.Cup
