module

public import LefschetzPort.TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-!
# The singular cup product on upstream's singular cohomology

Rung `cochain-cup-upstream` (front `cup`). Upstream's singular cochains are linear duals
`Module.Dual ℚ (C_n(X; ℚ))`; Tau Ceti's are morphisms `C_n(X; ℚ) ⟶ ℚ` in `ModuleCat ℚ`. The
two cochain complexes are isomorphic degreewise by `ModuleCat.homLinearEquiv`, and the singular
cup product (front face times back face, no sign) transfers to upstream's `Cohomology ℚ X n`
with associativity and graded commutativity.

## Main definitions

* `HodgeLadder.Cup.dualIsoYoneda`, `HodgeLadder.Cup.cupSing`

## Main results

* `HodgeLadder.Cup.cupSing_gradedComm`, `HodgeLadder.Cup.cupSing_assoc`
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace HodgeLadder.Cup

/-- Linear duals of a chain complex of `ℚ`-modules are morphisms into `ℚ`. -/
def dualIsoYoneda (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) :
    K.linearDualCochainComplex ≅ K.linearYonedaObj ℚ (ModuleCat.of ℚ ℚ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => LinearEquiv.toModuleIso
      ((ModuleCat.homLinearEquiv (R := ℚ) (S := ℚ) (M := K.X n)
        (N := ModuleCat.of ℚ ℚ)).symm : Module.Dual ℚ (K.X n) ≃ₗ[ℚ] (K.X n ⟶ ModuleCat.of ℚ ℚ)))
    (fun i j _ => by ext φ; rfl)

variable (X : TopCat.{0})

/-- Tau Ceti's singular cohomology with rational coefficients. -/
abbrev tcCoh (n : ℕ) : ModuleCat.{0} ℚ :=
  X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ)) n

/-- Upstream's singular cohomology is Tau Ceti's. -/
def cohIso (n : ℕ) : AlgebraicTopology.Singular.Cohomology ℚ X n ≅ tcCoh X n :=
  HomologicalComplex.homologyMapIso
    (dualIsoYoneda (AlgebraicTopology.Singular.SingularChainComplex ℚ X)) n

/-- Tau Ceti's cup product with rational coefficients: unit chains, multiplication `λ`. -/
abbrev tcCup (p q n : ℕ) (h : p + q = n) : tcCoh X p →ₗ[ℚ] tcCoh X q →ₗ[ℚ] tcCoh X n :=
  X.singularCup ℚ (λ_ _).inv (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h

/-- **The singular cup product** on upstream's `Cohomology ℚ X`. -/
def cupSing {p q : ℕ} (a : AlgebraicTopology.Singular.Cohomology ℚ X p)
    (b : AlgebraicTopology.Singular.Cohomology ℚ X q) (n : ℕ) (h : p + q = n) :
    AlgebraicTopology.Singular.Cohomology ℚ X n :=
  (cohIso X n).inv (tcCup X p q n h ((cohIso X p).hom a) ((cohIso X q).hom b))

/-- **Graded commutativity of the singular cup product**:
`b ∪ a = (−1)^{pq} a ∪ b`. -/
theorem cupSing_gradedComm {p q : ℕ} (a : AlgebraicTopology.Singular.Cohomology ℚ X p)
    (b : AlgebraicTopology.Singular.Cohomology ℚ X q) (n : ℕ) (h : p + q = n) :
    cupSing X b a n (by omega) = ((-1 : ℤ) ^ (p * q)) • cupSing X a b n h := by
  unfold cupSing
  rw [TopCat.singularCup_gradedComm_tensorUnit X ℚ
    (by rw [braiding_tensorUnit_left, unitors_equal]; simp) h,
    map_zsmul]

/-- **Associativity of the singular cup product.** -/
theorem cupSing_assoc {p q r : ℕ} (a : AlgebraicTopology.Singular.Cohomology ℚ X p)
    (b : AlgebraicTopology.Singular.Cohomology ℚ X q)
    (c : AlgebraicTopology.Singular.Cohomology ℚ X r) (n : ℕ) (h : p + q + r = n) :
    cupSing X (cupSing X a b (p + q) rfl) c n h = cupSing X a (cupSing X b c (q + r) rfl) n
      (by omega) := by
  unfold cupSing
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  congr 1
  exact TopCat.singularCup_assoc_tensorUnit X ℚ (by simp [unitors_equal]) rfl h rfl (by omega)
    _ _ _

end HodgeLadder.Cup
