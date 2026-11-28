module

public import HodgeLadder.Cup.SingularCup
public import HodgeLadder.Cup.RelCupNaturality

/-!
# Bilinearity and naturality of the singular cup product

Rung `torus-singular-cohomology` (red team change 1, finding 8). `cupSing` is `ℚ`-bilinear: it is
Tau Ceti's bilinear `singularCup` conjugated by the linear isomorphisms `cohIso`; no sign. The
cup is also natural: pulling back along a continuous map `f` carries `a ⌣ b` to
`f^* a ⌣ f^* b`, exactly, with no sign.

## Main definitions

* `HodgeLadder.Cup.cupSingBilin`: `cupSing` as a `ℚ`-bilinear map.
* `HodgeLadder.Cup.cupSingRight`: right cup with a fixed class, `a ↦ a ⌣ b`.

## Main results

* `HodgeLadder.Cup.cupSingBilin_apply`: the bilinear map applies as `cupSing`, by `rfl`.
* `HodgeLadder.Cup.cupSing_add_left`, `HodgeLadder.Cup.cupSing_smul_left`,
  `HodgeLadder.Cup.cupSing_add_right`, `HodgeLadder.Cup.cupSing_smul_right`: linearity in each
  slot.
* `HodgeLadder.Cup.cohIso_cohomologyMap`, `HodgeLadder.Cup.cupSing_cohomologyMap`: `cohIso`
  intertwines the two pullbacks, and `f^* (a ⌣ b) = f^* a ⌣ f^* b`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology.Singular

namespace HodgeLadder.Cup

/-- **The singular cup product as a `ℚ`-bilinear map**
`H^p(X; ℚ) → H^q(X; ℚ) → H^n(X; ℚ)`. -/
def cupSingBilin (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n) :
    Cohomology ℚ X p →ₗ[ℚ] Cohomology ℚ X q →ₗ[ℚ] Cohomology ℚ X n :=
  ((tcCup X p q n h).compl₁₂ (cohIso X p).toLinearEquiv.toLinearMap
    (cohIso X q).toLinearEquiv.toLinearMap).compr₂ (cohIso X n).symm.toLinearEquiv.toLinearMap

/-- `cupSingBilin X p q n h a b = a ⌣ b`, by `rfl`. -/
theorem cupSingBilin_apply (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n) (a : Cohomology ℚ X p)
    (b : Cohomology ℚ X q) : cupSingBilin X p q n h a b = cupSing X a b n h :=
  rfl

/-- **`cupSing` is additive in the first slot**: `(a + a') ⌣ b = a ⌣ b + a' ⌣ b`. -/
theorem cupSing_add_left (X : TopCat.{0}) {p q : ℕ} (a a' : Cohomology ℚ X p)
    (b : Cohomology ℚ X q) (n : ℕ) (h : p + q = n) :
    cupSing X (a + a') b n h = cupSing X a b n h + cupSing X a' b n h := by
  simp only [← cupSingBilin_apply, map_add, LinearMap.add_apply]

/-- **`cupSing` is `ℚ`-homogeneous in the first slot**: `(c • a) ⌣ b = c • (a ⌣ b)`. -/
theorem cupSing_smul_left (X : TopCat.{0}) {p q : ℕ} (c : ℚ) (a : Cohomology ℚ X p)
    (b : Cohomology ℚ X q) (n : ℕ) (h : p + q = n) :
    cupSing X (c • a) b n h = c • cupSing X a b n h := by
  simp only [← cupSingBilin_apply, map_smul, LinearMap.smul_apply]

/-- **`cupSing` is additive in the second slot**: `a ⌣ (b + b') = a ⌣ b + a ⌣ b'`. -/
theorem cupSing_add_right (X : TopCat.{0}) {p q : ℕ} (a : Cohomology ℚ X p)
    (b b' : Cohomology ℚ X q) (n : ℕ) (h : p + q = n) :
    cupSing X a (b + b') n h = cupSing X a b n h + cupSing X a b' n h := by
  simp only [← cupSingBilin_apply, map_add]

/-- **`cupSing` is `ℚ`-homogeneous in the second slot**: `a ⌣ (c • b) = c • (a ⌣ b)`. -/
theorem cupSing_smul_right (X : TopCat.{0}) {p q : ℕ} (c : ℚ) (a : Cohomology ℚ X p)
    (b : Cohomology ℚ X q) (n : ℕ) (h : p + q = n) :
    cupSing X a (c • b) n h = c • cupSing X a b n h := by
  simp only [← cupSingBilin_apply, map_smul]

/-- Right cup with `b`, `a ↦ a ⌣ b`, as a `ℚ`-linear map `H^p(X; ℚ) → H^n(X; ℚ)`. -/
def cupSingRight (X : TopCat.{0}) {p q : ℕ} (b : Cohomology ℚ X q) (n : ℕ) (h : p + q = n) :
    Cohomology ℚ X p →ₗ[ℚ] Cohomology ℚ X n where
  toFun a := cupSing X a b n h
  map_add' a a' := cupSing_add_left X a a' b n h
  map_smul' c a := cupSing_smul_left X c a b n h

/-- `cupSingRight X b n h a = a ⌣ b`. -/
@[simp]
theorem cupSingRight_apply (X : TopCat.{0}) {p q : ℕ} (b : Cohomology ℚ X q) (n : ℕ)
    (h : p + q = n) (a : Cohomology ℚ X p) : cupSingRight X b n h a = cupSing X a b n h :=
  rfl

/-- `cohIso` intertwines upstream's pullback `cohomologyMap` with Tau Ceti's
`singularCohomologyMap`. -/
theorem cohIso_cohomologyMap {Y Y' : TopCat.{0}} (f : Y ⟶ Y') (m : ℕ) (γ : Cohomology ℚ Y' m) :
    (cohIso Y m).hom (cohomologyMap ℚ m f γ) =
      TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℚ)) (k := ℚ)
        (M := 𝟙_ (ModuleCat.{0} ℚ)) f m ((cohIso Y' m).hom γ) :=
  homologyMap_dualIsoYoneda_apply (singularChainComplexMap ℚ f) m γ

/-- **Naturality of the singular cup product**: `f^* (a ⌣ b) = f^* a ⌣ f^* b`, exact, no
sign. -/
theorem cupSing_cohomologyMap {Y Y' : TopCat.{0}} (f : Y ⟶ Y') {p q : ℕ}
    (a : Cohomology ℚ Y' p) (b : Cohomology ℚ Y' q) (n : ℕ) (h : p + q = n) :
    cohomologyMap ℚ n f (cupSing Y' a b n h) =
      cupSing Y (cohomologyMap ℚ p f a) (cohomologyMap ℚ q f b) n h := by
  apply (cohIso Y n).toLinearEquiv.injective
  change (cohIso Y n).hom _ = (cohIso Y n).hom _
  rw [cohIso_cohomologyMap, cupSing, cupSing, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply,
    cohIso_cohomologyMap, cohIso_cohomologyMap]
  exact (TopCat.singularCup_naturality f ℚ _ _ p q n h _ _).symm

end HodgeLadder.Cup
