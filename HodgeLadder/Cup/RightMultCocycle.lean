module

public import HodgeLadder.Cup.RightMult
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Right multiplication as a cocycle of the Hom complex

Rung `right-mult-cocycle` (front `cup`, sub-rung 4 of `cup-singular-comparison`). On the
`ℤ`-indexed singular cochain sheaf complex `S_ℤ = S.extend embeddingUpNat`, right multiplication
by a global `q`-cocycle `b`, with sign `(−1)^{pq}` in source degree `p ≥ 0` and `0` in negative
degrees, is a degree-`q` cocycle of the Hom complex `Hom(S_ℤ, S_ℤ)`. Mathlib's
`Cocycle.equivHomShift` turns it into a chain map `S_ℤ ⟶ S_ℤ⟦q⟧`.

## Main definitions

* `HodgeLadder.Cup.sInt`, `HodgeLadder.Cup.rightMulCochain`, `HodgeLadder.Cup.rightMulCocycle`,
  `HodgeLadder.Cup.rightMulHom`

## Main results

* `HodgeLadder.Cup.rightMulCochain_δ`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular CochainComplex

namespace HodgeLadder.Cup

variable {X : TopCat.{0}}

variable (X) in
/-- The `ℤ`-indexed singular cochain sheaf complex. -/
abbrev sInt : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ :=
  (singularCochainSheafComplex ℚ X).extend ComplexShape.embeddingUpNat

/-- The degree-`p` term of `sInt X` for `p = k ≥ 0`. -/
def sInt_XIso {k : ℕ} {p : ℤ} (hp : (k : ℤ) = p) :
    (sInt X).X p ≅ singularCochainSheaf ℚ X k :=
  (singularCochainSheafComplex ℚ X).extendXIso ComplexShape.embeddingUpNat hp

/-- **Right multiplication as a Hom-complex cochain** of degree `q`, with sign `(−1)^{pq}`. -/
def rightMulCochain {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) :
    HomComplex.Cochain (sInt X) (sInt X) q :=
  HomComplex.Cochain.mk fun p p' hpp' =>
    if hp : 0 ≤ p then
      (sInt_XIso (Int.toNat_of_nonneg hp)).hom ≫
        (((p * q).negOnePow : ℤ) • rightMulSheaf b p.toNat (p.toNat + q) rfl) ≫
          (sInt_XIso (by push_cast; omega)).inv
    else 0

/-- The components of `rightMulCochain`, for any representation of the degrees. -/
lemma rightMulCochain_v {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) (k m : ℕ) (p p' : ℤ)
    (hk : (k : ℤ) = p) (hm : (m : ℤ) = p') (h : k + q = m) (hpp' : p + q = p') :
    (rightMulCochain b).v p p' hpp' =
      (sInt_XIso hk).hom ≫ (((p * q).negOnePow : ℤ) • rightMulSheaf b k m h) ≫
        (sInt_XIso hm).inv := by
  have hp : 0 ≤ p := by omega
  obtain rfl : k = p.toNat := by omega
  obtain rfl : m = p.toNat + q := by omega
  simp only [rightMulCochain, HomComplex.Cochain.mk_v, dif_pos hp]

lemma rightMulCochain_v_of_neg {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) (p p' : ℤ) (hp : p < 0)
    (hpp' : p + q = p') : (rightMulCochain b).v p p' hpp' = 0 := by
  simp only [rightMulCochain, HomComplex.Cochain.mk_v, dif_neg (not_le.mpr hp)]

lemma sInt_d {k : ℕ} {p p' : ℤ} (hk : (k : ℤ) = p) (hl : ((k + 1 : ℕ) : ℤ) = p') :
    (sInt X).d p p' = (sInt_XIso hk).hom ≫ singularCochainSheafCoboundary ℚ X k ≫
      (sInt_XIso hl).inv := by
  rw [HomologicalComplex.extend_d_eq _ _ (show ComplexShape.embeddingUpNat.f k = p from hk)
    (show ComplexShape.embeddingUpNat.f (k + 1) = p' from hl), singularCochainSheafComplex_d]
  rfl

/-- **Right multiplication by a cocycle is a cocycle of the Hom complex.** -/
theorem rightMulCochain_δ {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ X q).app (op ⊤) b = 0) :
    HomComplex.δ q (q + 1) (rightMulCochain b) = 0 := by
  ext p p'' hpp''
  rw [HomComplex.δ_v q (q + 1) rfl _ p p'' hpp'' (p + q) (p + 1) (by omega) rfl,
    HomComplex.Cochain.zero_v]
  by_cases hp : 0 ≤ p
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = p := ⟨p.toNat, Int.toNat_of_nonneg hp⟩
    rw [rightMulCochain_v b n (n + q) n (n + q) rfl (by push_cast; ring) rfl,
      sInt_d (k := n + q) (by push_cast; ring) (by push_cast; omega),
      sInt_d (k := n) rfl (by push_cast; ring),
      rightMulCochain_v b (n + 1) (n + q + 1) ((n : ℤ) + 1) p''
        (by push_cast; ring) (by push_cast; omega) (by omega)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul]
    rw [← Category.assoc (rightMulSheaf b n (n + q) _), rightMulSheaf_comp_coboundary b hb n (n + q) rfl,
      Category.assoc]
    have hsign : ((q : ℤ) + 1).negOnePow • (((n : ℤ) + 1) * q).negOnePow =
        -(((n : ℤ) * q).negOnePow : ℤˣ) := by
      rw [smul_eq_mul, ← Int.negOnePow_add,
        show (q : ℤ) + 1 + ((n : ℤ) + 1) * q = ((n : ℤ) * q + 1) + 2 * q by ring,
        Int.negOnePow_add, Int.negOnePow_two_mul, mul_one, Int.negOnePow_succ]
    have hval := congrArg (fun u : ℤˣ => (u : ℤ)) hsign
    simp only [smul_eq_mul, Units.val_mul, Units.val_neg] at hval
    rw [Units.smul_def, smul_smul, hval, neg_smul]
    exact add_neg_cancel _
  · rw [rightMulCochain_v_of_neg _ _ _ (by omega), Limits.zero_comp, zero_add]
    have hz : Limits.IsZero ((sInt X).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
        change (i : ℤ) = p at hi; omega)
    rw [hz.eq_of_src ((sInt X).d p (p + 1)) 0, Limits.zero_comp, smul_zero]

/-- Right multiplication by a global cocycle `b`, as a cocycle of the Hom complex. -/
def rightMulCocycle {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ X q).app (op ⊤) b = 0) :
    HomComplex.Cocycle (sInt X) (sInt X) q :=
  HomComplex.Cocycle.mk (rightMulCochain b) (q + 1) rfl (rightMulCochain_δ b hb)

/-- **Right multiplication by `b` as a chain map `S_ℤ ⟶ S_ℤ⟦q⟧`.** -/
def rightMulHom {q : ℕ} (b : OpenCochains ℚ X (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ X q).app (op ⊤) b = 0) :
    sInt X ⟶ (sInt X)⟦(q : ℤ)⟧ :=
  HomComplex.Cocycle.equivHomShift.symm (rightMulCocycle b hb)

end HodgeLadder.Cup
