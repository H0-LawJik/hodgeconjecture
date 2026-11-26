module

public import HodgeLadder.Cup.RightMultClass
public import HodgeLadder.Cup.CocycleClass

/-!
# Composing the cocycle naming `a` with right multiplication by `b`

Rung `named-cocycle-comp` (front `cup`, part of `cup-singular-comparison`). For global singular
cocycles `a` of degree `p` and `b` of degree `q`, let `z_a = R_a ∘ ι_ℤ` be the Hom-complex cocycle
`ℤ_Y[0] → S_ℤ` naming `a` (`ext-class-right-mult`). Then `z_a` followed by `R_b` is
`(−1)^{pq}` times the cocycle naming `a ∪ b`. The sign is the one built into `rightMulCochain`
in source degree `p`.

## Main definitions

* `HodgeLadder.Cup.cupGlobal`, `HodgeLadder.Cup.namedCocycle`

## Main results

* `HodgeLadder.Cup.cupGlobal_coboundary`, `HodgeLadder.Cup.globalMap_comp_rightMulSheaf`,
  `HodgeLadder.Cup.namedCocycle_comp_rightMul`, `HodgeLadder.Cup.toSmallShiftedHom_named_comp_rightMul`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular CochainComplex
  HomComplex TopCat.Sheaf

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

section General

variable {C : Type*} [Category C] [Abelian C]

/-- The component out of a single complex of a composite cochain. -/
lemma fromSingleEquiv_comp {A : C} {K L : CochainComplex C ℤ} {n₁ n₂ n : ℤ}
    (α : Cochain ((singleFunctor C 0).obj A) K n₁) (β : Cochain K L n₂) (h : n₁ + n₂ = n) :
    Cochain.fromSingleEquiv (zero_add n) (α.comp β h) =
      Cochain.fromSingleEquiv (zero_add n₁) α ≫ β.v n₁ n (by omega) := by
  simp [Cochain.fromSingleEquiv, Cochain.comp_v _ _ h 0 n₁ n (by simp) (by omega)]

end General

variable {Y : TopCat.{0}}

/-- The cup product `a ∪ b` of two global singular cochains. -/
def cupGlobal {p q : ℕ} (a : OpenCochains ℚ Y (op ⊤) p) (b : OpenCochains ℚ Y (op ⊤) q) :
    OpenCochains ℚ Y (op ⊤) (p + q) :=
  rightMulApp b (op ⊤) p (p + q) rfl a

/-- The cup product of two global cocycles is a cocycle. -/
lemma cupGlobal_coboundary {p q : ℕ} {a : OpenCochains ℚ Y (op ⊤) p}
    {b : OpenCochains ℚ Y (op ⊤) q}
    (ha : (singularCochainCoboundary ℚ Y p).app (op ⊤) a = 0)
    (hb : (singularCochainCoboundary ℚ Y q).app (op ⊤) b = 0) :
    (singularCochainCoboundary ℚ Y (p + q)).app (op ⊤) (cupGlobal a b) = 0 := by
  rw [cupGlobal, rightMulApp_coboundary b hb, ha]
  exact map_zero _

/-- The Hom-complex cocycle `ℤ_Y[0] → S_ℤ` naming a global cocycle `a`. -/
def namedCocycle {p : ℕ} (a : OpenCochains ℚ Y (op ⊤) p)
    (ha : (singularCochainCoboundary ℚ Y p).app (op ⊤) a = 0) :
    Cocycle ((singleFunctor (TopCat.Sheaf AddCommGrpCat Y) 0).obj 𝓒(Y; ℤ)) (sInt Y) p :=
  (rightMulCocycle a ha).precomp (iotaZ Y)

/-- `namedCocycle a` is the cocycle with component `globalMap a` out of `ℤ_Y`. -/
lemma fromSingleEquiv_namedCocycle {p : ℕ} (a : OpenCochains ℚ Y (op ⊤) p)
    (ha : (singularCochainCoboundary ℚ Y p).app (op ⊤) a = 0) :
    Cochain.fromSingleEquiv (zero_add (p : ℤ)) (namedCocycle a ha).1 = globalMap a :=
  fromSingleEquiv_rightMul_precomp a ha

/-- On the map `1 ↦ a`, right multiplication by `b` gives the map `1 ↦ a ∪ b`. -/
lemma globalMap_comp_rightMulSheaf {p q : ℕ} (a : OpenCochains ℚ Y (op ⊤) p)
    (b : OpenCochains ℚ Y (op ⊤) q) :
    (integerConstantHomAddEquivGlobalSections (singularCochainSheaf ℚ Y p)).symm
        ((toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf ℚ Y p)).app (op ⊤) a) ≫
      rightMulSheaf b p (p + q) rfl =
    (integerConstantHomAddEquivGlobalSections (singularCochainSheaf ℚ Y (p + q))).symm
      ((toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf ℚ Y (p + q))).app (op ⊤)
        (cupGlobal a b)) := by
  apply (integerConstantHomAddEquivGlobalSections (singularCochainSheaf ℚ Y (p + q))).injective
  erw [AddEquiv.apply_symm_apply, integerConstantHomAddEquivGlobalSections_naturality,
    AddEquiv.apply_symm_apply]
  have h := congrArg (fun f => f.app (op ⊤))
    (toSheafify_naturality (Opens.grothendieckTopology Y) (rightMul b p (p + q) rfl))
  have h' := ConcreteCategory.congr_hom h a
  simp only [NatTrans.comp_app] at h'
  exact h'.symm

/-- **`z_a` followed by `R_b` is `(−1)^{pq}` times `z_{a ∪ b}`.** -/
theorem namedCocycle_comp_rightMul {p q : ℕ} (a : OpenCochains ℚ Y (op ⊤) p)
    (b : OpenCochains ℚ Y (op ⊤) q)
    (ha : (singularCochainCoboundary ℚ Y p).app (op ⊤) a = 0)
    (hb : (singularCochainCoboundary ℚ Y q).app (op ⊤) b = 0) :
    cocycleComp (namedCocycle a ha) (rightMulCocycle b hb)
        (show (p : ℤ) + q = ((p + q : ℕ) : ℤ) by push_cast; rfl) =
      (((p : ℤ) * q).negOnePow : ℤ) • namedCocycle (cupGlobal a b) (cupGlobal_coboundary ha hb) := by
  ext : 1
  apply (Cochain.fromSingleEquiv (zero_add ((p + q : ℕ) : ℤ))).injective
  rw [Cocycle.coe_smul]
  erw [map_zsmul]
  rw [fromSingleEquiv_namedCocycle]
  change Cochain.fromSingleEquiv _ ((namedCocycle a ha).1.comp (rightMulCocycle b hb).1
    (show (p : ℤ) + q = ((p + q : ℕ) : ℤ) by push_cast; rfl)) = _
  rw [fromSingleEquiv_comp, fromSingleEquiv_namedCocycle, globalMap, globalMap]
  erw [rightMulCochain_v b p (p + q) (p : ℤ) ((p + q : ℕ) : ℤ) rfl rfl rfl]
  rw [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    ← Category.assoc, globalMap_comp_rightMulSheaf]

section Variety

open AlgebraicGeometry ComplexPoint Localization

variable (X : Over (Spec ↧ℂ))

/-- **In the derived category**: the class of `z_a` followed by the class of `R_b` is the class
of `(−1)^{pq} · z_{a ∪ b}`. -/
theorem toSmallShiftedHom_named_comp_rightMul {p q : ℕ}
    (a : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) p)
    (b : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) q)
    (ha : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) p).app (op ⊤) a = 0)
    (hb : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) q).app (op ⊤) b = 0) :
    (CohomologyClass.mk (namedCocycle a ha)).toSmallShiftedHom.{1}.comp
        (CohomologyClass.mk (rightMulCocycle b hb)).toSmallShiftedHom.{1}
        (show (q : ℤ) + p = ((p + q : ℕ) : ℤ) by push_cast; ring) =
      (CohomologyClass.mk ((((p : ℤ) * q).negOnePow : ℤ) •
        namedCocycle (cupGlobal a b) (cupGlobal_coboundary ha hb))).toSmallShiftedHom.{1} := by
  rw [← namedCocycle_comp_rightMul, toSmallShiftedHom_cocycleComp]

end Variety

end HodgeLadder.Cup
