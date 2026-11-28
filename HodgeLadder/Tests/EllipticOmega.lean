module

public import HodgeLadder.General.ContMDiffInv
public import HodgeLadder.Tests.EllipticCurveCoordinates
public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.HolomorphicDeRham
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff

namespace HodgeLadder.Tests

section Kaehler

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- `2y dy = (3x² − 1) dx` from `y² = x³ − x`. -/
theorem kaehler_ellipticCurve (x y : A) (hy : y ^ 2 = x ^ 3 - x) :
    (2 * y) • KaehlerDifferential.D ℂ A y = (3 * x ^ 2 - 1) • KaehlerDifferential.D ℂ A x := by
  have h := congrArg (KaehlerDifferential.D ℂ A)
    (show y * y = x * (x * x) - x by linear_combination hy)
  simp only [Derivation.leibniz, map_sub] at h
  linear_combination (norm := module) h

/-- `w dx = 2a dy`. -/
theorem kaehler_ellipticTwo (x y w a : A) (hy : y ^ 2 = x ^ 3 - x) (hw : w * y = 1)
    (ha : a * (3 * x ^ 2 - 1) = 1) :
    w • KaehlerDifferential.D ℂ A x = (2 * a) • KaehlerDifferential.D ℂ A y := by
  have h1 := kaehler_ellipticCurve x y hy
  linear_combination (norm := module) -(a * w) • h1 +
    hw • ((2 * a) • KaehlerDifferential.D ℂ A y) - ha • (w • KaehlerDifferential.D ℂ A x)

/-- `w dx = −2b du`. -/
theorem kaehler_ellipticThree (x y w u b : A) (hy : y ^ 2 = x ^ 3 - x) (hw : w * y = 1)
    (hu : x * w = u) (hb : b * (1 + 2 * u * w) = 1) :
    w • KaehlerDifferential.D ℂ A x = (-2 * b) • KaehlerDifferential.D ℂ A u := by
  have h1 := kaehler_ellipticCurve x y hy
  have h2 : KaehlerDifferential.D ℂ A w = (-w ^ 2) • KaehlerDifferential.D ℂ A y := by
    have := congrArg (KaehlerDifferential.D ℂ A) hw
    rw [Derivation.leibniz, Derivation.map_one_eq_zero] at this
    linear_combination (norm := module) w • this - hw • KaehlerDifferential.D ℂ A w
  have h3 : KaehlerDifferential.D ℂ A u =
      w • KaehlerDifferential.D ℂ A x + x • KaehlerDifferential.D ℂ A w := by
    rw [← hu, Derivation.leibniz, add_comm]
  have hs : w * (1 + 2 * b - b * x * w ^ 2 * (3 * x ^ 2 - 1)) = 0 := by
    linear_combination w * (3 * b * w ^ 2 * hy - 3 * b * (w * y + 1) * hw - hb - 2 * b * w * hu)
  linear_combination (norm := module) (2 * b) • h3 + (2 * b * x) • h2 - (b * x * w ^ 3) • h1 -
    hw • ((-2 * b * x * w ^ 2) • KaehlerDifferential.D ℂ A y) +
    hs • KaehlerDifferential.D ℂ A x

end Kaehler

section Opens

/-- Holomorphic functions on an open, in upstream's spelling. -/
abbrev Hol (V : Opens (ComplexPoint ellipticCurve)) :=
  OpenHolomorphicFunctions ellipticCurve (TopologicalSpace.dim ellipticCurve.left) (op V)

/-- Restriction. -/
abbrev holRes {U V : Opens (ComplexPoint ellipticCurve)} (h : V ≤ U) : Hol U →ₐ[ℂ] Hol V :=
  holomorphicRestrictionAlgHom ellipticCurve _ (homOfLE h).op

/-- Cast. -/
abbrev toEH {V : Opens (ComplexPoint ellipticCurve)} (f : Hol V) : EllipticHolomorphic V := f

theorem holRes_holRes {U V W : Opens (ComplexPoint ellipticCurve)} (h : V ≤ U) (h' : W ≤ V)
    (f : Hol U) : holRes h' (holRes h f) = holRes (h'.trans h) f := rfl

theorem toEH_holRes_apply {U V : Opens (ComplexPoint ellipticCurve)} (h : V ≤ U) (f : Hol U)
    (z : V) : toEH (holRes h f) z = toEH f ⟨z.1, h z.2⟩ := rfl


/-- The coordinate `x` in upstream's ring spelling. -/
abbrev holX : Hol ellipticAffineOpen := ellipticX
/-- The coordinate `y` in upstream's ring spelling. -/
abbrev holY : Hol ellipticAffineOpen := ellipticY
/-- The coordinate `u` in upstream's ring spelling. -/
abbrev holU : Hol ellipticInfinityOpen := ellipticU
/-- The coordinate `w` in upstream's ring spelling. -/
abbrev holW : Hol ellipticInfinityOpen := ellipticW

/-- `3x² − 1`. -/
def ellipticCoeffTwo : Hol ellipticAffineOpen := 3 * holX ^ 2 - 1

/-- `1 + 2uw`. -/
def ellipticCoeffThree : Hol ellipticInfinityOpen :=
  1 + 2 * holU * holW

/-- The open `V₂`. -/
def ellipticOpenTwo : Opens (ComplexPoint ellipticCurve) :=
  ⟨Subtype.val '' {z : ellipticAffineOpen | toEH ellipticCoeffTwo z ≠ 0},
    ellipticAffineOpen.isOpen.isOpenMap_subtype_val _
      (isOpen_ne_fun (toEH ellipticCoeffTwo).contMDiff.continuous continuous_const)⟩

/-- The open `V₃`. -/
def ellipticOpenThree : Opens (ComplexPoint ellipticCurve) :=
  ⟨Subtype.val '' {z : ellipticInfinityOpen | toEH ellipticCoeffThree z ≠ 0},
    ellipticInfinityOpen.isOpen.isOpenMap_subtype_val _
      (isOpen_ne_fun (toEH ellipticCoeffThree).contMDiff.continuous continuous_const)⟩

theorem mem_ellipticOpenTwo {p : ComplexPoint ellipticCurve} :
    p ∈ ellipticOpenTwo ↔ ∃ h : p ∈ ellipticAffineOpen, toEH ellipticCoeffTwo ⟨p, h⟩ ≠ 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨h, hp⟩
    exact ⟨⟨p, h⟩, hp, rfl⟩

theorem mem_ellipticOpenThree {p : ComplexPoint ellipticCurve} :
    p ∈ ellipticOpenThree ↔ ∃ h : p ∈ ellipticInfinityOpen, toEH ellipticCoeffThree ⟨p, h⟩ ≠ 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨h, hp⟩
    exact ⟨⟨p, h⟩, hp, rfl⟩

theorem ellipticOpenTwo_le : ellipticOpenTwo ≤ ellipticAffineOpen :=
  fun _ hp => (mem_ellipticOpenTwo.mp hp).1

theorem ellipticOpenThree_le : ellipticOpenThree ≤ ellipticInfinityOpen :=
  fun _ hp => (mem_ellipticOpenThree.mp hp).1

theorem ellipticOpenTwo_inf_ellipticOpenThree_le :
    ellipticOpenTwo ⊓ ellipticOpenThree ≤ ellipticOverlapOpen :=
  inf_le_inf ellipticOpenTwo_le ellipticOpenThree_le

/-- The cover. -/
theorem ellipticCoeffTwo_apply (z : ellipticAffineOpen) :
    toEH ellipticCoeffTwo z = 3 * ellipticX z ^ 2 - 1 := by
  change ContMDiffMap.evalRingHom z (3 * ellipticX ^ 2 - 1) = _
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one]
  rfl

theorem ellipticCoeffThree_apply (z : ellipticInfinityOpen) :
    toEH ellipticCoeffThree z = 1 + 2 * ellipticU z * ellipticW z := by
  change ContMDiffMap.evalRingHom z (1 + 2 * ellipticU * ellipticW) = _
  simp only [map_add, map_mul, map_ofNat, map_one]
  rfl

theorem ellipticOverlapOpen_sup_sup :
    ellipticOverlapOpen ⊔ ellipticOpenTwo ⊔ ellipticOpenThree = ⊤ := by
  refine eq_top_iff.mpr fun p _ => ?_
  by_cases hA : p ∈ ellipticAffineOpen
  · by_cases hy : ellipticY ⟨p, hA⟩ = 0
    · refine Or.inl (Or.inr (mem_ellipticOpenTwo.mpr ⟨hA, ?_⟩))
      rw [ellipticCoeffTwo_apply]
      have h3 := ellipticY_sq_apply ⟨p, hA⟩
      rw [hy] at h3
      intro h
      have hx : ellipticX ⟨p, hA⟩ = 0 := by
        linear_combination (3 / 2 : ℂ) * h3 + (ellipticX ⟨p, hA⟩ / 2) * h
      rw [hx] at h
      norm_num at h
    · refine Or.inl (Or.inl ⟨hA, ?_⟩)
      have := (mem_ellipticInfinityOpen_iff ⟨p, hA⟩).mpr
      rw [← ellipticY_apply] at this
      exact this hy
  · have hp : p = ellipticCurveInfinity := by
      have : p ∈ (ellipticAffineOpen : Set (ComplexPoint ellipticCurve))ᶜ := hA
      rwa [compl_ellipticAffineOpen] at this
    subst hp
    refine Or.inr (mem_ellipticOpenThree.mpr ⟨ellipticCurveInfinity_mem, ?_⟩)
    rw [ellipticCoeffThree_apply, ellipticUW_infinity.1, ellipticUW_infinity.2]
    norm_num

end Opens

section Forms

/-- The presheaf of holomorphic 1-forms. -/
abbrev ellipticFormPresheaf :=
  holomorphicDeRhamPresheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left) 1

/-- The sheaf of holomorphic 1-forms. -/
abbrev ellipticFormSheaf :=
  holomorphicDeRhamSheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left) 1

/-- The class of `a dv` in `HolomorphicForm`. -/
def formClass {V : Opens (ComplexPoint ellipticCurve)} (a v : Hol V) :
    ellipticFormPresheaf.obj (op V) :=
  Submodule.Quotient.mk (Algebra.DeRham.mk ℂ (Hol V) 1 a ![v])

theorem formClass_res {U V : Opens (ComplexPoint ellipticCurve)} (h : V ≤ U) (a v : Hol U) :
    ellipticFormPresheaf.map (homOfLE h).op (formClass a v) =
      formClass (holRes h a) (holRes h v) := by
  show Submodule.Quotient.mk (formRestriction _ _ _ 1 _) = _
  rw [formRestriction_mk]
  rfl

theorem formClass_eq {V : Opens (ComplexPoint ellipticCurve)} {a v b w : Hol V}
    (h : a • KaehlerDifferential.D ℂ (Hol V) v = b • KaehlerDifferential.D ℂ (Hol V) w) :
    formClass a v = formClass b w := by
  refine congrArg _ ((exteriorPower.oneEquiv (Hol V) Ω[Hol V⁄ℂ]).injective ?_)
  simp only [Algebra.DeRham.mk, Algebra.DeRham.exact, map_smul, exteriorPower.oneEquiv_ιMulti]
  exact h

/-- The relation `y² = x³ − x` restricted to an open of `z ≠ 0`. -/
theorem holY_sq_res {W : Opens (ComplexPoint ellipticCurve)} (h : W ≤ ellipticAffineOpen) :
    holRes h holY ^ 2 = holRes h holX ^ 3 - holRes h holX := by
  rw [← map_pow, ← map_pow, ← map_sub]
  exact congrArg (holRes h) ellipticY_sq

/-- `w · y = 1` restricted to an open of the overlap. -/
theorem holW_mul_holY_res {W : Opens (ComplexPoint ellipticCurve)} (h : W ≤ ellipticOverlapOpen) :
    holRes (h.trans inf_le_right) holW * holRes (h.trans inf_le_left) holY = 1 := by
  have := congrArg (holRes h) (show (holRes inf_le_right holW : Hol ellipticOverlapOpen) *
    holRes inf_le_left holY = 1 from ellipticW_mul_ellipticY)
  rwa [map_mul, map_one, holRes_holRes, holRes_holRes] at this

/-- `x · w = u` restricted to an open of the overlap. -/
theorem holX_mul_holW_res {W : Opens (ComplexPoint ellipticCurve)} (h : W ≤ ellipticOverlapOpen) :
    holRes (h.trans inf_le_left) holX * holRes (h.trans inf_le_right) holW =
      holRes (h.trans inf_le_right) holU := by
  have := congrArg (holRes h) (show (holRes inf_le_left holX : Hol ellipticOverlapOpen) *
    holRes inf_le_right holW = holRes inf_le_right holU from ellipticX_mul_ellipticW)
  rwa [map_mul, holRes_holRes, holRes_holRes, holRes_holRes] at this

theorem ellipticCoeffTwo_ne_zero (z : ellipticOpenTwo) :
    toEH (holRes ellipticOpenTwo_le ellipticCoeffTwo) z ≠ 0 := by
  obtain ⟨h, hne⟩ := mem_ellipticOpenTwo.mp z.2
  exact hne

theorem ellipticCoeffThree_ne_zero (z : ellipticOpenThree) :
    toEH (holRes ellipticOpenThree_le ellipticCoeffThree) z ≠ 0 := by
  obtain ⟨h, hne⟩ := mem_ellipticOpenThree.mp z.2
  exact hne

/-- `(3x² − 1)⁻¹` on `V₂`. -/
def ellipticInvTwo : Hol ellipticOpenTwo :=
  contMDiffMapInv₀ (toEH (holRes ellipticOpenTwo_le ellipticCoeffTwo)) ellipticCoeffTwo_ne_zero

/-- `(1 + 2uw)⁻¹` on `V₃`. -/
def ellipticInvThree : Hol ellipticOpenThree :=
  contMDiffMapInv₀ (toEH (holRes ellipticOpenThree_le ellipticCoeffThree))
    ellipticCoeffThree_ne_zero

theorem ellipticInvTwo_mul :
    ellipticInvTwo * holRes ellipticOpenTwo_le ellipticCoeffTwo = 1 :=
  contMDiffMapInv₀_mul _ _

theorem ellipticInvThree_mul :
    ellipticInvThree * holRes ellipticOpenThree_le ellipticCoeffThree = 1 :=
  contMDiffMapInv₀_mul _ _

/-- `y⁻¹ dx = w dx` on `V₁`. -/
def ellipticFormOne : ellipticFormPresheaf.obj (op ellipticOverlapOpen) :=
  formClass (holRes inf_le_right holW) (holRes inf_le_left holX)

/-- `2 (3x² − 1)⁻¹ dy` on `V₂`. -/
def ellipticFormTwo : ellipticFormPresheaf.obj (op ellipticOpenTwo) :=
  formClass (2 * ellipticInvTwo) (holRes ellipticOpenTwo_le holY)

/-- `−2 (1 + 2uw)⁻¹ du` on `V₃`. -/
def ellipticFormThree : ellipticFormPresheaf.obj (op ellipticOpenThree) :=
  formClass (-2 * ellipticInvThree) (holRes ellipticOpenThree_le holU)

theorem ellipticFormTwo_res {W : Opens (ComplexPoint ellipticCurve)} (h1 : W ≤ ellipticOverlapOpen)
    (h2 : W ≤ ellipticOpenTwo) :
    ellipticFormPresheaf.map (homOfLE h2).op ellipticFormTwo =
      ellipticFormPresheaf.map (homOfLE h1).op ellipticFormOne := by
  rw [ellipticFormTwo, ellipticFormOne, formClass_res, formClass_res]
  refine (formClass_eq ?_).symm
  have ha := congrArg (holRes h2) ellipticInvTwo_mul
  rw [map_mul, map_one, holRes_holRes, ellipticCoeffTwo, map_sub, map_mul, map_pow, map_ofNat,
    map_one] at ha
  rw [map_mul, map_ofNat, holRes_holRes, holRes_holRes, holRes_holRes]
  exact kaehler_ellipticTwo _ _ _ _ (holY_sq_res _) (holW_mul_holY_res h1) ha

theorem ellipticFormThree_res {W : Opens (ComplexPoint ellipticCurve)}
    (h1 : W ≤ ellipticOverlapOpen) (h3 : W ≤ ellipticOpenThree) :
    ellipticFormPresheaf.map (homOfLE h3).op ellipticFormThree =
      ellipticFormPresheaf.map (homOfLE h1).op ellipticFormOne := by
  rw [ellipticFormThree, ellipticFormOne, formClass_res, formClass_res]
  refine (formClass_eq ?_).symm
  have hb := congrArg (holRes h3) ellipticInvThree_mul
  rw [map_mul, map_one, holRes_holRes, ellipticCoeffThree, map_add, map_mul, map_mul, map_ofNat,
    map_one] at hb
  rw [map_mul, map_neg, map_ofNat, holRes_holRes, holRes_holRes, holRes_holRes]
  exact kaehler_ellipticThree _ _ _ _ _ (holY_sq_res _) (holW_mul_holY_res h1)
    (holX_mul_holW_res h1) hb

theorem formClass_eq_zero_iff {V : Opens (ComplexPoint ellipticCurve)} (a v : Hol V) :
    formClass a v = 0 ↔ Algebra.DeRham.mk ℂ (Hol V) 1 a ![v] ∈
      chartEvaluationKernel ellipticCurve (TopologicalSpace.dim ellipticCurve.left) (op V) 1 :=
  Submodule.Quotient.mk_eq_zero _

end Forms

section Glue

/-- The cover `V₁, V₂, V₃` of `E(ℂ)`. -/
def ellipticCover : Fin 3 → Opens (ComplexPoint ellipticCurve) :=
  ![ellipticOverlapOpen, ellipticOpenTwo, ellipticOpenThree]

/-- The three local forms. -/
def ellipticLocalForm : ∀ i, ellipticFormPresheaf.obj (op (ellipticCover i))
  | 0 => ellipticFormOne
  | 1 => ellipticFormTwo
  | 2 => ellipticFormThree

theorem ellipticLocalForm_res (i : Fin 3) {W : Opens (ComplexPoint ellipticCurve)}
    (hi : W ≤ ellipticCover i) (h1 : W ≤ ellipticOverlapOpen) :
    ellipticFormPresheaf.map (homOfLE hi).op (ellipticLocalForm i) =
      ellipticFormPresheaf.map (homOfLE h1).op ellipticFormOne := by
  fin_cases i
  · rfl
  · exact ellipticFormTwo_res h1 hi
  · exact ellipticFormThree_res h1 hi

theorem ellipticCover_inf_le {i j : Fin 3} (hij : i ≠ j) :
    ellipticCover i ⊓ ellipticCover j ≤ ellipticOverlapOpen := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact inf_le_left
    | exact inf_le_right
    | exact ellipticOpenTwo_inf_ellipticOpenThree_le
    | exact (inf_comm _ _).le.trans ellipticOpenTwo_inf_ellipticOpenThree_le

theorem top_le_iSup_ellipticCover : ⊤ ≤ iSup ellipticCover := by
  intro p _
  have hp : p ∈ ellipticOverlapOpen ⊔ ellipticOpenTwo ⊔ ellipticOpenThree := by
    rw [ellipticOverlapOpen_sup_sup]; trivial
  rcases hp with (h | h) | h
  · exact Opens.mem_iSup.mpr ⟨0, h⟩
  · exact Opens.mem_iSup.mpr ⟨1, h⟩
  · exact Opens.mem_iSup.mpr ⟨2, h⟩

/-- The local sections in the sheaf. -/
def ellipticLocalSection (i : Fin 3) :
    ToType (ellipticFormSheaf.presheaf.obj (op (ellipticCover i))) :=
  (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint ellipticCurve)))
    ellipticFormPresheaf).app _ (ellipticLocalForm i)

theorem ellipticLocalSection_compatible :
    TopCat.Presheaf.IsCompatible ellipticFormSheaf.presheaf ellipticCover ellipticLocalSection := by
  intro i j
  simp only [ellipticLocalSection]
  erw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  congr 1
  by_cases hij : i = j
  · subst hij; rfl
  · exact (ellipticLocalForm_res i inf_le_left (ellipticCover_inf_le hij)).trans
      (ellipticLocalForm_res j inf_le_right (ellipticCover_inf_le hij)).symm

/-- **The holomorphic 1-form `ω = dx / y` on `E(ℂ)`.** -/
def ellipticOmega :
    ToType ((holomorphicDeRhamSheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left) 1
      ).presheaf.obj (op ⊤)) :=
  (ellipticFormSheaf.existsUnique_gluing' ellipticCover ⊤ (fun _ => homOfLE le_top)
    top_le_iSup_ellipticCover ellipticLocalSection ellipticLocalSection_compatible).exists.choose

theorem ellipticOmega_res_cover (i : Fin 3) :
    ellipticFormSheaf.presheaf.map (homOfLE le_top).op ellipticOmega = ellipticLocalSection i :=
  (ellipticFormSheaf.existsUnique_gluing' ellipticCover ⊤ (fun _ => homOfLE le_top)
    top_le_iSup_ellipticCover ellipticLocalSection
    ellipticLocalSection_compatible).exists.choose_spec i

/-- **Restriction pin.** -/
theorem ellipticOmega_res :
    (holomorphicDeRhamSheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left) 1).presheaf.map
        (homOfLE (le_top : ellipticOverlapOpen ≤ ⊤)).op ellipticOmega =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint ellipticCurve)))
        (holomorphicDeRhamPresheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left) 1)).app
        (op ellipticOverlapOpen)
        (Submodule.Quotient.mk (Algebra.DeRham.mk ℂ _ 1
          (ellipticResInfinity ellipticW) ![ellipticResAffine ellipticX])) :=
  ellipticOmega_res_cover 0

/-- No three distinct points of `z ≠ 0` share the value of `x`. -/
theorem ellipticX_fibre_three {a b c : ellipticAffineOpen} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (h1 : ellipticX a = ellipticX b) (h2 : ellipticX a = ellipticX c) : False := by
  rcases ellipticY_eq_or_eq_neg_of_ellipticX_eq h1 with hb | hb
  · exact hab (eq_of_ellipticX_eq_of_ellipticY_eq h1 hb)
  rcases ellipticY_eq_or_eq_neg_of_ellipticX_eq h2 with hc | hc
  · exact hac (eq_of_ellipticX_eq_of_ellipticY_eq h2 hc)
  have hy : ellipticY b = ellipticY c := by
    have := hb.symm.trans hc
    exact neg_injective this
  exact hbc (eq_of_ellipticX_eq_of_ellipticY_eq (h1.symm.trans h2) hy)

/-- On the overlap, `w` vanishes nowhere. -/
theorem ellipticW_ne_zero_of_mem (z : ellipticOverlapOpen) :
    ellipticResInfinity ellipticW z ≠ 0 := by
  rw [ellipticW_eq_inv]
  exact one_div_ne_zero (ellipticY_ne_zero_of_mem z)

theorem ellipticFormOne_res_ne_zero {W : Opens (ComplexPoint ellipticCurve)}
    (hW : W ≤ ellipticOverlapOpen) (p : ComplexPoint ellipticCurve) (hp : p ∈ W) :
    ellipticFormPresheaf.map (homOfLE hW).op ellipticFormOne ≠ 0 := by
  set d := TopologicalSpace.dim ellipticCurve.left
  rw [ellipticFormOne, formClass_res]
  intro h
  rw [formClass_eq_zero_iff] at h
  have hker := (mem_chartEvaluationKernel_iff _ _ _ 1 _).1 h p
  set a : Hol W := holRes hW (holRes inf_le_right holW)
  set v : Hol W := holRes hW (holRes inf_le_left holX)
  set e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) p
  set D := chartSectionDomain ellipticCurve d (op W) p
  have hpsource : p ∈ e.source := mem_extChartAt_source p
  have hy₀ : e p ∈ D := by
    refine ⟨mem_extChartAt_target p, ?_⟩
    change e.symm (e p) ∈ W
    rw [e.left_inv hpsource]
    exact hp
  have hDopen : IsOpen D := isOpen_chartSectionDomain _ _ _ _
  -- the derivative of `x` in the chart vanishes on `D`
  have hzero : ∀ y ∈ D, chartSectionDifferential ellipticCurve d (op W) p v y = 0 := by
    intro y hy
    have h1 := hker y hy
    rw [chartEvaluation_mk _ _ _ _ _ _ _ hy] at h1
    simp only [chartGeneratorEvaluation] at h1
    have hc : chartSection ellipticCurve d (op W) p a y ≠ 0 := by
      rw [chartSection_apply_of_mem _ _ _ _ _ hy]
      exact ellipticW_ne_zero_of_mem ⟨e.symm y, hW hy.2⟩
    have h2 := congrArg (fun f => (chartSection ellipticCurve d (op W) p a y)⁻¹ • f) h1
    simp only [inv_smul_smul₀ hc] at h2
    refine ContinuousLinearMap.ext fun vec => ?_
    have h3 := congrArg (fun f => f ![vec]) h2
    simpa [ContinuousAlternatingMap.wedgeCovectors_apply_eq_det] using h3
  -- so `x` is constant on a ball around `e p`
  set f := chartSection ellipticCurve d (op W) p v
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hDopen (e p) hy₀
  have hconst : ∀ y ∈ Metric.ball (e p) r, f y = f (e p) := by
    intro y hy
    refine (convex_ball _ _).is_const_of_fderivWithin_eq_zero
      (((chartSection_contDiffOn _ _ _ _ v).differentiableOn (by simp)).mono hball) ?_ hy
      (Metric.mem_ball_self hr)
    intro y' hy'
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hy', ← fderivWithin_of_isOpen hDopen (hball hy')]
    exact hzero y' (hball hy')
  -- three points of the ball
  have hd : 0 < d := by
    change 0 < TopologicalSpace.dim ellipticCurve.left
    rw [dim_ellipticCurve]; exact Nat.one_pos
  let i₀ : Fin d := ⟨0, hd⟩
  let v₀ : Fin d → ℂ := fun _ => 1
  have hv₀ : ‖v₀‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp [v₀]
  let pt : ℝ → Fin d → ℂ := fun t => e p + (t : ℂ) • v₀
  have hpt_mem : ∀ t : ℝ, |t| < r → pt t ∈ Metric.ball (e p) r := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [pt, add_sub_cancel_left]
    calc ‖(t : ℂ) • v₀‖ = |t| * ‖v₀‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hv₀ (abs_nonneg t)
      _ < r := by rw [mul_one]; exact ht
  have hpt_inj : ∀ s t : ℝ, pt s = pt t → s = t := by
    intro s t hst
    have := congrFun hst i₀
    simp only [pt, v₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, add_right_inj] at this
    exact_mod_cast this
  let q : ∀ t : ℝ, |t| < r → ellipticAffineOpen := fun t ht =>
    ⟨e.symm (pt t), (hW (hball (hpt_mem t ht)).2).1⟩
  have hq_x : ∀ t (ht : |t| < r), ellipticX (q t ht) = f (e p) := by
    intro t ht
    rw [← hconst _ (hpt_mem t ht)]
    show _ = chartSection ellipticCurve d (op W) p v (pt t)
    rw [chartSection_apply_of_mem _ _ _ _ _ (hball (hpt_mem t ht))]
    rfl
  have hq_inj : ∀ s t (hs : |s| < r) (ht : |t| < r), q s hs = q t ht → s = t := by
    intro s t hs ht hst
    apply hpt_inj
    have hst' : (q s hs).1 = (q t ht).1 := congrArg Subtype.val hst
    exact e.symm.injOn (hball (hpt_mem s hs)).1 (hball (hpt_mem t ht)).1 hst'
  have h0 : |(0 : ℝ)| < r := by simpa using hr
  have h1 : |r / 2| < r := by rw [abs_of_pos (by positivity)]; linarith
  have h2 : |r / 4| < r := by rw [abs_of_pos (by positivity)]; linarith
  exact ellipticX_fibre_three (a := q 0 h0) (b := q (r / 2) h1) (c := q (r / 4) h2)
    (fun h => by have := hq_inj 0 (r / 2) h0 h1 h; linarith)
    (fun h => by have := hq_inj 0 (r / 4) h0 h2 h; linarith)
    (fun h => by have := hq_inj (r / 2) (r / 4) h1 h2 h; linarith)
    ((hq_x 0 h0).trans (hq_x (r / 2) h1).symm) ((hq_x 0 h0).trans (hq_x (r / 4) h2).symm)

theorem toSheafify_ellipticFormOne_ne_zero :
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint ellipticCurve)))
      ellipticFormPresheaf).app (op ellipticOverlapOpen) ellipticFormOne ≠ 0 := by
  intro h0
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint ellipticCurve))
  let p := ellipticCurveChartMeet
  have hp : p ∈ ellipticOverlapOpen :=
    ⟨ellipticCurveChartMeet_mem, ellipticCurveChartMeet_mem_ellipticInfinityOpen⟩
  have h1 : TopCat.Presheaf.germ (sheafify J ellipticFormPresheaf) ellipticOverlapOpen p hp
      ((toSheafify J ellipticFormPresheaf).app _ ellipticFormOne) = 0 := by
    rw [h0, map_zero]
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply] at h1
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p AddCommGrpCat
    ellipticFormPresheaf
  have hinj : Function.Injective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat p).map (toSheafify J ellipticFormPresheaf)) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have h2 : TopCat.Presheaf.germ ellipticFormPresheaf ellipticOverlapOpen p hp ellipticFormOne =
      TopCat.Presheaf.germ ellipticFormPresheaf ellipticOverlapOpen p hp 0 :=
    hinj (h1.trans (map_zero _).symm |>.trans (congrArg _ (map_zero _)).symm)
  obtain ⟨W, hpW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq ellipticFormPresheaf p hp hp _ _ h2
  rw [map_zero] at hW
  exact ellipticFormOne_res_ne_zero iU.le p hpW hW

/-- **ω is nonzero.** -/
theorem ellipticOmega_ne_zero : ellipticOmega ≠ 0 := by
  intro h
  have h0 := ellipticOmega_res_cover 0
  rw [h, map_zero] at h0
  exact toSheafify_ellipticFormOne_ne_zero h0.symm

end Glue

end HodgeLadder.Tests
