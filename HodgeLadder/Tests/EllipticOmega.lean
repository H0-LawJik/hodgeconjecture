module

public import HodgeLadder.General.ContMDiffInv
public import HodgeLadder.Tests.EllipticCurveCoordinates
public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.HolomorphicDeRham
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# The holomorphic 1-form `dx / y` on the plane cubic

Rung `elliptic-omega` (sub-rung S5 of `elliptic-curve-holomorphic-form`,
`docs/sketches/elliptic-curve-holomorphic-form.md`). On the cubic `E : y²z = x³ − xz²` of
`plane-cubic-subscheme`, the form `ω = dx / y` is a global section of upstream's sheaf of
holomorphic 1-forms `holomorphicDeRhamSheaf ellipticCurve (dim E) 1`, and it is nonzero.

Upstream's sheaf is the sheafification of `U ↦ HolomorphicForm`, the Kähler 1-forms of the ring of
holomorphic functions `𝒪(U)` modulo the forms whose chart evaluations vanish
(`chartEvaluationKernel`). Its value at `⊤` is not the presheaf value at `⊤`, so `ω` is glued from
three local forms on the opens

* `V₁ = {z ≠ 0, y ≠ 0}` (`ellipticOverlapOpen`): `y⁻¹ dx`, written `w dx` with `w = z / y = y⁻¹`;
* `V₂ = {z ≠ 0, 3x² − 1 ≠ 0}` (`ellipticOpenTwo`): `2 (3x² − 1)⁻¹ dy`;
* `V₃ = {y ≠ 0, 1 + 2uw ≠ 0}` (`ellipticOpenThree`): `−2 (1 + 2uw)⁻¹ du`.

They cover `E(ℂ)` (`ellipticOverlapOpen_sup_sup`): a point with `z ≠ 0, y = 0` has `x³ = x`, so
`3x² − 1 ∈ {−1, 2}`, and the only point with `z = 0` is `[0 : 1 : 0]`, where `u = w = 0`. Since
`V₂ ⊓ V₃ ≤ V₁`, agreement is checked on opens of `V₁ ⊓ V₂` and `V₁ ⊓ V₃` only.

## Route

1. **Kähler identities** in any commutative `ℂ`-algebra (`kaehler_ellipticCurve`,
   `kaehler_ellipticTwo`, `kaehler_ellipticThree`): from `y² = x³ − x` and `w y = 1`,
   `2y dy = (3x² − 1) dx`, so `w dx = 2a dy` when `a (3x² − 1) = 1`; with `u = x w` also
   `dw = −w² dy`, `du = w dx + x dw` and `w dx = −2b du` when `b (1 + 2uw) = 1`. The constants are
   exact: `−2b du = −2b w (1 − x w² (3x² − 1) / 2) dx = w dx` because
   `−2 + (3x³ − x) w² = 1 + 2xw²` reduces to `3 y² w² = 3`. They hold before the quotient by
   `chartEvaluationKernel`.
2. **Restriction** of `[a dv]` along `V ≤ U` is `[a|_V d(v|_V)]` (`formClass_res`, upstream
   `formRestriction_mk`), and equal Kähler forms give equal classes (`formClass_eq`, through
   Mathlib's `exteriorPower.oneEquiv`). So the local forms agree on every open of the overlaps
   (`ellipticFormTwo_res`, `ellipticFormThree_res`), already in the presheaf.
3. **Gluing.** The images under `toSheafify` are compatible by naturality, and Mathlib's
   `TopCat.Sheaf.existsUnique_gluing'` glues them over `⊤`.
4. **Nonvanishing.** The stalk map of `toSheafify` is an isomorphism (Mathlib's
   `stalkFunctor_map_unit_toSheafify_isIso`), so if the germ of `ω` at `p ∈ V₁` vanished, `w dx`
   would lie in `chartEvaluationKernel` on an open `W ∋ p` (`TopCat.Presheaf.germ_eq`). Its
   evaluation in upstream's chart at `p` is `w · D(x ∘ e⁻¹)` with `w ≠ 0`, so `x ∘ e⁻¹` would have
   zero derivative on a ball around `e p` and be constant there (Mathlib's
   `Convex.is_const_of_fderivWithin_eq_zero`); three points of the ball give three distinct points
   of `E(ℂ)` with the same `x`, while a fibre of `x` has at most two points
   (`ellipticY_eq_or_eq_neg_of_ellipticX_eq`, `eq_of_ellipticX_eq_of_ellipticY_eq`). This uses
   `dim E = 1` only to have a nonzero vector in the model space.

## Signs and normalizations

No sign convention enters `ω ≠ 0`. The scalars `2` and `−2` of the local forms are load-bearing for
the gluing: they are the constants for which the forms agree with `y⁻¹ dx`, and the tests
`ellipticFormThree_wrongSign_ne` and `ellipticFormTwo_wrongScalar_ne` show that `+2 (1 + 2uw)⁻¹ du`
and `(3x² − 1)⁻¹ dy` disagree with `y⁻¹ dx` on every nonempty open of the overlaps, which are
nonempty (`ellipticCurveChartMeet ∈ V₁ ⊓ V₂`, `ellipticTestPoint ∈ V₁ ⊓ V₃`; the chart meet
`(i, 1 − i)` has `1 + 2uw = 0` and lies outside `V₃`). Row "Holomorphic form on E" of
`docs/conventions.md`.

## Main definitions

* `HodgeLadder.Tests.Hol`, `holRes`, `toEH`, `holX`, `holY`, `holU`, `holW`, `formClass`
* `HodgeLadder.Tests.ellipticCoeffTwo`, `ellipticCoeffThree`, `ellipticOpenTwo`,
  `ellipticOpenThree`, `ellipticInvTwo`, `ellipticInvThree`
* `HodgeLadder.Tests.ellipticFormOne`, `ellipticFormTwo`, `ellipticFormThree`, `ellipticCover`,
  `ellipticLocalForm`, `ellipticLocalSection`
* `HodgeLadder.Tests.ellipticOmega`: the glued global section
* `HodgeLadder.Tests.ellipticTestPoint`

## Main results

* `HodgeLadder.Tests.kaehler_ellipticCurve`, `kaehler_ellipticTwo`, `kaehler_ellipticThree`
* `HodgeLadder.Tests.ellipticOverlapOpen_sup_sup`, `top_le_iSup_ellipticCover`
* `HodgeLadder.Tests.formClass_res`, `formClass_eq`, `formClass_add`, `formClass_eq_zero_iff`
* `HodgeLadder.Tests.ellipticFormTwo_res`, `ellipticFormThree_res`,
  `ellipticLocalSection_compatible`
* `HodgeLadder.Tests.ellipticOmega_res`: the restriction to `V₁` is `toSheafify` of the class of
  `w dx`, spelled with `ellipticResInfinity ellipticW` and `ellipticResAffine ellipticX`;
  `ellipticOmega_res_cover` on all three opens
* `HodgeLadder.Tests.formClass_holX_ne_zero`, `germ_ellipticOmega_ne_zero` (the germ of `ω` at
  every point of `V₁` is nonzero), `ellipticOmega_ne_zero`
* `HodgeLadder.Tests.ellipticFormThree_wrongSign_ne`, `ellipticFormTwo_wrongScalar_ne`,
  `ellipticCurveChartMeet_mem_inf_two`, `ellipticTestPoint_mem_inf_three`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff

namespace HodgeLadder.Tests

section Kaehler

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- **The curve relation in Kähler forms.** In a commutative `ℂ`-algebra, `y² = x³ − x` gives
`2y dy = (3x² − 1) dx` in `Ω[A⁄ℂ]`. -/
theorem kaehler_ellipticCurve (x y : A) (hy : y ^ 2 = x ^ 3 - x) :
    (2 * y) • KaehlerDifferential.D ℂ A y = (3 * x ^ 2 - 1) • KaehlerDifferential.D ℂ A x := by
  have h := congrArg (KaehlerDifferential.D ℂ A)
    (show y * y = x * (x * x) - x by linear_combination hy)
  simp only [Derivation.leibniz, map_sub] at h
  linear_combination (norm := module) h

/-- **Agreement on `V₁ ⊓ V₂`.** With `y² = x³ − x`, `w y = 1` and `a (3x² − 1) = 1`:
`w dx = 2a dy`, the constant `2` exact. -/
theorem kaehler_ellipticTwo (x y w a : A) (hy : y ^ 2 = x ^ 3 - x) (hw : w * y = 1)
    (ha : a * (3 * x ^ 2 - 1) = 1) :
    w • KaehlerDifferential.D ℂ A x = (2 * a) • KaehlerDifferential.D ℂ A y := by
  have h1 := kaehler_ellipticCurve x y hy
  linear_combination (norm := module) -(a * w) • h1 +
    hw • ((2 * a) • KaehlerDifferential.D ℂ A y) - ha • (w • KaehlerDifferential.D ℂ A x)

/-- **Agreement on `V₁ ⊓ V₃`.** With `y² = x³ − x`, `w y = 1`, `x w = u` and
`b (1 + 2uw) = 1`: `w dx = −2b du`, the constant `−2` exact. -/
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

/-- Holomorphic functions on an open of `E(ℂ)` in upstream's spelling
`OpenHolomorphicFunctions`, the coefficient ring of `HolomorphicForm`. It is `EllipticHolomorphic`
by definition (`ellipticHolomorphic_eq_openHolomorphicFunctions`). -/
abbrev Hol (V : Opens (ComplexPoint ellipticCurve)) :=
  OpenHolomorphicFunctions ellipticCurve (TopologicalSpace.dim ellipticCurve.left) (op V)

/-- Restriction of holomorphic functions along `V ≤ U`: upstream's
`holomorphicRestrictionAlgHom`. -/
abbrev holRes {U V : Opens (ComplexPoint ellipticCurve)} (h : V ≤ U) : Hol U →ₐ[ℂ] Hol V :=
  holomorphicRestrictionAlgHom ellipticCurve _ (homOfLE h).op

/-- A holomorphic function in upstream's spelling, read as a `C^ω` map (the identity). -/
abbrev toEH {V : Opens (ComplexPoint ellipticCurve)} (f : Hol V) : EllipticHolomorphic V := f

/-- Restriction is transitive, by definition. -/
theorem holRes_holRes {U V W : Opens (ComplexPoint ellipticCurve)} (h : V ≤ U) (h' : W ≤ V)
    (f : Hol U) : holRes h' (holRes h f) = holRes (h'.trans h) f := rfl

/-- The value of a restriction. -/
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

/-- The function `3x² − 1` on `z ≠ 0`. -/
def ellipticCoeffTwo : Hol ellipticAffineOpen := 3 * holX ^ 2 - 1

/-- The function `1 + 2uw` on `y ≠ 0`. -/
def ellipticCoeffThree : Hol ellipticInfinityOpen :=
  1 + 2 * holU * holW

/-- The open `V₂ = {z ≠ 0, 3x² − 1 ≠ 0}`. -/
def ellipticOpenTwo : Opens (ComplexPoint ellipticCurve) :=
  ⟨Subtype.val '' {z : ellipticAffineOpen | toEH ellipticCoeffTwo z ≠ 0},
    ellipticAffineOpen.isOpen.isOpenMap_subtype_val _
      (isOpen_ne_fun (toEH ellipticCoeffTwo).contMDiff.continuous continuous_const)⟩

/-- The open `V₃ = {y ≠ 0, 1 + 2uw ≠ 0}`. -/
def ellipticOpenThree : Opens (ComplexPoint ellipticCurve) :=
  ⟨Subtype.val '' {z : ellipticInfinityOpen | toEH ellipticCoeffThree z ≠ 0},
    ellipticInfinityOpen.isOpen.isOpenMap_subtype_val _
      (isOpen_ne_fun (toEH ellipticCoeffThree).contMDiff.continuous continuous_const)⟩

/-- Membership in `V₂`. -/
theorem mem_ellipticOpenTwo {p : ComplexPoint ellipticCurve} :
    p ∈ ellipticOpenTwo ↔ ∃ h : p ∈ ellipticAffineOpen, toEH ellipticCoeffTwo ⟨p, h⟩ ≠ 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨h, hp⟩
    exact ⟨⟨p, h⟩, hp, rfl⟩

/-- Membership in `V₃`. -/
theorem mem_ellipticOpenThree {p : ComplexPoint ellipticCurve} :
    p ∈ ellipticOpenThree ↔
      ∃ h : p ∈ ellipticInfinityOpen, toEH ellipticCoeffThree ⟨p, h⟩ ≠ 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨h, hp⟩
    exact ⟨⟨p, h⟩, hp, rfl⟩

/-- `V₂` lies in the chart `z ≠ 0`. -/
theorem ellipticOpenTwo_le : ellipticOpenTwo ≤ ellipticAffineOpen :=
  fun _ hp => (mem_ellipticOpenTwo.mp hp).1

/-- `V₃` lies in the chart `y ≠ 0`. -/
theorem ellipticOpenThree_le : ellipticOpenThree ≤ ellipticInfinityOpen :=
  fun _ hp => (mem_ellipticOpenThree.mp hp).1

/-- `V₂ ⊓ V₃ ≤ V₁`. -/
theorem ellipticOpenTwo_inf_ellipticOpenThree_le :
    ellipticOpenTwo ⊓ ellipticOpenThree ≤ ellipticOverlapOpen :=
  inf_le_inf ellipticOpenTwo_le ellipticOpenThree_le

/-- The value of `3x² − 1`. -/
theorem ellipticCoeffTwo_apply (z : ellipticAffineOpen) :
    toEH ellipticCoeffTwo z = 3 * ellipticX z ^ 2 - 1 := by
  change ContMDiffMap.evalRingHom z (3 * ellipticX ^ 2 - 1) = _
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one]
  rfl

/-- The value of `1 + 2uw`. -/
theorem ellipticCoeffThree_apply (z : ellipticInfinityOpen) :
    toEH ellipticCoeffThree z = 1 + 2 * ellipticU z * ellipticW z := by
  change ContMDiffMap.evalRingHom z (1 + 2 * ellipticU * ellipticW) = _
  simp only [map_add, map_mul, map_ofNat, map_one]
  rfl

/-- **The cover** `V₁ ⊔ V₂ ⊔ V₃ = E(ℂ)`. A point with `z ≠ 0, y = 0` has `x³ = x`, so
`3x² − 1 ≠ 0`; the point `[0 : 1 : 0]` has `1 + 2uw = 1`. -/
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

/-- Upstream's presheaf of holomorphic 1-forms on `E(ℂ)`, `U ↦ HolomorphicForm … U 1`. -/
abbrev ellipticFormPresheaf :=
  holomorphicDeRhamPresheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left) 1

/-- Upstream's sheaf of holomorphic 1-forms on `E(ℂ)`, the sheafification of
`ellipticFormPresheaf`. -/
abbrev ellipticFormSheaf :=
  holomorphicDeRhamSheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left) 1

/-- The class of the Kähler form `a dv` in `HolomorphicForm`, the presheaf value. -/
def formClass {V : Opens (ComplexPoint ellipticCurve)} (a v : Hol V) :
    ellipticFormPresheaf.obj (op V) :=
  Submodule.Quotient.mk (Algebra.DeRham.mk ℂ (Hol V) 1 a ![v])

/-- Restriction of `[a dv]` is `[a|_V d(v|_V)]`. -/
theorem formClass_res {U V : Opens (ComplexPoint ellipticCurve)} (h : V ≤ U) (a v : Hol U) :
    ellipticFormPresheaf.map (homOfLE h).op (formClass a v) =
      formClass (holRes h a) (holRes h v) := by
  show Submodule.Quotient.mk (formRestriction _ _ _ 1 _) = _
  rw [formRestriction_mk]
  rfl

/-- Equal Kähler forms `a dv = b dw` in `Ω[𝒪(V)⁄ℂ]` have equal classes. -/
theorem formClass_eq {V : Opens (ComplexPoint ellipticCurve)} {a v b w : Hol V}
    (h : a • KaehlerDifferential.D ℂ (Hol V) v = b • KaehlerDifferential.D ℂ (Hol V) w) :
    formClass a v = formClass b w := by
  refine congrArg _ ((exteriorPower.oneEquiv (Hol V) Ω[Hol V⁄ℂ]).injective ?_)
  simp only [Algebra.DeRham.mk, Algebra.DeRham.exact, map_smul, exteriorPower.oneEquiv_ιMulti]
  exact h

/-- The class is additive in the coefficient. -/
theorem formClass_add {V : Opens (ComplexPoint ellipticCurve)} (a b v : Hol V) :
    formClass a v + formClass b v = formClass (a + b) v := by
  simp only [formClass, Algebra.DeRham.mk, add_smul]
  rfl

/-- `[a dv] = 0` exactly when the chart evaluations of `a dv` vanish. -/
theorem formClass_eq_zero_iff {V : Opens (ComplexPoint ellipticCurve)} (a v : Hol V) :
    formClass a v = 0 ↔ Algebra.DeRham.mk ℂ (Hol V) 1 a ![v] ∈
      chartEvaluationKernel ellipticCurve (TopologicalSpace.dim ellipticCurve.left) (op V) 1 :=
  Submodule.Quotient.mk_eq_zero _

/-- `y² = x³ − x` restricted to an open of `z ≠ 0`. -/
theorem holY_sq_res {W : Opens (ComplexPoint ellipticCurve)} (h : W ≤ ellipticAffineOpen) :
    holRes h holY ^ 2 = holRes h holX ^ 3 - holRes h holX := by
  rw [← map_pow, ← map_pow, ← map_sub]
  exact congrArg (holRes h) ellipticY_sq

/-- `w · y = 1` restricted to an open of the overlap. -/
theorem holW_mul_holY_res {W : Opens (ComplexPoint ellipticCurve)}
    (h : W ≤ ellipticOverlapOpen) :
    holRes (h.trans inf_le_right) holW * holRes (h.trans inf_le_left) holY = 1 := by
  have := congrArg (holRes h) (show (holRes inf_le_right holW : Hol ellipticOverlapOpen) *
    holRes inf_le_left holY = 1 from ellipticW_mul_ellipticY)
  rwa [map_mul, map_one, holRes_holRes, holRes_holRes] at this

/-- `x · w = u` restricted to an open of the overlap. -/
theorem holX_mul_holW_res {W : Opens (ComplexPoint ellipticCurve)}
    (h : W ≤ ellipticOverlapOpen) :
    holRes (h.trans inf_le_left) holX * holRes (h.trans inf_le_right) holW =
      holRes (h.trans inf_le_right) holU := by
  have := congrArg (holRes h) (show (holRes inf_le_left holX : Hol ellipticOverlapOpen) *
    holRes inf_le_right holW = holRes inf_le_right holU from ellipticX_mul_ellipticW)
  rwa [map_mul, holRes_holRes, holRes_holRes, holRes_holRes] at this

/-- `3x² − 1` vanishes nowhere on `V₂`. -/
theorem ellipticCoeffTwo_ne_zero (z : ellipticOpenTwo) :
    toEH (holRes ellipticOpenTwo_le ellipticCoeffTwo) z ≠ 0 := by
  obtain ⟨h, hne⟩ := mem_ellipticOpenTwo.mp z.2
  exact hne

/-- `1 + 2uw` vanishes nowhere on `V₃`. -/
theorem ellipticCoeffThree_ne_zero (z : ellipticOpenThree) :
    toEH (holRes ellipticOpenThree_le ellipticCoeffThree) z ≠ 0 := by
  obtain ⟨h, hne⟩ := mem_ellipticOpenThree.mp z.2
  exact hne

/-- `(3x² − 1)⁻¹` on `V₂`, by `HodgeLadder.contMDiffMapInv₀`. -/
def ellipticInvTwo : Hol ellipticOpenTwo :=
  contMDiffMapInv₀ (toEH (holRes ellipticOpenTwo_le ellipticCoeffTwo)) ellipticCoeffTwo_ne_zero

/-- `(1 + 2uw)⁻¹` on `V₃`, by `HodgeLadder.contMDiffMapInv₀`. -/
def ellipticInvThree : Hol ellipticOpenThree :=
  contMDiffMapInv₀ (toEH (holRes ellipticOpenThree_le ellipticCoeffThree))
    ellipticCoeffThree_ne_zero

/-- `(3x² − 1)⁻¹ · (3x² − 1) = 1` on `V₂`. -/
theorem ellipticInvTwo_mul :
    ellipticInvTwo * holRes ellipticOpenTwo_le ellipticCoeffTwo = 1 :=
  contMDiffMapInv₀_mul _ _

/-- `(1 + 2uw)⁻¹ · (1 + 2uw) = 1` on `V₃`. -/
theorem ellipticInvThree_mul :
    ellipticInvThree * holRes ellipticOpenThree_le ellipticCoeffThree = 1 :=
  contMDiffMapInv₀_mul _ _

/-- **`y⁻¹ dx` on `V₁`**, written `w dx` with `w = z / y = y⁻¹` (`ellipticW_eq_inv`). -/
def ellipticFormOne : ellipticFormPresheaf.obj (op ellipticOverlapOpen) :=
  formClass (holRes inf_le_right holW) (holRes inf_le_left holX)

/-- **`2 (3x² − 1)⁻¹ dy` on `V₂`.** -/
def ellipticFormTwo : ellipticFormPresheaf.obj (op ellipticOpenTwo) :=
  formClass (2 * ellipticInvTwo) (holRes ellipticOpenTwo_le holY)

/-- **`−2 (1 + 2uw)⁻¹ du` on `V₃`.** -/
def ellipticFormThree : ellipticFormPresheaf.obj (op ellipticOpenThree) :=
  formClass (-2 * ellipticInvThree) (holRes ellipticOpenThree_le holU)

/-- **Agreement on `V₁ ⊓ V₂`**: on every open `W` of `V₁ ⊓ V₂`, `2 (3x² − 1)⁻¹ dy = y⁻¹ dx`, by
`kaehler_ellipticTwo`. -/
theorem ellipticFormTwo_res {W : Opens (ComplexPoint ellipticCurve)}
    (h1 : W ≤ ellipticOverlapOpen) (h2 : W ≤ ellipticOpenTwo) :
    ellipticFormPresheaf.map (homOfLE h2).op ellipticFormTwo =
      ellipticFormPresheaf.map (homOfLE h1).op ellipticFormOne := by
  rw [ellipticFormTwo, ellipticFormOne, formClass_res, formClass_res]
  refine (formClass_eq ?_).symm
  have ha := congrArg (holRes h2) ellipticInvTwo_mul
  rw [map_mul, map_one, holRes_holRes, ellipticCoeffTwo, map_sub, map_mul, map_pow, map_ofNat,
    map_one] at ha
  rw [map_mul, map_ofNat, holRes_holRes, holRes_holRes, holRes_holRes]
  exact kaehler_ellipticTwo _ _ _ _ (holY_sq_res _) (holW_mul_holY_res h1) ha

/-- **Agreement on `V₁ ⊓ V₃`**: on every open `W` of `V₁ ⊓ V₃`, `−2 (1 + 2uw)⁻¹ du = y⁻¹ dx`, by
`kaehler_ellipticThree`. -/
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

end Forms

section Nonvanishing

/-- No three distinct points of `z ≠ 0` share the value of `x`. -/
theorem ellipticX_fibre_three {a b c : ellipticAffineOpen} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (h1 : ellipticX a = ellipticX b) (h2 : ellipticX a = ellipticX c) : False := by
  rcases ellipticY_eq_or_eq_neg_of_ellipticX_eq h1 with hb | hb
  · exact hab (eq_of_ellipticX_eq_of_ellipticY_eq h1 hb)
  rcases ellipticY_eq_or_eq_neg_of_ellipticX_eq h2 with hc | hc
  · exact hac (eq_of_ellipticX_eq_of_ellipticY_eq h2 hc)
  have hy : ellipticY b = ellipticY c := neg_injective (hb.symm.trans hc)
  exact hbc (eq_of_ellipticX_eq_of_ellipticY_eq (h1.symm.trans h2) hy)

/-- On the overlap, `w` vanishes nowhere. -/
theorem ellipticW_ne_zero_of_mem (z : ellipticOverlapOpen) :
    ellipticResInfinity ellipticW z ≠ 0 := by
  rw [ellipticW_eq_inv]
  exact one_div_ne_zero (ellipticY_ne_zero_of_mem z)

/-- **`a dx ≠ 0`.** On a nonempty open `W` of the overlap, the class of `a dx` is nonzero for every
nowhere-vanishing `a`: its evaluation in upstream's chart at `p ∈ W` is `a · D(x ∘ e⁻¹)`, and if
it vanished, `x` would be constant on the image of a ball, which holds three distinct points of
`E(ℂ)`, while a fibre of `x` has at most two. -/
theorem formClass_holX_ne_zero {W : Opens (ComplexPoint ellipticCurve)}
    (hW : W ≤ ellipticOverlapOpen) (p : ComplexPoint ellipticCurve) (hp : p ∈ W) (a : Hol W)
    (ha : ∀ z, toEH a z ≠ 0) :
    formClass a (holRes (hW.trans inf_le_left) holX) ≠ 0 := by
  set d := TopologicalSpace.dim ellipticCurve.left
  intro h
  rw [formClass_eq_zero_iff] at h
  have hker := (mem_chartEvaluationKernel_iff _ _ _ 1 _).1 h p
  set v : Hol W := holRes (hW.trans inf_le_left) holX
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
      exact ha _
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
  -- three points of the ball, on the real line through `e p` in the direction `(1, …, 1)`
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

/-- The restriction of `y⁻¹ dx` to a nonempty open of `V₁` is nonzero. -/
theorem ellipticFormOne_res_ne_zero {W : Opens (ComplexPoint ellipticCurve)}
    (hW : W ≤ ellipticOverlapOpen) (p : ComplexPoint ellipticCurve) (hp : p ∈ W) :
    ellipticFormPresheaf.map (homOfLE hW).op ellipticFormOne ≠ 0 := by
  rw [ellipticFormOne, formClass_res]
  exact formClass_holX_ne_zero hW p hp _ fun z => ellipticW_ne_zero_of_mem ⟨z.1, hW z.2⟩

end Nonvanishing

section Glue

/-- The cover `V₁, V₂, V₃` of `E(ℂ)`. -/
def ellipticCover : Fin 3 → Opens (ComplexPoint ellipticCurve) :=
  ![ellipticOverlapOpen, ellipticOpenTwo, ellipticOpenThree]

/-- The three local forms `y⁻¹ dx`, `2 (3x² − 1)⁻¹ dy`, `−2 (1 + 2uw)⁻¹ du`. -/
def ellipticLocalForm : ∀ i, ellipticFormPresheaf.obj (op (ellipticCover i))
  | 0 => ellipticFormOne
  | 1 => ellipticFormTwo
  | 2 => ellipticFormThree

/-- Each local form restricts to `y⁻¹ dx` on every open of its meet with `V₁`. -/
theorem ellipticLocalForm_res (i : Fin 3) {W : Opens (ComplexPoint ellipticCurve)}
    (hi : W ≤ ellipticCover i) (h1 : W ≤ ellipticOverlapOpen) :
    ellipticFormPresheaf.map (homOfLE hi).op (ellipticLocalForm i) =
      ellipticFormPresheaf.map (homOfLE h1).op ellipticFormOne := by
  fin_cases i
  · rfl
  · exact ellipticFormTwo_res h1 hi
  · exact ellipticFormThree_res h1 hi

/-- Two distinct opens of the cover meet inside `V₁`. -/
theorem ellipticCover_inf_le {i j : Fin 3} (hij : i ≠ j) :
    ellipticCover i ⊓ ellipticCover j ≤ ellipticOverlapOpen := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact inf_le_left
    | exact inf_le_right
    | exact ellipticOpenTwo_inf_ellipticOpenThree_le
    | exact (inf_comm _ _).le.trans ellipticOpenTwo_inf_ellipticOpenThree_le

/-- The cover covers `⊤`. -/
theorem top_le_iSup_ellipticCover : ⊤ ≤ iSup ellipticCover := by
  intro p _
  have hp : p ∈ ellipticOverlapOpen ⊔ ellipticOpenTwo ⊔ ellipticOpenThree := by
    rw [ellipticOverlapOpen_sup_sup]; trivial
  rcases hp with (h | h) | h
  · exact Opens.mem_iSup.mpr ⟨0, h⟩
  · exact Opens.mem_iSup.mpr ⟨1, h⟩
  · exact Opens.mem_iSup.mpr ⟨2, h⟩

/-- The local forms as sections of the sheaf: their images under `toSheafify`. -/
def ellipticLocalSection (i : Fin 3) :
    ToType (ellipticFormSheaf.presheaf.obj (op (ellipticCover i))) :=
  (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint ellipticCurve)))
    ellipticFormPresheaf).app _ (ellipticLocalForm i)

/-- The local sections are compatible: naturality of `toSheafify` and agreement in the
presheaf. -/
theorem ellipticLocalSection_compatible :
    TopCat.Presheaf.IsCompatible ellipticFormSheaf.presheaf ellipticCover
      ellipticLocalSection := by
  intro i j
  simp only [ellipticLocalSection]
  erw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  congr 1
  by_cases hij : i = j
  · subst hij; rfl
  · exact (ellipticLocalForm_res i inf_le_left (ellipticCover_inf_le hij)).trans
      (ellipticLocalForm_res j inf_le_right (ellipticCover_inf_le hij)).symm

/-- **The holomorphic 1-form `ω = dx / y` on `E(ℂ)`**: a global section of upstream's sheaf of
holomorphic 1-forms, glued from `ellipticLocalSection` by Mathlib's
`TopCat.Sheaf.existsUnique_gluing'`. -/
def ellipticOmega :
    ToType ((holomorphicDeRhamSheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left) 1
      ).presheaf.obj (op ⊤)) :=
  (ellipticFormSheaf.existsUnique_gluing' ellipticCover ⊤ (fun _ => homOfLE le_top)
    top_le_iSup_ellipticCover ellipticLocalSection ellipticLocalSection_compatible).exists.choose

/-- `ω` restricts to the three local sections. -/
theorem ellipticOmega_res_cover (i : Fin 3) :
    ellipticFormSheaf.presheaf.map (homOfLE le_top).op ellipticOmega = ellipticLocalSection i :=
  (ellipticFormSheaf.existsUnique_gluing' ellipticCover ⊤ (fun _ => homOfLE le_top)
    top_le_iSup_ellipticCover ellipticLocalSection
    ellipticLocalSection_compatible).exists.choose_spec i

/-- **Restriction pin.** On `V₁ = {z ≠ 0, y ≠ 0}`, `ω` is the image under `toSheafify` of the class
of `w dx = y⁻¹ dx` (`Algebra.DeRham.mk ℂ _ 1 w ![x]`, with `w = y⁻¹` by `ellipticW_eq_inv`). -/
theorem ellipticOmega_res :
    (holomorphicDeRhamSheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left) 1).presheaf.map
        (homOfLE (le_top : ellipticOverlapOpen ≤ ⊤)).op ellipticOmega =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint ellipticCurve)))
        (holomorphicDeRhamPresheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left) 1)).app
        (op ellipticOverlapOpen)
        (Submodule.Quotient.mk (Algebra.DeRham.mk ℂ _ 1
          (ellipticResInfinity ellipticW) ![ellipticResAffine ellipticX])) :=
  ellipticOmega_res_cover 0

/-- The germ of `toSheafify (y⁻¹ dx)` at any point of `V₁` is nonzero: the stalk map of
`toSheafify` is an isomorphism, and `ellipticFormOne_res_ne_zero`. -/
theorem germ_toSheafify_ellipticFormOne_ne_zero (p : ComplexPoint ellipticCurve)
    (hp : p ∈ ellipticOverlapOpen) :
    TopCat.Presheaf.germ
        (sheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint ellipticCurve)))
          ellipticFormPresheaf) ellipticOverlapOpen p hp
        ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint ellipticCurve)))
          ellipticFormPresheaf).app (op ellipticOverlapOpen) ellipticFormOne) ≠ 0 := by
  intro h1
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint ellipticCurve))
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

/-- **The germ of `ω` at every point of `V₁` is nonzero.** -/
theorem germ_ellipticOmega_ne_zero (p : ComplexPoint ellipticCurve)
    (hp : p ∈ ellipticOverlapOpen) :
    TopCat.Presheaf.germ ellipticFormSheaf.presheaf ⊤ p trivial ellipticOmega ≠ 0 := by
  have h0 : ellipticFormSheaf.presheaf.map (homOfLE (le_top : ellipticOverlapOpen ≤ ⊤)).op
      ellipticOmega = _ := ellipticOmega_res_cover 0
  rw [← TopCat.Presheaf.germ_res_apply ellipticFormSheaf.presheaf (homOfLE le_top) p hp, h0]
  exact germ_toSheafify_ellipticFormOne_ne_zero p hp

/-- **`ω ≠ 0`.** Its germ at `[i : 1 − i : 1] ∈ V₁` is nonzero. -/
theorem ellipticOmega_ne_zero : ellipticOmega ≠ 0 := by
  intro h
  apply germ_ellipticOmega_ne_zero ellipticCurveChartMeet
    ⟨ellipticCurveChartMeet_mem, ellipticCurveChartMeet_mem_ellipticInfinityOpen⟩
  rw [h, map_zero]

end Glue

section Tests

/-- The point `(2, √6)` of `y² = x³ − x`. -/
def ellipticTestPoint : affineCurve :=
  ⟨(2, (Real.sqrt 6 : ℂ)), by
    show ((Real.sqrt 6 : ℝ) : ℂ) ^ 2 = 2 ^ 3 - 2
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num⟩

/-- **Nonvacuity of `V₁ ⊓ V₂`.** `[i : 1 − i : 1]` has `y = 1 − i ≠ 0` and `3x² − 1 = −4`. -/
theorem ellipticCurveChartMeet_mem_inf_two :
    ellipticCurveChartMeet ∈ ellipticOverlapOpen ⊓ ellipticOpenTwo := by
  refine ⟨⟨ellipticCurveChartMeet_mem, ellipticCurveChartMeet_mem_ellipticInfinityOpen⟩,
    mem_ellipticOpenTwo.mpr ⟨ellipticCurveChartMeet_mem, ?_⟩⟩
  rw [ellipticCoeffTwo_apply, ellipticXY_chartMeet.1, Complex.I_sq]
  norm_num

/-- **Nonvacuity of `V₁ ⊓ V₃`.** `(x, y) = (2, √6)` has `1 + 2uw = 1 + 2x / y² = 5 / 3`. -/
theorem ellipticTestPoint_mem_inf_three :
    affinePoint ellipticTestPoint ∈ ellipticOverlapOpen ⊓ ellipticOpenThree := by
  have hs : ((Real.sqrt 6 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have hI : affinePoint ellipticTestPoint ∈ ellipticInfinityOpen :=
    (affinePoint_mem_ellipticInfinityOpen_iff _).mpr hs
  refine ⟨⟨affinePoint_mem _, hI⟩, mem_ellipticOpenThree.mpr ⟨hI, ?_⟩⟩
  have huw := ellipticInfinityHomeomorph_of_mem ⟨_, affinePoint_mem ellipticTestPoint⟩ hI
  rw [ellipticAffineHomeomorph_affinePoint] at huw
  rw [ellipticCoeffThree_apply, ellipticU_apply, ellipticW_apply, huw]
  show 1 + 2 * (2 / ((Real.sqrt 6 : ℝ) : ℂ)) * (1 / ((Real.sqrt 6 : ℝ) : ℂ)) ≠ 0
  have h6 : ((Real.sqrt 6 : ℝ) : ℂ) ^ 2 = 6 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have : (1 : ℂ) + 2 * (2 / ((Real.sqrt 6 : ℝ) : ℂ)) * (1 / ((Real.sqrt 6 : ℝ) : ℂ)) =
      1 + 4 / ((Real.sqrt 6 : ℝ) : ℂ) ^ 2 := by ring
  rw [this, h6]
  norm_num

/-- **Sign test on `V₃`.** The form with the opposite sign, `+2 (1 + 2uw)⁻¹ du`, disagrees with
`y⁻¹ dx` on every nonempty open of `V₁ ⊓ V₃`: the gluing needs the `−2`. -/
theorem ellipticFormThree_wrongSign_ne {W : Opens (ComplexPoint ellipticCurve)}
    (h1 : W ≤ ellipticOverlapOpen) (h3 : W ≤ ellipticOpenThree) (p : ComplexPoint ellipticCurve)
    (hp : p ∈ W) :
    ellipticFormPresheaf.map (homOfLE h3).op
        (formClass (2 * ellipticInvThree) (holRes ellipticOpenThree_le holU)) ≠
      ellipticFormPresheaf.map (homOfLE h1).op ellipticFormOne := by
  intro hwrong
  have hgood := ellipticFormThree_res h1 h3
  rw [ellipticFormThree, formClass_res] at hgood
  rw [formClass_res] at hwrong
  rw [ellipticFormOne, formClass_res] at hgood hwrong
  have hsum := formClass_add (holRes h3 (2 * ellipticInvThree))
    (holRes h3 (-2 * ellipticInvThree)) (holRes h3 (holRes ellipticOpenThree_le holU))
  rw [hwrong, hgood, formClass_add, ← map_add (holRes h3), show (2 : Hol ellipticOpenThree) *
    ellipticInvThree + -2 * ellipticInvThree = 0 by ring, map_zero] at hsum
  have hzero : formClass (0 : Hol W) (holRes h3 (holRes ellipticOpenThree_le holU)) = 0 := by
    rw [formClass_eq_zero_iff, Algebra.DeRham.mk, zero_smul]
    exact Submodule.zero_mem _
  rw [hzero] at hsum
  refine formClass_holX_ne_zero h1 p hp _ (fun z => ?_) hsum
  change ellipticResInfinity ellipticW ⟨z.1, h1 z.2⟩ + ellipticResInfinity ellipticW ⟨z.1, h1 z.2⟩ ≠ 0
  rw [← two_mul]
  exact mul_ne_zero two_ne_zero (ellipticW_ne_zero_of_mem _)

/-- **Scalar test on `V₂`.** The form without the factor `2`, `(3x² − 1)⁻¹ dy`, disagrees with
`y⁻¹ dx` on every nonempty open of `V₁ ⊓ V₂`. -/
theorem ellipticFormTwo_wrongScalar_ne {W : Opens (ComplexPoint ellipticCurve)}
    (h1 : W ≤ ellipticOverlapOpen) (h2 : W ≤ ellipticOpenTwo) (p : ComplexPoint ellipticCurve)
    (hp : p ∈ W) :
    ellipticFormPresheaf.map (homOfLE h2).op
        (formClass ellipticInvTwo (holRes ellipticOpenTwo_le holY)) ≠
      ellipticFormPresheaf.map (homOfLE h1).op ellipticFormOne := by
  intro hwrong
  have hgood := ellipticFormTwo_res h1 h2
  rw [ellipticFormTwo, formClass_res, map_mul, map_ofNat, two_mul, ← formClass_add,
    ← formClass_res, hwrong] at hgood
  have h0 := ellipticFormOne_res_ne_zero h1 p hp
  exact h0 (by simpa using hgood)

end Tests

end HodgeLadder.Tests
