module

public import HodgeLadder.Hodge.WedgeDescends
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicPoincare

/-!
# The wedge product on upstream's holomorphic forms

Rung `wedge-presheaf` (front `cup`, first third of the former `wedge-sheaf-map`). Upstream defines
the holomorphic `p`-forms on an analytic open `U ⊆ X(ℂ)` as the complex quotient
`HolomorphicForm X d U p = Form ℂ 𝒪(U) p ⧸ chartEvaluationKernel X d U p`, with restriction
`holomorphicFormRestriction` and differential `holomorphicFormDifferential` induced from the
algebraic ones. This file descends the wedge product `HodgeLadder.formWedge` (multiplication in
`⋀_{𝒪(U)} Ω_{𝒪(U)/ℂ}`, first factor on the left) to a `ℂ`-bilinear map on these quotients, by
`LinearMap.liftQ₂` and the two sides of the checked `HodgeLadder.wedgeDescends`.

The kernel is a `ℂ`-submodule upstream, so `HolomorphicForm X d U p` is a `ℂ`-module and the
wedge is `ℂ`-bilinear; an `𝒪(U)`-module structure is not available at the pin.

## Degrees

`holomorphicFormDifferential` lands in degree `n + 1`. On `θ ∧ η` with `θ` of degree `p` and `η`
of degree `q`, the three terms of the Leibniz rule live in degrees `(p + q) + 1`, `(p + 1) + q`
and `p + (q + 1)`. The first and the third agree definitionally; the second needs the transport
`HodgeLadder.holomorphicFormCast` along `Nat.add_right_comm p 1 q`, which acts on
representatives as the identity of the exterior algebra (`holomorphicFormCast_mk`).

## Main definitions

* `HodgeLadder.formWedgeBilin`: `formWedge` as an `R`-bilinear map of algebraic forms
* `HodgeLadder.holomorphicWedge`: the wedge
  `HolomorphicForm X d U p →ₗ[ℂ] HolomorphicForm X d U q →ₗ[ℂ] HolomorphicForm X d U (p + q)`
* `HodgeLadder.holomorphicFormCast`: transport of holomorphic forms along an equality of degrees

## Main results

* `HodgeLadder.holomorphicWedge_mk`: on representatives the wedge is `formWedge` (by `rfl`)
* `HodgeLadder.map_formWedge`: `Algebra.DeRham.map` along an algebra map is multiplicative
* `HodgeLadder.holomorphicFormRestriction_holomorphicWedge`: naturality under restriction;
  `HodgeLadder.holomorphicWedge_compr₂_restriction`, the same as an equation of bilinear maps
* `HodgeLadder.holomorphicFormDifferential_holomorphicWedge`: the Leibniz rule
  `d(θ ∧ η) = dθ ∧ η + (−1)^p θ ∧ dη`, with Mathlib's Koszul sign as in `formWedge_differential`
* `HodgeLadder.holomorphicWedge_ofConstant_left`, `HodgeLadder.holomorphicWedge_ofConstant_right`:
  the constant zero-form `c` acts by `c •` on either side
* `HodgeLadder.holomorphicWedge_ofFunction`: in degree zero the wedge is multiplication of functions
* `HodgeLadder.holomorphicWedge_ofConstant_one_ne_zero`: `[1] ∧ [1] ≠ 0` on a nonempty open
  (nonvacuity)
* cast lemmas: `holomorphicFormCast_trans`, `holomorphicFormRestriction_holomorphicFormCast`,
  `holomorphicFormDifferential_holomorphicFormCast`, `eqToHom_apply_eq_holomorphicFormCast`,
  `XIsoOfEq_hom_app_eq_holomorphicFormCast`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLadder

section Algebraic

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The underlying element of `θ ∧ η` in the exterior algebra is the product `θ · η`. -/
@[simp] lemma coe_formWedge {p q : ℕ} (θ : Algebra.DeRham.Form R A p)
    (η : Algebra.DeRham.Form R A q) :
    (formWedge θ η : Algebra.DeRham.ExtAlg R A) =
      (θ : Algebra.DeRham.ExtAlg R A) * (η : Algebra.DeRham.ExtAlg R A) := rfl

variable (R A) in
/-- `formWedge` as an `R`-bilinear map `Form R A p →ₗ Form R A q →ₗ Form R A (p + q)`. -/
def formWedgeBilin (p q : ℕ) :
    Algebra.DeRham.Form R A p →ₗ[R] Algebra.DeRham.Form R A q →ₗ[R]
      Algebra.DeRham.Form R A (p + q) :=
  LinearMap.mk₂ R formWedge
    (fun θ θ' η => Subtype.ext (by simp [add_mul]))
    (fun c θ η => Subtype.ext (by simp))
    (fun θ η η' => Subtype.ext (by simp [mul_add]))
    (fun c θ η => Subtype.ext (by simp))

@[simp] lemma formWedgeBilin_apply (p q : ℕ) (θ : Algebra.DeRham.Form R A p)
    (η : Algebra.DeRham.Form R A q) : formWedgeBilin R A p q θ η = formWedge θ η := rfl

/-- **Functoriality of the wedge.** Upstream's `Algebra.DeRham.map` along an `R`-algebra map
`f : A → B` is multiplicative: it is induced by the algebra map `extAlgMap` of exterior
algebras. -/
lemma map_formWedge {B : Type u} [CommRing B] [Algebra R B] (f : A →ₐ[R] B) {p q : ℕ}
    (θ : Algebra.DeRham.Form R A p) (η : Algebra.DeRham.Form R A q) :
    Algebra.DeRham.map R f (p + q) (formWedge θ η) =
      formWedge (Algebra.DeRham.map R f p θ) (Algebra.DeRham.map R f q η) := by
  let _ := f.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact Subtype.ext (map_mul (Algebra.DeRham.extAlgMap R A B) _ _)

end Algebraic

section Holomorphic

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

variable (X d) in
/-- **The wedge of holomorphic forms.** The `ℂ`-bilinear map
`HolomorphicForm X d U p × HolomorphicForm X d U q → HolomorphicForm X d U (p + q)` induced by
`formWedge` on representatives. It is well defined by both sides of `wedgeDescends`. -/
def holomorphicWedge (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p q : ℕ) :
    HolomorphicForm X d U p →ₗ[ℂ] HolomorphicForm X d U q →ₗ[ℂ] HolomorphicForm X d U (p + q) :=
  LinearMap.liftQ₂ (chartEvaluationKernel X d U p) (chartEvaluationKernel X d U q)
    ((formWedgeBilin ℂ (OpenHolomorphicFunctions X d U) p q).compr₂
      (chartEvaluationKernel X d U (p + q)).mkQ)
    (fun θ hθ => LinearMap.ext fun η => by
      simpa [formWedgeBilin] using (wedgeDescends X d U p q θ η).1 hθ)
    (fun η hη => LinearMap.ext fun θ => by
      simpa [formWedgeBilin] using (wedgeDescends X d U p q θ η).2 hη)

/-- On representatives, the wedge of holomorphic forms is the class of `formWedge`. -/
@[simp] lemma holomorphicWedge_mk {U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} {p q : ℕ}
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    (η : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) q) :
    holomorphicWedge X d U p q (Submodule.Quotient.mk θ) (Submodule.Quotient.mk η) =
      Submodule.Quotient.mk (formWedge θ η) := rfl

/-- **Naturality under restriction** (rung `wedge-presheaf`). For analytic opens `V ⊆ U`,
restricting `a ∧ b` from `U` to `V` gives the wedge of the restrictions. -/
theorem holomorphicFormRestriction_holomorphicWedge {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (i : U ⟶ V) {p q : ℕ} (a : HolomorphicForm X d U p) (b : HolomorphicForm X d U q) :
    holomorphicFormRestriction X d i (p + q) (holomorphicWedge X d U p q a b) =
      holomorphicWedge X d V p q (holomorphicFormRestriction X d i p a)
        (holomorphicFormRestriction X d i q b) := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective _ a
  obtain ⟨η, rfl⟩ := Submodule.mkQ_surjective _ b
  change Submodule.Quotient.mk (formRestriction X d i (p + q) (formWedge θ η)) =
    Submodule.Quotient.mk (formWedge (formRestriction X d i p θ) (formRestriction X d i q η))
  rw [formRestriction, map_formWedge]
  rfl

/-- **Naturality under restriction, as an equation of bilinear maps.** Restricting after the wedge
on `U` equals the wedge on `V` after restricting both factors. -/
theorem holomorphicWedge_compr₂_restriction {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (i : U ⟶ V) (p q : ℕ) :
    (holomorphicWedge X d U p q).compr₂ (holomorphicFormRestriction X d i (p + q)) =
      (holomorphicWedge X d V p q).compl₁₂ (holomorphicFormRestriction X d i p)
        (holomorphicFormRestriction X d i q) :=
  LinearMap.ext₂ fun a b => holomorphicFormRestriction_holomorphicWedge i a b

variable (X d) in
/-- Transport of holomorphic forms along an equality of degrees `m = n`. On representatives it
keeps the underlying element of the exterior algebra (`holomorphicFormCast_mk`). -/
def holomorphicFormCast (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) {m n : ℕ} (h : m = n) :
    HolomorphicForm X d U m →ₗ[ℂ] HolomorphicForm X d U n :=
  h ▸ LinearMap.id

/-- Transport along `rfl` is the identity. -/
@[simp] lemma holomorphicFormCast_rfl (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (m : ℕ) :
    holomorphicFormCast X d U (rfl : m = m) = LinearMap.id := rfl

/-- Transport of a class `[θ]` is the class of the same element of the exterior algebra, read in
the new degree. -/
lemma holomorphicFormCast_mk {U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} {m n : ℕ} (h : m = n)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) m) :
    holomorphicFormCast X d U h (Submodule.Quotient.mk θ) =
      Submodule.Quotient.mk ⟨(θ : Algebra.DeRham.ExtAlg ℂ _), h ▸ θ.2⟩ := by
  subst h; rfl

/-- The holomorphic differential on a class `[θ]` is the class of the algebraic differential. -/
lemma holomorphicFormDifferential_mk {U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} {p : ℕ}
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    holomorphicFormDifferential X d U p (Submodule.Quotient.mk θ) =
      Submodule.Quotient.mk (Algebra.DeRham.differential ℂ _ p θ) := rfl

/-- Transports compose. -/
lemma holomorphicFormCast_trans (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) {m n k : ℕ}
    (h : m = n) (h' : n = k) (a : HolomorphicForm X d U m) :
    holomorphicFormCast X d U h' (holomorphicFormCast X d U h a) =
      holomorphicFormCast X d U (h.trans h') a := by
  subst h h'; rfl

/-- Transport commutes with restriction. -/
lemma holomorphicFormRestriction_holomorphicFormCast {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (i : U ⟶ V) {m n : ℕ} (h : m = n) (a : HolomorphicForm X d U m) :
    holomorphicFormRestriction X d i n (holomorphicFormCast X d U h a) =
      holomorphicFormCast X d V h (holomorphicFormRestriction X d i m a) := by
  subst h; rfl

/-- Transport commutes with the holomorphic differential. -/
lemma holomorphicFormDifferential_holomorphicFormCast (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {m n : ℕ} (h : m = n) (a : HolomorphicForm X d U m) :
    holomorphicFormDifferential X d U n (holomorphicFormCast X d U h a) =
      holomorphicFormCast X d U (congrArg (· + 1) h) (holomorphicFormDifferential X d U m a) := by
  subst h; rfl

/-- Transport agrees with `eqToHom` between the sections of upstream's presheaves of forms. -/
lemma eqToHom_apply_eq_holomorphicFormCast (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {m n : ℕ} (h : m = n) (a : HolomorphicForm X d U m) :
    (eqToHom (congrArg (fun k => (holomorphicDeRhamPresheaf X d k).obj U) h)) a =
      holomorphicFormCast X d U h a := by
  subst h; rfl

/-- Transport agrees with `HomologicalComplex.XIsoOfEq` on upstream's presheaf de Rham complex. -/
lemma XIsoOfEq_hom_app_eq_holomorphicFormCast (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {m n : ℕ} (h : m = n) (a : HolomorphicForm X d U m) :
    ((holomorphicDeRhamPresheafComplex X d).XIsoOfEq h).hom.app U a =
      holomorphicFormCast X d U h a := by
  subst h; rfl

/-- The Leibniz rule on representatives, with both degree transports written out. The second
transport is along `p + (q + 1) = p + q + 1`, which holds by `rfl`. -/
lemma holomorphicFormDifferential_formWedge_mk {U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    {p q : ℕ} (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    (η : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) q) :
    (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ _ (p + q) (formWedge θ η)) :
        HolomorphicForm X d U (p + q + 1)) =
      holomorphicFormCast X d U (Nat.add_right_comm p 1 q)
          (Submodule.Quotient.mk (formWedge (Algebra.DeRham.differential ℂ _ p θ) η)) +
        ((-1 : ℤ) ^ p) • holomorphicFormCast X d U (Nat.add_assoc p q 1).symm
          (Submodule.Quotient.mk (formWedge θ (Algebra.DeRham.differential ℂ _ q η))) := by
  rw [holomorphicFormCast_mk, holomorphicFormCast_mk, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_add]
  congr 1
  exact Subtype.ext (formWedge_differential θ η)

/-- **Leibniz rule on holomorphic forms.** For `a` of degree `p` and `b` of degree `q`,
`d(a ∧ b) = da ∧ b + (−1)^p a ∧ db` in `HolomorphicForm X d U (p + q + 1)`, the first term
transported from degree `(p + 1) + q`. The sign is Mathlib's Koszul sign `ε₂(p, q) = (−1)^p`, as
in `formWedge_differential`, from which this descends. Conventions row 'Wedge product of algebraic
forms'; the degree transport is row 'Wedge product of holomorphic forms', with no sign. -/
theorem holomorphicFormDifferential_holomorphicWedge
    {U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} {p q : ℕ}
    (a : HolomorphicForm X d U p) (b : HolomorphicForm X d U q) :
    holomorphicFormDifferential X d U (p + q) (holomorphicWedge X d U p q a b) =
      holomorphicFormCast X d U (Nat.add_right_comm p 1 q)
          (holomorphicWedge X d U (p + 1) q (holomorphicFormDifferential X d U p a) b) +
        ((-1 : ℤ) ^ p) •
          holomorphicWedge X d U p (q + 1) a (holomorphicFormDifferential X d U q b) := by
  induction a using Submodule.Quotient.induction_on with | H θ => ?_
  induction b using Submodule.Quotient.induction_on with | H η => ?_
  exact holomorphicFormDifferential_formWedge_mk θ η

/-- **Left unit.** The constant zero-form `c` wedged on the left acts by `c •`, read in degree
`0 + q`. -/
theorem holomorphicWedge_ofConstant_left {U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} {q : ℕ}
    (c : ℂ) (b : HolomorphicForm X d U q) :
    holomorphicWedge X d U 0 q (holomorphicFormOfConstant X d U c) b =
      holomorphicFormCast X d U (Nat.zero_add q).symm (c • b) := by
  obtain ⟨η, rfl⟩ := Submodule.mkQ_surjective _ b
  change Submodule.Quotient.mk (formWedge (Algebra.DeRham.ofConstant ℂ _ c) η) =
    holomorphicFormCast X d U (Nat.zero_add q).symm (Submodule.Quotient.mk (c • η))
  rw [holomorphicFormCast_mk]
  congr 1
  refine Subtype.ext ?_
  simp [Algebra.DeRham.ofConstant_apply, Algebra.DeRham.ofFunction_apply]

/-- **Right unit.** The constant zero-form `c` wedged on the right acts by `c •`. -/
theorem holomorphicWedge_ofConstant_right {U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} {p : ℕ}
    (a : HolomorphicForm X d U p) (c : ℂ) :
    holomorphicWedge X d U p 0 a (holomorphicFormOfConstant X d U c) = c • a := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective _ a
  change Submodule.Quotient.mk (formWedge θ (Algebra.DeRham.ofConstant ℂ _ c)) =
    Submodule.Quotient.mk (c • θ)
  congr 1
  refine Subtype.ext ?_
  simp [Algebra.DeRham.ofConstant_apply, Algebra.DeRham.ofFunction_apply]

/-- **Degree zero.** The wedge of the zero-forms of two holomorphic functions is the zero-form of
their product. -/
theorem holomorphicWedge_ofFunction (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f g : OpenHolomorphicFunctions X d U) :
    holomorphicWedge X d U 0 0
        (Submodule.Quotient.mk (Algebra.DeRham.ofFunction ℂ _ f))
        (Submodule.Quotient.mk (Algebra.DeRham.ofFunction ℂ _ g)) =
      Submodule.Quotient.mk (Algebra.DeRham.ofFunction ℂ _ (f * g)) := by
  rw [holomorphicWedge_mk]
  congr 1
  refine Subtype.ext ?_
  simp [Algebra.DeRham.ofFunction_apply, Algebra.DeRham.mk]
  rw [smul_smul, mul_comm]

/-- **Nonvacuity.** On a nonempty open, the wedge of the constant zero-form `1` with itself is
not zero: through the right unit law it is `[1]`, whose chart evaluation at any point is `1`. -/
theorem holomorphicWedge_ofConstant_one_ne_zero (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    [Nonempty U.unop] :
    holomorphicWedge X d U 0 0 (holomorphicFormOfConstant X d U 1)
      (holomorphicFormOfConstant X d U 1) ≠ 0 := by
  rw [holomorphicWedge_ofConstant_right, one_smul]
  intro hzero
  let a : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) 0 :=
    Algebra.DeRham.ofConstant ℂ (OpenHolomorphicFunctions X d U) 1
  have ha : a ∈ chartEvaluationKernel X d U 0 := by
    change Submodule.Quotient.mk a = 0 at hzero
    rwa [Submodule.Quotient.mk_eq_zero] at hzero
  let x : U.unop := Classical.arbitrary U.unop
  let e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x.1
  have hxsource : x.1 ∈ e.source := mem_extChartAt_source x.1
  have hxe : e x.1 ∈ chartSectionDomain X d U x.1 := by
    refine ⟨mem_extChartAt_target x.1, ?_⟩
    change e.symm (e x.1) ∈ U.unop
    rw [e.left_inv hxsource]
    exact x.2
  have heval := (mem_chartEvaluationKernel_iff X d U 0 a).1 ha x.1 (e x.1) hxe
  rw [chartEvaluation_ofConstant X d U x.1 1 hxe] at heval
  have hcoeff := congrArg (fun f : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ ↦ f Fin.elim0) heval
  simp at hcoeff

end Holomorphic

end HodgeLadder
