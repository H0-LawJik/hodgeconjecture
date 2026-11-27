module

public import HodgeLadder.Hodge.WedgePresheaf
public import HodgeLadder.Hodge.RationalDeRhamComplex
public import HodgeLadder.Tests.DeRhamUnitNonzero

/-!
# The sheafified wedge `Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ`

Rung `wedge-sheafify` (front `cup`, second third of the former `wedge-sheaf-map`). The wedge of
holomorphic forms `HodgeLadder.holomorphicWedge` is `ℂ`-bilinear; read `ℚ`-bilinearly through the
instance `holomorphicFormRatModule` and lifted to `⊗[ℚ]`, it is a morphism of presheaves of
`ℚ`-vector spaces `Ω^p_ℚ,pre ⊗ Ω^q_ℚ,pre ⟶ Ω^{p+q}_ℚ,pre`, natural by
`holomorphicFormRestriction_holomorphicWedge`. Sheafification `presheafToSheaf` is a monoidal
functor for Mathlib's `Sheaf.monoidalCategory` (local instance `Cup.sheafMonoidal`), with
`μ P Q : sheafify P ⊗ sheafify Q ≅ sheafify (P ⊗ Q)`; the sheafified wedge is `μ` followed by
the sheafification of the presheaf wedge.

## The defining square

`toSheafifyTensor P Q : P ⊗ Q ⟶ (sheafify P ⊗ sheafify Q)` (underlying presheaf) is the
sheafification map of `P ⊗ Q` followed by `μ⁻¹ = δ`. The sheafified wedge is the unique morphism
`f` of sheaves with

`toSheafifyTensor P_p P_q ≫ f = wedge ≫ toSheafify P_{p+q}`

(`toSheafifyTensor_comp_wedgeSheaf`, uniqueness `eq_wedgeSheaf_iff`). Forgetting the
`ℚ`-structure and applying the pinned comparison `forgetRationalHolomorphicFormSheafIso`
(`toSheafify_comp_forgetRationalHolomorphicFormSheafIso`) turns the right side into upstream's
sheafification map applied to `a ∧ b` (`forget_wedgeSheaf`, `forget_wedgeSheaf_apply`). No sign
and no scalar enter: `μ`, `δ` and the sheafification maps are Mathlib's, the comparison is
`sheafComposeNatIso`, and the wedge keeps the factor order `a ∧ b`. The scale is pinned by the
unit law `wedgeSheaf_unit_left` against the left unitor of `Sheaf.monoidalCategory`, whose unit
`ε` is the identity (`sheafifyQ_ε`).

## Instances

Instance search does not apply `Cup.sheafMonoidal` at the concrete space
`TopCat.of (ComplexPoint X)`: its discrimination-tree key mentions `TopCat.carrier ?Y`, which the
concrete goal reduces away. The structure is restated at the concrete space as
`analyticShQMonoidal X`, used as a local instance here and by consumers.

## Main definitions

* `HodgeLadder.toSheafifyTensor P Q`: `P ⊗ Q ⟶ sheafify P ⊗ sheafify Q`, any space
* `HodgeLadder.analyticShQMonoidal X`: `Cup.sheafMonoidal` at `TopCat.of (ComplexPoint X)`
* `HodgeLadder.rationalWedgeBilin X d U p q`: `(holomorphicWedge X d U p q).restrictScalars₁₂ ℚ ℚ`
* `HodgeLadder.rationalWedgePresheaf X d p q`: the presheaf wedge, `TensorProduct.lift` of it
* `HodgeLadder.wedgeSheaf X d p q`: `Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ`

## Main results

* `HodgeLadder.toSheafifyTensor_comp_μ`, `toSheafifyTensor_comp_map`, `toSheafifyTensor_hom_ext`,
  `toSheafifyTensor_naturality_left`, `toSheafifyTensor_naturality_right`,
  `toSheafifyTensor_leftUnitor`, `toSheafify_comp_eqToHom`: the generic layer
* `HodgeLadder.sheafifyQ_ε`: the unit of the monoidal sheafification is `𝟙` (`rfl`, a pin)
* `HodgeLadder.rationalWedgePresheaf_app_tmul`: on `a ⊗ₜ b` the presheaf wedge is `a ∧ b` (`rfl`)
* `HodgeLadder.toSheafifyTensor_comp_wedgeSheaf`: the defining square, `eq_wedgeSheaf_iff` its
  uniqueness, `toSheafifyTensor_comp_wedgeSheaf_apply` on sections
* `HodgeLadder.forget_wedgeSheaf`, `HodgeLadder.forget_wedgeSheaf_apply`: the reading on upstream's
  sheaves of forms through the comparison
* `HodgeLadder.rationalWedgePresheaf_unit_left`, `HodgeLadder.wedgeSheaf_unit_left`: the unit law
  `(u ▷ Ω^q_ℚ) ≫ wedgeSheaf 0 q ≫ cast = λ`, the scale pin of the wedge
* `HodgeLadder.rationalWedgePresheaf_app_ne_zero`: nonvacuity on a nonempty open;
  `HodgeLadder.wedgeSheaf_ne_zero`: the sheaf wedge `Ω⁰_ℚ ⊗ Ω⁰_ℚ ⟶ Ω⁰_ℚ` is not zero when `X(ℂ)`
  is nonempty
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry ComplexPoint TopologicalSpace

attribute [local instance] HodgeLadder.Cup.sheafMonoidal

namespace HodgeLadder

section Generic

variable {Y : TopCat.{0}}

/-- The canonical map from `P ⊗ Q` to the presheaf underlying `sheafify P ⊗ sheafify Q`: the
sheafification map of `P ⊗ Q` followed by the inverse `δ` of the tensorator `μ` of the monoidal
functor `presheafToSheaf`. -/
def toSheafifyTensor (P Q : Cup.PreQ Y) :
    P ⊗ Q ⟶ (Cup.presheafQ Y).obj ((Cup.sheafifyQ Y).obj P ⊗ (Cup.sheafifyQ Y).obj Q) :=
  toSheafify (Cup.J Y) (P ⊗ Q) ≫
    (Cup.presheafQ Y).map (Functor.OplaxMonoidal.δ (Cup.sheafifyQ Y) P Q)

/-- `toSheafifyTensor` followed by `μ` is the sheafification map of `P ⊗ Q`. -/
theorem toSheafifyTensor_comp_μ (P Q : Cup.PreQ Y) :
    toSheafifyTensor P Q ≫ (Cup.presheafQ Y).map (Functor.LaxMonoidal.μ (Cup.sheafifyQ Y) P Q) =
      toSheafify (Cup.J Y) (P ⊗ Q) := by
  rw [toSheafifyTensor, Category.assoc, Functor.Monoidal.δ_μ_map]
  exact Category.comp_id _

/-- **The square of a sheafified map out of a tensor product.** For `w : P ⊗ Q ⟶ R`, the
morphism `μ ≫ sheafify w : sheafify P ⊗ sheafify Q ⟶ sheafify R` satisfies
`toSheafifyTensor P Q ≫ (μ ≫ sheafify w) = w ≫ toSheafify R` on underlying presheaves. -/
theorem toSheafifyTensor_comp_map (P Q R : Cup.PreQ Y) (w : P ⊗ Q ⟶ R) :
    toSheafifyTensor P Q ≫ (Cup.presheafQ Y).map
        (Functor.LaxMonoidal.μ (Cup.sheafifyQ Y) P Q ≫ (Cup.sheafifyQ Y).map w) =
      w ≫ toSheafify (Cup.J Y) R := by
  rw [Functor.map_comp, ← Category.assoc, toSheafifyTensor_comp_μ]
  exact (toSheafify_naturality _ _).symm

/-- **Maps out of a sheafified tensor product are determined on presheaf tensors.** Two morphisms
of sheaves `sheafify P ⊗ sheafify Q ⟶ S` agree once they agree after `toSheafifyTensor P Q`. -/
theorem toSheafifyTensor_hom_ext {P Q : Cup.PreQ Y} {S : Cup.ShQ Y}
    {f g : (Cup.sheafifyQ Y).obj P ⊗ (Cup.sheafifyQ Y).obj Q ⟶ S}
    (h : toSheafifyTensor P Q ≫ (Cup.presheafQ Y).map f =
      toSheafifyTensor P Q ≫ (Cup.presheafQ Y).map g) : f = g := by
  rw [← cancel_epi (Functor.OplaxMonoidal.δ (Cup.sheafifyQ Y) P Q)]
  apply (Cup.presheafQ Y).map_injective
  apply sheafify_hom_ext (Cup.J Y) _ _ S.property
  rw [Functor.map_comp, Functor.map_comp]
  simpa only [toSheafifyTensor, Category.assoc] using h

/-- `toSheafifyTensor` is natural in the first factor. -/
theorem toSheafifyTensor_naturality_left {P P' : Cup.PreQ Y} (α : P ⟶ P') (Q : Cup.PreQ Y) :
    toSheafifyTensor P Q ≫
        (Cup.presheafQ Y).map ((Cup.sheafifyQ Y).map α ▷ (Cup.sheafifyQ Y).obj Q) =
      (α ▷ Q) ≫ toSheafifyTensor P' Q := by
  rw [toSheafifyTensor, toSheafifyTensor, Category.assoc, ← Functor.map_comp,
    Functor.OplaxMonoidal.δ_natural_left, Functor.map_comp, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _) (toSheafify_naturality _ _).symm

/-- `toSheafifyTensor` is natural in the second factor. -/
theorem toSheafifyTensor_naturality_right (P : Cup.PreQ Y) {Q Q' : Cup.PreQ Y} (β : Q ⟶ Q') :
    toSheafifyTensor P Q ≫
        (Cup.presheafQ Y).map ((Cup.sheafifyQ Y).obj P ◁ (Cup.sheafifyQ Y).map β) =
      (P ◁ β) ≫ toSheafifyTensor P Q' := by
  rw [toSheafifyTensor, toSheafifyTensor, Category.assoc, ← Functor.map_comp,
    Functor.OplaxMonoidal.δ_natural_right, Functor.map_comp, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _) (toSheafify_naturality _ _).symm

/-- **Pin of the unit of the monoidal sheafification.** The unit `ε` of `presheafToSheaf` is the
identity at the pin: Mathlib's `Sheaf.monoidalCategory` is localized along `Iso.refl`. The unit
law `toSheafifyTensor_leftUnitor`, and so the scale of `wedgeSheaf`, depends on it; a Mathlib bump
that changes it breaks here. -/
theorem sheafifyQ_ε (Y : TopCat.{0}) : Functor.LaxMonoidal.ε (Cup.sheafifyQ Y) = 𝟙 _ := rfl

/-- **`toSheafifyTensor` and the left unitor.** With the unit presheaf on the left, the left
unitor of sheaves after `toSheafifyTensor` is the left unitor of presheaves followed by the
sheafification map. -/
theorem toSheafifyTensor_leftUnitor (Q : Cup.PreQ Y) :
    toSheafifyTensor (𝟙_ (Cup.PreQ Y)) Q ≫
        (Cup.presheafQ Y).map (λ_ ((Cup.sheafifyQ Y).obj Q)).hom =
      (λ_ Q).hom ≫ toSheafify (Cup.J Y) Q := by
  rw [Functor.LaxMonoidal.left_unitality, sheafifyQ_ε, id_whiskerRight, Category.id_comp]
  exact toSheafifyTensor_comp_map _ _ _ (λ_ Q).hom

/-- Sheafification maps commute with the transports `eqToHom` along an equality of indices in a
family of presheaves. -/
theorem toSheafify_comp_eqToHom (P : ℕ → Cup.PreQ Y) {m n : ℕ} (h : m = n) :
    toSheafify (Cup.J Y) (P m) ≫
        (Cup.presheafQ Y).map (eqToHom (congrArg (fun k => (Cup.sheafifyQ Y).obj (P k)) h)) =
      eqToHom (congrArg P h) ≫ toSheafify (Cup.J Y) (P n) := by
  subst h
  simp

end Generic

/-- `Cup.sheafMonoidal` at the analytic space `X(ℂ)`. Instance search does not apply
`Cup.sheafMonoidal` there (its key mentions `TopCat.carrier ?Y`, which the concrete goal reduces
away); this abbreviation is used as a local instance instead. -/
abbrev analyticShQMonoidal (X : Over (Spec ↧ℂ)) :
    MonoidalCategory (Cup.ShQ (TopCat.of (ComplexPoint X))) :=
  Cup.sheafMonoidal _

attribute [local instance] analyticShQMonoidal

section Forms

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The wedge of holomorphic forms, read as a `ℚ`-bilinear map for `holomorphicFormRatModule`. -/
def rationalWedgeBilin (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p q : ℕ) :
    HolomorphicForm X d U p →ₗ[ℚ] HolomorphicForm X d U q →ₗ[ℚ]
      HolomorphicForm X d U (p + q) :=
  (holomorphicWedge X d U p q).restrictScalars₁₂ ℚ ℚ

/-- **The presheaf wedge** `Ω^p_ℚ,pre ⊗ Ω^q_ℚ,pre ⟶ Ω^{p+q}_ℚ,pre`, a morphism of presheaves of
`ℚ`-vector spaces: on an open `U`, `a ⊗ b ↦ a ∧ b` (`TensorProduct.lift` of
`rationalWedgeBilin`), natural by `holomorphicFormRestriction_holomorphicWedge`. -/
def rationalWedgePresheaf (p q : ℕ) :
    rationalHolomorphicFormPresheaf X d p ⊗ rationalHolomorphicFormPresheaf X d q ⟶
      rationalHolomorphicFormPresheaf X d (p + q) where
  app U := ModuleCat.ofHom (TensorProduct.lift (rationalWedgeBilin X d U p q))
  naturality U V i := ModuleCat.hom_ext <| TensorProduct.ext' fun a b => by
    change holomorphicWedge X d V p q (holomorphicFormRestriction X d i p a)
        (holomorphicFormRestriction X d i q b) =
      holomorphicFormRestriction X d i (p + q) (holomorphicWedge X d U p q a b)
    exact (holomorphicFormRestriction_holomorphicWedge i a b).symm

/-- On `a ⊗ₜ b` the presheaf wedge is `holomorphicWedge X d U p q a b`. -/
@[simp] theorem rationalWedgePresheaf_app_tmul (p q : ℕ)
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (a : HolomorphicForm X d U p)
    (b : HolomorphicForm X d U q) :
    ((rationalWedgePresheaf X d p q).app U).hom (a ⊗ₜ[ℚ] b) = holomorphicWedge X d U p q a b :=
  rfl

/-- **The sheafified wedge** `Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ` in sheaves of `ℚ`-vector spaces on
`X(ℂ)`: the tensorator `μ` of the monoidal functor `presheafToSheaf`, then the sheafification of
`rationalWedgePresheaf`. Factor order `a ∧ b`, no sign. -/
def wedgeSheaf (p q : ℕ) :
    rationalHolomorphicFormSheaf X d p ⊗ rationalHolomorphicFormSheaf X d q ⟶
      rationalHolomorphicFormSheaf X d (p + q) :=
  Functor.LaxMonoidal.μ (Cup.sheafifyQ (TopCat.of (ComplexPoint X))) _ _ ≫
    (Cup.sheafifyQ (TopCat.of (ComplexPoint X))).map (rationalWedgePresheaf X d p q)

/-- **The defining square** (rung `wedge-sheafify`). On underlying presheaves,
`toSheafifyTensor ≫ wedgeSheaf = rationalWedgePresheaf ≫ toSheafify`: the sheafified wedge of the
images of `a` and `b` is the image of `a ∧ b` under the rational sheafification map. Exact. -/
theorem toSheafifyTensor_comp_wedgeSheaf (p q : ℕ) :
    toSheafifyTensor (rationalHolomorphicFormPresheaf X d p)
        (rationalHolomorphicFormPresheaf X d q) ≫
      (Cup.presheafQ _).map (wedgeSheaf X d p q) =
    rationalWedgePresheaf X d p q ≫
      toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
        (rationalHolomorphicFormPresheaf X d (p + q)) :=
  toSheafifyTensor_comp_map _ _ _ (rationalWedgePresheaf X d p q)

/-- **The square determines the sheafified wedge.** A morphism `Ω^p_ℚ ⊗ Ω^q_ℚ ⟶ Ω^{p+q}_ℚ` is
`wedgeSheaf X d p q` if and only if it satisfies the defining square. -/
theorem eq_wedgeSheaf_iff (p q : ℕ)
    (f : rationalHolomorphicFormSheaf X d p ⊗ rationalHolomorphicFormSheaf X d q ⟶
      rationalHolomorphicFormSheaf X d (p + q)) :
    f = wedgeSheaf X d p q ↔
      toSheafifyTensor (rationalHolomorphicFormPresheaf X d p)
          (rationalHolomorphicFormPresheaf X d q) ≫ (Cup.presheafQ _).map f =
        rationalWedgePresheaf X d p q ≫ toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
          (rationalHolomorphicFormPresheaf X d (p + q)) :=
  ⟨fun h => h ▸ toSheafifyTensor_comp_wedgeSheaf X d p q,
    fun h => toSheafifyTensor_hom_ext (h.trans (toSheafifyTensor_comp_wedgeSheaf X d p q).symm)⟩

/-- The defining square on sections: for `a`, `b` over `U`, the sheafified wedge of
`toSheafifyTensor (a ⊗ b)` is the rational sheafification map applied to `a ∧ b`. -/
theorem toSheafifyTensor_comp_wedgeSheaf_apply (p q : ℕ)
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (a : HolomorphicForm X d U p)
    (b : HolomorphicForm X d U q) :
    (((Cup.presheafQ _).map (wedgeSheaf X d p q)).app U).hom
        (((toSheafifyTensor (rationalHolomorphicFormPresheaf X d p)
          (rationalHolomorphicFormPresheaf X d q)).app U).hom (a ⊗ₜ[ℚ] b)) =
      ((toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
        (rationalHolomorphicFormPresheaf X d (p + q))).app U).hom
          (holomorphicWedge X d U p q a b) :=
  congrArg (fun φ => (φ.app U).hom (a ⊗ₜ[ℚ] b)) (toSheafifyTensor_comp_wedgeSheaf X d p q)

/-- **The reading on upstream's forms.** Forgetting the `ℚ`-structure of the defining square and
applying the comparison `forgetRationalHolomorphicFormSheafIso` (pinned by
`toSheafify_comp_forgetRationalHolomorphicFormSheafIso`) gives upstream's sheafification map of
`holomorphicDeRhamPresheaf X d (p + q)` after the wedge. Exact, no sign. -/
theorem forget_wedgeSheaf (p q : ℕ) :
    Functor.whiskerRight (toSheafifyTensor (rationalHolomorphicFormPresheaf X d p)
        (rationalHolomorphicFormPresheaf X d q) ≫ (Cup.presheafQ _).map (wedgeSheaf X d p q))
        Cup.U ≫
      (sheafToPresheaf (Cup.J (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}).map
        (forgetRationalHolomorphicFormSheafIso X d (p + q)).hom =
    Functor.whiskerRight (rationalWedgePresheaf X d p q) Cup.U ≫
      toSheafify (Cup.J (TopCat.of (ComplexPoint X))) (holomorphicDeRhamPresheaf X d (p + q)) := by
  refine (congrArg (fun φ => Functor.whiskerRight φ Cup.U ≫
    (sheafToPresheaf (Cup.J (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}).map
      (forgetRationalHolomorphicFormSheafIso X d (p + q)).hom)
    (toSheafifyTensor_comp_wedgeSheaf X d p q)).trans ?_
  refine (congrArg (· ≫ _) (Functor.whiskerRight_comp _ _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg _ (toSheafify_comp_forgetRationalHolomorphicFormSheafIso X d (p + q))

/-- **The reading on sections of upstream's sheaf.** For holomorphic forms `a`, `b` over `U`,
the comparison carries the sheafified wedge of `toSheafifyTensor (a ⊗ b)` to upstream's
sheafification map applied to `a ∧ b`, in `holomorphicDeRhamSheaf X d (p + q)`. -/
theorem forget_wedgeSheaf_apply (p q : ℕ) (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (a : HolomorphicForm X d U p) (b : HolomorphicForm X d U q) :
    ((forgetRationalHolomorphicFormSheafIso X d (p + q)).hom.hom.app U).hom
        (((Cup.presheafQ _).map (wedgeSheaf X d p q)).app U |>.hom
          ((toSheafifyTensor (rationalHolomorphicFormPresheaf X d p)
            (rationalHolomorphicFormPresheaf X d q)).app U |>.hom (a ⊗ₜ[ℚ] b))) =
      ((toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d (p + q))).app U).hom (holomorphicWedge X d U p q a b) :=
  congrArg (fun φ => (φ.app U).hom (a ⊗ₜ[ℚ] b)) (forget_wedgeSheaf X d p q)

/-- **Nonvacuity of the presheaf wedge.** On a nonempty open, the component of
`rationalWedgePresheaf X d 0 0` is not zero: it sends `[1] ⊗ [1]` to `[1] ∧ [1] ≠ 0`
(`holomorphicWedge_ofConstant_one_ne_zero`). -/
theorem rationalWedgePresheaf_app_ne_zero (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    [Nonempty U.unop] : (rationalWedgePresheaf X d 0 0).app U ≠ 0 := by
  intro h
  apply holomorphicWedge_ofConstant_one_ne_zero (X := X) (d := d) U
  have := congrArg (fun φ => φ.hom (holomorphicFormOfConstant X d U 1 ⊗ₜ[ℚ]
    holomorphicFormOfConstant X d U 1)) h
  exact this

/-- Transport along an equality of degrees in `rationalHolomorphicFormPresheaf` acts on sections
as `holomorphicFormCast`. -/
theorem eqToHom_app_rationalHolomorphicFormPresheaf (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {m n : ℕ} (h : m = n) (a : HolomorphicForm X d U m) :
    ((eqToHom (congrArg (rationalHolomorphicFormPresheaf X d) h)).app U).hom a =
      holomorphicFormCast X d U h a := by
  subst h
  rfl

/-- **Unit law of the presheaf wedge.** The constant zero-form `[r]` wedged on the left, read in
degree `q`, is `r •`: `(u ▷ P_q) ≫ wedge ≫ cast = λ`, with `u` the presheaf map `r ↦ [r]`. -/
theorem rationalWedgePresheaf_unit_left (q : ℕ) :
    (rationalConstantsToFormsPresheaf X d ▷ rationalHolomorphicFormPresheaf X d q) ≫
        rationalWedgePresheaf X d 0 q ≫
          eqToHom (congrArg (rationalHolomorphicFormPresheaf X d) (Nat.zero_add q)) =
      (λ_ (rationalHolomorphicFormPresheaf X d q)).hom := by
  refine NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| TensorProduct.ext'
    fun (r : ℚ) (b : HolomorphicForm X d U q) => ?_
  change ((eqToHom (congrArg (rationalHolomorphicFormPresheaf X d) (Nat.zero_add q))).app U).hom
      (holomorphicWedge X d U 0 q (holomorphicFormOfConstant X d U (algebraMap ℚ ℂ r)) b) =
        r • b
  rw [eqToHom_app_rationalHolomorphicFormPresheaf X d U (Nat.zero_add q),
    holomorphicWedge_ofConstant_left, holomorphicFormCast_trans]
  rfl

/-- **Unit law of the sheafified wedge** (the scale pin of `wedgeSheaf`, red team of
`wedge-sheafify`, change 5). In bidegree `(0, q)`, the unit `ℚ_X ⟶ Ω⁰_ℚ` wedged on the left and
transported to degree `q` is the left unitor `ℚ_X ⊗ Ω^q_ℚ ≅ Ω^q_ℚ` of `Sheaf.monoidalCategory`.
Exact, no scalar. -/
theorem wedgeSheaf_unit_left (q : ℕ) :
    (rationalConstantsToFormsSheaf X d ▷ rationalHolomorphicFormSheaf X d q) ≫
        wedgeSheaf X d 0 q ≫
          eqToHom (congrArg (rationalHolomorphicFormSheaf X d) (Nat.zero_add q)) =
      (λ_ (rationalHolomorphicFormSheaf X d q)).hom := by
  refine toSheafifyTensor_hom_ext (P := 𝟙_ (Cup.PreQ (TopCat.of (ComplexPoint X))))
    (Q := rationalHolomorphicFormPresheaf X d q) ?_
  refine Eq.trans ?_ (toSheafifyTensor_leftUnitor (rationalHolomorphicFormPresheaf X d q)).symm
  refine (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (toSheafifyTensor_naturality_left
    (rationalConstantsToFormsPresheaf X d) (rationalHolomorphicFormPresheaf X d q))).trans ?_
  have h1 : toSheafifyTensor (rationalHolomorphicFormPresheaf X d 0)
        (rationalHolomorphicFormPresheaf X d q) ≫ (Cup.presheafQ _).map (wedgeSheaf X d 0 q ≫
          eqToHom (congrArg (rationalHolomorphicFormSheaf X d) (Nat.zero_add q))) =
      rationalWedgePresheaf X d 0 q ≫
        eqToHom (congrArg (rationalHolomorphicFormPresheaf X d) (Nat.zero_add q)) ≫
          toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
            (rationalHolomorphicFormPresheaf X d q) := by
    refine (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (toSheafifyTensor_comp_wedgeSheaf X d 0 q)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (_ ≫ ·)
      (toSheafify_comp_eqToHom (rationalHolomorphicFormPresheaf X d) (Nat.zero_add q))
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans ?_)
  rw [← rationalWedgePresheaf_unit_left X d q]
  simp only [Category.assoc]
  rfl

end Forms

/-- **Nonvacuity of the sheafified wedge.** On a variety with a complex point, the wedge
`Ω⁰_ℚ ⊗ Ω⁰_ℚ ⟶ Ω⁰_ℚ` is not zero. If it were, the unit law `wedgeSheaf_unit_left` would make the
left unitor of `Ω⁰_ℚ` zero, so `Ω⁰_ℚ` would be a zero object and the unit `rationalDeRhamUnit X`
would vanish, against `Tests.rationalDeRhamUnit_ne_zero` (rung `de-rham-unit-nonzero`). -/
theorem wedgeSheaf_ne_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [Nonempty (ComplexPoint X)] : wedgeSheaf X (dim X.left) 0 0 ≠ 0 := by
  intro h
  have h0 : (λ_ (rationalHolomorphicFormSheaf X (dim X.left) 0)).hom = 0 := by
    rw [← wedgeSheaf_unit_left X (dim X.left) 0, h, zero_comp, comp_zero]
    rfl
  have hZ : IsZero (rationalHolomorphicFormSheaf X (dim X.left) 0) := by
    rw [IsZero.iff_id_eq_zero, ← Iso.inv_hom_id (λ_ (rationalHolomorphicFormSheaf X _ 0)), h0,
      comp_zero]
  apply Tests.rationalDeRhamUnit_ne_zero X
  apply homFromSingleExtend_ext
  exact (hZ : IsZero ((rationalHolomorphicDeRhamComplexNat X (dim X.left)).X 0)).eq_of_tgt _ _

end HodgeLadder
