module

public import HodgeLadder.Cup.Product
public import HodgeLadder.Cup.SheafTensor
public import HodgeLadder.Hodge.Conjugation
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Cup products and the Hodge filtration: statements and the reduction

Rungs `cup-hodge-reduction` (checked), `cup-hodge-classes` (stated) and the sub-rung statements
`wedge-descends`, `tensor-bounded-quasi-iso` (front `cup`, decision 0009, item 8; red team
`docs/sketches/cup-hodge-filtration.redteam.md`).

Upstream defines a Hodge class of codimension `p` (`hodgeClasses ℚ X p`, notation `Hdg^p(X; ℚ)`)
as a class `α ∈ H^{2p}(X; ℚ)` whose de Rham image `ι α = fieldToDeRhamCohomology ℚ X (2p) α`
lies in `hodgePiece X p p (2p) = F^p ⊓ conj⁻¹(F^p)`. A Hodge class has three parts:

* rational: `α` is an element of `H^{2p}(X; ℚ)`. The checked rational cup
  (`HodgeLadder.Cup.cup`) takes values in `H^*(X; ℚ)`, so this part is closed under `cup` by its
  type;
* conjugate: `deRhamConj (ι α) ∈ F^p`. Conjugation fixes `ι α` for every rational `α`
  (`HodgeLadder.deRhamConj_fieldToDeRhamCohomology`), so for rational classes this part follows
  from the filtration part (`HodgeLadder.mem_hodgeClasses_iff_mem_hodgeFiltration`);
* filtration: `ι α ∈ F^p`. This is the only part with content.

So "products of Hodge classes are Hodge classes" (`HodgeLadder.CupPreservesHodgeClasses`)
follows from the rational filtration statement `HodgeLadder.CupRespectsHodgeFiltrationRational`:
if `ι α ∈ F^p` and `ι β ∈ F^q` then `ι (α ∪ β) ∈ F^{p+q}`. This reduction is proved here
(`HodgeLadder.cupPreservesHodgeClasses_of_rational`). For `p ≤ 0` the filtration is everything
(`HodgeLadder.hodgeFiltration_eq_top_of_nonpos`), so every degree-zero class is a Hodge class
(`HodgeLadder.mem_hodgeClasses_zero`).

The complex form `F^p ∪ F^q ⊆ F^{p+q}` on `H_dR^*(X)` (rung `cup-hodge-filtration`) needs a
product on de Rham hypercohomology, which neither upstream nor Mathlib has at the pin; its
construction and the sub-rungs are in `docs/sketches/cup-hodge-filtration.md`. Two sub-rung
statements can be written on present definitions and are stated as `Prop`s below, open:

* `HodgeLadder.WedgeDescends` (sub-rung `wedge-descends`): the wedge product of algebraic
  Kähler forms descends to upstream's holomorphic forms;
* `HodgeLadder.TensorBoundedQuasiIso` (sub-rung `tensor-bounded-quasi-iso`): tensoring with a
  bounded complex of sheaves of `ℚ`-vector spaces preserves quasi-isomorphisms.

## Main definitions

* `HodgeLadder.CupRespectsHodgeFiltrationRational`, `HodgeLadder.CupPreservesHodgeClasses`
* `HodgeLadder.formWedge`, `HodgeLadder.WedgeDescends`, `HodgeLadder.TensorBoundedQuasiIso`
* the instance `HodgeLadder.curriedTensor_additive`

## Main results

* `HodgeLadder.mem_hodgeClasses_iff_mem_hodgeFiltration`
* `HodgeLadder.cupPreservesHodgeClasses_of_rational`
* `HodgeLadder.hodgeFiltration_eq_top_of_nonpos`, `HodgeLadder.mem_hodgeClasses_zero`
* `HodgeLadder.formWedge_differential`: the Leibniz rule with Mathlib's Koszul sign
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder

/-! ### The target statements -/

section Targets

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- **Rational filtration form.** For rational classes `α ∈ H^a(X; ℚ)` and `β ∈ H^b(X; ℚ)` whose
de Rham images lie in `F^p H_dR^a(X)` and `F^q H_dR^b(X)`, the de Rham image of the cup product
`α ∪ β ∈ H^n(X; ℚ)` (`n = a + b`) lies in `F^{p+q} H_dR^n(X)`. Here `F^p` is upstream's
`hodgeFiltration` (the image of `ℍ^n(X; F^p Ω^•)`), the de Rham image is upstream's
`fieldToDeRhamCohomology ℚ X`, and `∪` is the checked Yoneda cup `HodgeLadder.Cup.cup`. Membership
does not depend on the order of the factors or on a sign, since `F^{p+q}` is an additive
subgroup. -/
def CupRespectsHodgeFiltrationRational : Prop :=
  ∀ (a b n : ℕ) (h : a + b = n) (p q : ℤ) (α : H^a(X; ℚ)) (β : H^b(X; ℚ)),
    fieldToDeRhamCohomology ℚ X a α ∈ hodgeFiltration X p a →
    fieldToDeRhamCohomology ℚ X b β ∈ hodgeFiltration X q b →
    fieldToDeRhamCohomology ℚ X n (Cup.cup α β n h) ∈ hodgeFiltration X (p + q) n

/-- **Products of Hodge classes are Hodge classes.** For `α ∈ Hdg^p(X; ℚ)` and
`β ∈ Hdg^q(X; ℚ)`, the cup product `α ∪ β ∈ H^{2(p+q)}(X; ℚ)` lies in `Hdg^{p+q}(X; ℚ)`, with
upstream's `hodgeClasses` on both sides. -/
def CupPreservesHodgeClasses : Prop :=
  ∀ (p q : ℕ) (α : H^(2 * p)(X; ℚ)) (β : H^(2 * q)(X; ℚ)),
    α ∈ Hdg^p(X; ℚ) → β ∈ Hdg^q(X; ℚ) →
    Cup.cup α β (2 * (p + q)) (by ring) ∈ Hdg^(p + q)(X; ℚ)

/-- For a rational class, membership in upstream's Hodge classes is membership of the de Rham
image in `F^p`: the rational part holds by the type, and the conjugate part follows from the
filtration part because conjugation fixes de Rham images of rational classes. -/
theorem mem_hodgeClasses_iff_mem_hodgeFiltration (p : ℕ) (α : H^(2 * p)(X; ℚ)) :
    α ∈ Hdg^p(X; ℚ) ↔
      fieldToDeRhamCohomology ℚ X (2 * p) α ∈ hodgeFiltration X p (2 * p : ℕ) :=
  ⟨fun h => h.1, mem_hodgeClasses_of_mem_hodgeFiltration X p α⟩

/-- **The reduction.** The rational filtration form implies that products of Hodge classes are
Hodge classes. -/
theorem cupPreservesHodgeClasses_of_rational (hF : CupRespectsHodgeFiltrationRational X) :
    CupPreservesHodgeClasses X := by
  intro p q α β hα hβ
  rw [mem_hodgeClasses_iff_mem_hodgeFiltration] at hα hβ ⊢
  have h := hF (2 * p) (2 * q) (2 * (p + q)) (by ring) p q α β hα hβ
  rwa [← Nat.cast_add] at h

/-- For `p ≤ 0` the Hodge filtration is everything: `Ω•` lives in degrees `≥ 0`, so the stupid
truncation `F^p Ω• → Ω•` is an isomorphism. -/
theorem hodgeFiltration_eq_top_of_nonpos (p : ℤ) (hp : p ≤ 0) (n : ℤ) :
    hodgeFiltration X p n = ⊤ := by
  have : Ω•(X).IsStrictlyGE p := CochainComplex.isStrictlyGE_of_ge Ω•(X) p 0 hp
  have hiso : IsIso (hodgeFilteredDeRhamInclusion X p) := by
    unfold hodgeFilteredDeRhamInclusion
    exact HomologicalComplex.stupidTruncInclusion_isIso (K := Ω•(X))
      (e := ComplexShape.embeddingUpIntGE p)
  rw [eq_top_iff]
  intro x _
  refine ⟨hypercohomologyMap X (inv (hodgeFilteredDeRhamInclusion X p)) n x, ?_⟩
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, IsIso.inv_hom_id]
  exact Localization.SmallShiftedHom.comp_mk₀_id _ _ _

/-- Every rational class of degree zero is a Hodge class: `Hdg^0(X; ℚ) = ⊤`. -/
theorem mem_hodgeClasses_zero (α : H^(2 * 0)(X; ℚ)) : α ∈ Hdg^0(X; ℚ) :=
  mem_hodgeClasses_of_mem_hodgeFiltration X 0 α
    (by rw [hodgeFiltration_eq_top_of_nonpos X _ (by simp)]; trivial)

end Targets

/-! ### Sub-rung `wedge-descends`: the wedge product of algebraic forms -/

section Wedge

open CliffordAlgebra

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The grade involution acts on `⋀^p` by `(−1)^p`. -/
theorem involute_of_mem_exteriorPower {p : ℕ} {x : Algebra.DeRham.ExtAlg R A}
    (hx : x ∈ ⋀[A]^p Ω[A⁄R]) : involute x = ((-1 : ℤ) ^ p) • x := by
  have hmem : x ∈ evenOdd (0 : QuadraticForm A Ω[A⁄R]) (p : ZMod 2) :=
    Submodule.mem_iSup_of_mem (⟨p, rfl⟩ : {n : ℕ // (n : ZMod 2) = (p : ZMod 2)}) hx
  rcases Nat.even_or_odd p with hp | hp
  · rw [(ZMod.natCast_eq_zero_iff_even).2 hp] at hmem
    rw [involute_eq_of_mem_even hmem, hp.neg_one_pow, one_smul]
  · rw [(ZMod.natCast_eq_one_iff_odd).2 hp] at hmem
    rw [involute_eq_of_mem_odd hmem, hp.neg_one_pow, neg_smul, one_smul]

/-- The wedge product of algebraic differential forms, `Form R A p × Form R A q → Form R A (p+q)`:
multiplication in the exterior algebra `⋀_A Ω_{A/R}`, in which upstream's `Algebra.DeRham.Form`
are the graded pieces, first factor on the left. -/
def formWedge {p q : ℕ} (θ : Algebra.DeRham.Form R A p) (η : Algebra.DeRham.Form R A q) :
    Algebra.DeRham.Form R A (p + q) :=
  ⟨(θ : Algebra.DeRham.ExtAlg R A) * (η : Algebra.DeRham.ExtAlg R A), by
    rw [ExteriorAlgebra.exteriorPower, pow_add]
    exact Submodule.mul_mem_mul θ.2 η.2⟩

/-- **Leibniz rule**, `d(θ ∧ η) = dθ ∧ η + (−1)^p θ ∧ dη` for `θ` of degree `p`, from upstream's
`Algebra.DeRham.extDeriv_mul`. The sign is Mathlib's Koszul sign `ε₂(p, q) = (−1)^p` for the
tensor product of `ℤ`-indexed cochain complexes (`ComplexShape.ε_up_ℤ`), so the wedge product
is a morphism of complexes `Ω^• ⊗ Ω^• → Ω^•` with no sign twist. Stated in the exterior
algebra, where the degrees `(p + q) + 1` and `(p + 1) + q` need no cast. -/
theorem formWedge_differential {p q : ℕ} (θ : Algebra.DeRham.Form R A p)
    (η : Algebra.DeRham.Form R A q) :
    (Algebra.DeRham.differential R A (p + q) (formWedge θ η) : Algebra.DeRham.ExtAlg R A) =
      (formWedge (Algebra.DeRham.differential R A p θ) η : Algebra.DeRham.ExtAlg R A) +
        ((-1 : ℤ) ^ p) • (formWedge θ (Algebra.DeRham.differential R A q η) :
          Algebra.DeRham.ExtAlg R A) := by
  simp only [Algebra.DeRham.coe_differential, formWedge]
  rw [Algebra.DeRham.extDeriv_mul, involute_of_mem_exteriorPower θ.2, smul_mul_assoc, add_comm]

/-- **Wedge descends** (sub-rung `wedge-descends`, open). A form whose chart evaluations vanish
wedges, on either side, with any form to a form whose chart evaluations vanish; so the wedge
product descends to upstream's holomorphic forms
`HolomorphicForm X d U p = Form ℂ 𝒪(U) p ⧸ chartEvaluationKernel X d U p`. -/
def WedgeDescends : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (U : (TopologicalSpace.Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p q : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    (η : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) q),
    (θ ∈ chartEvaluationKernel X d U p → formWedge θ η ∈ chartEvaluationKernel X d U (p + q)) ∧
      (η ∈ chartEvaluationKernel X d U q → formWedge θ η ∈ chartEvaluationKernel X d U (p + q))

end Wedge

/-! ### Sub-rung `tensor-bounded-quasi-iso` -/

section TensorBounded

open MonoidalCategory Cup Limits

attribute [local instance] sheafMonoidal

variable {Y : TopCat.{0}}

/-- The tensor product of sheaves of `ℚ`-vector spaces is additive in the first variable, as a
functor to endofunctors (from `tensorRight_additive`). Mathlib's tensor product of complexes
asks for it. -/
instance curriedTensor_additive : (curriedTensor (ShQ Y)).Additive where
  map_add {F F' f g} := by
    ext Z : 2
    exact (tensorRight_additive Y Z).map_add (f := f) (g := g)

/-- **Tensoring with a bounded complex preserves quasi-isomorphisms** (sub-rung
`tensor-bounded-quasi-iso`, open). In cochain complexes of sheaves of `ℚ`-vector spaces on `Y`,
with Mathlib's tensor product of complexes (`HomologicalComplex.tensorObj`, Koszul signs,
`docs/conventions.md` row "Tensor product of ℤ-indexed cochain complexes and its shifts"),
`f ⊗ 𝟙_M` is a quasi-isomorphism when `f` is one and `M` is bounded. The `HasTensor` hypotheses
ask for the coproducts `⨁_{i+j=n} K^i ⊗ M^j`, which exist since `ShQ Y` is cocomplete. Expected
route: induction on the length of `M` through its stupid filtration, two-out-of-three for short
exact sequences of complexes, and `tensor_exact` for `M` a single sheaf. -/
def TensorBoundedQuasiIso : Prop :=
  ∀ (Y : TopCat.{0}) (K L : CochainComplex (ShQ Y) ℤ) (f : K ⟶ L) [QuasiIso f]
    (M : CochainComplex (ShQ Y) ℤ) (a b : ℤ) [M.IsStrictlyGE a] [M.IsStrictlyLE b]
    [HomologicalComplex.HasTensor K M] [HomologicalComplex.HasTensor L M],
    QuasiIso (HomologicalComplex.tensorHom f (𝟙 M))

end TensorBounded

end HodgeLadder
