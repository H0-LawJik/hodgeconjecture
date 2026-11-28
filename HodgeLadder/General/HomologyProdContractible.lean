module

public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Cohomology
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Contractible
public import Mathlib.Topology.Homotopy.Product
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Singular homology of a product with a contractible factor

For a topological space `Y`, a contractible space `W` and a point `w₀ : W`, the projection
`Y × W → Y` and the section `y ↦ (y, w₀)` are inverse homotopy equivalences. Through upstream's
`AlgebraicTopology.singularChainHomotopyEquivOfHomotopyEquiv` they induce inverse isomorphisms
`H_k(Y × W; R) ≅ H_k(Y; R)` for every commutative ring `R` and every degree `k`. The isomorphism
is explicit: its forward map is `homologyMap R k` of the projection and its inverse is
`homologyMap R k` of the section, both by `rfl`. No sign enters.

The composite projection after section is the identity of `Y` on the nose, so
`homologyMap_prodFst_comp_prodSection` holds without contractibility; the other composite is
the identity only up to the homotopy `(y, w) ↦ (y, w₀) ≃ id`, which uses that `W` is
contractible.

## Main definitions

* `HodgeLadder.prodFst`, `HodgeLadder.prodSection`: the projection `Y × W ⟶ Y` and the
  section `y ↦ (y, w₀)` as morphisms of `TopCat`
* `HodgeLadder.prodContractibleHomotopyEquiv`: `Y × W ≃ₕ Y` with forward map the projection
  and inverse the section
* `HodgeLadder.homologyProdContractibleIso`, `HodgeLadder.homologyProdContractibleEquiv`: the
  induced isomorphism `H_k(Y × W; R) ≅ H_k(Y; R)`, as an iso in `ModuleCat R` and as a linear
  equivalence
* `HodgeLadder.homologyIsoOfHomeomorph`: the isomorphism `H_k(A; R) ≅ H_k(B; R)` induced by a
  homeomorphism `A ≃ₜ B`, with `homologyIsoOfHomeomorph_hom` identifying its forward map

## Main results

* `HodgeLadder.homotopic_of_contractibleSpace`: any two maps into a contractible space are
  homotopic
* `HodgeLadder.homologyProdContractibleIso_hom`, `HodgeLadder.homologyProdContractibleIso_inv`:
  the forward map is `homologyMap R k (prodFst Y W)` and the inverse is
  `homologyMap R k (prodSection Y W w₀)`
* `HodgeLadder.homologyMap_prodFst_comp_prodSection`,
  `HodgeLadder.homologyMap_prodSection_comp_prodFst`: the two composites are the identity
* `HodgeLadder.homologyMap_prodFst_bijective`, `HodgeLadder.homologyMap_prodSection_bijective`:
  both induced maps are bijective
* `HodgeLadder.nonempty_homology_prod_contractible_iso`: the rung statement,
  `Nonempty (Homology ℚ (TopCat.of (Y × W)) k ≅ Homology ℚ Y k)`
* `HodgeLadder.finrank_homology_zero_point_prod`: a nonvacuity check, `H_0(pt × W; ℚ)` has
  dimension `1`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
open scoped ContinuousMap

universe u

namespace HodgeLadder

/-- Any two continuous maps into a contractible space are homotopic: both are homotopic to
their composite with `W → Unit → W`, and those composites agree. -/
theorem homotopic_of_contractibleSpace {X W : Type*} [TopologicalSpace X] [TopologicalSpace W]
    [ContractibleSpace W] (f g : C(X, W)) :
    f.Homotopic g := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit W
  have h1 : (ContinuousMap.id W).Homotopic (e.invFun.comp e.toFun) := e.left_inv.symm
  have hf : f.Homotopic ((e.invFun.comp e.toFun).comp f) := by
    simpa using h1.comp (ContinuousMap.Homotopic.refl f)
  have hg : g.Homotopic ((e.invFun.comp e.toFun).comp g) := by
    simpa using h1.comp (ContinuousMap.Homotopic.refl g)
  have heq : (e.invFun.comp e.toFun).comp f = (e.invFun.comp e.toFun).comp g := by
    ext x; rfl
  exact hf.trans (heq ▸ hg.symm)

variable (Y : TopCat.{u}) (W : Type u) [TopologicalSpace W]

/-- The projection `Y × W ⟶ Y` as a morphism of `TopCat`. Definitionally
`TopCat.prodFst (X := Y) (Y := TopCat.of W)`. -/
def prodFst : TopCat.of (Y × W) ⟶ Y := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The section `y ↦ (y, w₀)` of the projection `Y × W ⟶ Y`, as a morphism of `TopCat`. -/
def prodSection (w₀ : W) : Y ⟶ TopCat.of (Y × W) :=
  TopCat.ofHom ⟨fun y ↦ (y, w₀), by fun_prop⟩

/-- For contractible `W`, the projection `Y × W → Y` is a homotopy equivalence with homotopy
inverse the section `y ↦ (y, w₀)`. The composite on `Y` is the identity; the composite on
`Y × W` is homotopic to the identity through a homotopy of `const w₀` to `snd` in `W`. -/
def prodContractibleHomotopyEquiv [ContractibleSpace W] (w₀ : W) : (Y × W) ≃ₕ Y where
  toFun := (prodFst Y W).hom
  invFun := (prodSection Y W w₀).hom
  left_inv := by
    have h := (ContinuousMap.Homotopic.refl (ContinuousMap.fst : C(Y × W, Y))).prodMk
      (homotopic_of_contractibleSpace (ContinuousMap.const (Y × W) w₀) ContinuousMap.snd)
    convert h using 1 <;> ext <;> rfl
  right_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id Y) using 1
    ext; rfl

variable (R : Type u) [CommRing R]

/-- The isomorphism `H_k(Y × W; R) ≅ H_k(Y; R)` for contractible `W`, obtained from the chain
homotopy equivalence `singularChainHomotopyEquivOfHomotopyEquiv` of
`prodContractibleHomotopyEquiv Y W w₀`. -/
def homologyProdContractibleIso [ContractibleSpace W] (w₀ : W) (k : ℕ) :
    Homology R (TopCat.of (Y × W)) k ≅ Homology R Y k :=
  (singularChainHomotopyEquivOfHomotopyEquiv R
    (prodContractibleHomotopyEquiv Y W w₀)).toHomologyIso k

/-- The forward map of `homologyProdContractibleIso` is the map induced by the projection. -/
theorem homologyProdContractibleIso_hom [ContractibleSpace W] (w₀ : W) (k : ℕ) :
    (homologyProdContractibleIso Y W R w₀ k).hom.hom = homologyMap R k (prodFst Y W) := rfl

/-- The inverse of `homologyProdContractibleIso` is the map induced by the section
`y ↦ (y, w₀)`. -/
theorem homologyProdContractibleIso_inv [ContractibleSpace W] (w₀ : W) (k : ℕ) :
    (homologyProdContractibleIso Y W R w₀ k).inv.hom = homologyMap R k (prodSection Y W w₀) := rfl

/-- `homologyProdContractibleIso` as an `R`-linear equivalence. -/
def homologyProdContractibleEquiv [ContractibleSpace W] (w₀ : W) (k : ℕ) :
    Homology R (TopCat.of (Y × W)) k ≃ₗ[R] Homology R Y k :=
  (homologyProdContractibleIso Y W R w₀ k).toLinearEquiv

/-- The forward map of `homologyProdContractibleEquiv` is `homologyMap R k (prodFst Y W)`. -/
theorem homologyProdContractibleEquiv_toLinearMap [ContractibleSpace W] (w₀ : W) (k : ℕ) :
    (homologyProdContractibleEquiv Y W R w₀ k).toLinearMap = homologyMap R k (prodFst Y W) := rfl

/-- The inverse of `homologyProdContractibleEquiv` is `homologyMap R k (prodSection Y W w₀)`. -/
theorem homologyProdContractibleEquiv_symm_toLinearMap [ContractibleSpace W] (w₀ : W) (k : ℕ) :
    (homologyProdContractibleEquiv Y W R w₀ k).symm.toLinearMap =
      homologyMap R k (prodSection Y W w₀) := rfl

/-- Projection after section induces the identity on `H_k(Y; R)`; no contractibility is used,
since the composite map of spaces is the identity of `Y`. -/
theorem homologyMap_prodFst_comp_prodSection (w₀ : W) (k : ℕ) :
    homologyMap R k (prodFst Y W) ∘ₗ homologyMap R k (prodSection Y W w₀) = LinearMap.id := by
  have h : prodSection Y W w₀ ≫ prodFst Y W = 𝟙 Y := by ext; rfl
  simp only [homologyMap, ← ModuleCat.hom_comp, ← Functor.map_comp, h]
  rw [CategoryTheory.Functor.map_id, ModuleCat.hom_id]

/-- For contractible `W`, section after projection induces the identity on
`H_k(Y × W; R)`. -/
theorem homologyMap_prodSection_comp_prodFst [ContractibleSpace W] (w₀ : W) (k : ℕ) :
    homologyMap R k (prodSection Y W w₀) ∘ₗ homologyMap R k (prodFst Y W) = LinearMap.id := by
  rw [← homologyProdContractibleEquiv_toLinearMap,
    ← homologyProdContractibleEquiv_symm_toLinearMap]
  exact LinearEquiv.symm_comp _

/-- For contractible `W`, the projection `Y × W → Y` induces a bijection on `H_k(-; R)`. -/
theorem homologyMap_prodFst_bijective [ContractibleSpace W] (k : ℕ) :
    Function.Bijective (homologyMap R k (prodFst Y W)) := by
  obtain ⟨w₀⟩ : Nonempty W := inferInstance
  rw [← homologyProdContractibleEquiv_toLinearMap Y W R w₀]
  exact (homologyProdContractibleEquiv Y W R w₀ k).bijective

/-- For contractible `W`, the section `y ↦ (y, w₀)` induces a bijection on `H_k(-; R)`. -/
theorem homologyMap_prodSection_bijective [ContractibleSpace W] (w₀ : W) (k : ℕ) :
    Function.Bijective (homologyMap R k (prodSection Y W w₀)) := by
  rw [← homologyProdContractibleEquiv_symm_toLinearMap Y W R w₀]
  exact (homologyProdContractibleEquiv Y W R w₀ k).symm.bijective

/-- A homeomorphism `A ≃ₜ B` induces `H_k(A; R) ≅ H_k(B; R)`, with forward map
`homologyMap R k` of the homeomorphism. -/
def homologyIsoOfHomeomorph {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (k : ℕ) : Homology R (TopCat.of A) k ≅ Homology R (TopCat.of B) k :=
  ((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).mapIso
    (TopCat.isoOfHomeo e)

/-- The forward map of `homologyIsoOfHomeomorph` is `homologyMap R k` of the homeomorphism. -/
theorem homologyIsoOfHomeomorph_hom {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (k : ℕ) :
    (homologyIsoOfHomeomorph R e k).hom.hom = homologyMap R k (TopCat.ofHom (e : C(A, B))) :=
  rfl

/-- **Rung `homology-prod-contractible`.** For contractible `W`, rational singular homology of
`Y × W` is isomorphic to that of `Y` in every degree. An explicit choice is
`homologyProdContractibleIso Y W ℚ w₀ k`, induced by the projection. -/
theorem nonempty_homology_prod_contractible_iso (Y : TopCat.{0}) (W : Type) [TopologicalSpace W]
    [ContractibleSpace W] (k : ℕ) :
    Nonempty (Homology ℚ (TopCat.of (Y × W)) k ≅ Homology ℚ Y k) := by
  obtain ⟨w₀⟩ : Nonempty W := inferInstance
  exact ⟨homologyProdContractibleIso Y W ℚ w₀ k⟩

/-- Nonvacuity check: for contractible `W`, `H_0(pt × W; ℚ)` has dimension `1`, read through
`homologyProdContractibleEquiv` and Mathlib's computation of `H_0` of a point. -/
theorem finrank_homology_zero_point_prod (W : Type) [TopologicalSpace W] [ContractibleSpace W] :
    Module.finrank ℚ (Homology ℚ (TopCat.of (PUnit.{1} × W)) 0) = 1 := by
  obtain ⟨w₀⟩ : Nonempty W := inferInstance
  let e1 := homologyProdContractibleEquiv (TopCat.of PUnit.{1}) W ℚ w₀ 0
  let e2 := (singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat.{0} ℚ)
    (ModuleCat.of ℚ ℚ) (TopCat.of PUnit.{1})).toLinearEquiv
  let e3 := (Limits.coproductUniqueIso
    (fun _ : TopCat.of PUnit.{1} ↦ ModuleCat.of ℚ ℚ)).toLinearEquiv
  exact ((e1.trans e2).trans e3).finrank_eq.trans (Module.finrank_self ℚ)

end HodgeLadder
