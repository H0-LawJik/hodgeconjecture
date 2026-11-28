module

public import HodgeLadder.General.CircleArcs
public import HodgeLadder.General.HomologyProdContractible
public import HodgeLadder.General.MayerVietorisRank
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.HomologyZeroNaturality

/-!
# Rational homology of a cylinder `Y × S¹`

For `Y : TopCat.{0}` and the circle `S¹ = UnitAddCircle`, cover `X = Y × S¹` by the open sets
`U = Y × U₀` and `V = Y × V₀` of `HodgeLadder.CircleArcs`. Each of `U`, `V` is homeomorphic to
`Y × (contractible)`, so its rational homology is that of `Y` (`homologyProdContractibleIso`).
The overlap `U ∩ V` is the disjoint open union of `P₁` and `P₂`, its parts over the arcs `W₁` and
`W₂`, each homeomorphic to `Y × (contractible)`, so `dim H_j(U ∩ V) ≤ 2 dim H_j(Y)`. The section
`y ↦ (y, ↑(1/4))` of the overlap, followed by the inclusion `i : U ∩ V → U` and the projection to
`Y`, is the identity, so `rank i_{*,j} ≥ dim H_j(Y)`. The Mayer–Vietoris count
`MayerVietoris.finrank_homology_succ_add_le` then gives
`dim H_{k+1}(Y × S¹) ≤ dim H_{k+1}(Y) + dim H_k(Y)`, with finite dimension. Only degrees
`k + 1 ≥ 1` are bounded; `b_0(Y × S¹)` is not covered here, and the torus induction
(`torus-homology-bound`) treats degree `0` by path-connectedness
(`MayerVietoris.finrank_homology_zero_of_pathConnected`). Only dimensions
enter, so no sign or normalization convention is used.

The bridges to `Y × W` are `prodSetHomeo` (built from `Homeomorph.Set.prod Set.univ S`) for `U`
and `V`, and the hand-built `sliceHomeo` for `P₁` and `P₂`.

## Main definitions

* `HodgeLadder.CircleCylinder.cylU`, `HodgeLadder.CircleCylinder.cylV`: the open cover of the
  cylinder.
* `HodgeLadder.CircleCylinder.P₁`, `HodgeLadder.CircleCylinder.P₂`: the two parts of the overlap.
* `HodgeLadder.CircleCylinder.overlapSection`: the section `y ↦ (y, ↑(1/4))`.
* `HodgeLadder.CircleCylinder.homologyEquivOfHomeomorphProd`: `H_j(A) ≃ H_j(Y)` for
  `A ≃ₜ Y × W` with `W` contractible.

## Main results

* `HodgeLadder.CircleCylinder.finiteDimensional_homology_prod_circle`,
  `HodgeLadder.CircleCylinder.finrank_homology_prod_circle_le`: the cylinder bound in degree
  `k + 1`.
* `HodgeLadder.CircleCylinder.finrank_homology_overlap_le`,
  `HodgeLadder.CircleCylinder.finrank_le_finrank_range_overlap`: the overlap bound and the rank
  from a section.
* `HodgeLadder.CircleCylinder.finiteDimensional_homology_one_circle`,
  `HodgeLadder.CircleCylinder.finrank_homology_one_circle_le`,
  `HodgeLadder.CircleCylinder.one_le_finrank_homology_one_circle`,
  `HodgeLadder.CircleCylinder.finrank_homology_one_circle`: the nonvacuity test at `Y = pt`,
  `dim H_1(S¹; ℚ) = 1` with finite dimension; the lower bound uses
  `HodgeLadder.CircleCylinder.finrank_range_overlap_zero_add_one_le`, the degree-zero rank bound
  from the augmentation.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology.Singular Module Set HodgeLadder.CircleArcs

namespace HodgeLadder.CircleCylinder

variable (Y : TopCat.{0})

/-- A space homeomorphic to `Y × W` with `W` contractible has the rational homology of `Y`. -/
noncomputable def homologyEquivOfHomeomorphProd {A W : Type} [TopologicalSpace A]
    [TopologicalSpace W] [ContractibleSpace W] (e : A ≃ₜ Y × W) (j : ℕ) :
    Homology ℚ (TopCat.of A) j ≃ₗ[ℚ] Homology ℚ Y j :=
  (homologyIsoOfHomeomorph ℚ e j ≪≫
    homologyProdContractibleIso Y W ℚ (Classical.arbitrary W) j).toLinearEquiv

/-- The bridge `↥(univ ×ˢ S) ≃ₜ Y × ↥S`. -/
def prodSetHomeo (S : Set UnitAddCircle) :
    ↥((univ : Set Y) ×ˢ S) ≃ₜ Y × ↥S :=
  (Homeomorph.Set.prod Set.univ S).trans ((Homeomorph.Set.univ Y).prodCongr (Homeomorph.refl _))

/-- The slice of a subset `A ⊆ Y × S¹` over `S ⊆ S¹`, when `A ⊇ Y × S`. -/
def sliceHomeo (A : Set (Y × UnitAddCircle)) (S : Set UnitAddCircle)
    (hS : ∀ (y : Y), ∀ w ∈ S, (y, w) ∈ A) :
    {q : ↥A // (q : Y × UnitAddCircle).2 ∈ S} ≃ₜ Y × ↥S where
  toFun q := (((q : ↥A) : Y × UnitAddCircle).1, ⟨((q : ↥A) : Y × UnitAddCircle).2, q.2⟩)
  invFun p := ⟨⟨(p.1, p.2.1), hS p.1 p.2.1 p.2.2⟩, p.2.2⟩
  left_inv q := rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun :=
    ((continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _).subtype_mk _

/-- The cylinder `Y × S¹` as an object of `TopCat`. -/
abbrev cyl : TopCat.{0} := TopCat.of (Y × UnitAddCircle)

/-- The open set `Y × U₀` of the cylinder. -/
def cylU : Set (cyl Y) := (univ : Set Y) ×ˢ U₀

/-- The open set `Y × V₀` of the cylinder. -/
def cylV : Set (cyl Y) := (univ : Set Y) ×ˢ V₀

/-- `Y × U₀` is open in the cylinder. -/
theorem isOpen_cylU : IsOpen (cylU Y) := isOpen_univ.prod isOpen_U₀

/-- `Y × V₀` is open in the cylinder. -/
theorem isOpen_cylV : IsOpen (cylV Y) := isOpen_univ.prod isOpen_V₀

/-- `Y × U₀` and `Y × V₀` cover the cylinder. -/
theorem cylU_union_cylV : cylU Y ∪ cylV Y = univ := by
  rw [cylU, cylV, ← Set.prod_union, U₀_union_V₀, Set.univ_prod_univ]

/-- `H_j(Y × U₀) ≃ H_j(Y)`. -/
noncomputable def homologyCylUEquiv (j : ℕ) :
    Homology ℚ (TopCat.of ↥(cylU Y)) j ≃ₗ[ℚ] Homology ℚ Y j :=
  homologyEquivOfHomeomorphProd Y (prodSetHomeo Y U₀) j

/-- `H_j(Y × V₀) ≃ H_j(Y)`. -/
noncomputable def homologyCylVEquiv (j : ℕ) :
    Homology ℚ (TopCat.of ↥(cylV Y)) j ≃ₗ[ℚ] Homology ℚ Y j :=
  homologyEquivOfHomeomorphProd Y (prodSetHomeo Y V₀) j

/-- The overlap `(Y × U₀) ∩ (Y × V₀)` as an object of `TopCat`. -/
abbrev overlap : TopCat.{0} := TopCat.of ↥(cylU Y ∩ cylV Y)

/-- The part of the overlap over the arc `W₁`. -/
def P₁ : Set (overlap Y) := {q | (q : Y × UnitAddCircle).2 ∈ W₁}

/-- The part of the overlap over the arc `W₂`. -/
def P₂ : Set (overlap Y) := {q | (q : Y × UnitAddCircle).2 ∈ W₂}

/-- `P₁` is open in the overlap. -/
theorem isOpen_P₁ : IsOpen (P₁ Y) :=
  isOpen_W₁.preimage (continuous_snd.comp continuous_subtype_val)

/-- `P₂` is open in the overlap. -/
theorem isOpen_P₂ : IsOpen (P₂ Y) :=
  isOpen_W₂.preimage (continuous_snd.comp continuous_subtype_val)

/-- `P₁` and `P₂` cover the overlap, from `U₀ ∩ V₀ = W₁ ∪ W₂`. -/
theorem P₁_union_P₂ : P₁ Y ∪ P₂ Y = univ := by
  refine eq_univ_iff_forall.2 fun q => ?_
  have h : (q : Y × UnitAddCircle).2 ∈ U₀ ∩ V₀ := ⟨q.2.1.2, q.2.2.2⟩
  rw [U₀_inter_V₀] at h
  exact h

/-- `P₁` and `P₂` are disjoint, from `disjoint_W₁_W₂`. -/
theorem disjoint_P₁_P₂ : Disjoint (P₁ Y) (P₂ Y) :=
  Set.disjoint_left.2 fun _ h₁ h₂ => Set.disjoint_left.1 disjoint_W₁_W₂ h₁ h₂

/-- A point `(y, w)` with `w ∈ U₀ ∩ V₀` lies in the overlap `(Y × U₀) ∩ (Y × V₀)`. -/
theorem mem_overlap_of_mem_inter {y : Y} {w : UnitAddCircle} (hw : w ∈ U₀ ∩ V₀) :
    ((y, w) : Y × UnitAddCircle) ∈ cylU Y ∩ cylV Y :=
  ⟨⟨trivial, hw.1⟩, ⟨trivial, hw.2⟩⟩

/-- `H_j(P₁) ≃ H_j(Y)`. -/
noncomputable def homologyP₁Equiv (j : ℕ) :
    Homology ℚ (TopCat.of ↥(P₁ Y)) j ≃ₗ[ℚ] Homology ℚ Y j :=
  homologyEquivOfHomeomorphProd Y (sliceHomeo Y (cylU Y ∩ cylV Y) W₁ fun _ _ hw =>
    mem_overlap_of_mem_inter Y (by rw [U₀_inter_V₀]; exact Or.inl hw)) j

/-- `H_j(P₂) ≃ H_j(Y)`. -/
noncomputable def homologyP₂Equiv (j : ℕ) :
    Homology ℚ (TopCat.of ↥(P₂ Y)) j ≃ₗ[ℚ] Homology ℚ Y j :=
  homologyEquivOfHomeomorphProd Y (sliceHomeo Y (cylU Y ∩ cylV Y) W₂ fun _ _ hw =>
    mem_overlap_of_mem_inter Y (by rw [U₀_inter_V₀]; exact Or.inr hw)) j

/-- If `H_j(Y; ℚ)` is finite-dimensional, so is `H_j` of the overlap. -/
theorem finiteDimensional_homology_overlap (j : ℕ) [FiniteDimensional ℚ (Homology ℚ Y j)] :
    FiniteDimensional ℚ (Homology ℚ (overlap Y) j) :=
  have := (homologyP₁Equiv Y j).symm.finiteDimensional
  have := (homologyP₂Equiv Y j).symm.finiteDimensional
  MayerVietoris.finiteDimensional_homology_of_disjoint (isOpen_P₁ Y) (isOpen_P₂ Y)
    (P₁_union_P₂ Y) (disjoint_P₁_P₂ Y) j

/-- **Overlap bound.** `dim H_j((Y × U₀) ∩ (Y × V₀); ℚ) ≤ 2 dim H_j(Y; ℚ)`, from the disjoint
open cover by `P₁ ≃ₜ Y × W₁` and `P₂ ≃ₜ Y × W₂` (the two sides are in fact equal). -/
theorem finrank_homology_overlap_le (j : ℕ) [FiniteDimensional ℚ (Homology ℚ Y j)] :
    finrank ℚ (Homology ℚ (overlap Y) j) ≤ 2 * finrank ℚ (Homology ℚ Y j) := by
  have := (homologyP₁Equiv Y j).symm.finiteDimensional
  have := (homologyP₂Equiv Y j).symm.finiteDimensional
  have h := MayerVietoris.finrank_homology_le_of_disjoint (isOpen_P₁ Y) (isOpen_P₂ Y)
    (P₁_union_P₂ Y) (disjoint_P₁_P₂ Y) j
  rw [(homologyP₁Equiv Y j).finrank_eq, (homologyP₂Equiv Y j).finrank_eq] at h
  omega

/-- The section `y ↦ (y, ↑(1/4))` of the cylinder over the overlap. -/
noncomputable def overlapSection : Y ⟶ overlap Y :=
  TopCat.ofHom ⟨fun y => ⟨(y, ((1 / 4 : ℝ) : UnitAddCircle)),
    mem_overlap_of_mem_inter Y quarter_mem_U₀_inter_V₀⟩, by fun_prop⟩

/-- The projection `Y × U₀ → Y`. -/
def cylUFst : TopCat.of ↥(cylU Y) ⟶ Y :=
  TopCat.ofHom ⟨fun q => (q : Y × UnitAddCircle).1, by fun_prop⟩

/-- Section, then inclusion `i : U ∩ V → U`, then projection is the identity of `Y`. -/
theorem overlapSection_comp : overlapSection Y ≫
    subsetIntersectionToLeft (cyl Y) (cylU Y) (cylV Y) ≫ cylUFst Y = 𝟙 Y := by
  ext; rfl

/-- **Rank of the overlap inclusion.** `dim H_j(Y; ℚ) ≤ rank (i_* : H_j(U ∩ V) → H_j(U))` for
the cover `U = Y × U₀`, `V = Y × V₀`, through the section `y ↦ (y, ↑(1/4))`. -/
theorem finrank_le_finrank_range_overlap (j : ℕ) [FiniteDimensional ℚ (Homology ℚ Y j)] :
    finrank ℚ (Homology ℚ Y j) ≤ finrank ℚ (LinearMap.range
      (homologyMap ℚ j (subsetIntersectionToLeft (cyl Y) (cylU Y) (cylV Y)))) := by
  have := (homologyCylUEquiv Y j).symm.finiteDimensional
  refine MayerVietoris.finrank_le_finrank_range_of_comp_eq_id
    (homologyMap ℚ j (overlapSection Y)) _ (homologyMap ℚ j (cylUFst Y)) ?_
  have h := overlapSection_comp Y
  simp only [homologyMap, ← ModuleCat.hom_comp, ← Functor.map_comp, Category.assoc, h]
  rw [CategoryTheory.Functor.map_id, ModuleCat.hom_id]

/-- **Finite dimension on the cylinder.** If `H_{k+1}(Y; ℚ)` and `H_k(Y; ℚ)` are finite-dimensional,
so is `H_{k+1}(Y × S¹; ℚ)`. -/
theorem finiteDimensional_homology_prod_circle (k : ℕ)
    [FiniteDimensional ℚ (Homology ℚ Y (k + 1))] [FiniteDimensional ℚ (Homology ℚ Y k)] :
    FiniteDimensional ℚ (Homology ℚ (TopCat.of (Y × UnitAddCircle)) (k + 1)) := by
  have := (homologyCylUEquiv Y (k + 1)).symm.finiteDimensional
  have := (homologyCylVEquiv Y (k + 1)).symm.finiteDimensional
  have := finiteDimensional_homology_overlap Y k
  exact MayerVietoris.finiteDimensional_homology_succ (isOpen_cylU Y) (isOpen_cylV Y)
    (cylU_union_cylV Y) k

/-- **Cylinder bound.** If `H_{k+1}(Y; ℚ)` and `H_k(Y; ℚ)` are finite-dimensional, then
`dim H_{k+1}(Y × S¹; ℚ) ≤ dim H_{k+1}(Y; ℚ) + dim H_k(Y; ℚ)`. Read it together with
`finiteDimensional_homology_prod_circle`: `finrank` is `0` on an infinite-dimensional space. No
sign enters; upstream's overlap map `(i_*, -j_*)` contributes only through ranks. -/
theorem finrank_homology_prod_circle_le (k : ℕ)
    [FiniteDimensional ℚ (Homology ℚ Y (k + 1))] [FiniteDimensional ℚ (Homology ℚ Y k)] :
    finrank ℚ (Homology ℚ (TopCat.of (Y × UnitAddCircle)) (k + 1)) ≤
      finrank ℚ (Homology ℚ Y (k + 1)) + finrank ℚ (Homology ℚ Y k) := by
  have := (homologyCylUEquiv Y (k + 1)).symm.finiteDimensional
  have := (homologyCylVEquiv Y (k + 1)).symm.finiteDimensional
  have := finiteDimensional_homology_overlap Y k
  have h := MayerVietoris.finrank_homology_succ_add_le (isOpen_cylU Y) (isOpen_cylV Y)
    (cylU_union_cylV Y) k
  rw [(homologyCylUEquiv Y (k + 1)).finrank_eq, (homologyCylVEquiv Y (k + 1)).finrank_eq] at h
  have h1 := finrank_le_finrank_range_overlap Y (k + 1)
  have h0 := finrank_le_finrank_range_overlap Y k
  have h2 : finrank ℚ (Homology ℚ (TopCat.of ↥(cylU Y ∩ cylV Y)) k) ≤ _ :=
    finrank_homology_overlap_le Y k
  change finrank ℚ (Homology ℚ (cyl Y) (k + 1)) ≤ _
  omega

/-- `H_j(pt × S¹; ℚ) ≃ H_j(S¹; ℚ)`, through `Homeomorph.punitProd`. -/
noncomputable def homologyPointProdCircleEquiv (j : ℕ) :
    Homology ℚ (TopCat.of (TopCat.of PUnit.{1} × UnitAddCircle)) j ≃ₗ[ℚ]
      Homology ℚ (TopCat.of UnitAddCircle) j :=
  (homologyIsoOfHomeomorph ℚ (Homeomorph.punitProd UnitAddCircle) j).toLinearEquiv

/-- **Nonvacuity test, finiteness.** `H_1(S¹; ℚ)` is finite-dimensional: the cylinder theorem at
`Y = pt`. -/
theorem finiteDimensional_homology_one_circle :
    FiniteDimensional ℚ (Homology ℚ (TopCat.of UnitAddCircle) 1) := by
  have : Subsingleton (Homology ℚ (TopCat.of PUnit.{1}) (0 + 1)) :=
    MayerVietoris.subsingleton_homology_succ_of_totallyDisconnected _ 0
  have := MayerVietoris.finiteDimensional_homology_zero_of_pathConnected (TopCat.of PUnit.{1})
  have := finiteDimensional_homology_prod_circle (TopCat.of PUnit.{1}) 0
  exact (homologyPointProdCircleEquiv 1).finiteDimensional

/-- **Nonvacuity test, bound.** `dim H_1(S¹; ℚ) ≤ 1`: the cylinder bound at `Y = pt`, with
`H_1(pt) = 0` and `dim H_0(pt) = 1`. This is the first positive-degree use of
`MayerVietoris.finrank_homology_succ_add_le`. -/
theorem finrank_homology_one_circle_le :
    finrank ℚ (Homology ℚ (TopCat.of UnitAddCircle) 1) ≤ 1 := by
  have : Subsingleton (Homology ℚ (TopCat.of PUnit.{1}) (0 + 1)) :=
    MayerVietoris.subsingleton_homology_succ_of_totallyDisconnected _ 0
  have := MayerVietoris.finiteDimensional_homology_zero_of_pathConnected (TopCat.of PUnit.{1})
  have h := finrank_homology_prod_circle_le (TopCat.of PUnit.{1}) 0
  rw [(homologyPointProdCircleEquiv 1).finrank_eq,
    finrank_zero_of_subsingleton (M := Homology ℚ (TopCat.of PUnit.{1}) (0 + 1)),
    MayerVietoris.finrank_homology_zero_of_pathConnected (TopCat.of PUnit.{1})] at h
  exact h

/-- **Rank of the degree-zero overlap map.** For an open cover with `U` nonempty, the overlap map
`(i_*, -j_*) : H_0(U ∩ V) → H_0(U) × H_0(V)` lands in the kernel of `(a, b) ↦ ε a + ε b`
(`ε` the augmentation, natural by `TopCat.singularHomology₀ε_naturality`), which is onto `ℚ`,
so `rank φ₀ + 1 ≤ dim H_0(U) + dim H_0(V)`. No sign enters: `ε` is used only through its
kernel. -/
theorem finrank_range_overlap_zero_add_one_le {X : TopCat.{0}} (U V : Set X) [Nonempty U]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of U) 0)]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of V) 0)] :
    finrank ℚ (LinearMap.range (LinearMap.prod
        (homologyMap ℚ 0 (subsetIntersectionToLeft X U V))
        (-homologyMap ℚ 0 (subsetIntersectionToRight X U V)))) + 1 ≤
      finrank ℚ (Homology ℚ (TopCat.of U) 0) + finrank ℚ (Homology ℚ (TopCat.of V) 0) := by
  let εU := ((TopCat.of U).singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom
  let εV := ((TopCat.of V).singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom
  let εW := ((TopCat.of ↥(U ∩ V)).singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom
  let ψ : (Homology ℚ (TopCat.of U) 0 × Homology ℚ (TopCat.of V) 0) →ₗ[ℚ] ℚ :=
    LinearMap.coprod εU εV
  have nL : ∀ x, εU (homologyMap ℚ 0 (subsetIntersectionToLeft X U V) x) = εW x := fun x =>
    congrArg (fun φ => ModuleCat.Hom.hom φ x)
      (TopCat.singularHomology₀ε_naturality (subsetIntersectionToLeft X U V) (ModuleCat.of ℚ ℚ))
  have nR : ∀ x, εV (homologyMap ℚ 0 (subsetIntersectionToRight X U V) x) = εW x := fun x =>
    congrArg (fun φ => ModuleCat.Hom.hom φ x)
      (TopCat.singularHomology₀ε_naturality (subsetIntersectionToRight X U V) (ModuleCat.of ℚ ℚ))
  have hle : LinearMap.range (LinearMap.prod
        (homologyMap ℚ 0 (subsetIntersectionToLeft X U V))
        (-homologyMap ℚ 0 (subsetIntersectionToRight X U V))) ≤ LinearMap.ker ψ := by
    rintro _ ⟨x, rfl⟩
    change εU (homologyMap ℚ 0 (subsetIntersectionToLeft X U V) x) +
      εV (-(homologyMap ℚ 0 (subsetIntersectionToRight X U V) x)) = 0
    rw [map_neg, nL x, nR x, add_neg_cancel]
  have hsurj : Function.Surjective ψ := by
    have := (TopCat.of U).singularHomology₀ε_epi (ModuleCat.of ℚ ℚ)
    have hs : Function.Surjective εU := (ModuleCat.epi_iff_surjective _).1 this
    intro r
    obtain ⟨a, ha⟩ := hs r
    exact ⟨(a, 0), by simp [ψ, ha]⟩
  have rn := LinearMap.finrank_range_add_finrank_ker ψ
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
    Module.finrank_prod] at rn
  have := Submodule.finrank_mono hle
  omega

/-- **Nonvacuity test, lower bound.** `1 ≤ dim H_1(S¹; ℚ)`: the exact Mayer–Vietoris count on the
cylinder over a point reads `dim H_1(S¹) + rank φ₁ + rank φ₀ = 0 + 0 + 2`, with `rank φ₁ = 0`
(`H_1` of the overlap is zero) and `rank φ₀ ≤ 1` (`finrank_range_overlap_zero_add_one_le`). -/
theorem one_le_finrank_homology_one_circle :
    1 ≤ finrank ℚ (Homology ℚ (TopCat.of UnitAddCircle) 1) := by
  let P := TopCat.of PUnit.{1}
  have : Subsingleton (Homology ℚ P (0 + 1)) :=
    MayerVietoris.subsingleton_homology_succ_of_totallyDisconnected _ 0
  have := MayerVietoris.finiteDimensional_homology_zero_of_pathConnected P
  have hP0 := MayerVietoris.finrank_homology_zero_of_pathConnected P
  have : Nonempty (cylU P) := ⟨⟨(PUnit.unit, ((1 / 4 : ℝ) : UnitAddCircle)), trivial,
    quarter_mem_U₀_inter_V₀.1⟩⟩
  have := (homologyCylUEquiv P (0 + 1)).symm.finiteDimensional
  have := (homologyCylVEquiv P (0 + 1)).symm.finiteDimensional
  have := (homologyCylUEquiv P 0).symm.finiteDimensional
  have := (homologyCylVEquiv P 0).symm.finiteDimensional
  have := finiteDimensional_homology_overlap P 0
  have := finiteDimensional_homology_overlap P (0 + 1)
  obtain ⟨-, h⟩ := MayerVietoris.finiteDimensional_homology_succ_and_finrank_eq
    (isOpen_cylU P) (isOpen_cylV P) (cylU_union_cylV P) 0
  have h0 := finrank_range_overlap_zero_add_one_le (X := cyl P) (cylU P) (cylV P)
  rw [(homologyCylUEquiv P 0).finrank_eq, (homologyCylVEquiv P 0).finrank_eq, hP0] at h0
  rw [(homologyCylUEquiv P (0 + 1)).finrank_eq, (homologyCylVEquiv P (0 + 1)).finrank_eq,
    finrank_zero_of_subsingleton (M := Homology ℚ P (0 + 1))] at h
  have := (homologyP₁Equiv P 0).symm.finiteDimensional
  have := (homologyP₂Equiv P 0).symm.finiteDimensional
  have hW := MayerVietoris.finrank_homology_eq_of_disjoint (isOpen_P₁ P) (isOpen_P₂ P)
    (P₁_union_P₂ P) (disjoint_P₁_P₂ P) 0
  rw [(homologyP₁Equiv P 0).finrank_eq, (homologyP₂Equiv P 0).finrank_eq, hP0] at hW
  have hW1 := finrank_homology_overlap_le P (0 + 1)
  rw [finrank_zero_of_subsingleton (M := Homology ℚ P (0 + 1))] at hW1
  have r1 := LinearMap.finrank_range_le (LinearMap.prod
    (homologyMap ℚ (0 + 1) (subsetIntersectionToLeft (cyl P) (cylU P) (cylV P)))
    (-homologyMap ℚ (0 + 1) (subsetIntersectionToRight (cyl P) (cylU P) (cylV P))))
  rw [(homologyPointProdCircleEquiv 1).symm.finrank_eq]
  change finrank ℚ (Homology ℚ (TopCat.of ↥(cylU P ∩ cylV P)) 0) = 2 at hW
  change finrank ℚ (Homology ℚ (TopCat.of ↥(cylU P ∩ cylV P)) (0 + 1)) ≤ 2 * 0 at hW1
  change 1 ≤ finrank ℚ (Homology ℚ (cyl P) (0 + 1))
  omega

/-- **Nonvacuity test, value.** `dim H_1(S¹; ℚ) = 1`, the point case of the Künneth count
`b_1(pt × S¹) = b_1(pt) + b_0(pt)`; it fails if positive-degree homology vanished. -/
theorem finrank_homology_one_circle :
    finrank ℚ (Homology ℚ (TopCat.of UnitAddCircle) 1) = 1 :=
  le_antisymm finrank_homology_one_circle_le one_le_finrank_homology_one_circle

end HodgeLadder.CircleCylinder
