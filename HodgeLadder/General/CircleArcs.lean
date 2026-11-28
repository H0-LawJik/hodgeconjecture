module

public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Two arcs covering the circle

On the circle `UnitAddCircle = AddCircle (1 : ℝ)`, the complements `U₀ = {↑0}ᶜ` and
`V₀ = {↑(1/2)}ᶜ` of two points are open, cover the circle and are contractible, each being
homeomorphic to an open interval of length one through `AddCircle.openPartialHomeomorphCoe`.
Their intersection is the union of the two open arcs `W₁ = ↑(0, 1/2)` and `W₂ = ↑(1/2, 1)`,
which are disjoint, open and contractible. The point `↑(1/4)` lies in `W₁` and `↑(3/4)` in `W₂`.

This is the cover used by a Mayer–Vietoris count on a product `Y × S¹`: the contractibility
instances let a consumer replace each piece by a point, and `↑(1/4)` gives a section into the
overlap. On the cylinder `X = Y × UnitAddCircle` with `U = univ ×ˢ U₀`, the bridge to `Y × ↥U₀` is
`(Homeomorph.Set.prod Set.univ U₀).trans ((Homeomorph.Set.univ Y).prodCongr (Homeomorph.refl _))`,
and the overlap `↥(U ∩ V)` splits along the preimages of `W₁` and `W₂` under the second
coordinate.

## Main definitions

* `HodgeLadder.CircleArcs.U₀`, `HodgeLadder.CircleArcs.V₀`: the complements of `↑0` and `↑(1/2)`
* `HodgeLadder.CircleArcs.W₁`, `HodgeLadder.CircleArcs.W₂`: the images of `(0, 1/2)` and
  `(1/2, 1)`
* `HodgeLadder.CircleArcs.W₁HomeomorphIoo`, `HodgeLadder.CircleArcs.W₂HomeomorphIoo`: the arcs
  as open intervals

## Main results

* `HodgeLadder.CircleArcs.isOpen_U₀`, `isOpen_V₀`, `U₀_union_V₀`: an open cover of the circle
* `HodgeLadder.CircleArcs.contractibleSpace_compl_singleton`: the complement of any point of
  `AddCircle p`, `0 < p`, is contractible, with instances `contractibleSpace_U₀` and `contractibleSpace_V₀`
* `HodgeLadder.CircleArcs.U₀_inter_V₀`: `U₀ ∩ V₀ = W₁ ∪ W₂`
* `HodgeLadder.CircleArcs.isOpen_W₁`, `isOpen_W₂`, `disjoint_W₁_W₂`, and the instances
  `contractibleSpace_W₁`, `contractibleSpace_W₂`
* `HodgeLadder.CircleArcs.quarter_mem_W₁`, `threeQuarter_mem_W₂`: the arcs are nonempty
* `HodgeLadder.CircleArcs.quarter_mem_U₀_inter_V₀`: the section point lies in the overlap
* `HodgeLadder.CircleArcs.circle_arc_cover`: all of the above in one statement
-/

@[expose] public section

namespace HodgeLadder.CircleArcs

open Set

/-- The circle minus the point `↑0`. -/
def U₀ : Set UnitAddCircle := {((0 : ℝ) : UnitAddCircle)}ᶜ

/-- The circle minus the point `↑(1/2)`. -/
def V₀ : Set UnitAddCircle := {((1 / 2 : ℝ) : UnitAddCircle)}ᶜ

/-- The open arc `↑(0, 1/2)`. -/
def W₁ : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Ioo 0 (1 / 2)

/-- The open arc `↑(1/2, 1)`. -/
def W₂ : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 2) 1

/-- Two reals in `[0, 1)` have the same image in the circle exactly when they are equal. -/
theorem coe_eq_coe_iff_of_mem_Ico {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) :
    (s : UnitAddCircle) = t ↔ s = t :=
  AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) (by rwa [zero_add]) (by rwa [zero_add])

/-- For `S ⊆ [0, 1)` and `t ∈ [0, 1)`, the point `↑t` lies in the image of `S` exactly when
`t ∈ S`. -/
theorem coe_mem_image_iff {S : Set ℝ} (hS : S ⊆ Ico 0 1) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (t : UnitAddCircle) ∈ ((↑) : ℝ → UnitAddCircle) '' S ↔ t ∈ S := by
  constructor
  · rintro ⟨s, hs, hst⟩
    rwa [← (coe_eq_coe_iff_of_mem_Ico (hS hs) ht).1 hst]
  · exact fun h => ⟨t, h, rfl⟩

/-- `U₀` is open. -/
theorem isOpen_U₀ : IsOpen U₀ := isOpen_compl_singleton

/-- `V₀` is open. -/
theorem isOpen_V₀ : IsOpen V₀ := isOpen_compl_singleton

/-- `U₀` and `V₀` cover the circle. -/
theorem U₀_union_V₀ : U₀ ∪ V₀ = univ := by
  refine eq_univ_iff_forall.2 fun x => ?_
  by_contra h
  simp only [U₀, V₀, mem_union, mem_compl_iff, mem_singleton_iff, not_or, not_not] at h
  have h01 := (coe_eq_coe_iff_of_mem_Ico (s := 0) (t := 1 / 2) (by norm_num) (by norm_num)).1
    (h.1.symm.trans h.2)
  norm_num at h01

/-- The complement of any point of a circle `AddCircle p` of positive period is contractible: it
is homeomorphic to an open interval of length `p` through `AddCircle.openPartialHomeomorphCoe`. -/
theorem contractibleSpace_compl_singleton {p : ℝ} [Fact (0 < p)] (x : AddCircle p) :
    ContractibleSpace ({x}ᶜ : Set (AddCircle p)) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  have : ContractibleSpace (Ioo a (a + p)) :=
    (convex_Ioo a (a + p)).contractibleSpace
      (nonempty_Ioo.2 (lt_add_of_pos_right a (Fact.out : 0 < p)))
  let h : ({(a : AddCircle p)}ᶜ : Set (AddCircle p)) ≃ₜ Ioo a (a + p) :=
    (AddCircle.openPartialHomeomorphCoe p a).toHomeomorphSourceTarget.symm
  exact h.contractibleSpace

/-- `U₀` is contractible. -/
instance contractibleSpace_U₀ : ContractibleSpace U₀ := contractibleSpace_compl_singleton _

/-- `V₀` is contractible. -/
instance contractibleSpace_V₀ : ContractibleSpace V₀ := contractibleSpace_compl_singleton _

/-- The overlap of `U₀` and `V₀` is the union of the two arcs `W₁` and `W₂`. -/
theorem U₀_inter_V₀ : U₀ ∩ V₀ = W₁ ∪ W₂ := by
  ext x
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico x
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := by norm_num
  have h12 : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 := by norm_num
  simp only [U₀, V₀, W₁, W₂, mem_inter_iff, mem_union, mem_compl_iff, mem_singleton_iff,
    coe_eq_coe_iff_of_mem_Ico ht h0, coe_eq_coe_iff_of_mem_Ico ht h12,
    coe_mem_image_iff (S := Ioo 0 (1 / 2)) (fun s hs => ⟨hs.1.le, by linarith [hs.2]⟩) ht,
    coe_mem_image_iff (S := Ioo (1 / 2) 1) (fun s hs => ⟨by linarith [hs.1], hs.2⟩) ht, mem_Ioo]
  obtain ⟨ht0, ht1⟩ := ht
  constructor
  · rintro ⟨hne0, hne12⟩
    rcases lt_or_gt_of_ne hne12 with h | h
    · exact Or.inl ⟨lt_of_le_of_ne ht0 (Ne.symm hne0), h⟩
    · exact Or.inr ⟨h, ht1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1.ne', h2.ne⟩
    · exact ⟨by linarith, h1.ne'⟩

/-- `W₁` is open. -/
theorem isOpen_W₁ : IsOpen W₁ := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

/-- `W₂` is open. -/
theorem isOpen_W₂ : IsOpen W₂ := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

/-- The arcs `W₁` and `W₂` are disjoint. -/
theorem disjoint_W₁_W₂ : Disjoint W₁ W₂ := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
  have := (coe_eq_coe_iff_of_mem_Ico ⟨by linarith [ht.1], ht.2⟩ ⟨hs.1.le, by linarith [hs.2]⟩).1 hts
  linarith [hs.2, ht.1]

/-- The arc `W₁` is homeomorphic to the open interval `(0, 1/2)`, through the inverse of the
quotient map on `(0, 1)`. -/
noncomputable def W₁HomeomorphIoo : W₁ ≃ₜ Ioo (0 : ℝ) (1 / 2) :=
  ((AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0).homeomorphOfImageSubsetSource
    (s := Ioo (0 : ℝ) (1 / 2)) (t := W₁)
    (fun s hs => ⟨hs.1, by rw [zero_add]; linarith [hs.2]⟩) rfl).symm

/-- The arc `W₂` is homeomorphic to the open interval `(1/2, 1)`, through the inverse of the
quotient map on `(0, 1)`. -/
noncomputable def W₂HomeomorphIoo : W₂ ≃ₜ Ioo (1 / 2 : ℝ) 1 :=
  ((AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0).homeomorphOfImageSubsetSource
    (s := Ioo (1 / 2 : ℝ) 1) (t := W₂)
    (fun s hs => ⟨by linarith [hs.1], by rw [zero_add]; exact hs.2⟩) rfl).symm

/-- `W₁` is contractible. -/
instance contractibleSpace_W₁ : ContractibleSpace W₁ :=
  haveI : ContractibleSpace (Ioo (0 : ℝ) (1 / 2)) :=
    (convex_Ioo _ _).contractibleSpace (nonempty_Ioo.2 (by norm_num))
  W₁HomeomorphIoo.contractibleSpace

/-- `W₂` is contractible. -/
instance contractibleSpace_W₂ : ContractibleSpace W₂ :=
  haveI : ContractibleSpace (Ioo (1 / 2 : ℝ) 1) :=
    (convex_Ioo _ _).contractibleSpace (nonempty_Ioo.2 (by norm_num))
  W₂HomeomorphIoo.contractibleSpace

/-- The point `↑(1/4)` lies in `W₁`. -/
theorem quarter_mem_W₁ : ((1 / 4 : ℝ) : UnitAddCircle) ∈ W₁ := ⟨1 / 4, by norm_num, rfl⟩

/-- The point `↑(3/4)` lies in `W₂`. -/
theorem threeQuarter_mem_W₂ : ((3 / 4 : ℝ) : UnitAddCircle) ∈ W₂ := ⟨3 / 4, by norm_num, rfl⟩

/-- The point `↑(1/4)` lies in the overlap `U₀ ∩ V₀`; it is the section point of a cylinder
`Y × S¹`. -/
theorem quarter_mem_U₀_inter_V₀ : ((1 / 4 : ℝ) : UnitAddCircle) ∈ U₀ ∩ V₀ := by
  rw [U₀_inter_V₀]
  exact Or.inl quarter_mem_W₁

/-- The circle cover in one statement: `U₀` and `V₀` are open, cover the circle and are
contractible; their overlap is `W₁ ∪ W₂` with `W₁`, `W₂` open, disjoint and contractible; and
`↑(1/4) ∈ W₁`, `↑(3/4) ∈ W₂`. -/
theorem circle_arc_cover :
    IsOpen U₀ ∧ IsOpen V₀ ∧ U₀ ∪ V₀ = univ ∧ ContractibleSpace U₀ ∧ ContractibleSpace V₀ ∧
      U₀ ∩ V₀ = W₁ ∪ W₂ ∧ IsOpen W₁ ∧ IsOpen W₂ ∧ Disjoint W₁ W₂ ∧
      ContractibleSpace W₁ ∧ ContractibleSpace W₂ ∧
      ((1 / 4 : ℝ) : UnitAddCircle) ∈ W₁ ∧ ((3 / 4 : ℝ) : UnitAddCircle) ∈ W₂ :=
  ⟨isOpen_U₀, isOpen_V₀, U₀_union_V₀, inferInstance, inferInstance, U₀_inter_V₀, isOpen_W₁,
    isOpen_W₂, disjoint_W₁_W₂, inferInstance, inferInstance, quarter_mem_W₁, threeQuarter_mem_W₂⟩

end HodgeLadder.CircleArcs
