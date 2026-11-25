module

public import LefschetzPort.AlgebraicGeometry.HolomorphicSheafGenerators

/-!
# Line bundles with the same transition functions are isomorphic

Let `M` and `M'` be holomorphic sheaves of modules with generating sections `σ i` and `f i` on
the members `V i` of an open cover, and suppose the two families have the same transition
functions: whenever `r • σ i = σ j` on an open below `V i ⊓ V j`, also `r • f i = f j` there.
Then `M ≅ M'`. A section `s` of `M` has unique coefficients `cᵢ` with `s = cᵢ • σ i` near each
point, and the image of `s` glues the local sections `cᵢ • f i` of `M'`. Part of rung
`unit-extension-of-invertible` (step B4).

## Main results

* `HodgeLadder.Frames.isoOfSameTransitions`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexPoint

namespace HodgeLadder

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance frameComparisonTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- Frames of a holomorphic sheaf of modules on an open cover. -/
structure Frames (M : SheafOfModules (holomorphicRingSheaf X d)) (ι : Type) where
  /-- The members of the cover. -/
  opens : ι → Opens (TopCat.of (ComplexPoint X))
  /-- The members cover the analytic space. -/
  covers (z : ComplexPoint X) : ∃ i, z ∈ opens i
  /-- The frame on each member. -/
  gen (i : ι) : M.val.obj (op (opens i))
  /-- Each frame generates. -/
  generates (i : ι) : HolomorphicGenerates (gen i)

variable {M : SheafOfModules (holomorphicRingSheaf X d)} {ι : Type} (c : Frames M ι)

namespace Frames

/-- The coefficient of a section with respect to the frame `i`, on `W ⊓ V i`. -/
def coeff {W : Opens (TopCat.of (ComplexPoint X))} (i : ι) (s : M.val.obj (op W)) :
    (holomorphicRingSheaf X d).obj.obj (op (W ⊓ c.opens i)) :=
  ((c.generates i).exists_smul_eq inf_le_right (holRes M inf_le_left s)).choose

lemma coeff_spec {W : Opens (TopCat.of (ComplexPoint X))} (i : ι) (s : M.val.obj (op W)) :
    c.coeff i s • holRes M inf_le_right (c.gen i) = holRes M inf_le_left s :=
  ((c.generates i).exists_smul_eq inf_le_right (holRes M inf_le_left s)).choose_spec

/-- Coefficients are determined by the equation they satisfy. -/
lemma coeff_eq_of_smul_eq {W : Opens (TopCat.of (ComplexPoint X))} (i : ι)
    (s : M.val.obj (op W)) (r : (holomorphicRingSheaf X d).obj.obj (op (W ⊓ c.opens i)))
    (hr : r • holRes M inf_le_right (c.gen i) = holRes M inf_le_left s) : c.coeff i s = r :=
  (c.generates i).smul_left_injective inf_le_right ((c.coeff_spec i s).trans hr.symm)

end Frames

/-- The underlying sheaf of abelian groups of a holomorphic sheaf of modules. -/
abbrev sheafAb (M : SheafOfModules (holomorphicRingSheaf X d)) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  ⟨M.val.presheaf, M.isSheaf⟩

variable {M' : SheafOfModules (holomorphicRingSheaf X d)}

/-- Frames `f i` of `M'` on the opens of `c` have the same transition functions as `c`. -/
def SameTransitions (c : Frames M ι) (f : ∀ i, M'.val.obj (op (c.opens i))) : Prop :=
  ∀ (i j : ι) (W : Opens (TopCat.of (ComplexPoint X)))
    (hi : W ≤ c.opens i) (hj : W ≤ c.opens j) (r : (holomorphicRingSheaf X d).obj.obj (op W)),
      r • holRes M hi (c.gen i) = holRes M hj (c.gen j) →
        r • holRes M' hi (f i) = holRes M' hj (f j)

namespace Frames

/-- The frames `f` of `M'` on the same cover. -/
def transfer (f : ∀ i, M'.val.obj (op (c.opens i))) (hf : ∀ i, HolomorphicGenerates (f i)) :
    Frames M' ι where
  opens := c.opens
  covers := c.covers
  gen := f
  generates := hf

/-- The local pieces `cᵢ(s) • fᵢ` of the image of `s`. -/
def piece (f : ∀ i, M'.val.obj (op (c.opens i))) {W : Opens (TopCat.of (ComplexPoint X))}
    (s : M.val.obj (op W)) (i : ι) : M'.val.obj (op (W ⊓ c.opens i)) :=
  c.coeff i s • holRes M' inf_le_right (f i)

end Frames

namespace Frames

/-- Restriction of the ring of holomorphic functions. -/
abbrev ringRes {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
    (r : (holomorphicRingSheaf X d).obj.obj (op U)) : (holomorphicRingSheaf X d).obj.obj (op V) :=
  (holomorphicRingSheaf X d).obj.map (homOfLE h).op r

/-- Restriction of the defining equation of a coefficient. -/
lemma coeff_spec_res {W O : Opens (TopCat.of (ComplexPoint X))} (i : ι) (s : M.val.obj (op W))
    (hO : O ≤ W ⊓ c.opens i) :
    ringRes hO (c.coeff i s) • holRes M (hO.trans inf_le_right) (c.gen i) =
      holRes M (hO.trans inf_le_left) s := by
  have := congrArg (holRes M hO) (c.coeff_spec i s)
  rwa [holRes_smul, holRes_holRes, holRes_holRes] at this

/-- The local pieces are compatible. -/
lemma piece_compatible (f : ∀ i, M'.val.obj (op (c.opens i))) (hT : SameTransitions c f)
    {W : Opens (TopCat.of (ComplexPoint X))} (s : M.val.obj (op W)) :
    TopCat.Presheaf.IsCompatible (sheafAb M').1 (fun i => W ⊓ c.opens i) (c.piece f s) := by
  intro i j
  set O := (W ⊓ c.opens i) ⊓ (W ⊓ c.opens j)
  have hOi : O ≤ W ⊓ c.opens i := inf_le_left
  have hOj : O ≤ W ⊓ c.opens j := inf_le_right
  obtain ⟨u, -, hu⟩ := ((c.generates i).restrict (hOi.trans inf_le_right)).exists_isUnit_smul_eq
    ((c.generates j).restrict (hOj.trans inf_le_right))
  have hci := c.coeff_spec_res i s hOi
  have hcj := c.coeff_spec_res j s hOj
  have hcoeff : ringRes hOi (c.coeff i s) = ringRes hOj (c.coeff j s) * u := by
    apply (c.generates i).smul_left_injective (hOi.trans inf_le_right)
    change ringRes hOi (c.coeff i s) • holRes M _ (c.gen i) =
      (ringRes hOj (c.coeff j s) * u) • holRes M _ (c.gen i)
    rw [mul_smul, hu, hci, hcj]
  have hf := hT i j O (hOi.trans inf_le_right) (hOj.trans inf_le_right) u hu
  change holRes M' hOi (c.piece f s i) = holRes M' hOj (c.piece f s j)
  unfold piece
  rw [holRes_smul, holRes_holRes, holRes_smul, holRes_holRes]
  change ringRes hOi (c.coeff i s) • holRes M' (hOi.trans inf_le_right) (f i) =
    ringRes hOj (c.coeff j s) • holRes M' (hOj.trans inf_le_right) (f j)
  rw [hcoeff, mul_smul, hf]

end Frames

namespace Frames

lemma le_iSup_inf (W : Opens (TopCat.of (ComplexPoint X))) : W ≤ ⨆ i, W ⊓ c.opens i := by
  intro z hz
  obtain ⟨i, hi⟩ := c.covers z
  exact Opens.mem_iSup.mpr ⟨i, ⟨hz, hi⟩⟩

variable (f : ∀ i, M'.val.obj (op (c.opens i))) (hT : SameTransitions c f)

/-- The image of a section: the gluing of its local pieces. -/
def image {W : Opens (TopCat.of (ComplexPoint X))} (s : M.val.obj (op W)) : M'.val.obj (op W) :=
  ((sheafAb M').existsUnique_gluing' (fun i => W ⊓ c.opens i) W (fun _ => homOfLE inf_le_left)
    (c.le_iSup_inf W) (c.piece f s) (c.piece_compatible f hT s)).exists.choose

lemma image_spec {W : Opens (TopCat.of (ComplexPoint X))} (s : M.val.obj (op W)) (i : ι) :
    holRes M' inf_le_left (c.image f hT s) = c.piece f s i := by
  unfold image
  exact ((sheafAb M').existsUnique_gluing' (fun i => W ⊓ c.opens i) W (fun _ => homOfLE inf_le_left)
    (c.le_iSup_inf W) (c.piece f s) (c.piece_compatible f hT s)).exists.choose_spec i

/-- A section of `M'` is the image of `s` as soon as it restricts to the pieces. -/
lemma eq_image {W : Opens (TopCat.of (ComplexPoint X))} (s : M.val.obj (op W))
    (t : M'.val.obj (op W)) (ht : ∀ i, holRes M' inf_le_left t = c.piece f s i) :
    t = c.image f hT s :=
  (sheafAb M').eq_of_locally_eq' (fun i => W ⊓ c.opens i) W (fun _ => homOfLE inf_le_left)
    (c.le_iSup_inf W) _ _ fun i => (ht i).trans (c.image_spec f hT s i).symm

end Frames

namespace Frames

lemma holRes_add {N : SheafOfModules (holomorphicRingSheaf X d)}
    {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U) (s t : N.val.obj (op U)) :
    holRes N h (s + t) = holRes N h s + holRes N h t :=
  map_add _ _ _

lemma coeff_add {W : Opens (TopCat.of (ComplexPoint X))} (i : ι) (s t : M.val.obj (op W)) :
    c.coeff i (s + t) = c.coeff i s + c.coeff i t := by
  apply c.coeff_eq_of_smul_eq
  rw [add_smul, c.coeff_spec, c.coeff_spec, holRes_add]

lemma coeff_smul {W : Opens (TopCat.of (ComplexPoint X))} (i : ι)
    (r : (holomorphicRingSheaf X d).obj.obj (op W)) (s : M.val.obj (op W)) :
    c.coeff i (r • s) = ringRes inf_le_left r * c.coeff i s := by
  apply c.coeff_eq_of_smul_eq
  rw [mul_smul, c.coeff_spec, holRes_smul]

lemma coeff_res {V W : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ W) (i : ι)
    (s : M.val.obj (op W)) :
    c.coeff i (holRes M h s) = ringRes (inf_le_inf_right _ h) (c.coeff i s) := by
  apply c.coeff_eq_of_smul_eq
  rw [c.coeff_spec_res i s (inf_le_inf_right _ h), holRes_holRes]

variable (f : ∀ i, M'.val.obj (op (c.opens i))) (hT : SameTransitions c f)

lemma image_add {W : Opens (TopCat.of (ComplexPoint X))} (s t : M.val.obj (op W)) :
    c.image f hT (s + t) = c.image f hT s + c.image f hT t := by
  symm
  apply c.eq_image
  intro i
  rw [holRes_add, c.image_spec, c.image_spec]
  simp only [piece, c.coeff_add, add_smul]

lemma image_smul {W : Opens (TopCat.of (ComplexPoint X))}
    (r : (holomorphicRingSheaf X d).obj.obj (op W)) (s : M.val.obj (op W)) :
    c.image f hT (r • s) = r • c.image f hT s := by
  symm
  apply c.eq_image
  intro i
  rw [holRes_smul, c.image_spec]
  simp only [piece, c.coeff_smul, mul_smul]

lemma image_res {V W : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ W) (s : M.val.obj (op W)) :
    c.image f hT (holRes M h s) = holRes M' h (c.image f hT s) := by
  symm
  apply c.eq_image
  intro i
  rw [holRes_holRes, ← holRes_holRes (inf_le_left : W ⊓ c.opens i ≤ W) (inf_le_inf_right (c.opens i) h),
    c.image_spec]
  simp only [piece, c.coeff_res]
  rw [holRes_smul, holRes_holRes]

end Frames

namespace Frames

variable (f : ∀ i, M'.val.obj (op (c.opens i))) (hT : SameTransitions c f)

/-- The image map as a morphism of sheaves of modules. -/
def imageHom : M ⟶ M' :=
  ⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom (AddMonoidHom.mk' (c.image f hT) (c.image_add f hT))
      naturality {W V} g := by
        ext s
        change c.image f hT (M.val.presheaf.map g s) = M'.val.presheaf.map g (c.image f hT s)
        have hg : g = (homOfLE (leOfHom g.unop)).op := Subsingleton.elim _ _
        rw [hg]
        exact c.image_res f hT (leOfHom g.unop) s }
    (fun _ r s => c.image_smul f hT r s)⟩

lemma imageHom_apply {W : Opens (TopCat.of (ComplexPoint X))} (s : M.val.obj (op W)) :
    (c.imageHom f hT).val.app (op W) s = c.image f hT s := rfl

variable (hf : ∀ i, HolomorphicGenerates (f i))

lemma coeff_transfer_image {W : Opens (TopCat.of (ComplexPoint X))} (i : ι)
    (s : M.val.obj (op W)) : (c.transfer f hf).coeff i (c.image f hT s) = c.coeff i s :=
  (c.transfer f hf).coeff_eq_of_smul_eq i _ _ (c.image_spec f hT s i).symm

include hT in
/-- The transition functions agree in the other direction too. -/
lemma sameTransitions_symm : SameTransitions (c.transfer f hf) c.gen := by
  intro i j W hi hj r hr
  obtain ⟨r', hr'⟩ := (c.generates i).exists_smul_eq hi (holRes M hj (c.gen j))
  have h' := hT i j W hi hj r' hr'
  have : r = r' := (hf i).smul_left_injective hi (hr.trans h'.symm)
  rw [this]
  exact hr'

lemma image_transfer_image {W : Opens (TopCat.of (ComplexPoint X))} (s : M.val.obj (op W)) :
    (c.transfer f hf).image c.gen (c.sameTransitions_symm f hT hf) (c.image f hT s) = s := by
  symm
  apply (c.transfer f hf).eq_image
  intro i
  simp only [piece, c.coeff_transfer_image f hT hf]
  exact (c.coeff_spec i s).symm

end Frames

namespace Frames

variable (f : ∀ i, M'.val.obj (op (c.opens i))) (hT : SameTransitions c f)
  (hf : ∀ i, HolomorphicGenerates (f i))

/-- **Frames with the same transition functions give isomorphic sheaves.** -/
def isoOfSameTransitions : M ≅ M' where
  hom := c.imageHom f hT
  inv := (c.transfer f hf).imageHom c.gen (c.sameTransitions_symm f hT hf)
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    ext W s
    exact c.image_transfer_image f hT hf s
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    ext W t
    exact (c.transfer f hf).image_transfer_image c.gen (c.sameTransitions_symm f hT hf)
      c.generates t

end Frames

end HodgeLadder
