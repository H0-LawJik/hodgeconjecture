module

public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.Constant
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import HodgeLadder.General.LocallyConstantSheaf

/-!
# The constant sheaf `ℤ` as locally constant functions

Upstream defines the constant sheaf `𝓒(Y; ℤ)` by sheafifying the constant presheaf. This file
builds the sheaf of continuous (that is, locally constant) `ℤ`-valued functions and identifies the
two: the map from the constant presheaf is locally injective and locally surjective. Part of rung
`unit-extension-of-invertible` (step B2).

This is the case `A = ℤ` of `HodgeLadder.constantSheafIsoLocallyConstantSheaf`, written with
continuous functions in place of Mathlib's `LocallyConstant`; `constIsoLC_trans_lcSheafIso`
identifies the two.

## Main definitions

* `HodgeLadder.lcSheaf`, `HodgeLadder.constIsoLC`

## Main results

* `HodgeLadder.toSheafify_constToLCSheaf`
* `HodgeLadder.lcSheafIsoLocallyConstantSheaf`, `HodgeLadder.constIsoLC_trans_lcSheafIso`:
  comparison with the general `HodgeLadder.constantSheafIsoLocallyConstantSheaf`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace HodgeLadder

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable (Y : TopCat.{0})

/-- Continuous `ℤ`-valued functions on an open set. -/
def lcSubgroup (U : Opens Y) : AddSubgroup (U → ℤ) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := hf.add hg
  neg_mem' hf := hf.neg

/-- The presheaf of locally constant integer functions. -/
def lcPresheaf : TopCat.Presheaf AddCommGrpCat Y where
  obj U := AddCommGrpCat.of (lcSubgroup Y (unop U))
  map i := AddCommGrpCat.ofHom
    { toFun f := ⟨fun x => f.1 ⟨x.1, i.unop.le x.2⟩,
        (TopCat.continuousLocal Y ℤ).res i.unop f.1 f.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sheaf of locally constant integer functions. -/
def lcSheaf : TopCat.Sheaf AddCommGrpCat Y where
  obj := lcPresheaf Y
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat)]
    exact (TopCat.subsheafToTypes (TopCat.continuousLocal Y ℤ)).property

/-- Constants as locally constant functions. -/
def constToLC : (Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℤ) ⟶ lcPresheaf Y where
  app _ := AddCommGrpCat.ofHom
    { toFun m := ⟨fun _ => m, continuous_const⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

instance constToLC_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) (constToLC Y) := by
  rw [← TopCat.Presheaf.IsLocallySurjective, TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  let f : U → ℤ := t.1
  have hf : Continuous f := t.2
  let V : Opens Y := ⟨Subtype.val '' (f ⁻¹' {f ⟨x, hx⟩}),
    U.isOpen.isOpenMap_subtype_val _ ((isOpen_discrete _).preimage hf)⟩
  have hVU : V ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  refine ⟨V, hVU, ⟨f ⟨x, hx⟩, ?_⟩, ⟨⟨x, hx⟩, rfl, rfl⟩⟩
  apply Subtype.ext
  funext y
  obtain ⟨y', hy', hyy'⟩ := y.2
  change f ⟨x, hx⟩ = f ⟨y.1, hVU y.2⟩
  have : (⟨y.1, hVU y.2⟩ : U) = y' := Subtype.ext hyy'.symm
  rw [this]
  exact hy'.symm

instance constToLC_isLocallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) (constToLC Y) where
  equalizerSieve_mem {_} m m' h := by
    intro x hx
    have hmm : m = m' := congrFun (congrArg Subtype.val h) ⟨x, hx⟩
    exact ⟨_, 𝟙 _, by simp [Presheaf.equalizerSieve, hmm], hx⟩

/-- The comparison from the constant sheaf to locally constant functions. -/
def constToLCSheaf : TopCat.Sheaf.const Y (AddCommGrpCat.of ℤ) ⟶ lcSheaf Y :=
  ⟨sheafifyLift (Opens.grothendieckTopology Y) (constToLC Y) (lcSheaf Y).property⟩

/-- `constToLCSheaf` restricts along the sheafification map to `constToLC`. -/
lemma toSheafify_constToLCSheaf :
    toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℤ)) ≫ (constToLCSheaf Y).hom =
      constToLC Y :=
  toSheafify_sheafifyLift ..

instance isIso_constToLCSheaf : IsIso (constToLCSheaf Y) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (J := Opens.grothendieckTopology Y)
    (A := AddCommGrpCat.{0})]
  have fac := toSheafify_constToLCSheaf Y
  have h1 : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℤ)) ≫ (constToLCSheaf Y).hom) := by
    rw [fac]
    exact constToLC_isLocallySurjective Y
  have h2 : Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℤ)) ≫ (constToLCSheaf Y).hom) := by
    rw [fac]
    exact constToLC_isLocallyInjective Y
  exact ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
      (Opens.grothendieckTopology Y) (toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℤ))) _,
    Presheaf.isLocallySurjective_of_isLocallySurjective (Opens.grothendieckTopology Y)
      (toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℤ))) _⟩

/-- **The constant sheaf `ℤ` is the sheaf of locally constant integer functions.** -/
def constIsoLC : TopCat.Sheaf.const Y (AddCommGrpCat.of ℤ) ≅ lcSheaf Y :=
  asIso (constToLCSheaf Y)

/-- Continuous integer functions are the locally constant ones: the presheaf `lcPresheaf Y` is
`locallyConstantPresheaf Y ℤ`. -/
def lcPresheafIsoLocallyConstantPresheaf : lcPresheaf Y ≅ locallyConstantPresheaf Y ℤ :=
  NatIso.ofComponents (fun _ => AddEquiv.toAddCommGrpIso
    { toFun f := ⟨f.1, (IsLocallyConstant.iff_continuous _).2 f.2⟩
      invFun f := ⟨⇑(show LocallyConstant _ ℤ from f), (show LocallyConstant _ ℤ from f).continuous⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl })
    (fun _ => rfl)

/-- The sheaf `lcSheaf Y` of continuous integer functions is the sheaf
`locallyConstantSheaf Y ℤ` of locally constant integer functions. -/
def lcSheafIsoLocallyConstantSheaf : lcSheaf Y ≅ locallyConstantSheaf Y ℤ :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (lcPresheafIsoLocallyConstantPresheaf Y)

/-- **`constIsoLC` is the case `A = ℤ` of the general comparison**: followed by the identification
of continuous and locally constant integer functions, it is
`constantSheafIsoLocallyConstantSheaf Y ℤ`. -/
theorem constIsoLC_trans_lcSheafIso :
    constIsoLC Y ≪≫ lcSheafIsoLocallyConstantSheaf Y = constantSheafIsoLocallyConstantSheaf Y ℤ := by
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (locallyConstantSheaf Y ℤ).property
  rw [constantSheafIsoLocallyConstantSheaf_hom, toSheafify_constantSheafToLocallyConstantSheaf_hom]
  have h := congrArg (fun φ => φ ≫ (lcSheafIsoLocallyConstantSheaf Y).hom.hom)
    (toSheafify_constToLCSheaf Y)
  exact (Category.assoc _ _ _).symm.trans h

end HodgeLadder
