module

public import HodgeLadder.Cup.SheafExact
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Exactness of the tensor product of rational sheaves

Let `Y` be a topological space. Sheaves of `ℚ`-vector spaces on `Y` carry the monoidal structure
`Sheaf.monoidalCategory` obtained by localizing the pointwise tensor product of presheaves along
sheafification; here it is the local instance `sheafMonoidal`. Tensoring with a sheaf `F` is
isomorphic to: take underlying presheaves, tensor pointwise with `F`, sheafify. Pointwise tensor
over the field `ℚ` is exact and preserves colimits, sheafification is exact and preserves
colimits, so tensoring with `F` is exact in each variable. The unit is the constant sheaf
`ℚ_Y`. Rung `sheaf-tensor-exact` (front `cup`, decision 0009).

## Main definitions

* `HodgeLadder.Cup.sheafMonoidal`, `HodgeLadder.Cup.sheafBraided`: the monoidal structure and
  its braiding, from `Sheaf.monoidalCategory` and `Sheaf.braidedCategory`.
* `HodgeLadder.Cup.tensorLeftIso`: `tensorLeft F ≅ forget ⋙ tensorLeft F.obj ⋙ sheafify`.

## Main results

* `HodgeLadder.Cup.tensor_exact`: for every sheaf `F`, `tensorLeft F` and `tensorRight F`
  preserve finite limits and finite colimits and are additive (also as instances
  `tensorLeft_preservesFiniteLimits`, `tensorLeft_preservesFiniteColimits`,
  `tensorLeft_additive` and their `tensorRight` versions).
* `HodgeLadder.Cup.tensorLeft_preservesColimits`, `HodgeLadder.Cup.tensorRight_preservesColimits`:
  small colimits are preserved.
* `HodgeLadder.Cup.unitIsoQX`: `𝟙_ ≅ ℚ_Y`, by `Iso.refl`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HodgeLadder.Cup

variable (Y : TopCat.{0})

/-- Presheaves of `ℚ`-vector spaces on `Y`. -/
abbrev PreQ := (TopologicalSpace.Opens Y)ᵒᵖ ⥤ ModuleCat.{0} ℚ

/-- Sheaves of `ℚ`-vector spaces on `Y`. -/
abbrev ShQ := Sheaf (J Y) (ModuleCat.{0} ℚ)

/-- The monoidal structure on sheaves of `ℚ`-vector spaces on `Y`. -/
abbrev sheafMonoidal : MonoidalCategory (ShQ Y) :=
  Sheaf.monoidalCategory (J Y) (ModuleCat.{0} ℚ)

attribute [local instance] sheafMonoidal

/-- Sheafification. -/
abbrev sheafifyQ : PreQ Y ⥤ ShQ Y := presheafToSheaf (J Y) (ModuleCat.{0} ℚ)

/-- Presheaves underlying sheaves. -/
abbrev presheafQ : ShQ Y ⥤ PreQ Y := sheafToPresheaf (J Y) (ModuleCat.{0} ℚ)

/-- Sheafifying a sheaf gives it back. -/
def sheafifyIso : presheafQ Y ⋙ sheafifyQ Y ≅ 𝟭 _ :=
  asIso (sheafificationAdjunction (J Y) (ModuleCat.{0} ℚ)).counit

/-- Tensoring with a sheaf after sheafifying is sheafifying after tensoring. -/
def commLeft (P : PreQ Y) :
    sheafifyQ Y ⋙ tensorLeft ((sheafifyQ Y).obj P) ≅ tensorLeft P ⋙ sheafifyQ Y :=
  Functor.Monoidal.commTensorLeft (sheafifyQ Y) P

/-- Tensoring presheaves with `P` is computed at each open. -/
def evalTensorLeft (P : PreQ Y) (W : (TopologicalSpace.Opens Y)ᵒᵖ) :
    tensorLeft P ⋙ (evaluation _ _).obj W ≅ (evaluation _ _).obj W ⋙ tensorLeft (P.obj W) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp)

/-- Tensoring presheaves of `ℚ`-vector spaces is left exact, since every `ℚ`-vector space is
flat. -/
instance presheafTensorLeft_preservesFiniteLimits (P : PreQ Y) :
    PreservesFiniteLimits (tensorLeft P) :=
  preservesFiniteLimits_of_evaluation _ fun W =>
    preservesFiniteLimits_of_natIso (evalTensorLeft Y P W).symm

/-- Tensoring presheaves of `ℚ`-vector spaces preserves small colimits. -/
instance presheafTensorLeft_preservesColimits (P : PreQ Y) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
  preservesColimits_of_evaluation _ fun W =>
    preservesColimits_of_natIso (evalTensorLeft Y P W).symm

/-- A functor on sheaves preserves colimits of a shape once its composite with sheafification
does: every diagram of sheaves is the sheafification of its diagram of underlying presheaves. -/
theorem preservesColimitsOfShape_of_sheafify (T : ShQ Y ⥤ ShQ Y) (K : Type) [SmallCategory K]
    [PreservesColimitsOfShape K (sheafifyQ Y ⋙ T)] : PreservesColimitsOfShape K T := by
  constructor
  intro D
  have h1 := isColimitOfPreserves (sheafifyQ Y) (colimit.isColimit (D ⋙ presheafQ Y))
  have h2 := isColimitOfPreserves (sheafifyQ Y ⋙ T) (colimit.isColimit (D ⋙ presheafQ Y))
  have : PreservesColimit ((D ⋙ presheafQ Y) ⋙ sheafifyQ Y) T :=
    preservesColimit_of_preserves_colimit_cocone h1 h2
  exact preservesColimit_of_iso_diagram T
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft D (sheafifyIso Y) ≪≫ D.rightUnitor)

/-- Tensoring with a sheaf `F` is tensoring with the sheafification of its underlying
presheaf. -/
def tensorLeftSheafifyIso (F : ShQ Y) :
    tensorLeft F ≅ tensorLeft ((sheafifyQ Y).obj ((presheafQ Y).obj F)) :=
  (curriedTensor (ShQ Y)).mapIso ((sheafifyIso Y).app F).symm

/-- After sheafification, tensoring with a sheaf is sheafified tensoring of presheaves. -/
def sheafifyTensorLeftIso (F : ShQ Y) :
    sheafifyQ Y ⋙ tensorLeft F ≅ tensorLeft ((presheafQ Y).obj F) ⋙ sheafifyQ Y :=
  Functor.isoWhiskerLeft _ (tensorLeftSheafifyIso Y F) ≪≫ commLeft Y _

/-- Tensoring with a sheaf is: take underlying presheaves, tensor, sheafify. -/
def tensorLeftIso (F : ShQ Y) :
    tensorLeft F ≅ presheafQ Y ⋙ tensorLeft ((presheafQ Y).obj F) ⋙ sheafifyQ Y :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (sheafifyIso Y).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (sheafifyTensorLeftIso Y F)

/-- **Tensoring with a sheaf on the left is left exact.** -/
instance tensorLeft_preservesFiniteLimits (F : ShQ Y) : PreservesFiniteLimits (tensorLeft F) :=
  preservesFiniteLimits_of_natIso (tensorLeftIso Y F).symm

/-- **Tensoring with a sheaf on the left preserves small colimits.** -/
instance tensorLeft_preservesColimits (F : ShQ Y) : PreservesColimitsOfSize.{0, 0} (tensorLeft F) :=
  ⟨fun {K} _ => by
    have : PreservesColimitsOfShape K (sheafifyQ Y ⋙ tensorLeft F) :=
      preservesColimitsOfShape_of_natIso (sheafifyTensorLeftIso Y F).symm
    exact preservesColimitsOfShape_of_sheafify Y _ K⟩

/-- **Tensoring with a sheaf on the left is right exact.** -/
instance tensorLeft_preservesFiniteColimits (F : ShQ Y) :
    PreservesFiniteColimits (tensorLeft F) := inferInstance

/-- **Tensoring with a sheaf on the left is additive.** -/
instance tensorLeft_additive (F : ShQ Y) : (tensorLeft F).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The braiding on sheaves of `ℚ`-vector spaces on `Y`. -/
abbrev sheafBraided : BraidedCategory (ShQ Y) :=
  Sheaf.braidedCategory (J Y) (ModuleCat.{0} ℚ)

attribute [local instance] sheafBraided

/-- Tensoring on the left and on the right agree up to the braiding. -/
def tensorLeftIsoTensorRight (F : ShQ Y) : tensorLeft F ≅ tensorRight F :=
  BraidedCategory.tensorLeftIsoTensorRight F

/-- **Tensoring with a sheaf on the right is left exact.** -/
instance tensorRight_preservesFiniteLimits (F : ShQ Y) : PreservesFiniteLimits (tensorRight F) :=
  preservesFiniteLimits_of_natIso (tensorLeftIsoTensorRight Y F)

/-- **Tensoring with a sheaf on the right preserves small colimits.** -/
instance tensorRight_preservesColimits (F : ShQ Y) :
    PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
  preservesColimits_of_natIso (tensorLeftIsoTensorRight Y F)

/-- **Tensoring with a sheaf on the right is right exact.** -/
instance tensorRight_preservesFiniteColimits (F : ShQ Y) :
    PreservesFiniteColimits (tensorRight F) := inferInstance

/-- **Tensoring with a sheaf on the right is additive.** -/
instance tensorRight_additive (F : ShQ Y) : (tensorRight F).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The tensor product of sheaves of `ℚ`-vector spaces on `Y` is exact in each variable.**
For every sheaf `F`, tensoring with `F` on either side preserves finite limits and finite
colimits and is additive. -/
theorem tensor_exact (F : ShQ Y) :
    PreservesFiniteLimits (tensorLeft F) ∧ PreservesFiniteColimits (tensorLeft F) ∧
      (tensorLeft F).Additive ∧ PreservesFiniteLimits (tensorRight F) ∧
      PreservesFiniteColimits (tensorRight F) ∧ (tensorRight F).Additive :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- **The unit of the tensor product is the constant sheaf `ℚ_Y`.** -/
def unitIsoQX : 𝟙_ (ShQ Y) ≅ QX Y := Iso.refl _

end HodgeLadder.Cup
