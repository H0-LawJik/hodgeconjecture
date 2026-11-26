module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The constant sheaf as the sheaf of locally constant functions

Let `X` be a topological space and `A` an abelian group. The constant sheaf with value `A`,
`(constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj (.of A)`, is defined by
sheafifying the constant presheaf. This file builds the sheaf `U ↦ LocallyConstant U A` of locally
constant functions and identifies the two: the map from the constant presheaf, sending `a` to the
constant function `a`, is locally injective and locally surjective, so its sheafification is an
isomorphism. No topology on `A` is used.

The ladder's `HodgeLadder.lcSheaf` (continuous `ℤ`-valued functions) is the case `A = ℤ`, compared
with this one in `HodgeLadder.Line.LocallyConstant`.

## Main definitions

* `HodgeLadder.locallyConstantPresheaf X A`, `HodgeLadder.locallyConstantSheaf X A`
* `HodgeLadder.constToLocallyConstantPresheaf X A`: constants as locally constant functions
* `HodgeLadder.constantSheafIsoLocallyConstantSheaf X A`

## Main results

* `HodgeLadder.toSheafify_constantSheafToLocallyConstantSheaf_hom`
* `HodgeLadder.constantSheafIsoLocallyConstantSheaf_hom_app_toSheafify`: the isomorphism sends
  the image of `a` in the constant sheaf to the constant function `a`
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace HodgeLadder

variable (X : TopCat.{u}) (A : Type u) [AddCommGroup A]

/-- Local constancy is a local predicate on functions `U → A`. -/
def isLocallyConstantLocal : TopCat.LocalPredicate (fun _ : X ↦ A) where
  pred f := IsLocallyConstant f
  res i _ h := h.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality f w := by
    let : TopologicalSpace A := ⊥
    have : DiscreteTopology A := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    refine (TopCat.continuousLocal X A).locality f fun x ↦ ?_
    obtain ⟨V, m, i, h⟩ := w x
    exact ⟨V, m, i, (IsLocallyConstant.iff_continuous _).1 h⟩

/-- The presheaf of locally constant functions with values in `A`: `U ↦ LocallyConstant U A`,
with restriction of functions. -/
def locallyConstantPresheaf : X.Presheaf AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (LocallyConstant U.unop A)
  map i := AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom
    ⟨_, (Opens.isOpenEmbedding_of_le i.unop.le).continuous⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction in `locallyConstantPresheaf X A` is restriction of functions. -/
@[simp]
lemma locallyConstantPresheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (f : LocallyConstant U.unop A) (x : V.unop) :
    (show LocallyConstant V.unop A from (locallyConstantPresheaf X A).map i f) x =
      f ⟨x.1, i.unop.le x.2⟩ :=
  rfl

/-- The underlying presheaf of types of `locallyConstantPresheaf X A` is the presheaf of
functions satisfying `isLocallyConstantLocal`. -/
def locallyConstantPresheafForgetIso :
    locallyConstantPresheaf X A ⋙ forget AddCommGrpCat ≅
      TopCat.subpresheafToTypes (isLocallyConstantLocal X A).toPrelocalPredicate :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun f := ⟨f.1, f.2⟩
      invFun f := ⟨f.1, f.2⟩
      left_inv _ := rfl
      right_inv _ := rfl })
    (fun _ ↦ rfl)

/-- The sheaf of locally constant functions with values in `A`. -/
def locallyConstantSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  obj := locallyConstantPresheaf X A
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat),
      CategoryTheory.Presheaf.isSheaf_of_iso_iff (locallyConstantPresheafForgetIso X A)]
    exact (TopCat.subsheafToTypes (isLocallyConstantLocal X A)).property

/-- Constants as locally constant functions: the map from the constant presheaf with value `A`
to `locallyConstantPresheaf X A`. -/
def constToLocallyConstantPresheaf :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A) ⟶ locallyConstantPresheaf X A where
  app _ := AddCommGrpCat.ofHom LocallyConstant.constAddMonoidHom
  naturality _ _ _ := rfl

/-- `constToLocallyConstantPresheaf` sends `a` to the constant function `a`. -/
@[simp]
lemma constToLocallyConstantPresheaf_app_apply (U : (Opens X)ᵒᵖ) (a : A) :
    (constToLocallyConstantPresheaf X A).app U a = LocallyConstant.const U.unop a :=
  rfl

/-- Every locally constant function is locally a constant: `constToLocallyConstantPresheaf` is
locally surjective. -/
instance isLocallySurjective_constToLocallyConstantPresheaf :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (constToLocallyConstantPresheaf X A) := by
  rw [← TopCat.Presheaf.IsLocallySurjective, TopCat.Presheaf.isLocallySurjective_iff]
  intro U t₀ x hx
  let t : LocallyConstant U A := t₀
  let V : Opens X := ⟨Subtype.val '' (t ⁻¹' {t ⟨x, hx⟩}),
    U.isOpen.isOpenMap_subtype_val _ (t.isLocallyConstant _)⟩
  have hVU : V ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  refine ⟨V, hVU, ⟨t ⟨x, hx⟩, ?_⟩, ⟨⟨x, hx⟩, rfl, rfl⟩⟩
  apply LocallyConstant.ext
  intro y
  obtain ⟨y', hy', hyy'⟩ := y.2
  change t ⟨x, hx⟩ = t ⟨y.1, hVU y.2⟩
  rw [show (⟨y.1, hVU y.2⟩ : U) = y' from Subtype.ext hyy'.symm]
  exact hy'.symm

/-- Two constants that agree as functions on an open agree near each of its points:
`constToLocallyConstantPresheaf` is locally injective. -/
instance isLocallyInjective_constToLocallyConstantPresheaf :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (constToLocallyConstantPresheaf X A) where
  equalizerSieve_mem {_} a a' h := by
    intro x hx
    have haa' : a = a' := LocallyConstant.congr_fun h ⟨x, hx⟩
    exact ⟨_, 𝟙 _, by simp [CategoryTheory.Presheaf.equalizerSieve, haa'], hx⟩

/-- The map from the constant sheaf with value `A` to the sheaf of locally constant functions,
induced by `constToLocallyConstantPresheaf` through sheafification. -/
def constantSheafToLocallyConstantSheaf :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of A) ⟶
      locallyConstantSheaf X A :=
  ⟨sheafifyLift (Opens.grothendieckTopology X) (constToLocallyConstantPresheaf X A)
    (locallyConstantSheaf X A).property⟩

/-- `constantSheafToLocallyConstantSheaf` restricts along the sheafification map to
`constToLocallyConstantPresheaf`. -/
@[reassoc (attr := simp)]
lemma toSheafify_constantSheafToLocallyConstantSheaf_hom :
    toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A)) ≫
      (constantSheafToLocallyConstantSheaf X A).hom = constToLocallyConstantPresheaf X A :=
  toSheafify_sheafifyLift ..

/-- The comparison from the constant sheaf is an isomorphism: it is locally injective and locally
surjective. -/
instance isIso_constantSheafToLocallyConstantSheaf :
    IsIso (constantSheafToLocallyConstantSheaf X A) := by
  rw [← CategoryTheory.Sheaf.isLocallyBijective_iff_isIso (J := Opens.grothendieckTopology X)
    (A := AddCommGrpCat.{u})]
  have fac := toSheafify_constantSheafToLocallyConstantSheaf_hom X A
  have h₁ : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A)) ≫
          (constantSheafToLocallyConstantSheaf X A).hom) := by
    rw [fac]
    exact isLocallySurjective_constToLocallyConstantPresheaf X A
  have h₂ : CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A)) ≫
          (constantSheafToLocallyConstantSheaf X A).hom) := by
    rw [fac]
    exact isLocallyInjective_constToLocallyConstantPresheaf X A
  exact ⟨CategoryTheory.Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
      (Opens.grothendieckTopology X) (toSheafify (Opens.grothendieckTopology X) _) _,
    CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective
      (Opens.grothendieckTopology X) (toSheafify (Opens.grothendieckTopology X) _) _⟩

/-- **The constant sheaf with value `A` is the sheaf of locally constant functions** with values
in `A`. -/
def constantSheafIsoLocallyConstantSheaf :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of A) ≅
      locallyConstantSheaf X A :=
  asIso (constantSheafToLocallyConstantSheaf X A)

/-- The forward map of `constantSheafIsoLocallyConstantSheaf`. -/
@[simp]
lemma constantSheafIsoLocallyConstantSheaf_hom :
    (constantSheafIsoLocallyConstantSheaf X A).hom = constantSheafToLocallyConstantSheaf X A :=
  rfl

/-- **Evaluation of the comparison**: on an open `U`, the isomorphism sends the image of `a` in
the constant sheaf to the constant function `a` on `U`. -/
@[simp]
lemma constantSheafIsoLocallyConstantSheaf_hom_app_toSheafify (U : (Opens X)ᵒᵖ) (a : A) :
    (constantSheafIsoLocallyConstantSheaf X A).hom.hom.app U
        ((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A))).app U a) =
      LocallyConstant.const U.unop a := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_constantSheafToLocallyConstantSheaf_hom X A) U) a

end HodgeLadder
