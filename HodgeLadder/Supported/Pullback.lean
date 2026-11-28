module

public import HodgeLadder.Cup.PullbackVariety
public import LefschetzPort.Oka.Topology.Sheaves.Cohomology.Pullback
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport
public import HodgeLadder.Cup.OneIsKappa
public import HodgeLadder.General.FreeAbelianTerminal

/-!
# Pullback of supported classes

Rungs `supported-class-pullback` (sub-rung of `fibre-class-pullback`) and
`pullback-port-agreement`. Upstream's supported
cohomology `H_[Z]^n(X; ℚ)` is `Extⁿ(ℤ[X, X ∖ Z], ℚ_X)` in abelian sheaves on `X(ℂ)`, and
`forgetSupport` precomposes with `ℤ_X ≅ ℤ[⊤] ⟶ ℤ[X, X ∖ Z]`. For a continuous `f : Y ⟶ X` and
closed `Z' ⊇ f⁻¹ Z`, the supported pullback applies the exact inverse image `f⁻¹` (the port's
`TopCat.Sheaf.pullbackAb`), precomposes with a map of pair sheaves
`ℤ[Y, Y ∖ Z'] ⟶ f⁻¹ ℤ[X, X ∖ Z]` and postcomposes with `f⁻¹ ℚ_X ≅ ℚ_Y`.

The pair map comes from `ℤ[f⁻¹ U] ⟶ f⁻¹ ℤ[U]`, the map classifying the image of the generator of
`ℤ[U]` under the unit of `f⁻¹ ⊣ f_*`; it is natural in `U`, so it descends to cokernels.

Two identities, both exact with no sign:

* `supportH_forget_supportPullback`: forgetting the support commutes with pullback, against the
  port's `H.pullback` followed by `f⁻¹ A_X ≅ A_Y` (any coefficients `A`).
* `pullbackH_eq_pullbackConst`: rung `cup-pullback`'s rational pullback `pullbackH` (conjugation
  by `f⁻¹` on `Ext(ℚ_X, ℚ_X)` in sheaves of `ℚ`-vector spaces) equals the port's abelian
  pullback. The comparison `f⁻¹ (forget M) ⟶ forget (f⁻¹ M)` is the mate of the identity
  `f_* ∘ forget = forget ∘ f_*`; with `κ : ℤ_X → ℚ_X` (rung `one-is-kappa`) the unit
  identifications drop out.

Together: `forgetSupport_supportedPullback`,
`forgetSupport (g^* α) = pullbackCoh g (forgetSupport α)` for `g : X' ⟶ X` over `Spec ℂ`.
Spelling for `fibre-class-pullback`: `supportedPullback g Z Z' hZ` with `hZ : g⁻¹ Z ⊆ Z'` as sets of complex points, or `supportedPullbackPreimage g Z` with target
support `preimageSupport g Z = Z.preimage _`.

## Main definitions

* `HodgeLadder.Supported.free`, `HodgeLadder.Supported.freePullback`,
  `HodgeLadder.Supported.pairPullback`, `HodgeLadder.Supported.supportPairMap`
* `HodgeLadder.Supported.supportPullback`, `HodgeLadder.Supported.pullbackConst`
* `HodgeLadder.Supported.forgetPullbackMate`
* `HodgeLadder.Supported.preimageSupport`, `HodgeLadder.Supported.supportedPullback`,
  `HodgeLadder.Supported.supportedPullbackPreimage`

## Main results

* `HodgeLadder.Supported.supportH_forget_supportPullback`, `HodgeLadder.Supported.terminal_square`
* `HodgeLadder.Supported.pullbackH_eq_pullbackConst`,
  `HodgeLadder.Supported.forgetPullbackMate_square`, `HodgeLadder.Supported.unit_forgetQX`,
  `HodgeLadder.Supported.conjExt_conjExt`, `HodgeLadder.Supported.conjExt_eq_of_natTrans`
* `HodgeLadder.Supported.forgetSupport_supportedPullback`
* `HodgeLadder.Supported.relH_forget_surjective_of_eq_bot`,
  `HodgeLadder.Supported.forgetSupport_surjective_of_eq_top`

Degree-zero non-vacuity tests: `HodgeLadder.Tests.SupportedPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace HodgeLadder.Supported

open HodgeLadder.Cup

section General

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

/-- The free abelian sheaf `ℤ[U]` on an open `U`. -/
abbrev free {T : TopCat.{0}} (U : Opens T) : TopCat.AbSheaf T :=
  (CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)).obj U

/-- The map `ℤ[f⁻¹ U] ⟶ f⁻¹ ℤ[U]` classifying the image of the generator of `ℤ[U]` under the unit
of `f⁻¹ ⊣ f_*`. -/
def freePullback (U : Opens X) :
    free ((Opens.map f).obj U) ⟶ (TopCat.Sheaf.pullbackAb f).obj (free U) :=
  (CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv _ _).symm
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit.app (free U)).hom.app
      (op U) (CategoryTheory.Sheaf.freeAbelianSheafGenerator U))

/-- The image of the generator of `ℤ[V]` in `ℤ[U]` is the restriction of the generator. -/
lemma free_map_generator {T : TopCat.{0}} {V U : Opens T} (h : V ⟶ U) :
    ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)).map h).hom.app (op V)
      (CategoryTheory.Sheaf.freeAbelianSheafGenerator V) =
      (free U).obj.map h.op (CategoryTheory.Sheaf.freeAbelianSheafGenerator U) := by
  have := CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv_map_comp h (free U) (𝟙 _)
  rw [Category.comp_id] at this
  exact this

/-- `freePullback` is natural in the open. -/
lemma freePullback_naturality {V U : Opens X} (h : V ⟶ U) :
    (CategoryTheory.Sheaf.freeAbelianSheaf _).map ((Opens.map f).map h) ≫ freePullback f U =
      freePullback f V ≫
        (TopCat.Sheaf.pullbackAb f).map ((CategoryTheory.Sheaf.freeAbelianSheaf _).map h) := by
  apply (CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv _ _).injective
  rw [CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv_map_comp,
    CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv_comp, freePullback, freePullback]
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit
  have h1 : (η.app (free U)).hom.app (op V) ((free U).obj.map h.op
      (CategoryTheory.Sheaf.freeAbelianSheafGenerator U)) =
      ((TopCat.Sheaf.pullbackAb f).obj (free U)).obj.map ((Opens.map f).map h).op
        ((η.app (free U)).hom.app (op U) (CategoryTheory.Sheaf.freeAbelianSheafGenerator U)) :=
    ConcreteCategory.congr_hom ((η.app (free U)).hom.naturality h.op) _
  have h2 : (η.app (free U)).hom.app (op V)
      (((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology X)).map h).hom.app
        (op V) (CategoryTheory.Sheaf.freeAbelianSheafGenerator V)) =
      ((TopCat.Sheaf.pullbackAb f).map
        ((CategoryTheory.Sheaf.freeAbelianSheaf _).map h)).hom.app (op ((Opens.map f).obj V))
        ((η.app (free V)).hom.app (op V) (CategoryTheory.Sheaf.freeAbelianSheafGenerator V)) :=
    congrArg (fun φ => φ.hom.app (op V) (CategoryTheory.Sheaf.freeAbelianSheafGenerator V))
      (η.naturality ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology X)).map h))
  rw [free_map_generator] at h2
  exact h1.symm.trans h2

/-- The map `ℤ[f⁻¹ V, f⁻¹ W] ⟶ f⁻¹ ℤ[V, W]` of pair sheaves induced by `freePullback`. -/
def pairPullback {W V : Opens X} (h : W ⟶ V) :
    CategoryTheory.Sheaf.pairSheaf (J := Opens.grothendieckTopology Y) ((Opens.map f).map h) ⟶
      (TopCat.Sheaf.pullbackAb f).obj
        (CategoryTheory.Sheaf.pairSheaf (J := Opens.grothendieckTopology X) h) :=
  cokernel.desc _ (freePullback f V ≫ (TopCat.Sheaf.pullbackAb f).map (cokernel.π _)) (by
    rw [← Category.assoc, freePullback_naturality, Category.assoc, ← Functor.map_comp,
      cokernel.condition, Functor.map_zero, comp_zero])

/-- `pairPullback` on the cokernel projection. -/
lemma π_pairPullback {W V : Opens X} (h : W ⟶ V) :
    cokernel.π _ ≫ pairPullback f h =
      freePullback f V ≫ (TopCat.Sheaf.pullbackAb f).map (cokernel.π _) :=
  cokernel.π_desc _ _ _

variable (Z : Closeds X) (Z' : Closeds Y) (hZ : Z'.compl ≤ (Opens.map f).obj Z.compl)

/-- The map of pair sheaves `ℤ[Y, Y ∖ Z'] ⟶ f⁻¹ ℤ[X, X ∖ Z]` for `f⁻¹ (X ∖ Z) ⊇ Y ∖ Z'`. -/
def supportPairMap :
    CategoryTheory.Sheaf.pairSheaf (J := Opens.grothendieckTopology Y)
        (homOfLE (le_top : Z'.compl ≤ ⊤)) ⟶
      (TopCat.Sheaf.pullbackAb f).obj
        (CategoryTheory.Sheaf.pairSheaf (J := Opens.grothendieckTopology X)
          (homOfLE (le_top : Z.compl ≤ ⊤))) :=
  CategoryTheory.Sheaf.pairSheafMap ((Opens.map f).map (homOfLE (le_top : Z.compl ≤ ⊤)))
    (homOfLE (le_top : Z'.compl ≤ ⊤)) (homOfLE hZ) (homOfLE (fun _ _ => trivial))
    (Subsingleton.elim _ _) ≫ pairPullback f _

/-- **Pullback of supported classes** `H^n_Z(X; A) → H^n_{Z'}(Y; A)` along `f : Y ⟶ X`, for a closed
`Z'` containing `f⁻¹ Z`: apply the exact functor `f⁻¹`, then precompose with `supportPairMap` and
postcompose with `f⁻¹ A_X ≅ A_Y`. -/
def supportPullback (A : AddCommGrpCat.{0}) (n : ℕ) :
    TopCat.Sheaf.supportH X Z ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A) n
      →+ TopCat.Sheaf.supportH Y Z'
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj A) n :=
  ((Ext.mk₀ (supportPairMap f Z Z' hZ)).precomp _ (zero_add n)).comp
    (((Ext.mk₀ ((TopCat.Sheaf.pullbackConstantSheafIso f).hom.app A)).postcomp _ (add_zero n)).comp
      ((TopCat.Sheaf.pullbackAb f).mapExtAddHom _ _ n))

/-- Pullback of absolute classes with constant coefficients, `Hⁿ(X; A) → Hⁿ(Y; A)`: the port's
`H.pullback` followed by `f⁻¹ A_X ≅ A_Y`. -/
def pullbackConst (A : AddCommGrpCat.{0}) (n : ℕ) :
    TopCat.Sheaf.H ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A) n →+
      TopCat.Sheaf.H ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj A) n :=
  (TopCat.Sheaf.H.map ((TopCat.Sheaf.pullbackConstantSheafIso f).hom.app A) n).comp
    (TopCat.Sheaf.H.pullback f)

end General

section Forget

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

/-- The unit of `constantSheafAdj` at `A` sends `a` to the image of the constant section `a` under
sheafification. -/
lemma constantSheafAdj_unit_apply {T : TopCat.{0}} (A : AddCommGrpCat.{0}) (a : A) :
    (constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0} isTerminalTop).unit.app A a =
      (toSheafify (Opens.grothendieckTopology T) ((Functor.const _).obj A)).app (op ⊤) a := rfl

/-- `f⁻¹ ℤ_X ≅ ℤ_Y` sends the constant section `1` of `ℤ_Y` to the image of the constant section
`1` of `ℤ_X` under the unit of `f⁻¹ ⊣ f_*`. -/
lemma pullbackConstZIso_inv_apply :
    (TopCat.Sheaf.pullbackConstZIso f).inv.hom.app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology Y)
          ((Functor.const _).obj (AddCommGrpCat.of (ULift ℤ)))).app (op ⊤) (ULift.up 1)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit.app
          (TopCat.Sheaf.constZ X)).hom.app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const _).obj (AddCommGrpCat.of (ULift ℤ)))).app (op ⊤) (ULift.up 1)) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{0} isTerminalTop)
    (TopCat.Sheaf.pullbackConstantSheafAdj f) (AddCommGrpCat.of (ULift ℤ))
  rw [Adjunction.homEquiv_unit] at h
  have h' := ConcreteCategory.congr_hom h (ULift.up 1)
  rw [TopCat.Sheaf.pullbackConstZIso, TopCat.Sheaf.pullbackConstantSheafIso, Iso.app_inv,
    Adjunction.leftAdjointUniq_inv_app]
  exact h'

/-- `pullbackConstZIso_inv_apply` on the generators of `ℤ[⊤]`. -/
lemma pullbackConstZIso_inv_generator :
    (TopCat.Sheaf.pullbackConstZIso f).inv.hom.app (op ⊤)
        ((CategoryTheory.Sheaf.freeAbelianSheafTerminalIso (J := Opens.grothendieckTopology Y)
          isTerminalTop).hom.hom.app (op ⊤) (CategoryTheory.Sheaf.freeAbelianSheafGenerator ⊤)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit.app
          (TopCat.Sheaf.constZ X)).hom.app (op ⊤)
        ((CategoryTheory.Sheaf.freeAbelianSheafTerminalIso (J := Opens.grothendieckTopology X)
          isTerminalTop).hom.hom.app (op ⊤) (CategoryTheory.Sheaf.freeAbelianSheafGenerator ⊤)) :=
  (congrArg (fun x => (TopCat.Sheaf.pullbackConstZIso f).inv.hom.app (op ⊤) x)
    (HodgeLadder.freeAbelianSheafTerminalIso_hom_generator isTerminalTop)).trans
    ((pullbackConstZIso_inv_apply f).trans
      (congrArg (fun x => ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit.app
          (TopCat.Sheaf.constZ X)).hom.app (op ⊤) x)
        (HodgeLadder.freeAbelianSheafTerminalIso_hom_generator isTerminalTop).symm))

/-- The terminal square: through `ℤ[⊤] ≅ ℤ` on both sides, `freePullback f ⊤` is
`f⁻¹ ℤ_X ≅ ℤ_Y`. -/
lemma terminal_square :
    (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso (J := Opens.grothendieckTopology Y)
        isTerminalTop).inv ≫
      (CategoryTheory.Sheaf.freeAbelianSheaf _).map
        (homOfLE (fun _ _ => trivial) : (⊤ : Opens Y) ⟶ (Opens.map f).obj ⊤) ≫ freePullback f ⊤ =
    (TopCat.Sheaf.pullbackConstZIso f).inv ≫ (TopCat.Sheaf.pullbackAb f).map
      (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso (J := Opens.grothendieckTopology X)
        isTerminalTop).inv := by
  rw [← cancel_epi (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
    (J := Opens.grothendieckTopology Y) isTerminalTop).hom, Iso.hom_inv_id_assoc]
  apply (CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv _ _).injective
  rw [CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv_map_comp, freePullback]
  erw [AddEquiv.apply_symm_apply]
  rw [CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv_apply]
  have hb : (homOfLE (fun _ _ => trivial) : (⊤ : Opens Y) ⟶ (Opens.map f).obj ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [hb]
  erw [op_id, CategoryTheory.Functor.map_id]
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit
  let tX := CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
    (J := Opens.grothendieckTopology X) isTerminalTop
  have hgX : tX.inv.hom.app (op ⊤) (tX.hom.hom.app (op ⊤)
      (CategoryTheory.Sheaf.freeAbelianSheafGenerator ⊤)) =
      CategoryTheory.Sheaf.freeAbelianSheafGenerator ⊤ :=
    ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op ⊤)) tX.hom_inv_id) _
  have hnat : (η.app (free ⊤)).hom.app (op ⊤) (tX.inv.hom.app (op ⊤) (tX.hom.hom.app (op ⊤)
      (CategoryTheory.Sheaf.freeAbelianSheafGenerator ⊤))) =
      ((TopCat.Sheaf.pullbackAb f).map tX.inv).hom.app (op ⊤)
        ((η.app (TopCat.Sheaf.constZ X)).hom.app (op ⊤) (tX.hom.hom.app (op ⊤)
          (CategoryTheory.Sheaf.freeAbelianSheafGenerator ⊤))) :=
    congrArg (fun φ => φ.hom.app (op ⊤) (tX.hom.hom.app (op ⊤)
      (CategoryTheory.Sheaf.freeAbelianSheafGenerator ⊤))) (η.naturality tX.inv)
  rw [hgX] at hnat
  refine (ConcreteCategory.id_apply _).trans (hnat.trans ?_)
  exact congrArg (fun x => ((TopCat.Sheaf.pullbackAb f).map tX.inv).hom.app (op ⊤) x)
    (pullbackConstZIso_inv_generator f).symm

variable (Z : Closeds X) (Z' : Closeds Y) (hZ : Z'.compl ≤ (Opens.map f).obj Z.compl)

/-- **Forgetting the support commutes with pullback**, on any spaces and coefficients. -/
theorem supportH_forget_supportPullback (A : AddCommGrpCat.{0}) (n : ℕ)
    (α : TopCat.Sheaf.supportH X Z
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A) n) :
    TopCat.Sheaf.supportH.forget Z' _ n (supportPullback f Z Z' hZ A n α) =
      pullbackConst f A n (TopCat.Sheaf.supportH.forget Z _ n α) := by
  change (Ext.mk₀ (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso isTerminalTop).inv).comp
      ((Ext.mk₀ (cokernel.π _)).comp ((Ext.mk₀ (supportPairMap f Z Z' hZ)).comp
        ((α.mapExactFunctor (TopCat.Sheaf.pullbackAb f)).comp
          (Ext.mk₀ ((TopCat.Sheaf.pullbackConstantSheafIso f).hom.app A)) (add_zero n))
        (zero_add n)) (zero_add n)) (zero_add n) =
    ((Ext.mk₀ (TopCat.Sheaf.pullbackConstZIso f).inv).comp
      (((Ext.mk₀ (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso isTerminalTop).inv).comp
        ((Ext.mk₀ (cokernel.π _)).comp α (zero_add n)) (zero_add n)).mapExactFunctor
          (TopCat.Sheaf.pullbackAb f)) (zero_add n)).comp
      (Ext.mk₀ ((TopCat.Sheaf.pullbackConstantSheafIso f).hom.app A)) (add_zero n)
  rw [Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero]
  congr 2
  have hq : cokernel.π _ ≫ supportPairMap f Z Z' hZ =
      (CategoryTheory.Sheaf.freeAbelianSheaf _).map
        (homOfLE (fun _ _ => trivial) : (⊤ : Opens Y) ⟶ (Opens.map f).obj ⊤) ≫
        freePullback f ⊤ ≫ (TopCat.Sheaf.pullbackAb f).map (cokernel.π _) := by
    rw [supportPairMap, ← Category.assoc, CategoryTheory.Sheaf.pairSheafMap, cokernel.π_desc,
      Category.assoc, π_pairPullback]
  rw [Category.assoc, hq, ← Category.assoc, ← Category.assoc, Category.assoc _ _ (freePullback f ⊤),
    terminal_square]

end Forget

section Conj

variable {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ] [Abelian 𝒞] [Abelian 𝒟]
  [Abelian ℰ] [HasExt.{0} 𝒞] [HasExt.{0} 𝒟] [HasExt.{0} ℰ]

/-- Conjugating twice is conjugating by the composite functor. -/
theorem conjExt_conjExt (F : 𝒞 ⥤ 𝒟) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : 𝒟 ⥤ ℰ) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] {A : 𝒞} {B : 𝒟} {C : ℰ} (a : F.obj A ≅ B) (b : G.obj B ≅ C)
    {n : ℕ} (x : Ext.{0} A A n) :
    conjExt G b (conjExt F a x) = conjExt (F ⋙ G) (G.mapIso a ≪≫ b) x := by
  unfold conjExt
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_mk₀, ← Ext.comp_mapExactFunctor, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rfl

/-- Conjugations by two exact functors related by a natural transformation agree, when the
transformation matches the two identifications. -/
theorem conjExt_eq_of_natTrans {F G : 𝒞 ⥤ 𝒟} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (τ : G ⟶ F) {A : 𝒞} {B : 𝒟} (a : F.obj A ≅ B) (b : G.obj A ≅ B)
    (h : τ.app A ≫ a.hom = b.hom) {n : ℕ} (x : Ext.{0} A A n) :
    conjExt F a x = conjExt G b x := by
  have hb : b.inv ≫ τ.app A = a.inv := by
    rw [← cancel_mono a.hom, Category.assoc, h, Iso.inv_hom_id, Iso.inv_hom_id]
  unfold conjExt
  rw [← h, ← Ext.mk₀_comp_mk₀]
  conv_rhs => rw [← Ext.comp_assoc_of_third_deg_zero (x.mapExactFunctor G) (Ext.mk₀ (τ.app A)),
    Ext.mapExactFunctor_comp_mk₀_natTransApp, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀_assoc, hb]

end Conj

section Agreement

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

/-- The mate of the identity `f_* ∘ forget = forget ∘ f_*`: the comparison
`f⁻¹ (forget M) ⟶ forget (f⁻¹ M)` between the inverse images of abelian and rational sheaves. -/
def forgetPullbackMate : forgetSheaf X ⋙ TopCat.Sheaf.pullbackAb f ⟶ pullbackQ f ⋙ forgetSheaf Y :=
  (mateEquiv (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)).symm (𝟙 _)

/-- The adjunct of `forgetPullbackMate` is `forget` applied to the unit of `f⁻¹ ⊣ f_*`. -/
lemma unit_forgetPullbackMate (M : Sheaf (J X) (ModuleCat.{0} ℚ)) :
    (forgetSheaf X).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app M) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
          ((forgetSheaf X).obj M) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map ((forgetPullbackMate f).app M) := by
  have := unit_mateEquiv_symm (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)
    (G := forgetSheaf X) (H := forgetSheaf Y) (𝟙 _) M
  rw [NatTrans.id_app] at this
  exact (Category.comp_id _).symm.trans this

omit f in
/-- The unit of the constant-sheaf adjunction for abelian groups at `ℚ` is the unit for rational
vector spaces followed by `forgetQX` on global sections (the step `F2` inside
`HodgeLadder.Cup.adj_tensorQSheafInt_comp_forgetQX`, stated on its own). -/
lemma unit_forgetQX (T : TopCat.{0}) :
    U.map ((constantSheafAdj (J T) (ModuleCat.{0} ℚ) isTerminalTop).unit.app (ModuleCat.of ℚ ℚ)) ≫
      ((sheafSections (J T) AddCommGrpCat.{0}).obj (op ⊤)).map (forgetQX T).hom =
      (constantSheafAdj (J T) AddCommGrpCat.{0} isTerminalTop).unit.app (AddCommGrpCat.of ℚ) := by
  let adjCQ := constantSheafAdj (J T) (ModuleCat.{0} ℚ) isTerminalTop
  let adjC := constantSheafAdj (J T) AddCommGrpCat.{0} isTerminalTop
  let P := (Functor.const (TopologicalSpace.Opens T)ᵒᵖ).obj (ModuleCat.of ℚ ℚ)
  have h1 := congrArg (fun f => f.app (Opposite.op ⊤)) (sheafComposeIso_inv_fac (J T) U P)
  have h2 := congrArg (fun f => f.app (Opposite.op ⊤))
    (toSheafify_naturality (J T)
      (Functor.constComp (TopologicalSpace.Opens T)ᵒᵖ (ModuleCat.of ℚ ℚ) U).hom)
  ext q
  have e1 := ConcreteCategory.congr_hom h1 q
  have e2 := ConcreteCategory.congr_hom h2 q
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, ConcreteCategory.comp_apply] at e1 e2
  simp only [constantSheafAdj, Adjunction.comp_unit_app]
  erw [ConcreteCategory.comp_apply]
  change ConcreteCategory.hom (((constantCommuteCompose (J T) U).hom.app
    (ModuleCat.of ℚ ℚ)).hom.app (Opposite.op ⊤)) _ = _
  rw [constantCommuteCompose_hom_app_hom]
  erw [NatTrans.comp_app, ConcreteCategory.comp_apply]
  erw [e1]
  erw [← e2]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison of inverse images matches the two identifications of `f⁻¹ ℚ_X` with
`ℚ_Y`.** -/
lemma forgetPullbackMate_square :
    (forgetPullbackMate f).app (QX X) ≫ (forgetSheaf Y).map (pullbackQX f).hom ≫
        (forgetQX Y).hom =
      (TopCat.Sheaf.pullbackAb f).map (forgetQX X).hom ≫
        (TopCat.Sheaf.pullbackConstantSheafIso f).hom.app (AddCommGrpCat.of ℚ) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit, ← unit_forgetPullbackMate, ← cancel_epi (forgetQX X).inv,
    Iso.inv_hom_id_assoc]
  apply ((constantSheafAdj (J X) AddCommGrpCat.{0} isTerminalTop).homEquiv _ _).injective
  have hc := Adjunction.homEquiv_leftAdjointUniq_hom_app (TopCat.Sheaf.pullbackConstantSheafAdj f)
    (constantSheafAdj (J Y) AddCommGrpCat.{0} isTerminalTop) (AddCommGrpCat.of ℚ)
  have hq := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((constantSheafAdj (J X) (ModuleCat.{0} ℚ) isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f))
    (constantSheafAdj (J Y) (ModuleCat.{0} ℚ) isTerminalTop) (ModuleCat.of ℚ ℚ)
  rw [TopCat.Sheaf.pullbackConstantSheafAdj, Adjunction.comp_homEquiv] at hc
  rw [Adjunction.comp_homEquiv] at hq
  erw [hc]
  erw [Equiv.trans_apply, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at hq
  have ha : (constantSheafAdj (J X) AddCommGrpCat.{0} isTerminalTop).unit.app (AddCommGrpCat.of ℚ) ≫
      ((sheafSections (J X) AddCommGrpCat.{0}).obj (op ⊤)).map (forgetQX X).inv =
      U.map ((constantSheafAdj (J X) (ModuleCat.{0} ℚ) isTerminalTop).unit.app
        (ModuleCat.of ℚ ℚ)) := by
    rw [← unit_forgetQX X, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  erw [ha]
  rw [← unit_forgetQX Y, ← hq]
  rfl

/-- `f⁻¹ ℤ_X ≅ ℤ_Y` and `f⁻¹ ℚ_X ≅ ℚ_Y` commute with `κ : ℤ → ℚ`. -/
lemma pullbackConstZIso_inv_kappa :
    (TopCat.Sheaf.pullbackConstZIso f).inv ≫ (TopCat.Sheaf.pullbackAb f).map (kappaSheaf X) =
      kappaSheaf Y ≫ (TopCat.Sheaf.pullbackConstantSheafIso f).inv.app (AddCommGrpCat.of ℚ) :=
  ((TopCat.Sheaf.pullbackConstantSheafIso f).inv.naturality kappaAb).symm

/-- **The rational pullback `pullbackH` is the port's pullback of abelian sheaf cohomology**,
followed by `f⁻¹ ℚ_X ≅ ℚ_Y`. -/
theorem pullbackH_eq_pullbackConst (n : ℕ) (α : HQ X n) :
    pullbackH f n α = pullbackConst f (AddCommGrpCat.of ℚ) n α := by
  obtain ⟨β, rfl⟩ : ∃ β, α = (rationalExtEquiv X n).symm β :=
    ⟨_, ((rationalExtEquiv X n).symm_apply_apply α).symm⟩
  have hα := eq_kappa_comp_forgetEnd X ((rationalExtEquiv X n).symm β)
  rw [AddEquiv.apply_symm_apply] at hα
  rw [eq_kappa_comp_forgetEnd Y (pullbackH f n _), rationalExtEquiv_pullbackH,
    AddEquiv.apply_symm_apply, hα]
  have key : forgetEnd Y (conjExt (pullbackQ f) (pullbackQX f) β) =
      conjExt (TopCat.Sheaf.pullbackAb f)
        ((TopCat.Sheaf.pullbackConstantSheafIso f).app (AddCommGrpCat.of ℚ)) (forgetEnd X β) := by
    change conjExt (forgetSheaf Y) (forgetQX Y) (conjExt (pullbackQ f) (pullbackQX f) β) =
      conjExt (TopCat.Sheaf.pullbackAb f)
        ((TopCat.Sheaf.pullbackConstantSheafIso f).app (AddCommGrpCat.of ℚ))
        (conjExt (forgetSheaf X) (forgetQX X) β)
    rw [conjExt_conjExt, conjExt_conjExt]
    refine conjExt_eq_of_natTrans (forgetPullbackMate f) _ _ ?_ β
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using forgetPullbackMate_square f
  rw [key]
  change _ = ((Ext.mk₀ (TopCat.Sheaf.pullbackConstZIso f).inv).comp
      (((Ext.mk₀ (kappaSheaf X)).comp (forgetEnd X β) (zero_add n)).mapExactFunctor
        (TopCat.Sheaf.pullbackAb f)) (zero_add n)).comp
      (Ext.mk₀ ((TopCat.Sheaf.pullbackConstantSheafIso f).hom.app (AddCommGrpCat.of ℚ)))
      (add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
    pullbackConstZIso_inv_kappa, ← Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]
  rfl

end Agreement

section Variety

open AlgebraicGeometry ComplexPoint

variable {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X)

/-- The preimage `g⁻¹ Z ⊆ X'(ℂ)` of a closed `Z ⊆ X(ℂ)` under the map of complex points. -/
abbrev preimageSupport (Z : Closeds (ComplexPoint X)) : Closeds (ComplexPoint X') :=
  Z.preimage (Point.continuousMap g).continuous

/-- A closed `Z' ⊇ g⁻¹ Z` has `X'(ℂ) ∖ Z' ⊆ g⁻¹ (X(ℂ) ∖ Z)`. -/
lemma compl_le_of_preimage_subset (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') :
    Z'.compl ≤ (Opens.map (pointMap g)).obj Z.compl :=
  fun _ hy hgy => hy (hZ hgy)

/-- Upstream's `forgetSupport` is `supportH.forget` with constant coefficients. -/
lemma forgetSupport_eq (Z : Closeds (ComplexPoint X)) (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    forgetSupport ℚ X Z n α =
      TopCat.Sheaf.supportH.forget (X := TopCat.of (ComplexPoint X)) Z _ n α := rfl

/-- **Pullback of supported classes** `H_[Z]^n(X; ℚ) → H_[Z']^n(X'; ℚ)` along `g : X' ⟶ X` over
`Spec ℂ`, for a closed `Z' ⊆ X'(ℂ)` containing `g⁻¹ Z`. -/
def supportedPullback (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') (n : ℕ) :
    H_[Z]^n(X; ℚ) →+ H_[Z']^n(X'; ℚ) :=
  supportPullback (pointMap g) Z Z' (compl_le_of_preimage_subset g Z Z' hZ) (AddCommGrpCat.of ℚ) n

/-- `supportedPullback` with target support exactly `g⁻¹ Z`. -/
abbrev supportedPullbackPreimage (Z : Closeds (ComplexPoint X)) (n : ℕ) :
    H_[Z]^n(X; ℚ) →+ H_[preimageSupport g Z]^n(X'; ℚ) :=
  supportedPullback g Z (preimageSupport g Z) (fun _ h => h) n

/-- **Forgetting the support commutes with pullback**:
`forgetSupport (g^* α) = g^* (forgetSupport α)` in `H^n(X'; ℚ)`, with `pullbackCoh g` the
pullback of rung `cup-pullback`. Exact, no sign. -/
theorem forgetSupport_supportedPullback (Z : Closeds (ComplexPoint X))
    (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') (n : ℕ)
    (α : H_[Z]^n(X; ℚ)) :
    forgetSupport ℚ X' Z' n (supportedPullback g Z Z' hZ n α) =
      pullbackCoh g n (forgetSupport ℚ X Z n α) := by
  rw [forgetSupport_eq, forgetSupport_eq]
  exact (supportH_forget_supportPullback (pointMap g) Z Z'
    (compl_le_of_preimage_subset g Z Z' hZ) (AddCommGrpCat.of ℚ) n α).trans
    (pullbackH_eq_pullbackConst (pointMap g) n _).symm

omit g in
/-- With `W = ⊥`, forgetting the pair `(V, W)` is surjective, on any space. -/
theorem relH_forget_surjective_of_eq_bot (T : TopCat.{0})
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) {W V : Opens T}
    (f : W ⟶ V) (hW : W = ⊥) (n : ℕ) :
    Function.Surjective (CategoryTheory.Sheaf.relH.forget F f n) :=
  haveI : Fact (W = ⊥) := ⟨hW⟩
  (Abelian.Ext.precompAddEquiv (asIso (cokernel.π
    ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)).map f))) F n).surjective

omit g in
/-- With support the whole space, forgetting the support is surjective. -/
theorem forgetSupport_surjective_of_eq_top (Z : Closeds (ComplexPoint X)) (hZ : Z = ⊤)
    (n : ℕ) : Function.Surjective (forgetSupport ℚ X Z n) :=
  (Sheaf.H'.addEquivTerminal isTerminalTop _ n).surjective.comp
    (relH_forget_surjective_of_eq_bot (TopCat.of (ComplexPoint X)) _ _ (by rw [hZ]; ext; simp) n)

end Variety

end HodgeLadder.Supported
