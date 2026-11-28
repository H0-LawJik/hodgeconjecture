module

public import HodgeLadder.Cup.PullbackVariety

/-!
# Pullback of rational cohomology is functorial and `ℚ`-linear

Rung `pullback-functorial` (plan `docs/notes/2026-11-27-t1-plan.md`, node A1). For morphisms
`g : X ⟶ Y` and `h : Y ⟶ Z` over `Spec ℂ`, the pullback `pullbackCoh` of rung `cup-pullback`
satisfies `(g ≫ h)^* = g^* ∘ h^*` and `(𝟙 X)^* = id`, and it is bundled as a `ℚ`-linear map.
The order is the one the types force: `h^*` lands in `Hⁿ(Y; ℚ)`, then `g^*` in `Hⁿ(X; ℚ)`.
No sign enters: the laws are equalities of maps, with no scalar.

Route. `pullbackCoh g` is `pullbackH (pointMap g)`, and `pointMap (g ≫ h)` is
`pointMap g ≫ pointMap h` by `rfl`, so the work is on a continuous map `f : Y ⟶ X`, where
`pullbackH f` conjugates `Ext(ℚ_X, ℚ_X)` by the exact functor `f⁻¹` and the iso
`pullbackQX f : f⁻¹ ℚ_X ≅ ℚ_Y`.

1. `Ext` side (Mathlib `Ext.comp_mapExactFunctor`, `Ext.id_mapExactFunctor`,
   `Ext.mapExactFunctor_comp_mk₀_natTransApp`): conjugation is invariant under a natural iso of
   exact functors (`conjExt_natIso`), compatible with composition of functors
   (`conjExt_comp_functor`) and trivial for `𝟭` (`conjExt_id_functor`).
2. Sheaf side: `(f₁ ≫ f₂)⁻¹ ≅ f₂⁻¹ ⋙ f₁⁻¹` and `(𝟙 X)⁻¹ ≅ 𝟭` by uniqueness of left adjoints
   (`pushforward (f₁ ≫ f₂)` is `pushforward f₁ ⋙ pushforward f₂` and `pushforward (𝟙 X)` is `𝟭`
   by `rfl`). Every iso involved is a `leftAdjointUniq` evaluated at `ℚ`; the identities between
   them (`pullbackQX_comp`, `pullbackQX_id`) are the abstract triangle lemmas
   `leftAdjointUniq_comp_triangle` and `leftAdjointUniq_id_triangle`, proved by comparing units.

## Main definitions

* `HodgeLadder.Pullback.pullbackCohLinear`: `g^* : Hⁿ(X; ℚ) →ₗ[ℚ] Hⁿ(X'; ℚ)`.
* `HodgeLadder.Pullback.sheafPullbackComp`, `HodgeLadder.Pullback.sheafPullbackId`: the
  composition and identity isos of `TopCat.Sheaf.pullback` for any coefficient category, and their
  instances `pullbackQComp`, `pullbackQId` at `ModuleCat ℚ`.

## Main results

* `HodgeLadder.Pullback.pullbackCoh_comp`, `HodgeLadder.Pullback.pullbackCoh_id`
* `HodgeLadder.Pullback.pullbackCohLinear_apply`, `pullbackCohLinear_comp`, `pullbackCohLinear_id`
* `HodgeLadder.Pullback.pullbackH_comp`, `HodgeLadder.Pullback.pullbackH_id`: the same laws for a
  continuous map of spaces.
* `HodgeLadder.Pullback.pullbackCoh_comm`: pullback along a commutative square.
* `HodgeLadder.Pullback.pullbackCoh_injective_of_section`: a morphism with a section pulls back
  injectively.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Pullback

open HodgeLadder.Cup

section IsoConj

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{0} 𝒜]

/-- Conjugation of a self-extension by an iso: `y ↦ d⁻¹ ∘ y ∘ d` (as an `Ext` composite,
`mk₀ d.inv`, then `y`, then `mk₀ d.hom`). -/
def isoConj {B C : 𝒜} (d : B ≅ C) {n : ℕ} (y : Abelian.Ext.{0} B B n) :
    Abelian.Ext.{0} C C n :=
  (Abelian.Ext.mk₀ d.inv).comp (y.comp (Abelian.Ext.mk₀ d.hom) (add_zero n)) (zero_add n)

/-- Conjugation by a composite iso is the composite of the conjugations. -/
theorem isoConj_trans {B C D : 𝒜} (c : B ≅ C) (d : C ≅ D) {n : ℕ}
    (y : Abelian.Ext.{0} B B n) : isoConj (c ≪≫ d) y = isoConj d (isoConj c y) := by
  unfold isoConj
  simp only [Iso.trans_hom, Iso.trans_inv, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀_assoc]

/-- Conjugation by the identity iso is the identity. -/
theorem isoConj_refl {B : 𝒜} {n : ℕ} (y : Abelian.Ext.{0} B B n) :
    isoConj (Iso.refl B) y = y := by
  simp [isoConj]

end IsoConj

section Conj

variable {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ] [Abelian 𝒞] [Abelian 𝒟]
  [Abelian ℰ] [HasExt.{0} 𝒞] [HasExt.{0} 𝒟] [HasExt.{0} ℰ]

/-- `conjExt Φ c` is `isoConj c` after mapping by `Φ`. -/
theorem conjExt_eq_isoConj (Φ : 𝒞 ⥤ 𝒟) [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] {A : 𝒞} {B : 𝒟} (c : Φ.obj A ≅ B) {n : ℕ}
    (x : Abelian.Ext.{0} A A n) : conjExt Φ c x = isoConj c (x.mapExactFunctor Φ) := rfl

/-- A natural iso `e : Φ ≅ Ψ` of exact functors conjugates `Ext.mapExactFunctor`:
`x.mapExactFunctor Ψ = isoConj (e.app A) (x.mapExactFunctor Φ)`. -/
theorem mapExactFunctor_natIso (Φ Ψ : 𝒞 ⥤ 𝒟) [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] [Ψ.Additive] [PreservesFiniteLimits Ψ]
    [PreservesFiniteColimits Ψ] (e : Φ ≅ Ψ) {A : 𝒞} {n : ℕ} (x : Abelian.Ext.{0} A A n) :
    x.mapExactFunctor Ψ = isoConj (e.app A) (x.mapExactFunctor Φ) := by
  unfold isoConj
  rw [Iso.app_hom, Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp, Iso.app_inv,
    Abelian.Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id_app, Abelian.Ext.mk₀_id_comp]

/-- **Conjugation is invariant under a natural iso of functors**, with the iso transported:
`conjExt Φ c = conjExt Ψ ((e.app A)⁻¹ ≪≫ c)`. -/
theorem conjExt_natIso (Φ Ψ : 𝒞 ⥤ 𝒟) [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] [Ψ.Additive] [PreservesFiniteLimits Ψ]
    [PreservesFiniteColimits Ψ] (e : Φ ≅ Ψ) {A : 𝒞} {B : 𝒟} (c : Φ.obj A ≅ B) {n : ℕ}
    (x : Abelian.Ext.{0} A A n) :
    conjExt Φ c x = conjExt Ψ ((e.app A).symm ≪≫ c) x := by
  rw [conjExt_eq_isoConj, conjExt_eq_isoConj, isoConj_trans, mapExactFunctor_natIso Φ Ψ e,
    ← isoConj_trans (e.app A) (e.app A).symm, Iso.self_symm_id, isoConj_refl]

/-- **Conjugation along a composite functor** is the composite of the conjugations, with the
composite iso `Ψ c₁ ≪≫ c₂`. -/
theorem conjExt_comp_functor (Φ : 𝒞 ⥤ 𝒟) [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] (Ψ : 𝒟 ⥤ ℰ) [Ψ.Additive] [PreservesFiniteLimits Ψ]
    [PreservesFiniteColimits Ψ] {A : 𝒞} {B : 𝒟} {C : ℰ} (c₁ : Φ.obj A ≅ B)
    (c₂ : Ψ.obj B ≅ C) {n : ℕ} (x : Abelian.Ext.{0} A A n) :
    conjExt (Φ ⋙ Ψ) (Ψ.mapIso c₁ ≪≫ c₂) x = conjExt Ψ c₂ (conjExt Φ c₁ x) := by
  rw [conjExt_eq_isoConj, conjExt_eq_isoConj, conjExt_eq_isoConj, isoConj_trans,
    Abelian.Ext.comp_mapExactFunctor]
  congr 1
  unfold isoConj
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mapExactFunctor_mk₀]
  rfl

/-- Conjugation by the identity functor and the identity iso is the identity. -/
theorem conjExt_id_functor {A : 𝒞} {n : ℕ} (x : Abelian.Ext.{0} A A n) :
    conjExt (𝟭 𝒞) (Iso.refl A) x = x := by
  rw [conjExt_eq_isoConj]
  exact (isoConj_refl _).trans (Abelian.Ext.id_mapExactFunctor x)

/-- If `Φ ≅ Ψ₂ ⋙ Ψ₁` carries `c` to `Ψ₁ c₂ ≪≫ c₁`, conjugation by `(Φ, c)` is conjugation by
`(Ψ₂, c₂)` followed by conjugation by `(Ψ₁, c₁)`. -/
theorem conjExt_eq_of_comp_iso (Φ : 𝒞 ⥤ ℰ) [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] (Ψ₂ : 𝒞 ⥤ 𝒟) [Ψ₂.Additive] [PreservesFiniteLimits Ψ₂]
    [PreservesFiniteColimits Ψ₂] (Ψ₁ : 𝒟 ⥤ ℰ) [Ψ₁.Additive] [PreservesFiniteLimits Ψ₁]
    [PreservesFiniteColimits Ψ₁] (e : Φ ≅ Ψ₂ ⋙ Ψ₁) {A : 𝒞} {B : 𝒟} {C : ℰ} (c : Φ.obj A ≅ C)
    (c₂ : Ψ₂.obj A ≅ B) (c₁ : Ψ₁.obj B ≅ C) (h : c = e.app A ≪≫ Ψ₁.mapIso c₂ ≪≫ c₁) {n : ℕ}
    (x : Abelian.Ext.{0} A A n) :
    conjExt Φ c x = conjExt Ψ₁ c₁ (conjExt Ψ₂ c₂ x) := by
  rw [h, conjExt_natIso _ _ e, Iso.symm_self_id_assoc, conjExt_comp_functor]

/-- If `Φ ≅ 𝟭` carries `c` to the identity, conjugation by `(Φ, c)` is the identity. -/
theorem conjExt_eq_of_id_iso (Φ : 𝒞 ⥤ 𝒞) [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] (e : Φ ≅ 𝟭 𝒞) {A : 𝒞} (c : Φ.obj A ≅ A) (h : c = e.app A)
    {n : ℕ} (x : Abelian.Ext.{0} A A n) : conjExt Φ c x = x := by
  rw [h, conjExt_natIso _ _ e, Iso.symm_self_id]
  exact conjExt_id_functor x

end Conj

section Adj0

/-- **Uniqueness of the comparison of left adjoints.** A morphism `φ : F x ⟶ F' x` compatible
with the units is the component of `leftAdjointUniq`. -/
theorem leftAdjointUniq_hom_app_eq {C D : Type*} [Category C] [Category D] {F F' : C ⥤ D}
    {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) (φ : F.obj x ⟶ F'.obj x)
    (h : adj1.unit.app x ≫ G.map φ = adj2.unit.app x) :
    (adj1.leftAdjointUniq adj2).hom.app x = φ := by
  apply (adj1.homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit, h]

end Adj0

section Adj

variable {C DZ DY DX : Type*} [Category C] [Category DZ] [Category DY] [Category DX]

/-- **Comparison of left adjoints along a composite.** With `cY : FY ⊣ Q₂ ⋙ GZ`,
`cX : FX ⊣ Q₁ ⋙ Q₂ ⋙ GZ` and `p₁₂ : P₁₂ ⊣ Q₁ ⋙ Q₂`, the comparison `FZ ⋙ P₁₂ ≅ FX` factors
through `P₁₂ ≅ P₂ ⋙ P₁`, then `FZ ⋙ P₂ ≅ FY` under `P₁`, then `FY ⋙ P₁ ≅ FX`. -/
theorem leftAdjointUniq_comp_triangle {FZ : C ⥤ DZ} {FY : C ⥤ DY} {FX : C ⥤ DX} {GZ : DZ ⥤ C}
    {P₂ : DZ ⥤ DY} {Q₂ : DY ⥤ DZ} {P₁ : DY ⥤ DX} {Q₁ : DX ⥤ DY} {P₁₂ : DZ ⥤ DX}
    (p₂ : P₂ ⊣ Q₂) (p₁ : P₁ ⊣ Q₁) (p₁₂ : P₁₂ ⊣ Q₁ ⋙ Q₂)
    (cZ : FZ ⊣ GZ) (cY : FY ⊣ Q₂ ⋙ GZ) (cX : FX ⊣ Q₁ ⋙ Q₂ ⋙ GZ) (x : C) :
    ((cZ.comp p₁₂).leftAdjointUniq cX).hom.app x =
      (p₁₂.leftAdjointUniq (p₂.comp p₁)).hom.app (FZ.obj x) ≫
        P₁.map (((cZ.comp p₂).leftAdjointUniq cY).hom.app x) ≫
          ((cY.comp p₁).leftAdjointUniq cX).hom.app x := by
  apply leftAdjointUniq_hom_app_eq
  have h1 := congrArg GZ.map
    (Adjunction.unit_leftAdjointUniq_hom_app p₁₂ (p₂.comp p₁) (FZ.obj x))
  have h2 := congrArg (fun f => GZ.map (Q₂.map f))
    (p₁.unit.naturality (((cZ.comp p₂).leftAdjointUniq cY).hom.app x))
  have h3 := Adjunction.unit_leftAdjointUniq_hom_app (cZ.comp p₂) cY x
  have h4 := Adjunction.unit_leftAdjointUniq_hom_app (cY.comp p₁) cX x
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Functor.comp_obj,
    Functor.id_obj, Functor.id_map, Category.assoc] at h1 h2 h3 h4 ⊢
  rw [reassoc_of% h1, ← reassoc_of% h2, reassoc_of% h3, h4]

/-- **Comparison of left adjoints along the identity.** For `p : P ⊣ 𝟭`, the comparison
`FX ⋙ P ≅ FX` is `P ≅ 𝟭` at `FX x`. -/
theorem leftAdjointUniq_id_triangle {FX : C ⥤ DX} {GX : DX ⥤ C} {P : DX ⥤ DX}
    (cX : FX ⊣ GX) (p : P ⊣ 𝟭 DX) (x : C) :
    ((cX.comp p).leftAdjointUniq cX).hom.app x =
      (p.leftAdjointUniq Adjunction.id).hom.app (FX.obj x) := by
  apply leftAdjointUniq_hom_app_eq
  have h := Adjunction.unit_leftAdjointUniq_hom_app p Adjunction.id (FX.obj x)
  simp only [Functor.id_map, Adjunction.id_unit, NatTrans.id_app] at h
  simp [Adjunction.comp_unit_app, ← GX.map_comp, h]

end Adj

section SheafPullback

universe w v u

variable (A : Type u) [Category.{w} A] {FA : A → A → Type v} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA] [HasColimits A]
  [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
  [PreservesFilteredColimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- `(f₁ ≫ f₂)⁻¹ ≅ f₂⁻¹ ⋙ f₁⁻¹` on `A`-valued sheaves: both are left adjoint to
`f₁_* ⋙ f₂_*`, which is `(f₁ ≫ f₂)_*` by `rfl`. -/
def sheafPullbackComp {X Y Z : TopCat.{w}} (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) :
    TopCat.Sheaf.pullback A (f₁ ≫ f₂) ≅
      TopCat.Sheaf.pullback A f₂ ⋙ TopCat.Sheaf.pullback A f₁ :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction A (f₁ ≫ f₂)).leftAdjointUniq
    ((TopCat.Sheaf.pullbackPushforwardAdjunction A f₂).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction A f₁))

/-- `(𝟙 X)⁻¹ ≅ 𝟭` on `A`-valued sheaves: both are left adjoint to `(𝟙 X)_*`, which is `𝟭` by
`rfl`. -/
def sheafPullbackId (X : TopCat.{w}) : TopCat.Sheaf.pullback A (𝟙 X) ≅ 𝟭 _ :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction A (𝟙 X)).leftAdjointUniq Adjunction.id

end SheafPullback

section Sheaf

variable {X Y Z : TopCat.{0}}

/-- `(f₁ ≫ f₂)⁻¹ ≅ f₂⁻¹ ⋙ f₁⁻¹` on sheaves of `ℚ`-vector spaces: `sheafPullbackComp` at
`ModuleCat ℚ`. -/
abbrev pullbackQComp (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) :
    pullbackQ (f₁ ≫ f₂) ≅ pullbackQ f₂ ⋙ pullbackQ f₁ :=
  sheafPullbackComp (ModuleCat.{0} ℚ) f₁ f₂

/-- `(𝟙 X)⁻¹ ≅ 𝟭` on sheaves of `ℚ`-vector spaces: `sheafPullbackId` at `ModuleCat ℚ`. -/
abbrev pullbackQId (X : TopCat.{0}) : pullbackQ (𝟙 X) ≅ 𝟭 _ :=
  sheafPullbackId (ModuleCat.{0} ℚ) X

/-- `pullbackQX (f₁ ≫ f₂)` is `pullbackQComp`, then `f₁⁻¹ (pullbackQX f₂)`, then
`pullbackQX f₁`. -/
theorem pullbackQX_comp (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) :
    pullbackQX (f₁ ≫ f₂) = (pullbackQComp f₁ f₂).app (QX Z) ≪≫
      (pullbackQ f₁).mapIso (pullbackQX f₂) ≪≫ pullbackQX f₁ := by
  apply Iso.ext
  have key := leftAdjointUniq_comp_triangle
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f₂)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f₁)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) (f₁ ≫ f₂))
    (constantSheafAdj (J Z) (ModuleCat.{0} ℚ) isTerminalTop)
    (constantSheafAdj (J Y) (ModuleCat.{0} ℚ) isTerminalTop)
    (constantSheafAdj (J X) (ModuleCat.{0} ℚ) isTerminalTop) (ModuleCat.of ℚ ℚ)
  exact key

/-- `pullbackQX (𝟙 X)` is `pullbackQId` at `ℚ_X`. -/
theorem pullbackQX_id (X : TopCat.{0}) :
    pullbackQX (𝟙 X) = (pullbackQId X).app (QX X) := by
  apply Iso.ext
  exact leftAdjointUniq_id_triangle (constantSheafAdj (J X) (ModuleCat.{0} ℚ) isTerminalTop)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) (𝟙 X)) _

/-- Conjugation by `(f₁ ≫ f₂)⁻¹` is conjugation by `f₂⁻¹`, then by `f₁⁻¹`. -/
theorem conjExt_pullbackQ_comp (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (n : ℕ)
    (x : Abelian.Ext.{0} (QX Z) (QX Z) n) :
    conjExt (pullbackQ (f₁ ≫ f₂)) (pullbackQX (f₁ ≫ f₂)) x =
      conjExt (pullbackQ f₁) (pullbackQX f₁) (conjExt (pullbackQ f₂) (pullbackQX f₂) x) :=
  conjExt_eq_of_comp_iso _ _ _ (pullbackQComp f₁ f₂) _ _ _ (pullbackQX_comp f₁ f₂) _

/-- Conjugation by `(𝟙 X)⁻¹` is the identity on `Ext(ℚ_X, ℚ_X)`. -/
theorem conjExt_pullbackQ_id (X : TopCat.{0}) (n : ℕ) (x : Abelian.Ext.{0} (QX X) (QX X) n) :
    conjExt (pullbackQ (𝟙 X)) (pullbackQX (𝟙 X)) x = x :=
  conjExt_eq_of_id_iso _ (pullbackQId X) _ (pullbackQX_id X) _

/-- **Pullback along a composite of continuous maps**: `(f₁ ≫ f₂)^* = f₁^* ∘ f₂^*`. -/
theorem pullbackH_comp (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (n : ℕ) (α : HQ Z n) :
    pullbackH (f₁ ≫ f₂) n α = pullbackH f₁ n (pullbackH f₂ n α) := by
  apply (rationalExtEquiv X n).injective
  rw [rationalExtEquiv_pullbackH, rationalExtEquiv_pullbackH, rationalExtEquiv_pullbackH]
  exact conjExt_pullbackQ_comp f₁ f₂ n _

/-- **Pullback along the identity** of a space is the identity. -/
theorem pullbackH_id (X : TopCat.{0}) (n : ℕ) (α : HQ X n) : pullbackH (𝟙 X) n α = α := by
  apply (rationalExtEquiv X n).injective
  rw [rationalExtEquiv_pullbackH]
  exact conjExt_pullbackQ_id X n _

end Sheaf

section Variety

variable {X Y Z : Over (Spec ↧ℂ)}

/-- **Pullback along a composite.** For `g : X ⟶ Y` and `h : Y ⟶ Z` over `Spec ℂ`,
`(g ≫ h)^* = g^* ∘ h^*` on `Hⁿ(Z; ℚ)`. -/
theorem pullbackCoh_comp (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ) (α : H^n(Z; ℚ)) :
    pullbackCoh (g ≫ h) n α = pullbackCoh g n (pullbackCoh h n α) :=
  pullbackH_comp (pointMap g) (pointMap h) n α

/-- **Pullback along the identity** is the identity on `Hⁿ(X; ℚ)`. -/
theorem pullbackCoh_id (X : Over (Spec ↧ℂ)) (n : ℕ) (α : H^n(X; ℚ)) :
    pullbackCoh (𝟙 X) n α = α :=
  pullbackH_id _ n α

/-- **Pullback as a `ℚ`-linear map** `g^* : Hⁿ(X; ℚ) →ₗ[ℚ] Hⁿ(X'; ℚ)`. Additivity is
`pullbackCoh_add`; a group homomorphism between `ℚ`-vector spaces is `ℚ`-linear. The
`ℚ`-structure on both sides is upstream's `fieldCohomologyModule ℚ` (instance search finds it,
and it agrees by `rfl` with `inferInstance`). Kernel cost: about 7 to 25 s per declaration whose
type mentions this map (`docs/gaps.md`, Known weaknesses). -/
def pullbackCohLinear {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X) (n : ℕ) :
    H^n(X; ℚ) →ₗ[ℚ] H^n(X'; ℚ) :=
  (AddMonoidHom.mk' (pullbackCoh g n) (pullbackCoh_add g n)).toRatLinearMap

/-- `pullbackCohLinear g n` applies `pullbackCoh g n`, by `rfl`. -/
@[simp]
theorem pullbackCohLinear_apply {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X) (n : ℕ)
    (α : H^n(X; ℚ)) : pullbackCohLinear g n α = pullbackCoh g n α := rfl

/-- The linear pullback along a composite is the composite of the linear pullbacks. -/
theorem pullbackCohLinear_comp (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ) :
    pullbackCohLinear (g ≫ h) n = pullbackCohLinear g n ∘ₗ pullbackCohLinear h n :=
  LinearMap.ext fun α => pullbackCoh_comp g h n α

/-- The linear pullback along the identity is the identity. -/
theorem pullbackCohLinear_id (X : Over (Spec ↧ℂ)) (n : ℕ) :
    pullbackCohLinear (𝟙 X) n = LinearMap.id :=
  LinearMap.ext fun α => pullbackCoh_id X n α

/-- A section of `p` makes `p^*` injective: if `s ≫ p = 𝟙`, then `s^* ∘ p^* = id`. -/
theorem pullbackCoh_injective_of_section (p : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (n : ℕ) : Function.Injective (pullbackCoh p n) := by
  intro α β h
  have key : ∀ γ : H^n(Y; ℚ), pullbackCoh s n (pullbackCoh p n γ) = γ := fun γ => by
    rw [← pullbackCoh_comp, hs, pullbackCoh_id]
  rw [← key α, ← key β, h]

/-- **Pullback along a commutative square.** If `f ≫ g = f' ≫ g'`, then
`f^* ∘ g^* = f'^* ∘ g'^*`. -/
theorem pullbackCoh_comm {W : Over (Spec ↧ℂ)} (f : W ⟶ X) (g : X ⟶ Z) (f' : W ⟶ Y)
    (g' : Y ⟶ Z) (w : f ≫ g = f' ≫ g') (n : ℕ) (α : H^n(Z; ℚ)) :
    pullbackCoh f n (pullbackCoh g n α) = pullbackCoh f' n (pullbackCoh g' n α) := by
  rw [← pullbackCoh_comp, w, pullbackCoh_comp]

end Variety

end HodgeLadder.Pullback
