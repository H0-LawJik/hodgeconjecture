module

public import HodgeLadder.Cup.SheafExact

/-!
# Cancelling `ℤ_Y → ℚ_Y` on extensions into rational sheaves

Rung `kappa-cancel` (front `cup`, part of `end-class-right-mult`). Let `κ : ℤ_Y → ℚ_Y` be the map
of constant sheaves of abelian groups. Then `ℚ ⊗ κ` is an isomorphism, and precomposition with
`κ` is injective on `Ext^n(ℚ_Y, M)` for every sheaf `M` of `ℚ`-vector spaces (seen as a sheaf of
abelian groups), in particular for `M = ℚ_Y`.

## Main definitions

* `HodgeLadder.Cup.kappaAb`, `HodgeLadder.Cup.kappaSheaf`

## Main results

* `HodgeLadder.Cup.precomp_kappaAb_bijective`, `HodgeLadder.Cup.isIso_tensorQ_map_kappaAb`,
  `HodgeLadder.Cup.isIso_tensorQSheaf_map_kappaSheaf`, `HodgeLadder.Cup.kappa_cancel`,
  `HodgeLadder.Cup.kappa_cancel_rational`
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace HodgeLadder.Cup

/-- The cast `ℤ → ℚ` of abelian groups (with upstream's `ULift ℤ`). -/
def kappaAb : AddCommGrpCat.of (ULift.{0} ℤ) ⟶ AddCommGrpCat.of ℚ :=
  AddCommGrpCat.ofHom ((Int.castAddHom ℚ).comp AddEquiv.ulift.toAddMonoidHom)

/-- **An additive map from `ℚ` to a `ℚ`-vector space is determined by its value at `1`, and every
value occurs.** -/
lemma precomp_kappaAb_bijective (T : ModuleCat.{0} ℚ) :
    Function.Bijective (fun h : AddCommGrpCat.of ℚ ⟶ U.obj T => kappaAb ≫ h) := by
  have lin : ∀ (h : AddCommGrpCat.of ℚ ⟶ U.obj T) (x : ℚ),
      (show ℚ →+ T from h.hom) x = x • (show ℚ →+ T from h.hom) 1 := fun h x => by
    rw [← map_rat_smul (show ℚ →+ T from h.hom) x 1, smul_eq_mul, mul_one]
  constructor
  · intro h h' hh
    have h1 : (show ℚ →+ T from h.hom) 1 = (show ℚ →+ T from h'.hom) 1 := by
      have := ConcreteCategory.congr_hom hh (ULift.up (1 : ℤ))
      simp only [kappaAb, ConcreteCategory.comp_apply] at this
      exact this
    ext x
    exact (lin h x).trans ((congrArg _ h1).trans (lin h' x).symm)
  · intro g
    refine ⟨AddCommGrpCat.ofHom
      (show ℚ →+ T from
        { toFun := fun x : ℚ => (x • (show ULift.{0} ℤ →+ T from g.hom) (ULift.up 1) : T)
          map_zero' := zero_smul ℚ _
          map_add' := fun x y => add_smul x y _ }), ?_⟩
    ext ⟨n⟩
    change ((n : ℚ) • (show ULift.{0} ℤ →+ T from g.hom) (ULift.up 1) : T) =
      (show ULift.{0} ℤ →+ T from g.hom) (ULift.up n)
    rw [Int.cast_smul_eq_zsmul]
    have : (ULift.up n : ULift.{0} ℤ) = n • ULift.up 1 := by
      ext; simp
    rw [this, map_zsmul]

/-- **`ℚ ⊗ κ` is an isomorphism.** -/
instance isIso_tensorQ_map_kappaAb : IsIso (tensorQ.map kappaAb) := by
  apply isIso_of_coyoneda_map_bijective
  intro T
  have e : (fun x : tensorQ.obj (AddCommGrpCat.of ℚ) ⟶ T => tensorQ.map kappaAb ≫ x) =
      (adjQ.homEquiv _ _).symm ∘ (fun h => kappaAb ≫ h) ∘ (adjQ.homEquiv _ _) := by
    funext x
    change _ = (adjQ.homEquiv _ _).symm (kappaAb ≫ (adjQ.homEquiv _ _) x)
    rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  rw [e]
  exact (Equiv.bijective _).comp ((precomp_kappaAb_bijective T).comp (Equiv.bijective _))

variable (Y : TopCat.{0})

/-- The map `ℤ_Y → ℚ_Y` of constant sheaves of abelian groups. -/
abbrev kappaSheaf : constAb Y (AddCommGrpCat.of (ULift.{0} ℤ)) ⟶ constAb Y (AddCommGrpCat.of ℚ) :=
  (constantSheaf (J Y) AddCommGrpCat.{0}).map kappaAb

/-- **Sheafified `ℚ ⊗ κ` is an isomorphism.** -/
instance isIso_tensorQSheaf_map_kappaSheaf : IsIso ((tensorQSheaf Y).map (kappaSheaf Y)) :=
  (NatIso.isIso_map_iff (tensorQConstIso Y) kappaAb).mpr
    (inferInstanceAs (IsIso ((constantSheaf (J Y) (ModuleCat.{0} ℚ)).map (tensorQ.map kappaAb))))

/-- **Precomposition with `κ` is injective on extensions into a sheaf of `ℚ`-vector spaces.** -/
theorem kappa_cancel (M : Sheaf (J Y) (ModuleCat.{0} ℚ)) {n : ℕ}
    (x x' : Abelian.Ext.{0} (constAb Y (AddCommGrpCat.of ℚ)) ((forgetSheaf Y).obj M) n)
    (h : (Abelian.Ext.mk₀ (kappaSheaf Y)).comp x (zero_add n) =
      (Abelian.Ext.mk₀ (kappaSheaf Y)).comp x' (zero_add n)) : x = x' := by
  obtain ⟨e, rfl⟩ := (adjQSheaf Y).extEquiv.surjective x
  obtain ⟨e', rfl⟩ := (adjQSheaf Y).extEquiv.surjective x'
  rw [← Adjunction.extEquiv_naturality_left₀, ← Adjunction.extEquiv_naturality_left₀] at h
  have h' := congrArg
    (fun t => (Abelian.Ext.mk₀ (inv ((tensorQSheaf Y).map (kappaSheaf Y)))).comp t (zero_add n))
    ((adjQSheaf Y).extEquiv.injective h)
  simp only [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    IsIso.inv_hom_id, Abelian.Ext.mk₀_id_comp] at h'
  rw [h']

/-- **The same with target `ℚ_Y`.** -/
theorem kappa_cancel_rational {n : ℕ}
    (x x' : Abelian.Ext.{0} (constAb Y (AddCommGrpCat.of ℚ)) (constAb Y (AddCommGrpCat.of ℚ)) n)
    (h : (Abelian.Ext.mk₀ (kappaSheaf Y)).comp x (zero_add n) =
      (Abelian.Ext.mk₀ (kappaSheaf Y)).comp x' (zero_add n)) : x = x' := by
  apply (extPostcompEquiv (forgetQX Y).symm n).injective
  apply kappa_cancel Y (QX Y)
  simp only [extPostcompEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero, h, Abelian.Ext.comp_assoc_of_third_deg_zero]

end HodgeLadder.Cup
