module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Topology.Sheaves.Forget
public import Mathlib.AlgebraicGeometry.FunctionField
public import LefschetzPort.AlgebraicGeometry.InvertibleSheafRationalSection

/-!
# The vanishing ideal sheaf of a closed set, as a sheaf of modules

For a set `Z` of points of a scheme `S`, the sections of `𝒪_S` over `U` whose germs at the points
of `Z ∩ U` lie in the maximal ideals form an ideal of `Γ(S, U)`; these ideals form a sheaf of
`𝒪_S`-modules, `HodgeLadder.vanishingIdealSheaf Z`. Mathlib's `Scheme.IdealSheafData` records
the same ideals on affine opens but not as an object of `S.Modules`. Part of rung
`prime-divisor-ideal-sheaf` (`docs/sketches/prime-divisors-cartier.md`).

## Main definitions

* `HodgeLadder.vanishingIdealSections Z U`: the ideal of sections over `U` vanishing on `Z`.
* `HodgeLadder.vanishingIdealSheaf Z : S.Modules`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace HodgeLadder

variable {S : Scheme.{u}} (Z : Set S)

/-- The sections of `𝒪_S` over `U` whose germs at the points of `Z ∩ U` are not units. -/
def vanishingIdealSections (U : S.Opens) : Ideal Γ(S, U) where
  carrier := {s | ∀ (x : S) (hx : x ∈ U), x ∈ Z →
    S.presheaf.germ U x hx s ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk x)}
  add_mem' {a b} ha hb x hx hz := by
    rw [map_add]; exact Ideal.add_mem _ (ha x hx hz) (hb x hx hz)
  zero_mem' x hx _ := by rw [map_zero]; exact Ideal.zero_mem _
  smul_mem' c s hs x hx hz := by
    rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ (hs x hx hz)

variable {Z}

lemma mem_vanishingIdealSections {U : S.Opens} (s : Γ(S, U)) :
    s ∈ vanishingIdealSections Z U ↔ ∀ (x : S) (hx : x ∈ U), x ∈ Z →
      S.presheaf.germ U x hx s ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk x) := Iff.rfl

/-- Restriction preserves vanishing on `Z`. -/
lemma res_mem_vanishingIdealSections {U V : S.Opens} (i : V ⟶ U) {s : Γ(S, U)}
    (hs : s ∈ vanishingIdealSections Z U) :
    S.presheaf.map i.op s ∈ vanishingIdealSections Z V := by
  intro x hx hz
  rw [S.presheaf.germ_res_apply i x hx s]
  exact hs x (leOfHom i hx) hz

variable (Z)

/-- The vanishing ideals as a subpresheaf of the presheaf of sets underlying `𝒪_S`. -/
def vanishingIdealSubfunctor : Subfunctor (S.presheaf ⋙ forget CommRingCat) where
  obj U := {s | s ∈ vanishingIdealSections Z U.unop}
  map {_ _} i _ hs := res_mem_vanishingIdealSections i.unop hs

/-- Membership in the vanishing ideal is local, so the subpresheaf is a sheaf. -/
theorem vanishingIdealSubfunctor_isSheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology S) (vanishingIdealSubfunctor Z).toFunctor := by
  have hF : Presieve.IsSheaf (Opens.grothendieckTopology S) (S.presheaf ⋙ forget CommRingCat) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1
      ((TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat) S.presheaf).1 S.IsSheaf)
  rw [Subfunctor.isSheaf_iff _ hF]
  intro U s hs x hx hz
  obtain ⟨V, i, hiV, hxV⟩ := hs x hx
  have := hiV x hxV hz
  have h := S.presheaf.germ_res_apply i x hxV s
  exact h ▸ this

/-- The vanishing ideal is a module over the ring of sections, written through the structure
sheaf as a sheaf of rings. -/
instance (U : S.Opensᵒᵖ) : Module (S.ringCatSheaf.obj.obj U) (vanishingIdealSections Z U.unop) :=
  inferInstanceAs (Module Γ(S, U.unop) (vanishingIdealSections Z U.unop))

/-- The vanishing ideal over `U`, as a module over the ring of sections. -/
def vanishingIdealModule (U : S.Opensᵒᵖ) : ModuleCat (S.ringCatSheaf.obj.obj U) :=
  ModuleCat.of (S.ringCatSheaf.obj.obj U) (vanishingIdealSections Z U.unop)

/-- Restriction of vanishing sections, linear after restricting scalars. -/
def vanishingIdealModuleMap {U V : S.Opensᵒᵖ} (i : U ⟶ V) :
    vanishingIdealModule Z U ⟶
      (ModuleCat.restrictScalars (S.ringCatSheaf.obj.map i).hom).obj (vanishingIdealModule Z V) := by
  letI : Module (S.ringCatSheaf.obj.obj U) (vanishingIdealModule Z V) :=
    Module.compHom (vanishingIdealModule Z V) (S.ringCatSheaf.obj.map i).hom
  exact ModuleCat.ofHom
    { toFun s := ⟨S.presheaf.map i s.1, res_mem_vanishingIdealSections i.unop s.2⟩
      map_add' a b := Subtype.ext (map_add _ a.1 b.1)
      map_smul' r a := Subtype.ext (map_mul (S.presheaf.map i).hom r a.1) }

/-- The vanishing ideals, as a presheaf of `𝒪_S`-modules. -/
def vanishingIdealPresheafOfModules : PresheafOfModules S.ringCatSheaf.obj where
  obj := vanishingIdealModule Z
  map := vanishingIdealModuleMap Z
  map_id U := by
    ext s
    exact Subtype.ext (by simp [vanishingIdealModuleMap]; rfl)
  map_comp f g := by
    ext s
    apply Subtype.ext
    simp only [vanishingIdealModuleMap]
    change S.presheaf.map (f ≫ g) s.1 = S.presheaf.map g (S.presheaf.map f s.1)
    rw [Functor.map_comp, CommRingCat.comp_apply]

/-- **The vanishing ideal sheaf** of `Z`, as an object of `S.Modules`. -/
def vanishingIdealSheaf : S.Modules where
  val := vanishingIdealPresheafOfModules Z
  isSheaf := by
    refine (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp _ _ (forget AddCommGrpCat)).2 ?_
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    have e : (vanishingIdealPresheafOfModules Z).presheaf ⋙ forget AddCommGrpCat ≅
        (vanishingIdealSubfunctor Z).toFunctor :=
      NatIso.ofComponents (fun U => Equiv.toIso
        { toFun s := ⟨(s : vanishingIdealSections Z U.unop).1, (s : vanishingIdealSections Z U.unop).2⟩
          invFun s := (⟨s.1, s.2⟩ : vanishingIdealSections Z U.unop)
          left_inv _ := rfl
          right_inv _ := rfl }) (fun _ => rfl)
    exact (Presieve.isSheaf_iso _ e.symm) (vanishingIdealSubfunctor_isSheaf Z)

section Generators

variable {Z}

/-- `π ∈ Γ(S, U)` generates the vanishing ideal of `Z` on `W ⊆ U` when every vanishing section
over an open `V ⊆ W` is a multiple of `π`. -/
def GeneratesVanishingOn {U : S.Opens} (π : Γ(S, U)) (W : S.Opens) (hW : W ≤ U) : Prop :=
  ∀ (V : S.Opens) (hV : V ≤ W) (s : Γ(S, V)), s ∈ vanishingIdealSections Z V →
    ∃ r : Γ(S, V), s = r * S.presheaf.map (homOfLE (hV.trans hW)).op π

/-- Restrictions compose. -/
lemma res_res {U V W : S.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(S, U)) :
    S.presheaf.map (homOfLE h₂).op (S.presheaf.map (homOfLE h₁).op a) =
      S.presheaf.map (homOfLE (h₂.trans h₁)).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable [IsIntegral S]

omit [IsIntegral S] in
private lemma subsingleton_of_not_nonempty {V : S.Opens} (hV : ¬ Nonempty V) :
    Subsingleton Γ(S, V) := by
  have : V = ⊥ := by
    ext x
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => hV ⟨⟨x, hx⟩⟩
  subst this
  infer_instance

/-- Multiplication by a nonzero section is injective on every smaller open. -/
lemma mul_res_injective {U V : S.Opens} (hVU : V ≤ U) {π : Γ(S, U)} (hπ : π ≠ 0) :
    Function.Injective fun r : Γ(S, V) => r * S.presheaf.map (homOfLE hVU).op π := by
  by_cases hV : Nonempty V
  · have hπV : S.presheaf.map (homOfLE hVU).op π ≠ 0 := fun h =>
      hπ (map_injective_of_isIntegral S (homOfLE hVU) (by rw [h, map_zero]))
    intro a b hab
    exact mul_right_cancel₀ hπV hab
  · have := subsingleton_of_not_nonempty hV
    intro a b _
    exact Subsingleton.elim a b

/-- **Local generation gives a generating section.** If `π` vanishes on `Z`, is nonzero, and
generates the vanishing ideal near every point of `U`, then `π` generates the vanishing ideal
sheaf on `U`. -/
theorem generates_of_locally {U : S.Opens} (π : Γ(S, U))
    (hπ : π ∈ vanishingIdealSections Z U) (hπ0 : π ≠ 0)
    (hloc : ∀ x ∈ U, ∃ (W : S.Opens) (hW : W ≤ U), x ∈ W ∧ GeneratesVanishingOn (Z := Z) π W hW) :
    Scheme.Modules.Generates (L := vanishingIdealSheaf Z)
      (show Γ(vanishingIdealSheaf Z, U) from ⟨π, hπ⟩) := by
  intro V hVU
  refine ⟨fun a b hab => mul_res_injective hVU hπ0 (congrArg Subtype.val hab), ?_⟩
  rintro ⟨t, ht⟩
  -- local quotients
  have hpt : ∀ x : V, ∃ (W : S.Opens) (hW : W ≤ U), (x : S) ∈ W ∧
      GeneratesVanishingOn (Z := Z) π W hW := fun x => hloc x (hVU x.2)
  choose W hW hxW hgen using hpt
  let Vx : V → S.Opens := fun x => V ⊓ W x
  have hq : ∀ x : V, ∃ r : Γ(S, Vx x),
      S.presheaf.map (homOfLE inf_le_left).op t =
        r * S.presheaf.map (homOfLE (inf_le_right.trans (hW x))).op π := fun x =>
    hgen x (Vx x) inf_le_right _ (res_mem_vanishingIdealSections (homOfLE inf_le_left) ht)
  choose r hr using hq
  have hcover : V ≤ iSup Vx := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, ⟨hy, hxW ⟨y, hy⟩⟩⟩
  have hcomp : TopCat.Presheaf.IsCompatible S.sheaf.1 Vx r := by
    intro x y
    apply mul_res_injective ((inf_le_left : Vx x ⊓ Vx y ≤ Vx x).trans
      (inf_le_right.trans (hW x))) hπ0
    have h1 := congrArg (S.presheaf.map (homOfLE (inf_le_left : Vx x ⊓ Vx y ≤ Vx x)).op) (hr x)
    have h2 := congrArg (S.presheaf.map (homOfLE (inf_le_right : Vx x ⊓ Vx y ≤ Vx y)).op) (hr y)
    rw [map_mul, res_res, res_res] at h1 h2
    change S.presheaf.map (homOfLE inf_le_left).op (r x) * _ =
      S.presheaf.map (homOfLE inf_le_right).op (r y) * _
    rw [← h1, h2]
  obtain ⟨g, hg, -⟩ := S.sheaf.existsUnique_gluing' Vx V (fun x => homOfLE inf_le_left) hcover r hcomp
  refine ⟨(show Γ(S, V) from g), Subtype.ext ?_⟩
  change (show Γ(S, V) from g) * S.presheaf.map (homOfLE hVU).op π = t
  apply TopCat.Sheaf.eq_of_locally_eq' S.sheaf Vx V (fun x => homOfLE inf_le_left) hcover
  intro x
  change S.presheaf.map (homOfLE inf_le_left).op
      ((show Γ(S, V) from g) * S.presheaf.map (homOfLE hVU).op π) =
    S.presheaf.map (homOfLE inf_le_left).op t
  rw [map_mul, res_res, hr x]
  congr 1
  exact hg x

end Generators

end HodgeLadder
