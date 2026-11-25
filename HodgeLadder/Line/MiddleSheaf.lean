module

public import HodgeLadder.Line.Transitions
public import HodgeLadder.Line.LocallyConstant
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The middle sheaf of the unit extension of a line bundle

Let `σ` be a holomorphic trivializing cover of `M` with transition values `g i j`
(`σ i = g i j • σ j`), and choose a base index `b z` with `z ∈ U (b z)`. A section of the middle
sheaf `N` on `U` is a function `z ↦ (n z, v z) ∈ ℤ × ℂˣ` with `n` locally constant and, for every
`i`, `z ↦ g (b z) i z ^ n z * v z` holomorphic on `U ⊓ Uᵢ`. Pointwise addition makes `N` a sheaf
of abelian groups (holomorphy is a local predicate). Part of rung
`unit-extension-of-invertible` (step B1).

## Main definitions

* `HodgeLadder.TCover.middleSheaf`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexPoint Filter
open scoped Manifold ContDiff Topology

namespace HodgeLadder

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance middleSheafTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable {M : SheafOfModules (holomorphicRingSheaf X d)} (T : HolomorphicTrivializingCover M)

namespace TCover

/-- The fiber of the middle sheaf. -/
abbrev Fib := ℤ × Additive ℂˣ

/-- A chosen member of the cover containing each point. -/
def base (z : ComplexPoint X) : T.ι := (T.covers z).choose

lemma mem_base (z : ComplexPoint X) : z ∈ T.opens (base T z) := (T.covers z).choose_spec

/-- A function on an open set, extended by `0` to the whole space. -/
def ext (U : Opens (TopCat.of (ComplexPoint X))) (s : U → Fib) (y : ComplexPoint X) : Fib := by
  classical
  exact if hy : y ∈ U then s ⟨y, hy⟩ else 0

lemma ext_of_mem (U : Opens (TopCat.of (ComplexPoint X))) (s : U → Fib) (y : ComplexPoint X)
    (hy : y ∈ U) : ext U s y = s ⟨y, hy⟩ := dif_pos hy

/-- The chart-`i` coordinate `g (b y) i y ^ n y * v y` of an ambient function. -/
def hcoord (i : T.ι) (g : ComplexPoint X → Fib) (y : ComplexPoint X) : ℂ :=
  gval T (base T y) i y ^ (g y).1 * ((Additive.toMul (g y).2 : ℂˣ) : ℂ)

lemma hcoord_ne_zero (i : T.ι) (g : ComplexPoint X → Fib) (y : ComplexPoint X) :
    hcoord T i g y ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (gval_ne_zero T _ _ _)) (Additive.toMul (g y).2).ne_zero

/-- The pointwise condition at `z`: locally constant degree, holomorphic chart coordinates. -/
def Good (g : ComplexPoint X → Fib) (z : ComplexPoint X) : Prop :=
  (∀ᶠ y in 𝓝 z, (g y).1 = (g z).1) ∧
    ∀ i, z ∈ T.opens i → ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (hcoord T i g) z

lemma Good.congr {g g' : ComplexPoint X → Fib} {z : ComplexPoint X} (h : g =ᶠ[𝓝 z] g')
    (hg : Good T g z) : Good T g' z := by
  have hz : g z = g' z := h.eq_of_nhds
  refine ⟨?_, fun i hi => (hg.2 i hi).congr_of_eventuallyEq ?_⟩
  · filter_upwards [hg.1, h] with y hy hgy
    rw [← hgy, hy, hz]
  · filter_upwards [h] with y hy
    simp only [hcoord, hy]

lemma ext_restrict {U V : Opens (TopCat.of (ComplexPoint X))} (i : V ⟶ U) (f : U → Fib)
    (z : ComplexPoint X) (hz : z ∈ V) :
    ext V (fun x : V => f ⟨x.1, i.le x.2⟩) =ᶠ[𝓝 z] ext U f := by
  filter_upwards [V.isOpen.mem_nhds hz] with y hy
  rw [ext_of_mem V _ y hy, ext_of_mem U f y (i.le hy)]

/-- The local predicate defining the middle sheaf. -/
def middlePredicate : TopCat.LocalPredicate (fun _ : TopCat.of (ComplexPoint X) => Fib) where
  pred {U} f := ∀ z : U, Good T (ext U f) z
  res {V U} i f hf z :=
    (hf ⟨z, i.le z.property⟩).congr T (ext_restrict i f z z.property).symm
  locality {U} f hf z := by
    obtain ⟨V, hzV, i, hV⟩ := hf z
    exact (hV ⟨z, hzV⟩).congr T (ext_restrict i f z hzV)

lemma ext_zero (U : Opens (TopCat.of (ComplexPoint X))) : ext U (0 : U → Fib) = 0 := by
  funext y
  unfold ext
  split_ifs <;> rfl

lemma ext_add (U : Opens (TopCat.of (ComplexPoint X))) (s t : U → Fib) :
    ext U (s + t) = ext U s + ext U t := by
  funext y
  by_cases hy : y ∈ U <;> simp [ext, hy]

lemma ext_neg (U : Opens (TopCat.of (ComplexPoint X))) (s : U → Fib) :
    ext U (-s) = -ext U s := by
  funext y
  by_cases hy : y ∈ U <;> simp [ext, hy]

lemma hcoord_zero (i : T.ι) : hcoord T i (0 : ComplexPoint X → Fib) = fun _ => 1 := by
  funext y
  simp [hcoord]

lemma hcoord_add (i : T.ι) (g g' : ComplexPoint X → Fib) :
    hcoord T i (g + g') = hcoord T i g * hcoord T i g' := by
  funext y
  simp only [hcoord, Pi.add_apply, Prod.fst_add, Prod.snd_add, toMul_add, Units.val_mul,
    Pi.mul_apply, zpow_add₀ (gval_ne_zero T _ _ _)]
  ring

lemma hcoord_neg (i : T.ι) (g : ComplexPoint X → Fib) :
    hcoord T i (-g) = fun y => (hcoord T i g y)⁻¹ := by
  funext y
  simp only [hcoord, Pi.neg_apply, Prod.fst_neg, Prod.snd_neg, toMul_neg, zpow_neg,
    Units.val_inv_eq_inv_val, mul_inv]

lemma good_zero (z : ComplexPoint X) : Good T (0 : ComplexPoint X → Fib) z :=
  ⟨Eventually.of_forall fun _ => rfl, fun i _ => by
    rw [hcoord_zero]
    exact contMDiffAt_const⟩

lemma Good.add {g g' : ComplexPoint X → Fib} {z : ComplexPoint X} (hg : Good T g z)
    (hg' : Good T g' z) : Good T (g + g') z := by
  refine ⟨?_, fun i hi => ?_⟩
  · filter_upwards [hg.1, hg'.1] with y hy hy'
    simp only [Pi.add_apply, Prod.fst_add, hy, hy']
  · rw [hcoord_add]
    exact (hg.2 i hi).mul (hg'.2 i hi)

lemma Good.neg {g : ComplexPoint X → Fib} {z : ComplexPoint X} (hg : Good T g z) :
    Good T (-g) z := by
  refine ⟨?_, fun i hi => ?_⟩
  · filter_upwards [hg.1] with y hy
    simp only [Pi.neg_apply, Prod.fst_neg, hy]
  · rw [hcoord_neg]
    exact (hg.2 i hi).inv₀ (hcoord_ne_zero T i g z)

/-- Sections of the middle sheaf on `U`. -/
def middleSubgroup (U : Opens (TopCat.of (ComplexPoint X))) : AddSubgroup (U → Fib) where
  carrier := (middlePredicate T).pred
  zero_mem' z := by
    change Good T (ext U 0) z
    rw [ext_zero]
    exact good_zero T z
  add_mem' {s t} hs ht z := by
    change Good T (ext U (s + t)) z
    rw [ext_add]
    exact (hs z).add T (ht z)
  neg_mem' {s} hs z := by
    change Good T (ext U (-s)) z
    rw [ext_neg]
    exact (hs z).neg T

/-- Restriction of middle sections. -/
def middleRestriction {U V : Opens (TopCat.of (ComplexPoint X))} (i : U ⟶ V) :
    middleSubgroup T V →+ middleSubgroup T U where
  toFun f := ⟨fun x => f.val ⟨x, i.le x.property⟩, (middlePredicate T).res i f.val f.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The presheaf of middle sections. -/
def middlePresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) where
  obj U := AddCommGrpCat.of (middleSubgroup T (unop U))
  map i := AddCommGrpCat.ofHom (middleRestriction T i.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The middle sheaf.** -/
def middleSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) where
  obj := middlePresheaf T
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat)]
    exact (TopCat.subsheafToTypes (middlePredicate T)).property

/-- A holomorphic function is holomorphic at a point of its domain, in any ambient extension. -/
lemma contMDiffAt_of_hev {U : Opens (TopCat.of (ComplexPoint X))}
    (r : (holomorphicRingSheaf X d).obj.obj (op U)) (F : ComplexPoint X → ℂ)
    (hF : ∀ y (hy : y ∈ U), F y = hev r y hy) (z : ComplexPoint X) (hz : z ∈ U) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω F z := by
  apply (contMDiffAt_subtype_iff (U := U) (x := ⟨z, hz⟩)).mp
  have hfun : (fun w : U => F w) = hmap r := by
    funext w
    exact hF w w.property
  rw [hfun]
  exact (ContMDiffMap.contMDiff (hmap r)).contMDiffAt

/-- The value of a holomorphic unit at a point. -/
def uev {U : Opens (TopCat.of (ComplexPoint X))}
    (u : ((holomorphicRingSheaf X d).obj.obj (op U))ˣ) (z : ComplexPoint X) (hz : z ∈ U) : ℂˣ where
  val := hev u.val z hz
  inv := hev u.inv z hz
  val_inv := by rw [← hev_mul, u.val_inv, hev_one]
  inv_val := by rw [← hev_mul, u.inv_val, hev_one]

/-- A section of the holomorphic-unit sheaf as a unit of holomorphic functions. -/
abbrev unitOf {U : Opens (TopCat.of (ComplexPoint X))}
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) : ((holomorphicRingSheaf X d).obj.obj (op U))ˣ :=
  Additive.toMul a

/-- The middle section of a holomorphic unit: degree `0`, value the unit. -/
def inclSection {U : Opens (TopCat.of (ComplexPoint X))}
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) : U → Fib :=
  fun z => (0, Additive.ofMul (uev (unitOf a) z z.property))

lemma inclSection_mem {U : Opens (TopCat.of (ComplexPoint X))}
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    inclSection a ∈ middleSubgroup T U := by
  intro z
  have h1 : ∀ y, (ext U (inclSection a) y).1 = 0 := by
    intro y
    by_cases hy : y ∈ U <;> simp [ext, hy, inclSection]
  refine ⟨Eventually.of_forall fun y => by rw [h1, h1], fun i _ => ?_⟩
  apply (contMDiffAt_of_hev (unitOf a).val _ _ z z.property).congr_of_eventuallyEq
  · filter_upwards [U.isOpen.mem_nhds z.property] with y hy
    rfl
  · intro y hy
    simp only [hcoord, ext_of_mem U _ y hy, inclSection, zpow_zero, one_mul, toMul_ofMul]
    rfl

/-- Holomorphic sections agree when their values agree. -/
lemma hsec_ext {U : Opens (TopCat.of (ComplexPoint X))}
    {r s : (holomorphicRingSheaf X d).obj.obj (op U)}
    (h : ∀ z (hz : z ∈ U), hev r z hz = hev s z hz) : r = s := by
  have : hmap r = hmap s := ContMDiffMap.ext fun w => h w.1 w.2
  exact this

/-- A holomorphic map as a section of the ring sheaf. -/
def hof {U : Opens (TopCat.of (ComplexPoint X))} (f : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) :
    (holomorphicRingSheaf X d).obj.obj (op U) := f

lemma hev_hof {U : Opens (TopCat.of (ComplexPoint X))} (f : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯)
    (z : ComplexPoint X) (hz : z ∈ U) : hev (hof f) z hz = f ⟨z, hz⟩ := rfl

lemma ContMDiffAt.zpow' {F : ComplexPoint X → ℂ} {z : ComplexPoint X}
    (hF : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω F z) (h0 : F z ≠ 0) (m : ℤ) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (fun y => F y ^ m) z := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa using hF.pow k
  · simpa using (hF.pow k).inv₀ (pow_ne_zero k h0)

/-- A nowhere-zero holomorphic function on `U` as a unit of holomorphic functions. -/
def unitOfFun {U : Opens (TopCat.of (ComplexPoint X))} (v : U → ℂˣ)
    (hv : ∀ z : U, ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (fun w : U => (v w : ℂ)) z) :
    ((holomorphicRingSheaf X d).obj.obj (op U))ˣ where
  val := hof ⟨fun w => v w, hv⟩
  inv := hof ⟨fun w => ((v w)⁻¹ : ℂˣ), fun z => by
    simpa only [Units.val_inv_eq_inv_val] using (hv z).inv₀ (v z).ne_zero⟩
  val_inv := hsec_ext fun z hz =>
    show ((v ⟨z, hz⟩ : ℂˣ) : ℂ) * (((v ⟨z, hz⟩)⁻¹ : ℂˣ) : ℂ) = 1 from (v ⟨z, hz⟩).mul_inv
  inv_val := hsec_ext fun z hz =>
    show (((v ⟨z, hz⟩)⁻¹ : ℂˣ) : ℂ) * ((v ⟨z, hz⟩ : ℂˣ) : ℂ) = 1 from (v ⟨z, hz⟩).inv_mul

lemma uev_unitOfFun {U : Opens (TopCat.of (ComplexPoint X))} (v : U → ℂˣ)
    (hv : ∀ z : U, ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (fun w : U => (v w : ℂ)) z)
    (z : ComplexPoint X) (hz : z ∈ U) : uev (unitOfFun v hv) z hz = v ⟨z, hz⟩ :=
  Units.ext rfl

/-- The degree of a middle section, a locally constant integer function. -/
def degree {U : Opens (TopCat.of (ComplexPoint X))} (s : middleSubgroup T U) :
    lcSubgroup (TopCat.of (ComplexPoint X)) U :=
  ⟨fun z => (s.1 z).1, by
    refine continuous_iff_continuousAt.mpr fun z => ?_
    have h := continuousAt_subtype_val.eventually (s.2 z).1
    refine (continuousAt_const (y := (s.1 z).1)).congr (h.mono fun y hy => ?_)
    change (ext U s.1 y).1 = (ext U s.1 z).1 at hy
    rw [ext_of_mem U _ _ y.2, ext_of_mem U _ _ z.2] at hy
    exact hy.symm⟩

/-- The degree map as a morphism of sheaves. -/
def projection : middleSheaf T ⟶ lcSheaf (TopCat.of (ComplexPoint X)) :=
  ⟨{ app _ := AddCommGrpCat.ofHom
      { toFun := degree T
        map_zero' := rfl
        map_add' _ _ := rfl }
     naturality _ _ _ := rfl }⟩

/-- A middle section of degree zero is a holomorphic unit. -/
lemma exists_incl_of_degree_eq_zero {U : Opens (TopCat.of (ComplexPoint X))}
    (s : middleSubgroup T U) (hs : ∀ z : U, (s.1 z).1 = 0) :
    ∃ a : (holomorphicUnitSheaf X d).obj.obj (op U), inclSection a = s.1 := by
  let v : U → ℂˣ := fun w => Additive.toMul (s.1 w).2
  have hv : ∀ z : U, ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (fun w : U => (v w : ℂ)) z := by
    intro z
    apply (contMDiffAt_subtype_iff (U := U) (x := z)
      (f := hcoord T (base T z) (ext U s.1))).mpr ((s.2 z).2 _ (mem_base T z)) |>.congr_of_eventuallyEq
    refine Eventually.of_forall fun w => ?_
    simp only [hcoord, ext_of_mem U _ _ w.2, hs w, zpow_zero, one_mul, v]
  refine ⟨Additive.ofMul (unitOfFun v hv), ?_⟩
  funext w
  refine Prod.ext (hs w).symm ?_
  change Additive.ofMul (uev (unitOfFun v hv) w w.2) = (s.1 w).2
  rw [uev_unitOfFun]
  rfl

/-- Transition values as units. -/
def gunit (i j : T.ι) (z : ComplexPoint X) : ℂˣ := Units.mk0 (gval T i j z) (gval_ne_zero T i j z)

lemma uev_mul {U : Opens (TopCat.of (ComplexPoint X))}
    (u v : ((holomorphicRingSheaf X d).obj.obj (op U))ˣ) (z : ComplexPoint X) (hz : z ∈ U) :
    uev (u * v) z hz = uev u z hz * uev v z hz := Units.ext (hev_mul _ _ z hz)

lemma inclSection_zero (U : Opens (TopCat.of (ComplexPoint X))) :
    inclSection (0 : (holomorphicUnitSheaf X d).obj.obj (op U)) = 0 := by
  funext w
  exact Prod.ext rfl (congrArg Additive.ofMul (Units.ext rfl))

lemma inclSection_add {U : Opens (TopCat.of (ComplexPoint X))}
    (a b : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    inclSection (a + b) = inclSection a + inclSection b := by
  funext w
  exact Prod.ext (add_zero 0).symm (congrArg Additive.ofMul (uev_mul _ _ _ _))

lemma inclSection_injective (U : Opens (TopCat.of (ComplexPoint X))) :
    Function.Injective (inclSection (X := X) (d := d) (U := U)) := by
  intro a b h
  apply Additive.toMul.injective
  apply Units.ext
  apply hsec_ext
  intro z hz
  have := congrArg (fun t : U → Fib => ((Additive.toMul (t ⟨z, hz⟩).2 : ℂˣ) : ℂ)) h
  exact this

/-- The inclusion of holomorphic units into the middle sheaf. -/
def inclusion : holomorphicUnitSheaf X d ⟶ middleSheaf T :=
  ⟨{ app _ := AddCommGrpCat.ofHom
      { toFun a := ⟨inclSection a, inclSection_mem T a⟩
        map_zero' := Subtype.ext (inclSection_zero _)
        map_add' a b := Subtype.ext (inclSection_add a b) }
     naturality _ _ _ := rfl }⟩

lemma inclusion_apply {U : Opens (TopCat.of (ComplexPoint X))}
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    ((inclusion T).hom.app (op U) a).1 = inclSection a := rfl

lemma inclusion_projection : inclusion T ≫ projection T = 0 := by
  apply Sheaf.hom_ext
  ext U a
  apply Subtype.ext
  funext w
  rfl

/-- The projection is locally surjective. -/
lemma projection_isLocallySurjective :
    TopCat.Presheaf.IsLocallySurjective (projection T).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t z hz
  let n : U → ℤ := t.1
  have hn : Continuous n := t.2
  let k := base T z
  let m := n ⟨z, hz⟩
  let V : Opens (TopCat.of (ComplexPoint X)) :=
    ⟨Subtype.val '' (n ⁻¹' {m}), U.isOpen.isOpenMap_subtype_val _
      ((isOpen_discrete _).preimage hn)⟩ ⊓ T.opens k
  have hVU : V ≤ U := by
    rintro _ ⟨⟨y, -, rfl⟩, -⟩
    exact y.2
  have hVn : ∀ y : V, n ⟨y.1, hVU y.2⟩ = m := by
    rintro ⟨_, ⟨y', hy', rfl⟩, -⟩
    exact hy'
  have hzV : z ∈ V := ⟨⟨⟨z, hz⟩, rfl, rfl⟩, mem_base T z⟩
  let sf : V → Fib := fun y => (m, Additive.ofMul (gunit T k (base T y) y ^ m))
  have hsf : sf ∈ middleSubgroup T V := by
    intro y
    have hev : ∀ w (hw : w ∈ V), ext V sf w = sf ⟨w, hw⟩ := fun w hw => ext_of_mem V sf w hw
    refine ⟨?_, fun i hi => ?_⟩
    · filter_upwards [V.isOpen.mem_nhds y.2] with w hw
      rw [hev w hw, hev y y.2]
    · have hyk : (y : ComplexPoint X) ∈ T.opens k := y.2.2
      have hg0 : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (gval T k i) y :=
        (contMDiffOn_gval T k i).contMDiffAt
          (inter_mem ((T.opens k).isOpen.mem_nhds hyk) ((T.opens i).isOpen.mem_nhds hi))
      have hg := ContMDiffAt.zpow' hg0 (gval_ne_zero T k i y) m
      apply hg.congr_of_eventuallyEq
      filter_upwards [V.isOpen.mem_nhds y.2, (T.opens i).isOpen.mem_nhds hi] with w hw hwi
      unfold hcoord
      rw [hev w hw]
      simp only [sf, gunit, toMul_ofMul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← mul_zpow, mul_comm, gval_mul T k (base T w) i w hw.2 (mem_base T w) hwi]
  refine ⟨V, hVU, ⟨⟨sf, hsf⟩, ?_⟩, hzV⟩
  apply Subtype.ext
  funext y
  exact (hVn y).symm

end TCover

end HodgeLadder
