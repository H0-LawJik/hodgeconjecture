module

public import HodgeLadder.Line.UnitExtension
public import HodgeLadder.Line.FrameComparison
public import LefschetzPort.AlgebraicGeometry.HolomorphicLineBundleFrame

/-!
# The section sheaf of the unit extension of a trivializing cover

For a holomorphic trivializing cover `σ` of `M`, the unit extension `E` built from `σ` has
section sheaf isomorphic to `M`. The chosen local lifts of `1` through `E` have degree one and
values `vˣ`; on `Oₓ ⊓ Uᵢ` the section `wˣᵢ • σ i` of `M`, with `wˣᵢ = g (b ·) i · vˣ`, has the
transition functions of `E`'s canonical frames, so `HodgeLadder.Frames.isoOfSameTransitions`
applies. Part of rung `unit-extension-of-invertible` (step B3).

## Main results

* `HodgeLadder.TCover.sectionIso`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry ComplexPoint Filter
open scoped Manifold ContDiff

namespace HodgeLadder

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance ofInvertibleTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable {M : SheafOfModules (holomorphicRingSheaf X d)} (T : HolomorphicTrivializingCover M)

namespace TCover

/-- The chosen lift through the unit extension at `x`. -/
abbrev lift (x : ComplexPoint X) : middleSubgroup T ((unitExtension T).localLifts.opens x) :=
  (unitExtension T).localLifts.lift x

lemma constIso_hom_top :
    (constIsoLC (TopCat.of (ComplexPoint X))).hom.hom.app (op ⊤)
      (HolomorphicUnitExtension.integerOneSection (X := X)) = ⟨fun _ => 1, continuous_const⟩ := by
  have h1 := ConcreteCategory.congr_hom (congrArg (fun φ => φ.app (op ⊤))
    (toSheafify_constToLCSheaf (TopCat.of (ComplexPoint X)))) (1 : ℤ)
  erw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h1
  exact h1

lemma constIso_hom_one (V : Opens (TopCat.of (ComplexPoint X))) :
    (constIsoLC (TopCat.of (ComplexPoint X))).hom.hom.app (op V)
      ((𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : V ≤ ⊤)).op
        (HolomorphicUnitExtension.integerOneSection (X := X))) =
        ⟨fun _ => 1, continuous_const⟩ := by
  erw [NatTrans.naturality_apply, constIso_hom_top]
  rfl

/-- The chosen lifts have degree one. -/
lemma lift_degree (x : ComplexPoint X) (z : (unitExtension T).localLifts.opens x) :
    ((lift T x).1 z).1 = 1 := by
  have hmap := (unitExtension T).localLifts.map_lift x
  have h3 := ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op ((unitExtension T).localLifts.opens x)))
      (constIsoLC (TopCat.of (ComplexPoint X))).inv_hom_id)
    ((projection T).hom.app _ (lift T x))
  erw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h3
  change _ = (projection T).hom.app _ (lift T x) at h3
  erw [hmap, constIso_hom_one] at h3
  exact (congrFun (congrArg Subtype.val h3) z).symm

/-- The value of the chosen lift at `x`. -/
def vx (x z : ComplexPoint X) (hz : z ∈ (unitExtension T).localLifts.opens x) : ℂˣ :=
  Additive.toMul ((lift T x).1 ⟨z, hz⟩).2

/-- Transition units of the unit extension are ratios of lift values. -/
lemma hev_transitionUnit (x y : ComplexPoint X) (V : Opens (TopCat.of (ComplexPoint X)))
    (hx : V ≤ (unitExtension T).localLifts.opens x) (hy : V ≤ (unitExtension T).localLifts.opens y)
    (z : ComplexPoint X) (hz : z ∈ V) :
    hev (((unitExtension T).transitionUnit x y V hx hy).val :
        (holomorphicRingSheaf X d).obj.obj (op V)) z hz =
      ((vx T x z (hx hz) / vx T y z (hy hz) : ℂˣ) : ℂ) := by
  have h := (unitExtension T).localLifts.transition_spec (unitExtension T).shortExact x y V hx hy
  have h2 := congrArg (fun t : middleSubgroup T V => Additive.toMul (t.1 ⟨z, hz⟩).2) h
  change uev (unitOf ((unitExtension T).localLifts.transition (unitExtension T).shortExact
    x y V hx hy)) z hz = _ at h2
  change ((uev (unitOf ((unitExtension T).localLifts.transition (unitExtension T).shortExact
    x y V hx hy)) z hz : ℂˣ) : ℂ) = _
  rw [h2]
  rfl

/-- The open `Oₓ ⊓ Uᵢ` of the product cover. -/
abbrev popens (p : ComplexPoint X × T.ι) : Opens (TopCat.of (ComplexPoint X)) :=
  (unitExtension T).localLifts.opens p.1 ⊓ T.opens p.2

/-- The chart coordinate `g (b z) i z * vˣ z` of the lift at `x`. -/
def wfun (p : ComplexPoint X × T.ι) : popens T p → ℂˣ :=
  fun z => gunit T (base T z) p.2 z * vx T p.1 z z.2.1

lemma wfun_contMDiffAt (p : ComplexPoint X × T.ι) (z : popens T p) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (fun w : popens T p => (wfun T p w : ℂ)) z := by
  have hg := ((lift T p.1).2 ⟨z.1, z.2.1⟩).2 p.2 z.2.2
  apply ((contMDiffAt_subtype_iff (U := popens T p) (x := z)).mpr hg).congr_of_eventuallyEq
  refine Eventually.of_forall fun w => ?_
  simp only [hcoord, ext_of_mem _ _ _ w.2.1, lift_degree T p.1 ⟨w.1, w.2.1⟩, zpow_one, wfun,
    gunit, vx, Units.val_mul, Units.val_mk0]

/-- The unit `wˣᵢ` on `Oₓ ⊓ Uᵢ`. -/
def wunit (p : ComplexPoint X × T.ι) : ((holomorphicRingSheaf X d).obj.obj (op (popens T p)))ˣ :=
  unitOfFun (wfun T p) (wfun_contMDiffAt T p)

/-- The frames `wˣᵢ • σ i` of `M` on the product cover. -/
def mframe (p : ComplexPoint X × T.ι) : M.val.obj (op (popens T p)) :=
  (wunit T p).val • holRes M inf_le_right (T.gen p.2)

/-- A unit multiple of a generating section generates. -/
lemma holomorphicGenerates_unit_smul {N : SheafOfModules (holomorphicRingSheaf X d)}
    {U : Opens (TopCat.of (ComplexPoint X))} {s : N.val.obj (op U)} (hs : HolomorphicGenerates s)
    (u : ((holomorphicRingSheaf X d).obj.obj (op U))ˣ) :
    HolomorphicGenerates (u.val • s) := by
  intro V h
  have hb := hs V h
  have hfun : (fun r : (holomorphicRingSheaf X d).obj.obj (op V) => r • holRes N h (u.val • s)) =
      (fun r => r • holRes N h s) ∘ (fun r => r * hres h u.val) := by
    funext r
    simp only [Function.comp_apply, mul_smul]
    rw [holRes_smul]
  rw [hfun]
  refine hb.comp ⟨fun a b hab => ?_, fun r => ⟨r * hres h u⁻¹.val, ?_⟩⟩
  · have := congrArg (· * hres h u⁻¹.val) hab
    simpa only [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one] using this
  · simp only [mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

lemma mframe_generates (p : ComplexPoint X × T.ι) : HolomorphicGenerates (mframe T p) :=
  holomorphicGenerates_unit_smul ((T.gen_generates p.2).restrict inf_le_right) (wunit T p)

/-- The canonical frames of the unit extension on the product cover. -/
def eframes : Frames (unitExtension T).sectionSheafOfModules (ComplexPoint X × T.ι) where
  opens := popens T
  covers z := ⟨(z, base T z), (unitExtension T).localLifts.mem_opens z, mem_base T z⟩
  gen p := (unitExtension T).frame p.1 (popens T p) inf_le_left
  generates p := (unitExtension T).holomorphicGenerates_frame p.1 _ inf_le_left

lemma hev_wunit (p : ComplexPoint X × T.ι) (z : ComplexPoint X) (hz : z ∈ popens T p) :
    hev (wunit T p).val z hz = gval T (base T z) p.2 z * (vx T p.1 z hz.1 : ℂ) := rfl

/-- **The two frame families have the same transition functions.** -/
theorem sameTransitions : SameTransitions (eframes T) (mframe T) := by
  intro p q W hp0 hq0 r hr
  have hp : W ≤ popens T p := hp0
  have hq : W ≤ popens T q := hq0
  change r • holRes M hp (mframe T p) = holRes M hq (mframe T q)
  have hpW : W ≤ (unitExtension T).localLifts.opens p.1 := hp.trans inf_le_left
  have hqW : W ≤ (unitExtension T).localLifts.opens q.1 := hq.trans inf_le_left
  -- the coefficient `r` is the transition unit of `E`
  have hr2 : r • (show (unitExtension T).sectionSheafOfModules.val.obj (op W) from
      (unitExtension T).frame p.1 W hpW) = (unitExtension T).frame q.1 W hqW :=
    ((congrArg (fun t : (unitExtension T).sectionSheafOfModules.val.obj (op W) => r • t)
      ((unitExtension T).holRes_frame p.1
      (inf_le_left : popens T p ≤ _) hp)).symm.trans hr).trans
        ((unitExtension T).holRes_frame q.1 (inf_le_left : popens T q ≤ _) hq)
  have hsm := (unitExtension T).smul_frame p.1 q.1 W hpW hqW
  have hr' : r = (((unitExtension T).transitionUnit q.1 p.1 W hqW hpW).val :
      (holomorphicRingSheaf X d).obj.obj (op W)) :=
    ((unitExtension T).holomorphicGenerates_frame p.1 W hpW).bijective.injective
      (hr2.trans hsm.symm)
  -- the `M` side, in terms of `σ q.2`
  have hWpq : W ≤ T.opens p.2 ⊓ T.opens q.2 := le_inf (hp.trans inf_le_right) (hq.trans inf_le_right)
  have hσ := tunit_smul_res T p.2 q.2 hWpq
  unfold mframe
  rw [holRes_smul, holRes_smul, holRes_holRes, holRes_holRes, ← hσ, ← mul_smul, ← mul_smul]
  congr 1
  apply hsec_ext
  intro z hz
  rw [hev_mul, hev_mul, hr', hev_transitionUnit T q.1 p.1 W hqW hpW z hz]
  change _ * hev (wunit T p).val z (hp hz) * hev (tunit T p.2 q.2) z (hWpq hz) =
    hev (wunit T q).val z (hq hz)
  rw [hev_wunit, hev_wunit, ← gval_of_mem T p.2 q.2 z (hWpq hz)]
  have hc := gval_mul T (base T z) p.2 q.2 z (mem_base T z) (hp hz).2 (hq hz).2
  rw [← hc, Units.val_div_eq_div_val]
  have h0 : (vx T p.1 z (hpW hz) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

/-- **`M` is the section sheaf of the unit extension of its trivializing cover.** -/
def sectionIso : M ≅ (unitExtension T).sectionSheafOfModules :=
  ((eframes T).isoOfSameTransitions (mframe T) (sameTransitions T) (mframe_generates T)).symm

end TCover

end HodgeLadder
