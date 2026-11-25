module

public import LefschetzPort.AlgebraicGeometry.HolomorphicSheafGenerators

/-!
# Transition functions of a holomorphic trivializing cover

For a holomorphic trivializing cover `σ` of a sheaf of modules `M` on `X(ℂ)`, the transition unit
`g i j` on `Uᵢ ⊓ Uⱼ` is defined by `σ i = g i j • σ j`. This file records it, its pointwise
values `gval i j z` (extended by `1` off the overlap), holomorphy on the overlap, the cocycle
identity `g i j * g j k = g i k` and nonvanishing. Part of rung `unit-extension-of-invertible`.

## Main definitions

* `HodgeLadder.HolomorphicTrivializingCover.tunit`, `gval`

## Main results

* `gval_mul`, `gval_ne_zero`, `gval_self`, `contMDiffOn_gval`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexPoint
open scoped Manifold ContDiff

namespace HodgeLadder

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance transitionsTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable {M : SheafOfModules (holomorphicRingSheaf X d)} (T : HolomorphicTrivializingCover M)

/-- Restriction of holomorphic functions. -/
abbrev hres {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
    (r : (holomorphicRingSheaf X d).obj.obj (op U)) : (holomorphicRingSheaf X d).obj.obj (op V) :=
  (holomorphicRingSheaf X d).obj.map (homOfLE h).op r

/-- A section of the holomorphic ring sheaf as a holomorphic map. -/
def hmap {U : Opens (TopCat.of (ComplexPoint X))}
    (r : (holomorphicRingSheaf X d).obj.obj (op U)) : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯ := r

/-- Evaluation of a holomorphic function at a point of its domain. -/
abbrev hev {U : Opens (TopCat.of (ComplexPoint X))} (r : (holomorphicRingSheaf X d).obj.obj (op U))
    (z : ComplexPoint X) (hz : z ∈ U) : ℂ :=
  hmap r ⟨z, hz⟩

lemma hev_hres {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
    (r : (holomorphicRingSheaf X d).obj.obj (op U)) (z : ComplexPoint X) (hz : z ∈ V) :
    hev (hres h r) z hz = hev r z (h hz) := rfl

lemma hev_mul {U : Opens (TopCat.of (ComplexPoint X))}
    (r s : (holomorphicRingSheaf X d).obj.obj (op U)) (z : ComplexPoint X) (hz : z ∈ U) :
    hev (r * s) z hz = hev r z hz * hev s z hz := rfl

lemma hev_one {U : Opens (TopCat.of (ComplexPoint X))} (z : ComplexPoint X) (hz : z ∈ U) :
    hev (1 : (holomorphicRingSheaf X d).obj.obj (op U)) z hz = 1 := rfl

lemma hev_ne_zero_of_isUnit {U : Opens (TopCat.of (ComplexPoint X))}
    {r : (holomorphicRingSheaf X d).obj.obj (op U)} (hr : IsUnit r) (z : ComplexPoint X)
    (hz : z ∈ U) : hev r z hz ≠ 0 := by
  obtain ⟨u, rfl⟩ := hr
  intro h0
  have h1 := congrArg (fun t => hev t z hz) u.val_inv
  rw [hev_mul, hev_one, h0, zero_mul] at h1
  exact zero_ne_one h1

namespace TCover

lemma exists_tunit (i j : T.ι) :
    ∃ u : (holomorphicRingSheaf X d).obj.obj (op (T.opens i ⊓ T.opens j)), IsUnit u ∧
      u • holRes M inf_le_right (T.gen j) = holRes M inf_le_left (T.gen i) :=
  ((T.gen_generates j).restrict inf_le_right).exists_isUnit_smul_eq
    ((T.gen_generates i).restrict inf_le_left)

/-- The transition unit: `σ i = tunit i j • σ j` on the overlap. -/
def tunit (i j : T.ι) : (holomorphicRingSheaf X d).obj.obj (op (T.opens i ⊓ T.opens j)) :=
  (exists_tunit T i j).choose

lemma isUnit_tunit (i j : T.ι) : IsUnit (tunit T i j) := (exists_tunit T i j).choose_spec.1

lemma tunit_smul (i j : T.ι) :
    tunit T i j • holRes M inf_le_right (T.gen j) = holRes M inf_le_left (T.gen i) :=
  (exists_tunit T i j).choose_spec.2

/-- The restricted transition identity on any smaller open. -/
lemma tunit_smul_res (i j : T.ι) {W : Opens (TopCat.of (ComplexPoint X))}
    (h : W ≤ T.opens i ⊓ T.opens j) :
    hres h (tunit T i j) • holRes M (h.trans inf_le_right) (T.gen j) =
      holRes M (h.trans inf_le_left) (T.gen i) := by
  have := congrArg (holRes M h) (tunit_smul T i j)
  rwa [holRes_smul, holRes_holRes, holRes_holRes] at this

/-- Two functions with the same multiple of a frame agree. -/
lemma eq_of_smul_gen (k : T.ι) {W : Opens (TopCat.of (ComplexPoint X))} (h : W ≤ T.opens k)
    {r s : (holomorphicRingSheaf X d).obj.obj (op W)}
    (hrs : r • holRes M h (T.gen k) = s • holRes M h (T.gen k)) : r = s :=
  (T.gen_generates k).smul_left_injective h hrs

/-- Pointwise transition values, extended by `1` off the overlap. -/
def gval (i j : T.ι) (z : ComplexPoint X) : ℂ := by
  classical
  exact if hz : z ∈ T.opens i ⊓ T.opens j then hev (tunit T i j) z hz else 1

lemma gval_of_mem (i j : T.ι) (z : ComplexPoint X) (hz : z ∈ T.opens i ⊓ T.opens j) :
    gval T i j z = hev (tunit T i j) z hz := dif_pos hz

lemma gval_ne_zero (i j : T.ι) (z : ComplexPoint X) : gval T i j z ≠ 0 := by
  unfold gval
  split_ifs with hz
  · exact hev_ne_zero_of_isUnit (isUnit_tunit T i j) z hz
  · exact one_ne_zero

/-- The cocycle identity on triple overlaps. -/
lemma gval_mul (i j k : T.ι) (z : ComplexPoint X) (hi : z ∈ T.opens i) (hj : z ∈ T.opens j)
    (hk : z ∈ T.opens k) : gval T i j z * gval T j k z = gval T i k z := by
  let W := T.opens i ⊓ T.opens j ⊓ T.opens k
  have hWij : W ≤ T.opens i ⊓ T.opens j := inf_le_left
  have hWjk : W ≤ T.opens j ⊓ T.opens k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hWik : W ≤ T.opens i ⊓ T.opens k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hWk : W ≤ T.opens k := inf_le_right
  have key : hres hWij (tunit T i j) * hres hWjk (tunit T j k) = hres hWik (tunit T i k) := by
    apply eq_of_smul_gen T k hWk
    rw [mul_smul, tunit_smul_res T j k hWjk, tunit_smul_res T i k hWik]
    exact tunit_smul_res T i j hWij
  have hz : z ∈ W := ⟨⟨hi, hj⟩, hk⟩
  have := congrArg (fun t => hev t z hz) key
  rw [gval_of_mem T i j z ⟨hi, hj⟩, gval_of_mem T j k z ⟨hj, hk⟩, gval_of_mem T i k z ⟨hi, hk⟩]
  exact this

lemma gval_self (i : T.ι) (z : ComplexPoint X) : gval T i i z = 1 := by
  by_cases hz : z ∈ T.opens i
  · have h := gval_mul T i i i z hz hz hz
    have h0 := gval_ne_zero T i i z
    exact (mul_eq_left₀ h0).mp h
  · rw [gval, dif_neg (fun h => hz h.1)]

/-- Transition values are holomorphic on the overlap. -/
theorem contMDiffOn_gval (i j : T.ι) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (gval T i j) (↑(T.opens i) ∩ ↑(T.opens j)) := by
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff (U := T.opens i ⊓ T.opens j) (x := ⟨z, hz⟩)).mp
  have hfun : (fun w : ↥(T.opens i ⊓ T.opens j) => gval T i j w) =
      hmap (tunit T i j) := by
    funext w
    exact gval_of_mem T i j w w.property
  rw [hfun]
  exact (ContMDiffMap.contMDiff (hmap (tunit T i j))).contMDiffAt

end TCover

end HodgeLadder
