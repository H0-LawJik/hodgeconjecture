module

public import HodgeLadder.Cycle.Multiplicative
public import HodgeLadder.Normalization.GermNoReg

/-!
# The transversal product of cycle classes without the regularity hypotheses

Rung `cycle-class-multiplicative-no-reg` (final red team of `cycle-class-multiplicative`,
change F). The checked theorem `cycleComponentSheafClass_cup_of_transversal` assumes, besides the
transversality hypothesis `htr`, that `T(ℂ)` lies off `Z_sing(ℂ)` and `W_sing(ℂ)` (`hxreg`,
`hwreg`). Those hypotheses enter the route only at step 5, where `cycle-class-germ` is applied to
`Z` and `W` at a point `y ∈ T(ℂ)`. This file applies `cycle-class-germ-no-reg`
(`transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted`, the identity on all of the
chart source) instead, and drops `hxreg` and `hwreg`. The conclusion is unchanged:
`[Z] ∪ [W] = [T]` in `H^{2(a+b)}(X; ℚ)`, exact, sign `+`.

The germ lemma also loses its hypothesis `y ∈ U_x`, `y ∈ U_w`, `y ∈ U_t`; the point `y ∈ U_t`
still appears in the localization step, since `TopCat.Presheaf.section_ext` runs over `U_t`.
Every other step (lift, product, forget, Yoneda sign, restriction to small opens, uniqueness) is
the checked lemma of `HodgeLadder.Cycle.Multiplicative`, reused by name.

## Main results

* `HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal_noReg`: the rung.
* `HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal_of_noReg`: the checked theorem
  `cycleComponentSheafClass_cup_of_transversal` recovered from the rung, so that the new statement
  is a strengthening.
* `HodgeLadder.Cycle.germ_transport_eq_of_chart_noReg`: steps 5 and 6 at a point, with no
  regularity hypothesis at the point.
* `HodgeLadder.Cycle.normalization_eq_coclassSection_of_product_noReg`,
  `HodgeLadder.Cycle.eq_supportedInjectiveClass_of_product_noReg`: step 6, localization and
  uniqueness, without `hxreg` and `hwreg`.

## Signs

The same as in `HodgeLadder.Cycle.Multiplicative`: `(−1)^{(2a)(2b)} = 1`, computed in the proof
(`cup_singular_comparison`), and the local `+` of `local-class-product`. `cycle-class-germ-no-reg`
is an identity with no sign or scalar, as is `cycle-class-germ`, so the sign chain is unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace HodgeLadder.Cycle

open HodgeLadder.Cup HodgeLadder.LocalClassProduct HodgeLadder.Normalization
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

section Cycle

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Every open of `X(ℂ)` is paracompact (upstream's `openParacompactSpace`). -/
local instance : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

/-- **Steps 5 and 6, at one point, with no regularity hypothesis at the point.** Let `φ` be a
holomorphic chart of `X(ℂ)` at `y` in which `Z` is `{first a coordinates = 0}` and `W` is
`{next b coordinates = 0}`. If `Φ_T γ` is the relative product of `Φ_Z [Z]` and `Φ_W [W]`, then
the germs at `y` of upstream's transports of `γ` and of `[T]` agree. The proof is that of
`germ_transport_eq_of_chart` with `cycle-class-germ-no-reg`
(`transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted`) in place of
`cycle-class-germ` for each of `Z`, `W`, `T`, so `y` need not lie off `Z_sing`, `W_sing` or
`T_sing`. -/
theorem germ_transport_eq_of_chart_noReg (x w t : X.left) {a b : ℕ} (hx : Order.coheight x = a)
    (hw : Order.coheight w = b) (ht : Order.coheight t = a + b) (hd : a + b ≤ dim X.left)
    (hT : cycleComponentAnalyticClosedSupport X t =
      cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X w)
    (φ : OpenPartialHomeomorph (ComplexPoint X) (Fin (dim X.left) → ℂ))
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hZφ : ∀ z ∈ φ.source,
      z ∈ cycleComponentAnalyticClosedSupport X x ↔ ∀ i : Fin a, φ z ⟨i, by omega⟩ = 0)
    (hWφ : ∀ z ∈ φ.source,
      z ∈ cycleComponentAnalyticClosedSupport X w ↔ ∀ j : Fin b, φ z ⟨a + j, by omega⟩ = 0)
    (y : ComplexPoint X) (hy : y ∈ φ.source)
    (γ : H_[cycleComponentAnalyticClosedSupport X t]^(2 * (a + b))(X; ℚ))
    (hγ : supportedEquivPair X (cycleComponentAnalyticClosedSupport X t) (2 * (a + b)) γ =
      relativeCohomologyMap ℚ (2 * (a + b)) (unionComplIso hT).inv
        (relCup2 (TopCat.of (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X x).compl : Set (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X w).compl : Set (ComplexPoint X))
          (cycleComponentAnalyticClosedSupport X x).compl.isOpen
          (cycleComponentAnalyticClosedSupport X w).compl.isOpen
          (supportedEquivPair X (cycleComponentAnalyticClosedSupport X x) (2 * a)
            (cycleComponentSupportedInjectiveClass X x hx))
          (supportedEquivPair X (cycleComponentAnalyticClosedSupport X w) (2 * b)
            (cycleComponentSupportedInjectiveClass X w hw))
          (2 * (a + b)) (Nat.mul_add 2 a b).symm)) :
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) (2 * (a + b)) ⊤ y
        trivial
        (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X t)
          ⊤ (2 * (a + b))
          (rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X t) (2 * (a + b)) γ)) =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) (2 * (a + b)) ⊤ y
        trivial
        (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X t)
          ⊤ (2 * (a + b))
          (rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X t) (2 * (a + b))
            (cycleComponentSupportedInjectiveClass X t ht))) := by
  -- the three adapted charts, split from `φ` along their normal coordinates
  let kZ : Fin a → Fin (dim X.left) := fun i => ⟨i, by omega⟩
  have hkZ : Function.Injective kZ := fun i j hij =>
    Fin.ext (by have := congrArg Fin.val hij; simpa [kZ] using this)
  let kW : Fin b → Fin (dim X.left) := fun j => ⟨a + j, by omega⟩
  have hkW : Function.Injective kW := fun i j hij =>
    Fin.ext (by have := congrArg Fin.val hij; simp [kW] at this; omega)
  let kT : Fin (a + b) → Fin (dim X.left) := fun k => ⟨k, by omega⟩
  have hkT : Function.Injective kT := fun i j hij =>
    Fin.ext (by have := congrArg Fin.val hij; simpa [kT] using this)
  let eZ := splitChart kZ hkZ φ
  let eW := splitChart kW hkW φ
  let eT := splitChart kT hkT φ
  have sZ : eZ.source = φ.source := splitChart_source kZ hkZ φ
  have sW : eW.source = φ.source := splitChart_source kW hkW φ
  have sT : eT.source = φ.source := splitChart_source kT hkT φ
  have hSZ : ∀ z ∈ eZ.source, z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔
      (eZ z).2 = 0 := fun z hz =>
    (hZφ z (sZ ▸ hz)).trans (funext_iff (f := (eZ z).2) (g := 0)).symm
  have hSW : ∀ z ∈ eW.source, z ∈ (cycleComponentAnalyticClosedSupport X w : Set (ComplexPoint X)) ↔
      (eW z).2 = 0 := fun z hz =>
    (hWφ z (sW ▸ hz)).trans (funext_iff (f := (eW z).2) (g := 0)).symm
  have hST : ∀ z ∈ eT.source, z ∈ (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ↔
      (eT z).2 = 0 := by
    intro z hz
    rw [sT] at hz
    refine ((mem_iff_of_eq_inf Set.univ hT z trivial).trans
      (and_congr (hZφ z hz) (hWφ z hz))).trans ?_
    refine Iff.trans ?_ (funext_iff (f := (eT z).2) (g := 0)).symm
    constructor
    · rintro ⟨h1, h2⟩ k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · exact h1 i
      · exact h2 j
    · intro h
      exact ⟨fun i => h (Fin.castAdd b i), fun j => h (Fin.natAdd a j)⟩
  -- `cycle-class-germ` for `Z`, `W`, `T`
  have hmZ := splitChart_mem_maximalAtlas kZ hkZ hφ
  have hmW := splitChart_mem_maximalAtlas kW hkW hφ
  have hmT := splitChart_mem_maximalAtlas kT hkT hφ
  have hyZ : y ∈ eZ.source := sZ ▸ hy
  have hyW : y ∈ eW.source := sW ▸ hy
  have hyT : y ∈ eT.source := sT ▸ hy
  have gZ := transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted X x hx
    eZ (normalSplit kZ hkZ).symm hmZ hSZ y hyZ
  have gW := transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted X w hw
    eW (normalSplit kW hkW).symm hmW hSW y hyW
  have gT := transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted X t ht
    eT (normalSplit kT hkT).symm hmT hST y hyT
  obtain ⟨VZ, hVZ, hyVZ, eqZ⟩ := gZ
  obtain ⟨VW, hVW, hyVW, eqW⟩ := gW
  obtain ⟨VT, hVT, hyVT, eqT⟩ := gT
  -- restrict all three to `V = VZ ∩ VW ∩ VT`
  let V : Opens (ComplexPoint X) := VZ ⊓ VW ⊓ VT
  have hyV : y ∈ V := ⟨⟨hyVZ, hyVW⟩, hyVT⟩
  have hV1 : (V : Set (ComplexPoint X)) ⊆ VZ := fun _ hz => hz.1.1
  have hV2 : (V : Set (ComplexPoint X)) ⊆ VW := fun _ hz => hz.1.2
  have hV3 : (V : Set (ComplexPoint X)) ⊆ VT := fun _ hz => hz.2
  have eqZ' := restrict_eq_chartNormalProjectionCoclass eZ _ hSZ hV1 hVZ (fun _ _ => trivial) _ eqZ
  have eqW' := restrict_eq_chartNormalProjectionCoclass eW _ hSW hV2 hVW (fun _ _ => trivial) _ eqW
  have eqT' := restrict_eq_chartNormalProjectionCoclass eT _ hST hV3 hVT (fun _ _ => trivial) _ eqT
  -- the product on `V`
  have hprod := transport_restrict_of_supportedEquivPair_eq X hT (V : Set (ComplexPoint X))
    (cycleComponentSupportedInjectiveClass X x hx) (cycleComponentSupportedInjectiveClass X w hw)
    (2 * (a + b)) (Nat.mul_add 2 a b).symm γ hγ
  have h2 := congrArg (relativeCohomologyMap ℚ (2 * (a + b))
      (chartUnionIso (V : Set (ComplexPoint X))
        (mem_iff_of_eq_inf (V : Set (ComplexPoint X)) hT)).inv)
    (congrArg₂ (fun u v => relCup2 (TopCat.of (V : Set (ComplexPoint X)))
      {w' : (V : Set (ComplexPoint X)) |
        w'.1 ∉ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))}
      {w' : (V : Set (ComplexPoint X)) |
        w'.1 ∉ (cycleComponentAnalyticClosedSupport X w : Set (ComplexPoint X))}
      (isOpen_neighborhoodComplement _ _) (isOpen_neighborhoodComplement _ _) u v (2 * (a + b))
      (Nat.mul_add 2 a b).symm) eqZ' eqW')
  have h3 := chartNormalProjectionCoclass_eq_relCup2 eZ eW eT _ _ _ hSZ hSW hST
    (V : Set (ComplexPoint X)) (hV1.trans hVZ) (hV2.trans hVW) (hV3.trans hVT)
    (fun _ _ => rfl) (fun _ _ => rfl) (isOpen_neighborhoodComplement _ _)
    (isOpen_neighborhoodComplement _ _) (mem_iff_of_eq_inf (V : Set (ComplexPoint X)) hT)
  have hchain := hprod.trans (h2.trans (h3.trans eqT'.symm))
  have hg := supportRelativeCohomologyGerm_eq_of_restrict_eq (TopCat.of (ComplexPoint X))
    (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) (2 * (a + b))
    (U := ⊤) (V := ⊤) (W := V) le_top le_top y hyV _ _ hchain
  convert hg using 2

/-- **Step 6, localization, without `hxreg` and `hwreg`.** Under the hypotheses of
`cycleComponentSheafClass_cup_of_transversal_noReg`, a class `γ` with `Φ_T γ` the relative product
of `Φ_Z [Z]` and `Φ_W [W]` has upstream's normalized coclass section as its normalization. As in
`normalization_eq_coclassSection_of_product`: germs determine sections on `U_T`
(`TopCat.Presheaf.section_ext`), both germs vanish off `T`, and on `T` they agree by
`germ_transport_eq_of_chart_noReg`. -/
theorem normalization_eq_coclassSection_of_product_noReg (x w t : X.left) {a b : ℕ}
    (hx : Order.coheight x = a) (hw : Order.coheight w = b) (ht : Order.coheight t = a + b)
    (hd : a + b ≤ dim X.left)
    (hT : cycleComponentAnalyticClosedSupport X t =
      cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X w)
    (htr : ∀ y ∈ (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)),
      ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X),
        y ∈ φ.source ∧ ∀ z ∈ φ.source,
          (z ∈ cycleComponentAnalyticClosedSupport X x ↔ ∀ i : Fin a, φ z ⟨i, by omega⟩ = 0) ∧
          (z ∈ cycleComponentAnalyticClosedSupport X w ↔ ∀ j : Fin b, φ z ⟨a + j, by omega⟩ = 0))
    (γ : H_[cycleComponentAnalyticClosedSupport X t]^(2 * (a + b))(X; ℚ))
    (hγ : supportedEquivPair X (cycleComponentAnalyticClosedSupport X t) (2 * (a + b)) γ =
      relativeCohomologyMap ℚ (2 * (a + b)) (unionComplIso hT).inv
        (relCup2 (TopCat.of (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X x).compl : Set (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X w).compl : Set (ComplexPoint X))
          (cycleComponentAnalyticClosedSupport X x).compl.isOpen
          (cycleComponentAnalyticClosedSupport X w).compl.isOpen
          (supportedEquivPair X (cycleComponentAnalyticClosedSupport X x) (2 * a)
            (cycleComponentSupportedInjectiveClass X x hx))
          (supportedEquivPair X (cycleComponentAnalyticClosedSupport X w) (2 * b)
            (cycleComponentSupportedInjectiveClass X w hw))
          (2 * (a + b)) (Nat.mul_add 2 a b).symm)) :
    (cycleComponentSupportedClassNormalizationIso X t ht).toAddMonoidHom γ =
      cycleComponentSmoothSupportCoclassSection X t ht := by
  refine (normalization_singular X t ht γ).trans
    (Eq.trans ?_ (coclassSection_eq_singular X t ht).symm)
  apply TopCat.Presheaf.section_ext
  intro y hy
  refine (supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
    (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) (2 * (a + b))
    (le_top : cycleComponentSmoothSupportAmbientOpen X t ≤ ⊤) y hy _).trans
      (Eq.trans ?_ (supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) (2 * (a + b))
        (le_top : cycleComponentSmoothSupportAmbientOpen X t ≤ ⊤) y hy _).symm)
  by_cases hyT : y ∈ (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X))
  · obtain ⟨φ, hφ, hyφ, hφZW⟩ := htr y hyT
    have h := germ_transport_eq_of_chart_noReg X x w t hx hw ht hd hT φ hφ
      (fun z hz => (hφZW z hz).1) (fun z hz => (hφZW z hz).2) y hyφ γ hγ
    convert h using 2
  · exact (supportRelativeCohomologyGerm_eq_zero_of_not_mem _ _ _
      (cycleComponentAnalyticClosedSupport X t).isClosed _ y _ hyT _).trans
        (supportRelativeCohomologyGerm_eq_zero_of_not_mem _ _ _
          (cycleComponentAnalyticClosedSupport X t).isClosed _ y _ hyT _).symm

/-- **Step 6, uniqueness, without `hxreg` and `hwreg`.** The class `γ` of
`normalization_eq_coclassSection_of_product_noReg` is upstream's supported class of `T`
(`cycleComponentSupportedInjectiveClass_unique`). -/
theorem eq_supportedInjectiveClass_of_product_noReg (x w t : X.left) {a b : ℕ}
    (hx : Order.coheight x = a) (hw : Order.coheight w = b) (ht : Order.coheight t = a + b)
    (hd : a + b ≤ dim X.left)
    (hT : cycleComponentAnalyticClosedSupport X t =
      cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X w)
    (htr : ∀ y ∈ (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)),
      ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X),
        y ∈ φ.source ∧ ∀ z ∈ φ.source,
          (z ∈ cycleComponentAnalyticClosedSupport X x ↔ ∀ i : Fin a, φ z ⟨i, by omega⟩ = 0) ∧
          (z ∈ cycleComponentAnalyticClosedSupport X w ↔ ∀ j : Fin b, φ z ⟨a + j, by omega⟩ = 0))
    (γ : H_[cycleComponentAnalyticClosedSupport X t]^(2 * (a + b))(X; ℚ))
    (hγ : supportedEquivPair X (cycleComponentAnalyticClosedSupport X t) (2 * (a + b)) γ =
      relativeCohomologyMap ℚ (2 * (a + b)) (unionComplIso hT).inv
        (relCup2 (TopCat.of (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X x).compl : Set (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X w).compl : Set (ComplexPoint X))
          (cycleComponentAnalyticClosedSupport X x).compl.isOpen
          (cycleComponentAnalyticClosedSupport X w).compl.isOpen
          (supportedEquivPair X (cycleComponentAnalyticClosedSupport X x) (2 * a)
            (cycleComponentSupportedInjectiveClass X x hx))
          (supportedEquivPair X (cycleComponentAnalyticClosedSupport X w) (2 * b)
            (cycleComponentSupportedInjectiveClass X w hw))
          (2 * (a + b)) (Nat.mul_add 2 a b).symm)) :
    γ = cycleComponentSupportedInjectiveClass X t ht :=
  cycleComponentSupportedInjectiveClass_unique X t ht γ
    (normalization_eq_coclassSection_of_product_noReg X x w t hx hw ht hd hT htr γ hγ)

end Cycle

/-- **The cycle class map is multiplicative for a transversal intersection, without regularity
hypotheses, sign `+`.** Let `X` be smooth, integral and projective over `ℂ` of dimension `d`,
and `x`, `w`, `t` scheme points of coheights `a`, `b`, `a + b` with reduced closures `Z`, `W`,
`T` such that `T(ℂ) = Z(ℂ) ∩ W(ℂ)` and every point of `T(ℂ)` has a holomorphic chart in which
`Z` is `{first a coordinates = 0}` and `W` is `{next b coordinates = 0}`. Then
`[Z] ∪ [W] = [T]` in `H^{2(a+b)}(X; ℚ)` for upstream's cycle classes and the ladder's Yoneda cup
product. Exact: no sign, no scalar. This is `cycleComponentSheafClass_cup_of_transversal` with
the hypotheses `hxreg` and `hwreg` (`T(ℂ)` off `Z_sing` and `W_sing`) removed; the sign chain is
the same, `(−1)^{(2a)(2b)} = 1` computed below and the local `+` of `local-class-product`.
Conventions (`docs/conventions.md`): row "Transversal product of cycle classes" and the rows
cited there. -/
theorem cycleComponentSheafClass_cup_of_transversal_noReg
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    (x w t : X.left) {a b : ℕ} (hx : Order.coheight x = a) (hw : Order.coheight w = b)
    (ht : Order.coheight t = a + b) (hd : a + b ≤ d)
    (hT : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) =
      (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ∩
        cycleComponentAnalyticClosedSupport X w)
    (htr : ∀ y ∈ (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)),
      ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X), y ∈ φ.source ∧
        ∀ z ∈ φ.source,
          (z ∈ cycleComponentAnalyticClosedSupport X x ↔ ∀ i : Fin a, φ z ⟨i, by omega⟩ = 0) ∧
          (z ∈ cycleComponentAnalyticClosedSupport X w ↔ ∀ j : Fin b, φ z ⟨a + j, by omega⟩ = 0)) :
    cup (cycleComponentSheafClass X x hx) (cycleComponentSheafClass X w hw) (2 * (a + b))
        (by ring) =
      cycleComponentSheafClass X t ht := by
  have : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  obtain rfl := SmoothOfRelativeDimension.dim_eq (f := X.hom) d
  have hT' := closeds_eq_inf_of_coe_eq hT
  obtain ⟨γ, hγ⟩ := (supportedEquivPair X (cycleComponentAnalyticClosedSupport X t)
    (2 * (a + b))).surjective
      (relativeCohomologyMap ℚ (2 * (a + b)) (unionComplIso hT').inv
        (relCup2 (TopCat.of (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X x).compl : Set (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X w).compl : Set (ComplexPoint X))
          (cycleComponentAnalyticClosedSupport X x).compl.isOpen
          (cycleComponentAnalyticClosedSupport X w).compl.isOpen
          (supportedEquivPair X (cycleComponentAnalyticClosedSupport X x) (2 * a)
            (cycleComponentSupportedInjectiveClass X x hx))
          (supportedEquivPair X (cycleComponentAnalyticClosedSupport X w) (2 * b)
            (cycleComponentSupportedInjectiveClass X w hw))
          (2 * (a + b)) (Nat.mul_add 2 a b).symm))
  have hγT := eq_supportedInjectiveClass_of_product_noReg X x w t hx hw ht hd hT' htr γ hγ
  have key := cup_forgetSupport_of_product X hT'
    (cycleComponentSupportedInjectiveClass X x hx) (cycleComponentSupportedInjectiveClass X w hw)
    (2 * (a + b)) (Nat.mul_add 2 a b).symm γ hγ
  -- the sign of `cup_singular_comparison` at `p = 2a`, `q = 2b`, computed
  have hsign : ((-1 : ℤ) ^ (2 * a * (2 * b))) = 1 :=
    Even.neg_one_pow ⟨a * (2 * b), by ring⟩
  apply (rationalCohomologyAddEquivSingularCohomology X (2 * (a + b))).injective
  refine key.trans ?_
  rw [hsign, one_smul, hγT]
  rfl

/-- The checked theorem `cycleComponentSheafClass_cup_of_transversal` follows from
`cycleComponentSheafClass_cup_of_transversal_noReg` by forgetting `hxreg` and `hwreg`: the new
statement is a strengthening, with the same conclusion. -/
theorem cycleComponentSheafClass_cup_of_transversal_of_noReg
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    (x w t : X.left) {a b : ℕ} (hx : Order.coheight x = a) (hw : Order.coheight w = b)
    (ht : Order.coheight t = a + b) (hd : a + b ≤ d)
    (hT : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) =
      (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ∩
        cycleComponentAnalyticClosedSupport X w)
    (_hxreg : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X x)
    (_hwreg : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X w)
    (htr : ∀ y ∈ (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)),
      ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X), y ∈ φ.source ∧
        ∀ z ∈ φ.source,
          (z ∈ cycleComponentAnalyticClosedSupport X x ↔ ∀ i : Fin a, φ z ⟨i, by omega⟩ = 0) ∧
          (z ∈ cycleComponentAnalyticClosedSupport X w ↔ ∀ j : Fin b, φ z ⟨a + j, by omega⟩ = 0)) :
    cup (cycleComponentSheafClass X x hx) (cycleComponentSheafClass X w hw) (2 * (a + b))
        (by ring) =
      cycleComponentSheafClass X t ht :=
  cycleComponentSheafClass_cup_of_transversal_noReg X x w t hx hw ht hd hT htr

/-- Agreement with the checked theorem: `cycleComponentSheafClass_cup_of_transversal_of_noReg`
has the type of `cycleComponentSheafClass_cup_of_transversal`. -/
example : @cycleComponentSheafClass_cup_of_transversal =
    @cycleComponentSheafClass_cup_of_transversal_of_noReg := rfl

end HodgeLadder.Cycle
