module

public import HodgeLadder.Tests.ProjectivePlanePoint
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf
public import Other.AlgebraicGeometry.ComplexPoint.LocalOrientation
public import Other.AlgebraicTopology.Singular.EmptySubspace
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# A class of `H₄(ℙ²(ℂ); ℚ)` restricting to the complex local orientation

Rung `p2-fundamental-class` (kind foundation). Some `μ ∈ H₄(ℙ²(ℂ); ℚ)` maps to upstream's
`complexLocalOrientation projectivePlane 2 [0 : 0 : 1]` in `H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ pt; ℚ)`. This is the
hypothesis `hμ` of `planeDegree_eq_eval_of_restrict` (rung `cycle-class-sign-test-p2`) and the
existence half of the literature's one-point characterization of the fundamental class `[ℙ²]`;
uniqueness is `existsUnique_restrict_complexLocalOrientation` in
`HodgeLadder.Tests.ProjectivePlaneFundamentalDegree`.

Route, all in degree three and four:

1. `Hˢʰ³(V; ℚ) = 0` for `V = ℙ²(ℂ) ∖ pt` (`subsingleton_H'_three_compl_planeOrigin`, rung
   `p2-point-class-nonzero`).
2. Upstream's `relH ℚ_X n (V ⊓ (X ∖ ⊤) ≤ V)` injects into `Hˢʰⁿ(V; ℚ)`, since `V ⊓ (X ∖ ⊤) = ⊥`
   (upstream's `relH.forget_injective_of_eq_bot`).
3. Upstream's injective supported-sections model at `V` (`relHAddEquivSupportedSectionsHomology`,
   ambient injective resolution of `ℚ`) followed by upstream's transport
   `complexSupportInjectiveSectionCohomologyEquiv X ⊤ V n` identifies that group with singular
   `Hⁿ(V, V ∖ ⊤; ℚ)`. The support `⊤` makes the second space empty; the transport uses upstream's
   `openParacompactSpace` internally.
4. Universal coefficients over `ℚ` (`relativeCohomologyEquivDualHomology`) and
   `Module.subsingleton_dual_iff`: a `ℚ`-vector space with zero dual is zero, so
   `Hₙ(V, V ∖ ⊤; ℚ) = 0`.
5. For an empty second space the projection `Hₙ(V) → Hₙ(V, ∅)` is bijective (upstream's
   `homologyEmptySubspaceIso`), and `V` as a set is `{pt}ᶜ`, so `H₃({pt}ᶜ; ℚ) = 0`
   (`subsingleton_homology_three_compl_planeOrigin`).
6. The homology sequence of the pair `(ℙ²(ℂ), {pt}ᶜ)`, from upstream's short exact sequence of
   singular chains (`relativeChainShortComplex_shortExact`) and Mathlib's
   `ShortComplex.ShortExact.homology_exact₃`: `H₄(ℙ²) → H₄(ℙ², {pt}ᶜ) → H₃({pt}ᶜ)` is exact, so the
   first map is onto (`planeOrigin_relativeHomologyProjection_surjective`).

No sign or normalization enters: every step is a vanishing statement or an equivalence used only to
transport vanishing. The class `μ` is a preimage, chosen by `Exists`; its image is upstream's local
orientation exactly. Reading `μ` as the fundamental class of the complex orientation uses that
`complexLocalOrientation` at the point is the complex local generator (row "Complex orientation of
ℂ^p" of `docs/conventions.md`, pinned); no statement here can detect a fault there.

## Main results

* `HodgeLadder.Tests.exists_restrict_complexLocalOrientation`: the rung.
* `HodgeLadder.Tests.planeOrigin_relativeHomologyProjection_surjective`:
  `H₄(ℙ²(ℂ); ℚ) → H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ pt; ℚ)` is onto.
* `HodgeLadder.Tests.subsingleton_homology_three_compl_planeOrigin`: `H₃(ℙ²(ℂ) ∖ pt; ℚ) = 0`.
* `HodgeLadder.Tests.subsingleton_homology_compl_planeOrigin_of_H'`: singular `Hₙ` of the
  complement vanishes when sheaf `Hⁿ` does, in every degree.
* `HodgeLadder.Tests.relativeHomologyProjection_surjective_of_subsingleton`,
  `relativeHomologyProjection_injective_of_subsingleton`: the two ends of the homology sequence of
  a pair, for any pair.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology TopologicalSpace AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLadder.Tests

/-! ### The homology sequence of a pair -/

/-- For a pair `(X, A)`, `Hₙ₊₁(X; ℚ) → Hₙ₊₁(X, A; ℚ)` is onto when `Hₙ(A; ℚ) = 0`: exactness of
`Hₙ₊₁(X) → Hₙ₊₁(X, A) → Hₙ(A)` (Mathlib's `homology_exact₃` on upstream's short exact sequence of
singular chains). -/
theorem relativeHomologyProjection_surjective_of_subsingleton (P : TopPair.{0}) (n : ℕ)
    (h : Subsingleton (Homology ℚ P.snd n)) :
    Function.Surjective (relativeHomologyProjection ℚ P (n + 1)).hom := by
  have hS := relativeChainShortComplex_shortExact ℚ P
  have hδ : hS.δ (n + 1) n (by simp) = 0 := by
    ext x
    exact Subsingleton.elim (α := Homology ℚ P.snd n) _ _
  exact (ModuleCat.epi_iff_surjective _).mp ((hS.homology_exact₃ (n + 1) n (by simp)).epi_f hδ)

/-- For a pair `(X, A)`, `Hₙ(X; ℚ) → Hₙ(X, A; ℚ)` is injective when `Hₙ(A; ℚ) = 0`: exactness of
`Hₙ(A) → Hₙ(X) → Hₙ(X, A)` (Mathlib's `homology_exact₂`). -/
theorem relativeHomologyProjection_injective_of_subsingleton (P : TopPair.{0}) (n : ℕ)
    (h : Subsingleton (Homology ℚ P.snd n)) :
    Function.Injective (relativeHomologyProjection ℚ P n).hom := by
  have hS := relativeChainShortComplex_shortExact ℚ P
  have hz : IsZero ((relativeChainShortComplex ℚ P).X₁.homology n) :=
    @ModuleCat.isZero_of_subsingleton _ _ _ h
  have hf : HomologicalComplex.homologyMap (relativeChainShortComplex ℚ P).f n = 0 :=
    hz.eq_of_src _ _
  exact (ModuleCat.mono_iff_injective _).mp ((hS.homology_exact₂ n).mono_g hf)

/-- For `A = ∅` the projection `Hₙ(X; ℚ) → Hₙ(X, A; ℚ)` is bijective (upstream's
`homologyEmptySubspaceIso`, after rewriting `A` to `∅`). -/
theorem relativeHomologyProjection_bijective_of_eq_empty {Y : TopCat.{0}} (A : Set Y)
    (hA : A = ∅) (n : ℕ) :
    Function.Bijective (relativeHomologyProjection ℚ (TopPair.ofSubset A) n).hom := by
  subst hA
  exact (ConcreteCategory.isIso_iff_bijective _).mp (homologyEmptySubspaceIso ℚ Y n).isIso_hom

/-! ### From sheaf cohomology of the complement to its singular homology -/

/-- The open `ℙ²(ℂ) ∖ [0 : 0 : 1]`. -/
abbrev planeOriginCompl : Opens (ComplexPoint projectivePlane) :=
  (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin).compl

/-- Upstream's `relH ℚ_X n (V ⊓ (X ∖ ⊤) ≤ V)` on `V = ℙ²(ℂ) ∖ pt` vanishes when sheaf
`Hⁿ(V; ℚ)` does: its second open is empty, so forgetting it is injective. -/
theorem subsingleton_relH_compl_planeOrigin (n : ℕ)
    (h : Subsingleton (Sheaf.H' planeConst n planeOriginCompl)) :
    Subsingleton (CategoryTheory.Sheaf.relH planeConst n
      (homOfLE (inf_le_left : planeOriginCompl ⊓
        (⊤ : Closeds (ComplexPoint projectivePlane)).compl ≤ planeOriginCompl))) := by
  have hW : planeOriginCompl ⊓ (⊤ : Closeds (ComplexPoint projectivePlane)).compl = ⊥ := by
    ext x; simp
  exact ⟨fun _ _ => TopCat.Sheaf.relH.forget_injective_of_eq_bot _ _ _ hW _
    (Subsingleton.elim _ _)⟩

/-- Singular `Hⁿ(V, V ∖ ⊤; ℚ)` on `V = ℙ²(ℂ) ∖ pt` vanishes when sheaf `Hⁿ(V; ℚ)` does, through
upstream's injective supported-sections model at `V` and upstream's transport
`complexSupportInjectiveSectionCohomologyEquiv projectivePlane ⊤ V n`. -/
theorem subsingleton_relativeCohomology_compl_planeOrigin (n : ℕ)
    (h : Subsingleton (Sheaf.H' planeConst n planeOriginCompl)) :
    Subsingleton (RelativeCohomology ℚ (neighborhoodSupportComplementPair
      (planeOriginCompl : Set (ComplexPoint projectivePlane))
      ((⊤ : Closeds (ComplexPoint projectivePlane)) : Set (ComplexPoint projectivePlane))) n) := by
  have := subsingleton_relH_compl_planeOrigin n h
  exact ((@TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
    (TopCat.of (ComplexPoint projectivePlane)) (⊤ : Closeds (ComplexPoint projectivePlane)).compl
    planeOriginCompl (planeOriginCompl ⊓ (⊤ : Closeds (ComplexPoint projectivePlane)).compl) rfl
    inferInstance _ (ambientRationalInjectiveComplex projectivePlane)
    (ambientRationalInjectiveComplex_isKInjective projectivePlane)
    (ambientRationalInjectiveSingleAugmentation projectivePlane)
    (ambientRationalInjectiveSingleAugmentation_quasiIso projectivePlane) n).trans
    (complexSupportInjectiveSectionCohomologyEquiv projectivePlane ⊤ planeOriginCompl
      n)).symm.toEquiv.subsingleton

/-- **Singular `Hₙ` of the complement from sheaf `Hⁿ`**: if sheaf `Hⁿ(ℙ²(ℂ) ∖ pt; ℚ) = 0` then
singular `Hₙ(ℙ²(ℂ) ∖ pt; ℚ) = 0`, by universal coefficients over `ℚ`. -/
theorem subsingleton_homology_compl_planeOrigin_of_H' (n : ℕ)
    (h : Subsingleton (Sheaf.H' planeConst n planeOriginCompl)) :
    Subsingleton (Homology ℚ
      (TopCat.of ({planeOriginPoint}ᶜ : Set (ComplexPoint projectivePlane))) n) := by
  have := subsingleton_relativeCohomology_compl_planeOrigin n h
  have hdual : Subsingleton (Module.Dual ℚ (RelativeHomology ℚ (neighborhoodSupportComplementPair
      (planeOriginCompl : Set (ComplexPoint projectivePlane))
      ((⊤ : Closeds (ComplexPoint projectivePlane)) : Set (ComplexPoint projectivePlane))) n)) :=
    (relativeCohomologyEquivDualHomology ℚ _ n).symm.toEquiv.subsingleton
  rw [Module.subsingleton_dual_iff] at hdual
  have hA : {w : (planeOriginCompl : Set (ComplexPoint projectivePlane)) |
      w.1 ∉ ((⊤ : Closeds (ComplexPoint projectivePlane)) : Set (ComplexPoint projectivePlane))} =
      ∅ := by
    ext w; simp
  have hV : Subsingleton (Homology ℚ
      (TopCat.of (planeOriginCompl : Set (ComplexPoint projectivePlane))) n) :=
    (Equiv.ofBijective _ (relativeHomologyProjection_bijective_of_eq_empty
      (Y := TopCat.of (planeOriginCompl : Set (ComplexPoint projectivePlane))) _ hA n)).subsingleton
  have key : ∀ (A B : Set (ComplexPoint projectivePlane)), A = B →
      Subsingleton (Homology ℚ (TopCat.of A) n) → Subsingleton (Homology ℚ (TopCat.of B) n) := by
    rintro A B rfl hA
    exact hA
  refine key _ _ ?_ hV
  change ((cycleComponentAnalyticClosedSupport projectivePlane planeOrigin :
    Set (ComplexPoint projectivePlane)))ᶜ = _
  rw [planeOrigin_support_eq_singleton]

/-- **`H₃(ℙ²(ℂ) ∖ [0 : 0 : 1]; ℚ) = 0`**, singular homology of the complement of the point. -/
theorem subsingleton_homology_three_compl_planeOrigin :
    Subsingleton (Homology ℚ
      (TopCat.of ({planeOriginPoint}ᶜ : Set (ComplexPoint projectivePlane))) 3) :=
  subsingleton_homology_compl_planeOrigin_of_H' 3 subsingleton_H'_three_compl_planeOrigin

/-! ### The fundamental class -/

/-- **`H₄(ℙ²(ℂ); ℚ) → H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ [0 : 0 : 1]; ℚ)` is onto**, from
`H₃(ℙ²(ℂ) ∖ pt; ℚ) = 0` and the homology sequence of the pair. -/
theorem planeOrigin_relativeHomologyProjection_surjective :
    Function.Surjective
      (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom :=
  relativeHomologyProjection_surjective_of_subsingleton (pointComplementPair planeOriginPoint) 3
    subsingleton_homology_three_compl_planeOrigin

/-- **A class of `H₄(ℙ²(ℂ); ℚ)` restricting to the complex local orientation** at
`[0 : 0 : 1]`: some `μ` maps to upstream's `complexLocalOrientation projectivePlane 2 pt` in
`H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ pt; ℚ)`, exactly. This is the hypothesis of `planeDegree_eq_eval_of_restrict`. -/
theorem exists_restrict_complexLocalOrientation :
    ∃ μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2),
      (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
        complexLocalOrientation projectivePlane 2 planeOriginPoint :=
  planeOrigin_relativeHomologyProjection_surjective _

end HodgeLadder.Tests
