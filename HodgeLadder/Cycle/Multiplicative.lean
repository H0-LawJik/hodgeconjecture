module

public import HodgeLadder.Local.ClassProduct
public import HodgeLadder.Cup.SupportedPairForget
public import HodgeLadder.Cup.CupSingular
public import HodgeLadder.Normalization.Germ
public import Other.AlgebraicGeometry.Cycle.FundamentalClass

/-!
# The cycle class map is multiplicative for a transversal intersection

Rung `cycle-class-multiplicative` (front `cup`, decisions 0009 and 0010; the front's kill
criterion). For `X` smooth, integral and projective over `ℂ`, integral subvarieties `Z`, `W`, `T`
of codimensions `a`, `b`, `a + b` with `T(ℂ) = Z(ℂ) ∩ W(ℂ)`, meeting transversally along `T` in
holomorphic charts and with `T(ℂ)` off `Z_sing ∪ W_sing`:
`[Z] ∪ [W] = [T]` in `H^{2(a+b)}(X; ℚ)`, for upstream's `cycleComponentSheafClass` and the
ladder's Yoneda cup `HodgeLadder.Cup.cup`. Exact, sign `+`.

Notation: `Φ_S = supportedEquivPair X S` (supported classes to `H^n(X, X ∖ S; ℚ)`), `Ψ` upstream's
sheaf–singular comparison, `𝒯 α` upstream's transport
`complexSupportInjectiveSectionCohomologyEquiv X S ⊤` of `α`, `N_T` upstream's normalization iso.

## Route

1. Lift: `[Z] = forgetSupport α_Z`, and `forgetRel (Φ_Z α_Z) = Ψ [Z]`
   (`forgetRel_supportedEquivPair`, `supported-pair-forget`). No sign.
2. Product: `relCup2 (Φ_Z α_Z) (Φ_W α_W)` on `(X, (X ∖ Z) ∪ (X ∖ W))`, read on `(X, X ∖ T)` along
   `unionComplIso` (the identity of `X`). By surjectivity of `Φ_T` it is `Φ_T γ` for some `γ`.
3. Forget: `forgetRel ∘ relCup2 = cupSing ∘ (forgetRel × forgetRel)` (`forgetRel_relCup2`), no
   sign; `forgetRel_unionComplIso`, no sign.
4. Yoneda: `Ψ (x ∪ y) = (−1)^{pq} cupSing (Ψ x) (Ψ y)` (`cup_singular_comparison'`), here
   `p = 2a`, `q = 2b`, so the sign is `1`. Together: `cup_forgetSupport_of_product`.
5. Germs: at `y ∈ T(ℂ)`, split the chart of the transversality hypothesis into adapted charts of
   `Z`, `W`, `T` (`splitChart`, a coordinate permutation) and apply `cycle-class-germ`
   (`transport_supportedClass_eq_chartNormalProjectionCoclass`) three times.
6. Local product and uniqueness: restriction of `𝒯 γ` to a small `V` is `relCup2` of the restricted
   transports (`transport_restrict_of_supportedEquivPair_eq`, from `relCup2_restrict` and the glue
   lemmas), which is the chart coclass of `T` by `chartNormalProjectionCoclass_eq_relCup2`
   (`local-class-product`, sign `+`), hence the germ of `𝒯 [T]` (`germ_transport_eq_of_chart`).
   Off `T` both germs vanish. Germs determine sections (`TopCat.Presheaf.section_ext`), so
   `N_T γ` is upstream's normalized coclass section (`normalization_eq_coclassSection_of_product`,
   through `normalization-singular`), and `γ = [T]_supp` by upstream's
   `cycleComponentSupportedInjectiveClass_unique`.
7. `Ψ` is injective.

## Main definitions

* `HodgeLadder.Cycle.unionComplIso`: `(X, (X ∖ Z) ∪ (X ∖ W)) ≅ (X, X ∖ T)` for `T = Z ⊓ W`, the
  identity of `X`.
* `HodgeLadder.Cycle.normalSplit`, `HodgeLadder.Cycle.splitChart`: a chart into `ℂ^d` split as
  tangential coordinates times the normal coordinates `k 0, …, k (c − 1)`.

## Main results

* `HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal`: the rung.
* `HodgeLadder.Cycle.cup_forgetSupport_of_product`: steps 1 to 4, with the general sign
  `(−1)^{pq}`.
* `HodgeLadder.Cycle.transport_restrict_of_supportedEquivPair_eq`: step 6, restriction.
* `HodgeLadder.Cycle.germ_transport_eq_of_chart`: steps 5 and 6 at a point.
* `HodgeLadder.Cycle.normalization_eq_coclassSection_of_product`,
  `HodgeLadder.Cycle.eq_supportedInjectiveClass_of_product`: step 6, localization and uniqueness.
* Glue: `neighborhoodSupportInclusionPairMap_comp_ofSubsetIsoNeighborhoodTop_inv`,
  `restrictToNeighborhood_comp_ofSubsetIsoNeighborhoodTop_hom`, `unionComplIso_fst_apply`,
  `mem_iff_of_eq_inf`, `unionComplIso_restrict`, `forgetRel_unionComplIso`,
  `restrict_eq_chartNormalProjectionCoclass`, `restrict_supportedEquivPair`,
  `splitChart_mem_maximalAtlas`, `closeds_eq_inf_of_coe_eq`.

## Signs

Every sign on the route, with its source: `(−1)^{(2a)(2b)} = 1` (`cup_singular_comparison`, row
"Sheaf–singular comparison Ψ" of `docs/conventions.md`); the local product `+`
(`local-class-product`, computed: the pairing of the model product with the orientation class is
`1`); every other map is a pullback along a map of pairs that is the identity on points, or an
upstream equivalence already in a checked statement. The chart splitting is a coordinate
permutation with no conjugation, and `cycle-class-germ` holds for every holomorphic adapted chart.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace HodgeLadder.Cycle

open HodgeLadder.Cup HodgeLadder.LocalClassProduct HodgeLadder.Normalization
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

section Glue

variable {Y : Type} [TopologicalSpace Y]

/-- Upstream's restriction from `(⊤, ⊤ ∖ Z)` to `(V, V ∖ Z)`, followed by the inverse of
`ofSubsetIsoNeighborhoodTop Z`, is the ladder's `restrictToNeighborhood V Z`. Identity on points. -/
theorem neighborhoodSupportInclusionPairMap_comp_ofSubsetIsoNeighborhoodTop_inv
    (V : Set Y) (Z : Closeds Y) :
    neighborhoodSupportInclusionPairMap (W := V) (V := ((⊤ : Opens Y) : Set Y))
        (fun _ _ => trivial) (Z : Set Y) ≫ (ofSubsetIsoNeighborhoodTop Z).inv =
      restrictToNeighborhood V Z := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext <;> rfl

/-- `restrictToNeighborhood V Z` followed by `ofSubsetIsoNeighborhoodTop Z` is upstream's
restriction from `(⊤, ⊤ ∖ Z)` to `(V, V ∖ Z)`. Identity on points. -/
theorem restrictToNeighborhood_comp_ofSubsetIsoNeighborhoodTop_hom
    (V : Set Y) (Z : Closeds Y) :
    restrictToNeighborhood V Z ≫ (ofSubsetIsoNeighborhoodTop Z).hom =
      neighborhoodSupportInclusionPairMap (W := V) (V := ((⊤ : Opens Y) : Set Y))
        (fun _ _ => trivial) (Z : Set Y) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext <;> rfl

/-- `(Y, (Y ∖ Z) ∪ (Y ∖ W)) ≅ (Y, Y ∖ T)` for `T = Z ⊓ W`, the identity of `Y`. -/
def unionComplIso {Z W T : Closeds Y} (hT : T = Z ⊓ W) :
    TopPair.ofSubset (X := TopCat.of Y) ((Z.compl : Set Y) ∪ (W.compl : Set Y)) ≅
      TopPair.ofSubset (X := TopCat.of Y) (T.compl : Set Y) :=
  TopPair.isoOfSubset (Homeomorph.refl Y) (fun y => by subst hT; simp [Closeds.compl]; tauto)

/-- `unionComplIso` is the identity on points. -/
theorem unionComplIso_fst_apply {Z W T : Closeds Y} (hT : T = Z ⊓ W) (y : Y) :
    TopPair.Hom.fst (unionComplIso hT).hom y = y :=
  rfl

/-- `T = Z ⊓ W` gives `y ∈ T ↔ y ∈ Z ∧ y ∈ W` on every subset, the hypothesis of
`chartUnionIso`. -/
theorem mem_iff_of_eq_inf (V : Set Y) {Z W T : Closeds Y} (hT : T = Z ⊓ W) :
    ∀ y ∈ V, y ∈ (T : Set Y) ↔ y ∈ (Z : Set Y) ∧ y ∈ (W : Set Y) := by
  subst hT; exact fun _ _ => Iff.rfl

/-- Restricting to `V` commutes with `unionComplIso`: both routes from `(V, V ∖ T)` to
`(Y, (Y ∖ Z) ∪ (Y ∖ W))` are the inclusion of `V`. -/
theorem unionComplIso_restrict (V : Set Y) {Z W T : Closeds Y} (hT : T = Z ⊓ W) :
    restrictToNeighborhood V T ≫ (unionComplIso hT).inv =
      (chartUnionIso V (mem_iff_of_eq_inf V hT)).inv ≫
        TopPair.ofSubsetHom (subsetInclusion V)
          (HodgeLadder.Relative.triadMap_mem_union (subsetInclusion V)
            (mem_compl_of_neighborhood V Z) (mem_compl_of_neighborhood V W)) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the subspace across `unionComplIso`: no sign, the map is the identity of `Y`. -/
theorem forgetRel_unionComplIso {Z W T : Closeds Y} (hT : T = Z ⊓ W) (n : ℕ)
    (z : RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of Y) ((Z.compl : Set Y) ∪ (W.compl : Set Y))) n) :
    forgetRel (TopPair.ofSubset (X := TopCat.of Y) (T.compl : Set Y)) n
        (relativeCohomologyMap ℚ n (unionComplIso hT).inv z) =
      forgetRel (TopPair.ofSubset (X := TopCat.of Y) ((Z.compl : Set Y) ∪ (W.compl : Set Y))) n
        z := by
  rw [forgetRel_relativeCohomologyMap]
  have h1 : TopPair.Hom.fst (unionComplIso hT).inv = 𝟙 (TopCat.of Y) := by ext; rfl
  have h : fstChainMap (unionComplIso hT).inv = 𝟙 _ := by
    rw [fstChainMap, h1]; exact CategoryTheory.Functor.map_id _ _
  rw [h]
  erw [HomologicalComplex.linearDualMap_id, HomologicalComplex.homologyMap_id]
  rfl

/-- A chart identity on `V'` restricts to every `V ⊆ V'` (upstream's
`chartNormalProjectionCoclass_restrict`). -/
theorem restrict_eq_chartNormalProjectionCoclass {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c : ℕ} (e : OpenPartialHomeomorph Y (E × (Fin c → ℂ))) (S : Set Y)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) {V V' B : Set Y} (hVV' : V ⊆ V')
    (hV' : V' ⊆ e.source) (hV'B : V' ⊆ B)
    (z : RelativeCohomology ℚ (neighborhoodSupportComplementPair B S) (2 * c))
    (h : relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap hV'B S) z =
      chartNormalProjectionCoclass E c e S hS V' hV') :
    relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap (hVV'.trans hV'B) S) z =
      chartNormalProjectionCoclass E c e S hS V (hVV'.trans hV') := by
  rw [← neighborhoodSupportInclusionPairMap_comp hVV' hV'B, relativeCohomologyMap_comp]
  change relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap hVV' S)
    (relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap hV'B S) z) = _
  rw [h, chartNormalProjectionCoclass_restrict]

end Glue


section Split

variable {c d : ℕ} (k : Fin c → Fin d) (hk : Function.Injective k)

/-- The tangential index set of a splitting of `Fin d` along an injection `k : Fin c → Fin d`. -/
abbrev TangIdx := {i : Fin d // i ∉ Set.range k}

/-- `Fin d` as the tangential indices followed by the normal indices `Fin c` (through `k`). -/
def splitIndexEquiv : TangIdx k ⊕ Fin c ≃ Fin d :=
  (Equiv.sumComm _ _).trans
    ((Equiv.sumCongr (Equiv.ofInjective k hk) (Equiv.refl _)).trans
      (Equiv.sumCompl (· ∈ Set.range k)))

/-- The coordinate splitting `ℂ^d ≃ ℂ^{tangential} × ℂ^c`, whose normal factor reads the
coordinates `k 0, …, k (c − 1)` in this order. A coordinate permutation: no conjugation. -/
def normalSplit : (Fin d → ℂ) ≃L[ℂ] ((TangIdx k → ℂ) × (Fin c → ℂ)) :=
  ((LinearEquiv.funCongrLeft ℂ ℂ (splitIndexEquiv k hk)).trans
    (LinearEquiv.sumArrowLequivProdArrow (TangIdx k) (Fin c) ℂ ℂ)).toContinuousLinearEquiv

/-- The normal factor of `normalSplit` reads the coordinates through `k`. -/
theorem normalSplit_apply_snd (v : Fin d → ℂ) (j : Fin c) :
    (normalSplit k hk v).2 j = v (k j) :=
  rfl

/-- A chart `φ` of `M` into `ℂ^d`, split so that its normal coordinate reads the coordinates
`k 0, …, k (c − 1)` of `φ`. -/
def splitChart {M : Type} [TopologicalSpace M] (φ : OpenPartialHomeomorph M (Fin d → ℂ)) :
    OpenPartialHomeomorph M ((TangIdx k → ℂ) × (Fin c → ℂ)) :=
  φ.trans (normalSplit k hk).toHomeomorph.toOpenPartialHomeomorph

/-- The split chart has the source of `φ`. -/
@[simp] theorem splitChart_source {M : Type} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (Fin d → ℂ)) : (splitChart k hk φ).source = φ.source := by
  simp [splitChart]

/-- The normal coordinate of the split chart reads the coordinates of `φ` through `k`. -/
theorem splitChart_apply_snd {M : Type} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (Fin d → ℂ)) (z : M) (j : Fin c) :
    (splitChart k hk φ z).2 j = φ z (k j) :=
  rfl

/-- The split chart followed by the inverse splitting is in the maximal atlas when `φ` is. -/
theorem splitChart_mem_maximalAtlas {M : Type} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℂ) M]
    {φ : OpenPartialHomeomorph M (Fin d → ℂ)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω M) :
    (splitChart k hk φ).trans (normalSplit k hk).symm.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω M := by
  apply StructureGroupoid.mem_maximalAtlas_of_eqOnSource (e := φ)
  · constructor
    · simp [splitChart]
    · intro z _
      simp [splitChart]
  · exact hφ

end Split

section Product

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Every open of `X(ℂ)` is paracompact (upstream's `openParacompactSpace`). -/
local instance : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

variable {Z W T : Closeds (ComplexPoint X)} (hT : T = Z ⊓ W)

/-- Composition of pullbacks, applied. -/
theorem relativeCohomologyMap_apply_apply {P Q R : TopPair.{0}} (f : P ⟶ Q) (g : Q ⟶ R) (n : ℕ)
    (x : RelativeCohomology ℚ R n) :
    relativeCohomologyMap ℚ n f (relativeCohomologyMap ℚ n g x) =
      relativeCohomologyMap ℚ n (f ≫ g) x := by
  rw [relativeCohomologyMap_comp]; rfl

/-- Restricting `Φ_Z α` from `(X, X ∖ Z)` to `(V, V ∖ Z)` is restricting upstream's transport of
`α` from `(⊤, ⊤ ∖ Z)`. No sign: `supportedEquivPair_eq_transport` and pair maps that are the
identity on points. -/
theorem restrict_supportedEquivPair (V : Set (ComplexPoint X)) (S : Closeds (ComplexPoint X))
    (n : ℕ) (α : H_[S]^n(X; ℚ)) :
    relativeCohomologyMap ℚ n (restrictToNeighborhood V S) (supportedEquivPair X S n α) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := V)
          (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
          (S : Set (ComplexPoint X)))
        (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n
          (rationalSupportAddEquivSupportedInjectiveHomology X S n α)) := by
  refine (congrArg (relativeCohomologyMap ℚ n (restrictToNeighborhood V S))
    (supportedEquivPair_eq_transport X S n α)).trans ?_
  rw [relativeCohomologyMap_apply_apply,
    restrictToNeighborhood_comp_ofSubsetIsoNeighborhoodTop_hom]

/-- **Steps 1 to 4**: if `Φ_T γ` is the relative product of `Φ_Z α` and `Φ_W β`, then the Yoneda
cup product of the forgotten classes is `(−1)^{pq}` times the forgotten class of `γ`, read on the
singular side through `Ψ`. The sign is the one of `cup_singular_comparison`;
`forgetRel_relCup2`, `forgetRel_supportedEquivPair` and `forgetRel_unionComplIso` carry none. -/
theorem cup_forgetSupport_of_product {p q : ℕ} (α : H_[Z]^p(X; ℚ))
    (β : H_[W]^q(X; ℚ)) (n : ℕ) (h : p + q = n) (γ : H_[T]^n(X; ℚ))
    (hγ : supportedEquivPair X T n γ =
      relativeCohomologyMap ℚ n (unionComplIso hT).inv
        (relCup2 (TopCat.of (ComplexPoint X)) (Z.compl : Set (ComplexPoint X))
          (W.compl : Set (ComplexPoint X)) Z.compl.isOpen W.compl.isOpen
          (supportedEquivPair X Z p α) (supportedEquivPair X W q β) n h)) :
    rationalCohomologyAddEquivSingularCohomology X n
        (cup (forgetSupport ℚ X Z p α) (forgetSupport ℚ X W q β) n h) =
      ((-1 : ℤ) ^ (p * q)) •
        rationalCohomologyAddEquivSingularCohomology X n (forgetSupport ℚ X T n γ) := by
  have e1 := forgetRel_supportedEquivPair X T n γ
  rw [hγ, forgetRel_unionComplIso, forgetRel_relCup2, forgetRel_supportedEquivPair,
    forgetRel_supportedEquivPair] at e1
  rw [cup_singular_comparison' X _ _ h]
  exact congrArg _ e1

/-- **Step 6, restriction**: if `Φ_T γ` is the relative product of `Φ_Z α` and `Φ_W β`, then
upstream's transport of `γ`, restricted from `(⊤, ⊤ ∖ T)` to `(V, V ∖ T)`, is `relCup2` of the
restricted transports of `α` and `β`, read through `chartUnionIso` (the identity of `V`). No
sign: every map is a pullback along an inclusion. -/
theorem transport_restrict_of_supportedEquivPair_eq (V : Set (ComplexPoint X)) {p q : ℕ}
    (α : H_[Z]^p(X; ℚ)) (β : H_[W]^q(X; ℚ)) (n : ℕ) (h : p + q = n) (γ : H_[T]^n(X; ℚ))
    (hγ : supportedEquivPair X T n γ =
      relativeCohomologyMap ℚ n (unionComplIso hT).inv
        (relCup2 (TopCat.of (ComplexPoint X)) (Z.compl : Set (ComplexPoint X))
          (W.compl : Set (ComplexPoint X)) Z.compl.isOpen W.compl.isOpen
          (supportedEquivPair X Z p α) (supportedEquivPair X W q β) n h)) :
    relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := V)
          (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
          (T : Set (ComplexPoint X)))
        (complexSupportInjectiveSectionCohomologyEquiv X T ⊤ n
          (rationalSupportAddEquivSupportedInjectiveHomology X T n γ)) =
      relativeCohomologyMap ℚ n (chartUnionIso V (mem_iff_of_eq_inf V hT)).inv
        (relCup2 (TopCat.of V) {w : V | w.1 ∉ (Z : Set (ComplexPoint X))}
          {w : V | w.1 ∉ (W : Set (ComplexPoint X))}
          (isOpen_neighborhoodComplement V Z) (isOpen_neighborhoodComplement V W)
          (relativeCohomologyMap ℚ p
            (neighborhoodSupportInclusionPairMap (W := V)
              (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
              (Z : Set (ComplexPoint X)))
            (complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ p
              (rationalSupportAddEquivSupportedInjectiveHomology X Z p α)))
          (relativeCohomologyMap ℚ q
            (neighborhoodSupportInclusionPairMap (W := V)
              (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
              (W : Set (ComplexPoint X)))
            (complexSupportInjectiveSectionCohomologyEquiv X W ⊤ q
              (rationalSupportAddEquivSupportedInjectiveHomology X W q β))) n h) := by
  refine (restrict_supportedEquivPair X V T n γ).symm.trans ?_
  refine (congrArg (relativeCohomologyMap ℚ n (restrictToNeighborhood V T)) hγ).trans ?_
  refine (relativeCohomologyMap_apply_apply _ _ n _).trans ?_
  refine (congrArg (fun f => relativeCohomologyMap ℚ n f _) (unionComplIso_restrict V hT)).trans ?_
  refine (relativeCohomologyMap_apply_apply _ _ n _).symm.trans ?_
  refine (congrArg (relativeCohomologyMap ℚ n _) (relCup2_restrict V Z W _ _ n h)).trans ?_
  exact congrArg (relativeCohomologyMap ℚ n (chartUnionIso V (mem_iff_of_eq_inf V hT)).inv)
    (congrArg₂ (fun u v => relCup2 (TopCat.of V) {w : V | w.1 ∉ (Z : Set (ComplexPoint X))}
          {w : V | w.1 ∉ (W : Set (ComplexPoint X))}
          (isOpen_neighborhoodComplement V Z) (isOpen_neighborhoodComplement V W) u v n h)
      (restrict_supportedEquivPair X V Z p α) (restrict_supportedEquivPair X V W q β))

end Product

section Cycle

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Every open of `X(ℂ)` is paracompact (upstream's `openParacompactSpace`). -/
local instance : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

/-- The set form of `hT` gives the `Closeds` form `T = Z ⊓ W`. -/
theorem closeds_eq_inf_of_coe_eq {Y : Type} [TopologicalSpace Y] {Z W T : Closeds Y}
    (h : (T : Set Y) = (Z : Set Y) ∩ (W : Set Y)) : T = Z ⊓ W :=
  SetLike.coe_injective (h.trans (Closeds.coe_inf Z W).symm)

/-- **Steps 5 and 6, at one point.** Let `φ` be a holomorphic chart of `X(ℂ)` at `y` in which `Z`
is `{first a coordinates = 0}` and `W` is `{next b coordinates = 0}`, with `y` off `Z_sing`,
`W_sing` and `T_sing`. If `Φ_T γ` is the relative product of `Φ_Z [Z]` and `Φ_W [W]`, then the
germs at `y` of upstream's transports of `γ` and of `[T]` agree. Route: `cycle-class-germ` for
`Z`, `W`, `T` in the charts `φ` split along their normal coordinates, restriction to the
intersection `V` of the three opens, `transport_restrict_of_supportedEquivPair_eq`, and
`chartNormalProjectionCoclass_eq_relCup2` (`local-class-product`, sign `+`). -/
theorem germ_transport_eq_of_chart (x w t : X.left) {a b : ℕ} (hx : Order.coheight x = a)
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
    (hyx : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (hyw : y ∈ cycleComponentSmoothSupportAmbientOpen X w)
    (hyt : y ∈ cycleComponentSmoothSupportAmbientOpen X t)
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
  have gZ := transport_supportedClass_eq_chartNormalProjectionCoclass X x hx
    eZ (normalSplit kZ hkZ).symm hmZ hSZ y hyZ hyx
  have gW := transport_supportedClass_eq_chartNormalProjectionCoclass X w hw
    eW (normalSplit kW hkW).symm hmW hSW y hyW hyw
  have gT := transport_supportedClass_eq_chartNormalProjectionCoclass X t ht
    eT (normalSplit kT hkT).symm hmT hST y hyT hyt
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

/-- **Step 6, localization.** Under the hypotheses of the main theorem, a class `γ` with `Φ_T γ`
the relative product of `Φ_Z [Z]` and `Φ_W [W]` has upstream's normalized coclass section as its
normalization. Two sections of the sheaf `𝓗^{2(a+b)}_T` on `U_T = X ∖ T_sing` agree when their
germs agree at every point (Mathlib's `TopCat.Presheaf.section_ext`); off `T` both germs vanish
(upstream's `supportRelativeCohomologyGerm_eq_zero_of_not_mem`), and on `T` they agree by
`germ_transport_eq_of_chart`. The normalization is read on the singular side by
`normalization-singular`. -/
theorem normalization_eq_coclassSection_of_product (x w t : X.left) {a b : ℕ}
    (hx : Order.coheight x = a) (hw : Order.coheight w = b) (ht : Order.coheight t = a + b)
    (hd : a + b ≤ dim X.left)
    (hT : cycleComponentAnalyticClosedSupport X t =
      cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X w)
    (hxreg : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X x)
    (hwreg : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X w)
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
    have h := germ_transport_eq_of_chart X x w t hx hw ht hd hT φ hφ (fun z hz => (hφZW z hz).1)
      (fun z hz => (hφZW z hz).2) y hyφ (hxreg hyT) (hwreg hyT) hy γ hγ
    convert h using 2
  · exact (supportRelativeCohomologyGerm_eq_zero_of_not_mem _ _ _
      (cycleComponentAnalyticClosedSupport X t).isClosed _ y _ hyT _).trans
        (supportRelativeCohomologyGerm_eq_zero_of_not_mem _ _ _
          (cycleComponentAnalyticClosedSupport X t).isClosed _ y _ hyT _).symm

/-- **Step 6, uniqueness.** The class `γ` of `normalization_eq_coclassSection_of_product` is
upstream's supported class of `T` (`cycleComponentSupportedInjectiveClass_unique`). -/
theorem eq_supportedInjectiveClass_of_product (x w t : X.left) {a b : ℕ}
    (hx : Order.coheight x = a) (hw : Order.coheight w = b) (ht : Order.coheight t = a + b)
    (hd : a + b ≤ dim X.left)
    (hT : cycleComponentAnalyticClosedSupport X t =
      cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X w)
    (hxreg : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X x)
    (hwreg : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X w)
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
    (normalization_eq_coclassSection_of_product X x w t hx hw ht hd hT hxreg hwreg htr γ hγ)

end Cycle

/-- **The cycle class map is multiplicative for a transversal intersection with one integral
component, sign `+`.** Let `X` be smooth, integral and projective over `ℂ` of dimension `d`, and
`x`, `w`, `t` scheme points of coheights `a`, `b`, `a + b` with reduced closures `Z`, `W`, `T`
such that `T(ℂ) = Z(ℂ) ∩ W(ℂ)`, every point of `T(ℂ)` lies off `Z_sing` and `W_sing`, and every
point of `T(ℂ)` has a holomorphic chart in which `Z` is `{first a coordinates = 0}` and `W` is
`{next b coordinates = 0}`. Then `[Z] ∪ [W] = [T]` in `H^{2(a+b)}(X; ℚ)` for upstream's cycle
classes and the ladder's Yoneda cup product. Exact: no sign, no scalar. The only sign on the
route is `(−1)^{(2a)(2b)} = 1` of `cup_singular_comparison`; the local sign is the computed `+` of
`local-class-product`. Conventions (`docs/conventions.md`): rows "Cup product", "Sheaf–singular
comparison Ψ", "Supported comparison Φ", "Triad relative cup product", "Holomorphic adapted
chart", "Product of local classes (model and chart)" and "Transversal product of cycle
classes". -/
theorem cycleComponentSheafClass_cup_of_transversal
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    (x w t : X.left) {a b : ℕ} (hx : Order.coheight x = a) (hw : Order.coheight w = b)
    (ht : Order.coheight t = a + b) (hd : a + b ≤ d)
    (hT : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) =
      (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ∩
        cycleComponentAnalyticClosedSupport X w)
    (hxreg : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X x)
    (hwreg : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X w)
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
  have hγT := eq_supportedInjectiveClass_of_product X x w t hx hw ht hd hT' hxreg hwreg htr γ hγ
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

end HodgeLadder.Cycle
