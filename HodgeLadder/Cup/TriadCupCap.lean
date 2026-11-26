module

public import HodgeLadder.Cup.TriadCup
public import HodgeLadder.Cup.TriadCapPins
import LefschetzPort.AlgebraicTopology.LinearDualConnecting

/-!
# The cup–cap adjunction for the triad products

Rung `triad-relative-cup-cap` (front `cup`, decision 0010). For open `A, B ⊆ X`, classes
`φ ∈ H^p(X, A)`, `ψ ∈ H^q(X, B)` and `z ∈ H_{p+q}(X, A ∪ B)`, all over `ℚ`:

`⟨relCup2 φ ψ, z⟩ = ⟨ψ, φ ⌢ z⟩`, no sign,

where `relCup2` is this repository's relative-relative cup (rung `triad-relative-cup`), `φ ⌢ z` is
upstream's customary triad cap `unionRelativeTriadCapCohomologyLinear` (library `Other`) taken
with the excision quasi-isomorphism `triadToUnionRelativeChainMap_quasiIso_of_isOpen`, and both
pairings are upstream's universal-coefficient evaluation `relativeCohomologyEquivDualHomology`
(`= linearDualHomologyEquiv`, `⟨[c], [x]⟩ = c(x)`, no sign; register row "Universal-coefficient
evaluation"), on `(X, A ∪ B)` on the left and on `(X, B)` on the right.

On a singular `(p + q)`-simplex `σ` both sides are `φ(σ|[v₀, …, v_p]) · ψ(σ|[v_p, …, v_{p+q}])`:
the cup is Alexander–Whitney front face times back face (Mathlib `SimplexCategory.subinterval 0 p`
and `subinterval p q`), the cap is `φ(front) • back` (upstream `frontInclusion`, `backInclusion`),
and the two pairs of face maps agree (`frontInclusion_eq_subinterval`,
`backInclusion_eq_subinterval`). [`Hatcher2002` §3.3, section recalled and not re-read: Hatcher
writes the cap with the cochain on the right, σ ⌢ φ = φ(σ|[v₀, …, v_p]) σ|[v_p, …, v_{p+q}], and
proves ψ(σ ⌢ φ) = (φ ⌣ ψ)(σ), also in the relative form C_n(X, A + B) × C^p(X, A) → C_{n−p}(X, B).]

This is the form `local-class-product` uses: `local-class-cross-model` evaluates `ψ` on
`φ ⌢ orient` and gets 1; the adjunction turns that into
`relativeCohomologyEquivDualHomology … (relCup2 φ ψ) orient = 1`, which is the hypothesis of
upstream's `normalizedRelativeCoclass_unique`.

Proof: on cocycle representatives `c`, `d`, a triad cycle `x = π(y)` and a chain `y` of `X`, the
left side is `triadCupCycles c d` evaluated on `x` (`triadExcisionCoh_relCup2_homologyπ`, the
port's `linearDualHomologyEquiv_homologyπ_apply`), the right side is `d(c ⌢ x)` (the cap's
homology map reads only its middle map `triadCapHom`; the `(-1)^p` on the outer maps does not
enter), and both are `d([c̃ ⌢ y])` by `triadProj_cupCochain` and `cupCochain_eq_capLift`. Then
`linearDualHomologyEquiv_naturality` along the excision comparison moves from the sum-relative
model to `H_{p+q}(X, A ∪ B)`. Red team: `docs/sketches/triad-relative-cup-cap.redteam.md`.

## Main results

* `HodgeLadder.Cup.frontInclusion_eq_subinterval`, `HodgeLadder.Cup.backInclusion_eq_subinterval`:
  upstream's cap faces are Mathlib's Alexander–Whitney faces
* `HodgeLadder.Cup.cupCochain_eq_capLift`: chain level, on `C_{p+q}(X)`, the
  Alexander–Whitney cup of the pulled-back cochains is `ψ ∘ proj_B ∘ (φ̃ ⌢ -)`
* `HodgeLadder.Cup.relativeCochainCohomologyEquiv_symm_homologyπ`: upstream's short-complex model
  of relative cohomology sends the class of a cocycle to the short-complex class of the same cocycle
* `HodgeLadder.Cup.relativeCohomologyEquivDualHomology_triadCapCohomologyLinear_homologyπ`: on
  representatives, `⟨[d], [c] ⌢ [x]⟩ = d(c ⌢ x)` with the chain-level `triadCap`, no sign
* `HodgeLadder.Cup.triadEval_relCup2`: the adjunction on the sum-relative model
  `C(X)/(C(A) + C(B))`, before excision
* `HodgeLadder.Cup.relCup2_eval_eq_eval_triadCap`: **the adjunction**
* `HodgeLadder.Cup.relCup2_dual_eq` (from the adjunction): the same identity as linear forms
  on `H_{p+q}(X, A ∪ B)`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial

namespace HodgeLadder.Cup

section Faces

/-- Upstream's front face of the cap, vertices `0, …, p` of `[p + q]`, is Mathlib's
`subinterval 0 p`, the front face of the Alexander–Whitney diagonal. -/
theorem frontInclusion_eq_subinterval (p q : ℕ) :
    Simplicial.frontInclusion p q = SimplexCategory.subinterval 0 p (by omega) := by
  ext i
  simp [SimplexCategory.subinterval]

/-- Upstream's back face of the cap, vertices `p, …, p + q` of `[p + q]`, is Mathlib's
`subinterval p q`, the back face of the Alexander–Whitney diagonal. -/
theorem backInclusion_eq_subinterval (p q : ℕ) :
    Simplicial.backInclusion p q = SimplexCategory.subinterval p q (by omega) := by
  ext i
  simp [SimplexCategory.subinterval, Simplicial.backInclusion_apply, add_comm]

end Faces

variable (X : TopCat.{0}) (A B : Set X)

/-- **Chain-level adjunction**, no sign: on `C_{p+q}(X)`, the Alexander–Whitney cup of the
pullbacks of `φ ∈ C^p(X, A)` and `ψ ∈ C^q(X, B)` is `c ↦ ψ([φ̃ ⌢ c])`, with `φ̃ ⌢ c` upstream's
`relativeCapLift` and `[·]` the projection `C_q(X) → C_q(X, B)`. -/
theorem cupCochain_eq_capLift {p q : ℕ} (φ : RelativeCochain ℚ (TopPair.ofSubset A) p)
    (ψ : RelativeCochain ℚ (TopPair.ofSubset B) q) :
    TauCeti.ChainComplex.cupCochain ℚ (awX X) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q (p + q) rfl
        ((relativeChainProjection ℚ (TopPair.ofSubset A)).f p ≫ ModuleCat.ofHom φ)
        ((relativeChainProjection ℚ (TopPair.ofSubset B)).f q ≫ ModuleCat.ofHom ψ) =
      ModuleCat.ofHom (relativeCapLift ℚ (TopPair.ofSubset A) p q φ) ≫
        (relativeChainProjection ℚ (TopPair.ofSubset B)).f q ≫ ModuleCat.ofHom ψ := by
  apply (TauCeti.cochainValuesEquiv ℚ (ModuleCat.of ℚ ℚ) (TopCat.toSSet.obj X) (p + q)).injective
  funext σ
  have hv := TopCat.cochainValuesEquiv_cupCochain_alexanderWhitneyDiagonal X ℚ p q (p + q) rfl
    ((relativeChainProjection ℚ (TopPair.ofSubset A)).f p ≫ ModuleCat.ofHom φ)
    ((relativeChainProjection ℚ (TopPair.ofSubset B)).f q ≫ ModuleCat.ofHom ψ) σ
  erw [hv]
  simp only [TauCeti.cochainValuesEquiv_apply]
  have hc : ModuleCat.ofHom (relativeCapLift ℚ (TopPair.ofSubset A) p q φ) =
      Simplicial.capHom ℚ p q (relativeCochainToAbsolute ℚ (TopPair.ofSubset A) p φ) := rfl
  rw [hc]
  erw [TauCeti.cochainValuesEquiv_apply]
  have hι := Simplicial.iota_capHom_assoc ℚ p q
    (relativeCochainToAbsolute ℚ (TopPair.ofSubset A) p φ) σ
    ((relativeChainProjection ℚ (TopPair.ofSubset B)).f q ≫ ModuleCat.ofHom ψ)
  have hι1 := ConcreteCategory.congr_hom hι 1
  rw [ConcreteCategory.comp_apply] at hι1
  erw [hι1]
  erw [TriadCapPins.frontFace_eq, TriadCapPins.backFace_eq, frontInclusion_eq_subinterval,
    backInclusion_eq_subinterval]
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply,
    one_smul, map_smul, smul_eq_mul, relativeCochainToAbsolute_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of upstream's `relativeCochainCohomologyEquiv` on the class of a cocycle is the
short-complex class of the same cocycle (both identifications are identities on cochains). -/
theorem relativeCochainCohomologyEquiv_symm_homologyπ {p : ℕ} (P : TopPair.{0})
    (c : (RelativeCochainComplex ℚ P).cycles p) :
    (relativeCochainCohomologyEquiv ℚ P p).symm
        ((RelativeCochainComplex ℚ P).homologyπ p c) =
      (((relativeChainFunctor ℚ).obj P).sc p).linearDual.homologyπ
        (ShortComplex.cyclesMap (HomologicalComplex.linearDualCochainComplexScIso
          ((relativeChainFunctor ℚ).obj P) p).hom c) :=
  ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality
    (HomologicalComplex.linearDualCochainComplexScIso ((relativeChainFunctor ℚ).obj P) p).hom) c

set_option backward.isDefEq.respectTransparency false in
/-- **The triad cap on representatives, evaluated**: for a relative cocycle `c` on `(X, A)`,
`d` on `(X, B)` and a cycle `x` of the triad complex, `⟨[d], [c] ⌢ [x]⟩ = d(c ⌢ x)`, with the
chain-level triad cap `triadCap`; no sign. -/
theorem relativeCohomologyEquivDualHomology_triadCapCohomologyLinear_homologyπ {p q : ℕ}
    (c : (RelativeCochainComplex ℚ (TopPair.ofSubset A)).cycles p)
    (d : (RelativeCochainComplex ℚ (TopPair.ofSubset B)).cycles q)
    (x : (triadChains X A B).cycles (p + q)) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) q
        ((RelativeCochainComplex ℚ (TopPair.ofSubset B)).homologyπ q d)
        (triadCapCohomologyLinear ℚ X A B p q
          ((RelativeCochainComplex ℚ (TopPair.ofSubset A)).homologyπ p c)
          ((triadChains X A B).homologyπ (p + q) x)) =
      (show Module.Dual ℚ _ from (RelativeCochainComplex ℚ (TopPair.ofSubset B)).iCycles q d)
        (triadCap ℚ X A B p q
          ((RelativeCochainComplex ℚ (TopPair.ofSubset A)).iCycles p c)
          ((triadChains X A B).iCycles (p + q) x)) := by
  rw [triadCapCohomologyLinear, LinearMap.comp_apply]
  erw [relativeCochainCohomologyEquiv_symm_homologyπ]
  rw [triadCapCochainCohomologyLinear, LinearMap.comp_apply]
  have h1 := ConcreteCategory.congr_hom (ShortComplex.π_moduleCatCyclesIso_hom
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).sc p).linearDual)
  erw [h1]
  rw [ConcreteCategory.comp_apply]
  erw [TriadCapPins.triadCapCohomologyExplicitLinear_mk]
  rw [TriadCapPins.triadCapCocycleHomologyLinear_eq, TriadCapPins.triadCapHomologyMap_eq]
  have h2 := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality
    (triadCapShortComplexHom ℚ X A B p q _
      (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset A) p
        ((ShortComplex.moduleCatCyclesIso _).hom ((ShortComplex.cyclesMap
          (HomologicalComplex.linearDualCochainComplexScIso
            ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)) p).hom) c))).2)) x
  erw [h2]
  unfold relativeCohomologyEquivDualHomology
  erw [HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply]
  have hi := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i
    (triadCapShortComplexHom ℚ X A B p q _
      (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset A) p
        ((ShortComplex.moduleCatCyclesIso _).hom ((ShortComplex.cyclesMap
          (HomologicalComplex.linearDualCochainComplexScIso
            ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)) p).hom) c))).2)) x
  erw [hi]
  rw [ConcreteCategory.comp_apply, triadCapShortComplexHom_τ₂]
  have hc : ((relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset A) p
        ((ShortComplex.moduleCatCyclesIso _).hom ((ShortComplex.cyclesMap
          (HomologicalComplex.linearDualCochainComplexScIso
            ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)) p).hom) c)) :
          RelativeCocycle ℚ (TopPair.ofSubset A) p) : RelativeCochain ℚ (TopPair.ofSubset A) p) =
      (RelativeCochainComplex ℚ (TopPair.ofSubset A)).iCycles p c := by
    rw [TriadCapPins.relativeCohomologyCycleToCocycle_val]
    have h3 := ConcreteCategory.congr_hom (ShortComplex.moduleCatCyclesIso_hom_i
      (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).sc p).linearDual)
      ((ShortComplex.cyclesMap (HomologicalComplex.linearDualCochainComplexScIso
            ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)) p).hom) c)
    rw [ConcreteCategory.comp_apply] at h3
    refine Eq.trans h3 ?_
    have h4 := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i
      (HomologicalComplex.linearDualCochainComplexScIso
            ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)) p).hom) c
    erw [h4]
    rfl
  rw [hc]
  rfl

/-- **The adjunction on the sum-relative model**, before excision: for `w` in the homology of
`C(X)/(C(A) + C(B))`, pairing the pullback `triadExcisionCoh (relCup2 φ ψ)` with `w` (upstream's
`linearDualHomologyEquiv` of the triad complex) equals pairing `ψ` with upstream's sum-relative
triad cap `triadCapCohomologyLinear φ w`. No sign. -/
theorem triadEval_relCup2 (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (φ : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (ψ : RelativeCohomology ℚ (TopPair.ofSubset B) q)
    (w : TriadRelativeHomology ℚ X A B (p + q)) :
    (triadChains X A B).linearDualHomologyEquiv (p + q)
        ((triadExcisionCoh X A B hA hB (p + q)).hom (relCup2 X A B hA hB φ ψ (p + q) rfl)) w =
      relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) q ψ
        (triadCapCohomologyLinear ℚ X A B p q φ w) := by
  obtain ⟨c, rfl⟩ :=
    (RelativeCochainComplex ℚ (TopPair.ofSubset A)).moduleCat_homologyπ_surjective p φ
  obtain ⟨d, rfl⟩ :=
    (RelativeCochainComplex ℚ (TopPair.ofSubset B)).moduleCat_homologyπ_surjective q ψ
  obtain ⟨x, rfl⟩ := (triadChains X A B).moduleCat_homologyπ_surjective (p + q) w
  rw [triadExcisionCoh_relCup2_homologyπ,
    relativeCohomologyEquivDualHomology_triadCapCohomologyLinear_homologyπ,
    HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply]
  let π := (triadRelativeChainProjection ℚ X A B).f (p + q)
  have : Epi π := Cofork.IsColimit.epi
    (triadRelativeChainProjectionComponentIsCokernel ℚ X A B (p + q))
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance
    ((triadChains X A B).iCycles (p + q) x)
  rw [← hy]
  erw [triadCap_projection_apply]
  unfold triadCupCycles
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (dualIsoYoneda (triadChains X A B)).inv (p + q))
  erw [hi]
  rw [ConcreteCategory.comp_apply]
  erw [TauCeti.ChainComplex.iCycles_cupCycles]
  have hiA := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (dualIsoYoneda ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A))).hom p) c
  have hiB := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (dualIsoYoneda ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B))).hom q) d
  erw [hiA, hiB]
  have key := cupCochain_eq_capLift X A B
    ((RelativeCochainComplex ℚ (TopPair.ofSubset A)).iCycles p c)
    ((RelativeCochainComplex ℚ (TopPair.ofSubset B)).iCycles q d)
  rw [triadProj_cupCochain] at key
  have hk := ConcreteCategory.congr_hom key y
  rw [ConcreteCategory.comp_apply] at hk
  exact hk

/-- **The cup–cap adjunction for the triad products**, no sign: for open `A, B ⊆ X`,
`φ ∈ H^p(X, A)`, `ψ ∈ H^q(X, B)` and `z ∈ H_{p+q}(X, A ∪ B)`,
`⟨relCup2 φ ψ, z⟩ = ⟨ψ, φ ⌢ z⟩`. The pairings are upstream's universal-coefficient evaluation
`relativeCohomologyEquivDualHomology` on `(X, A ∪ B)` and on `(X, B)`; the cap is upstream's
`unionRelativeTriadCapCohomologyLinear` with the excision quasi-isomorphism
`triadToUnionRelativeChainMap_quasiIso_of_isOpen`. -/
theorem relCup2_eval_eq_eval_triadCap (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (φ : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (ψ : RelativeCohomology ℚ (TopPair.ofSubset B) q)
    (z : RelativeHomology ℚ (TopPair.ofSubset (A ∪ B)) (p + q)) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (A ∪ B)) (p + q)
        (relCup2 X A B hA hB φ ψ (p + q) rfl) z =
      relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) q ψ
        (unionRelativeTriadCapCohomologyLinear ℚ X A B p q
          (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB) φ z) := by
  have := triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB
  let w := (isoOfQuasiIsoAt (triadToUnionRelativeChainMap ℚ X A B) (p + q)).inv z
  have hz : z = HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X A B) (p + q) w :=
    (Iso.inv_hom_id_apply (isoOfQuasiIsoAt (triadToUnionRelativeChainMap ℚ X A B) (p + q)) z).symm
  change _ = relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) q ψ
    (triadCapCohomologyLinear ℚ X A B p q φ w)
  rw [← triadEval_relCup2 X A B hA hB φ ψ w]
  unfold relativeCohomologyEquivDualHomology
  rw [hz]
  exact (HomologicalComplex.linearDualHomologyEquiv_naturality
    (triadToUnionRelativeChainMap ℚ X A B) (p + q) _ w).symm

/-- **The adjunction as linear forms** on `H_{p+q}(X, A ∪ B)`: the evaluation of `relCup2 φ ψ`
is the evaluation of `ψ` after the triad cap with `φ`, no sign. -/
theorem relCup2_dual_eq (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (φ : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (ψ : RelativeCohomology ℚ (TopPair.ofSubset B) q) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (A ∪ B)) (p + q)
        (relCup2 X A B hA hB φ ψ (p + q) rfl) =
      (relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) q ψ).comp
        (unionRelativeTriadCapCohomologyLinear ℚ X A B p q
          (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB) φ) :=
  LinearMap.ext (relCup2_eval_eq_eval_triadCap X A B hA hB φ ψ)

end HodgeLadder.Cup
