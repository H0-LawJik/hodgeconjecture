module

public import Other.AlgebraicTopology.Singular.Cap.Triad

/-!
# Pins of upstream's triad cap product

Upstream's cap products (`Other/AlgebraicTopology/Singular/Cap/{Simplicial,Relative,Triad}.lean`,
library `Other`) are outside upstream's statement guard, so a change there would not be flagged
upstream. This module pins each step of the construction by `rfl` (or by restating an upstream
formula with its exact right-hand side), so that a change of a definition breaks the build here
(red-team hand computation 5, `docs/sketches/cycle-class-multiplicative.redteam.md`; register row
"Triad cap product", `docs/conventions.md`).

The chain of definitions, from the simplex formula to the customary triad pairing
`H^p(X, A) → (H_{p+q}(X, A ∪ B) → H_q(X, B))`:

1. `Simplicial.capHom`: on a `(p + q)`-simplex `x`, `φ ⌢ x = φ(front p-face of x) • (back q-face
   of x)`, the front face on vertices `0, …, p`, the back face on vertices `p, …, p + q`, no sign.
2. `relativeCapLift`: the cap of the pullback of a relative cochain to `C(X)`.
3. `triadCapLiftHom`, `triadCapHom`: the lift followed by the projection `C(X) → C(X, B)`, then
   descended through `C(X) → C(X)/(C(A) + C(B))`.
4. `triadCapShortComplexHom`: middle map `triadCapHom` with no sign; the outer maps carry
   `(-1)^p` and do not reach homology.
5. `triadCapHomologyMap`, `triadCapCocycleHomologyLinear`, `triadCapCochainCohomologyLinear`,
   `triadCapCohomologyLinear`: homology, then descent in the cocycle through upstream's
   short-complex model of relative cohomology (`relativeCochainCohomologyEquiv`).
6. `unionRelativeTriadCapCohomologyLinear`: `triadCapCohomologyLinear` after the inverse of the
   excision equivalence `triadUnionExcisionHomologyEquiv`, which is `isoOfQuasiIsoAt` of the
   comparison `triadToUnionRelativeChainMap` (induced by the identity of `C(X)`).

## Main results

* `HodgeLadder.Cup.TriadCapPins.capHom_eq`, `cap_chainOfSimplex_eq`, `frontInclusion_val`,
  `backInclusion_val`, `chainOfSimplex_eq`: the simplex formula of the cap, front and back faces
* `HodgeLadder.Cup.TriadCapPins.triadSubspaceChainMap_pin`, `triadRelativeChainComplex_eq`,
  `triadRelativeChainProjection_eq`, `triadToUnionRelativeChainMap_eq`,
  `triadRelativeChainProjection_triadToUnionRelativeChainMap_eq`: the triad complex and the
  excision comparison, induced by the identity of `C(X)`
* `HodgeLadder.Cup.TriadCapPins.relativeCapLift_eq`, `relativeCochainToAbsolute_eq`
* `HodgeLadder.Cup.TriadCapPins.triadCapLiftHom_eq`, `triadCap_eq`,
  `triadRelativeChainProjection_triadCapHom_eq`: the chain-level triad cap
* `HodgeLadder.Cup.TriadCapPins.triadCapShortComplexHom_τ₂_eq`,
  `triadCapShortComplexHomSucc_τ₁_eq`, `triadCapShortComplexHomSucc_τ₃_eq`,
  `triadCapShortComplexHomZero_τ₁_eq`: the signs
* `HodgeLadder.Cup.TriadCapPins.triadCapHomologyMap_eq`, `triadCapCocycleHomologyLinear_eq`,
  `triadCapCochainCohomologyLinear_eq`, `triadCapCohomologyExplicitLinear_mk`,
  `relativeCohomologyCycleToCocycle_val`, `triadCapCohomologyLinear_eq`,
  `relativeCochainCohomologyEquiv_symm_eq`: descent to cohomology
* `HodgeLadder.Cup.TriadCapPins.triadToUnionRelativeHomologyMap_eq`
* `HodgeLadder.Cup.TriadCapPins.triadUnionExcisionHomologyEquiv_symm_eq`,
  `unionRelativeTriadCapCohomologyLinear_eq`: the excision inverse and the customary pairing,
  and the composite `unionRelativeTriadCapCohomologyLinear_apply_eq`
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial

universe u

namespace HodgeLadder.Cup.TriadCapPins

section Simplicial

open AlgebraicTopology.Simplicial

variable (R : Type u) [CommRing R]

/-- Pin: the front inclusion `[p] → [p + q]` sends vertex `i` to vertex `i`. -/
theorem frontInclusion_val (p q : ℕ) (i : Fin (p + 1)) :
    ((frontInclusion p q).toOrderHom i).val = i.val :=
  rfl

/-- Pin: the back inclusion `[q] → [p + q]` sends vertex `i` to vertex `p + i`. -/
theorem backInclusion_val (p q : ℕ) (i : Fin (q + 1)) :
    ((backInclusion p q).toOrderHom i).val = p + i.val :=
  rfl

/-- Pin: the front and back faces are the simplicial operators of the two inclusions. -/
theorem frontFace_eq (X : SSet.{u}) {p q : ℕ} (x : X _⦋p + q⦌) :
    frontFace X x = X.map (frontInclusion p q).op x :=
  rfl

/-- Pin: the back face is the simplicial operator of the back inclusion. -/
theorem backFace_eq (X : SSet.{u}) {p q : ℕ} (x : X _⦋p + q⦌) :
    backFace X x = X.map (backInclusion p q).op x :=
  rfl

/-- Pin: the definition of `capHom`, the cofan of `x ↦ φ(front x) • back x` over the simplices
of the unnormalized chain group. -/
theorem capHom_eq {X : SSet.{u}} (p q : ℕ) (φ : Cochain R X p) :
    capHom R p q φ =
      (X.isColimitChainComplexXCofan (ModuleCat.of R R) (p + q)).desc
        (Cofan.mk _ fun x ↦ ModuleCat.ofHom <|
          LinearMap.toSpanSingleton R _ <|
            φ (chainOfSimplex R (frontFace X x)) • chainOfSimplex R (backFace X x)) :=
  rfl

/-- Pin: `cap` is the linear map underlying `capHom`. -/
theorem cap_eq {X : SSet.{u}} (p q : ℕ) (φ : Cochain R X p) :
    cap R p q φ = (capHom R p q φ).hom :=
  rfl

/-- **The cap formula on a simplex**, no sign: `φ ⌢ x = φ(front p-face of x) • back q-face of x`
(upstream `cap_chainOfSimplex`, restated with its right-hand side written out). -/
theorem cap_chainOfSimplex_eq {X : SSet.{u}} (p q : ℕ) (φ : Cochain R X p) (x : X _⦋p + q⦌) :
    cap R p q φ (chainOfSimplex R x) =
      φ (chainOfSimplex R (X.map (frontInclusion p q).op x)) •
        chainOfSimplex R (X.map (backInclusion p q).op x) :=
  cap_chainOfSimplex R p q φ x

/-- Pin: the chain of a simplex is the generator `1` of its summand. -/
theorem chainOfSimplex_eq {Y : SSet.{u}} {n : ℕ} (x : Y _⦋n⦌) :
    Simplicial.chainOfSimplex R x = (Y.ιChainComplex (R := ModuleCat.of R R) x).hom 1 :=
  rfl

end Simplicial

section Relative

variable (R : Type u) [CommRing R]

/-- Pin: the pullback of a relative cochain to `C(X)` is the dual of the relative projection. -/
theorem relativeCochainToAbsolute_eq (P : TopPair.{u}) (n : ℕ) :
    relativeCochainToAbsolute R P n = ((relativeChainProjection R P).f n).hom.dualMap :=
  rfl

/-- Pin: `relativeCapLift` is the simplicial cap of the pulled-back cochain. -/
theorem relativeCapLift_eq (P : TopPair.{u}) (p q : ℕ) (φ : RelativeCochain R P p) :
    relativeCapLift R P p q φ = Simplicial.cap R p q (relativeCochainToAbsolute R P p φ) :=
  rfl

end Relative

section Triad

variable (R : Type u) [CommRing R] (X : TopCat.{u}) (A B : Set X)

/-- Pin: the ambient triad cap lift is the relative cap lift followed by `C(X) → C(X, B)`. -/
theorem triadCapLiftHom_eq (p q : ℕ) (φ : RelativeCochain R (TopPair.ofSubset A) p) :
    triadCapLiftHom R X A B p q φ =
      ModuleCat.ofHom (relativeCapLift R (TopPair.ofSubset A) p q φ) ≫
        (relativeChainProjection R (TopPair.ofSubset B)).f q :=
  rfl

/-- Pin: `triadCap` is the linear map underlying `triadCapHom`. -/
theorem triadCap_eq (p q : ℕ) (φ : RelativeCochain R (TopPair.ofSubset A) p) :
    triadCap R X A B p q φ = (triadCapHom R X A B p q φ).hom :=
  rfl

/-- **The chain-level triad cap on a projected ambient chain**: for `c ∈ C_{p+q}(X)`,
`φ ⌢ [c] = [φ̃ ⌢ c] ∈ C_q(X, B)`, with `φ̃` the pullback of `φ` to `C(X)` (upstream
`triadCap_projection_apply`, right-hand side written out). -/
theorem triadRelativeChainProjection_triadCapHom_eq (p q : ℕ)
    (φ : RelativeCochain R (TopPair.ofSubset A) p)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) (p + q)) :
    triadCap R X A B p q φ ((triadRelativeChainProjection R X A B).f (p + q) c) =
      (relativeChainProjection R (TopPair.ofSubset B)).f q
        (Simplicial.cap R p q (((relativeChainProjection R (TopPair.ofSubset A)).f p).hom.dualMap
          φ) c) :=
  triadCap_projection_apply R X A B p q φ c

/-- Pin: the middle map of the triad cap short-complex morphism is `triadCapHom`, no sign. -/
theorem triadCapShortComplexHom_τ₂_eq (p q : ℕ) (φ : RelativeCochain R (TopPair.ofSubset A) p)
    (hφ : relativeCoboundary R (TopPair.ofSubset A) p φ = 0) :
    (triadCapShortComplexHom R X A B p q φ hφ).τ₂ = triadCapHom R X A B p q φ :=
  triadCapShortComplexHom_τ₂ R X A B p q φ hφ

/-- Pin: the left map of the positive-degree short-complex morphism carries `(-1)^p`. -/
theorem triadCapShortComplexHomSucc_τ₁_eq (p q : ℕ)
    (φ : RelativeCochain R (TopPair.ofSubset A) p)
    (hφ : relativeCoboundary R (TopPair.ofSubset A) p φ = 0) :
    (triadCapShortComplexHomSucc R X A B p q φ hφ).τ₁ =
      ModuleCat.ofHom (((-1 : R) ^ p) • triadCap R X A B p ((q + 1) + 1) φ) :=
  rfl

/-- Pin: the right map of the positive-degree short-complex morphism carries `(-1)^p`. -/
theorem triadCapShortComplexHomSucc_τ₃_eq (p q : ℕ)
    (φ : RelativeCochain R (TopPair.ofSubset A) p)
    (hφ : relativeCoboundary R (TopPair.ofSubset A) p φ = 0) :
    (triadCapShortComplexHomSucc R X A B p q φ hφ).τ₃ =
      ModuleCat.ofHom (((-1 : R) ^ p) • triadCap R X A B p q φ) :=
  rfl

/-- Pin: the triad cap on homology is the homology map of the short-complex morphism. -/
theorem triadCapHomologyMap_eq (p q : ℕ) (φ : RelativeCochain R (TopPair.ofSubset A) p)
    (hφ : relativeCoboundary R (TopPair.ofSubset A) p φ = 0) :
    triadCapHomologyMap R X A B p q φ hφ =
      (ShortComplex.homologyMap (triadCapShortComplexHom R X A B p q φ hφ)).hom :=
  rfl

/-- Pin: the cocycle-linear triad cap. -/
theorem triadCapCocycleHomologyLinear_eq (p q : ℕ)
    (φ : RelativeCocycle R (TopPair.ofSubset A) p) :
    triadCapCocycleHomologyLinear R X A B p q φ = triadCapHomologyMap R X A B p q φ.1 φ.2 :=
  rfl

/-- Pin: on the short-complex model of relative cohomology, the triad cap descends the
cocycle map through `moduleCatHomologyIso` of the dual short complex. -/
theorem triadCapCochainCohomologyLinear_eq (p q : ℕ) :
    triadCapCochainCohomologyLinear R X A B p q =
      (triadCapCohomologyExplicitLinear R X A B p q).comp
        ((((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual.moduleCatHomologyIso
          ).hom.hom :=
  rfl

/-- Pin: the explicit quotient form descends `triadRelativeCohomologyCycleCapLinear`. -/
theorem triadCapCohomologyExplicitLinear_mk (p q : ℕ)
    (φ : LinearMap.ker
      ((((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual.g.hom)) :
    triadCapCohomologyExplicitLinear R X A B p q (Submodule.Quotient.mk φ) =
      triadCapCocycleHomologyLinear R X A B p q
        (relativeCohomologyCycleToCocycle R (TopPair.ofSubset A) p φ) :=
  rfl

/-- Pin: an explicit dual cycle of the short-complex model is a relative cocycle with the same
underlying cochain. -/
theorem relativeCohomologyCycleToCocycle_val (P : TopPair.{u}) (p : ℕ)
    (φ : LinearMap.ker ((((relativeChainFunctor R).obj P).sc p).linearDual.g.hom)) :
    ((relativeCohomologyCycleToCocycle R P p φ : RelativeCocycle R P p) : RelativeCochain R P p) =
      φ.1 :=
  rfl

/-- Pin: the triad cap on upstream's relative cohomology is the short-complex form after the
inverse of `relativeCochainCohomologyEquiv`. -/
theorem triadCapCohomologyLinear_eq (p q : ℕ) :
    triadCapCohomologyLinear R X A B p q =
      (triadCapCochainCohomologyLinear R X A B p q).comp
        (relativeCochainCohomologyEquiv R (TopPair.ofSubset A) p).symm.toLinearMap :=
  rfl

/-- Pin: the inverse of `relativeCochainCohomologyEquiv` is the homology map of upstream's
degreewise identification `linearDualCochainComplexScIso`, the same identification that
`linearDualHomologyEquiv` (the evaluation pairing) goes through. -/
theorem relativeCochainCohomologyEquiv_symm_eq (P : TopPair.{u}) (p : ℕ) :
    (relativeCochainCohomologyEquiv R P p).symm.toLinearMap =
      (ShortComplex.homologyMap (HomologicalComplex.linearDualCochainComplexScIso
        ((relativeChainFunctor R).obj P) p).hom).hom :=
  rfl

/-- Pin: the comparison `C(X)/(C(A) + C(B)) → C(X, A ∪ B)` on homology. -/
theorem triadToUnionRelativeHomologyMap_eq (n : ℕ) :
    triadToUnionRelativeHomologyMap R X A B n =
      (HomologicalComplex.homologyMap (triadToUnionRelativeChainMap R X A B) n).hom :=
  rfl

/-- Pin: the inverse of the excision equivalence is the inverse of `isoOfQuasiIsoAt` of the
comparison chain map. -/
theorem triadUnionExcisionHomologyEquiv_symm_eq (n : ℕ)
    (hExcision : QuasiIso (triadToUnionRelativeChainMap R X A B)) :
    (triadUnionExcisionHomologyEquiv R X A B n hExcision).symm.toLinearMap =
      (letI := hExcision; (isoOfQuasiIsoAt (triadToUnionRelativeChainMap R X A B) n).inv.hom) :=
  rfl

/-- Pin: the customary triad pairing is the sum-relative one after the excision inverse. -/
theorem unionRelativeTriadCapCohomologyLinear_eq (p q : ℕ)
    (hExcision : QuasiIso (triadToUnionRelativeChainMap R X A B))
    (α : RelativeCohomology R (TopPair.ofSubset A) p) :
    unionRelativeTriadCapCohomologyLinear R X A B p q hExcision α =
      (triadCapCohomologyLinear R X A B p q α).comp
        (triadUnionExcisionHomologyEquiv R X A B (p + q) hExcision).symm.toLinearMap :=
  rfl

/-- **The composite pin**: the customary triad pairing, unfolded through
`triadCapCochainCohomologyLinear`, the short-complex identification of relative cohomology,
and the inverse of `isoOfQuasiIsoAt` of the excision comparison. -/
theorem unionRelativeTriadCapCohomologyLinear_apply_eq (p q : ℕ)
    (hExcision : QuasiIso (triadToUnionRelativeChainMap R X A B))
    (α : RelativeCohomology R (TopPair.ofSubset A) p)
    (z : RelativeHomology R (TopPair.ofSubset (A ∪ B)) (p + q)) :
    unionRelativeTriadCapCohomologyLinear R X A B p q hExcision α z =
      triadCapCochainCohomologyLinear R X A B p q
        ((ShortComplex.homologyMap (HomologicalComplex.linearDualCochainComplexScIso
          ((relativeChainFunctor R).obj (TopPair.ofSubset A)) p).hom).hom α)
        ((letI := hExcision;
          isoOfQuasiIsoAt (triadToUnionRelativeChainMap R X A B) (p + q)).inv.hom z) :=
  rfl

/-- Pin: the subspace map `C(A) ⊞ C(B) → C(X)` is `biprod.desc` of the two inclusions. -/
theorem triadSubspaceChainMap_pin :
    triadSubspaceChainMap R X A B =
      biprod.desc ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom
        ((chainPairFunctor R).obj (TopPair.ofSubset B)).hom :=
  rfl

/-- Pin: the triad complex is the cokernel of the subspace map. -/
theorem triadRelativeChainComplex_eq :
    triadRelativeChainComplex R X A B = cokernel (triadSubspaceChainMap R X A B) :=
  rfl

/-- Pin: the triad projection is the cokernel projection. -/
theorem triadRelativeChainProjection_eq :
    triadRelativeChainProjection R X A B = cokernel.π (triadSubspaceChainMap R X A B) :=
  rfl

/-- Pin: the excision comparison is the cokernel descent of the projection to `C(X, A ∪ B)`. -/
theorem triadToUnionRelativeChainMap_eq :
    triadToUnionRelativeChainMap R X A B =
      (cokernelIsCokernel (triadSubspaceChainMap R X A B)).desc
        (CokernelCofork.ofπ (relativeChainProjection R (TopPair.ofSubset (A ∪ B)))
          (triadSubspaceChainMap_unionRelativeChainProjection_eq_zero R X A B)) :=
  rfl

/-- **The excision comparison is induced by the identity of `C(X)`**: after the triad
projection it is the projection `C(X) → C(X, A ∪ B)` (upstream
`triadRelativeChainProjection_triadToUnionRelativeChainMap`, restated). -/
theorem triadRelativeChainProjection_triadToUnionRelativeChainMap_eq :
    triadRelativeChainProjection R X A B ≫ triadToUnionRelativeChainMap R X A B =
      relativeChainProjection R (TopPair.ofSubset (A ∪ B)) :=
  triadRelativeChainProjection_triadToUnionRelativeChainMap R X A B

/-- Pin: in the degree-zero morphism the left map carries `(-1)^p`. -/
theorem triadCapShortComplexHomZero_τ₁_eq (p : ℕ)
    (φ : RelativeCochain R (TopPair.ofSubset A) p)
    (hφ : relativeCoboundary R (TopPair.ofSubset A) p φ = 0) :
    (triadCapShortComplexHomZero R X A B p φ hφ).τ₁ =
      ModuleCat.ofHom (((-1 : R) ^ p) • triadCap R X A B p 1 φ) :=
  rfl

end Triad

end HodgeLadder.Cup.TriadCapPins
