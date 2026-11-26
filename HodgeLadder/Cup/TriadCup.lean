module

public import HodgeLadder.Cup.RelCupNaturality
public import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality
public import HodgeConjecture.Mathlib.Topology.Category.TopPair
public import Other.AlgebraicTopology.Singular.Excision.Triad
import Other.AlgebraicTopology.Singular.EmptySubspace

/-!
# The relative-relative singular cup product on a triad

Rung `triad-relative-cup` (front `cup`, decision 0010). For subsets `A, B` of a space `X`, the
Alexander–Whitney diagonal of `X` followed by the two relative projections,
`C(X) → C(X) ⊗ C(X) → C(X, A) ⊗ C(X, B)`, kills the chains of `A` (first factor) and of `B`
(second factor), so it descends to a diagonal on upstream's sum-relative triad complex
`C(X)/(C(A) + C(B))` (`triadRelativeChainComplex`). Tau Ceti's generic cup product along this
diagonal is a product `H^p(X, A) × H^q(X, B) → H^{p+q}` of the triad complex. For open `A` and
`B`, upstream's triad excision (`triadToUnionRelativeChainMap_quasiIso_of_isOpen`, library
`Other`) makes the comparison `C(X)/(C(A) + C(B)) → C(X, A ∪ B)` a quasi-isomorphism; its dual
over `ℚ` is an isomorphism on cohomology, and its inverse lands the product in `H^{p+q}(X, A ∪ B)`.

Conventions (`docs/conventions.md`, rows "Singular cup product", "Relative singular cup
product"): front `p`-face of the `A`-relative factor times back `q`-face of the `B`-relative
factor, no sign; the `A` factor is first. The comparison isomorphisms are induced by identity
maps on chains and carry no sign.

## Main definitions

* `HodgeLadder.Cup.triadDiagonal`: `C(X)/(C(A) + C(B)) → C(X, A) ⊗ C(X, B)`
* `HodgeLadder.Cup.triadExcisionCoh`: `H^n(X, A ∪ B) ≅ H^n(Hom(C(X)/(C(A) + C(B)), ℚ))` for
  open `A, B`, the pullback along upstream's excision comparison
* `HodgeLadder.Cup.relCup2`: `H^p(X, A) × H^q(X, B) → H^{p+q}(X, A ∪ B)`
* `HodgeLadder.Cup.unionEmptyIso`: the pair `(X, A ∪ ∅)` is `(X, A)`, by the identity of `X`
* `HodgeLadder.Cup.triadCupCycles`: the triad cup of a relative cocycle on `(X, A)` and one on
  `(X, B)`, a cocycle on the triad complex

## Main results

* `HodgeLadder.Cup.forgetRel_relCup2`:
  `forgetRel (relCup2 a b) = cupSing (forgetRel a) (forgetRel b)`
* `HodgeLadder.Cup.relCup2_empty`: for `B = ∅`, `relCup2 a b` is `relCupSing a (forgetRel b)`
  read on `(X, A ∪ ∅) = (X, A)` through `unionEmptyIso`
* `HodgeLadder.Cup.forgetRel_empty_bijective`: `forgetRel : H^q(X, ∅) → H^q(X)` is bijective
  (upstream's `relativeChainProjection_empty_isIso`, library `Other`)
* `HodgeLadder.Cup.triadExcisionCoh_relCup2_homologyπ`, `HodgeLadder.Cup.triadProj_cupCochain`:
  the cocycle formula. Through triad excision, `relCup2 [c] [d]` is the class of
  `triadCupCycles c d`, and that cochain pulled back to `C(X)` is the Alexander–Whitney cup of
  `c` and `d` pulled back to `C(X)`. The two compatibility theorems alone do not determine
  `relCup2`, since `forgetRel` loses the relative information; the cocycle formula does.
* `HodgeLadder.Cup.homologyMap_linearDualMap_bijective`: over `ℚ`, the dual of a
  quasi-isomorphism is bijective on cohomology (general)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology.Singular

namespace HodgeLadder.Cup

section Dual

/-- Over `ℚ`, the dual of a quasi-isomorphism of chain complexes is bijective on cohomology:
under upstream's universal-coefficient identification `linearDualHomologyEquiv` it is the
transpose of the homology isomorphism. -/
theorem homologyMap_linearDualMap_bijective {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (f : K ⟶ L) [QuasiIso f] (n : ℕ) :
    Function.Bijective
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n) := by
  let e : K.homology n ≃ₗ[ℚ] L.homology n := (isoOfQuasiIsoAt f n).toLinearEquiv
  let g : L.linearDualCochainComplex.homology n ≃ₗ[ℚ] K.linearDualCochainComplex.homology n :=
    (L.linearDualHomologyEquiv n).trans
      (e.dualMap.trans (K.linearDualHomologyEquiv n).symm)
  have hg : ∀ a, HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n a = g a := by
    intro a
    apply (K.linearDualHomologyEquiv n).injective
    ext z
    rw [HomologicalComplex.linearDualHomologyEquiv_naturality]
    simp [g, e, LinearEquiv.dualMap_apply]
  have : (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n :
      _ → _) = g := funext hg
  rw [this]
  exact g.bijective

end Dual

variable (X : TopCat.{0}) (A B : Set X)

/-- The sum-relative triad complex `C(X)/(C(A) + C(B))` (upstream `triadRelativeChainComplex`). -/
abbrev triadChains : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  triadRelativeChainComplex ℚ X A B

set_option backward.isDefEq.respectTransparency false in
/-- **The triad diagonal** `C(X)/(C(A) + C(B)) → C(X, A) ⊗ C(X, B)`: the Alexander–Whitney
diagonal of `X` followed by the two relative projections, which kills `C(A)` in the first factor
and `C(B)` in the second. -/
def triadDiagonal :
    triadChains X A B ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset A) ⊗
        (relativeChainFunctor ℚ).obj (TopPair.ofSubset B) :=
  cokernel.desc (triadSubspaceChainMap ℚ X A B)
    (awX X ≫ (relativeChainProjection ℚ (TopPair.ofSubset A) ⊗ₘ
      relativeChainProjection ℚ (TopPair.ofSubset B))) (by
      have hA := TopCat.alexanderWhitneyDiagonal_naturality (TopPair.ofSubset A).map
        (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
      have hB := TopCat.alexanderWhitneyDiagonal_naturality (TopPair.ofSubset B).map
        (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
      have cA : SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset A).map)
          (𝟙_ (ModuleCat.{0} ℚ)) ≫ relativeChainProjection ℚ (TopPair.ofSubset A) = 0 :=
        cokernel.condition _
      have cB : SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset B).map)
          (𝟙_ (ModuleCat.{0} ℚ)) ≫ relativeChainProjection ℚ (TopPair.ofSubset B) = 0 :=
        cokernel.condition _
      apply biprod.hom_ext'
      · rw [comp_zero, triadSubspaceChainMap, biprod.inl_desc_assoc]
        change SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset A).map) _ ≫ awX X ≫ _ = 0
        rw [← Category.assoc]
        erw [hA]
        rw [Category.assoc, tensorHom_comp_tensorHom, cA]
        simp
      · rw [comp_zero, triadSubspaceChainMap, biprod.inr_desc_assoc]
        change SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset B).map) _ ≫ awX X ≫ _ = 0
        rw [← Category.assoc]
        erw [hB]
        rw [Category.assoc, tensorHom_comp_tensorHom, cB]
        simp)

/-- Upstream's cochain cohomology of the triad complex as Tau Ceti cohomology. -/
def triadCohIso (n : ℕ) :
    (triadChains X A B).linearDualCochainComplex.homology n ≅
      ((triadChains X A B).linearYonedaObj ℚ (ModuleCat.of ℚ ℚ)).homology n :=
  HomologicalComplex.homologyMapIso (dualIsoYoneda (triadChains X A B)) n

/-- **Triad excision on rational cohomology**, for open `A, B`: the pullback
`H^n(X, A ∪ B) → H^n(Hom(C(X)/(C(A) + C(B)), ℚ))` along upstream's comparison
`triadToUnionRelativeChainMap` (induced by the identity of `C(X)`) is an isomorphism. -/
def triadExcisionCoh (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    RelativeCohomology ℚ (TopPair.ofSubset (A ∪ B)) n ≅
      (triadChains X A B).linearDualCochainComplex.homology n :=
  haveI := triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB
  (LinearEquiv.ofBijective
    (HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap (triadToUnionRelativeChainMap ℚ X A B)) n).hom
    (homologyMap_linearDualMap_bijective _ n)).toModuleIso

/-- **The relative-relative singular cup product** `H^p(X, A) × H^q(X, B) → H^{p+q}(X, A ∪ B)`
for open `A, B`: Tau Ceti's cup along `triadDiagonal` (front face of `a`, back face of `b`, no
sign), carried to `H^{p+q}(X, A ∪ B)` by the inverse of `triadExcisionCoh`. -/
def relCup2 (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (a : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset B) q) (n : ℕ) (h : p + q = n) :
    RelativeCohomology ℚ (TopPair.ofSubset (A ∪ B)) n :=
  (triadExcisionCoh X A B hA hB n).inv ((triadCohIso X A B n).inv
    (TauCeti.ChainComplex.cup ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
      ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b)))

set_option backward.isDefEq.respectTransparency false in
/-- **Forgetting the subspaces carries `relCup2` to the singular cup product**, no sign:
`forgetRel (relCup2 a b) = cupSing (forgetRel a) (forgetRel b)` in `H^{p+q}(X)`. -/
theorem forgetRel_relCup2 (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (a : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset B) q) (n : ℕ) (h : p + q = n) :
    forgetRel (TopPair.ofSubset (A ∪ B)) n (relCup2 X A B hA hB a b n h) =
      cupSing X (forgetRel (TopPair.ofSubset A) p a) (forgetRel (TopPair.ofSubset B) q b) n h := by
  have key : ∀ z, forgetRel (TopPair.ofSubset (A ∪ B)) n z =
      HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        (triadRelativeChainProjection ℚ X A B)) n ((triadExcisionCoh X A B hA hB n).hom z) := by
    intro z
    unfold forgetRel
    rw [← triadRelativeChainProjection_triadToUnionRelativeChainMap,
      HomologicalComplex.linearDualMap_comp, HomologicalComplex.homologyMap_comp]
    rfl
  rw [relCup2, key, Iso.inv_hom_id_apply]
  apply (cohIso X n).toLinearEquiv.injective
  change (cohIso X n).hom _ = (cohIso X n).hom _
  rw [cupSing, Iso.inv_hom_id_apply]
  have e1 := cohIso_forgetRel (TopPair.ofSubset A) p a
  have e2 := cohIso_forgetRel (TopPair.ofSubset B) q b
  have e3 := homologyMap_dualIsoYoneda_apply (triadRelativeChainProjection ℚ X A B) n
    ((triadCohIso X A B n).inv
      (TauCeti.ChainComplex.cup ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
        ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b)))
  have hD : triadRelativeChainProjection ℚ X A B ≫ triadDiagonal X A B =
      awX X ≫ (relativeChainProjection ℚ (TopPair.ofSubset A) ⊗ₘ
        relativeChainProjection ℚ (TopPair.ofSubset B)) := cokernel.π_desc _ _ _
  have hn := TauCeti.ChainComplex.cup_naturality (k := ℚ) (D := triadDiagonal X A B)
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (awX X) (triadRelativeChainProjection ℚ X A B)
    (relativeChainProjection ℚ (TopPair.ofSubset A))
    (relativeChainProjection ℚ (TopPair.ofSubset B)) hD p q n h
    ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b)
  have e4 : HomologicalComplex.homologyMap (dualIsoYoneda (triadChains X A B)).hom n
      ((triadCohIso X A B n).inv
        (TauCeti.ChainComplex.cup ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
          ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b))) =
      TauCeti.ChainComplex.cup ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
          ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b) :=
    Iso.inv_hom_id_apply (triadCohIso X A B n) _
  change HomologicalComplex.homologyMap (dualIsoYoneda _).hom n _ = _
  rw [e3, e4, tcCup_eq]
  erw [e1, e2]
  exact hn.symm

/-- The pair `(X, A ∪ ∅)` is the pair `(X, A)`: the identity of `X`, which maps `A ∪ ∅` onto
`A` (upstream `TopPair.isoOfSubset`). -/
def unionEmptyIso : TopPair.ofSubset (A ∪ (∅ : Set X)) ≅ TopPair.ofSubset A :=
  TopPair.isoOfSubset (Homeomorph.refl X) (fun x => by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back along `f` then `g` with `g ≫ f = 𝟙` is the identity on cohomology. -/
lemma homologyMap_linearYoneda_cancel {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (M : ModuleCat.{0} ℚ) (f : K ⟶ L) (g : L ⟶ K) (hgf : g ≫ f = 𝟙 L) (n : ℕ)
    (x : (L.linearYonedaObj ℚ M).homology n) :
    HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor ℚ M).map g.op) n
      (HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor ℚ M).map f.op) n x)
      = x := by
  have h1 : (TauCeti.ChainComplex.linearYonedaFunctor ℚ M).map f.op ≫
      (TauCeti.ChainComplex.linearYonedaFunctor ℚ M).map g.op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, hgf, op_id, CategoryTheory.Functor.map_id]
  have h2 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) h1
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at h2
  exact ConcreteCategory.congr_hom h2 x

set_option backward.isDefEq.respectTransparency false in
/-- **`relCup2` with `B = ∅` is `relCupSing`**, no sign: on `(X, A ∪ ∅)`, identified with
`(X, A)` by `unionEmptyIso` (the identity of `X`), `relCup2 a b` is `relCupSing a (forgetRel b)`,
where `forgetRel : H^q(X, ∅) → H^q(X)` is the identification of `forgetRel_empty_bijective`. -/
theorem relCup2_empty (hA : IsOpen A) {p q : ℕ}
    (a : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset (∅ : Set X)) q) (n : ℕ) (h : p + q = n) :
    relCup2 X A ∅ hA isOpen_empty a b n h =
      relativeCohomologyMap ℚ n (unionEmptyIso X A).hom
        (relCupSing (TopPair.ofSubset A) a (forgetRel (TopPair.ofSubset (∅ : Set X)) q b) n h) := by
  let P0 := TopPair.ofSubset (∅ : Set X)
  let g : (relativeChainFunctor ℚ).obj P0 ⟶ SingularChainComplex ℚ X :=
    inv (relativeChainProjection ℚ P0)
  let e : triadChains X A ∅ ⟶ (relativeChainFunctor ℚ).obj (TopPair.ofSubset A) :=
    triadToUnionRelativeChainMap ℚ X A ∅ ≫ (relativeChainFunctor ℚ).map (unionEmptyIso X A).hom
  have hπe : triadRelativeChainProjection ℚ X A ∅ ≫ e =
      relativeChainProjection ℚ (TopPair.ofSubset A) := by
    simp only [e]
    rw [triadRelativeChainProjection_triadToUnionRelativeChainMap_assoc]
    erw [TopPair.Homotopy.relativeChainProjection_naturality]
    have : (TopPair.Hom.fst (unionEmptyIso X A).hom) = 𝟙 X := rfl
    erw [this, CategoryTheory.Functor.map_id, Category.id_comp]
  have hD : e ≫ relDiagonal (TopPair.ofSubset A) =
      triadDiagonal X A ∅ ≫ (𝟙 _ ⊗ₘ g) := by
    have : Epi (triadRelativeChainProjection ℚ X A ∅) := by
      change Epi (cokernel.π _); infer_instance
    rw [← cancel_epi (triadRelativeChainProjection ℚ X A ∅), ← Category.assoc, hπe,
      relProj_relDiagonal]
    erw [← Category.assoc, cokernel.π_desc]
    rw [Category.assoc, tensorHom_comp_tensorHom]
    simp only [g]
    erw [IsIso.hom_inv_id]
    rfl
  -- reduce through the excision isomorphism
  apply (triadExcisionCoh X A ∅ hA isOpen_empty n).toLinearEquiv.injective
  apply (triadCohIso X A ∅ n).toLinearEquiv.injective
  change (triadCohIso X A ∅ n).hom ((triadExcisionCoh X A ∅ hA isOpen_empty n).hom _) =
    (triadCohIso X A ∅ n).hom ((triadExcisionCoh X A ∅ hA isOpen_empty n).hom _)
  rw [relCup2, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  have hr : ∀ z, (triadExcisionCoh X A ∅ hA isOpen_empty n).hom
      (relativeCohomologyMap ℚ n (unionEmptyIso X A).hom z) =
      HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap e) n z := by
    intro z
    simp only [e, HomologicalComplex.linearDualMap_comp, HomologicalComplex.homologyMap_comp]
    rfl
  rw [hr]
  change _ = HomologicalComplex.homologyMap (dualIsoYoneda _).hom n _
  rw [homologyMap_dualIsoYoneda_apply]
  have e5 : HomologicalComplex.homologyMap
      (dualIsoYoneda ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A))).hom n
      (relCupSing (TopPair.ofSubset A) a (forgetRel P0 q b) n h) =
      TauCeti.ChainComplex.cup ℚ (relDiagonal (TopPair.ofSubset A)) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
        p q n h ((relCohIso (TopPair.ofSubset A) p).hom a) ((cohIso X q).hom (forgetRel P0 q b)) :=
    Iso.inv_hom_id_apply (relCohIso (TopPair.ofSubset A) n) _
  erw [e5]
  have hn := TauCeti.ChainComplex.cup_naturality (k := ℚ) (D := relDiagonal (TopPair.ofSubset A))
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (triadDiagonal X A ∅) e (𝟙 _) g hD p q n h
    ((relCohIso (TopPair.ofSubset A) p).hom a)
    ((cohIso X q).hom (forgetRel P0 q b))
  erw [← hn]
  have e6 := cohIso_forgetRel P0 q b
  erw [e6]
  rw [CategoryTheory.op_id]
  erw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id, ConcreteCategory.id_apply]
  congr 1
  exact (homologyMap_linearYoneda_cancel _ (relativeChainProjection ℚ P0) g
    (IsIso.inv_hom_id _) q _).symm

/-- Forgetting the empty subspace, `H^q(X, ∅) → H^q(X)`, is bijective. -/
theorem forgetRel_empty_bijective (q : ℕ) :
    Function.Bijective (forgetRel (TopPair.ofSubset (∅ : Set X)) q) := by
  exact homologyMap_linearDualMap_bijective _ q

/-- The triad cup of two relative cocycles, a cocycle on the triad complex. -/
def triadCupCycles {p q : ℕ}
    (c : (RelativeCochainComplex ℚ (TopPair.ofSubset A)).cycles p)
    (d : (RelativeCochainComplex ℚ (TopPair.ofSubset B)).cycles q) (n : ℕ) (h : p + q = n) :
    (triadChains X A B).linearDualCochainComplex.cycles n :=
  HomologicalComplex.cyclesMap (dualIsoYoneda (triadChains X A B)).inv n
    (TauCeti.ChainComplex.cupCycles ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
      (HomologicalComplex.cyclesMap
        (dualIsoYoneda ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A))).hom p c)
      (HomologicalComplex.cyclesMap
        (dualIsoYoneda ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B))).hom q d))

set_option backward.isDefEq.respectTransparency false in
/-- **`relCup2` on cocycles** is, through triad excision, the class of the triad cup cocycle. -/
theorem triadExcisionCoh_relCup2_homologyπ (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (c : (RelativeCochainComplex ℚ (TopPair.ofSubset A)).cycles p)
    (d : (RelativeCochainComplex ℚ (TopPair.ofSubset B)).cycles q) (n : ℕ) (h : p + q = n) :
    (triadExcisionCoh X A B hA hB n).hom
        (relCup2 X A B hA hB ((RelativeCochainComplex ℚ (TopPair.ofSubset A)).homologyπ p c)
          ((RelativeCochainComplex ℚ (TopPair.ofSubset B)).homologyπ q d) n h) =
      (triadChains X A B).linearDualCochainComplex.homologyπ n (triadCupCycles X A B c d n h) := by
  rw [relCup2, Iso.inv_hom_id_apply]
  unfold triadCohIso relCohIso triadCupCycles
  simp only [HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_inv]
  have hπ : ∀ {K L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (m : ℕ) (x : K.cycles m),
      HomologicalComplex.homologyMap φ m (K.homologyπ m x) =
        L.homologyπ m (HomologicalComplex.cyclesMap φ m x) := by
    intro K L φ m x
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
  erw [hπ, hπ]
  erw [TauCeti.ChainComplex.cup_homologyπ, hπ]

/-- On chains: the triad cup cochain, pulled back to `C(X)`, is the Alexander–Whitney cup of the
two cochains pulled back to `C(X)`. -/
lemma triadProj_cupCochain {p q : ℕ}
    (φ : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).X p ⟶ ModuleCat.of ℚ ℚ)
    (ψ : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).X q ⟶ ModuleCat.of ℚ ℚ)
    (n : ℕ) (h : p + q = n) :
    TauCeti.ChainComplex.cupCochain ℚ (awX X) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
        ((relativeChainProjection ℚ (TopPair.ofSubset A)).f p ≫ φ)
        ((relativeChainProjection ℚ (TopPair.ofSubset B)).f q ≫ ψ) =
      (triadRelativeChainProjection ℚ X A B).f n ≫
        TauCeti.ChainComplex.cupCochain ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
          p q n h φ ψ := by
  have hD : triadRelativeChainProjection ℚ X A B ≫ triadDiagonal X A B =
      awX X ≫ (relativeChainProjection ℚ (TopPair.ofSubset A) ⊗ₘ
        relativeChainProjection ℚ (TopPair.ofSubset B)) := cokernel.π_desc _ _ _
  exact TauCeti.ChainComplex.cupCochain_naturality (k := ℚ) (D := triadDiagonal X A B)
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (awX X) (triadRelativeChainProjection ℚ X A B)
    (relativeChainProjection ℚ (TopPair.ofSubset A))
    (relativeChainProjection ℚ (TopPair.ofSubset B)) hD p q n h φ ψ

end HodgeLadder.Cup
