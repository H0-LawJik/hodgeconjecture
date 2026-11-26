module

public import HodgeLadder.Cup.TriadCup
public import HodgeLadder.Relative.CrossTriadNaturality
public import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.FundamentalClass
public import Mathlib.Topology.Sets.Closeds

/-!
# Naturality of the triad relative cup product

Rung `triad-relative-cup-naturality` (front `cup`, decision 0010). For a continuous map
`f : X' → X` with `f(A') ⊆ A` and `f(B') ⊆ B`, all four subsets open, pulling back along `f`
carries the relative-relative cup `relCup2 : H^p(X, A) × H^q(X, B) → H^{p+q}(X, A ∪ B)` of
rung `triad-relative-cup` to the one of `(X'; A', B')`, with no sign:
`f^* (relCup2 a b) = relCup2 (f^* a) (f^* b)`. The three pullbacks are upstream's
`relativeCohomologyMap` along the maps of pairs `TopPair.ofSubsetHom f _` on `(X', A')`,
`(X', B')` and `(X', A' ∪ B')`.

Conventions (`docs/conventions.md`, row "Triad relative cup product"): the `A` factor is first,
front face times back face, no sign. Pulling back along a map of spaces multiplies by no scalar,
so the identity is exact. The chain map of a map of triads is `HodgeLadder.Relative.triadChainMap`
(rung `relative-cross-triad-naturality`); this file adds its compatibility with the triad
diagonal.

## Main definitions

* `HodgeLadder.Cup.restrictToNeighborhood`: the map of pairs `(V, V ∖ Z) → (Y, Y ∖ Z)` given by
  the inclusion of a subset `V`, from upstream's `neighborhoodSupportComplementPair V Z` to the
  pair `TopPair.ofSubset Z.compl` in which the supported comparison lands

## Main results

* `HodgeLadder.Cup.relCup2_naturality`: naturality along `TopPair.ofSubsetHom f`
* `HodgeLadder.Cup.relCup2_naturality_of_fst`: the same for any three maps of pairs between the
  `TopPair.ofSubset` pairs whose map of ambient spaces is `f` (for maps built otherwise, such as
  upstream's `neighborhoodSupportInclusionPairMap` or a composite with an isomorphism of pairs)
* `HodgeLadder.Cup.relCup2_restrict`: restriction to a subset `V` of `Y`, in the spelling of
  the supported comparison (`Z.compl` for `Z : Closeds Y`) and of upstream's
  `neighborhoodSupportComplementPair`
* `HodgeLadder.Cup.eq_ofSubsetHom`: a map of `TopPair.ofSubset` pairs is `TopPair.ofSubsetHom`
  of its ambient map
* `HodgeLadder.Cup.triadChainMap_triadDiagonal`: the triad diagonal is natural along
  `HodgeLadder.Relative.triadChainMap`, no sign
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory TopologicalSpace AlgebraicTopology.Singular

namespace HodgeLadder.Cup

section Pairs

variable {X X' : TopCat.{0}}

/-- A map of `TopPair.ofSubset` pairs sends the subspace into the subspace. -/
theorem mem_of_pairHom {A' : Set X'} {A : Set X}
    (g : TopPair.ofSubset A' ⟶ TopPair.ofSubset A) :
    ∀ x ∈ A', TopPair.Hom.fst g x ∈ A := by
  intro x hx
  have h := TopPair.Hom.w_apply g ⟨x, hx⟩
  have hmem : (TopPair.ofSubset A).map (TopPair.Hom.snd g ⟨x, hx⟩) ∈ A :=
    (TopPair.Hom.snd g ⟨x, hx⟩).2
  rw [h] at hmem
  exact hmem

/-- **A map of `TopPair.ofSubset` pairs is determined by its ambient map**: it is upstream's
`TopPair.ofSubsetHom` of that map. -/
theorem eq_ofSubsetHom {A' : Set X'} {A : Set X}
    (g : TopPair.ofSubset A' ⟶ TopPair.ofSubset A) :
    g = TopPair.ofSubsetHom (TopPair.Hom.fst g) (mem_of_pairHom g) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext a
    apply Subtype.ext
    have h := TopPair.Hom.w_apply g a
    exact h
  · rfl

/-- A map of `TopPair.ofSubset` pairs with ambient map `f` is `TopPair.ofSubsetHom f`. -/
theorem eq_ofSubsetHom_of_fst {A' : Set X'} {A : Set X} (f : X' ⟶ X)
    (g : TopPair.ofSubset A' ⟶ TopPair.ofSubset A) (hg : TopPair.Hom.fst g = f) :
    g = TopPair.ofSubsetHom f (hg ▸ mem_of_pairHom g) := by
  subst hg
  exact eq_ofSubsetHom g

end Pairs

section TriadChains

set_option backward.isDefEq.respectTransparency false in
/-- **The triad diagonal is natural for maps of triads**: `Relative.triadChainMap` followed by the
diagonal of `(X; A, B)` is the diagonal of `(X'; A', B')` followed by the tensor product of the
relative chain maps of `f`. No sign. -/
theorem triadChainMap_triadDiagonal {X X' : TopCat.{0}} (f : X' ⟶ X) {A B : Set X}
    {A' B' : Set X'} (hfA : ∀ x ∈ A', f x ∈ A) (hfB : ∀ x ∈ B', f x ∈ B) :
    HodgeLadder.Relative.triadChainMap f hfA hfB ≫ triadDiagonal X A B =
      triadDiagonal X' A' B' ≫ ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hfA) ⊗ₘ
        (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hfB)) := by
  have : Epi (triadRelativeChainProjection ℚ X' A' B') := by
    change Epi (cokernel.π _); infer_instance
  rw [← cancel_epi (triadRelativeChainProjection ℚ X' A' B'),
    HodgeLadder.Relative.triadRelativeChainProjection_triadChainMap_assoc]
  erw [cokernel.π_desc, ← Category.assoc (cokernel.π _), cokernel.π_desc]
  have hn := TopCat.alexanderWhitneyDiagonal_naturality f (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc, Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  rw [TopPair.Homotopy.relativeChainProjection_naturality,
    TopPair.Homotopy.relativeChainProjection_naturality]
  rfl

end TriadChains

section Naturality

variable {X X' : TopCat.{0}}

set_option backward.isDefEq.respectTransparency false in
/-- **The triad relative cup is natural for maps of triads**, no sign. For `f : X' → X` with
`f(A') ⊆ A` and `f(B') ⊆ B`, all four open, pulling back along `f` on `(X', A' ∪ B')` carries
`relCup2 a b` to `relCup2` of the pullbacks of `a` on `(X', A')` and of `b` on `(X', B')`. -/
theorem relCup2_naturality (f : X' ⟶ X) {A B : Set X} {A' B' : Set X'}
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B')
    (hfA : ∀ x ∈ A', f x ∈ A) (hfB : ∀ x ∈ B', f x ∈ B) {p q : ℕ}
    (a : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset B) q) (n : ℕ) (h : p + q = n) :
    relativeCohomologyMap ℚ n
        (TopPair.ofSubsetHom f (HodgeLadder.Relative.triadMap_mem_union f hfA hfB))
        (relCup2 X A B hA hB a b n h) =
      relCup2 X' A' B' hA' hB'
        (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hfA) a)
        (relativeCohomologyMap ℚ q (TopPair.ofSubsetHom f hfB) b) n h := by
  apply (triadExcisionCoh X' A' B' hA' hB' n).toLinearEquiv.injective
  apply (triadCohIso X' A' B' n).toLinearEquiv.injective
  change (triadCohIso X' A' B' n).hom ((triadExcisionCoh X' A' B' hA' hB' n).hom _) =
    (triadCohIso X' A' B' n).hom ((triadExcisionCoh X' A' B' hA' hB' n).hom _)
  have hL : ∀ z, (triadExcisionCoh X' A' B' hA' hB' n).hom
      (relativeCohomologyMap ℚ n
        (TopPair.ofSubsetHom f (HodgeLadder.Relative.triadMap_mem_union f hfA hfB)) z) =
      HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        (HodgeLadder.Relative.triadChainMap f hfA hfB)) n
        ((triadExcisionCoh X A B hA hB n).hom z) := by
    intro z
    have e := congrArg (fun φ => HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap φ) n)
      (HodgeLadder.Relative.triadChainMap_triadToUnionRelativeChainMap f hfA hfB)
    simp only [HomologicalComplex.linearDualMap_comp, HomologicalComplex.homologyMap_comp] at e
    exact (ConcreteCategory.congr_hom e z).symm
  rw [hL, relCup2, Iso.inv_hom_id_apply, relCup2, Iso.inv_hom_id_apply]
  change HomologicalComplex.homologyMap (dualIsoYoneda _).hom n _ = _
  rw [homologyMap_dualIsoYoneda_apply]
  have e4 : ∀ c, HomologicalComplex.homologyMap (dualIsoYoneda (triadChains X A B)).hom n
      ((triadCohIso X A B n).inv c) = c := fun c => Iso.inv_hom_id_apply (triadCohIso X A B n) c
  rw [e4, Iso.inv_hom_id_apply, relCohIso_map, relCohIso_map]
  have hn := TauCeti.ChainComplex.cup_naturality (k := ℚ) (D := triadDiagonal X A B)
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (triadDiagonal X' A' B')
    (HodgeLadder.Relative.triadChainMap f hfA hfB)
    ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hfA))
    ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hfB))
    (triadChainMap_triadDiagonal f hfA hfB) p q n h
    ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b)
  exact hn.symm

/-- **Naturality for maps of pairs given with a common ambient map**, no sign: any three maps of
pairs `(X', A') → (X, A)`, `(X', B') → (X, B)`, `(X', A' ∪ B') → (X, A ∪ B)` whose maps of
ambient spaces are one map `f`. -/
theorem relCup2_naturality_of_fst (f : X' ⟶ X) {A B : Set X} {A' B' : Set X'}
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B')
    (gA : TopPair.ofSubset A' ⟶ TopPair.ofSubset A)
    (gB : TopPair.ofSubset B' ⟶ TopPair.ofSubset B)
    (g : TopPair.ofSubset (A' ∪ B') ⟶ TopPair.ofSubset (A ∪ B))
    (hgA : TopPair.Hom.fst gA = f) (hgB : TopPair.Hom.fst gB = f) (hg : TopPair.Hom.fst g = f)
    {p q : ℕ} (a : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset B) q) (n : ℕ) (h : p + q = n) :
    relativeCohomologyMap ℚ n g (relCup2 X A B hA hB a b n h) =
      relCup2 X' A' B' hA' hB' (relativeCohomologyMap ℚ p gA a)
        (relativeCohomologyMap ℚ q gB b) n h := by
  rw [eq_ofSubsetHom_of_fst f gA hgA, eq_ofSubsetHom_of_fst f gB hgB, eq_ofSubsetHom_of_fst f g hg]
  exact relCup2_naturality f hA hB hA' hB' _ _ a b n h

end Naturality

section Restriction

variable {Y : Type} [TopologicalSpace Y]

/-- The inclusion of a subset `V` of `Y` as a map of spaces. -/
abbrev subsetInclusion (V : Set Y) : TopCat.of V ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of `V` sends `V ∖ Z` into `Y ∖ Z`. -/
theorem mem_compl_of_neighborhood (V : Set Y) (Z : Closeds Y) :
    ∀ w ∈ {w : V | w.1 ∉ (Z : Set Y)}, subsetInclusion V w ∈ (Z.compl : Set Y) :=
  fun _ hw => hw

/-- **Restriction to a subset**, as a map of pairs `(V, V ∖ Z) → (Y, Y ∖ Z)`: the inclusion of
`V`, from upstream's `neighborhoodSupportComplementPair V Z` to `TopPair.ofSubset Z.compl`, the
spelling of the codomain of the supported comparison (`supportedEquivPair`). -/
def restrictToNeighborhood (V : Set Y) (Z : Closeds Y) :
    neighborhoodSupportComplementPair V (Z : Set Y) ⟶
      TopPair.ofSubset (X := TopCat.of Y) (Z.compl : Set Y) :=
  TopPair.ofSubsetHom (subsetInclusion V) (mem_compl_of_neighborhood V Z)

/-- In a subset `V`, the complement of a closed set is open. -/
theorem isOpen_neighborhoodComplement (V : Set Y) (Z : Closeds Y) :
    IsOpen {w : V | w.1 ∉ (Z : Set Y)} :=
  Z.compl.isOpen.preimage continuous_subtype_val

/-- **Restriction of the triad relative cup to a subset `V`**, no sign: in the spelling of the
supported comparison on `Y` and of upstream's `neighborhoodSupportComplementPair` on `V`, the
restriction of `relCup2 a b` from `(Y, Y ∖ Z ∪ Y ∖ W)` to `(V, V ∖ Z ∪ V ∖ W)` is `relCup2` of
the restrictions of `a` and `b`. `V` need not be open. -/
theorem relCup2_restrict (V : Set Y) (Z W : Closeds Y) {p q : ℕ}
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of Y) (Z.compl : Set Y)) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of Y) (W.compl : Set Y)) q)
    (n : ℕ) (h : p + q = n) :
    relativeCohomologyMap ℚ n
        (TopPair.ofSubsetHom (subsetInclusion V)
          (HodgeLadder.Relative.triadMap_mem_union (subsetInclusion V)
            (mem_compl_of_neighborhood V Z) (mem_compl_of_neighborhood V W)) :
          TopPair.ofSubset ({w : V | w.1 ∉ (Z : Set Y)} ∪ {w : V | w.1 ∉ (W : Set Y)}) ⟶
            TopPair.ofSubset (X := TopCat.of Y) ((Z.compl : Set Y) ∪ (W.compl : Set Y)))
        (relCup2 (TopCat.of Y) (Z.compl : Set Y) (W.compl : Set Y) Z.compl.isOpen W.compl.isOpen
          a b n h) =
      relCup2 (TopCat.of V) {w : V | w.1 ∉ (Z : Set Y)} {w : V | w.1 ∉ (W : Set Y)}
        (isOpen_neighborhoodComplement V Z) (isOpen_neighborhoodComplement V W)
        (relativeCohomologyMap ℚ p (restrictToNeighborhood V Z) a)
        (relativeCohomologyMap ℚ q (restrictToNeighborhood V W) b) n h :=
  relCup2_naturality (subsetInclusion V) _ _ _ _ _ _ a b n h

end Restriction

end HodgeLadder.Cup
