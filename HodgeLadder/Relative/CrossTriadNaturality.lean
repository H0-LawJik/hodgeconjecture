module

public import HodgeLadder.Relative.CrossChain

/-!
# Naturality of the relative cross product at the triad level

Rung `relative-cross-triad-naturality` (front `cup`, sub-rung of `local-class-product`), change 2
of the red team of `relative-cross-chain`. A map of triads `f : (X; A, B) → (Y; A', B')`, that is
a map `f : X ⟶ Y` with `f '' A ⊆ A'` and `f '' B ⊆ B'`, induces a chain map of upstream's
sum-relative triad complexes

`C(X) / (C(A) + C(B)) ⟶ C(Y) / (C(A') + C(B'))`,

the descent of the singular chain map of `f` through the two cokernel projections. It commutes
with upstream's comparison `triadToUnionRelativeChainMap` to the union pairs, and the relative
cross product `relCross` of `HodgeLadder.Relative.CrossChain` commutes with it, with no sign:
for maps of pairs `f : (P, A) → (P', A')` and `g : (Q, B) → (Q', B')`,

`relCross (f_* x) (g_* y) = (f × g)^triad_* (relCross x y)`

in `TriadRelativeHomology(P' × Q'; A' × Q', P' × B')` (register row "Relative homology cross
product"). No openness is assumed anywhere. Applying the comparison to both sides gives the form
of `relCrossUnion_naturality` (checked separately in `HodgeLadder.Relative.CrossChain`), by
`triadChainMap_triadToUnionRelativeChainMap`.

## Main definitions

* `HodgeLadder.Relative.triadChainMap`: the chain map of triad complexes induced by a map of
  triads.

## Main results

* `HodgeLadder.Relative.triadRelativeChainProjection_triadChainMap`: it is induced by the chain
  map of `f` on ambient chains.
* `HodgeLadder.Relative.triadChainMap_id`, `HodgeLadder.Relative.triadChainMap_comp`:
  functoriality.
* `HodgeLadder.Relative.triadChainMap_triadToUnionRelativeChainMap`: compatibility with upstream's
  comparison to `C(X, A ∪ B)` along `TopPair.ofSubsetHom f`;
  `HodgeLadder.Relative.triadToUnionRelativeHomologyMap_triadChainMap`: its homology form.
* `HodgeLadder.Relative.relCross_naturality`: naturality of the relative cross product at the
  triad level, no sign.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  HomologicalComplex AlgebraicTopology.Singular

namespace HodgeLadder.Relative

/-- Upstream's map `C(A) ⊞ C(B) ⟶ C(X)`, written with the singular chain functor. -/
lemma triadSubspaceChainMap_eq (X : TopCat.{0}) (A B : Set X) :
    triadSubspaceChainMap ℚ X A B =
      biprod.desc (singChainFunctor.map (TopPair.ofSubset A).map)
        (singChainFunctor.map (TopPair.ofSubset B).map) :=
  rfl

/-- Chains of `A` vanish in the triad complex `C(X) / (C(A) + C(B))`. -/
@[reassoc]
lemma subsetLeft_triadRelativeChainProjection (X : TopCat.{0}) (A B : Set X) :
    singChainFunctor.map (TopPair.ofSubset A).map ≫ triadRelativeChainProjection ℚ X A B = 0 := by
  have h := biprod.inl ≫= triadSubspaceChainMap_triadRelativeChainProjection ℚ X A B
  rw [triadSubspaceChainMap_eq] at h
  erw [biprod.inl_desc_assoc, comp_zero] at h
  exact h

/-- Chains of `B` vanish in the triad complex `C(X) / (C(A) + C(B))`. -/
@[reassoc]
lemma subsetRight_triadRelativeChainProjection (X : TopCat.{0}) (A B : Set X) :
    singChainFunctor.map (TopPair.ofSubset B).map ≫ triadRelativeChainProjection ℚ X A B = 0 := by
  have h := biprod.inr ≫= triadSubspaceChainMap_triadRelativeChainProjection ℚ X A B
  rw [triadSubspaceChainMap_eq] at h
  erw [biprod.inr_desc_assoc, comp_zero] at h
  exact h

/-- A map `f : X ⟶ Y` with `f '' S ⊆ S'` restricts to `S ⟶ S'`, compatibly with the inclusions,
on singular chains. -/
lemma singChainFunctor_map_subset {X Y : TopCat.{0}} (f : X ⟶ Y) {S : Set X} {S' : Set Y}
    (hS : ∀ a ∈ S, f a ∈ S') :
    singChainFunctor.map (TopPair.ofSubset S).map ≫ singChainFunctor.map f =
      singChainFunctor.map (TopPair.Hom.snd (TopPair.ofSubsetHom f hS)) ≫
        singChainFunctor.map (TopPair.ofSubset S').map := by
  have e : (TopPair.ofSubset S).map ≫ f =
      TopPair.Hom.snd (TopPair.ofSubsetHom f hS) ≫ (TopPair.ofSubset S').map := by
    ext; rfl
  exact (singChainFunctor.map_comp _ _).symm.trans
    ((congrArg singChainFunctor.map e).trans (singChainFunctor.map_comp _ _))

/-- A map of triads kills the subspace chains after the triad projection of the target. -/
lemma triadSubspaceChainMap_map_triadRelativeChainProjection {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    triadSubspaceChainMap ℚ X A B ≫ singChainFunctor.map f ≫
      triadRelativeChainProjection ℚ Y A' B' = 0 := by
  have hl : singChainFunctor.map (TopPair.ofSubset A).map ≫ singChainFunctor.map f ≫
      triadRelativeChainProjection ℚ Y A' B' = 0 := by
    refine (Category.assoc _ _ _).symm.trans
      ((singChainFunctor_map_subset f hA =≫ triadRelativeChainProjection ℚ Y A' B').trans ?_)
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (subsetLeft_triadRelativeChainProjection Y A' B')).trans comp_zero)
  have hr : singChainFunctor.map (TopPair.ofSubset B).map ≫ singChainFunctor.map f ≫
      triadRelativeChainProjection ℚ Y A' B' = 0 := by
    refine (Category.assoc _ _ _).symm.trans
      ((singChainFunctor_map_subset f hB =≫ triadRelativeChainProjection ℚ Y A' B').trans ?_)
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (subsetRight_triadRelativeChainProjection Y A' B')).trans comp_zero)
  rw [triadSubspaceChainMap_eq]
  apply biprod.hom_ext'
  · exact (biprod.inl_desc_assoc _ _ _).trans (hl.trans comp_zero.symm)
  · exact (biprod.inr_desc_assoc _ _ _).trans (hr.trans comp_zero.symm)

/-- A map `f : X ⟶ Y` with `f '' A ⊆ A'` and `f '' B ⊆ B'` induces a chain map of upstream's
sum-relative triad complexes. -/
def triadChainMap {X Y : TopCat.{0}} (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y}
    (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    triadRelativeChainComplex ℚ X A B ⟶ triadRelativeChainComplex ℚ Y A' B' :=
  cokernel.desc _ (singChainFunctor.map f ≫ triadRelativeChainProjection ℚ Y A' B')
    (triadSubspaceChainMap_map_triadRelativeChainProjection f hA hB)

/-- `triadChainMap f` is induced by the singular chain map of `f` on ambient chains. -/
@[reassoc]
lemma triadRelativeChainProjection_triadChainMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    triadRelativeChainProjection ℚ X A B ≫ triadChainMap f hA hB =
      singChainFunctor.map f ≫ triadRelativeChainProjection ℚ Y A' B' :=
  cokernel.π_desc _ _ _

/-- The singular chain map of `f` is the simplicial chain map of its singular simplicial set map;
this is the form in which the red team of `relative-cross-chain` wrote
`triadRelativeChainProjection_triadChainMap`. -/
lemma singChainFunctor_map_eq_chainComplexMap {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singChainFunctor.map f = SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) :=
  rfl

/-- The identity of `X` induces the identity of the triad complex. -/
lemma triadChainMap_id (X : TopCat.{0}) (A B : Set X) :
    triadChainMap (𝟙 X) (A := A) (B := B) (fun _ h => h) (fun _ h => h) = 𝟙 _ := by
  have : Epi (triadRelativeChainProjection ℚ X A B) :=
    inferInstanceAs (Epi (cokernel.π (triadSubspaceChainMap ℚ X A B)))
  refine (cancel_epi (triadRelativeChainProjection ℚ X A B)).1 ?_
  refine (triadRelativeChainProjection_triadChainMap (𝟙 X) _ _).trans ?_
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- `triadChainMap` is functorial: a composite of maps of triads induces the composite. -/
lemma triadChainMap_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {A B : Set X} {A' B' : Set Y} {A'' B'' : Set Z}
    (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B')
    (hA' : ∀ a ∈ A', g a ∈ A'') (hB' : ∀ b ∈ B', g b ∈ B'') :
    triadChainMap (f ≫ g) (fun a ha => hA' _ (hA a ha)) (fun b hb => hB' _ (hB b hb)) =
      triadChainMap f hA hB ≫ triadChainMap g hA' hB' := by
  have : Epi (triadRelativeChainProjection ℚ X A B) :=
    inferInstanceAs (Epi (cokernel.π (triadSubspaceChainMap ℚ X A B)))
  refine (cancel_epi (triadRelativeChainProjection ℚ X A B)).1 ?_
  refine (triadRelativeChainProjection_triadChainMap (f ≫ g) _ _).trans ?_
  rw [triadRelativeChainProjection_triadChainMap_assoc, CategoryTheory.Functor.map_comp,
    Category.assoc, triadRelativeChainProjection_triadChainMap]

/-- A map of triads `(X; A, B) → (Y; A', B')` is a map of pairs `(X, A ∪ B) → (Y, A' ∪ B')`. -/
lemma triadMap_mem_union {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    ∀ x ∈ A ∪ B, f x ∈ A' ∪ B' := by
  rintro x (h | h)
  exacts [Or.inl (hA x h), Or.inr (hB x h)]

/-- **`triadChainMap` commutes with upstream's comparison** from the triad complex to the
union-relative complex, along the map of pairs `(X, A ∪ B) → (Y, A' ∪ B')` given by `f`. No
sign. -/
lemma triadChainMap_triadToUnionRelativeChainMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    triadChainMap f hA hB ≫ triadToUnionRelativeChainMap ℚ Y A' B' =
      triadToUnionRelativeChainMap ℚ X A B ≫
        (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f (triadMap_mem_union f hA hB)) := by
  have : Epi (triadRelativeChainProjection ℚ X A B) :=
    inferInstanceAs (Epi (cokernel.π (triadSubspaceChainMap ℚ X A B)))
  refine (cancel_epi (triadRelativeChainProjection ℚ X A B)).1 ?_
  rw [triadRelativeChainProjection_triadChainMap_assoc,
    triadRelativeChainProjection_triadToUnionRelativeChainMap_assoc]
  exact (congrArg (singChainFunctor.map f ≫ ·)
    (triadRelativeChainProjection_triadToUnionRelativeChainMap ℚ Y A' B')).trans
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
        (TopPair.ofSubsetHom f (triadMap_mem_union f hA hB))).symm

/-- **`triadChainMap` commutes with upstream's comparison on homology**: the triad push-forward
followed by `triadToUnionRelativeHomologyMap` is the comparison followed by the push-forward
along the map of pairs `(X, A ∪ B) → (Y, A' ∪ B')`. No sign. -/
lemma triadToUnionRelativeHomologyMap_triadChainMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') (n : ℕ)
    (z : TriadRelativeHomology ℚ X A B n) :
    triadToUnionRelativeHomologyMap ℚ Y A' B' n
        ((HomologicalComplex.homologyMap (triadChainMap f hA hB) n).hom z) =
      relativeHomologyMap ℚ n (TopPair.ofSubsetHom f (triadMap_mem_union f hA hB))
        (triadToUnionRelativeHomologyMap ℚ X A B n z) := by
  have h := congrArg (fun φ : triadRelativeChainComplex ℚ X A B ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (A' ∪ B')) =>
        (HomologicalComplex.homologyMap φ n).hom z)
    (triadChainMap_triadToUnionRelativeChainMap f hA hB)
  simp only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h
  exact h

/-- **Naturality of the relative cross product at the triad level**, an exact equality with no
sign (register row "Relative homology cross product"): the cross product of the images of `x`
and `y` under maps of pairs `f`, `g` is the image of `relCross A B m n x y` under the chain map
of triad complexes induced by `f ⊗ₘ g`. -/
theorem relCross_naturality {P P' Q Q' : TopCat.{0}} (f : P ⟶ P') (g : Q ⟶ Q')
    {A : Set P} {A' : Set P'} {B : Set Q} {B' : Set Q'}
    (hf : ∀ a ∈ A, f a ∈ A') (hg : ∀ b ∈ B, g b ∈ B') {m n : ℕ}
    (x : RelativeHomology ℚ (TopPair.ofSubset A) m)
    (y : RelativeHomology ℚ (TopPair.ofSubset B) n) :
    relCross A' B' m n (relativeHomologyMap ℚ m (TopPair.ofSubsetHom f hf) x)
        (relativeHomologyMap ℚ n (TopPair.ofSubsetHom g hg) y) =
      (HomologicalComplex.homologyMap
        (triadChainMap (f ⊗ₘ g) (A' := leftProdSet A' Q') (B' := rightProdSet P' B')
          (fun _ hz => hf _ hz) (fun _ hz => hg _ hz)) (m + n)).hom
        (relCross A B m n x y) := by
  obtain ⟨zx, rfl⟩ :=
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).moduleCat_homologyπ_surjective m x
  obtain ⟨zy, rfl⟩ :=
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).moduleCat_homologyπ_surjective n y
  obtain ⟨x, hx⟩ : ∃ x : (SingularChainComplex ℚ P).X m,
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x =
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx :=
    relProj_surjective (TopPair.ofSubset A) m _
  obtain ⟨y, hy⟩ : ∃ y : (SingularChainComplex ℚ Q).X n,
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y =
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy :=
    relProj_surjective (TopPair.ofSubset B) n _
  have hx' : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A')).iCycles m).hom
      (HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hf)) m
        zx) =
        ((relativeChainProjection ℚ (TopPair.ofSubset A')).f m).hom
          ((singChainFunctor.map f).f m x) := by
    erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, ← hx]
    exact congrArg (fun φ : SingularChainComplex ℚ P ⟶ _ => (φ.f m).hom x)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) (TopPair.ofSubsetHom f hf))
  have hy' : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B')).iCycles n).hom
      (HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom g hg)) n
        zy) =
        ((relativeChainProjection ℚ (TopPair.ofSubset B')).f n).hom
          ((singChainFunctor.map g).f n y) := by
    erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, ← hy]
    exact congrArg (fun φ : SingularChainComplex ℚ Q ⟶ _ => (φ.f n).hom y)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) (TopPair.ofSubsetHom g hg))
  obtain ⟨z, hz⟩ := exists_triadCycle_shuffle A B x y zx hx.symm zy hy.symm
  obtain ⟨z', hz'⟩ := exists_triadCycle_shuffle A' B' _ _ _ hx' _ hy'
  have lhs := relCross_homologyπ A' B' m n _ _ _ _ z' hx' hy' hz'
  have rhs := relCross_homologyπ A B m n x y zx zy z hx.symm hy.symm hz
  refine (congrArg₂ (fun a b => relCross A' B' m n a b)
    (HomologicalComplex.moduleCat_homologyMap_homologyπ _ _ _)
    (HomologicalComplex.moduleCat_homologyMap_homologyπ _ _ _)).trans (lhs.trans ?_)
  refine Eq.trans ?_ (congrArg _ rhs).symm
  refine Eq.trans ?_ (HomologicalComplex.moduleCat_homologyMap_homologyπ _ _ _).symm
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, hz', hz]
  rw [shuffleBilin_eq_shB, shuffleBilin_eq_shB, shB_naturality]
  exact (congrArg (fun φ : SingularChainComplex ℚ (P ⊗ Q) ⟶ _ =>
    (φ.f (m + n)).hom (shB P Q m n (m + n) rfl x y))
      (triadRelativeChainProjection_triadChainMap (f ⊗ₘ g)
        (A' := leftProdSet A' Q') (B' := rightProdSet P' B')
        (fun _ hz => hf _ hz) (fun _ hz => hg _ hz))).symm

end HodgeLadder.Relative
