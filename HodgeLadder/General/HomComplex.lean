module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Composition lemmas for Hom-complex cocycles

General facts about Mathlib's Hom complex `CochainComplex.HomComplex`, for cochain complexes
indexed by `ℤ` in a preadditive category: precomposing or postcomposing a cocycle twice is
composing once with the composite, and the identification `Cochain.fromSingleEquiv` of cochains
out of a single complex carries composition with a map of single complexes, or with a chain map,
to composition in the category. They are used for the classes of named cocycles on the front
`cup`; the classes of composites themselves are in `HodgeLadder.Cup.CocycleClass`.

## Main results

* `HodgeLadder.HomComplex.cocycle_precomp_precomp`,
  `HodgeLadder.HomComplex.cocycle_postcomp_postcomp`
* `HodgeLadder.HomComplex.fromSingleEquiv_ofHom_comp`,
  `HodgeLadder.HomComplex.fromSingleEquiv_comp_ofHom`
* `HodgeLadder.HomComplex.fromSingleEquiv_cocycle_precomp_single`: the cocycle form of
  `fromSingleEquiv_ofHom_comp`
-/

@[expose] public section

open CategoryTheory CochainComplex HomComplex

namespace HodgeLadder.HomComplex

variable {C : Type*} [Category C] [Preadditive C]

/-- **Precomposing a cocycle twice is precomposing once with the composite.** -/
lemma cocycle_precomp_precomp {F F' G K : CochainComplex C ℤ} {n : ℤ} (z : Cocycle G K n)
    (g : F ⟶ G) (f : F' ⟶ F) :
    (z.precomp g).precomp f = z.precomp (f ≫ g) := by
  ext : 1
  simp [Cocycle.precomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

/-- **Postcomposing a cocycle twice is postcomposing once with the composite.** -/
lemma cocycle_postcomp_postcomp {F G K K' : CochainComplex C ℤ} {n : ℤ} (z : Cocycle F G n)
    (g : G ⟶ K) (f : K ⟶ K') :
    (z.postcomp g).postcomp f = z.postcomp (g ≫ f) := by
  ext : 1
  simp [Cocycle.postcomp, Cochain.ofHom_comp]

variable [Limits.HasZeroObject C]

/-- **`fromSingleEquiv` carries precomposition with a map of single complexes to composition**:
for `g : X' ⟶ X` and a cochain `α` out of `X` placed in degree `p`, the morphism attached to
`ofHom (single g) ∘ α` is `g ≫ fromSingleEquiv α`. -/
lemma fromSingleEquiv_ofHom_comp {X X' : C} {K : CochainComplex C ℤ} (g : X' ⟶ X)
    {p q n : ℤ} (h : p + n = q) (α : Cochain ((singleFunctor C p).obj X) K n) :
    Cochain.fromSingleEquiv h
        ((Cochain.ofHom ((singleFunctor C p).map g)).comp α (zero_add n)) =
      g ≫ Cochain.fromSingleEquiv h α := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective α q h
  rw [← Cochain.fromSingleMk_precomp, Cochain.fromSingleEquiv_fromSingleMk,
    Cochain.fromSingleEquiv_fromSingleMk]

/-- **`fromSingleEquiv` carries postcomposition with a chain map to composition**: for a chain
map `g : K ⟶ L`, the morphism attached to `α ∘ ofHom g` is `fromSingleEquiv α ≫ g.f q`. -/
lemma fromSingleEquiv_comp_ofHom {X : C} {K L : CochainComplex C ℤ} (g : K ⟶ L)
    {p q n : ℤ} (h : p + n = q) (α : Cochain ((singleFunctor C p).obj X) K n) :
    Cochain.fromSingleEquiv h (α.comp (Cochain.ofHom g) (add_zero n)) =
      Cochain.fromSingleEquiv h α ≫ g.f q := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective α q h
  rw [← Cochain.fromSingleMk_postcomp, Cochain.fromSingleEquiv_fromSingleMk,
    Cochain.fromSingleEquiv_fromSingleMk]

/-- The cocycle form of `fromSingleEquiv_ofHom_comp`: precomposing a cocycle out of a single
complex with the image of `g : X' ⟶ X` composes the attached morphism with `g`. -/
lemma fromSingleEquiv_cocycle_precomp_single {X X' : C} {L : CochainComplex C ℤ}
    {p q n : ℤ} (h : p + n = q) (z : Cocycle ((singleFunctor C p).obj X) L n) (g : X' ⟶ X) :
    Cochain.fromSingleEquiv h (z.precomp ((singleFunctor C p).map g)).1 =
      g ≫ Cochain.fromSingleEquiv h z.1 :=
  fromSingleEquiv_ofHom_comp g h z.1

end HodgeLadder.HomComplex
