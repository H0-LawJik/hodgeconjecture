module

public import HodgeLadder.Relative.CrossTriadNaturality
public import HodgeLadder.Local.CrossOrientation
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity

/-!
# Non-vacuity of the triad-level naturality of the relative cross product

Rung `relative-cross-triad-naturality-test`. The triad push-forward of `relCross` along a map
that is not the identity is nonzero: along `complexAppendMap a b : ℂ^a × ℂ^b → ℂ^{a+b}`, from the
triad `(ℂ^a × ℂ^b; (ℂ^a ∖ 0) × ℂ^b, ℂ^a × (ℂ^b ∖ 0))` to `(ℂ^{a+b}; setA, setB)`, the push-forward
of the cross product of upstream's complex orientation classes maps under upstream's comparison
to `orient a b`, which is nonzero. This is the shape `local-class-cross-model` reads on its cap
route.

## Main results

* `HodgeLadder.Tests.orient_eq_triadToUnion_triadChainMap`: `orient a b` is the comparison image
  of the triad push-forward of `relCross` along `complexAppendMap`.
* `HodgeLadder.Tests.orient_ne_zero`: `orient a b ≠ 0`.
* `HodgeLadder.Tests.triadChainMap_relCross_orientation_ne_zero`: the triad push-forward is
  nonzero for every `a, b`.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
open HodgeLadder.Relative HodgeLadder.CrossOrientation

namespace HodgeLadder.Tests

/-- `complexAppendMap` sends `(ℂ^a ∖ 0) × ℂ^b` into `setA`. -/
lemma complexAppendMap_mem_setA (a b : ℕ) :
    ∀ z ∈ leftProdSet (P := TopCat.of (Fin a → ℂ)) ({0}ᶜ : Set (Fin a → ℂ))
        (TopCat.of (Fin b → ℂ)), complexAppendMap a b z ∈ setA a b := by
  intro z hz h
  exact hz (funext fun i => (Fin.append_left z.1 z.2 i).symm.trans (congrFun h i))

/-- `complexAppendMap` sends `ℂ^a × (ℂ^b ∖ 0)` into `setB`. -/
lemma complexAppendMap_mem_setB (a b : ℕ) :
    ∀ z ∈ rightProdSet (TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
        ({0}ᶜ : Set (Fin b → ℂ)), complexAppendMap a b z ∈ setB a b := by
  intro z hz h
  exact hz (funext fun j => (Fin.append_right z.1 z.2 j).symm.trans (congrFun h j))

/-- **`orient a b` is the comparison image of the triad push-forward of the cross product** of
upstream's complex orientation classes along `complexAppendMap`. No sign. -/
theorem orient_eq_triadToUnion_triadChainMap (a b : ℕ) :
    orient a b =
      triadToUnionRelativeHomologyMap ℚ (TopCat.of (Fin (a + b) → ℂ)) (setA a b) (setB a b)
        (2 * a + 2 * b)
        ((HomologicalComplex.homologyMap
          (triadChainMap (complexAppendMap a b) (complexAppendMap_mem_setA a b)
            (complexAppendMap_mem_setB a b)) (2 * a + 2 * b)).hom
          (relCross (P := TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
            ({0}ᶜ : Set (Fin a → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)) (2 * a) (2 * b)
            (standardComplexLocalClass ℚ a) (standardComplexLocalClass ℚ b))) := by
  rw [triadToUnionRelativeHomologyMap_triadChainMap, ← cross_orientation_orient]
  rfl

/-- Upstream's complex orientation class on `(ℂ^{a+b}, setA ∪ setB)` is nonzero. -/
theorem orient_ne_zero (a b : ℕ) : orient a b ≠ 0 := by
  have key : ∀ {d d' : ℕ} (h : d = d')
      (x : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (Fin (a + b) → ℂ))
        (setA a b ∪ setB a b)) d), x ≠ 0 → (h ▸ x) ≠ 0 := by
    intro d d' h x hx; subst h; exact hx
  apply key
  intro h0
  apply standardComplexLocalClass_ne_zero (a + b)
  have := congrArg (relativeHomologyMap ℚ (2 * (a + b))
    (TopPair.isoOfSubset (Homeomorph.refl _) (fun z => union_eq a b z)).inv) h0
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, Iso.hom_inv_id,
    relativeHomologyMap_id] at this
  simpa using this

/-- **The triad push-forward of the cross product of orientations is nonzero** for every `a, b`,
so `relCross_naturality` and `triadChainMap` are not vacuous along a map that is not the
identity. -/
theorem triadChainMap_relCross_orientation_ne_zero (a b : ℕ) :
    (HomologicalComplex.homologyMap
          (triadChainMap (complexAppendMap a b) (complexAppendMap_mem_setA a b)
            (complexAppendMap_mem_setB a b)) (2 * a + 2 * b)).hom
          (relCross (P := TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
            ({0}ᶜ : Set (Fin a → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)) (2 * a) (2 * b)
            (standardComplexLocalClass ℚ a) (standardComplexLocalClass ℚ b)) ≠ 0 := by
  intro h
  apply orient_ne_zero a b
  rw [orient_eq_triadToUnion_triadChainMap, h, map_zero]

end HodgeLadder.Tests
