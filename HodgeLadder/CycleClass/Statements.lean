module

public import HodgeConjecture.Statement
public import HodgeConjecture.Variants

/-!
# The known half and the equality forms

Upstream states the Hodge conjecture and Lefschetz (1,1) as inclusions
`Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p`. The known half, that cycle classes are Hodge classes,
is a theorem in the literature and is not stated upstream. This file states it, states the
equality forms (decision 0004, equality first), and proves that each equality is equivalent to
the upstream inclusion together with the known half.

These are statements on upstream definitions; nothing here restates the upstream conjecture.

## Main definitions

* `HodgeLadder.CycleClassesAreHodge`: `algebraicCycleClassSpan X p ≤ Hdg^p(X; ℚ)` for all `X`, `p`.
* `HodgeLadder.HodgeConjectureEquality`: `Hdg^p(X; ℚ) = algebraicCycleClassSpan X p`.
* `HodgeLadder.LefschetzOneOneEquality`: the case `p = 1`.

## Main results

* `HodgeLadder.hodgeConjectureEquality_iff`: equality ↔ upstream `HodgeConjecture` ∧ the known half.
* `HodgeLadder.lefschetzOneOneEquality_iff`: equality in codimension one ↔ upstream
  `LefschetzOneOne` ∧ the known half in codimension one.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder

/-- The known half of the Hodge conjecture: the class of every codimension-`p` subvariety of a
smooth projective complex variety is a rational Hodge class. -/
def CycleClassesAreHodge : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ),
    algebraicCycleClassSpan X p ≤ Hdg^p(X; ℚ)

/-- The known half in codimension one. -/
def CycleClassesAreHodgeOne : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
    algebraicCycleClassSpan X 1 ≤ Hdg^1(X; ℚ)

/-- The Hodge conjecture as an equality: the rational Hodge classes of degree `2p` are exactly
the ℚ-span of the classes of codimension-`p` subvarieties. -/
def HodgeConjectureEquality : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ),
    Hdg^p(X; ℚ) = algebraicCycleClassSpan X p

/-- Lefschetz (1,1) as an equality: the rational Hodge classes of degree two are exactly the
ℚ-span of the classes of prime divisors. -/
def LefschetzOneOneEquality : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
    Hdg^1(X; ℚ) = algebraicCycleClassSpan X 1

/-- The equality form is the upstream inclusion together with the known half. -/
theorem hodgeConjectureEquality_iff :
    HodgeConjectureEquality ↔ HodgeConjecture ∧ CycleClassesAreHodge :=
  ⟨fun h => ⟨fun X _ _ _ p => (h X p).le, fun X _ _ _ p => (h X p).ge⟩,
    fun h X _ _ _ p => le_antisymm (h.1 X p) (h.2 X p)⟩

/-- In codimension one, the equality is upstream `LefschetzOneOne` together with the known half
in codimension one. -/
theorem lefschetzOneOneEquality_iff :
    LefschetzOneOneEquality ↔ LefschetzOneOne ∧ CycleClassesAreHodgeOne :=
  ⟨fun h => ⟨fun X _ _ _ => (h X).le, fun X _ _ _ => (h X).ge⟩,
    fun h X _ _ _ => le_antisymm (h.1 X) (h.2 X)⟩

/-- The known half in every codimension gives it in codimension one. -/
theorem cycleClassesAreHodgeOne_of (h : CycleClassesAreHodge) : CycleClassesAreHodgeOne :=
  fun X _ _ _ => h X 1

end HodgeLadder
