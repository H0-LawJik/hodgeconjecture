module

public import HodgeConjecture.Variants
public import LefschetzPort.AlgebraicGeometry.LefschetzOneOne

/-!
# Rational Lefschetz (1,1), checked at this repository's pin

The upstream statement of record `LefschetzOneOne` (`Paul-Lez/HodgeConjecture`, `Variants.lean`):
for every smooth projective integral scheme `X` over `ℂ`, every rational Hodge class of degree two
lies in the span of the classes of codimension-one algebraic cycles,
`Hdg^1(X; ℚ) ≤ algebraicCycleClassSpan X 1`.

The proof is the upstream authors' (the Lefschetz (1,1) stack, upstream PRs #217–#226, #9, #230,
#228), ported to the pin in the staging library `LefschetzPort`; see `docs/port-lefschetz.md` for
every change the port made. The port changes proofs only. The statement proved here is upstream's
`Prop`, unchanged, and this file checks it against that `Prop` by definitional unfolding.

This is the inclusion. The equality form (`HodgeLadder.LefschetzOneOneEquality`) also needs the
known half in codimension one (rung `lefschetz-1-1-equality`).

## Main results

* `HodgeLadder.lefschetzOneOne_holds`: `LefschetzOneOne`.
-/

@[expose] public section

namespace HodgeLadder

/-- **Rational Lefschetz (1,1).** The upstream statement of record `LefschetzOneOne` holds: on a
smooth projective integral complex scheme, every rational degree-two Hodge class lies in the span
of codimension-one algebraic cycle classes. -/
theorem lefschetzOneOne_holds : LefschetzOneOne :=
  fun X _ _ _ => lefschetzOneOne X

end HodgeLadder
