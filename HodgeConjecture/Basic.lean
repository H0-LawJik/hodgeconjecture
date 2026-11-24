module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# HodgeConjecture.Basic

Shared preamble for the development: the namespace, the universe conventions, and nothing else.
Real content lives in the topic modules listed in `HodgeConjecture.lean`.
-/

namespace HodgeConjecture

/-- Toolchain smoke test. Kept so a broken Mathlib pin fails here, with a short error. -/
theorem toolchain_ok : (1 : ℕ) + 1 = 2 := rfl

end HodgeConjecture
