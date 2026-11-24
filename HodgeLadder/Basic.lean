module

public import Mathlib.Data.Nat.Basic

/-!
# HodgeLadder.Basic

Namespace preamble and a toolchain smoke test.
-/

@[expose] public section

namespace HodgeLadder

/-- Toolchain smoke test. Kept so a broken pin fails here, with a short error. -/
theorem toolchain_ok : (1 : ℕ) + 1 = 2 := rfl

end HodgeLadder
