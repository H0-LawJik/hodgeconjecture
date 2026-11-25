/-
Copyright (c) 2026 The Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Port supplement: coface maps of the simplex category on elements

Mathlib after the pin states, in `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean`
(section `Concrete`, at Mathlib commit `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`), that the
coface map `SimplexCategory.δ i` sends `j` to `Fin.succAbove i j`. The pin has the function-level
form `SimplexCategory.coe_δ` only. The Tau Ceti file
`LefschetzPort.TauCeti.AlgebraicTopology.SimplexCategory.Subinterval` rewrites with the pointwise
form, so it is copied here, in the `LefschetzPort` namespace so that it does not clash with
Mathlib's declaration after a pin bump. See `docs/port-tauceti.md`, batch H2.

## Main results

* `LefschetzPort.SimplexCategory.δ_apply`: `SimplexCategory.δ i j = Fin.succAbove i j`.
-/

@[expose] public section

namespace LefschetzPort.SimplexCategory

/-- The coface map `SimplexCategory.δ i` sends `j` to `Fin.succAbove i j` (Mathlib's
`SimplexCategory.δ_apply` after the pin). -/
lemma δ_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    _root_.SimplexCategory.δ i j = Fin.succAbove i j := rfl

end LefschetzPort.SimplexCategory
