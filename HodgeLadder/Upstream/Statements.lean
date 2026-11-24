module

public import HodgeConjecture.Statement
public import HodgeConjecture.Variants

/-!
# The statements of record

The Hodge conjecture and its special cases are stated in the upstream project
`Paul-Lez/HodgeConjecture` (library `HodgeConjecture`), pinned in `lakefile.toml`. This project
proves things about those statements and does not restate them. See
`docs/decisions/0003-rebase-on-upstream-statement.md`.

## Main results

* `HodgeLadder.lefschetzOneOne_of_hodgeConjecture`: the upstream Lefschetz (1,1) statement is the
  `p = 1` instance of the upstream Hodge conjecture. This checks that the two statements of record
  use the same objects, with no cast or reindexing between them.
* `HodgeLadder.dimensionLE_of_hodgeConjecture`: the same for the low-dimension variant.
-/

@[expose] public section

namespace HodgeLadder

/-- The upstream Lefschetz (1,1) statement is the codimension-one instance of the upstream Hodge
conjecture, by definitional unfolding alone. -/
theorem lefschetzOneOne_of_hodgeConjecture (h : HodgeConjecture) : LefschetzOneOne :=
  fun X _ _ _ => h X 1

/-- The upstream low-dimension variant follows from the upstream Hodge conjecture by discarding
the dimension hypothesis. -/
theorem dimensionLE_of_hodgeConjecture (h : HodgeConjecture) (n : ℕ) :
    HodgeConjectureInDimensionLE n :=
  fun X _ _ _ _ p => h X p

end HodgeLadder
