# 0012. Close the cup-product front: won

Date: 2026-11-27. Status: accepted. Closes the front opened by decision 0008, as amended by decisions 0009 and 0010.

## Context

Decision 0009 ordered the front in eight rungs. With `cup-hodge-filtration` and `cup-hodge-classes` checked (red team `docs/sketches/cup-hodge-filtration-checked.redteam.md`), all eight are checked:

| Item | Rung | Checked result |
|---|---|---|
| 1 | `cup-pullback` | pullback along a morphism is multiplicative |
| 2 | `sheaf-tensor-exact` | the tensor of sheaves of ℚ-vector spaces is exact |
| 3 | `supported-cup` | supported times absolute, compatible with forgetting the support |
| 4 | `cup-singular-comparison` | the Yoneda cup goes to the singular cup, sign fixed exactly |
| 5 | `local-class-product` | product of normalized local classes of transversal components |
| 6 | `cycle-class-multiplicative` (with `cycle-class-multiplicative-no-reg`) | [Z] ∪ [W] = [T] for a transversal intersection with one integral component, sign + |
| 7 | `cup-graded-commutative` | α ∪ β = (−1)^{pq} β ∪ α |
| 8 | `cup-hodge-filtration`, `cup-hodge-classes` | F^p ∪ F^q ⊆ F^{p+q} for the de Rham cup; Hdg^p ∪ Hdg^q ⊆ Hdg^{p+q} |

The product itself (`cup-product`: associative, unital, biadditive) and the vacuity test of decision 0009 (`cup-positive-degree-test-p2`: [L₀] ∪ [L₁] = [pt] ≠ 0 on ℙ²) are checked. The win condition of `docs/strategy.md` asks for a checked associative, unital, graded-commutative cup product compatible with the cycle class map; compatibility is read as decision 0010 fixes it, the transversal case with one integral component.

## Decision

Close front `cup` as won. Its ledger rung `cup-front` becomes `checked`, with module `HodgeLadder` and the headline declarations `HodgeLadder.Cup.cup_assoc`, `HodgeLadder.Cup.one_cup`, `HodgeLadder.Cup.cup_one`, `HodgeLadder.Cup.cup_gradedComm`, `HodgeLadder.Cup.cup_singular_comparison'`, `HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal_noReg`, `HodgeLadder.Tests.planeLines_cup_eq_planeOrigin`, `HodgeLadder.cupPreservesHodgeClasses_holds`. The kill criteria of decisions 0009 and 0010 lapse.

## Consequences

- M2 and M3 are no longer blocked by the front. The next M2 rung is T1 of the Markman inventory (`docs/notes/2026-11-25-markman-inventory.md` §6); its inputs `de-rham-cup-antisymm-h1` and `de-rham-cup-unique`, outside the closed front, are checked (#220).
- `cup-positive-degree-test` (ℙ¹ × ℙ¹) stays open as a test; its product identity `cycle-class-multiplicative-p1p1` is checked.
- Non-transversal products of cycle classes (excess intersection, multiplicities) were outside the front's scope and have no rung; a rung for them opens a new front or joins an existing one by its own decision.
- The rungs that depend on `cup-front` keep that dependency; the front rung keeps `depends_on: ["upstream-statement"]`, so the ledger has no cycle.
