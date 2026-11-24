# Acknowledged gaps

A rolling registry. Add an entry when a shortcut is taken or a thread is dropped; close it in the same file with the date and the commit that closed it.

## To upstream to Mathlib

| Local declaration | Module | Why local | Opened |
|---|---|---|---|
| `AlgebraicCycle.IsCodim`, `codimCycles` | `HodgeConjecture.Cycles.Codimension` | Mathlib has only the `p = 1` case (`IsWeilDivisor`). Candidate for a short Mathlib PR. | 2026-11-23 |

## Known weaknesses

| Gap | Impact | Opened |
|---|---|---|
| `IsCodim` is indexed by `ℕ∞` because `Order.coheight` is; the literature uses `ℕ`. Decide whether `Z^p` for finite `p` should be the primary object before `rational-equivalence` builds on it. | Possible churn in one module | 2026-11-23 |
| Singular cohomology with coefficients is missing from Mathlib (only homology exists). Every analytic rung depends on a choice between building cohomology, or stating the conjecture against de Rham cohomology alone. | Shapes the `statement` rung | 2026-11-23 |

## Dead ends

None yet.

## Dropped threads

None yet.
