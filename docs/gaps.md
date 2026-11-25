# Acknowledged gaps

A rolling registry. Add an entry when a shortcut is taken or a thread is dropped; close it in the same file with the date and the commit that closed it.

## To upstream to Mathlib

| Local declaration | Module | Why local | Opened |
|---|---|---|---|
| `codimCycles_one` (codimension one equals Mathlib `weilDivisors`), `codimCycles_inf_eq_bot` (distinct codimensions meet in zero) | removed from this repository (decision 0003); recoverable from git history at `ba3dbef` | Upstream `codimensionCycleSubgroup` lacks these two facts; offer them to `Paul-Lez/HodgeConjecture` as lemmas on its subgroup | 2026-11-24 |
| Regular local rings are UFDs (Auslander–Buchsbaum); needed for `prime-divisors-cartier` | not yet written | Mathlib has `IsRegularLocalRing`; factoriality is missing there and is general commutative algebra | 2026-11-24 |

## Known weaknesses

| Gap | Impact | Opened |
|---|---|---|
| Three Lean pins in play: upstream v4.35.0-rc4 (followed here), the Lefschetz stack v4.33.1, Tau Ceti v4.37.0-rc1 (Mathlib master) | Reuse of Tau Ceti material needs a backport or a wait | 2026-11-24 |
| Building this repository compiles upstream's statement import closure; CI time grows | Watch CI duration | 2026-11-24 |
| The upstream Lefschetz stack is resolved: it builds at the pin in `port/LefschetzPort` (`lefschetz-port` checked). Kept for the record | none now | 2026-11-24 |
| The port declares `CategoryTheory.Sheaf.H.δ` (`port/LefschetzPort/CategoryTheory/Sites/SheafCohomology/Connecting.lean:24`), a name Mathlib also declares at the pin (`Mathlib/CategoryTheory/Sites/SheafCohomology/ExactSequences.lean`); importing both fails. Bodies agree, no sign differs (red team M1). Global data instances on Mathlib's `Sheaf` in `CategoryTheory/Sites/Forget.lean` carry the same risk (L7) | A future pin or import that reaches the Mathlib module breaks the port build; rename the port's copy or switch to Mathlib's `H.δ hS 1 2 rfl` before the next pin bump | 2026-11-24 |
| Two staged modules have no counterpart at the verified head (`ChernWindingRawBoundary.lean`, `HolomorphicExponentialSupportWinding.lean`), and `relBaseSubmoduleAddSubgroupClass` is a global `Prop` instance, not a local one (red team L2, L3) | none for truth; hygiene | 2026-11-24 |

## Process items to investigate

| Item | Why | Opened |
|---|---|---|
| How the 2026-11-20 RH Lean proof was certified against its statement (statement-comparison tool, what it checks) | Adopt for `lefschetz-1-1` and the port; `docs/notes/2026-11-24-spinors-characters-tests.md` §4 | 2026-11-24 |
| Candidate front `fermat` (character sieve on Fermat varieties) | Needs a decision record and a first rung; research note §2 | 2026-11-24 |

## Dead ends

| Thread | Why it died | Date |
|---|---|---|
| Interface-first statement (`hodge-interface`, `statement-interface` and the cases built on it) | Interface statements of this conjecture are vacuous or false (LeanDojo regression tests); real definitions exist upstream (decision 0003) | 2026-11-24 |
| Own foundations for stating the conjecture (`de-rham`, `complex-analytic-space`, `hodge-decomposition`, `cycle-class`) | Upstream already defines them on real objects (decision 0003) | 2026-11-24 |

## Dropped threads

None yet.
