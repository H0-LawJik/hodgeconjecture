# Conformance audit, 2026-11-24

Checks of this repository's outline against the 2025–2026 literature, in two parts. Load-bearing claims were verified against the primary repository or the arXiv record; the rest are marked as reported by the research pass.

## Formalization

| Finding | Evidence | Verified | Consequence |
|---|---|---|---|
| A sorry-free, axiom-free Lean statement of the Hodge conjecture on real definitions exists | `Paul-Lez/HodgeConjecture` at `2ead713`: 461 Lean files, about 84,000 lines, 0 `sorry`, 0 axiom declarations; `HodgeConjecture/Statement.lean` | yes, by clone and count | decision 0003: rebase on it |
| Interface-style statements are vacuous or false | `lean-dojo/LeanMillenniumPrizeProblems`, `Tests/Hodge/CycleClassUnconstrained.lean` (`killCycles`) and `StatementIsVacuous.lean` | yes, by reading the files | interface-first pattern retired |
| `formal-conjectures` rejects placeholder statements | `google-deepmind/formal-conjectures` issue #4685, comment by Paul-Lez | yes | statements must use real definitions |
| Upstream has a codimension-p cycle subgroup | `Other/AlgebraicGeometry/Cycle/Codimension.lean`, `codimensionCycleSubgroup` | yes | our `Z-cycles` rung retired |
| A proof of rational Lefschetz (1,1) on upstream definitions exists, unmerged | upstream PRs #217–#226, #9, #230, #228; head `c7d5c94b`, Lean v4.33.1 | yes, by PR records; build reproduction in progress | rung `lefschetz-upstream-verify` |
| Tau Ceti has Chow groups, Hodge structures, line bundles, de Rham | `TauCetiProject/TauCeti`: `AlgebraicGeometry/Chow/*`, `Geometry/Hodge/*`, `AlgebraicGeometry/LineBundle/*` | partly (directory listings) | fallback source; tracks Mathlib master |
| Open Mathlib PRs on the planned foundations | #38472 (Weil divisor of a rational function), #45315 (forms on manifolds), #34626 (affine analytification) | yes, by PR state | not on the critical path after 0003 |
| Pinned Mathlib already has sheaf cohomology, constant sheaves, ℓ-adic cohomology | `CategoryTheory/Sites/SheafCohomology/*`, `Sites/ConstantSheaf.lean`, `AlgebraicGeometry/Sites/ElladicCohomology.lean` | yes, by local search | the earlier "no rational structure" gap was overstated |
| Field-standard practice this repository lacks | blueprints (leanblueprint, LeanArchitect arXiv:2601.22554), test-lemma suites per definition, named cited assumptions (FLT `Assumptions/`), statements read against a fixed definitions root (pequalnp) | reported | rungs `nonvacuity-tests`; harness changes |

## Mathematics (`docs/problem.md`)

| Correction | Source | Verified |
|---|---|---|
| The CM reduction row was wrong: Abdulali proves Hazama's theorem (HC for all CM abelian varieties implies GHC for them), not a reduction of HC for all abelian varieties to CM | arXiv:math/0601052 abstract | yes |
| "No serious attempt is recorded as retracted" was false: three manuscripts claiming cases via homological mirror symmetry were withdrawn in October 2026 after a sign error; a claim for powers of CM fourfolds was withdrawn by its author | arXiv:2610.30976; arXiv:2609.27916 v2 | yes |
| New: HC for generalized Kummer type of dimension 2n with n+1 prime, and powers (preprint) | arXiv:2610.31740 | yes |
| New: Tate for abelian fourfolds over finitely generated fields, building on Markman (preprint) | arXiv:2611.30237 | yes |
| Abelian fourfolds of every discriminant rest on the Markman 2025 preprint; only dimension ≤ 3 is unconditional | Markman2023, FloccariFu2025 (JMPA 2026), Markman2025 | reported |
| Fermat row overstated; published da Silva covers m ≤ 100 coprime to 6; newer preprints extend; a 2016 claim for all Fermat fourfolds conflicts with later papers | Exp. Results 2 (2021) e22; arXiv:2609.27301, 2609.12759, 2608.18134; Kang 2016 | reported |
| Frontier phrasing: very general members are trivial; the open cases are arbitrary or special members | da Silva 2021; Voisin 2025 | reported |
| Shimura row omitted a trace-formula condition | BMM2016 | reported |

## Applied

Decision 0003; ledger restructure; `docs/problem.md` and `docs/references.md` corrections; `docs/conventions.md`; red-team definition updated with falsification duties.
