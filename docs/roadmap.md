# Roadmap: the ladder

Each row is a live rung in `ledger/ladder.json`. Status words: `checked` (the checker accepts the declarations), `stated` (statement sorry-free, proof open), `open`, `refuted`, `dead`. Dead rungs stay in the ledger with their reason; decision 0003 retired fifteen of them.

| Rung | Kind | Status | Depends on | What it needs |
|---|---|---|---|---|
| `upstream-statement` | statement | stated | | upstream `HodgeConjecture`, `LefschetzOneOne`, `HodgeConjectureInDimensionLE` at the pinned commit |
| `statements-consistent` | reduction | checked | `upstream-statement` | done in `HodgeLadder.Upstream.Statements` |
| `cycle-class-pins` | test | checked | `upstream-statement` | done in `HodgeLadder.CycleClass.Pins`; see `docs/cycle-class.md` |
| `known-half-statement` | statement | stated | `upstream-statement` | `CycleClassesAreHodge`, `HodgeConjectureEquality`, `LefschetzOneOneEquality` |
| `equality-reductions` | reduction | checked | `known-half-statement` | equality ↔ upstream inclusion ∧ known half |
| `lefschetz-upstream-verify` | case | checked | `upstream-statement` | reproduce the build of upstream PR #228 at `c7d5c94b`; axiom audit; red-team verdict |
| `nonvacuity-tests` | test | checked | `upstream-statement` | done in `HodgeLadder.Tests`: Spec ℂ meets the hypotheses; Hdg^0 = span ≠ 0 for every X |
| `divisor-chern-exact` | foundation | checked | `lefschetz-upstream-verify` | the class of a Cartier divisor equals the rational image of c₁(𝒪(D)) exactly on the pinned cycle class, sign determined |
| `lefschetz-port` | foundation | checked | `lefschetz-upstream-verify`, `divisor-chern-exact` | port the upstream stack (PRs #217–#226, #9, #230, #228) from v4.33.1 to the current pin; coordinate with upstream first |
| `lefschetz-1-1` | case | checked | `lefschetz-port`, `nonvacuity-tests` | done in `HodgeLadder.Lefschetz.OneOne` (`lefschetzOneOne_holds`; the inclusion, a step) |
| `chern-classes-are-hodge` | foundation | checked | `lefschetz-port`, `divisor-chern-exact` | done in `HodgeLadder.Hodge.ChernClasses`: F¹ = ker(H_dR → ℍ(𝒪)); rational c₁ and Cartier divisor classes are Hodge |
| `prime-divisors-cartier` | foundation | open | `chern-classes-are-hodge` | local factoriality of smooth varieties (Mathlib lacks regular local ⇒ UFD); a unit extension for each invertible sheaf |
| `lefschetz-1-1-equality` | case | open | `lefschetz-1-1`, `divisor-chern-exact`, `equality-reductions`, `chern-classes-are-hodge`, `prime-divisors-cartier` | `theorem : LefschetzOneOneEquality`; the checkpoint's definition of done |
| `cycle-classes-are-hodge` | foundation | open | `known-half-statement`, `cycle-class-pins` | `theorem : CycleClassesAreHodge` |
| `lefschetz-1-1-integral` | case | open | `lefschetz-port`, `divisor-chern-exact` | image of c₁ on Pic equals the integral Hodge classes in H² |
| `projective-space-test` | test | open | `upstream-statement` | Hdg^1(ℙ^n) = span, both one-dimensional |
| `clifford-exterior-spin` | foundation | open | `lefschetz-1-1-equality` | Clifford algebra of the split form on H ⊕ H^∨ acting on ∧*H; for the Markman inventory (`docs/notes/2026-11-24-spinors-characters-tests.md`) |
| `elliptic-product-test` | test | open | `lefschetz-1-1-equality` | dim Hdg^1(E₁ × E₂) = 2 + rank Hom(E₁, E₂) while h^{1,1} = 4 |
| `hard-lefschetz` | foundation | open | `upstream-statement` | Kähler geometry and the Lefschetz decomposition on upstream cohomology; inventory before sub-rungs |
| `dimension-le-three` | case | open | `lefschetz-1-1`, `hard-lefschetz` | `HodgeConjectureInDimensionLE 3` |
| `markman-statement` | front | open | `lefschetz-1-1-equality` | Markman's theorem on upstream definitions, after the checkpoint inventory |

## Order of attack

1. `lefschetz-upstream-verify` and `nonvacuity-tests`, in parallel. Both read upstream source and build it; neither changes it.
2. `lefschetz-port`, after a note to the upstream authors: they proposed taking Oka as a dependency instead of vendoring 372 modules, and a port should follow their choice.
3. `divisor-chern-exact` as part of the port, then `lefschetz-1-1` and `lefschetz-1-1-equality` here. Then the Markman inventory (`docs/strategy.md` M2).
4. `projective-space-test` and `cycle-classes-are-hodge` can start now; both read upstream definitions only.
5. `hard-lefschetz` is the long pole for `dimension-le-three`; start its inventory once the checkpoint is in.

## Watch signals

- The upstream pin moves: diff the definitions in `docs/conventions.md` between commits before bumping.
- A rung sitting `open` with no issue for a month: post sub-rungs or mark it `dead` with a reason.
- Any rung marked `checked` whose declarations no longer pass the axiom check after a bump: CI fails, and the fix goes before any new work.
