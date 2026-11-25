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
| `ufd-descent` | foundation | checked | | done in `HodgeLadder.Algebra.UFDDescent` (Mori's descent, local case) |
| `analytic-stalk-ufd` | foundation | checked | `lefschetz-port` | done in `HodgeLadder.Divisor.AnalyticStalk` |
| `local-factoriality` | foundation | checked | `ufd-descent`, `analytic-stalk-ufd` | done in `HodgeLadder.Divisor.LocalFactoriality` |
| `prime-divisor-ideal-sheaf` | foundation | checked | `local-factoriality` | done in `HodgeLadder.Divisor.PrimeDivisorSmooth`: the ideal sheaf of D is invertible, represented by Cartier data with divisor −D |
| `unit-extension-of-invertible` | foundation | checked | `lefschetz-port` | a unit extension E with L^an ≅ E.section for every invertible L |
| `prime-divisors-cartier` | foundation | checked | `chern-classes-are-hodge`, `local-factoriality`, `prime-divisor-ideal-sheaf`, `unit-extension-of-invertible` | assembly: `CycleClassesAreHodgeOne` |
| `lefschetz-1-1-equality` | case | checked | `lefschetz-1-1`, `divisor-chern-exact`, `equality-reductions`, `chern-classes-are-hodge`, `prime-divisors-cartier` | `theorem : LefschetzOneOneEquality`; the checkpoint's definition of done |
| `cycle-classes-are-hodge` | foundation | open | `known-half-statement`, `cycle-class-pins` | `theorem : CycleClassesAreHodge` |
| `lefschetz-1-1-integral` | case | open | `lefschetz-port`, `divisor-chern-exact` | image of c₁ on Pic equals the integral Hodge classes in H² |
| `projective-space-test` | test | open | `upstream-statement`, `projective-line-test` | Hdg^1(ℙ^n) = span, both one-dimensional; split into the ℙ¹ rungs below (`docs/sketches/projective-space-test.md`) |
| `projective-line-witness` | test | checked | `upstream-statement` | ℙ¹ = `ProjectiveSpace.toBase (Fin 2) (Spec ℂ)` is integral, smooth of relative dimension one, projective; Oka charts and base change |
| `projective-line-point` | test | checked | `projective-line-witness` | a point of coheight one whose analytic complement is homeomorphic to ℂ |
| `forget-support-exact` | foundation | checked | `upstream-statement` | done in `HodgeLadder.Tests.ForgetSupport`: forgetSupport injective in degree n + 1, surjective in degree n, when H^n of the open complement vanishes |
| `contractible-open-acyclic` | foundation | checked | `upstream-statement` | done in `HodgeLadder.Tests.ContractibleAcyclic`: H'^q(U; ℚ) = 0 for q > 0 and U ⊆ X(ℂ) a contractible open, through the flasque singular-cochain resolution on U |
| `projective-line-class-nonzero` | test | checked | `projective-line-point`, `forget-support-exact`, `contractible-open-acyclic` | the class of a point is nonzero in H²(ℙ¹; ℚ); the degree-two non-vacuity test |
| `projective-line-h2` | test | checked | `projective-line-class-nonzero` | dim H²(ℙ¹; ℚ) = 1 and it equals the span; one-dimensionality of H²_pt on the sheaf side |
| `projective-line-test` | test | checked | `projective-line-h2`, `lefschetz-1-1`, `chern-classes-are-hodge` | Hdg^1(ℙ¹) = span, both one-dimensional; needs the point class to be Hodge |
| `clifford-exterior-spin` | foundation | open | `lefschetz-1-1-equality` | Clifford algebra of the split form on H ⊕ H^∨ acting on ∧*H; for the Markman inventory (`docs/notes/2026-11-24-spinors-characters-tests.md`) |
| `elliptic-product-test` | test | open | `lefschetz-1-1-equality` | dim Hdg^1(E₁ × E₂) = 2 + rank Hom(E₁, E₂) while h^{1,1} = 4 |
| `cup-front` | front | open | `upstream-statement` | ring structure on H^*(X; ℚ), decision 0008 |
| `rational-ext-equiv` | foundation | checked | `cup-front` | H^n(X; ℚ) ≅ Ext^n(ℚ_X, ℚ_X) in sheaves of ℚ-vector spaces |
| `cup-product` | foundation | checked | `rational-ext-equiv` | cup product: associative, unital, bilinear |
| `cup-graded-commutative` | foundation | open | `cup-product` | α ∪ β = (−1)^{pq} β ∪ α |
| `cycle-class-multiplicative` | foundation | open | `cup-product` | class of an intersection is the cup product of classes |
| `hard-lefschetz` | foundation | open | `upstream-statement` | Kähler geometry and the Lefschetz decomposition on upstream cohomology; inventory before sub-rungs |
| `dimension-le-three` | case | open | `lefschetz-1-1`, `hard-lefschetz` | `HodgeConjectureInDimensionLE 3` |
| `markman-statement` | front | open | `lefschetz-1-1-equality` | Markman's theorem on upstream definitions, after the checkpoint inventory |

## Order of attack

1. `lefschetz-upstream-verify` and `nonvacuity-tests`, in parallel. Both read upstream source and build it; neither changes it.
2. `lefschetz-port`, after a note to the upstream authors: they proposed taking Oka as a dependency instead of vendoring 372 modules, and a port should follow their choice.
3. `divisor-chern-exact` as part of the port, then `lefschetz-1-1` and `lefschetz-1-1-equality` here. Then the Markman inventory (`docs/strategy.md` M2).
4. `cycle-classes-are-hodge` can start now. `projective-space-test` goes through ℙ¹: `projective-line-witness` and `contractible-open-acyclic` can run in parallel, then `projective-line-point` and `projective-line-class-nonzero`.
5. `hard-lefschetz` is the long pole for `dimension-le-three`; start its inventory once the checkpoint is in.

## Watch signals

- The upstream pin moves: diff the definitions in `docs/conventions.md` between commits before bumping.
- A rung sitting `open` with no issue for a month: post sub-rungs or mark it `dead` with a reason.
- Any rung marked `checked` whose declarations no longer pass the axiom check after a bump: CI fails, and the fix goes before any new work.
