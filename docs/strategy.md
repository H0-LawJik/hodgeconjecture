# Strategy: what we attack, in what order

The Hodge conjecture is open, and the literature offers no route to a proof. This document says what the project can honestly aim at, in what order, and what it will say about each outcome. It is the "what we tell Claude" half; `docs/harness.md` is the "how". The mathematical picture it rests on, with sources, is `docs/problem.md`: read that first. The reasons for the current shape are in `docs/decisions/0003-rebase-on-upstream-statement.md`.

## The one rule

A claim is a result when the checker accepts it. Everything else in this document is a plan for producing claims the checker can judge.

## Equality first

The ladder aims at non-vacuous equalities (decision 0004). The conjecture's target form here is Hdg^p(X; ℚ) = algebraicCycleClassSpan X p; the upstream inclusion is a step toward it. Identities between classes are proved exactly, with signs and normalizations recorded in `docs/conventions.md`; "equal up to a nonzero scalar" does not discharge one. Cases where only an inclusion is known, or where an equality fails, are study points.

## Statements of record

The conjecture and its standard variants are stated upstream, in `Paul-Lez/HodgeConjecture` (Lean library `HodgeConjecture`), on real definitions: X(ℂ) with the analytic topology, constant-sheaf rational cohomology, the Hodge filtration on holomorphic de Rham hypercohomology, and cycle classes from cohomology with support. This repository imports them at a pinned commit and proves things about them. It does not restate them, and it does not define the conjecture against an interface.

## Milestones

| | Milestone | Done when | Why it is worth doing on its own |
|---|---|---|---|
| M0 | Adopt the statements of record | `upstream-statement` stated and `statements-consistent` checked at the pinned upstream commit | Every later result is about the same objects the wider community checks |
| M1 | The Lefschetz checkpoint | `lefschetz-upstream-verify`, `nonvacuity-tests`, `divisor-chern-exact`, `lefschetz-port` done; `lefschetz-1-1` and `lefschetz-1-1-equality` checked here; red-team `pass`; conventions register filled with the exact divisor–Chern sign | First equality-level case of the conjecture on these definitions at the current pin; the strongest available test that the definitions mean what the literature means |
| M1+ | The Lefschetz extras | `lefschetz-1-1-integral` and `projective-space-test` checked | The literature's integral form, and a computed example that pins the definitions from both sides |
| M2 | Markman inventory | A written inventory of the tools and gaps between the Lefschetz checkpoint and Markman's theorem, and `markman-statement` stated | Sets the frontier target with the tools actually in hand. The inventory found that the all-discriminant proof [Markman2025] passes through degree six, and that the discriminant-1 proof [Markman2023] stays in degree four |
| M3 | Low dimension and the known half | `hard-lefschetz`, `dimension-le-three` (equality form) and `cycle-classes-are-hodge` checked | Completes the cases a textbook proves, and makes the general statement an equality |
| M4 | Known cases and reductions | Published reductions (hyperplane sections above the middle degree, projective bundles, dominant maps, blow-ups) and known cases (cellular varieties, cubic and uniruled fourfolds, generic abelian varieties) checked on upstream definitions | Each is a published theorem with a bounded formalization; `docs/problem.md` §3 and §4 list them with sources. Products are not on this list: HC(X) and HC(Y) do not give HC(X × Y) |
| M5 | Fronts | At least one front with a checked statement at the frontier, or a checked conditional "if A then HC for class C" with A precise | Where a new result could appear, and where most work will die |

| Milestone | Status (2026-11-25) |
|---|---|
| M0 | done: `upstream-statement` stated, `statements-consistent` checked, merged to `main` |
| M1 | done: `lefschetz-1-1-equality` checked; red team pass with changes (`docs/sketches/lefschetz-1-1-equality.redteam.md`); divisor–Chern sign + in `docs/conventions.md` |
| M1+ | in part: the ℙ¹ case `projective-line-test` is checked; `projective-space-test` (ℙⁿ, n ≥ 2) and `lefschetz-1-1-integral` are open |
| M2 | current target. Inventory written: `docs/notes/2026-11-25-markman-inventory.md`. `markman-statement` is open. The blocking foundation is front `cup` (decision 0008): no ring structure exists on upstream's H^*(X; ℚ) at the pin. After it, the inventory's target sequence T1 to T5 (§6) starts with T1, Weil classes on abelian surfaces of Weil type |
| M3 | open; needs front `cup` as well (inventory §5) |

## Fronts

A front is an approach with a named owner (a thinker agent or a person), a kill criterion, and a first rung. Fronts are recorded in the ledger as rungs with `kind: "front"` and live or die in public.

| Front | Idea | What a win looks like | What kills it | First rung |
|---|---|---|---|---|
| `abelian` | Abelian varieties: Mumford-Tate groups, Hodge rings generated by divisors, Weil classes; the richest proven class and the live frontier (`docs/problem.md` §3). Markman's methods: hyperkähler geometry for discriminant 1 in degree four [Markman2023]; secant sheaves, Orlov's equivalence and semiregularity on sixfolds (degree six) for every discriminant [Markman2025] (preprint), with Voisin's product reduction from sixfolds to fourfolds [Voisin2026Bourbaki] | Markman's theorem stated on upstream definitions; known cases (generic abelian varieties; Hodge ring generated by divisors) checked | A statement that cannot be made on upstream definitions without new foundations larger than the inventory can carry | `markman-statement` (open); the first Markman-directed rung is T1 of the inventory (`docs/notes/2026-11-25-markman-inventory.md` §6), after front `cup` |
| `cup` | A ring structure on upstream's `H^*(X; ℚ)`: Yoneda products after `H^n(X; ℚ) ≅ Ext^n(ℚ_X, ℚ_X)` in sheaves of ℚ-vector spaces (decision 0008), compared with the singular cup product (decision 0009); cycle classes multiply through a relative cup of two supported classes on the singular side, with ℙ² as the first test case (decision 0010) | A checked associative, unital, graded-commutative cup product, compatible with the cycle class map; it unblocks M2 and M3 | The sign in `cup-singular-comparison` cannot be fixed exactly, or the product cannot be shown compatible with `cycleComponentSheafClass` on upstream definitions | `rational-ext-equiv` and `cup-product` (checked), with `cup-singular-comparison` and `cup-graded-commutative`; next `cycle-class-multiplicative`, tested first by `cycle-class-multiplicative-codim-zero` and on ℙ² (`cup-positive-degree-test-p2`) |
| `reduce` | Reductions that are theorems (`docs/problem.md` §4) | Checked reductions; birational invariance in dimension ≤ 5 as the capstone | Nothing; known results, the front ends when they are formalized | `hard-lefschetz` |
| `variational` | Hodge loci are algebraic (Cattani, Deligne, Kaplan); the variational Hodge conjecture | A checked conditional: variational implies classical for a stated class | Formalizing variations of Hodge structure proves too large before any conditional is stated | define a variation of Hodge structure over a base on upstream definitions |
| `absolute` | Absolute Hodge classes; HC splits as Hodge ⇒ absolute Hodge and absolute Hodge ⇒ algebraic | Deligne's theorem for abelian varieties, or a checked "absolute Hodge implies algebraic for class C" | No formalizable notion of "absolute" without étale or de Rham comparison (Mathlib now has ℓ-adic cohomology of schemes) | state absolute Hodge using Mathlib's ℓ-adic cohomology and upstream de Rham |
| `refute` | Falsification: the stronger forms are false (integral, Kähler, Hodge's generalized form); test the definitions for vacuity and convention drift; keep the October 2026 sign-error withdrawals in sight | A checked statement that the integral version fails, a checked non-vacuity suite, or a checked counterexample to the rational version | The standing fact that no counterexample is known; this front is small and permanent | `nonvacuity-tests` |

Fronts that are not in this table do not exist yet. Adding one is a decision record plus a ledger rung.

## Where results live (decision 0011)

| Kind of result | Where it goes |
|---|---|
| Statements of record: the conjecture, its variants, the cycle class | `Paul-Lez/HodgeConjecture` at the pinned commit, imported and not restated (decision 0003) |
| General mathematics the ladder needs that the pin lacks | this repository, listed in `docs/gaps.md` "General lemmas kept local" |
| Proofs of the upstream variants, reductions, frontier statements, the ledger, falsification records, the literature map | this repository |

## What we will and will not say

- "Checked" means the checker accepted it. "Stated" means the statement compiles and the proof is open. Every public surface uses these words and the ledger's other statuses, and no others.
- We do not say "progress toward a proof". We say which rung moved.
- If a front dies, the ledger says why and the dead rung stays visible.
- If the verdict ever changes, the change is a checked declaration, a decision record, and a note on the site, in that order.

## References

Claims that something is "known" cite `docs/references.md`. A thinker that cannot cite a source for a claimed theorem writes "unverified" next to it, and a red-team pass must clear it before a statement rung is posted.
