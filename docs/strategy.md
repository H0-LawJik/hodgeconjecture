# Strategy: what we attack, in what order

The Hodge conjecture is open, and the literature offers no route to a proof. This document says what the project can honestly aim at, in what order, and what it will say about each outcome. It is the "what we tell Claude" half; `docs/harness.md` is the "how".

## The one rule

A claim is a result when the checker accepts it. Everything else in this document is a plan for producing claims the checker can judge.

## Milestones

| | Milestone | Done when | Why it is worth doing on its own |
|---|---|---|---|
| M0 | Cycles and Chow groups | `Z-cycles` and `rational-equivalence` checked | First Mathlib-grade algebraic cycle theory beyond divisors. Upstream candidate. |
| M1 | The statement, interface-first | `statement` is `stated`: a `Prop` with no `sorry`, parameterized by a `HodgeInterface` structure that packages cohomology, the Hodge decomposition and the cycle class map as data with axioms | Lets the proof side start years before the analytic foundations exist. Every later proof against the interface is honest about being conditional. |
| M2 | Known cases against the interface | `p = 0`, `p = dim X`, and `p = 1` (Lefschetz (1,1), from the exponential sequence axiomatized in the interface) checked; `p = dim X - 1` by hard Lefschetz, if hard Lefschetz is part of the interface | These are the theorems a textbook proves; they test whether the interface is the right shape. |
| M3 | Foundations | `de-rham`, `complex-analytic-space`, `hodge-decomposition`, `cycle-class` checked and the interface instantiated for a smooth projective complex variety | Removes the conditional. Largest body of work; most of it is general-purpose mathematics Mathlib lacks. |
| M4 | Known theorems and reductions | Reductions (hard Lefschetz reduces to `2p ≤ dim X`; behavior under products and blow-ups) and known special cases (abelian varieties of specific types, uniruled fourfolds) stated and checked | Each one is a published theorem with a bounded formalization. |
| M5 | Fronts | At least one approach front with a stated conditional theorem of the form "if `A` then the Hodge conjecture for class `C`", where `A` is a precise open statement | This is where a new result could appear, and where most work will die. |

Milestones are not strictly sequential. M1 and M2 start now; M0 and M3 run in parallel; M4 and M5 open once M1 exists.

## Fronts

A front is an approach with a named owner (a thinker agent or a person), a kill criterion, and a first rung. Fronts are recorded in the ledger as rungs with `kind: "front"` and live or die in public.

| Front | Idea | What a win looks like | What kills it | First rung |
|---|---|---|---|---|
| `reduce` | Reductions: hard Lefschetz, products, blow-ups, Künneth | Checked theorems that shrink the class of varieties and degrees that need to be handled | Nothing; these are known results, the front ends when they are formalized | hard Lefschetz as an interface axiom and the `2p ≤ dim X` reduction |
| `abelian` | Abelian varieties: Weil classes, exceptional Hodge classes, the cases known in the literature | Checked statements of the known cases against the interface | A statement that cannot be made precise without the full analytic stack | define the Hodge ring of an abelian variety from a polarized Hodge structure of weight one |
| `variational` | Hodge loci are algebraic (Cattani, Deligne, Kaplan); the variational Hodge conjecture | A checked conditional: variational implies classical for a stated class | Formalizing variations of Hodge structure proves too large before any conditional is stated | define a variation of Hodge structure over a base and the Hodge locus of a class |
| `absolute` | Absolute Hodge classes (Deligne); HC implies every Hodge class is absolute; the converse direction as a target | A checked "absolute Hodge implies algebraic for class `C`" for a class `C` where it is known | No formalizable notion of "absolute" without étale or de Rham comparison | state absolute Hodge against an interface carrying Galois conjugates of the variety |
| `refute` | Red team: look for a rational Hodge class with no algebraic representative on a concrete variety | A checked counterexample (the project then changes its verdict and its name stays) | The standing fact that no counterexample is known despite a century of search; this front is small and permanent | the Atiyah and Hirzebruch integral counterexample, as a checked statement that the integral version fails |

Fronts that are not in this table do not exist yet. Adding one is a decision record plus a ledger rung.

## What we will and will not say

- "Checked" means the checker accepted it. "Stated" means the statement compiles and the proof is open. "Conditional on the interface" means proved against `HodgeInterface` before it is instantiated. Every public surface uses these words and no others.
- We do not say "progress toward a proof". We say which rung moved.
- If a front dies, the ledger says why and the dead rung stays visible.
- If the verdict ever changes, the change is a checked declaration, a decision record, and a note on the site, in that order.

## References

Claims that something is "known" cite `docs/references.md`. A thinker that cannot cite a source for a claimed theorem writes "unverified" next to it, and a red-team pass must clear it before a statement rung is posted.
