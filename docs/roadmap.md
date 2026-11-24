# Roadmap: the ladder

Each row is a rung in `ledger/ladder.json`. Status words: `checked` (the checker accepts the declarations), `stated` (statement sorry-free, proof open), `open`, `refuted`, `dead`. Dependencies point downward; a rung can be worked before its dependencies are checked when its statement does not need them.

| Rung | Status | Depends on | Mathlib already has | Missing |
|---|---|---|---|---|
| `Z-cycles` | checked | | `AlgebraicCycle`, `IsWeilDivisor`, `weilDivisors` | nothing; done in `HodgeConjecture.Cycles.Codimension` |
| `rational-equivalence` | open | `Z-cycles` | `OrderOfVanishing`, residue fields, pushforward of cycles | divisor of a rational function on a subvariety; `CH^p(X)` as a quotient |
| `complex-analytic-space` | open | | complex manifolds, holomorphic functions, projective spectrum | analytification of a projective scheme; `X(ℂ)` as a compact complex manifold |
| `de-rham` | open | | smooth manifolds, tangent and vector bundles, partitions of unity, Stokes in Euclidean space | differential forms on manifolds, exterior derivative, de Rham cohomology, de Rham theorem |
| `hodge-decomposition` | open | `de-rham` | inner product spaces, Hodge star on exterior powers (`HodgeStar.lean`), some elliptic theory for Euclidean domains | Kähler metrics, `(p,q)` forms, Dolbeault, Laplacian on a compact manifold, the decomposition |
| `cycle-class` | open | `rational-equivalence`, `complex-analytic-space`, `hodge-decomposition` | | fundamental class of a subvariety, Poincaré duality, `cl` lands in `H^{p,p}` |
| `hodge-interface` | open | `Z-cycles` | | `HodgeInterface` structure: cohomology, decomposition, cycle class, cited axioms (see `docs/harness.md`) |
| `statement-interface` | open | `hodge-interface` | | the conjecture as a sorry-free `Prop` against the interface; milestone M1; target status `stated` |
| `case-trivial-degrees` | open | `statement-interface` | | `p = 0` and `p = dim X` against the interface |
| `case-lefschetz-1-1` | open | `statement-interface` | | exponential sequence as interface data; the `p = 1` case |
| `reduce-hard-lefschetz` | open | `statement-interface` | | hard Lefschetz as interface data; reduction to `2p ≤ dim X` |
| `statement` | open | `cycle-class`, `statement-interface` | | the unconditional statement once the interface is instantiated (M3) |

## Order of attack

Milestones and fronts are in `docs/strategy.md`; this table is the rung-level view.

1. `rational-equivalence` is the cheapest next rung and builds directly on what is checked. It is also the most likely to be welcome upstream in Mathlib.
2. `de-rham` is the largest block of foundations. It is independent of the algebraic side and can run in parallel. Smaller sub-rungs should be posted as issues: forms as sections of the exterior power of the cotangent bundle, `d` and `d ∘ d = 0`, cohomology as a quotient, pullback.
3. A `stated` version of `statement` may be reachable earlier by assuming the Hodge decomposition as a structure (a `class` carrying the decomposition and the cycle class map) and proving the trivial cases against that interface. That keeps the proof side honest while foundations catch up, and the ledger marks it `stated`, not `checked`, until the interface is instantiated.

## Watch signals

- A rung sitting `open` with no issue for a month: post sub-rungs or mark it `dead` with a reason.
- A local definition that duplicates something Mathlib gained in a newer tag: bump the pin and delete the local copy.
- Any rung marked `checked` whose declarations no longer pass the axiom check after a Mathlib bump: CI fails, and the fix goes before any new work.
