# The statement

## Informal

Let `X` be a smooth projective variety over the complex numbers, of dimension `n`. Its singular cohomology with rational coefficients carries a Hodge decomposition

    H^k(X, C) = ⊕_{p+q=k} H^{p,q}(X),   with H^{q,p} the conjugate of H^{p,q}.

A rational class in `H^{2p}(X, Q)` whose image in `H^{2p}(X, C)` lies in `H^{p,p}(X)` is a **Hodge class**. Every algebraic cycle `Z` of codimension `p` (a formal integer combination of irreducible closed subvarieties of codimension `p`) has a cohomology class `cl(Z)` in `H^{2p}(X, Q)`, and that class is a Hodge class.

**Hodge conjecture.** Every Hodge class is a rational linear combination of classes of algebraic cycles:

    Hdg^p(X) = H^{2p}(X, Q) ∩ H^{p,p}(X)  equals  the Q-span of { cl(Z) : Z ∈ Z^p(X) }.

## What is known

| Case | Status in the literature | Rung |
|---|---|---|
| `p = 0` and `p = n` | trivial | `p = 0`: `nonvacuity-tests` (checked, equality form); `p = n`: no rung yet |
| `p = 1` | Lefschetz (1,1) theorem [Lefschetz1924] | `lefschetz-1-1` (checked, the upstream inclusion), `lefschetz-1-1-equality` (checked, the equality); `lefschetz-1-1-integral` (open) |
| `p = n - 1` | follows from `p = 1` by the hard Lefschetz theorem [Shioda1983] | `hard-lefschetz`, `dimension-le-three` (open) |
| abelian varieties | dimension ≤ 3 [MoonenZarhin1999]; Weil classes of discriminant 1 on fourfolds [Markman2023]; all fourfolds and dimension 5 through the preprint [Markman2025] (`docs/problem.md` §3) | `markman-statement` (open), front `abelian` |
| general `p` | open | upstream `HodgeConjecture`; ledger verdict `open` |

The integral version is false [AtiyahHirzebruch1962]; the rational version above is the conjecture.

## Formal statement

The statement of record is upstream, in `Paul-Lez/HodgeConjecture`, file `HodgeConjecture/Statement.lean`, pinned in this repository's `lakefile.toml` (decision 0003):

```lean
def HodgeConjecture : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ),
    Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p
```

Here `Hdg^p(X; ℚ)` is the space of rational classes in `H^{2p}(X(ℂ); ℚ)` (constant-sheaf cohomology on X(ℂ) with the analytic topology) whose de Rham image lies in `F^p ∩ conj F^p`, with `F^p` the image of the hypercohomology of holomorphic forms of degree at least p. `algebraicCycleClassSpan X p` is the ℚ-span of the fundamental classes of codimension-p integral closed subvarieties, built from cohomology with support and normalized by complex orientations of normal spaces.

Upstream also states the variants this repository works on, in `HodgeConjecture/Variants.lean`: `LefschetzOneOne`, `HodgeConjectureInDimensionLE n`, `HodgeConjectureForAbelianVarieties`, `HodgeConjectureForAbelianVarietiesInDimensionLE n`. Upstream's docstrings call the last one a theorem for n ≤ 5. For Weil classes of discriminant other than 1 that rests on the preprint [Markman2025]; `docs/gaps.md` records it as a red-team item.

## Targets on this ladder

See `docs/roadmap.md`. The Lefschetz checkpoint is checked: `lefschetz-1-1` (upstream `LefschetzOneOne` at this repository's pin) and `lefschetz-1-1-equality` (Hdg^1 = `algebraicCycleClassSpan X 1`). The current target is milestone M2 (`docs/strategy.md`), with front `cup` as its blocking foundation.
