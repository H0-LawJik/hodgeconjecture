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
| `p = 0` and `p = n` | trivial | part of `statement` |
| `p = 1` | Lefschetz (1,1) theorem | `lefschetz-1-1` (to be added after `cycle-class`) |
| `p = n - 1` | follows from `p = 1` by the hard Lefschetz theorem | later |
| abelian varieties, some special cases | partial results | later |
| general `p` | open | `statement` |

The integral version is false (Atiyah and Hirzebruch, 1961); the rational version above is the conjecture.

## Formalization targets

In order of appearance in Lean:

1. `Z^p(X)` as a subgroup of `AlgebraicCycle X ℤ`. **Checked** (`HodgeConjecture.Cycles.Codimension`).
2. Rational equivalence and `CH^p(X)`.
3. The complex manifold underlying `X`, and its singular cohomology (Mathlib has singular homology; the cohomology side and the comparison with de Rham are both missing).
4. Differential forms, `d`, de Rham cohomology, and the de Rham theorem.
5. Kähler metrics, the `(p,q)` decomposition of forms, and the Hodge decomposition on cohomology.
6. The cycle class map and the fact that it lands in `H^{p,p}`.
7. The statement, as a `Prop` with no `sorry`, parameterized by `X` and `p`. Then the trivial cases, then `p = 1`.

## Formal statement

Not yet written. When it exists, it lives in `HodgeConjecture/Statement.lean` and this section quotes it.
