# Handoff 2026-11-26: `cup-odd-degree-test`

- Goal: a nonzero product of two classes in H¹(X; ℚ) on a curve of positive genus or an abelian surface, the test in which the sign (−1)^{pq} of the cup comparison equals −1.
- Route (sketch `docs/sketches/cup-odd-degree-test.md`): evaluate H² on a torus cycle; on two degree-one classes the value is a determinant; winding classes of two units with a periodic torus give 1 and −1; pull back along Ψ.
- Checked: `torus-cycle-pairing`, `winding-torus-cup`, `singular-odd-cup-test` (ℂˣ × ℂˣ), `cup-odd-degree-transfer` (any X with the four instances and torus data), `gm2-witness`, `gm2-points`, `cup-odd-degree-gm2` (`gm2_exists_cup_ne_zero`, `gm2_torusEval_cup` with value −1).
- `cup-odd-degree-test` stays open. Blocker: no elliptic curve at the pin; Mathlib has ℘ and its differential equation, and lacks Δ(Λ) ≠ 0, the two-to-one counting of ℘ on a period parallelogram, and any scheme structure on Weierstrass curves.
- Proposed sub-rungs (sketch section 5): `elliptic-curve-witness`, `elliptic-curve-points`, `elliptic-curve-uniformization`, `elliptic-curve-torus-data`. Kill criterion in section 6.
- Lean notes: state over a general `TopCat` and specialize; `val` must be a `def` (an `abbrev` blocks `rw`); build `ModuleCat` cocycles with `cyclesMk`, since `liftCycles` with `toSpanSingleton` hits instance mismatches; pass `(show 1 + 1 = 2 from rfl)` to `cup_singular_comparison_swap`.
