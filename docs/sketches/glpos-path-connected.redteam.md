# Red team: `glpos-path-connected` (statement pass)

Date 2026-11-26. Pin: upstream `2ead713`, Lean and Mathlib `v4.35.0-rc4`. Target: `HodgeLadder/Glpos/PathConnected.lean` (proof `sorry`), statement section "glpos-path-connected: statement" of `docs/sketches/local-class-product.md`.

**Verdict: pass with changes.** The changes are bookkeeping for proof time (C1 to C3); the statement stands as written.

## Findings

1. **Literature statement.** Classical: GL⁺ₙ(ℝ), the real matrices with positive determinant, is path-connected (standard; no key in `docs/references.md`, so unverified here). The rung states it field by field: carrier `{M : Matrix n n ℝ | 0 < M.det}`, Mathlib's `Matrix.det`; ambient topology the product topology of `Mathlib.Topology.Instances.Matrix`; `JoinedIn S 1 A` for every `A ∈ S`, and `IsPathConnected S` as a corollary. The two are equivalent to the classical theorem (the corollary is proved; the converse is `IsPathConnected.joinedIn`). The statement loses nothing against the literature. Mathlib's `Matrix.GLPos` lives in the units topology; the matrix form is the one the consumer can use (finding 7).
2. **Hypotheses satisfiable.** `A = 1` works, and so does `A = diagonal ![-1, -1]` at `n = Fin 2` (scratch: `0 < A.det ∧ A ≠ 1`, by `simp [det_diagonal, Fin.prod_univ_two]`). The second exercises the sign flip, the new part of the proof.
3. **Vacuity and trivial proofs.** `rfl`, `trivial`, `simp`, `exact JoinedIn.refl _`, `aesop`, `grind` all fail on the statement (scratch at the pin). Every piece is a Mathlib definition with no `True` unfolding, no `ℕ∞` and no coercion. The hypothesis is needed: without it `A = 0` is a counterexample, since `0 ∉ S`. Negative check, kernel-checked in scratch at the pin: `¬ JoinedIn {M : Matrix (Fin 1) (Fin 1) ℝ | M.det ≠ 0} 1 (diagonal ![-1])` (continuity of `det` along the path and `intermediate_value_univ`, eight lines). So the `0 < det` form is the right strength, and the `det ≠ 0` form that upstream's complex isotopy uses is false over ℝ.
4. **Empty index type.** For `n = Fin 0` every matrix equals `1` (`Subsingleton.elim`) and `JoinedIn.refl` closes it (scratch, two lines). The case is harmless and the general proof should cover it without a special case (`diagonal_transvection_induction` has no nonemptiness hypothesis).
5. **Already in Mathlib?** No. A grep of `.lake/packages/mathlib/Mathlib` for `GLPos` (3 files: `GeneralLinearGroup/Defs.lean`, `UpperHalfPlane/MoebiusAction.lean`, `ModularForms/Basic.lean`; none mentions connectedness), and for `IsPathConnected`, `PathConnectedSpace`, `JoinedIn`, `IsConnected` near `det`, `Matrix`, `GL`, `SpecialLinear`, `orthogonal`, `unitary`, found only balls, spheres, complements of points and subspaces, the circle and unitary balls in C⋆-algebras. No connectedness of `SL`, `SO` or `GL⁺` over ℝ at the pin.
6. **Proof route.** Sound. Checked pieces: `JoinedIn.mul` (line 277 of `Topology/Connected/PathConnected.lean`) gives `JoinedIn (S * S) (1 * 1) (A * B)`, and `S * S ⊆ S` by `det_mul`; `JoinedIn.map` takes `ContinuousOn` and lands in `f '' S`, and `diagonal D * ·` maps `S` into `S` when `0 < ∏ D`; `diagonal_transvection_induction` has the shape the sketch uses (hypothesis `det (diagonal D) = det M`, so `∏ D = det A > 0` and no entry of `D` is zero). The quarter turn: for `i ≠ j`, `W = transvection i j (-1) * transvection j i 1 * transvection i j (-1)` is the rotation by π/2 in the (i, j)-plane (hand computation at n = 2: `W = !![0, -1; 1, 0]`), and the identity `W * W = diagonal ![-1, 1, -1]` at `n = Fin 3`, `i = 0`, `j = 2` checks in scratch by `fin_cases` and `simp`. Since `W` is a product of three transvections, `W * W` is joined to `1` in `S` by steps 1 and 2. Step 6 (strong induction on the number of negative entries; exactly one is excluded by the sign of the product) is correct. An equivalent bookkeeping that may be shorter in Lean: fix one index `i₀` and flip each pair `(i₀, j)` with `D j < 0`, an induction over a `Finset`; after the last flip `D i₀ > 0` by the sign of the product. Either works.
7. **Fit to the consumer.** `real-affine-orientation` copies upstream's `complexMatrixPuncturedPairHomotopy` (`ComplexClassLinearInvariance.lean`, line 220), which consumes `ComplexIsotopyToOne A`: a `C(unitInterval, Matrix n n ℂ)` with `path 0 = 1`, `path 1 = A`, `det ≠ 0` at each time. The real data comes straight out of the rung; this checks in scratch at the pin:

   ```lean
   example {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
       (h : JoinedIn {M : Matrix (Fin d) (Fin d) ℝ | 0 < M.det} 1 A) :
       ∃ P : C(unitInterval, Matrix (Fin d) (Fin d) ℝ), P 0 = 1 ∧ P 1 = A ∧ ∀ t, (P t).det ≠ 0 :=
     ⟨h.somePath.toContinuousMap, h.somePath.source, h.somePath.target,
       fun t ↦ ne_of_gt (h.somePath_mem t)⟩
   ```

   It has the same direction (1 to A), the same matrix type with `Fin d` and the same topology instance, so `fun_prop` continuity of `(P t).mulVec x` goes through as upstream's `continuous_complexMatrixPath_mulVec` does.
8. **Interface axioms, checker, pin drift.** Not applicable: no structure, the rung is not checked yet, and the statement depends on no upstream declaration, so nothing can drift between upstream pins. A Mathlib bump could rename `JoinedIn.map` (already renamed from `map_continuousOn`, deprecated 2026-08-08) or `diagonal_transvection_induction`; such a rename breaks the build loudly and changes nothing about truth.
9. **Conventions.** `Matrix.det` (Leibniz, `det 1 = 1`) and the product topology on `Matrix n n ℝ`. The statement's truth depends on neither: path-connectedness has no sign, and `0 < det` is transpose-invariant, so the column (`mulVec`) and row (`vecMul`) actions give the same set. Row added to `docs/conventions.md` ("Real determinant and the topology of real matrices"). The sign that matters downstream, sign(det) acting on the local class, belongs to `real-affine-orientation`, whose red team fixes it against the orientation of ℝ^d in `standardLocalClass`.
10. **Equality first, non-vacuity test.** The rung is a topological lemma, neither an identity nor an inclusion of classes; it is a step toward the identity in `real-affine-orientation` (exists, `open`). Smallest test that fails if the statement were trivial: the negative check of finding 3 at `Fin 1`, together with the `diagonal ![-1, -1]` instance at `Fin 2` (the case the `det ≠ 0` form cannot separate). Neither exists in the repository; C2 adds them.

## Changes

| | Change | When |
|---|---|---|
| C1 | Ledger: set `module` to `HodgeLadder.Glpos.PathConnected`, list both declarations; update the note, which still says "pairs of negative entries by a rotation", to the quarter-turn route of the sketch (`W` as three transvections) | proof time |
| C2 | Add the negative check `¬ JoinedIn {M : Matrix (Fin 1) (Fin 1) ℝ \| M.det ≠ 0} 1 (diagonal ![-1])` as a named test lemma next to the rung (or in `HodgeLadder/Tests/`), and an instance at `diagonal ![-1, -1]` | proof time |
| C3 | Add a citation key for the classical theorem to `docs/references.md` (librarian; any textbook statement that GL⁺ₙ(ℝ) is connected) and list both declarations in `docs/gaps.md` "General lemmas kept local" (decision 0011) | proof time |

## What was tried

- The six tactics of finding 3 on the statement: all fail.
- A scratch `intermediate_value_univ` attempt in the wrong order of endpoints failed first (goal `0 ∈ Icc 1 (-1)`); swapping to `intermediate_value_univ 1 0` closes the negative check.
- The general-`n` identity for `W * W` was not attempted here (the sketch reports one leftover `if` case); only `Fin 3` was checked, which is enough to confirm the sign pattern (−1 at both i and j, +1 off the plane).
- Scratch files lived in the worktree and are deleted.
