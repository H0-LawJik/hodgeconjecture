# Red team: `weil-eigen-algebra`

Date: 2026-11-27. Candidate: commit `a3a33f2` on `track/weil-eigen-algebra`, file `HodgeLadder/Weil/Eigen/Algebra.lean`. Pin unchanged from `main` (`8ee8053`): upstream `2ead713`, Lean and Mathlib `v4.35.0-rc4`. Probes ran with `lake env lean` in a scratch directory under the worktree, deleted afterwards.

**Verdict: pass with changes.** The theorem is correct, general and exactly the plan's node A2; every hypothesis is used where it should be; the checker accepts all five declarations with standard axioms. The changes are placement and bookkeeping, one bridge lemma the consumer needs, and one test that exercises the hard inclusion.

## Findings

1. **Statement against the plan.** `ker_sub_smul_le_span_of_eigen` matches `docs/notes/2026-11-27-t1-plan.md` node A2 token for token (binders, `hS`, `he`, `hspan`, the conclusion). There is no literature definition to compare against: the rung is linear algebra over a field, and the literature step it formalizes is the inventory's "by linear algebra" (the −d-eigenspace of ∧²φ on ∧²H¹ is spanned by ∧²V₊ and ∧²V₋, §1 of the plan). Field by field: `K` any field; `V`, `W` arbitrary vector spaces, no finiteness; `ι` arbitrary, no `Fintype`; `e` need not be a basis, need not be nonzero; `B` bilinear with the same `V` in both slots, matching `deRhamCupBilinear A 1 1 2 _ : H_dR^1(A) →ₗ[ℂ] H_dR^1(A) →ₗ[ℂ] H_dR^2(A)`.

2. **Hypotheses satisfiable.** `EigenProductExample` supplies `hS`, `he`, `hspan` over ℚ (`T = diag(1, −1)`, `B` the tensor product into ℚ^(2 × 2)). The kernel is neither ⊥ (`B (e 0) (e 1)` is a nonzero member) nor ⊤ (`B (e 0) (e 0)` is excluded), so with `ker_eq` the span side is neither ⊥ nor ⊤ either.

3. **Every hypothesis is used.** `hS` and `he` give the eigenvector property of each product; `hspan` splits `w` into the `c`-part and the rest. The converse `span_le_ker_sub_smul_of_eigen` correctly omits `hspan`. Probe: without `hspan` the inclusion fails (`V = W = ℚ`, `B = 0`, `T = id`, `μ = 1`, `S = −id`, `c = −1`: the kernel is ℚ and the span is over the empty set), checked in Lean as a `¬ (… ≤ …)` example.

4. **No trivial proof.** Tried `le_top.trans hspan.ge`, `intro w hw; simp_all` and `aesop` on the main statement; all fail. The conclusion has no definition that unfolds to `True`, no coercion, and the index type is arbitrary (an empty `ι` forces `W = 0` through `hspan`, where the statement is true for the right reason).

5. **Checker.** `python3 tools/check.py --no-build` exits 0 with `ACCEPTED: all checks passed`. Axioms: `ker_sub_smul_le_span_of_eigen`, `ker_sub_smul_eq_span_of_eigen`, `EigenProductExample.ker_eq`, `EigenProductExample.mem_ker` use `[Classical.choice, Quot.sound, propext]`; `span_le_ker_sub_smul_of_eigen` uses `[Quot.sound, propext]`. The five names are the ledger's five declarations.

6. **Equality first.** The rung proves the equality `ker_sub_smul_eq_span_of_eigen`, exact, no scalar. The ledger asked only for the inclusion; the equality is stronger and costs nothing.

7. **Fit with `weil-surface-reduction` (plan node B).**
   - The −d-eigenspace. `weilSpace` (A3) is written `LinearMap.ker (… + d • LinearMap.id)`; on `H_dR^2` the reduction will write `LinearMap.ker (S + (d : ℂ) • LinearMap.id)` with `S = deRhamPullback f 2`. The rewrite to this rung's form, checked:
     ```lean
     example {W : Type*} [AddCommGroup W] [Module ℂ W] (S : W →ₗ[ℂ] W) (d : ℕ) :
         LinearMap.ker (S + (d : ℂ) • LinearMap.id) =
           LinearMap.ker (S - (-(d : ℂ)) • LinearMap.id) := by
       rw [neg_smul, sub_neg_eq_add]
     ```
     so the reduction applies the theorem at `c := -(d : ℂ)`.
   - `hS`. With `B = deRhamCupBilinear A 1 1 2 _`, `T = deRhamPullback f 1`, `S = deRhamPullback f 2`, `hS x y` is `deRhamPullback_cup` (A5) after `deRhamCupBilinear_apply` (`rfl`). The degree bookkeeping (`ℕ` degrees on `deRhamPullback`, `ℤ` on `deRhamCup`, conventions row "de Rham cup order") is A5's to settle; nothing here constrains it.
   - `he` from `Module.End.HasEigenvector`. `fun i => (h i).apply_eq_smul` converts, checked; no extra variant needed.
   - `S` defined only through `B` on the span. Not needed: A5 states `deRhamPullback_cup` for all `x y`.
   - `hspan`. **Missing.** The reduction's hypothesis is `Submodule.span ℂ (Set.image2 (fun x y => deRhamCup x y 2 _) Set.univ Set.univ) = ⊤`; this rung asks for the span of the products of the family `e`. The bridge is a general Mathlib-only lemma that belongs in this module (required change 3); it compiles in seven lines through `Submodule.map₂_span_span` and `Set.image2_range`. With `e` a basis, `he := e.span_eq`.
   - With `μ = ![i√d, i√d, −i√d, −i√d]` the set `{p | μ p.1 * μ p.2 = −d}` is the eight pairs inside `{0,1}²` and `{2,3}²`; excluding the mixed pairs needs `d ≠ 0`, which `IsWeilTypeSurface` supplies (`0 < d`). That computation is the reduction's.

8. **Mathlib equivalents.** None at the pin. Searched `Mathlib/LinearAlgebra/Eigenspace/` and `Mathlib/Algebra/Lie/` for eigenspaces of tensor products or bilinear images (`eigenspace.*tensor`, `mul_mem_eigenspace`, `eigenspace_eq_span`). Nearest: `Module.End.hasEigenvalue_toLin_diagonal_iff` (`Eigenspace/Matrix.lean`) uses the same `eigenspaces_iSupIndep` and `disjoint_biSup` argument for one diagonal operator; `LieModule` weight spaces of tensor products (`Algebra/Lie/Weights/Basic.lean`) are the additive analogue for derivations. Neither states "eigenvectors spanning `W` cut out each eigenspace as the span of those with that eigenvalue", which is the core of this proof once the product structure gives the eigenvalues.

9. **Placement.** The module imports only Mathlib (`pinwalk.py` layer 0) and names no Weil object; the directory `Weil/Eigen/` comes from `next.py`'s fallback for an id with no `module`. The #212 layout keeps Mathlib-only general lemmas under `HodgeLadder/General/` with a row in `docs/gaps.md` "General lemmas kept local" (decision 0011). The candidate adds no gaps row, so a pin walk would skip it. Move it to `HodgeLadder/General/EigenProducts.lean`; the namespace `HodgeLadder` and the declaration names stay (other `General` modules also use the root namespace, for example `General/Codimension.lean`), so the ledger's `declarations` list is unchanged.

10. **Nonvacuity sharpness.** The example's facts all come from the easy direction: `mem_ker`'s first conjunct rewrites with `ker_eq` and uses `subset_span` (the content of `span_le_ker_sub_smul_of_eigen`), and the third conjunct is a direct computation. No declaration applies the hard inclusion, the content of A2. The smallest test that does: a `−1`-eigenvector of the example's `S` has zero `(0, 0)` coordinate, derived from `ker_sub_smul_le_span_of_eigen` (required change 4). It would fail if the inclusion were replaced by anything weaker than the span bound.

11. **Conventions.** Used: the eigenvalue convention `w ∈ ker (S − c • id) ↔ S w = c • w`, which agrees with Mathlib's `Module.End.eigenspace f μ = ker (f − μ • 1)` (`mem_eigenspace_iff` in the proof); the product `μ i * μ j` is commutative and the theorem ranges over all ordered pairs, so the factor order of `B` (row "de Rham cup order") cannot matter; the scalar action on `H_dR` (row "Complex structure on H_dR") enters only at the consumer. No sign enters this rung, and its truth depends on none. The sign that matters downstream is `weilSpace`'s `+ d • id` meaning eigenvalue `−d`; it belongs to the planned row "Weil space" (G1, `weil-surface-statement`), which should record the rewrite in finding 7. No new row is needed for this rung.

12. **Pin drift.** Checked at the current pin; Mathlib-only. Declarations it depends on: `Module.End.eigenspaces_iSupIndep`, `Module.End.mem_eigenspace_iff`, `iSupIndep_def`, `Submodule.disjoint_def`, `Submodule.span_union`, `Pi.basisFun`, and for change 3 `Submodule.map₂_span_span`, `Set.image2_range`. A bump that renames `iSupIndep` (it was `CompleteLattice.Independent` until 2024) breaks the build loudly; no change could alter the statement's truth.

13. **Bookkeeping.** `docs/roadmap.md` line 199 still says `open` for this rung.

## Required changes

1. Move `HodgeLadder/Weil/Eigen/Algebra.lean` to `HodgeLadder/General/EigenProducts.lean`, module `HodgeLadder.General.EigenProducts`; update the import in `HodgeLadder.lean` and the ledger field to `"module": "HodgeLadder.General.EigenProducts"`. Remove the empty `HodgeLadder/Weil/` directory. Declaration names unchanged.

2. Add to `docs/gaps.md`, "General lemmas kept local", a new category after "Linear algebra: Clifford and exterior algebras":

   ```
   ### Linear algebra: eigenspaces

   Diff at a bump: Mathlib `LinearAlgebra/Eigenspace/`, `Algebra/Module/Submodule/Bilinear.lean`, `Order/SupIndep.lean`.

   | Local declaration | Module | Layer | Why local | Opened |
   |---|---|---|---|---|
   | `ker_sub_smul_le_span_of_eigen`, `span_le_ker_sub_smul_of_eigen`, `ker_sub_smul_eq_span_of_eigen` (if `T` is diagonal on a family `e` with eigenvalues `μ`, `S (B x y) = B (T x) (T y)` and the `B (e i) (e j)` span `W`, then `ker (S − c • id)` is the span of the `B (e i) (e j)` with `μ i * μ j = c`; any field, any index type), `span_range_prod_eq_top_of_span` (products of a spanning family span `W` when all products do) | `HodgeLadder.General.EigenProducts` | 0 | general linear algebra, not in Mathlib at the pin: Mathlib has `eigenspaces_iSupIndep` and the one-operator diagonal case `hasEigenvalue_toLin_diagonal_iff`, no eigenspace of a bilinear image; rung `weil-eigen-algebra` | 2026-11-27 |
   ```

3. Add to the module, and to the ledger's `declarations`, the bridge lemma (checked as written):

   ```lean
   /-- If a family `e` spans `V` and the products `B x y` span `W`, then the products
   `B (e i) (e j)` span `W`. -/
   theorem span_range_prod_eq_top_of_span {K V W ι : Type*} [Field K] [AddCommGroup V]
       [Module K V] [AddCommGroup W] [Module K W] (B : V →ₗ[K] V →ₗ[K] W) (e : ι → V)
       (he : Submodule.span K (Set.range e) = ⊤)
       (hB : Submodule.span K (Set.image2 (fun x y => B x y) Set.univ Set.univ) = ⊤) :
       Submodule.span K (Set.range fun p : ι × ι => B (e p.1) (e p.2)) = ⊤ := by
     have h1 := Submodule.map₂_span_span K B (Set.range e) (Set.range e)
     have h2 := Submodule.map₂_span_span K B (Set.univ : Set V) (Set.univ : Set V)
     rw [Submodule.span_univ] at h2
     rw [he, h2, hB, Set.image2_range] at h1
     exact h1.symm
   ```

   It needs `public import Mathlib.Algebra.Module.Submodule.Bilinear`. Add it to the module docstring's "Main results".

4. Add to `EigenProductExample`, and to the ledger's `declarations`, the test of the hard inclusion (checked as written):

   ```lean
   /-- The inclusion `ker_sub_smul_le_span_of_eigen`, applied in the example: a `-1`-eigenvector
   of `S` has zero `(0, 0)` coordinate. -/
   theorem apply_zero_zero_of_mem_ker (w : Fin 2 × Fin 2 → ℚ)
       (hw : w ∈ LinearMap.ker (S - (-1 : ℚ) • LinearMap.id)) : w (0, 0) = 0 := by
     have hw' := ker_sub_smul_le_span_of_eigen B T S hS e μ he hspan (-1) hw
     refine Submodule.span_induction (p := fun v _ => v (0, 0) = 0) ?_ ?_ ?_ ?_ hw'
     · rintro _ ⟨⟨i, j⟩, hp, rfl⟩
       show B (e i) (e j) (0, 0) = 0
       rw [B_e (i, j)]
       simp only [Set.mem_ofPred_eq] at hp
       fin_cases i <;> fin_cases j
       all_goals (try simp [μ] at hp ⊢)
       all_goals (try norm_num at hp)
     · rfl
     · intro x y _ _ hx hy; simp [hx, hy]
     · intro a x _ hx; simp [hx]
   ```

   Append to the ledger note: "The hard inclusion is exercised by EigenProductExample.apply_zero_zero_of_mem_ker; span_range_prod_eq_top_of_span turns weil-surface-reduction's image2 span hypothesis into hspan."

5. `docs/roadmap.md` line 199: status `checked`, module `HodgeLadder.General.EigenProducts`.

## Optional

- The necessity example of finding 3 (`hspan` cannot be dropped) as a named test in `EigenProductExample`.
- The reduction will also need, over ℂ, `ker (T − i√d • id) ⊔ ker (T + i√d • id) = ⊤` from `T² = −d • id` and `d ≠ 0`. It is Mathlib-only and fits this module; a separate small rung keeps this one closed.

## What was tried

- Trivial closes of the main statement (`le_top`, `simp_all`, `aesop`): failed, as expected.
- Dropping `hspan`: a counterexample over ℚ, checked.
- The consumer's rewrite, the `HasEigenvector` form of `he`, the bridge lemma and the hard-direction test: all compiled against the current build.
- Mathlib search for an existing statement: none found (finding 8).
