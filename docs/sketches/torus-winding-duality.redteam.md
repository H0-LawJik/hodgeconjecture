# Red team: `torus-winding-duality`

Date: 2026-11-27. Branch `track/torus-winding-duality` at `3a13a96`, worktree off `main` `8eba28e`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the ledger toolchain block. Target: `HodgeLadder/Torus/Winding/Duality.lean` (module `HodgeLadder.Torus.Winding.Duality`, 23 public declarations, not yet root-imported or in the ledger). Read: `python3 tools/next.py torus-winding-duality`, the ledger entries `torus-winding-duality`, `winding-torus-cup`, `torus-cycle-pairing`, `torus-singular-cohomology`, `winding-class-pullback`; `docs/sketches/torus-singular-cohomology.md`, `docs/sketches/cup-odd-degree-test.redteam.md`; `HodgeLadder/Cup/{TorusCycle,TorusPairing,WindingTorus,SingularCup}.lean`, `HodgeLadder/Tests/TorusSingular.lean`; `docs/conventions.md` rows "Singular cup product", "Sheaf–singular comparison Ψ", "Torus cycle and winding classes", "Cup product"; `docs/gaps.md`, `docs/pin-walk.md`, `docs/references.md`. Probes ran in a scratch directory, since deleted.

**Verdict: pass with changes.** The sign is the literature's: with Hatcher's front-face times back-face cup on the counterclockwise lower triangle minus the clockwise upper triangle, ⟨aᵢ ⌣ aⱼ, T_kl⟩ is the 2 × 2 determinant of edge values, which is the formula stated, and at n = 2, k = 0, l = 1 it agrees with the checked `winding-torus-cup` values through an independent route (probe P1). The statement is non-trivial, the pairing is non-degenerate on the i < j products (probe P5 proves their linear independence from this theorem alone in 20 lines), and every declaration uses only the three standard axioms. The changes: three lemmas carry a hypothesis `k ≠ l` their proofs do not use, the ledger and roadmap titles write the cup as `∪` (the register's symbol for the sheaf cup, which differs by −1 in degree (1, 1)), and the landing needs a conventions row, a gaps row and the ledger entry. Nothing here weakens the statement.

## Findings

1. **Sign: front face times back face on T_kl (attack 1).** The literature cup is (φ ⌣ ψ)(σ) = φ(σ|[v₀, v₁]) ψ(σ|[v₁, v₂]) on a singular 2-simplex (`Hatcher2002` §3.2; quoted from memory, section locator as listed in `docs/references.md`, page unverified). On the lower triangle [(0,0), (1,0), (1,1)] (`lowerTriangle`, `lowerTriangle_single` checks the vertices), the front edge is δ₂ (vertices 0, 1: (0,0) to (1,0)) and the back edge δ₀ (vertices 1, 2: (1,0) to (1,1)), with Mathlib's δᵢ skipping vertex i. The checked `torusPairing_tcCup` uses the face identities `torus_h0`, `torus_h2` to rewrite the upper-triangle term, giving ⟨a ⌣ b, lower − upper⟩ = a(e) b(f) − a(f) b(e), e = front, f = back. The candidate's edge lemmas give, for `T_kl`, aᵢ(e) = [i = k] (`val_frontEdge_coord`) and aᵢ(f) = [i = l] (`val_backEdge_coord`); substituting, [i = k][j = l] − [i = l][j = k]. The literature value of ⟨αᵢ ⌣ αⱼ, [T_kl]⟩ for the circle-dual basis and the subtorus oriented by (e_k, e_l) is the same determinant det((αᵢ(e_k), αᵢ(e_l)), (αⱼ(e_k), αⱼ(e_l))), the singular counterpart of ∫ dxᵢ ∧ dxⱼ over T_kl (the exterior-algebra description of H*(Tⁿ) is `Hatcher2002` §3.2, locator unverified). Field by field:

   | Literature | Lean | Agrees |
   |---|---|---|
   | Tⁿ = (ℝ/ℤ)ⁿ | `torus n = TopCat.of (UnitAddTorus (Fin n))`, `UnitAddTorus d = d → UnitAddCircle`, product topology | yes |
   | αᵢ dual to the i-th circle | `coordWinding i`: winding class of `x ↦ toCircle (x i)` = exp(2πi xᵢ) (`AddCircle.toCircle_apply_mk`, `Circle.coe_exp`, period 1, checked inside `coordChar_coordTorus`) | yes, αᵢ(e_k) = [i = k] is `val_frontEdge_coord` |
   | [T_kl] oriented by (e_k, e_l) | `T_kl ∘ (lower − upper)`, `T_kl (s, t)` with s in coordinate k, t in coordinate l; lower − upper carries ds ∧ dt (register row "Torus cycle and winding classes", red team 2026-11-26) | yes |
   | cup of Hatcher | `cupSing` = Tau Ceti `singularCup` along `cohIso`, no sign (row "Singular cup product") | yes |
   | value | `(if i = k ∧ j = l then 1 else 0) - (if i = l ∧ j = k then 1 else 0)`, exact, in ℚ | yes |

   Reduction at n = 2 (probe P1, compiled): with g₁ = `coordChar 0`, g₂ = `coordChar 1`, T = `coordTorus 0 1`, the checked `torusEval_cupSing_winding` and `torusEval_cupSing_winding_swap` give ⟨a₀ ⌣ a₁, T₀₁⟩ = 1 and ⟨a₁ ⌣ a₀, T₀₁⟩ = −1, the hypotheses h₁, h₂ discharged by `coordChar_coordTorus` and `simp [coordPhase]`. That route uses none of the candidate's edge lemmas, so it is an independent check of the sign at the base case. Orientation of T_kl: Mathlib and upstream fix no orientation of `UnitAddTorus`; the only orientation in the ladder is the square's (lower counterclockwise, upper clockwise), and T_kl inherits it with s on coordinate k. For k < l this is the restriction of dx₀ ∧ ⋯ ∧ dx_{n−1}'s coordinate order; T_lk gives the negative (`torusEval_coordTorus_swap`, value −1). Nothing is off.

2. **Ψ and the factor order.** The file contains no Ψ. A consumer that reads sheaf classes xᵢ with Ψ xᵢ = aᵢ gets ⟨Ψ(xᵢ ∪ xⱼ), T_kl⟩ = −([i = k][j = l] − [i = l][j = k]) from `cup_singular_comparison` (row "Sheaf–singular comparison Ψ"); the module docstring says so. The ledger title and the roadmap row (line 230) write "⟨aᵢ ∪ aⱼ, T_kl⟩". In the register `∪` is the Yoneda cup (row "Cup product"), and with that reading the formula is off by −1 in exactly the degree this rung lives in. Required change 2 writes ⌣ and names `cupSing`.

3. **Evaluation pairing and independence downstream (attack 2).** `torusEval` is a ℚ-linear map `Cohomology ℚ Y 2 →ₗ[ℚ] ℚ`, the descent of φ ↦ φ(σ₁) − φ(σ₂) (checked in `torus-cycle-pairing`), composed with `cohIso`; it is not degenerate since it takes the value 1. For i < j and k < l the second indicator [i = l][j = k] forces j = k < l = i, so the evaluation matrix on the H² family is the identity. Probe P5 (compiled, below) proves `LinearIndependent ℚ (fun p : {p : Fin n × Fin n // p.1 < p.2} => cupSing (torus n) (coordWinding p.1.1) (coordWinding p.1.2) 2 rfl)` for every n from `torusEval_coordTorus_cup`, `map_sum`, `map_smul` and `Finset.sum_eq_single`; this is the sketch's `linearIndependent_coordCup` with its `coordCup` index type, so the statement shape fits step 9 for H² unchanged. For H¹, step 9 cups on the right with a_m and evaluates on T_km; the formula covers it (value [i = k] for i ≠ m), and the missing input is additivity of `cupSing` in the first slot, which has no lemma at the pin (grep of `HodgeLadder/` for `cupSing_add`, `add_cupSing`, `smul_cupSing`: none). That is `torus-singular-cohomology`'s to supply, as its sketch says.

4. **coordTorus and the hypothesis k ≠ l (attack 3).** For k ≠ l, `coordTorus_apply` gives coordinate k equal to s, coordinate l equal to t and the others 0, so T_kl descends to an injective continuous map from (ℝ/ℤ)² onto the subtorus through 0 in directions k, l: a genuine 2-torus. For k = l the inner update is overwritten, T_kk (s, t) = update 0 k t, a circle. Three findings:
   - the proofs of `coordTorus_apply` and `coordChar_coordTorus` do not use `hkl` (probe P2, P4: both compile with `hkl` deleted and the same proofs). `val_backEdge_coord` also does not need it: its case i = k, i ≠ l closes with `hl` alone (probe P3).
   - `val_frontEdge_coord` does need it: on T_kk the front edge is constant, so the value of a_k is 0, against the claimed [k = k] = 1 (probe P3 computes 0).
   - The main formula does not need it. At k = l both sides are 0 (left: every front-edge value is 0, so the determinant vanishes; right: the two indicators coincide). Probe P4 proves `torusEval_coordTorus_cup` with no hypothesis in 10 lines by splitting on `k = l`. Keeping `hkl` matches the posted statement and every consumer has k ≠ l from i < j; dropping it would be a strengthening (optional change O1).

   An unused hypothesis in a lemma is not a vacuity: the conclusions are the honest coordinate formulas. It is removed in required change 1 because the register asks for every hypothesis to carry weight and because downstream callers (`winding-class-pullback`, the elliptic transports) will call `coordChar_coordTorus` on the diagonal-free API.

5. **Triviality and circularity (attack 4).** `simp` on the main goal makes no progress (probe). The left side unfolds through `windingClass` (`cohIso` of the class of the port's `rationalWindingCochain`), `cupSing`, `torusEval`; none is a constant, and `torus_two_cup_swap_ne` would fail for a zero or a symmetric cup. The proof uses `torusEval_cupSing` (checked) and the four edge values computed through `simplexIncrement_torus` and `val_windingTC_of_increment` from `logIncrement_of_exp`; the edge values are derived from the phase functions, so there is no circular use of the formula. No ℕ∞ coercion, no empty index type: `Fin n` with k ≠ l needs n ≥ 2, and the T² lemmas instantiate n = 2.

6. **Interface.** Not an interface rung; no structure, no axioms.

7. **Checker and axioms.** `python3 tools/check.py --no-build` on the branch: "ACCEPTED: all checks passed" (the rung is not in the ledger yet, so the checker names none of its declarations). `#print axioms` on all 23 public declarations of the module (scratch file): each depends on `[propext, Classical.choice, Quot.sound]`. `lake env lean HodgeLadder/Torus/Winding/Duality.lean`: no errors, no warnings; build of the module from a current tree in about 3 s.

8. **Conventions (item 6).** Used, with the dependence of the truth on each:

   | Convention | Where | Register row | Truth depends on it |
   |---|---|---|---|
   | front face δ₂ times back face δ₀, no sign | `torusEval_cupSing` | "Singular cup product" | the value, yes (back face first would transpose and negate the antisymmetric part); independence, no |
   | δᵢ skips vertex i | `val_*_of_phase` through `lowerFace_single` | covered by the cup row | the identification front = (0,0)→(1,0), yes; checked by `lowerTriangle_single` |
   | cycle lower − upper | `torusEval` | "Torus cycle and winding classes" | the sign of every value, yes; independence, no |
   | s in coordinate k, t in coordinate l | `coordTorus` | missing; new row in change 3 | the sign (T_lk = −T_kl), yes; independence and span, no |
   | aᵢ = winding of exp(2πi xᵢ), period 1 | `coordChar` via `AddCircle.toCircle` | "Torus cycle and winding classes" | no: negating every aᵢ (exp(−2πi x) or −1/2πi) leaves every product unchanged; a rescaling c of all aᵢ multiplies values by c² |
   | generator order i < j for H² | consumers (`coordCup`) | new row | span and rank, no; explicit elements in F2, yes (aⱼ ⌣ aᵢ = −aᵢ ⌣ aⱼ by `cupSing_gradedComm`) |
   | cohIso has no degree sign | `windingClass`, `torusEval`, `cupSing` | "Singular cup product" | the values, yes; checked as degreewise `homLinearEquiv` (red team 2026-11-26) |
   | Ψ(x ∪ y) = (−1)^{pq} cupSing(Ψx)(Ψy) | consumers only | "Sheaf–singular comparison Ψ" | values read from sheaf cups, yes (−1); spans, no |

   Borrowed results and their conventions: `torusPairing_tcCup` and `torusEval_cupSing` are stated against `cupSing` and `torusEval` exactly as used; `simplexIncrement_torus` measures the increment from vertex 0 to vertex 1, matching π(1,0) − π(0,0) on the front edge and π(1,1) − π(1,0) on the back edge (the `succAbove` values in `val_*_of_phase`: δ₂ keeps vertices 0, 1, δ₀ keeps 1, 2). No row is missing beyond the coordinate-torus row.

9. **Equality first (item 7).** The rung is an identity in ℚ, proved exactly for every i, j and k ≠ l, with no scalar; the docstrings state the sign. It is a step toward the equalities of `torus-singular-cohomology` (`span_coordCup = ⊤`, `finrank_cohomology_two_torus n = n.choose 2`), which exists as an open rung with this as a dependency.

10. **Non-vacuity (item 7b).** The smallest test that fails for a trivially true statement is `HodgeLadder.Torus.torus_two_cup_swap_ne` (fails if `cupSing` were zero or symmetric on degree one), with `torusEval_coordTorus_cup_kl` (fails if `torusEval` or the cup vanished); both exist in the candidate. `torus_two_cup_self_eval` (value 0) holds for a zero cup too, so it adds no non-vacuity; keep it as a value lemma. The sharper test is probe P5, linear independence of all n(n−1)/2 products, which belongs to `torus-singular-cohomology` (optional change O2).

11. **Placement (attack 5).** `HodgeLadder/Torus/Winding/Duality.lean` is `next.py`'s fallback for an id with no module; the sibling fallbacks are `HodgeLadder/Torus/Singular/Cohomology.lean` and `HodgeLadder/Torus/Homology/Bound.lean`, so the T1 C6 cluster lands in one directory `HodgeLadder/Torus/`. Keep the path. Moving the content next to `Cup/WindingTorus.lean` would put a T1 torus file in the cup front, and editing `WindingTorus.lean` itself (layer 11, 9 downstream modules) for the two general edge lemmas would rebuild nine modules; a new leaf at layer 12 (`pinwalk.py --hubs`, downstream 0) is the layout `docs/pin-walk.md` asks for. The namespace `HodgeLadder.Torus` with the abbrev `torus` is clash-free: no `UnitAddTorus` or `toCircle` use elsewhere in `HodgeLadder/` or the port, and `HodgeLadder.Tests.TorusSingular` works on ℂˣ × ℂˣ, a different space.

    `val_frontEdge_of_phase` and `val_backEdge_of_phase` are general (any space, any T, any g with g ∘ T = exp(2πi π)) and generalize `winding-torus-cup`'s four edge lemmas. They shadow nothing in Mathlib; upstream at the pin has no `ChernWinding` file (grep of `.lake/packages/HodgeConjecture` for `rationalWindingCochain`, `logIncrement_of_exp`: none), so they are about the port's winding cochain, which an upstream landing of the Lefschetz stack would replace. That is the case the gaps table exists for (row in change 4, category "Singular homology, cohomology and simplicial cochains", layer 12, between the layer-10 and layer-13 rows). The four `WindingTorus` edge lemmas and `simplexIncrement_torus`, `val_windingTC_of_increment` have no row either; that is a pre-existing omission (optional change O3).

12. **Pin drift (item 8).** Checked at `2ead713`, the current pin, against the shared `.lake/packages` of `main`; `git diff main --stat` shows only the new file. No drift. At a bump the dependencies whose change could alter truth are `AddCircle.toCircle_apply_mk` (normalization exp(2πi x/T)), `Circle.coe_exp` and upstream's `AlgebraicTopology.Singular.Cohomology` through `cohIso`. A flip of the `toCircle` sign negates every aᵢ and leaves every product unchanged (finding 8); a change of `UnitAddCircle`'s period breaks `coordTorus_one_left` loudly; a degree sign in a respelled `cohIso` would change `torusEval`, and the pins of `torus-cycle-pairing` already guard that path.

## Probes

All compiled at the pin in a scratch file importing the candidate module; deleted afterwards.

- P1: base case through `torusEval_cupSing_winding` and `_swap` (finding 1).
- P2, P3: `coordTorus_apply`, `coordChar_coordTorus`, `val_backEdge_coord` without `hkl`; front-edge value 0 on T_kk.
- P4: the main formula with no `k ≠ l`:

```lean
theorem cup_all {n : ℕ} (k l i j : Fin n) :
    torusEval (coordTorus_one_left k l) (coordTorus_one_right k l)
        (cupSing (torus n) (coordWinding i) (coordWinding j) 2 rfl) =
      (if i = k ∧ j = l then 1 else 0) - (if i = l ∧ j = k then 1 else 0) := by
  by_cases hkl : k = l
  · subst hkl
    have hf : ∀ m : Fin n, val (windingTC (coordChar m) (coordChar_ne_zero m))
        (frontEdge (coordTorus k k)) = 0 := fun m =>
      val_frontEdge_of_phase _ _ _ (continuous_coordPhase k k m) (coordChar_coordTorus' k k m) 0
        (by by_cases h : m = k <;> simp [coordPhase, h])
    rw [coordWinding, coordWinding, torusEval_cupSing, hf, hf]
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp [hi, hj]
  · exact torusEval_coordTorus_cup hkl i j
```

  (`coordChar_coordTorus'` is `coordChar_coordTorus` with `hkl` removed and `k l` explicit.)
- P5: independence of the H² products:

```lean
example (n : ℕ) : LinearIndependent ℚ (fun p : {p : Fin n × Fin n // p.1 < p.2} =>
    cupSing (torus n) (coordWinding p.1.1) (coordWinding p.1.2) 2 rfl) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have hkl : q.1.1 ≠ q.1.2 := ne_of_lt q.2
  have := congrArg (torusEval (coordTorus_one_left q.1.1 q.1.2)
    (coordTorus_one_right q.1.1 q.1.2)) hg
  rw [map_sum, map_zero] at this
  simp only [map_smul, torusEval_coordTorus_cup hkl, smul_eq_mul] at this
  rw [Finset.sum_eq_single q] at this
  · have h2 : ¬ (q.1.1 = q.1.2 ∧ q.1.2 = q.1.1) := fun h => hkl h.1
    simpa [h2] using this
  · intro p _ hpq
    have hp := p.2
    have hq := q.2
    have h1 : ¬ (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) := fun h =>
      hpq (Subtype.ext (Prod.ext h.1 h.2))
    have h2 : ¬ (p.1.1 = q.1.2 ∧ p.1.2 = q.1.1) := by
      rintro ⟨h3, h4⟩; rw [h3, h4] at hp; exact lt_asymm hp hq
    simp [h1, h2]
  · simp
```

Tried and failed: `simp` on the main goal (no progress); no other short route closes it.

## Required changes

1. In `HodgeLadder/Torus/Winding/Duality.lean`, remove the unused hypothesis from three lemmas and make `k l` explicit, with these signatures (proofs unchanged, except that the `hkl` in `simp [coordPhase, hkl]` of `val_backEdge_coord` becomes `hl`):
   - `theorem coordTorus_apply {n : ℕ} (k l : Fin n) (p : ℝ × ℝ) (i : Fin n) : …` with docstring "The coordinates of `T_kl (s, t)`; for `k = l` the second update wins."
   - `theorem coordChar_coordTorus {n : ℕ} (k l i : Fin n) (p : ℝ × ℝ) : …` (its `rw [coordTorus_apply hkl, …]` becomes `rw [coordTorus_apply, …]`).
   - `theorem val_backEdge_coord {n : ℕ} (k l i : Fin n) : …` with docstring "The winding value of `aᵢ` on the back edge of `T_kl`: `[i = l]`, for all `k l`."
   Update the call sites: `val_frontEdge_coord` uses `(coordChar_coordTorus k l i)`; `torusEval_coordTorus_cup` uses `val_backEdge_coord k l, val_backEdge_coord k l` in its `rw`. `val_frontEdge_coord` keeps `hkl` (it is false at k = l). The whole change, applied to a copy of the file, compiles at the pin with no warnings.
2. Ledger title of `torus-winding-duality` and `docs/roadmap.md` line 230: replace `⟨aᵢ ∪ aⱼ, T_kl⟩` by `⟨aᵢ ⌣ aⱼ, T_kl⟩` and add `(singular cup cupSing)` after it. Roadmap row text: "⟨aᵢ ⌣ aⱼ, T_kl⟩ = [i = k][j = l] − [i = l][j = k] on Tⁿ, singular cup `cupSing`, exact, k ≠ l".
3. `docs/conventions.md`, a new row after "Torus cycle and winding classes":

   `| Coordinate tori of Tⁿ | this repository, `HodgeLadder.Torus.coordWinding`, `HodgeLadder.Torus.coordTorus` (`HodgeLadder/Torus/Winding/Duality.lean`, rung `torus-winding-duality`) | Tⁿ = `UnitAddTorus (Fin n)`; aᵢ ∈ H¹(Tⁿ; ℚ) is the winding class of x ↦ exp(2πi xᵢ) (`AddCircle.toCircle`, period 1); T_kl (s, t) puts s in coordinate k, t in coordinate l and 0 elsewhere, so T_kl ∘ (lower − upper) carries dx_k ∧ dx_l; the H² generators are aᵢ ⌣ aⱼ (`cupSing`) with i < j | the exact values ⟨aᵢ ⌣ aⱼ, T_kl⟩ = [i = k][j = l] − [i = l][j = k]; T_lk gives the negative; a sheaf cup read through Ψ gives the negative (row "Sheaf–singular comparison Ψ"); negating every aᵢ leaves every value unchanged, a rescaling c multiplies them by c²; linear independence, spans and dimensions depend on none of it. A homeomorphism h : Y ≃ₜ Tⁿ transports the values unchanged; whether T_kl corresponds to a given orientation of Y (for E(ℂ) = ℂ/Λ under (s, t) ↦ sω₁ + tω₂, the complex orientation exactly when Im(ω₂/ω₁) > 0) is the consumer's to fix | checked at the pin: edge values by `logIncrement_of_exp`; at n = 2, k = 0, l = 1 the values agree with `torusEval_cupSing_winding` and `_swap` through a route that skips the new edge lemmas (red team 2026-11-27) |`
4. `docs/gaps.md`, section "Singular homology, cohomology and simplicial cochains", a row between the layer-10 row (`ProjectivePlaneFundamental`) and the first layer-13 row:

   `| `HodgeLadder.Torus.val_frontEdge_of_phase`, `HodgeLadder.Torus.val_backEdge_of_phase` (the port's rational winding cochain of g takes the values π(1, 0) − π(0, 0) and π(1, 1) − π(1, 0) on the front and back edges of the square T whenever g ∘ T = exp(2πi π) for a continuous real π; any space, any T) | `HodgeLadder.Torus.Winding.Duality` | 12 | general lemmas on the port's `ChernWinding.rationalWindingCochain`, generalizing the four edge lemmas of `winding-torus-cup`; upstream has no winding cochain at the pin, so a bump that lands upstream's Lefschetz stack checks for an equivalent | 2026-11-27 |`
5. On landing: `public import HodgeLadder.Torus.Winding.Duality` in `HodgeLadder.lean`; ledger entry `"status": "checked"`, `"module": "HodgeLadder.Torus.Winding.Duality"`, `"contributors": ["H0-LawJik"]`, and

   `"declarations": ["HodgeLadder.Torus.torus", "HodgeLadder.Torus.coordChar", "HodgeLadder.Torus.coordWinding", "HodgeLadder.Torus.coordTorus", "HodgeLadder.Torus.coordTorus_apply", "HodgeLadder.Torus.coordTorus_one_left", "HodgeLadder.Torus.coordTorus_one_right", "HodgeLadder.Torus.coordPhase", "HodgeLadder.Torus.coordChar_coordTorus", "HodgeLadder.Torus.val_frontEdge_of_phase", "HodgeLadder.Torus.val_backEdge_of_phase", "HodgeLadder.Torus.val_frontEdge_coord", "HodgeLadder.Torus.val_backEdge_coord", "HodgeLadder.Torus.torusEval_coordTorus_cup", "HodgeLadder.Torus.torusEval_coordTorus_cup_kl", "HodgeLadder.Torus.torusEval_coordTorus_cup_lk", "HodgeLadder.Torus.torusEval_coordTorus_swap", "HodgeLadder.Torus.torusEval_coordTorus_cup_self", "HodgeLadder.Torus.coordWinding_cup_ne_zero", "HodgeLadder.Torus.torus_two_cup_ne_zero", "HodgeLadder.Torus.torus_two_cup_swap_ne"]`

   with note "Checked 2026-11-27. On Tⁿ = UnitAddTorus (Fin n), with aᵢ the winding class of exp(2πi xᵢ) and T_kl (s, t) putting s in coordinate k and t in coordinate l: ⟨aᵢ ⌣ aⱼ, T_kl⟩ = [i = k][j = l] − [i = l][j = k] for k ≠ l, exact, singular cup cupSing (front face times back face), cycle lower − upper; T_lk gives the negative, a sheaf cup read through Ψ the negative. Reduces to winding-torus-cup at n = 2. Red team: docs/sketches/torus-winding-duality.redteam.md." Roadmap row status `checked`.

## Optional changes

- O1. State the formula for all k, l (probe P4) as `torusEval_coordTorus_cup` with `hkl` dropped, or add it as `torusEval_coordTorus_cup_diag` (value 0 on T_kk). A strengthening; consumers lose one side condition.
- O2. Record probe P5 in issue #230 (`torus-singular-cohomology`) as the proof of `linearIndependent_coordCup`; it uses nothing beyond this rung.
- O3. Add a gaps row for `HodgeLadder.Cup.simplexIncrement_torus`, `val_windingTC_of_increment` and the four edge lemmas of `HodgeLadder.Cup.WindingTorus` (layer 11), with the same "why local" text as change 4.
