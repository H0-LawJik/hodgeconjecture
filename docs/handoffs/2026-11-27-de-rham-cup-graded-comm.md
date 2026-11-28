# Handoff 2026-11-27: `de-rham-cup-unique` and `de-rham-cup-antisymm-h1`

- Checked: `HodgeLadder/Hodge/DeRhamCupGradedComm.lean` (module `HodgeLadder.Hodge.DeRhamCupGradedComm`), imported from `HodgeLadder.lean`, 6 declarations across the two rungs, standard axioms only.
- `de-rham-cup-unique`: `deRhamCupBilinear_unique`, the ledger statement verbatim (RT6 of `docs/sketches/de-rham-cup.redteam.md`, unchanged); `deRhamCupBilinear_eq_iff` adds the converse, so `hP` is satisfiable. On smooth projective integral X a `ℂ`-bilinear P with P (ι α) (ι β) = ι (α ∪ β) is `deRhamCupBilinear`.
- `de-rham-cup-antisymm-h1`: `deRhamCup_antisymm_one`, the ledger statement verbatim, as the case a = b = 1 of `deRhamCup_gradedComm`: `deRhamCup y x n _ = (-1 : ℤ) ^ (a * b) • deRhamCup x y n _` for `a b n : ℕ`, `a + b = n`, the sign a `ℤ`-scalar on the right as in `Cup.cup_gradedComm`. Bundled: `deRhamCupBilinear_flip`. Red team change 5: `deRhamCup_self_of_odd`, `deRhamCup x x n _ = 0` in odd degree.
- Proof: `LinearMap.ext_on` twice with `span_range_fieldToDeRhamCohomology_rat`, then `fieldToDeRhamCohomology_cup`, `Cup.cup_gradedComm`, `map_zsmul`. Rewriting at general `ℕ` degrees avoids the cast friction RT7 recorded at literal degrees.
- Signs: only `(−1)^{ab}`, symmetric in a and b, so independent of the diagrammatic factor order; the sheaf-singular comparison sign cancels.
- Non-vacuity: uniqueness is separated by `0` and `−deRhamCupBilinear` at degree (0, 0) and on ℙ² at (2, 2). Every projective X at the pin has b₁ = 0, so the antisymmetry has only zero instances there; `Tests.gm2_deRhamCup_antisymm` on the affine 𝔾ₘ² is a separate theorem with a nonzero product. A projective instance waits on `cup-odd-degree-test`.
- Timing: the module checks in about 37 s.
- Red team: `docs/sketches/de-rham-cup-graded-comm.redteam.md`, pass with changes, all implemented (changes 1 to 4, optional change 5). The kept-local row in `docs/gaps.md` (layer 24) also lists `deRhamCup_self_of_odd`.
- Next: `cup-hodge-filtration`; `cup-odd-degree-test` for a projective witness with H¹ ≠ 0.
