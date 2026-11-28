# Handoff 2026-11-27: `weil-eigen-algebra`

- Checked: `HodgeLadder/General/EigenProducts.lean`, Mathlib only (layer 0), imported from `HodgeLadder.lean`, 9 declarations in the ledger, standard axioms only.
- Statement: `ker_sub_smul_le_span_of_eigen` is plan node A2 as written, for any field and any index type. The equality `ker_sub_smul_eq_span_of_eigen` holds under the same span hypothesis; the converse inclusion needs none. Proof by `Module.End.eigenspaces_iSupIndep`, about 30 lines.
- Bridge: `span_range_prod_eq_top_of_span` turns the reduction's `Set.image2` span hypothesis and a spanning family into `hspan` (`Submodule.map₂_span_span`).
- Splitting: `isCompl_ker_sub_smul_ker_add_smul`, if `T (T x) = (s * s) • x`, `s ≠ 0` and `2 ≠ 0`, the `s`- and `-s`-eigenspaces of `T` are complementary. Over ℂ with `s = i√d` this is `H¹ = V₊ ⊕ V₋` for `weil-surface-reduction`.
- Tests: over ℚ with `T = diag(1, -1)` and the tensor product, `mem_ker` (a nonzero `-1`-eigenvector, a product excluded), `apply_zero_zero_of_mem_ker` (the hard inclusion applied), `not_ker_le_span_without_hspan` (the span hypothesis cannot be dropped).
- Signs: none. The reduction applies the theorem at `c := -(d : ℂ)` after `rw [neg_smul, sub_neg_eq_add]`.
- Timing: the module checks in about 4 s.
- Red team: `docs/sketches/weil-eigen-algebra.redteam.md`, pass with changes, changes 1 to 5 and both optional items applied.
- Next: `weil-space` and `de-rham-pullback`, then `weil-surface-statement` and `weil-surface-reduction`.
