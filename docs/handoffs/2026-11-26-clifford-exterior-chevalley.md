# Handoff 2026-11-26: `clifford-exterior-chevalley`

- Checked in `HodgeLadder/Markman/Chevalley.lean`: for M finite free over a commutative ring R (no `Nontrivial R`), `spinAction_bijective`, and `spinEquiv : CliffordAlgebra (QuadraticForm.dualProd R M) ≃ₐ[R] Module.End R (ExteriorAlgebra R M)` with `spinEquiv_ι_apply` and `spinEquiv_symm_spinGen`. This is [GolyshevLuntsOrlov2001] Prop. 3.2.1(e).
- Route, GLO's proof with the rank from a count. Spanning for any quadratic form: the sublist products of a spanning list span the Clifford algebra (`span_sublists_prod_eq_top`, an induction on the list with no order on the index set). Surjectivity: matrix units `(e_S * ·) ∘ c ∘ (e_{I∖T} * ·)` up to a sign in `ℤˣ`, where `c` is all dual-basis contractions, which send `e_I` to `1` and kill lower degrees. Injectivity: Orzech property on `R ^ (2 ^ (2 n)) → Cl → End(∧M)`.
- The bridge the red team proposed (`basis_exteriorAlgebra_eq_list_prod`) kept `powersetCard` confined to one lemma; step 2 is about 230 lines.
- By-products: the sublist products of `dualProdList b` are a basis (`linearIndependent_sublistProd_dualProd`, `cliffordDualProdBasis`); `finrank_cliffordAlgebra_dualProd` (rank 2 ^ (2 * finrank R M), needs `Nontrivial R`), `finrank_cliffordAlgebra_dualProd_int` (rank 4).
- Hypothesis test: `spinAction_int_zmod_two_not_surjective` (ZMod 2 over ℤ), so `Module.Free` cannot be dropped. Finite projective would also work (`docs/gaps.md`).
- Red team (statement): pass with changes, all implemented; the sketch has the table.
- New open rung `clifford-exterior-half-spin` (parity iff statements, then `Cl⁰ ≅ End(∧^ev) × End(∧^odd)`), statements in `docs/sketches/clifford-exterior-chevalley.md`. Chevalley's S ⊗ S ≅ ∧*V is recorded there as a future rung.
- Next move: a red team on the checked module, then `clifford-exterior-half-spin`.
