# Handoff 2026-11-28: `lattice-fundamental-rectangle`

- Checked: `HodgeLadder/Period/FundamentalRectangle.lean`, imported from `HodgeLadder.lean`, Mathlib only (`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`, `Mathlib.Analysis.Real.Cardinality`) plus `HodgeLadder.Period.Pair.Normalize` for the test pairs. Sub-rung 5 of `docs/sketches/weierstrass-two-to-one.md`, statement as posted (`exists_fundamental_rect`).
- Unique shift for every corner `a` (`existsUnique_shift_mem_Ico`): `n` from `existsUnique_add_zsmul_mem_Ico` with period `Im ω₂`, then `m` with period `1` after the shear `n Re ω₂`; uniqueness compares lattice points directly, so ℝ-independence is not needed.
- Boundary clause (`exists_boundary_avoids`): the corners to avoid have `a.re ∈ {(s − l).re, (s − l).re − 1}` or `a.im ∈ {(s − l).im, (s − l).im − Im ω₂}` for `s ∈ S`, `l ∈ Λ`, a countable union (`lattice_countable`), and ℝ is uncountable (`Cardinal.not_countable_real`).
- Counting forms for `weierstrass-order-sum`: `shift_mem_Ico_iff`, `eq_of_sub_mem_lattice`, `mem_Ioo_of_boundary_avoids` (finding 4 (c), (d) of the `rect-periodic` red team).
- Tests: `(1, i)` and the sheared `(1, 1/2 + i)` with exact shifts; the vertical guess `−ω₂` misses at the sheared pair; `(1, −i)` and `(2, i)` show `h₂` and `h₁` are used; `S = Λ` gives an interior lattice point.
- No sign or normalization convention. Elaboration about 4.5 s wall for the file.
- Next: red team; then `weierstrass-order-sum` once `rect-argument-principle` lands.
