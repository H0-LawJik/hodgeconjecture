# 2026-11-28 de-rham-pullback

- Rung `de-rham-pullback` (issue #257, T1 plan node A5): checked in `HodgeLadder/Hodge/DeRhamPullback.lean`; red team `docs/sketches/de-rham-pullback.redteam.md`, pass with changes, all six required and both optional changes applied.
- `deRhamPullback g n : H_dR^n(Y) →ₗ[ℂ] H_dR^n(X)` is `deRhamBaseChangeEquiv X n ∘ (pullbackCohLinear g n).baseChange ℂ ∘ (deRhamBaseChangeEquiv Y n).symm`, for smooth projective integral X, Y.
- Laws, exact, no sign: `deRhamPullback_fieldToDeRhamCohomology`, `deRhamPullback_unique` (a ℂ-linear map sending ι α to ι (g^* α) is `deRhamPullback g n`), `deRhamPullback_comp`, `deRhamPullback_id`, `deRhamPullback_injective_of_section`, `deRhamPullback_cupBilinear` (bilinear maps, `compr₂` against `compl₁₂`), `deRhamPullback_cup` (a + b = n in ℕ, `by lia` for the ℤ degree proofs), `deRhamPullback_conj`.
- Route: the ι law from `deRhamBaseChangeEquiv_tmul` at `1 ⊗ α`; every other law on ι-images, extended by `span_range_fieldToDeRhamCohomology_rat` and `LinearMap.ext_on` (semilinear for conjugation, through upstream's `deRhamConjSemilinear`).
- New rung `de-rham-pullback-test` (module `HodgeLadder.Tests.DeRhamPullbackP1p1`): `deRhamPullback prod.fst 2 (ι [∞]) ≠ 0` and injectivity of `deRhamPullback prod.fst n` in every degree on ℙ¹ × ℙ¹.
- Consumer note: with literal ℤ degrees, `rw` or `simp` with `deRhamPullback_cup` fails on `↑2` against `2`; use `exact`, or `LinearMap.congr_fun₂` of `deRhamPullback_cupBilinear` (the `hS` of `weil-eigen-algebra`).
- Kernel cost: about 27 s for the definition, 31 to 37 s for the ι law (a variant with `simp` took 61 s), 14 s for uniqueness, 2 to 10 s for each other law. A consumer-side `Module ℚ` shortcut instance gives no gain (`docs/gaps.md`, Known weaknesses).
- Rows added: `docs/conventions.md` "Pullback on de Rham cohomology", `docs/gaps.md` layer 25 row and the kernel-cost append.
- Next: `weil-surface-statement` and `weil-surface-reduction` can use `deRhamPullback f 1`, `deRhamPullback f 2` and `deRhamPullback_cupBilinear` directly; `de-rham-hypercohomology-pullback` closes through `deRhamPullback_unique`.
