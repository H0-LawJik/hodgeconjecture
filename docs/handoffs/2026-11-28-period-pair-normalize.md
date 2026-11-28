# Handoff 2026-11-28: `period-pair-normalize`

- Checked: `HodgeLadder/Period/Pair/Normalize.lean`, imported from `HodgeLadder.lean`, Mathlib only (`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`). Sub-rung 6 of `docs/sketches/weierstrass-two-to-one.md`, statement as posted (`exists_normalized`).
- Witnesses: `normalize L = smul μ (oriented L)` and `μ = normalizeScale L = (oriented L).ω₁⁻¹`.
- Orientation choice: `oriented L` keeps `(ω₁, ω₂)` when `Im(ω₂/ω₁) > 0` and swaps to `(ω₂, ω₁)` when `Im(ω₂/ω₁) < 0` (`im_div_ne_zero` excludes 0). So `τ = ω₂/ω₁, μ = ω₁⁻¹` or `τ = ω₁/ω₂, μ = ω₂⁻¹` (`normalize_of_pos`, `normalize_of_neg`).
- Homogeneity for every `μ ≠ 0`: `weierstrassP_smul` (`℘_{μΛ}(μz) = μ⁻² ℘_Λ(z)`), by reindexing the `tsum` along `smulLatticeEquiv` (`l ↦ μl`) and `tsum_mul_left`; same proof gives `derivWeierstrassP_smul` (μ⁻³), `G_smul` (μ⁻ⁿ), `g₂_smul` (μ⁻⁴), `g₃_smul` (μ⁻⁶). `weierstrassP_congr`: ℘ depends only on the lattice.
- Tests: `(1, i)` kept, scale 1, τ = i; `(1, −i)` swapped, scale i, τ = i; `℘_{ℤ[i]}(iz) = −℘_{ℤ[i]}(z)` through `i ℤ[i] = ℤ[i]`.
- No sign beyond the orientation `Im τ > 0`; exponents exact. Elaboration about 5 s wall for the file.
- Red team: pass with changes (docs/sketches/period-pair-normalize.redteam.md): exponent and transport-direction tests at μ = 2, ℘′(iz) = i℘′(z), the bases (c, ±ic) normalized; conventions and gaps rows.
- Next: C3 can fix `c` with `g₂(cℤ[i]) = 4` from `g₂_smul`; `weierstrass-order-sum` takes `normalize L` as input.
