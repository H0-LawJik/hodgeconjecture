# Handoff 2026-11-28: `weierstrass-surjective`

- Checked: `HodgeLadder/General/WeierstrassSurjective.lean` (rung `weierstrass-surjective`, issue #284, sub-rung 1 of `weierstrass-two-to-one`), imported from `HodgeLadder.lean`; one declaration, `HodgeLadder.weierstrassP_surjOn (L : PeriodPair) (c : ℂ) : ∃ z ∉ L.lattice, L.weierstrassP z = c`, the statement as posted; standard axioms only; Mathlib only.
- Route: the sketch's step 1. Assume ℘ z ≠ c off Λ; g = (℘ − c)⁻¹ off Λ, 0 on Λ. At l ∈ Λ, g agrees with (℘ − c)⁻¹ on a punctured neighbourhood (`compl_lattice_sdiff_singleton_mem_nhds`); the order of ℘ − c is −2 (`order_weierstrassP`, `meromorphicOrderAt_add_eq_left_of_lt` against the constant), so g has order 2 (`fun_meromorphicOrderAt_inv`) and is analytic (`AnalyticAt.of_meromorphicOrderAt_pos`). Off Λ, `analyticOnNhd_weierstrassP`. Periodic, bounded (`IsZLattice.isCompact_range_of_periodic`), constant (`Differentiable.apply_eq_apply_of_bounded`), so g (ω₁/2) = g 0 = 0, a contradiction.
- Signs: none. The hypothesis z ∉ Λ carries weight (junk value ℘ = 0 on Λ); noted in the module docstring.
- Failed attempts: `meromorphicOrderAt_fun_inv` does not exist; the `to_fun` variant is `fun_meromorphicOrderAt_inv`. `push_neg` is deprecated at the pin (`push Not`).
- Timing: the file elaborates in about 4 s (2.6 s in `lake build`).
- Docs: `docs/gaps.md` row (Complex analysis and elliptic functions), `docs/roadmap.md` row, ledger entry.
- Red team: `docs/sketches/weierstrass-surjective.redteam.md`, pass with changes; changes 1 to 4 applied (module moved to `General/WeierstrassSurjective`, gaps row, moved after the red team into the category "Complex analysis and elliptic functions" that #294 added, whose bump line now also names `Analysis/Meromorphic/Order.lean` and `Algebra/Module/ZLattice/Basic.lean`, conventions row "Weierstrass ℘ of a period pair", ledger note).
- Next: the remaining sub-rungs of `weierstrass-two-to-one` (`rect-winding` heads the critical path).
