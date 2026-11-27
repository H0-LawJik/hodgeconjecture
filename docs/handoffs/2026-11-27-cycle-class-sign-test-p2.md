# Handoff 2026-11-27: `cycle-class-sign-test-p2`

- Checked: `HodgeLadder.Tests.CycleClassSignTestP2`, 24 declarations, standard axioms, imported from `HodgeLadder.lean`. `planeDegree : H⁴(ℙ²; ℚ) →+ ℚ` lifts a class to H⁴_{pt}, carries it by upstream's transport to H⁴(ℙ²(ℂ), ℙ²(ℂ) ∖ pt; ℚ) and evaluates it on upstream's complex local orientation.
- Results: deg [pt] = 1 (`planeDegree_planeOrigin`), H⁴(ℙ²; ℚ) ≅ ℚ (`planeDegree_bijective`), deg ([L₀] ∪ [L₁]) = 1 through the checked identity, and agreement with ⟨Ψ −, μ⟩ for any μ restricting to the local orientation (`planeDegree_eq_eval_of_restrict`, conditional).
- New mathematics on the way: H^{q+3}(ℙ²(ℂ) ∖ pt; ℚ) = 0 for every q (the covers of `p2-point-class-nonzero` in all degrees), so `forgetSupport` is bijective in degree 4.
- What it does not show (red team, findings 1 and 2): the value 1 is upstream's point normalization read as a number; the ladder's steps carry no sign. The product is read through `planeLines_cup_eq_planeOrigin`, so the multiplicativity sign at a = b = 1 has no independent recomputation. With ε = +1 the two line-class scalars multiply to 1.
- Red team changes A to E and G implemented. A: the independence guard now judges imported constants by import closure, since imported theorem bodies are not visible under the module system. F (unconditional singular reading) skipped to keep kernel time down.
- Weakness: about 4.5 minutes to elaborate, 195 s of kernel type checking; a leaf module, recorded in `docs/gaps.md`.
- Next: `p2-fundamental-class` (new, open) discharges `hμ` from H₃(ℙ²(ℂ) ∖ pt; ℚ) = 0. A second computation of [L₀] ∪ [L₁] is still the missing sign test at a = b = 1.
