# Handoff 2026-11-26: `clifford-exterior-spin`

- Checked in `HodgeLadder/Markman/CliffordSpin.lean`, for any module M over a commutative ring R: `spinAction : CliffordAlgebra (QuadraticForm.dualProd R M) →ₐ[R] Module.End R (ExteriorAlgebra R M)`, with ι (f, x) acting as `contractLeft f` plus left multiplication by `ι x`.
- `spinGen_mul_self`: the generator squares to `algebraMap R _ (f x)`, sign +, no factor 2. Built with `CliffordAlgebra.lift`.
- Parity: `spinAction_mem_exteriorParity` (an element of `evenOdd (dualProd R M) i` maps the span of the `⋀[R]^k M` with k ≡ j into parity i + j), through `contractLeft_mem_range_ι_pow` (contraction maps the (n + 1)-st power of the range of ι into the n-th, for any Q) and `contractLeft_mem_evenOdd`.
- Library search: Mathlib at the pin has `contractLeft` and `evenOdd`; it has no Clifford action of the split form on the exterior algebra under another name.
- The whole file elaborates in about 10 seconds.
- Open: `clifford-exterior-chevalley` (bijectivity for M finite free), posted to the ledger with a route. The blocker is a spanning set of 2^{2n} ordered monomials for a Clifford algebra, which Mathlib lacks; the exterior algebra basis exists (`Module.Basis.ExteriorAlgebra`).
- Red team: check the sign of the square against Chevalley1954 and record it in `docs/conventions.md`.
