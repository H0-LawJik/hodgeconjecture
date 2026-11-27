# Handoff 2026-11-27: `wedge-sheaf-map`

- Checked: `HodgeLadder/Hodge/WedgeSheafMap.lean`, imported from `HodgeLadder.lean`, 44 declarations in the ledger (three of them local instances), standard axioms only.
- Statement: `deRhamWedge X : (tensorRightComplex Y Ω•_ℚ).obj Ω•_ℚ ⟶ Ω•_ℚ`, the `m` of `pairProductShQ`, built by the generic `extendMul` from `wedgeSheaf`; on `Ω^p ⊗ Ω^q` it is `wedgeSheaf p q` (`ιTensorObj_deRhamWedge_f`), and `eq_extendMul_of_components` makes the components determine it.
- Sign: the chain-map obligation `ExtendMulLeibniz` carries Mathlib's Koszul sign `ε₂(p, q) = (−1)^p` only, read off `TensorSigns (up ℤ)` inside the kernel-checked proof; it is the checked Leibniz rule of `holomorphicWedge` verbatim. Factor order `a ∧ b`, no twist.
- Unit law: `deRhamWedge_unit` against Mathlib's left unitor (spelled `tensorHomShQ`, `shQLeftUnitor`, `deRhamUnitShQ`, all `rfl` to the requested form); `deRhamWedge_unit_unit` is the `hm` of `pairProductShQ_naturality` at `m = unitComplexMul`, plugged in at 5 s in scratch.
- Filtration: `deRhamWedgeFiltered X p q` with `deRhamWedgeFiltered_comp_inclusion`, unique by `eq_truncMul_iff`; global bound instances on `F^p Ω•_ℚ` so `pairProductShQ` takes `B = F^q`.
- Tests: `deRhamWedge_ne_zero` and the sign separation `deRhamWedge_unit_neg` on every X with a complex point.
- Cost: module build about 5 min, mostly five sheaf-level declarations; two spellings that did not finish (searched `HasTensor`, `haveI` instances at the concrete space) are recorded in `docs/gaps.md`.
- Red team: `docs/sketches/wedge-sheaf-map.redteam.md`, pass with changes, all implemented; finding 8 became the open rung `de-rham-scalar-sheaf`.
- Next: `de-rham-cup` (its exact identity needs only `deRhamWedge_unit_unit` and naturality), `de-rham-scalar-sheaf` for ℂ-bilinearity.
