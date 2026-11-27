# Handoff 2026-11-26: `clifford-exterior-half-spin`

- Checked in `HodgeLadder/Markman/HalfSpin.lean` (40 declarations, standard axioms). For `M` finite free over a commutative ring, `x ∈ evenOdd (dualProd R M) i` holds exactly when `spinAction x` maps parity `j` of ∧M into parity `j + i` for every `j` (`spinAction_mem_evenOdd_iff`, with the posted `_zero_iff` and `_one_iff`).
- The general form is `spinAction_mem_evenOdd_iff_of_injective`: it needs only a faithful action. `injective_spinAction_iff` shows that the criterion for all `i` is equivalent to faithfulness.
- Equality forms: `map_evenOdd_dualProd_eq_parityShift` (GLO 4.3.6, "sends Cl^+ onto H^ev") and `evenOdd_dualProd_eq_comap_parityShift`.
- Half-spin isomorphism: `spinEquivEven : even (dualProd R M) ≃ₐ[R] End(∧^ev) × End(∧^odd)`, built as `AlgEquiv.ofBijective` of the restriction map `spinActionEven`. Its value lemmas are `rfl`, the S⁺ component comes first and there is no sign. `spinActionParity_surjective` holds for each component.
- Proof route: split `x` into the parity-`i` part and the opposite part. The opposite part sends each parity of ∧M into two complementary parts, so it acts by `0` (`ext_exteriorParity`) and vanishes by injectivity. Surjectivity goes through `Submodule.projectionOnto`; `linearProjOfIsCompl` is deprecated at the pin.
- Tests from the red team, compiled as written and wrapped to 100 columns:
  - For the ideal `(2)` of `ZMod 4`, a nonzero even element acts by `0`. `evenOdd_one_iff_zmod_four_fails`, `spinActionEven_zmod_four_not_injective` and `not_free_zmodFourIdeal` follow from this.
  - `ι_vec_not_mem_evenOdd_zero_int`.
  - `spinActionEven_int_zmod_two_not_surjective` (from phase 1).
- Docs:
  - Sketch: phase 1 and phase 2 sections in `docs/sketches/clifford-exterior-chevalley.md`, a corrected hypothesis table, and a future rung for GLO 3.5.1 irreducibility (sketch only).
  - `docs/gaps.md`: a "To upstream" row and a weakness row next to the Chevalley finite-projective row.
  - `docs/conventions.md`: the red team's register row "Half-spin labels, parity shift and component order" is kept.
- Deferred: `spinUnitsEquivEven`, to the rung that defines Spin(V), which needs its own conventions row against Mathlib's `spinGroup`.
- Open question, which no statement depends on: whether `Module.Finite` is needed for the criterion over a general ring for free `M` of infinite rank.
- Next on this track: the GLO 3.5.1 irreducibility rung or the Spin(V) rung, when the Markman inventory reaches them.
