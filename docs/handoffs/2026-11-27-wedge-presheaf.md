# Handoff 2026-11-27: `wedge-presheaf`

- Checked: `HodgeLadder/Hodge/WedgePresheaf.lean`, imported from `HodgeLadder.lean`. `holomorphicWedge X d U p q : HolomorphicForm X d U p →ₗ[ℂ] HolomorphicForm X d U q →ₗ[ℂ] HolomorphicForm X d U (p + q)` is Mathlib's `LinearMap.liftQ₂` of `mkQ ∘ formWedge`, well defined by both sides of `wedgeDescends`.
- Exact identities: naturality under `holomorphicFormRestriction`, pointwise and as an equation of bilinear maps; the Leibniz rule `d(a ∧ b) = cast(da ∧ b) + (−1)^p a ∧ db`; unit laws for the constant zero-forms on both sides.
- Degrees: only `da ∧ b` needs a transport, `holomorphicFormCast` along `Nat.add_right_comm p 1 q`, which is `h ▸ LinearMap.id` and keeps the element of the exterior algebra. The five cast lemmas a consumer needs (trans, restriction, differential, `eqToHom`, `XIsoOfEq`) are `subst h; rfl`.
- Nonvacuity: `holomorphicWedge_ofConstant_one_ne_zero` (`[1] ∧ [1] ≠ 0` on a nonempty open, through upstream's `chartEvaluation_ofConstant`); `holomorphicWedge_ofFunction` (degree zero is multiplication of functions).
- Scalars: ℂ-bilinear only. Upstream's kernel is a ℂ-submodule, so `HolomorphicForm` has no 𝒪(U)- or ℚ-module structure. `rational-de-rham-complex` must supply `Module ℚ`, which is unique; its ledger note says so.
- Failed: rewriting a second time inside the Leibniz goal, `obtain ⟨_, rfl⟩` on the second argument, and `change` all ran past 200000 heartbeats in `whnf`. What works is `Submodule.Quotient.induction_on` on both arguments, then `exact` a lemma on representatives with both transports explicit.
- Known weakness, in `docs/gaps.md`: no test pins the Leibniz sign directly. That needs a nonzero 1-form such as `dz` on ℙ¹.
- Red team: `docs/sketches/wedge-presheaf.redteam.md`, pass with changes, all implemented. The conventions row is "Wedge product of holomorphic forms".
- Next: `wedge-sheafify` (needs `rational-de-rham-complex` for the ℚ-module structure).
