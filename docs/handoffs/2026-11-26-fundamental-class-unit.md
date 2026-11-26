# Handoff 2026-11-26: `fundamental-class-unit`

- Checked: `cycleComponentSheafClass_genericPoint_eq_one`, [X] = `one X` in H⁰(X; ℚ) for every smooth integral projective X over ℂ, exact, sign +, no scalar (`HodgeLadder/Tests/FundamentalClassUnit.lean`). Sign test `cycleComponentSheafClass_genericPoint_ne_neg_one` ([X] ≠ −1), red-team change C.
- Kill criterion of decisions 0009 and 0010: `fundamental-class-unit` holds, so front `cup` is not killed in codimension 0.
- Route: [X] = c • 1 on the line H⁰; Ψ(1) = `oneSing`; at a point y of X ∖ Z_sing, `cycle-class-germ` and `supported-pair-forget` make the restriction of Ψ[X] the forgotten degree-0 normal projection coclass, which is `oneSing W`; so c = 1.
- The sign is decided by `normalizedDual_apply_self`, `standardAmbientClassZero_projection` (the reference 0-simplex of ℝ⁰ with coefficient 1) and `SSet.ιChainComplex_constCochain`; `standardLocalClass_zero_epsilon` enters only for nonvanishing. Register row "Degree-zero orientation and the unit" (added by the red team).
- New rung `singular-unit` (foundation, checked, `HodgeLadder/Cup/SingularUnit.lean`, change B): `oneSing` is a natural two-sided unit of `cupSing`, nonzero on a nonempty space; Ψ(one X) = `oneSing` under `[T2Space]` and paracompact opens; `one X = fieldCohomologyUnit ℚ X`. Listed in `docs/gaps.md`, "General lemmas kept local".
- `cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤` was not needed: one point of the smooth ambient open suffices (`exists_mem_cycleComponentSmoothSupportAmbientOpen`). Docstring of `adaptedChart_genericPoint` updated (change D).
- Not done here: the Status block in `CLAUDE.md` (left to the coordinator, as for the other parallel tracks).
- Next: `cycle-class-multiplicative-codim-zero` ([X] ∪ [X] = [X] now follows from this rung and `one_cup`; the rung's own route through the transversal theorem still needs its hypotheses), then `local-class-cross-model`.
