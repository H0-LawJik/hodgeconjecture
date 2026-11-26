# Handoff 2026-11-26: `cup-comparison-supported-open`

- Goal: the supported cup comparison on a general open `V` of `X(ℂ)`, `W = V ⊓ (X ∖ Z)`, for `local-class-product` (upstream's normalized local classes live on small opens).
- Checked: `singular-restrict-open` (`cohomologyMap_inclusion_singClass`), `supported-open-rep` (`exists_supported_rep_open`), `supported-open-sections-class` (`supCup_flasque_open`), `cup-comparison-supported-open` (`cup_singular_comparison_open`), `cup-comparison-open-test` (ℙ¹ instantiation).
- Statement: `Φ_V (supCupY α β) = (−1)^{pq} • relCupSing (Φ_V α) (cohomologyMap ℚ q (Opens.inclusion' V) (Ψ β))`, `α` in upstream's `relH ℚ_X p (V ⊓ Z.compl ≤ V)`.
- The product is `supCupY` with source the pair sheaf `ℤ[V, W]`; no new definition.
- Two timeouts and their fixes: give `Opens.inclusion'` its space explicitly (`X := TopCat.of (ComplexPoint X)`); state the restriction lemma with the `pairVU` spelling for a general space (`cohomologyMap_inclusion_singClass_pair`) and apply it with `Y` explicit.
- Elaboration: `SupportedOpen.lean` about 100 s, `SupportedOpenClass.lean` about 75 s, `SupportedOpenFinal.lean` about 120 s.
- Open: at `V = ⊤` the new statement and `cup_singular_comparison_supported` use different spellings of `W` (`⊤ ⊓ Z.compl` against `Z.compl`) and are not identified in Lean. A nonzero class of `(V, W)` with `V ≠ ⊤` is not exhibited, so the ℙ¹ test covers the hypotheses only. A product of two supported classes is not provided.
- Next move: `local-class-product`, using `cup_singular_comparison_open` on the opens where upstream's normalized local classes live.
