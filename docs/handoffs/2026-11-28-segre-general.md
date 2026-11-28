# Handoff 2026-11-28: `segre-general`

- Checked: `HodgeLadder/Segre/General.lean`, imported from `HodgeLadder.lean`, 30 declarations in the ledger, standard axioms only.
- General Segre: `segre R m n : ℙₒ(m; R) ×_R ℙₒ(n; R) ⟶ ℙₒ(mn + m + n; R)` over every commutative ring, glued with `HodgeLadder.Segre.glue` from the (m + 1)(n + 1) chart products, x_{(k, l)} = a_k b_l at index l + (n + 1)k (`pairEquiv`, `finProdFinEquiv`). The m = n = 1 proofs carried over with `1` replaced by `m`, `n`; nothing in them used the dimension.
- `segre_toSpec`, `segre_preimage`, `isClosedImmersion_segre`; `segre_one_one : segre R 1 1 = HodgeLadder.Segre.segre R` holds by `rfl`, so the ℙ¹ × ℙ¹ files stay untouched.
- Products: `prodImmersion` = `Over.prodLeftIsoPullback` then `pullback.map` of the two presentations through `(okaIsoSpace _).inv`, a closed immersion by `MorphismProperty.pullbackMap`; `prodPresentation` follows it by the Segre map and `okaIsoSpace`. Instance `isProjective_prod : IsProjective (X ⨯ Y).hom`.
- Gotcha: `inferInstance` fails on `MorphismProperty.IsStableUnderComposition @IsClosedImmersion` although `IsMultiplicative` resolves: unification with the parent projection fails under the default `backward.isDefEq.respectTransparency.types` (with the option false it succeeds, and Mathlib's `IsClosedImmersion.comp` sets it for the same reason; `@IsOpenImmersion` is unaffected). `IsMultiplicative.toIsStableUnderComposition` by hand works.
- Instance search: `IsProjective p1p1.hom`, a nested product `(ℙ¹ × ℙ²) × ℙ¹`, `X ⨯ (Y ⨯ X)`, `IsProper (X ⨯ Y).hom`, and the failing goals (no hypotheses, one hypothesis, bare `X`) each resolve or fail in under 3 ms; `Smooth` searches unchanged.
- Tests: `isProjective_p1p2`, ℙ¹ × ℙ² over ℂ is projective; `not_isProjective_affineLine`, the affine line is not (red team change 1).
- Red team: `docs/sketches/segre-general.redteam.md`, pass with changes, changes 1 to 5 and O3, O4 applied.
- Signs: none. Conventions row "Segre embedding of ℙᵐ × ℙⁿ".
- Timing: the file elaborates in about 10 s.
- Next: `elliptic-square-witness` (projectivity of E × E is now `inferInstance` given `IsProjective ellipticCurve.hom`).
