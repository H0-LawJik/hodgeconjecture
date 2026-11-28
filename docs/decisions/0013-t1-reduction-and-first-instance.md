# 0013. T1 as a reduction with a first instance on E × E

Date: 2026-11-27. Status: accepted. Changes the first rung of front `abelian` (`docs/strategy.md`, fronts table). Plan: `docs/notes/2026-11-27-t1-plan.md`.

## Context

The Markman inventory (`docs/notes/2026-11-25-markman-inventory.md` §6) names T1, Weil classes on abelian surfaces of Weil type are algebraic, as the first Markman-directed rung after front `cup`, and lists its needs as the cup product and pullback along endomorphisms on H¹. Front `cup` is closed as won (decision 0012). A survey of the pin for this plan found:

- no abelian surface, no elliptic curve and no smooth projective X with b₁ ≠ 0 (the projective witnesses are the point, ℙ¹, ℙⁿ, ℙ¹ × ℙ¹); Mathlib's `WeierstrassCurve` has no scheme over `Spec ℂ`, and Mathlib's ℘ has no uniformization;
- the inclusion W_K ≤ Hdg^1 also needs H²(A) spanned by cup products of H¹ classes with b₁ = 4, and, to check the Weil-type condition on a concrete A, the Hodge filtration preserved by pullback; neither has a rung;
- with the Weil space defined as the −d-eigenspace of f^* on H²(A; ℚ) and balance stated through F¹H¹_dR, the linear-algebra step is a conditional theorem whose extra hypotheses (rank of H¹_dR, span of H²_dR by products) are statements on upstream definitions, and every input of it is checked or small.

## Decision

1. T1 is posted as a chain of 32 open rungs (plan §4). Its first checked form is the reduction `weil-surface-reduction`: on a smooth projective integral surface with an endomorphism of Weil type, rank 4 and the span hypothesis give `weilSpace ≤ Hdg^1`, hence `≤ algebraicCycleClassSpan 1`.
2. The first instance is `weil-elliptic-square`: A = E × E with E : y²z = x³ − xz² (CM by ℤ[i]) and f = [i] × [i]⁻¹, d = 1. E is built as a closed subscheme of upstream's ℙ². The elliptic-curve sub-rungs proposed in `docs/sketches/cup-odd-degree-test.md` §5 join this chain with their ids and serve both `cup-odd-degree-test` and T1.
3. T1 in general (`weil-surface`, on upstream's `[GrpObj A]` abelian surfaces) is parked behind the instance through `abelian-surface-uniformization`, which depends on `weil-elliptic-square`.
4. The first rung of front `abelian` becomes the pair `pullback-functorial`, `weil-eigen-algebra` (both small and ready), on the way to `weil-surface-reduction`. `markman-statement` stays open as the front's target.

## Consequences

- `python3 tools/next.py` offers `pullback-functorial` first: the T1 block sits ahead of the older open rungs in the ledger.
- `cup-odd-degree-test` depends on `elliptic-curve-torus-data`; its kill criterion and the kill criterion of `weierstrass-two-to-one` are the same event.
- Kill criteria for the large rungs are in the plan §7. If the Hodge inputs of the instance die, the fallback is a divisor route on E × E (plan §3), which has no rung.
- A conventions row "Weil space" (pullback direction, the sign −d, the root i√d) is owed by the red team before `weil-surface-statement` is posted.
