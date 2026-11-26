# Handoff 2026-11-26: `triad-relative-cup`

- Checked: `relCup2 : H^p(X, A) × H^q(X, B) → H^{p+q}(X, A ∪ B)` for A, B open in X (`HodgeLadder/Cup/TriadCup.lean`). It is Tau Ceti's cup along `triadDiagonal` on upstream's triad complex C(X)/(C(A) + C(B)), with the A factor first, front face times back face and no sign, carried to H(X, A ∪ B) by the inverse of `triadExcisionCoh`, which is the dual of upstream's triad excision comparison.
- Theorems:
  - `forgetRel_relCup2`: the product forgets to `cupSing`.
  - `relCup2_empty`: for B = ∅ it is `relCupSing a (forgetRel b)` on (X, A ∪ ∅) = (X, A).
  - `forgetRel_empty_bijective`.
  - The cocycle formula, required by red-team finding 3 because the two compatibilities do not determine `relCup2`: `triadCupCycles`, `triadExcisionCoh_relCup2_homologyπ`, `triadProj_cupCochain`.
- Test `torusEval_relCup2_winding` (`HodgeLadder/Tests/TriadCupTorus.lean`): the torus evaluation is 1 at A = B = ∅.
- The proofs follow the red-team appendix (`docs/sketches/triad-relative-cup.redteam.md`). C(∅) = 0 comes from upstream's `relativeChainProjection_empty_isIso`; there is no local copy.
- Statement-phase choice: the hypotheses require A and B to be open in X. Upstream's excision only needs them open in A ∪ B (`_of_openCover`), and that generalization is not done.
- Register row "Triad relative cup product" added by the red team; `homologyMap_linearDualMap_bijective` is listed in `docs/gaps.md`.
- Next: `triad-relative-cup-naturality` (maps of triads via `TopPair.ofSubsetHom`) and `triad-relative-cup-cap` (start from `triadProj_cupCochain` and the `rfl` pins of the `Other` cap).
