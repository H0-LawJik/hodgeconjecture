# Handoff 2026-11-28: `weil-surface-reduction`

- Checked: `HodgeLadder/Weil/Surface/Reduction.lean` (module `HodgeLadder.Weil.Surface.Reduction`), imported from `HodgeLadder.lean`, standard axioms only. Plan node B, issue #279. This is a conditional theorem; T1 itself stays open.
- Statement: on a smooth projective integral `A` over `Spec ℂ` (no dimension hypothesis) with `IsWeilTypeSurface A f d`, `finrank ℂ H_dR^1(A) = 4` and `H_dR^2(A)` spanned by `deRhamCup x y` for `x, y ∈ H_dR^1(A)`, `weilSpace A f d ≤ Hdg^1(A; ℚ)` (`weilSpace_le_hodge_of_rank_span`), hence `≤ algebraicCycleClassSpan A 1` (`weilSpace_le_algebraic_of_rank_span`). `weilClassesAlgebraicSurface_of_rank_span`: rank and span on every abelian surface give `WeilClassesAlgebraicSurface`.
- Linear algebra on abstract ℂ-spaces in `ker_sub_smul_le_of_isBalanced`: conjugation forces both eigenspaces of `T` to rank 2 (`rank_le_of_injective_injectiveₛ` along `starRingEnd ℂ`); balance gives a class of `F¹` in each; products inside a rank-2 eigenspace then lie in `F¹H²`; `ker_sub_smul_le_span_of_eigen` with `ι = V₊ ⊕ V₋`. No f-stability of F¹ is used.
- New general lemma: `HodgeLadder.deRhamConj_deRhamConj` (conjugation is an involution), placed in `HodgeLadder.Hodge.DeRhamPullback` beside `deRhamPullback_conj` (red team O2; that module has 3 dependents).
- Signs: −d through `weilRoot_sq`, Koszul `(−1)^(1·1)` through `deRhamCup_self_of_odd`; no other sign or scalar.
- Checks in the file: the ℂ⁴, ∧²ℂ⁴ model (conclusion holds, eigenspace neither ⊥ nor ⊤, `G ≠ ⊤`; fails for signature (2, 0)), and the rank-(3, 1) model where the conclusion fails without the conjugation hypotheses (O1).
- Vacuous at the pin: no X has a checked `b₁ ≠ 0`. Planned instance E × E through `elliptic-square-cohomology` and `weil-elliptic-square`; the universal hypothesis of the T1 corollary waits on `weil-surface`.
- Kernel cost: about 20 s for the Hodge form, 12 s for the algebraic form, the rest small; the module builds in under a minute.
- Red team: `docs/sketches/weil-surface-reduction.redteam.md`, pass with changes; changes 1 to 7, O1, O2, O4 applied. O3 (scheme-level guard `¬ weilSpace (E × E) ([i] × [i]) 1 ≤ Hdg^1`, needs h^{2,0} ≠ 0) recorded in the ledger note, no rung.
- Rows: gaps (two), conventions ("Weil type", "de Rham cup order", new "Conjugation on H_dR"), roadmap, references (`Mumford1970` scope).
- Next: `weil-surface-rank` (companion rank identity), then the E × E inputs (`elliptic-square-cohomology`, `weil-elliptic-square`).
