# Handoff 2026-11-26: `relative-cross-chain`

- Checked: rung `relative-cross-chain`, module `HodgeLadder.Relative.CrossChain` (`HodgeLadder/Relative/CrossChain.lean`), imported from `HodgeLadder.lean`. The statements are unchanged from the red-teamed text (`docs/sketches/relative-cross-chain.redteam.md`, pass with changes). Standard axioms only; `python3 tools/check.py` exits 0.
- Content: the relative cross product H_m(P, A) × H_n(Q, B) → `TriadRelativeHomology` of (P × Q; A × Q, P × B) → H_{m+n}(P × Q, A × Q ∪ P × B) exists, is unique and equals [shuffle(x ⊗ y)] on cycles. It is exact with no sign and natural in both pairs; the identity shuffle has coefficient +1; two vertices give the vertex of the product (`shuffleBilin_vertex`, the red team's proof).
- Route: Leibniz rule on chains in three cases (`shB_d_*`, from Tau Ceti's `ιTensorObj_d_of_rel` family). The shuffle product descends through both cokernel projections (`relMu`, `descendBilin`). `relMu_cycle`, `relMu_boundary_left` and `relMu_boundary_right` show it sends cycles to cycles and boundaries to boundaries. The general `homologyBilin` (any complex shape) gives the bilinear map. Uniqueness comes from surjectivity of `homologyπ` and of the projections.
- Red-team changes made:
  - ledger module name corrected;
  - sign-visible test added to the `cross-orientation` note;
  - new open rung `relative-cross-triad-naturality` (statements in its note), with `local-class-cross-model` now depending on it;
  - `shuffleBilin_vertex` added;
  - register citations in the docstrings, and the excision remark in the module docstring made precise;
  - `docs/gaps.md` row added, `docs/port-tauceti.md` note on the `import all`, drift list extended in the sketch;
  - register rows "Shuffle map" and "Relative homology cross product" set to checked.
- Timing: `lake env lean` on the file takes 9 to 14 s with default heartbeats. A full `python3 tools/check.py` on a warm build takes 20 s.
- Failed attempts:
  - `rw` fails whenever a term is typed by `(TopPair.ofSubset A).fst` and the lemma expects `P`. They are defeq, but not at the implicit transparency `rw` uses. Fixes: give lifts an explicit type (`obtain ⟨x, hx⟩ : ∃ x : C_m(P), …`), use `erw`, or use `exact` with `.trans`.
  - `erw` timed out (200000 heartbeats) when the boundary lemmas ran on untyped lifts.
  - `HomologicalComplex` biprod lemmas need `erw` (instance mismatch).
- Not done: the `CLAUDE.md` status block (left to the maintainer, since parallel worktrees edit it).
- Next move: `cross-orientation`, whose real-form test is in its ledger note. After that, `cap-cross-evaluation` and `relative-cross-triad-naturality`.
