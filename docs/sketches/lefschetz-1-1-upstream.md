# Verification record: upstream Lefschetz (1,1) proof

Rung `lefschetz-upstream-verify`. Independent reproduction of the upstream proof of rational Lefschetz (1,1), run on this project's build machine on 2026-11-24.

| Item | Value |
|---|---|
| Repository | `Paul-Lez/HodgeConjecture`, branch `codex/lefschetz-one-one-proper-gaga` (upstream PR #228, stacked on #217–#226, #9, #230) |
| Commit | `c7d5c94b44882a3b58e598a0bd22741e3b11eb8c` |
| Toolchain | Lean `v4.33.1`, Mathlib `v4.33.1` (prebuilt cache) |
| Theorem | `lefschetzOneOne` in `Other/AlgebraicGeometry/LefschetzOneOne.lean` |
| Build | `lake build Other.AlgebraicGeometry.LefschetzOneOne`: success, 5,519 jobs |
| Upstream axiom gate | `lake build CheckLefschetzOneOneAxioms`: success, 5,522 jobs |
| Direct axiom print | `'lefschetzOneOne' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| Positive control | a `sorry` placed in a non-exposed proof body of one module and used by a theorem in a second module is reported as `[sorryAx]` by the same `#print axioms` route; module boundaries do not hide it |

## What this establishes

The upstream theorem is kernel-checked at that commit with only the standard axioms, and the gate that guards it can detect a hidden `sorry`.

## What it does not establish

- That the theorem proves the statement of record at this repository's pin. The proof runs on an older cycle-class construction that agrees with the pinned one only up to a nonzero rational scalar (red-team record, `lefschetz-1-1-upstream.redteam.md`, item 1). The inclusion survives that scalar; the identities underneath it need `divisor-chern-exact`.
- The equality Hdg^1 = span (`lefschetz-1-1-equality`, decision 0004).
