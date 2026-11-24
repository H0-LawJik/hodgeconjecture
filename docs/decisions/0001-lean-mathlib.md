# 0001: Lean 4 and Mathlib as the only proof language

**Date:** 2026-11-23. **Status:** adopted.

## Context

The project needs one notion of "result" that people and coding agents agree on without discussion. Candidates were Lean 4 with Mathlib, Coq with its algebra libraries, and Isabelle.

## Decision

Lean 4, pinned to a Mathlib release tag. Python is allowed only for tooling around the proofs (the checker, ledger validation, future orchestration scripts), never as a proof source.

## Consequences

- Mathlib's algebraic geometry (schemes, algebraic cycles, orders of vanishing) and manifold library are the starting floor; what it lacks (differential forms, de Rham cohomology, Kähler geometry, singular cohomology) becomes rungs of this project.
- Anything general enough goes upstream to Mathlib under Apache 2.0, which is why this repository uses the same license.
- Toolchain bumps are a deliberate, single commit touching `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.
