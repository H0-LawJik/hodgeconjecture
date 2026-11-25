# 0006. The checker imports all of Mathlib with both libraries

Date: 2026-11-24. Status: accepted.

## Context

The red-team pass on the port (`docs/sketches/lefschetz-port.redteam.md`, finding M1) found that the port declared `CategoryTheory.Sheaf.H.δ`, a name Mathlib also declares at the pin. Nothing in the build imported both, so the clash was invisible until a later import or pin bump reached the Mathlib module. Global instances on Mathlib types (finding L7) carry the same risk.

## Decision

`tools/check.py` elaborates a file that imports `Mathlib`, `HodgeLadder` and `LefschetzPort` together and rejects if it fails. The port's copy of `Sheaf.H.δ` is removed in favour of Mathlib's.

## Consequences

A clashing declaration name fails the checker on the change that introduces it. The step loads all of Mathlib, which costs time and memory in CI.
