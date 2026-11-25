# 0005. The `sorry` scan covers the port

Date: 2026-11-24. Status: accepted.

## Context

`tools/check.py` scanned `HodgeLadder/` for `sorry`. Since part 9 the staging library `port/LefschetzPort` is a default target, and checked rungs (`divisor-chern-exact`, `lefschetz-port`, `lefschetz-1-1`) name declarations in it or depend on it. The red-team pass on the port (`docs/sketches/lefschetz-port.redteam.md`, finding L4) noted that a `sorry` in a port module that no named declaration uses passes the checker.

## Decision

The `sorry` scan covers `port/` as well as `HodgeLadder/`. The axiom audit is unchanged: it already catches `sorryAx` in every declaration the ledger names.

## Consequences

A port module with a `sorry` fails the checker even when no rung depends on it. There were 0 such occurrences when this was adopted.
