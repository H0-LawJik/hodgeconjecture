# 0014. The checker scans the build log for placeholders

Date: 2026-11-27. Status: accepted. Amends the checker rules (`tools/check.py`, `CONTRIBUTING.md`, `AGENTS.md`).

## Context

The checker rejected the literal word `sorry` in source text and checked the axioms of every declaration the ledger names. The red team of `plane-cubic-subscheme` (`docs/sketches/plane-cubic-subscheme.redteam.md`, finding 5) found three ways past the text scan:

- `admit` and `stop` elaborate to `sorryAx` with a warning only, and contain no `sorry` text;
- a `local notation` used inside a `variable` binder elaborated to `sorry` with no message at the `variable` command; the declarations using it then failed to build.

The axiom step covers only declarations the ledger names, so a placeholder in an unnamed helper used by no ledger declaration would pass both steps.

## Decision

`tools/check.py` rejects any build whose log contains Lean's warning "declaration uses `sorry`", which every elaboration to `sorryAx` prints. In full mode it scans the output of `lake build`; with `--no-build` it scans the output of `lake build --no-build`, which replays the stored logs of up-to-date modules. The text scan for `sorry` stays.

## Consequences

- `admit`, `stop` and any other route to `sorryAx` in any built module fail the check, named or not.
- The notation case already fails the build; the record of it is the Known-weaknesses row in `docs/gaps.md`.
- The scan reads replayed logs, so it costs about 8 s in `--no-build` mode.
