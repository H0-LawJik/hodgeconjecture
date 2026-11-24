# Harness: how we tell Claude what to do

`docs/strategy.md` says what to attack. This file says how a session is run, which agent does what, where the prompts live, and the gates that keep an agent from fooling itself or us.

## Principle

Claude proposes; Lean disposes. No agent in this harness can mark anything checked. The checker (`tools/check.py`) and a merged pull request are the only path from "claim" to "result", and the ledger is the only record. Every role below is a way of producing better claims faster, and nothing more.

## Roles

| Role | Definition | Does | Out of bounds |
|---|---|---|---|
| Orchestrator | `.claude/agents/hodge-orchestrator.md` | Reads ledger and roadmap, splits big rungs into small ones, posts issues, keeps `docs/roadmap.md` and the status block current | Writes proofs; edits a statement a prover has taken |
| Thinker | `.claude/agents/hodge-thinker.md` | Writes a paper sketch for one rung into `docs/sketches/<id>.md` with citations from `docs/references.md`; proposes the Lean statement and the sub-lemmas | Claims a sketch is a proof; posts a statement without a red-team pass |
| Red team (falsification) | `.claude/agents/hodge-red-team.md` | Attacks a proposed statement before it is posted and a checked rung after: is it the literature's statement, is it vacuous, is it provable for the wrong reason, which sign and normalization conventions it depends on, whether upstream definitions drifted between pins | Softens a statement to make it pass |
| Prover | `.claude/agents/hodge-prover.md` | Takes one posted rung, writes one Lean file, runs the checker, opens the pull request | Changes the statement; touches a second rung; adds axioms |
| Librarian | `.claude/agents/hodge-librarian.md` | Finds what Mathlib already has for a rung, names the exact declarations, flags what should go upstream | Writes proofs |

One person reviews statements. Review reads the statement and the sketch, not the proof.

## Where the instructions live

| Audience | File | Harness |
|---|---|---|
| Any agent, any harness | `AGENTS.md` | neutral |
| Claude Code, this repo | `CLAUDE.md` | Claude |
| Claude Code subagents | `.claude/agents/*.md` | Claude |
| Claude Code entry points | `.claude/skills/{prove-rung,post-rungs,red-team}/SKILL.md` | Claude |
| Machine brief for a rung | `python3 tools/next.py [id]` | neutral |

The neutral files are the contract. The Claude files are a convenience layer that points at them; if the two disagree, the neutral file wins and the Claude file is fixed.

## A session

1. Start: read `CLAUDE.md` status, `git log -5`, `ledger/ladder.json`, the newest `docs/handoffs/*.md`. Run `python3 tools/next.py` to see what is ready.
2. Pick one mode for the session: orchestrate, think, red-team, prove, or librarian. Mixed sessions produce mixed records.
3. Work the rung. The 20-minute rule applies to a prover: stay with a hard step for at least 20 minutes of real attempts before releasing it with the sub-lemma it needs.
4. Close: `python3 tools/check.py`, update the ledger if a state changed, write `docs/handoffs/YYYY-MM-DD-<id>.md` (what moved, what failed, what the next session should try first), commit.

A handoff is five to fifteen lines. It names the rung, the approach tried, the exact error or gap, and the next move. It does not restate the plan.

## Rung lifecycle

```
proposed (issue, no ledger entry)
  → red team pass → open (ledger + issue labeled rung)
  → prover takes it (comment) → pull request → checker green → merged → checked
                                           ↘ released with missing_lemma → orchestrator splits → new open rungs
  → refuted (checked counterexample) / dead (written reason)
```

Size rule: one rung is one Lean file under about 200 lines and one session for a prover. If a sketch needs more, it is a milestone, and the orchestrator splits it before a prover starts.

## Statements of record

Statements of record live upstream, in `Paul-Lez/HodgeConjecture`, pinned in `lakefile.toml` (decision 0003). Rules:

- A rung's statement is read against upstream definitions and Mathlib only. A pull request may not add notation, instances or attributes that change how an upstream statement elaborates; the red team checks this.
- Nothing in this repository restates the conjecture or a variant upstream already states. A proof of an upstream variant is a theorem whose type is that upstream `Prop`.
- No interface structures stand in for missing objects. Interface statements of this conjecture have been shown vacuous or false elsewhere (LeanDojo regression tests). Assumed inputs, where a conditional theorem needs them, are hypotheses that are themselves statements on real definitions, each cited, each listed with its convention in `docs/conventions.md`.
- Upstream pin bumps follow upstream's toolchain and are reviewed by the red team for definition drift.

## External checks

A rung may be `checked` by a reproduced build of another repository at another pin, when this repository cannot import that pin. The rung then carries an `external` record (repository, commit, toolchain, declarations, axioms, and a record file under `docs/sketches/` with the build output and a positive control for the axiom gate). The checker validates the record's shape and that its axioms are the standard three; it does not rebuild. The site shows such a rung as checked at the named commit. A rung whose statement is about this repository's pin needs a check here; an external record does not discharge it.

## Ledger kinds

Each rung has a `kind`: `foundation`, `statement`, `case`, `reduction`, `front`, `test`, or `interface` (retired; kept for dead rungs). The checker validates the field. The site shows it.

## Gates

| Gate | Enforced by |
|---|---|
| No `sorry`, standard axioms only, declarations exist | `tools/check.py`, CI, branch protection |
| Statement matches the literature | red-team pass before posting; human statement review on the pull request |
| Identities proved exactly; inclusions not presented as endpoints (decision 0004) | red-team pass; reviewer |
| Statement is not vacuous; conventions recorded | `nonvacuity-tests` rung; `docs/conventions.md`; red-team items 6 to 8 |
| Upstream definitions unchanged by a pin bump | red-team diff of the definitions in `docs/conventions.md` |
| "Known" claims carry a citation key or "unverified" | red-team pass; `docs/references.md` |
| One rung per pull request, no statement edits | pull request template; reviewer |
| Public words: checked / stated / open / refuted / dead | `CLAUDE.md` writing conventions; the site reads the ledger and nothing else |
| No secrets, no private paths | `.gitignore`, pre-commit grep, CI needs no credentials by design |

## Running agents

- One at a time, by hand: `/prove-rung <id>`, `/post-rungs`, `/red-team <id>` in Claude Code.
- Unattended: a `/loop` or a scheduled routine that runs `/prove-rung` on the next ready rung, with a cap of one pull request per run. Switch this on only after five rungs have gone through by hand and the handoffs read clean.
- Fan-out (several provers on several rungs, or several red-teamers on one statement) uses the Workflow tool when the owner opts in for that session. The ledger and branch protection make collisions cheap: two pull requests on one rung means one gets closed.

## Budgets and stop conditions

- A prover stops after one session or one pull request, whichever first.
- A rung released three times goes back to the orchestrator as "needs split" and is not reposted as is.
- A front with no stated rung after two thinker sessions is marked dead with the sketches kept.
- Token spend per rung is recorded in the handoff when known. Spend without a handoff is the failure mode to watch.

## What success looks like at each stage

| Stage | Visible signal |
|---|---|
| Harness works | Five rungs through the full lifecycle by hand, each with a handoff and a clean pull request |
| M1 | `lefschetz-1-1-equality` checked; red-team `pass`; non-vacuity suite checked; exact divisor–Chern sign in the conventions register |
| M2 | Markman inventory written; `markman-statement` stated |
| Unattended | a week of loop runs with no closed-as-duplicate pull requests and no statement edits |
