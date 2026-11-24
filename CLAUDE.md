# hodgeconjecture: project instructions

Lean 4 formalization of the Hodge conjecture, built in public by humans and coding agents. Every result in this repository is a Lean declaration that the pinned toolchain accepts; nothing else counts as progress. This file is the operating manual for any agent or person working in the tree.

## What this repo is

A proof repository with a thin Python harness around it. There is one library (`HodgeConjecture/`), one checker (`tools/check.py`), one ledger (`ledger/ladder.json`) and the documents that explain them. Quality is measured by the checker exiting 0 on `main` and by the ledger telling the truth about what is checked and what is open.

## Boundaries

- **Public.** Everything in this repository is public. Do not add credentials, private paths, personal email addresses, or references to other private projects. Commit with the GitHub noreply address (set per-repo in `.git/config`).
- **Lean first.** A claim becomes a result only when it is a sorry-free Lean declaration that `tools/check.py` accepts with the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Prose, sketches and Python never prove anything here; they organize the search.
- **Mathlib is upstream.** Prefer Mathlib definitions over local ones. If a definition is missing, add the smallest local version, mark it in `docs/gaps.md` as a candidate for upstreaming, and do not fork Mathlib behavior silently.
- **Harness-neutral corpus.** `AGENTS.md`, `CONTRIBUTING.md` and `docs/` are written for any agent or person. Claude-Code-specific detail stays in this file and in `.claude/` (per-developer settings are gitignored).
- **Scope.** The target is the statement in `docs/statement.md`. Formalizing foundations that Mathlib lacks (differential forms, de Rham cohomology, Kähler geometry) is in scope when the roadmap names it. Unrelated Mathlib contributions are not.

## Status

**2026-11-23, later.** Strategy and harness written (`docs/strategy.md`, `docs/harness.md`). Ledger gained `kind` and five interface-first rungs (`hodge-interface`, `statement-interface`, `case-trivial-degrees`, `case-lefschetz-1-1`, `reduce-hard-lefschetz`); `statement` now also depends on `statement-interface`. Roles exist as `.claude/agents/`; entry points as `/prove-rung`, `/post-rungs`, `/red-team`; `tools/next.py` prints briefs. Nothing has gone through the lifecycle yet; the first target is five rungs by hand (harness.md, "What success looks like").

**2026-11-23.** Scaffolded; Mathlib pinned at `v4.36.0`; checker and ledger live; CI configured. One rung checked (`Z-cycles`). Verdict: **open**.

**Next planned work:** `rational-equivalence` (M0) and `hodge-interface` (M1) are both ready; run a thinker then a red team on `hodge-interface` before any prover touches it.

Keep this block to one paragraph per state change, newest first, and trim anything older than three entries into `docs/decisions/` or the git log.

## Files

| Path | Role |
|---|---|
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Pins: Lean `v4.36.0`, Mathlib tag `v4.36.0`. Bump all three together in one commit. |
| `HodgeConjecture.lean` | Library root. One `public import` per topic module, in ladder order. |
| `HodgeConjecture/Basic.lean` | Namespace preamble and a toolchain smoke test. No content. |
| `HodgeConjecture/Cycles/Codimension.lean` | Rung `Z-cycles`: `IsCodim`, `codimCycles`, relation to Mathlib's Weil divisors. |
| `ledger/ladder.json` | Machine-readable status of every rung: `checked`, `stated`, `open`, `refuted`, `dead`. The website reads this file. |
| `tools/check.py` | The checker: `lake build`, sorry scan, `#print axioms` for every declaration a `checked`/`stated` rung names, ledger validation (statuses and kinds). Standard library only. |
| `tools/next.py` | Prints the prover brief for the next ready rung or a named one (`--all`, `--json`). The local equivalent of a "desk". |
| `.claude/agents/hodge-{orchestrator,thinker,red-team,prover,librarian}.md` | Claude Code subagent definitions, one per role in `docs/harness.md`. Convenience layer over `AGENTS.md`; the neutral file wins on conflict. |
| `.claude/skills/{prove-rung,post-rungs,red-team}/SKILL.md` | Session entry points: `/prove-rung <id>`, `/post-rungs`, `/red-team <id>`. |
| `AGENTS.md` | Instruction sheet for an outside coding agent: how to pick a rung, prove it, and submit it. |
| `CONTRIBUTING.md` | Rules for pull requests, human or agent. |
| `docs/strategy.md` | What we attack and in what order: milestones M0 to M5, fronts with kill criteria, the words we use in public. |
| `docs/harness.md` | How a session runs: roles, where prompts live, rung lifecycle, interface-first pattern, gates, budgets. |
| `docs/references.md` | Citation keys. A "known" claim anywhere carries a key or the word "unverified". |
| `docs/sketches/<id>.md`, `docs/sketches/<id>.redteam.md` | Thinker sketch and red-team verdict per rung. A statement rung is posted only with a `pass`. |
| `docs/handoffs/YYYY-MM-DD-<id>.md` | Five to fifteen lines per session: what moved, what failed, next move. |
| `docs/statement.md` | The conjecture, informal statement and formalization targets. |
| `docs/roadmap.md` | The ladder: what Mathlib has, what is missing, in what order. |
| `docs/gaps.md` | Acknowledged gaps: local definitions to upstream, known weaknesses, dropped threads. |
| `docs/decisions/` | Architecture decision records, one decision per file, numbered and never renumbered. |
| `.github/workflows/ci.yml` | Runs `tools/check.py` on every push and pull request. |
| `.github/ISSUE_TEMPLATE/gap.md`, `.github/PULL_REQUEST_TEMPLATE.md` | Intake shapes for a new rung and for a proof. |

## Commands

| Command | Use |
|---|---|
| `lake build` | Build the library. Mathlib comes from the prebuilt cache; a build that starts compiling Mathlib means the pin moved, run `lake exe cache get`. |
| `lake env lean <file>` | Check one file. |
| `python3 tools/check.py` | Full check (build, sorry, axioms, ledger). Run before every commit. |
| `python3 tools/check.py --no-build` | Same, assuming the build is current. |
| `python3 tools/next.py [id]` | Brief for the next ready rung, or the named one. Start of every prover session. |
| `/prove-rung <id>`, `/post-rungs`, `/red-team <id>` | The three session modes, as skills. |
| `lake update` | Only after editing `lakefile.toml`; commit `lake-manifest.json`. |

## Conventions

- Every file starts with `module`. Use `public import` for anything a downstream file needs re-exported; plain `import` otherwise. Put `@[expose] public section` at the top of files that define things other modules unfold.
- One topic per module under `HodgeConjecture/`, re-exported from `HodgeConjecture.lean`. Module names follow the ladder (`Cycles`, `Chow`, `Analytic`, `DeRham`, `Hodge`, `CycleClass`, `Statement`).
- Prefer `theorem` for propositions, `def` for data, `lemma` only inside a namespace where it reads naturally. Docstrings on every public declaration. Each file carries a module docstring with `Main definitions` and `Main results`.
- `import Mathlib` is fine while exploring; narrow to specific modules before the pull request.
- No `sorry` on `main`. A rung whose statement compiles with `sorry` in the proof goes in a branch, or in the ledger as `stated` once the statement itself is sorry-free and the proof is still open.
- Variable binders: bind instance arguments per declaration (`[Zero R]` on the theorem, not on the section) when a section mixes `Zero`, `AddMonoid` and `AddGroup`; a section-level `[Zero R]` conflicts with a later `[AddGroup R]`.
- Cross-reference by ledger rung id (for example `Z-cycles`) in prose, issues and commit messages. Ids are stable identifiers; never rename one, mark it `dead` and add a new rung instead.

## Change propagation map

| Change | Files to touch, in order |
|---|---|
| **Prove a rung** | 1. Lean module under `HodgeConjecture/` 2. `HodgeConjecture.lean` import 3. `ledger/ladder.json`: status, module, declarations, contributors 4. `docs/roadmap.md` row 5. Status block above |
| **Add a rung** | 1. `ledger/ladder.json` entry with `depends_on` 2. `docs/roadmap.md` row 3. open a GitHub issue from the gap template so outside agents can find it |
| **State the conjecture or a case** | 1. `HodgeConjecture/Statement.lean` (statement sorry-free; proof may be absent as a separate `open` rung) 2. ledger `stated` 3. `docs/statement.md` section "Formal statement" |
| **Add a local definition Mathlib lacks** | 1. The module 2. `docs/gaps.md` "To upstream" table 3. Mathlib issue or Zulip thread link if one exists |
| **Bump Lean or Mathlib** | 1. `lean-toolchain` 2. `lakefile.toml` rev 3. `lake update`, commit `lake-manifest.json` 4. `ledger/ladder.json` toolchain block 5. `README.md` version line 6. `.github/workflows/ci.yml` if the action pin changes |
| **Add or change a role or prompt** | 1. `docs/harness.md` roles table 2. `.claude/agents/<role>.md` 3. `AGENTS.md` if the outside-agent path changed 4. the skill that invokes it |
| **Open or kill a front** | 1. `docs/decisions/` record 2. `docs/strategy.md` fronts table 3. ledger rung with `kind: "front"` 4. issue |
| **Change the checker rules** | 1. `tools/check.py` 2. `CONTRIBUTING.md` "What the checker requires" 3. `AGENTS.md` same list 4. `docs/decisions/` record |
| **Mark a rung refuted or dead** | 1. Ledger status plus `note` naming what failed 2. `docs/gaps.md` "Dead ends" 3. Keep the Lean file if it holds a checked counterexample, delete it otherwise |

## Pre-commit checklist

- [ ] `python3 tools/check.py` exits 0
- [ ] Ledger edited if any rung changed state; `updated` date bumped
- [ ] New public declarations have docstrings; new modules have module docstrings and are imported from the root
- [ ] No `import Mathlib` in a file that is past exploration
- [ ] Propagation map consulted for the change type
- [ ] `git diff --cached | grep -iE 'token|password|secret|api[_-]?key|/home/'` is empty
- [ ] Commit author is the noreply address (`git log -1 --format=%ae`)

## Branching

- `main`: always green. Direct pushes allowed for the maintainer on documentation; proofs land by pull request so CI runs the checker.
- Topic branches named by rung id: `rung/rational-equivalence`.
- Outside contributions: fork, one rung per pull request, one Lean file added or changed.

## Writing conventions

- Voice: direct, second person, imperative. Primary reader is a coding agent, secondary a mathematician skimming.
- Tables over prose for lists of files, rules and rungs.
- Say "checked" for a result the checker accepts, "stated" for a sorry-free statement with an open proof, "open" otherwise. Do not say "proved" or "solved" about the conjecture anywhere in this repository until the `statement` rung is `checked`.
- Public copy (README, AGENTS, docs) avoids absolute claims and audience qualifiers. State counts, methods and why they matter.

## What NOT to do

- Do not weaken a statement to make it prove. Open a new rung for the weaker version and leave the original `open`.
- Do not add axioms, `native_decide`, or `unsafe` definitions to anything the ledger names.
- Do not commit `.lake/`, build products, or per-developer `.claude/settings.local.json` and `.mcp*.json`.
- Do not edit `ledger/ladder.json` to `checked` without the declarations named in it existing and passing `tools/check.py`.
- Do not reference private repositories, local filesystem paths, or other projects of the maintainer.
