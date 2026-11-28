# hodgeconjecture: project instructions

A public ladder of Lean 4 proofs about the Hodge conjecture, built by humans and coding agents. The conjecture and its standard variants are stated upstream in `Paul-Lez/HodgeConjecture`, which this repository imports at a pinned commit; every result here is a Lean declaration about those statements that the pinned toolchain accepts. Nothing else counts as progress. This file is the operating manual for any agent or person working in the tree.

## What this repo is

A proof repository with a thin Python harness around it. There is one library (`HodgeLadder/`), one upstream dependency holding the statements of record (`HodgeConjecture`, from `Paul-Lez/HodgeConjecture`), one checker (`tools/check.py`), one ledger (`ledger/ladder.json`) and the documents that explain them. Quality is measured by the checker exiting 0 on `main` and by the ledger telling the truth about what is checked and what is open.

## Boundaries

- **Public.** Everything in this repository is public. Do not add credentials, private paths, personal email addresses, or references to other private projects. Commit with the GitHub noreply address (set per-repo in `.git/config`).
- **Lean first.** A claim becomes a result only when it is a sorry-free Lean declaration that `tools/check.py` accepts with the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Prose, sketches and Python prove nothing here; they organize the search.
- **Statements of record are upstream.** Do not restate the conjecture or a variant that `Paul-Lez/HodgeConjecture` states; prove theorems whose types are those `Prop`s. No interface structures for missing objects (decision 0003). Do not add notation, instances or attributes that change how an upstream statement elaborates.
- **Local lemmas (decision 0011).** General lemmas the ladder needs are written and kept here; this repository does not open pull requests against Mathlib or `Paul-Lez/HodgeConjecture`. Use what Mathlib and upstream already have at the pin before writing a local copy, and list general local lemmas in `docs/gaps.md` "General lemmas kept local" so a pin bump can check them for clashes.
- **Equality first.** Aim at non-vacuous equalities (decision 0004). Inclusions are steps; identities between classes are proved exactly, with the sign in the docstring and in `docs/conventions.md`; "up to a nonzero scalar" does not discharge an identity rung.
- **Falsification.** Every checked rung gets a red-team pass covering vacuity, sign and normalization conventions (`docs/conventions.md`), and upstream definition drift between pins. Keep the October 2026 sign-error withdrawals (arXiv:2610.30976) in sight.
- **Harness-neutral corpus.** `AGENTS.md`, `CONTRIBUTING.md` and `docs/` are written for any agent or person. Claude-Code-specific detail stays in this file and in `.claude/` (per-developer settings are gitignored).
- **Scope.** The target is the statement in `docs/statement.md`. Formalizing foundations that Mathlib lacks (differential forms, de Rham cohomology, Kähler geometry) is in scope when the roadmap names it. Unrelated Mathlib contributions are not.

## Status

**2026-11-27 (round six: de Rham cup, ℙ² orientation, products).** Merged: `p2-fundamental-class-every-point` (#206, exactly one μ ∈ H₄(ℙ²(ℂ); ℚ) restricts to the local orientation at every point; general lemmas in `HodgeLadder.General.LocalOrientation`), `de-rham-scalar-sheaf` (#207, S_c on Ω•_ℚ pinned to upstream's scalar map, scalar laws of deRhamWedge in both factors, S_c induces c • on H_dR), `complex-points-prod` (#208, ComplexPoint (X ⨯ Y) ≃ₜ ComplexPoint X × ComplexPoint Y pinned to the projections, product charts in the maximal atlas, `smooth_prod`), `de-rham-cup-exact` (#209, deRhamCup with ι (α ∪ β) = deRhamCup (ι α) (ι β) exact; on 𝔾ₘ² in degrees (1, 1) the (−1)^{ab} twist fails the identity and antisymmetry has the literature sign). **Next planned work:** `de-rham-cup` (#210) with `de-rham-cup-test-p2` (#211), then `cup-hodge-filtration` and `cup-hodge-classes`; `p1p1-witness` (#105, Segre embedding built, red team running); a pin-hierarchy pass over `docs/gaps.md`.

**2026-11-27 (round five, continued: base change, complex points, the wedge on Ω•_ℚ).** Merged: `de-rham-rational-base-change`, `de-rham-p2-top-rank` and `de-rham-rational-independent-test-gm2` (#199: ℂ ⊗_ℚ H^n(X; ℚ) ≃ₗ[ℂ] H_dR^n(X) for smooth projective integral X, finrank ℂ H_dR⁴(ℙ²) = 1, the two winding classes of 𝔾ₘ² stay ℂ-independent), `rational-cohomology-finite-dimensional` (#201, both sides of the base change finite-dimensional), `complex-point-nonempty` (#202, Nonempty (ComplexPoint X) for smooth integral X, so the nonvacuity tests of #188 and #190 hold unconditionally), `wedge-sheaf-map` (#203, deRhamWedge on Ω•_ℚ with Mathlib's Koszul sign (−1)^p only, its F^p ⊗ F^q restriction, unique, and the unit law). `de-rham-cup` split: the definition and the exact identity ι (α ∪ β) = deRhamCup (ι α) (ι β) are `de-rham-cup-exact`; ℂ-bilinearity waits on `de-rham-scalar-sheaf` (#204). **Next planned work:** `de-rham-cup-exact`, `de-rham-scalar-sheaf`, `p2-fundamental-class-every-point` (#183); then `de-rham-cup-test-p2` and `cup-hodge-filtration`.

**2026-11-27 (round five: rational structure on H_dR, sheafified wedge).** Merged: `de-rham-unit-nonzero` (#188, both units nonzero and distinct from their negatives), `wedge-sheafify` (#190, the wedge on Ω_ℚ pinned by its sheafification square, the forget iso and the unit law), `betti-additive-naturality` (#192, the port's coefficient change generalized to additive maps in place), `de-rham-rational-independent` (#195, ℚ-independent classes stay ℂ-independent on every smooth integral X), `simplicial-complex-span` and `de-rham-rational-span` (#196, rational classes span H_dR over ℂ for smooth projective X). With #195 this gives ℂ ⊗_ℚ H^n(X; ℚ) ≅ H_dR^n(X) up to the one-line rung `de-rham-rational-base-change` (#197). **Next planned work:** `wedge-sheaf-map` (#191, statement phase), then `de-rham-cup`; `de-rham-rational-base-change` (#197), `de-rham-p2-top-rank` (#198), `complex-point-nonempty` (#189).

Keep this block to one paragraph per state change, newest first, and trim anything older than three entries into `docs/decisions/` or the git log.

## Files

| Path | Role |
|---|---|
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Pins: upstream `Paul-Lez/HodgeConjecture` at an exact commit, and the Lean and Mathlib versions it pins (`v4.35.0-rc4`). Bump all of them together in one commit, after a red-team drift check. |
| `HodgeLadder.lean` | Library root. One `public import` per module. |
| `HodgeLadder/Basic.lean` | Namespace preamble and a toolchain smoke test. No content. |
| `HodgeLadder/General/{HomComplex,Homology,Ext,LocallyConstantSheaf,FreeAbelianTerminal,Codimension}.lean` | General lemmas kept local (decision 0011): Hom-complex composition, homology functors on cycles, `Ext` transport, the constant sheaf as locally constant functions, the generator of `ℤ[T]`, codimension-cycle facts. Rows in `docs/gaps.md`. |
| `HodgeLadder/Upstream/Statements.lean` | Rung `statements-consistent`: the upstream variants are instances of the upstream conjecture. |
| `HodgeLadder/CycleClass/Pins.lean` | Rung `cycle-class-pins`: `rfl` pins of each step of the upstream cycle-class and Hodge-class constructions; a change upstream breaks the build here. |
| `HodgeLadder/CycleClass/Statements.lean` | Rungs `known-half-statement`, `equality-reductions`: cycle classes are Hodge classes, the equality forms, and their equivalence with upstream inclusion plus known half. |
| `HodgeLadder/Tests/Witness.lean`, `HodgeLadder/Tests/CodimensionZero.lean` | Rung `nonvacuity-tests`: Spec ℂ satisfies the three hypotheses; the equality form holds non-vacuously in codimension zero (imports upstream's `Other` library). |
| `HodgeLadder/Lefschetz/OneOne.lean` | Rung `lefschetz-1-1`: `lefschetzOneOne_holds : LefschetzOneOne`, from the port. |
| `HodgeLadder/Hodge/{Conjugation,ZeroForms,FirstFiltration,ChernClasses}.lean` | Rung `chern-classes-are-hodge`: conjugation fixes rational classes; Ω⁰ ≅ 𝒪; F¹ = ker(H_dR → ℍ(𝒪)); rational c₁ and Cartier divisor classes are Hodge. |
| `port/LefschetzPort/`, `docs/port-lefschetz.md` | Staging library and log for the port of the upstream Lefschetz (1,1) stack to the current pin (rung `lefschetz-port`). A default target since part 9; holds the checked divisor–Chern identity (`hasDivisorClassOfCartierData`). |
| `docs/cycle-class.md` | How the cycle class is built at the pin, step by step, with the pins and upstream normalization theorems. |
| `.lake/packages/HodgeConjecture/` | Upstream source at the pin (statements of record). Read it; do not edit it. |
| `ledger/ladder.json` | Machine-readable status of every rung: `checked`, `stated`, `open`, `refuted`, `dead`. The website reads this file. |
| `tools/check.py` | The checker: `lake build`, sorry scan, `#print axioms` for every declaration a `checked`/`stated` rung names, ledger validation (statuses and kinds). Standard library only. |
| `tools/next.py` | Prints the prover brief for the next ready rung or a named one (`--all`, `--json`). The local equivalent of a "desk". |
| `.claude/agents/hodge-{orchestrator,thinker,red-team,prover,librarian}.md` | Claude Code subagent definitions, one per role in `docs/harness.md`. Convenience layer over `AGENTS.md`; the neutral file wins on conflict. |
| `.claude/skills/{prove-rung,post-rungs,red-team}/SKILL.md` | Session entry points: `/prove-rung <id>`, `/post-rungs`, `/red-team <id>`. |
| `AGENTS.md` | Instruction sheet for an outside coding agent: how to pick a rung, prove it, and submit it. |
| `CONTRIBUTING.md` | Rules for pull requests, human or agent. |
| `docs/problem.md` | The complete picture: statement, variants and their status, known cases by degree and class, reductions, obstructions, approaches, what it means for the ladder. Every claim keyed to `docs/references.md`. |
| `docs/strategy.md` | What we attack and in what order: milestones M0 to M5, fronts with kill criteria, the words we use in public. |
| `docs/harness.md` | How a session runs: roles, where prompts live, rung lifecycle, interface-first pattern, gates, budgets. |
| `docs/references.md` | Citation keys. A "known" claim anywhere carries a key or the word "unverified". |
| `docs/sketches/<id>.md`, `docs/sketches/<id>.redteam.md` | Thinker sketch and red-team verdict per rung. A statement rung is posted only with a `pass`. |
| `docs/handoffs/YYYY-MM-DD-<id>.md` | Five to fifteen lines per session: what moved, what failed, next move. |
| `docs/statement.md` | The conjecture, informal statement and formalization targets. |
| `docs/roadmap.md` | The ladder: what Mathlib has, what is missing, in what order. |
| `docs/conventions.md` | Register of sign and normalization conventions every statement and proof depends on; maintained by the red team. |
| `docs/audits/` | Dated conformance audits against the literature. |
| `docs/notes/` | Dated research notes: ideas reviewed against the literature, kept in corrected form, with what was set aside and why. A note can propose rungs; it is not a result. |
| `docs/gaps.md` | Acknowledged gaps: general lemmas kept local (grouped by the Mathlib or upstream area they shadow, with import layers), known weaknesses, dropped threads. |
| `docs/pin-walk.md`, `tools/pinwalk.py` | Pin-bump procedure: walk the `docs/gaps.md` kept-local categories in layer order, `python3 tools/pinwalk.py --clash <Mathlib or upstream dir>` for name and phrase candidates, `--hubs` for frozen hub modules (do not edit a checked hub; add lemmas in new leaf modules), then the pin modules and the `docs/conventions.md` drift list. |
| `docs/decisions/` | Architecture decision records, one decision per file, numbered; numbers are permanent. |
| `.github/workflows/ci.yml` | Runs `tools/check.py` on pushes to `main` and on pull requests from forks (decision 0007). |
| `.github/ISSUE_TEMPLATE/gap.md`, `.github/PULL_REQUEST_TEMPLATE.md` | Intake shapes for a new rung and for a proof. |

## Commands

| Command | Use |
|---|---|
| `lake build` | Build the library. Mathlib comes from the prebuilt cache; upstream's statement closure compiles locally (several hundred files, first build only). A build that starts compiling Mathlib means the pin moved: run `lake exe cache get`. |
| `lake env lean <file>` | Check one file. |
| `python3 tools/check.py` | Full check (build, sorry, axioms, ledger). Run before every commit. |
| `python3 tools/check.py --no-build` | Same, assuming the build is current. |
| `python3 tools/next.py [id]` | Brief for the next ready rung, or the named one. Start of every prover session. |
| `/prove-rung <id>`, `/post-rungs`, `/red-team <id>` | The three session modes, as skills. |
| `lake update` | Only after editing `lakefile.toml`; commit `lake-manifest.json`. |
| `python3 tools/pinwalk.py [--hubs \| --clash DIR]` | Layers, frozen hubs and clash candidates for a pin bump (`docs/pin-walk.md`). |

## Conventions

- Every file starts with `module`. Use `public import` for anything a downstream file needs re-exported; plain `import` otherwise. Put `@[expose] public section` at the top of files that define things other modules unfold.
- One topic per module under `HodgeLadder/`, re-exported from `HodgeLadder.lean`. Namespace `HodgeLadder`. Upstream declarations live in their own namespaces (`AlgebraicGeometry.ComplexPoint`, root-level `HodgeConjecture`, `LefschetzOneOne`); refer to them, do not shadow them.
- Prefer `theorem` for propositions, `def` for data, `lemma` only inside a namespace where it reads naturally. Docstrings on every public declaration. Each file carries a module docstring with `Main definitions` and `Main results`.
- `import Mathlib` is fine while exploring; narrow to specific modules before the pull request.
- No `sorry` on `main`. A rung whose statement compiles with `sorry` in the proof goes in a branch, or in the ledger as `stated` once the statement itself is sorry-free and the proof is still open.
- Variable binders: bind instance arguments per declaration (`[Zero R]` on the theorem, not on the section) when a section mixes `Zero`, `AddMonoid` and `AddGroup`; a section-level `[Zero R]` conflicts with a later `[AddGroup R]`.
- Cross-reference by ledger rung id (for example `Z-cycles`) in prose, issues and commit messages. Ids are stable identifiers; to retire one, mark it `dead` and add a new rung instead.

## Change propagation map

| Change | Files to touch, in order |
|---|---|
| **Prove a rung** | 1. Lean module under `HodgeLadder/` 2. `HodgeLadder.lean` import 3. `ledger/ladder.json`: status, module, declarations, contributors 4. `docs/roadmap.md` row 5. Status block above |
| **Add a rung** | 1. `ledger/ladder.json` entry with `depends_on` 2. `docs/roadmap.md` row 3. open a GitHub issue from the gap template so outside agents can find it |
| **Use a new upstream statement** | 1. confirm it exists at the pin 2. ledger rung with `kind` and the upstream declaration names 3. red-team pass 4. `docs/statement.md` if it is a new variant |
| **Add a local definition Mathlib lacks** | 1. The module 2. `docs/gaps.md` "General lemmas kept local" table |
| **Bump the upstream pin (and with it Lean and Mathlib)** | 0. follow `docs/pin-walk.md` 1. red-team drift check of the definitions in `docs/conventions.md` 2. `lakefile.toml` (upstream rev, Mathlib rev) and `lean-toolchain` 3. `lake update`, commit `lake-manifest.json` 4. `ledger/ladder.json` toolchain block 5. `README.md` version line 6. handoff noting the drift result |
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

- `main`: always green. Direct pushes allowed for the maintainer on documentation; proofs land by pull request. The maintainer's pull requests merge on a clean local `python3 tools/check.py`, and CI rechecks `main` after the merge; pull requests from forks are checked by CI before review (decision 0007).
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
- Do not edit anything under `.lake/packages/`; write what the ladder needs locally (decision 0011).
