# Port log: upstream Lefschetz (1,1) stack to the current pin

Rung `lefschetz-port`. Source: the upstream stack on Lean and Mathlib v4.33.1 (PRs #217–#226, #9, #230, #228; head `c7d5c94b`, verified in `docs/sketches/lefschetz-1-1-upstream.md`). Target: upstream main at the pin in `lakefile.toml` (`2ead713`, v4.35.0-rc4). Staging library: `port/LefschetzPort` (lean_lib `LefschetzPort`, not a default target). Files keep their upstream headers; ported parts go back upstream once the authors agree on the shape (questions posted on upstream PR #228, 2026-11-24).

Method per part: stage the part's new `Other/` modules at that part's own head; route imports of stack-new modules into the staging library; keep imports of modules that exist on main; do not stage edits to files that exist on main unless the build needs them; build every staged module against the pin.

## Status

| Part | Upstream PR | Content | Modules | Port changes | Status |
|---|---|---|---|---|---|
| 1/11 | #217 | algebraic generators, Cartier data, divisor cycle; vendored Tau Ceti invertible sheaves | 7 | none | builds at the pin |
| 2/11 | #218 | first Chern classes in ordinary sheaf cohomology; exponential sequence; holomorphic logarithm | 10 | `HolomorphicUnitExtension.lean`: main keeps the universe-0 `HasExt` instance for analytic sheaves local to `Hodge/Filtration.lean`, so it is restated locally and `extClass` is called at universe 0 explicitly. The part's edits to statement-level files are not staged: main already computes these groups in universe 0 | builds at the pin |
| 3/11 | #219 | analytic line bundles and module analytification | 7 | none | builds at the pin |
| 4/11 | #220 | statement of divisor–Chern compatibility | 1 | none; the part's edits to three existing files were not needed | builds at the pin |
| 5/11 to 10/11 | #221–#226 | cohomology tools, exponential classes and winding, local divisor equations, normal charts, the identity's proof, finite integral homology | | | not started |
| 11/11 | #9 | reduction to algebraization of line bundles | | | not started |
| Oka | #230 | proper GAGA, 372 modules | | | waiting on upstream's answer: dependency or vendored |
| final | #228 | the theorem | | | not started |

## What part 4 fixes for the sign question

The staged statement `HasDivisorClassOfCartierData` says: for every Cartier datum c representing an invertible sheaf L whose analytification is the section sheaf of a unit extension E,

  sheafCycleClassOnCycles 1 c.divisor = integralToRationalCohomology 2 E.firstChernClass,

with sign +. On main, `sheafCycleClassOnCycles` (upstream `Other/AlgebraicGeometry/Cycle/SheafClass.lean`) is built from main's `cycleComponentSheafClass`, the class of record, and `sheafCycleClassOnCycles_single` gives each component its exact integer multiplicity. So the ported statement is about the class of record, and proving it at the pin (part 9) is rung `divisor-chern-exact`. Where the branch's proof used its older cycle-class model, the port must redo it on main's; a proof that only gives the identity up to a nonzero scalar does not discharge the rung (decision 0004).

## Counts

| | Value |
|---|---|
| Modules staged and built | 25 |
| `sorry` in staged files | 0 |
| Build of `LefschetzPort` at the pin | 4,748 jobs, success |
