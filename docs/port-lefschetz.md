# Port log: upstream Lefschetz (1,1) stack to the current pin

Rung `lefschetz-port`. Source: the upstream stack on Lean and Mathlib v4.33.1 (PRs #217–#226, #9, #230, #228; head `c7d5c94b`, verified in `docs/sketches/lefschetz-1-1-upstream.md`). Target: upstream main at the pin in `lakefile.toml` (`2ead713`, v4.35.0-rc4). Staging library: `port/LefschetzPort` (lean_lib `LefschetzPort`, not a default target). Files keep their upstream headers (Apache 2.0). The port lives on this repository's branch `port/lefschetz` and does not wait on upstream: Oka's proper GAGA is staged here as well. Questions were posted on upstream PR #228 (2026-11-24); contributing the port upstream is optional and later.

Method per part: stage the part's new `Other/` modules at that part's own head; route imports of stack-new modules into the staging library; keep imports of modules that exist on main; do not stage edits to files that exist on main unless the build needs them; build every staged module against the pin.

## Status

| Part | Upstream PR | Content | Modules | Port changes | Status |
|---|---|---|---|---|---|
| 1/11 | #217 | algebraic generators, Cartier data, divisor cycle; vendored Tau Ceti invertible sheaves | 7 | none | builds at the pin |
| 2/11 | #218 | first Chern classes in ordinary sheaf cohomology; exponential sequence; holomorphic logarithm | 10 | `HolomorphicUnitExtension.lean`: main keeps the universe-0 `HasExt` instance for analytic sheaves local to `Hodge/Filtration.lean`, so it is restated locally and `extClass` is called at universe 0 explicitly. The part's edits to statement-level files are not staged: main already computes these groups in universe 0 | builds at the pin |
| 3/11 | #219 | analytic line bundles and module analytification | 7 | none | builds at the pin |
| 4/11 | #220 | statement of divisor–Chern compatibility | 1 | none; the part's edits to three existing files were not needed | builds at the pin |
| 5/11 | #221 | cohomology tools: mapping cones, connecting maps, supported and relative cochains, flasque models | 51 | six, all from Mathlib drift: (a) `Q` is no longer definitionally `quotient ⋙ Qh`, so `PrecompFactorization` and `HypercohomologyFlasqueNaturality` move across `DerivedCategory.quotientCompQhIso` and use `DerivedCategory.Q_map_eq_of_homotopy`; (b) newer `simp` closes two goals in `RelativeCochainConeForgetComparison` and `RelativeCochainConeBoundaryComparison`, so trailing `rfl`s are removed; (c) `SingularExcisionScalar` needs an explicit import of `Mathlib.CategoryTheory.Limits.MonoCoprod`. No statement changed | builds at the pin |
| 6/11 | #222 | exponential classes, winding cochains and boundaries, restriction to opens, cohomology with support | 36 | (a) Mathlib's topological simplex is now the type `Convexity.StdSimplex`; supplement `Supplement/StdSimplex` gives a homeomorphism with the old subset and transfers contractibility and local path-connectedness; `ChernWindingCochain` and `ChernWindingRational` rewritten to the new API (`single`, `map_single`, `continuous_map ℝ`); (b) the global universe-0 `Ext` instance the stack relies on is restated in `Supplement/AnalyticExt` and imported into every staged geometry and topology file, and `extClass` of analytic sequences is taken at universe 0 explicitly (`Ext` and `H^n` therefore land in the same universe as main's statement of record); (c) lemmas the stack adds to files that exist on main are staged in `Supplement/MapExtend`, `Supplement/ShiftedExact`, `Supplement/RelativeCochainCone` (the last re-declares a lemma that is `private` on main); the branch-only file `HodgeConjecture/Mathlib/CategoryTheory/Localization/SmallShiftedHom.lean` is staged under `LefschetzPort/HC/`; (d) newer `simp`/`convert` close five goals, so redundant final steps are removed; (e) one coerced inverse needs `erw`; (f) one theorem's heartbeat budget raised from 1e6 to 4e6 (`ChernClassRestrictionVanishing`, step 3c). No statement changed | builds at the pin |
| 7/11 | #223 | local divisor equations, discrete valuations, normal derivatives, point jets | 18 | (a) the branch-only notation module `HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation` is now in Mathlib under the same name, so Mathlib's module is imported; (b) two missing transitive imports added (`Mathlib.Analysis.Analytic.Constructions`, `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`); (c) one singleton `{f a b}` parenthesized, since current Lean reads it as set-builder notation | builds at the pin |
| 8/11 | #224 | normal charts, winding on charts, the local model and the divisor–Chern assembly | 54 | **The bridge to main's cycle class of record.** (a) `CycleClassExtComparison.cycleComponentSheafClass_eq_injectiveModel` is restated on main's class: the supported class (main's `Ext` model) is transported exactly into the injective model by main's `rationalSupportAddEquivSupportedInjectiveHomology`; the proof is three rewrites, no scalar. (b) `ChernLocalModel`: new `componentTransport` (that equivalence, per component); `HasChernLocalModel` applies main's normalization `cycleComponentSupportedClassNormalizationIso` after transport; the uniqueness step concludes with main's class transported, using main's `cycleComponentSupportedInjectiveClass_normalization`; the assembly `hasDivisorClassOfCartierData_of_localModel` closes through the bridge. (c) `ChernLocalModelWinding` uses the same routing. (d) Supplement `Supplement/SupportExtension`: injective-model vanishing of the singular boundary in degrees 2p, 2p+1 derived from main's public `Ext`-model lemma across the same equivalence, and the branch's restriction isomorphism restated with upstream's proof. (e) Mathlib drift: `Convexity.StdSimplex` coordinates as `weights` in `ChernWindingStandardTriangle` (with main's `weights_map_apply`); coordinate lemmas of `Complex.piCoordCLE` re-proved via `smulTower'_repr` (statements unchanged); one `erw`; universe-0 `extClass` lemma | builds at the pin |
| 9/11 to 10/11 | #225–#226 | the identity's proof, finite integral homology | | | not started |
| 11/11 | #9 | reduction to algebraization of line bundles | | | not started |
| Oka | #230 | proper GAGA, 372 modules | | | to be staged here |
| final | #228 | the theorem | | | not started |

## What part 4 fixes for the sign question

The staged statement `HasDivisorClassOfCartierData` says: for every Cartier datum c representing an invertible sheaf L whose analytification is the section sheaf of a unit extension E,

  sheafCycleClassOnCycles 1 c.divisor = integralToRationalCohomology 2 E.firstChernClass,

with sign +. On main, `sheafCycleClassOnCycles` (upstream `Other/AlgebraicGeometry/Cycle/SheafClass.lean`) is built from main's `cycleComponentSheafClass`, the class of record, and `sheafCycleClassOnCycles_single` gives each component its exact integer multiplicity. So the ported statement is about the class of record, and proving it at the pin (part 9) is rung `divisor-chern-exact`. Where the branch's proof used its older cycle-class model, the port must redo it on main's; a proof that only gives the identity up to a nonzero scalar does not discharge the rung (decision 0004).

## Not staged on purpose

The branch-only file `HodgeConjecture/Definitions/AlgebraicGeometry/Cycle/Transport/CohomologySheaf.lean` carries the branch's older cycle-class model. It is staged only if a later part needs it, and then only behind an explicit bridge to main's class (rung `divisor-chern-exact`); the port's statements stay on main's class of record.

## Counts

| | Value |
|---|---|
| Modules staged and built | 191 (184 from the stack, 6 supplements, 1 branch-only upstream file) |
| `sorry` in staged files | 0 |
| Build of `LefschetzPort` at the pin | 4,986 jobs, success |
