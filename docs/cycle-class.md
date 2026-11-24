# The cycle class, as encoded

The known half of the Hodge conjecture says the class of every subvariety is a Hodge class. That statement means something only with the class pinned down. This page records how the class is built at the upstream pin (`Paul-Lez/HodgeConjecture`, see `lakefile.toml`), which steps are pinned here by definitional-equality tests, and which normalization theorems upstream proves. Lean: `HodgeLadder/CycleClass/Pins.lean`, `HodgeLadder/CycleClass/Statements.lean`; ledger rungs `cycle-class-pins`, `known-half-statement`, `equality-reductions`.

## Construction

Let X be smooth, integral and projective over ℂ, and Z ⊆ X an integral closed subvariety of codimension p with generic point x (a point of coheight p). Cohomology is sheaf cohomology of constant sheaves on X(ℂ) with the analytic topology.

| Step | Upstream declaration | What it does | Pinned here by |
|---|---|---|---|
| 1. Local class | `AlgebraicTopology.Singular.normalizedRelativeCoclass` applied to `standardComplexLocalClass` | on complex normal coordinates, the class in H^{2p}(ℂ^p, ℂ^p ∖ 0; ℚ) dual to the oriented generator, so that it pairs to 1 with it | upstream theorem `normalizedRelativeCoclass_pairing_self` (audited by the checker) |
| Orientation | `complexRealHomeomorph`, `standardComplexLocalClass` | real coordinates ordered (Re z₀, Im z₀, Re z₁, Im z₁, …) | `HodgeLadder.Pins.complexRealHomeomorph_eq`; upstream `standardComplexLocalClass_ne_zero` |
| Chart independence | `relativeHomologyMap_complexDifferentiable_standardComplexLocalClass` | a holomorphic germ fixing 0 with invertible derivative fixes the oriented local class | upstream theorem (audited by the checker) |
| 2. Gluing on Z_reg | `cycleComponentSmoothSupportCoclassSection` | the local classes glue to a section of the local cohomology sheaf with support Z(ℂ), over X(ℂ) ∖ Z_sing(ℂ) | used by step 3's pin |
| 3. Extension by purity | `cycleComponentSupportedClassNormalizationIso`, `cycleComponentSupportedInjectiveClass` | lowest-degree purity identifies H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) with those sections; the supported class is the unique preimage | `cycleComponentSupportedInjectiveClass_eq` |
| 4. Forget support | `forgetSupport`, `cycleComponentSheafClass` | H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) → H^{2p}(X(ℂ); ℚ) | `cycleComponentSheafClass_eq` |
| 5. Span | `algebraicCycleClassSpan` | ℚ-span of the classes of all points of coheight p | `algebraicCycleClassSpan_eq` |

Hodge side, for comparison: `hodgeClasses` (pinned by `hodgeClasses_eq`) is the set of rational classes whose de Rham image lies in `hodgePiece X p p (2p)`, which is F^p ∩ conj F^p (pinned by `hodgePiece_eq`), with F^p the image of the hypercohomology of holomorphic forms of degree at least p.

## Statements built on it

| Lean | Meaning | Status |
|---|---|---|
| `HodgeLadder.CycleClassesAreHodge` | algebraicCycleClassSpan X p ≤ Hdg^p(X; ℚ), all X and p | stated; proof is rung `cycle-classes-are-hodge` |
| `HodgeLadder.HodgeConjectureEquality` | Hdg^p(X; ℚ) = algebraicCycleClassSpan X p | stated |
| `HodgeLadder.LefschetzOneOneEquality` | Hdg^1(X; ℚ) = algebraicCycleClassSpan X 1 | stated; proof is rung `lefschetz-1-1-equality` |
| `HodgeLadder.hodgeConjectureEquality_iff` | equality ↔ upstream `HodgeConjecture` ∧ the known half | checked |
| `HodgeLadder.lefschetzOneOneEquality_iff` | codimension-one equality ↔ upstream `LefschetzOneOne` ∧ the known half in codimension one | checked |

## What is not yet encoded

- A theorem that the class depends on Z only (independence of compactification and the rational-equivalence invariance upstream mentions as separate statements).
- The sign relating this class to the first Chern class of 𝒪(Z): rung `divisor-chern-exact`.
- Any computed value: rung `projective-space-test` (the hyperplane class of ℙ^n spans Hdg^1).
