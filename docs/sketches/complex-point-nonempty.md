# Sketch: `complex-point-nonempty`

Rung: `Nonempty (ComplexPoint X)` for `X : Over (Spec ↧ℂ)` with `IsIntegral X.left` and `Smooth X.hom`. Purpose: red team of `de-rham-unit-nonzero`, change 5 (optional). The general nonvacuity tests of that rung and `wedgeSheaf_ne_zero` (rung `wedge-sheafify`) take `Nonempty (ComplexPoint X)` as an argument; this rung discharges it on every smooth integral `X`.

Inventory taken 2026-11-27 at the upstream pin `2ead713`. Verdict: one session, a few lines of Lean. Modules `HodgeLadder.General.ComplexPoint` (the three lemmas, light imports) and `HodgeLadder.Tests.ComplexPointNonempty` (the corollaries and the empty-scheme check), split on the red team's change 2.

## Definition at the pin

Upstream's `ComplexPoint X` is `Point ℂ X` (`HodgeConjecture/Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean`), the morphisms `Spec ℂ ⟶ X.left` over `Spec ℂ`. A term is `Over.homMk p h` for a section `p` of `X.hom`.

## Route

| Step | At the pin |
|---|---|
| `X.hom` locally of finite type | Mathlib instance from `Smooth` (through `LocallyOfFinitePresentation`) |
| `X.left` nonempty | Mathlib instance from `IsIntegral` |
| `X.left` is a Jacobson space | Mathlib `LocallyOfFiniteType.jacobsonSpace` (the base `Spec ℂ` is Jacobson) |
| a closed point | Mathlib `nonempty_inter_closedPoints` with `Z = Set.univ` (open, so locally closed) |
| closed point to section of `X.hom` | Mathlib `pointEquivClosedPoint` (`AlgebraicGeometry/AlgClosed/Basic.lean`), for `ℂ` algebraically closed: the residue field at a closed point is finite over `ℂ`, which is the Nullstellensatz step |
| `IsAlgClosed ℂ` | `Mathlib.Analysis.Complex.Polynomial.Basic` |

The affine-open route of the posted note (a nonzero finitely generated `ℂ`-algebra has a maximal ideal with residue field `ℂ`) is the same argument; Mathlib packages it at the level of schemes, so no affine cover is chosen.

## Hypotheses

Integrality is used only for nonemptiness and smoothness only for local finite type. The general form is `[Nonempty X.left] [LocallyOfFiniteType X.hom]`. Under local finite type the conclusion is equivalent to `Nonempty X.left` (a complex point evaluated at the closed point of `Spec ℂ` is a point of `X.left`), so this form is sharp. The empty scheme shows `Nonempty X.left` cannot be dropped.

## Upstream overlap

Upstream's `Other` library has the instance `AlgebraicGeometry.ComplexPoint.instNonemptyComplexPoint` (`Other/AlgebraicGeometry/ComplexPoint/ProjectiveConnected.lean`), the same argument under `IsIntegral X.left` and `LocallyOfFiniteType X.hom`. That instance proves `nonempty_complexPoint` by `inferInstance` and is already in the library root's closure, through `HodgeLadder.Tests.CodimensionZero`. The light file `HodgeLadder.General.ComplexPoint` imports no `Other` module and no ladder module. The local copy is kept (decision 0011) for the weaker hypothesis `Nonempty X.left`, the `iff`, and the light import; it is listed in `docs/gaps.md`.

## Corollaries

The primed forms `Tests.fieldToHolomorphicDeRhamComplexInt_ne_zero'`, `Tests.rationalDeRhamUnit_ne_zero'`, `Tests.nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero'`, `Tests.fieldToHolomorphicDeRhamComplexInt_ne_neg'`, `Tests.rationalDeRhamUnit_ne_neg'` and `wedgeSheaf_ne_zero'` restate the checked tests on every smooth integral `X` with no point argument, in `HodgeLadder.Tests.ComplexPointNonempty`. Where upstream's instance is imported the unprimed originals already apply, so the primed forms record that the hypothesis is removable more than they add reach. `Tests.not_nonempty_complexPoint_empty` checks that the empty scheme over `Spec ℂ` has no complex point. The checked file `HodgeLadder.Tests.DeRhamUnitNonzero` is unchanged.

## For the red team

- Vacuity: `ComplexPoint X` is a type of morphisms; inhabitation is the whole content. `infer_instance` and the trivial tactics fail on the statement in the light import set (upstream's instance, reachable from the root, closes it there).
- Conventions: none involved; no sign or normalization enters.
- Drift: the proof depends on `ComplexPoint` being `Point ℂ X` with `Point` the sections over `Spec ℂ`; a change of that definition upstream breaks `Over.homMk z.1 z.2` at build time.
