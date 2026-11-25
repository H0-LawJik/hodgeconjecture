# Port log: Tau Ceti material backported to the current pin

Source: Tau Ceti (https://github.com/TauCetiProject/TauCeti, Apache 2.0), commit
`7433fc3695f4fbf5a07041090628c5c94067c0b9` (2026-11-25), Lean v4.37.0-rc1, Mathlib
`31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. Target: the pin in `lakefile.toml` (Lean and Mathlib
v4.35.0-rc4). Staging library: `port/LefschetzPort`, under `LefschetzPort.TauCeti.*`. The four
invertible-sheaf files already there (`LefschetzPort.TauCeti.SheafOfModules.*`) came in through the
upstream Lefschetz stack, from Tau Ceti commit `b8d215394069a6c5713292fadcfa49746702a0eb`; see
`docs/port-lefschetz.md`, part 1.

Method: copy each file with its header; rewrite `import TauCeti.X` to
`import LefschetzPort.TauCeti.X`; keep the `TauCeti` namespace; add a provenance line to the module
docstring; build at the pin; record every change below. Tau Ceti code is written by AI contributors
under AI review (its README); the checker's axiom audit is the acceptance test here.

## Status

| Batch | Tau Ceti modules | Content | Port changes | Status |
|---|---|---|---|---|
| H1 | `Basic.Complex.ConjZPow`, `LinearAlgebra.Complex.{Module,Conjugation}`, `LinearAlgebra.Basis.Semilinear`, `RingTheory.TensorProduct.IsBaseChange`, `Geometry.Hodge.{Conjugation,Structure}` | conjugations on complex vector spaces; pure Hodge structures of any weight on a complex space with a conjugation (Deligne's opposed filtrations), Hodge components, transport | one: `Geometry/Hodge/Conjugation.lean` relies on `autoImplicit` to bind the universes `u v` after a namespace is reopened; this repository builds with `autoImplicit = false`, so `universe u v` is declared again there. No statement changed | builds at the pin |

## Checks at the pin

| Check | Result |
|---|---|
| `lake build LefschetzPort.TauCeti.Geometry.Hodge.Structure` | success (seven modules, 3,297 lines) |
| `sorry`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `run_cmd`, `initialize` in the seven files | none |
| `#print axioms` on `HodgeStructureOn`, `HodgeStructureOn.conj_piece`, `HodgeStructureOn.finite_setOf_piece_ne_bot`, `HodgeStructureOn.comap`, `Conjugation.tensorProduct`, `Conjugation.dual`, `complexificationConjugation` | `propext`, `Classical.choice`, `Quot.sound` |

## Why this batch

It is the base of Tau Ceti's Hodge-structure library (weight-one structures, Weil operator,
polarizations, Mumford-Tate groups), which is the linear-algebra input for the Weil-class targets
in `docs/notes/2026-11-25-markman-inventory.md`. Nothing in the ladder names these declarations
yet; they are staged so that later batches (`Geometry/Hodge/WeilOperator`,
`Geometry/Hodge/WeightOne/*`) can be ported on top of them.
