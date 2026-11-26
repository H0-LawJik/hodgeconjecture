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
| H2 | import closure of `AlgebraicTopology.Cohomology.Cup.Basic` and `AlgebraicTopology.Cohomology.GradedCommutativity` (41 modules, 13,252 lines; none overlaps H1) | Alexander-Whitney and Eilenberg-Zilber maps, shuffles, the Koszul braiding on tensor products of complexes, the singular cup product `TopCat.singularCup` with naturality, associativity, units and graded commutativity | ten files edited, one declaration renamed, one supplement lemma; no statement changed (section below) | builds at the pin |

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

## Batch H2: the singular cup product

Source: Tau Ceti commit `7433fc3695f4fbf5a07041090628c5c94067c0b9`, the import closure of
`TauCeti/AlgebraicTopology/Cohomology/Cup/Basic.lean` and
`TauCeti/AlgebraicTopology/Cohomology/GradedCommutativity.lean` (the red team's
`Cup/GradedCommutativity` is at `Cohomology/GradedCommutativity` in the tree). Method as above.
Three files (`Cohomology/Cup/Basic`, `Cohomology/GradedCommutativity`, `SimplicialSet/Shuffle`)
were compared byte for byte with the files served by the GitHub API at that commit: identical.

Files, under `port/LefschetzPort/TauCeti/`:

| Directory | Modules |
|---|---|
| `Algebra/BigOperators/Finset/` | `PartialSum` |
| `Algebra/Homology/` | `Bifunctor/Basic`, `ComplexShape/Signs`, `HomologicalComplex/Basic`, `LinearYoneda`, `ModuleCat/Basic`, `ModuleCat/Bilinear`, `Monoidal/Basic`, `Monoidal/Cup`, `Monoidal/KoszulBraiding`, `Monoidal/Summand`, `Monoidal/Tensor/Cochain`, `Monoidal/Tensor/Differential`, `Monoidal/Tensor/Symmetry` |
| `AlgebraicTopology/Cohomology/` | `Basic`, `Cup/Basic`, `GradedCommutativity` |
| `AlgebraicTopology/SimplexCategory/` | `Subinterval` |
| `AlgebraicTopology/SimplicialObject/` | `AlexanderWhitney` |
| `AlgebraicTopology/SimplicialSet/` | `AlexanderWhitney`, `Cochains/Basic`, `EilenbergZilber`, `Homology/Basic`, `Homology/Pairing`, `KoszulBraiding`, `Shuffle`, `TopAdj` |
| `AlgebraicTopology/Singular/` | `AlexanderWhitney/Basic`, `KoszulBraiding`, `Shuffle` |
| `CategoryTheory/` | `Linear/Yoneda`, `Monoidal/Cartesian/Basic`, `Monoidal/Limits`, `Monoidal/Linear`, `Monoidal/Preadditive` |
| `Data/Fin/` | `Basic` |
| `Geometry/Convex/ConvexSpace/` | `Defs`, `PathConnectedSpaceStdSimplex`, `Topology` |
| `LinearAlgebra/` | `End/LocallyNilpotent`, `Graded/LinearMap` |

Supplement: `port/LefschetzPort/Supplement/SimplexCategoryApply.lean` holds
`LefschetzPort.SimplexCategory.δ_apply : SimplexCategory.δ i j = Fin.succAbove i j` (`rfl`), copied
from Mathlib `31ce06e` (`Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean`, section
`Concrete`), in the `LefschetzPort` namespace so that it does not clash with Mathlib's name after a
pin bump.

Edits at the pin (31 files are copied unchanged apart from imports and the provenance line):

| File | Edit | Why |
|---|---|---|
| `Algebra/BigOperators/Finset/PartialSum.lean` | `eq_zero_of_forall_sum_Iic_eq_zero`: the proof first builds `WellFoundedLT ι` from the strictly growing cardinalities of `Iio k` | the pin has no instance `LocallyFiniteOrderBot ι → WellFoundedLT ι` for a partial order |
| `Algebra/Homology/Bifunctor/Basic.lean` | plain `import Mathlib.CategoryTheory.Preadditive.FunctorCategory` | `NatTrans.app_zero` lives there at the pin |
| `Algebra/Homology/HomologicalComplex/Basic.lean` | instance `hasCoproducts`: `.mk fun _ ↦ inferInstance` becomes `fun _ ↦ inferInstance` | `HasCoproducts` is not a structure at the pin |
| `Algebra/Homology/Monoidal/Summand.lean` | `leftUnitor_inv_f`, `rightUnitor_inv_f`: `rfl` after the `simp` call; two em dashes in the module docstring replaced by parentheses | at the pin `simp` leaves a goal that holds by `rfl` |
| `Algebra/Homology/Monoidal/Tensor/Symmetry.lean` | `braidingBicomplexIso`: each differential compatibility closes with `exact (BraidedCategory.braiding_(inv_)naturality_{left,right} _ _).symm` after `simp`, the two inverse laws with `exact Iso.hom_inv_id _` / `Iso.inv_hom_id _`; `ιTensorObj_tensorBraiding_inv_f`: three rewrites (`ιTotal_map`, `Category.assoc`, `ι_mapBifunctorFlipIso_hom`, `Linear.comp_units_smul`) use `erw` | the pin's `simp` set orients the braiding naturality the other way and does not see the tensor through `mapBifunctorHomologicalComplex`; the summand inclusion is not syntactically `ιTotal` |
| `AlgebraicTopology/SimplexCategory/Subinterval.lean` | `δ_apply` becomes `LefschetzPort.SimplexCategory.δ_apply` (three lemmas), with the supplement imported | Mathlib's `SimplexCategory.δ_apply` postdates the pin |
| `AlgebraicTopology/SimplicialSet/TopAdj.lean` | `ContinuousMap.coe_ofClass` becomes `ContinuousMap.coe_coe` (four rewrites) | renamed in Mathlib after the pin (`coe_coe` is its deprecated alias there) |
| `Geometry/Convex/ConvexSpace/Defs.lean` | `Convexity.StdSimplex.weights_map_apply` renamed `Convexity.StdSimplex.weights_map_apply_eq_sum`, with a note in its docstring; statement unchanged, no vendored file uses it | the upstream statement library declares `Convexity.StdSimplex.weights_map_apply` (the case `R = ℝ`, in `HodgeConjecture.Mathlib.Geometry.Convex.StdSimplex`); the build of `LefschetzPort` failed on the duplicate name |
| `Data/Fin/Basic.lean` | `Finset.insert_Iio` becomes `Finset.Iio_insert`; in `exists_foldl_eq_of_parent` the `Nat.strong_induction_on` case is named `h` instead of `ind`; two em dashes in the module docstring replaced by parentheses | name and case-name differences at the pin |
| `LinearAlgebra/End/LocallyNilpotent.lean` | `mul_apply_eq_comp` and `one_apply_eq_self` (twelve uses) become `Module.End.mul_apply` and `Module.End.one_apply` | the pin has no `IsMulApplyEqComp` or `IsOneApplyEqSelf` instance for `Module.End` |

One warning remains: `TopAdj.lean` uses `SSet.stdSimplex.yonedaEquiv_map`, deprecated at the pin in
favor of `SSet.yonedaEquiv_map`; left as in the source.

Checks at the pin:

| Check | Result |
|---|---|
| `lake build LefschetzPort.TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity LefschetzPort.TauCeti.AlgebraicTopology.Cohomology.Cup.Basic` | success |
| `initialize`, `run_cmd`, `IO`, `extern`, `implemented_by`, `unsafe`, `native_decide`, `sorry`, `axiom` in the 41 files | none |
| `#print axioms` on `TopCat.singularCup`, `TopCat.singularCup_naturality`, `TopCat.singularCup_assoc`, `TopCat.singularCup_assoc_tensorUnit`, `TopCat.singularCup_gradedComm`, `TopCat.singularCup_gradedComm_tensorUnit`, `TopCat.singularCup_self_eq_zero_of_odd` | `propext`, `Classical.choice`, `Quot.sound` |
| `python3 tools/check.py` (build, sorry, axioms, ledger, import clash with Mathlib) | all checks passed, after the rename in `ConvexSpace/Defs.lean` |

The declarations keep Tau Ceti's namespaces (`TopCat.singularCup*` and the rest under `TauCeti`,
`HomologicalComplex`, `SSet`). This batch is the backport that `cup-singular-comparison` (decision
0009, rung 4) and the transfer route of `cup-graded-commutative` (rung 7) need; nothing in the
ledger names these declarations yet.

## Downstream readers of non-exposed bodies

| Reader | Vendored file | What it reads | Consequence on a re-vendor |
|---|---|---|---|
| `HodgeLadder.Relative.CrossChain` (rung `relative-cross-chain`), through a private `import all LefschetzPort.TauCeti.AlgebraicTopology.SimplicialSet.Shuffle` | `port/LefschetzPort/TauCeti/AlgebraicTopology/SimplicialSet/Shuffle.lean` | the bodies of `SSet.stdSimplex.cone` and `SSet.stdSimplex.prodCone` (vertex computations in `shuffleChain_idShuffle_coeff`; the public lemmas give every vertex of `prodCone x` except vertex 0) | rebuild `HodgeLadder.Relative.CrossChain`; a change of these bodies breaks its build and cannot change a statement. The import is not re-exported and adds no axiom or instance |
