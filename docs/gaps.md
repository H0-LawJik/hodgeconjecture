# Acknowledged gaps

A rolling registry. Add an entry when a shortcut is taken or a thread is dropped; close it in the same file with the date and the commit that closed it.

## To upstream to Mathlib

| Local declaration | Module | Why local | Opened |
|---|---|---|---|
| `codimCycles_one` (codimension one equals Mathlib `weilDivisors`), `codimCycles_inf_eq_bot` (distinct codimensions meet in zero) | removed from this repository (decision 0003); recoverable from git history at `ba3dbef` | Upstream `codimensionCycleSubgroup` lacks these two facts; offer them to `Paul-Lez/HodgeConjecture` as lemmas on its subgroup | 2026-11-24 |
| Regular local rings are UFDs (Auslander–Buchsbaum); planned for `prime-divisors-cartier`, not used: `local-factoriality` descends factoriality from the analytic stalks | not yet written | Mathlib has `IsRegularLocalRing`; factoriality is missing there and is general commutative algebra | 2026-11-24 |
| `lcSheaf`, `constIsoLC` (the constant sheaf ℤ is the sheaf of locally constant functions), `Frames.isoOfSameTransitions` (line bundles with equal transitions are isomorphic) | `HodgeLadder.Line.LocallyConstant`, `HodgeLadder.Line.FrameComparison` | general sheaf theory; written against the upstream statement of the constant sheaf | 2026-11-25 |
| `Acyclic.subsingleton_H_of_isFlasque` (flasque sheaves are acyclic), `Acyclic.subsingleton_H_cycles` (cycle sheaves of a flasque resolution with exact global sections are acyclic), `Acyclic.subsingleton_H_const_of_contractible` | `HodgeLadder.Tests.ContractibleAcyclic` | general sheaf theory; upstream's `FlasqueAcyclic.lean` carries the docstring of the first and no theorem at the pin | 2026-11-25 |
| Exactness of `sheafCompose (forget₂ (ModuleCat ℚ) AddCommGrpCat)` and of sheafified `ℚ ⊗ −`; `Ext` transport along isomorphisms (`extPrecompEquiv`, `extPostcompEquiv`); `Hⁿ(Y; ℚ) ≃+ Extⁿ(ℚ_Y, ℚ_Y)` | `HodgeLadder.Cup.SheafExact` | general sheaf theory, not in Mathlib at the pin | 2026-11-25 |
| Exactness and colimit preservation of `tensorLeft F`, `tensorRight F` for `Sheaf.monoidalCategory` on sheaves of vector spaces over a field (`tensor_exact`, via `tensorLeftIso`); `preservesColimitsOfShape_of_sheafify` (a functor on sheaves preserves colimits once its composite with sheafification does); the unit is the constant sheaf (`unitIsoQX`) | `HodgeLadder.Cup.SheafTensor` | general sheaf theory, not in Mathlib at the pin; the proof uses flatness of every ℚ-vector space and exactness of sheafification; a general version over any site and field is expected (unverified) | 2026-11-25 |
| `toSmallShiftedHom_postcomp`, `toSmallShiftedHom_precomp`, `toSmallShiftedHom_cocycleComp` (the derived-category class of a Hom-complex cocycle is compatible with composition by chain maps and with composition of cocycles) | `HodgeLadder.Cup.CocycleClass` | general facts about Mathlib's Hom complex, needed for `step2-cocycle-class`; they belong next to `equiv_toSmallShiftedHom_mk` | 2026-11-25 |
| `homologyπ_mapHomologyIso_hom` (`mapHomologyIso` on classes: `homologyπ ≫ (S.mapHomologyIso F).hom = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ`) | `HodgeLadder.Cup.TopOpenCup` | general short-complex fact, needed for `cup-top-open`; belongs next to `mapHomologyIso_hom_naturality` | 2026-11-25 |

## Known weaknesses

| Gap | Impact | Opened |
|---|---|---|
| `cup-product` is checked for associativity, unit and biadditivity, which the square-zero product also satisfies; the ℙ¹ test uses only the unit law | a positive-degree product could be zero unnoticed; `cup-positive-degree-test` closes it | 2026-11-25 |
| Three Lean pins in play: upstream v4.35.0-rc4 (followed here), the Lefschetz stack v4.33.1, Tau Ceti v4.37.0-rc1 (Mathlib master) | Reuse of Tau Ceti material needs a backport or a wait | 2026-11-24 |
| Tau Ceti Hodge-structure files (batch H1) and the singular cup-product closure (batch H2, 41 modules) are vendored under `port/LefschetzPort/TauCeti/` (`docs/port-tauceti.md`); they belong upstream in Mathlib or stay in Tau Ceti. `LefschetzPort.SimplexCategory.δ_apply` (`port/LefschetzPort/Supplement/SimplexCategoryApply.lean`) copies a Mathlib lemma that postdates the pin | Drop the copies when the pin reaches a Mathlib or Tau Ceti that provides them | 2026-11-25 |
| Building this repository compiles upstream's statement import closure; CI time grows | Watch CI duration | 2026-11-24 |
| The port's global data instances on Mathlib's `Sheaf` (`port/LefschetzPort/CategoryTheory/Sites/Forget.lean`: `Sheaf.homFunLike`, `Sheaf.concreteCategory`, `Sheaf.hasForget₂`) could clash with a future Mathlib (red team L7). They are load-bearing: `holomorphicAdditiveSheaf` uses `forget₂` on sheaves. No clash at the pin; the checker's import-clash step (decision 0006) catches one on the change that introduces it | Handle at the next pin bump if the step fails | 2026-11-24 |
| Upstream's docstring for `HodgeConjectureForAbelianVarietiesInDimensionLE` (`HodgeConjecture/Variants.lean`, and the module docstring) calls the case n ≤ 5 a theorem. For Weil classes of discriminant other than 1 on abelian fourfolds, and so for dimension 5, that rests on [Markman2025], an unrefereed preprint (latest arXiv version v2, 2025-06-08) whose proof passes through Weil classes on sixfolds. Only the discriminant-1 route [Markman2023] is refereed. Red-team item | Any rung or public copy that cites the upstream docstring for n = 4 or 5 says "preprint"; offer a docstring note upstream | 2026-11-25 |

## Process items to investigate

| Item | Why | Opened |
|---|---|---|
| How the 2026-11-20 RH Lean proof was certified against its statement (statement-comparison tool, what it checks) | Adopt for `lefschetz-1-1` and the port; `docs/notes/2026-11-24-spinors-characters-tests.md` §4 | 2026-11-24 |
| Candidate front `fermat` (character sieve on Fermat varieties) | Needs a decision record and a first rung; research note §2 | 2026-11-24 |

## Dead ends

| Thread | Why it died | Date |
|---|---|---|
| Interface-first statement (`hodge-interface`, `statement-interface` and the cases built on it) | Interface statements of this conjecture are vacuous or false (LeanDojo regression tests); real definitions exist upstream (decision 0003) | 2026-11-24 |
| Own foundations for stating the conjecture (`de-rham`, `complex-analytic-space`, `hodge-decomposition`, `cycle-class`) | Upstream already defines them on real objects (decision 0003) | 2026-11-24 |
| Port duplicate of `CategoryTheory.Sheaf.H.δ` (red team M1) | Removed; `holomorphicFirstChernClass` uses Mathlib's `Sheaf.H.δ hS 1 2 rfl`, same body | 2026-11-24 |
| Staged modules `ChernWindingRawBoundary`, `HolomorphicExponentialSupportWinding` (red team L3) | No counterpart at the verified head and no importer; deleted | 2026-11-24 |
| `support-cone-right-mult`, `support-named-class` | right multiplication does not act on upstream's support cone, whose target is a chosen injective resolution of the complement; replaced by the supported-sections route | 2026-11-25 |

## Dropped threads

None yet.
