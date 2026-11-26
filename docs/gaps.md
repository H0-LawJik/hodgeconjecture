# Acknowledged gaps

A rolling registry. Add an entry when a shortcut is taken or a thread is dropped; close it in the same file with the date and the commit that closed it.

## General lemmas kept local

Decision 0011: these stay in this repository. A pin bump checks each row for a name clash or a new equivalent in Mathlib or upstream.

| Local declaration | Module | Why local | Opened |
|---|---|---|---|
| `cocycle_precomp_precomp`, `cocycle_postcomp_postcomp`, `fromSingleEquiv_ofHom_comp`, `fromSingleEquiv_comp_ofHom`, `fromSingleEquiv_cocycle_precomp_single` (Hom-complex cocycles, any preadditive category); `HodgeLadder.Cup.cocycle_precomp_precomp` and `HodgeLadder.Cup.fromSingleEquiv_precomp_single` now derive from them | `HodgeLadder.General.HomComplex` | general facts about Mathlib's Hom complex; Mathlib master (v4.37.0-rc1) adds `Cocycle.comp`, not these | 2026-11-26 |
| `toSmallShiftedHom_postcomp`, `toSmallShiftedHom_precomp`, `cocycleComp`, `equivHomShift_symm_cocycleComp`, `toSmallShiftedHom_cocycleComp` (the derived-category class of a Hom-complex cocycle is compatible with composition by chain maps and with composition of cocycles; any abelian category) | `HodgeLadder.Cup.CocycleClass` | already stated in full generality; at a pin with Mathlib's `Cocycle.comp`, replace `cocycleComp` by it | 2026-11-25 |
| `homologyπ_comp_mapHomologyIso_hom` (`mapHomologyIso` on classes), `cyclesMap_cyclesMk`, `homologyMap_homologyπ_cyclesMk` (any concrete abelian category, any complex shape), `mapHomologyIso_hom_comp_map_shiftIso_inv_app` (any shift, categories with homology); `HodgeLadder.Cup.homologyπ_mapHomologyIso_hom`, `HodgeLadder.Cup.homologyMap_cyclesMk` and `HodgeLadder.Cup.mapHomologyIso_shiftIso` (shift `1`) now derive from them | `HodgeLadder.General.Homology` | general homology facts, not in Mathlib at the pin; the port's `CategoryTheory.ShortComplex.homologyπ_mapHomologyIso_hom` is the abelian case of the first | 2026-11-25 |
| `precompIsoAddEquiv`, `postcompIsoAddEquiv` (`Ext` transport along isomorphisms, any universe); `HodgeLadder.Cup.extPrecompEquiv` and `extPostcompEquiv` (universe `0`) are now defined by them. Upstream's `Abelian.Ext.precompAddEquiv` is the same map for sheaf categories | `HodgeLadder.General.Ext` | not in Mathlib at the pin | 2026-11-25 |
| `locallyConstantPresheaf`, `locallyConstantSheaf`, `constantSheafIsoLocallyConstantSheaf` (the constant sheaf with value an abelian group `A` is `U ↦ LocallyConstant U A`; no topology on `A`), with the evaluation lemmas; `lcSheaf`, `constIsoLC` (the case `A = ℤ` with continuous functions) are compared with it by `constIsoLC_trans_lcSheafIso` | `HodgeLadder.General.LocallyConstantSheaf`, `HodgeLadder.Line.LocallyConstant` | general sheaf theory, not in Mathlib at the pin | 2026-11-25 |
| `freeAbelianSheafTerminalIso_hom_generator` (upstream's `ℤ[T] ≅ ULift ℤ` sends `[𝟙 T]` to `1`, any site with a terminal object), `toSheafify_app_sheafifyMap_app`; `HodgeLadder.Cup.terminalIso_generator` now derives from it. `HodgeLadder.Cup.integerConstantHomAddEquivGlobalSections_apply` stays in `HodgeLadder.Cup.ConstantGenerator`: it is about upstream's topological definition | `HodgeLadder.General.FreeAbelianTerminal` | upstream lemmas on upstream's definitions | 2026-11-26 |
| `irreducibleSpace_of_cover` (a space with an irreducible open `U` and a cover by irreducible sets, each meeting `U`, is irreducible; any topological space) | `HodgeLadder.Tests.ProjectivePlane` | general topology, not in Mathlib at the pin in this form; the ℙ¹ file's `irreducibleSpace_of_two` is the two-set case | 2026-11-26 |
| `codimensionCycleSubgroup_one` (codimension one equals Mathlib's `weilDivisors`), `codimensionCycleSubgroup_inf_eq_bot`, `disjoint_codimensionCycleSubgroup`, restated for upstream's `codimensionCycleSubgroup` from `codimCycles_one`, `codimCycles_inf_eq_bot` (git history at `ba3dbef`) | `HodgeLadder.General.Codimension` | upstream's subgroup lacks these two facts | 2026-11-24 |
| `map_shiftedLiftShortComplex`, `map_shortExactHomologyIsoCone` (an exact functor commutes with upstream's `shortExactHomologyIsoCone`; any abelian categories), `mapArrowHom_eq_map` | `HodgeLadder.Cup.ConeMaps` | already general; the first has the same name as a lemma in upstream's open stack (PR #221), so check it at the next pin bump | 2026-11-25 |
| `mapExtendCanonicalIso_inv_f`, `extend_d_zero_iff` | `HodgeLadder.Cup.SupportedRelCup` | component lemmas for upstream's `mapExtendCanonicalIso` and for `extend`; the first is also in upstream's open PR #222, so check it at the next pin bump | 2026-11-25 |
| `Frames.isoOfSameTransitions` (line bundles with equal transitions are isomorphic) | `HodgeLadder.Line.FrameComparison` | stated for the port's `holomorphicRingSheaf`; a general form needs a notion of generating sections | 2026-11-25 |
| `Acyclic.subsingleton_H_cycles` (cycle sheaves of a flasque resolution with exact global sections are acyclic), `Acyclic.subsingleton_H_const_of_contractible` | `HodgeLadder.Tests.ContractibleAcyclic` | general sheaf theory. Upstream's `cycles_isFlasque_of_exact_le` does not cover the first: here `Z⁰` is the resolved sheaf, which need not be flasque, and the exactness of global sections carries the induction | 2026-11-25 |
| `Acyclic.subsingleton_H_of_isFlasque` (flasque sheaves are acyclic) | `HodgeLadder.Tests.ContractibleAcyclic` | **closed 2026-11-26**: now a restatement of upstream's `TopCat.Sheaf.IsFlasque.subsingleton_cohomology_succ` (`Other/AlgebraicTopology/Sheaf/FlasqueGlobalSections.lean`), kept for the ledger | 2026-11-25 |
| Exactness of `sheafCompose (forget₂ (ModuleCat ℚ) AddCommGrpCat)` and of sheafified `ℚ ⊗ −`; `Hⁿ(Y; ℚ) ≃+ Extⁿ(ℚ_Y, ℚ_Y)` | `HodgeLadder.Cup.SheafExact` | general sheaf theory, not in Mathlib at the pin; stated for `ℚ` on a topological space | 2026-11-25 |
| Exactness and colimit preservation of `tensorLeft F`, `tensorRight F` for `Sheaf.monoidalCategory` on sheaves of vector spaces over a field (`tensor_exact`, via `tensorLeftIso`); `preservesColimitsOfShape_of_sheafify`; the unit is the constant sheaf (`unitIsoQX`) | `HodgeLadder.Cup.SheafTensor` | general sheaf theory, not in Mathlib at the pin; the proof uses flatness of every ℚ-vector space and exactness of sheafification; a general version over any site and field is expected (unverified) | 2026-11-25 |
| Regular local rings are UFDs (Auslander–Buchsbaum); planned for `prime-divisors-cartier`, not used: `local-factoriality` descends factoriality from the analytic stalks | not yet written | Mathlib has `IsRegularLocalRing`; factoriality is missing there and is general commutative algebra | 2026-11-24 |

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
| `supported-sections-right-mult` | off the route used: the supported comparison works with evaluation at the generator and needs no map of supported-section complexes | 2026-11-26 |

## Dropped threads

None yet.
