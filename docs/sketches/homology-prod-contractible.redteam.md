# Red team: `homology-prod-contractible` (sub-rung of `torus-singular-cohomology`, order 1)

Date: 2026-11-27. Worktree `homology-prod-contractible`, candidate commit `2a41eef` on `track/homology-prod-contractible`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4` (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain` unchanged against `main`). Issue #240.

Target: `HodgeLadder/General/HomologyProdContractible.lean`, namespace `HodgeLadder`: `homotopic_of_contractibleSpace`, `prodFst`, `prodSection`, `prodContractibleHomotopyEquiv`, `homologyProdContractibleIso` with `_hom`, `_inv`, `homologyProdContractibleEquiv` with `_toLinearMap`, `_symm_toLinearMap`, `homologyMap_prodFst_comp_prodSection`, `homologyMap_prodSection_comp_prodFst`, `homologyMap_prodFst_bijective`, `homologyMap_prodSection_bijective`, the rung statement `nonempty_homology_prod_contractible_iso`, the test `finrank_homology_zero_point_prod`. The ledger row is still `open` with no module.

Read: the Lean file; upstream `HodgeConjecture/Definitions/AlgebraicTopology/Singular/Cohomology.lean` (`Homology`, `homologyMap`), `HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Contractible.lean` (`singularChainHomotopyEquivOfHomotopyEquiv`, `contractibleSingularChainHomotopyEquiv`); Mathlib `Topology/Homotopy/Contractible.lean`, `Topology/Homotopy/Product.lean`, `Topology/Category/TopCat/Limits/Products.lean` (`TopCat.prodFst`); the port's `AlgebraicTopology/SingularContractibleMapQuasiIso.lean`; `docs/sketches/torus-singular-cohomology.md` (steps 2 and 5); the sibling modules `HodgeLadder/General/CircleArcs.lean` (`track/circle-arc-cover`, `4cfb2ba`) and `HodgeLadder/General/MayerVietorisRank.lean` (`track/mayer-vietoris-finrank`, `302ef42`); `docs/conventions.md`, `docs/references.md`, `docs/gaps.md`.

Scratch (directory `scratch-rt-hpc-cac/` in this worktree, deleted at the end; the three branches' oleans combined by symlink into one search path):

| File | What | Result |
|---|---|---|
| `Consumer.lean` | the `circle-cylinder-homology` chain on `TopCat.of (Y × UnitAddCircle)`, `Y : TopCat.{0}`: `H_k(univ ×ˢ U₀; ℚ) ≅ H_k(Y; ℚ)` by `Homeomorph.Set.prod`, `TopCat.isoOfHomeo`, `Functor.mapIso` and `homologyProdContractibleIso Y ↥U₀ ℚ _ k`; the same for the overlap pieces `↥P₁ ≃ₜ Y × ↥W₁`, `↥P₂ ≃ₜ Y × ↥W₂`; `dim H_k(U ∩ V) ≤ 2 dim H_k(Y)` closed through `finrank_homology_le_of_disjoint`; `finrank_homology_succ_add_le` applied at the cylinder cover; the section identity `s ≫ subsetIntersectionToLeft X U V ≫ p = 𝟙 Y` by `ext; rfl` | compiles, no `sorry`, about 4 s |
| `Axioms.lean` | `#print axioms` on all thirteen theorems and definitions above; `HodgeLadder.prodFst Y W = TopCat.prodFst (X := Y) (Y := TopCat.of W)` by `rfl`; `prodFst Y W` under `open TopCat`; `Nontrivial (Homology ℚ (TopCat.of (PUnit × W)) 0)` from the test; `homologyProdContractibleIso` at `Y : TopCat.{u}`, `W R : Type u` | `[propext, Classical.choice, Quot.sound]` each; the `rfl` holds; `open TopCat` resolves by arity; the rest elaborates |
| `Owed.lean` | `homologyIsoOfHomeomorph` with its `_hom` lemma (`rfl`), and `homotopic_of_contractibleSpace` with `{X : Type*} {W : Type*}` | compile with the three standard axioms (recommended changes R1, R2) |

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`. The checker names no declaration of this rung yet (ledger row `open`), so the axioms above come from the scratch `#print axioms`. `lake env lean` on the module: about 3 s.

**Verdict: pass with changes.** The rung states homotopy invariance of singular homology for the projection off a contractible factor, with the forward map and its inverse identified by `rfl` as `homologyMap` of the projection and of the section. No sign or scalar enters. The isomorphism composes with `circle-arc-cover` and `mayer-vietoris-finrank` into the overlap bound of `circle-cylinder-homology` (closed in scratch). The required changes are the ledger entry, the gaps row and a conventions row.

## Findings

1. **Literature.** Homotopy invariance: a homotopy equivalence f induces isomorphisms f_* on singular homology (`Hatcher2002` §2.1, Corollary 2.11; locator recalled, unverified; the key's row in `docs/references.md` lists §2.2 and §3 only, change R4). For contractible W and w₀ ∈ W, pr₁ : Y × W → Y is a homotopy equivalence with inverse y ↦ (y, w₀). Field by field: H_k(-; R) is upstream's `Homology R X k`, homology of Mathlib's unnormalized singular chain complex with coefficients `ModuleCat.of R R`; the induced map is upstream's `homologyMap R k`; the chain homotopy equivalence is upstream's `singularChainHomotopyEquivOfHomotopyEquiv R e`, whose `hom` and `inv` are `F.map` of `e.toFun` and `e.invFun`; `prodContractibleHomotopyEquiv` has `toFun = pr₁`, `invFun = (·, w₀)`. Hence `homologyProdContractibleIso_hom` and `_inv` hold by `rfl`, checked. Match.

2. **Hypotheses.** `[ContractibleSpace W]` is satisfiable: any convex nonempty subset of ℝ, `PUnit`, and the arcs of `circle-arc-cover` (`ContractibleSpace ↥U₀`, `↥W₁` found by instance in `Consumer.lean`). `Y` is arbitrary.

3. **Trivial truth.** Tried and failed. The conclusion is `Nonempty` of an isomorphism in `ModuleCat ℚ`; it is false for non-contractible W in general (W = two points doubles H_0), and the hypothesis is used: `homologyMap_prodSection_comp_prodFst` needs the homotopy from `homotopic_of_contractibleSpace`, and `homologyMap_prodFst_bijective` uses the `Nonempty W` that `ContractibleSpace` supplies. A `Subsingleton` shortcut is excluded in degree 0 by the test (`Nontrivial` of `H_0(pt × W)` compiles). No `ℕ∞`, no definition that unfolds to `True`.

4. **Interface rung.** Not applicable; no structure.

5. **Checker.** Run above. The ledger row must list the declarations of change A for the checker to read their axioms.

6. **Conventions.** No sign: the isomorphism is `homologyMap` of continuous maps, and `Homology` uses Mathlib's singular complex with its standard face-map differential; no orientation and no scalar appears. Truth of the rung (a `Nonempty` iso) is insensitive to any sign or nonzero scalar; the `rfl` identifications are exact. `docs/conventions.md` has no row for homotopy invariance or the product with a contractible factor; change C adds one so `circle-cylinder-homology` and later rungs can cite which map is the forward one (the projection) and which the inverse (the section at the chosen w₀).

7. **Equality first.** The rung is an isomorphism with explicit maps and two exact composition laws; no scalar. It is a step toward `circle-cylinder-homology` (ledger row present, depends on this rung) and through `torus-homology-bound` toward the dimension equalities of `torus-singular-cohomology`.

7b. **Non-vacuity.** `finrank_homology_zero_point_prod` (dim H_0(pt × W; ℚ) = 1) is the smallest test that fails if the iso were between zero modules; it exists and reads the rung's own `homologyProdContractibleEquiv`. A positive-degree test needs a space with known nonzero H_k for k ≥ 1, which the ladder does not have yet (the torus rungs produce it); none is owed here.

8. **Composition with the consumers.** `circle-cylinder-homology` reaches this rung through a homeomorphism: `finrank_homology_succ_add_le` is stated on `Homology ℚ (TopCat.of ↥U) _` with `U : Set (TopCat.of (Y × UnitAddCircle))`, and this rung on `TopCat.of (Y × W)`. The bridge for U is `(Homeomorph.Set.prod Set.univ U₀).trans ((Homeomorph.Set.univ Y).prodCongr (Homeomorph.refl _))`; for the overlap pieces a hand-built `↥P₁ ≃ₜ Y × ↥W₁` (eight lines). Each is pushed to homology by `((singularHomologyFunctor (ModuleCat.{0} ℚ) k).obj (ModuleCat.of ℚ ℚ)).mapIso (TopCat.isoOfHomeo e)`, which typechecks against `Homology` because `Homology` is an `abbrev`. That step is used four times; no lemma for it exists in upstream or the ladder at the pin, so R1 adds `homologyIsoOfHomeomorph`. Universes: `nonempty_homology_prod_contractible_iso` fixes `TopCat.{0}` and `W : Type`, the general definitions take `Y : TopCat.{u}`, `W R : Type u`; the consumer instantiates `u = 0` with `R = ℚ`. Compatible.

9. **Mathlib and upstream equivalents.** Mathlib at the pin has no homology of a product and no lemma "any two maps into a contractible space are homotopic"; it has `id_nullhomotopic`, `ContinuousMap.Nullhomotopic.comp_left` and `ContractibleSpace.hequiv`. The port's `AlgebraicTopology.homotopyEquivOfMapBetweenContractibleSpaces` (both spaces contractible) is the nearest relative. Upstream has `contractibleSingularChainHomotopyEquiv` (to a point, no product). `HodgeLadder.prodFst Y W` is definitionally Mathlib's `TopCat.prodFst (X := Y) (Y := TopCat.of W)` (`rfl`, `Axioms.lean`); under `open TopCat` the bare name resolves by arity, so it is a pin-walk clash candidate and no error today.

10. **Placement.** `HodgeLadder/General/`, layer 0 (`python3 tools/pinwalk.py --hubs`: downstream 0, layer 0). Gaps category: "Singular homology, cohomology and simplicial cochains", first row by layer (the current first row, `HodgeLadder.Local.RealAffineOrientation`, has layer 1). The category's diff list names upstream `{Definitions,Lemmas}/AlgebraicTopology/{Singular,…}/`, which covers `Lemmas/AlgebraicTopology/Singular/Contractible.lean`, and lacks the Mathlib homotopy files this module reads. Root import present.

11. **Pin drift.** Written and checked at the current pin; nothing to diff. Drift targets at a bump: upstream `singularChainHomotopyEquivOfHomotopyEquiv` (its `hom` and `inv` fields; a change breaks the `rfl` of `_hom` and `_inv` at build), upstream `Homology` and `homologyMap`, Mathlib `HomotopyEquiv.toHomologyIso`, `ContinuousMap.Homotopic.prodMk` (`Topology/Homotopy/Basic.lean`), reached through the import `Mathlib.Topology.Homotopy.Product`.

12. **Minor.** `homotopic_of_contractibleSpace` takes `{X W : Type u}` in one universe; the proof works with `{X : Type*} {W : Type*}` (`Owed.lean`), which is what a general lemma should say.

## Required changes

A. `ledger/ladder.json`, rung `homology-prod-contractible`: set `status` to `checked`, `module` to `HodgeLadder.General.HomologyProdContractible`, `contributors` to `["claude-code"]`, and

```json
"declarations": [
  "HodgeLadder.homotopic_of_contractibleSpace",
  "HodgeLadder.prodFst",
  "HodgeLadder.prodSection",
  "HodgeLadder.prodContractibleHomotopyEquiv",
  "HodgeLadder.homologyProdContractibleIso",
  "HodgeLadder.homologyProdContractibleIso_hom",
  "HodgeLadder.homologyProdContractibleIso_inv",
  "HodgeLadder.homologyProdContractibleEquiv",
  "HodgeLadder.homologyProdContractibleEquiv_toLinearMap",
  "HodgeLadder.homologyProdContractibleEquiv_symm_toLinearMap",
  "HodgeLadder.homologyMap_prodFst_comp_prodSection",
  "HodgeLadder.homologyMap_prodSection_comp_prodFst",
  "HodgeLadder.homologyMap_prodFst_bijective",
  "HodgeLadder.homologyMap_prodSection_bijective",
  "HodgeLadder.nonempty_homology_prod_contractible_iso",
  "HodgeLadder.finrank_homology_zero_point_prod"
],
"note": "Checked 2026-11-27. Sketch: docs/sketches/torus-singular-cohomology.md (order 1, step 2). For W contractible and w₀ : W, nonempty_homology_prod_contractible_iso: Nonempty (Homology ℚ (TopCat.of (Y × W)) k ≅ Homology ℚ Y k), Y : TopCat.{0}; the explicit iso homologyProdContractibleIso Y W R w₀ k (any commutative R, any universe u) is HomotopyEquiv.toHomologyIso of upstream's singularChainHomotopyEquivOfHomotopyEquiv on prodContractibleHomotopyEquiv (pr₁ with inverse y ↦ (y, w₀)); its hom is homologyMap R k (prodFst Y W) and its inv homologyMap R k (prodSection Y W w₀), both rfl. Composition laws: pr₁ ∘ section = id with no contractibility; section ∘ pr₁ = id for contractible W. Exact, no sign. Nonvacuity: finrank_homology_zero_point_prod, dim H_0(pt × W; ℚ) = 1. With circle-arc-cover and mayer-vietoris-finrank the overlap bound of circle-cylinder-homology was closed in red-team scratch, through Homeomorph.Set.prod and TopCat.isoOfHomeo. Red team: docs/sketches/homology-prod-contractible.redteam.md, pass with changes. General, kept local (decision 0011); about 3 s to elaborate."
```

B. `docs/gaps.md`, category "Singular homology, cohomology and simplicial cochains": append to the "Diff at a bump" line, after `Topology/Category/TopPair.lean (…)`, the text `, Topology/Homotopy/Basic.lean, Topology/Homotopy/Contractible.lean, Topology/Homotopy/Equiv.lean, Topology/Homotopy/Product.lean` (each in backticks, as the existing entries), and add this row as the first row of the table (layer 0):

```
| `HodgeLadder.homotopic_of_contractibleSpace` (any two maps into a contractible space are homotopic), `prodFst` (definitionally Mathlib's `TopCat.prodFst` at `TopCat.of W`; resolves by arity under `open TopCat`), `prodSection`, `prodContractibleHomotopyEquiv` (Y × W ≃ₕ Y for contractible W), `homologyProdContractibleIso`, `homologyProdContractibleEquiv` with `_hom`, `_inv`, `_toLinearMap`, `_symm_toLinearMap`, `homologyMap_prodFst_comp_prodSection`, `homologyMap_prodSection_comp_prodFst`, `homologyMap_prodFst_bijective`, `homologyMap_prodSection_bijective`, `nonempty_homology_prod_contractible_iso`, `finrank_homology_zero_point_prod` | `HodgeLadder.General.HomologyProdContractible` | 0 | homotopy invariance on upstream's `Homology` for a contractible factor; Mathlib at the pin has `id_nullhomotopic` and no homotopy lemma for maps into a contractible space, and neither Mathlib nor upstream has homology of a product; the port's `homotopyEquivOfMapBetweenContractibleSpaces` needs both spaces contractible; rung `homology-prod-contractible`, for `circle-cylinder-homology` | 2026-11-27 |
```

C. `docs/conventions.md`, register table: add this row after the row "Singular coboundary".

```
| Homology of a product with a contractible factor | upstream `singularChainHomotopyEquivOfHomotopyEquiv`, `Homology`, `homologyMap`; this repository, `HodgeLadder.homologyProdContractibleIso` (rung `homology-prod-contractible`) | forward map `homologyMap R k (prodFst Y W)` (the projection), inverse `homologyMap R k (prodSection Y W w₀)` (y ↦ (y, w₀)), both by `rfl`; no sign, no scalar; the inverse does not depend on w₀ (all sections are homotopic), the statement still names it | none for spans, dimensions or the rung's `Nonempty` form; an identity that reads a class on Y × W through this iso must use the projection as the forward map | checked (red team 2026-11-27, `docs/sketches/homology-prod-contractible.redteam.md`) |
```

## Recommended changes (optional)

R1. Add to this module (or to `circle-cylinder-homology`) the homology isomorphism of a homeomorphism, which the consumer needs four times; compiled in scratch with the three standard axioms:

```lean
/-- A homeomorphism `A ≃ₜ B` induces `H_k(A; R) ≅ H_k(B; R)`, with forward map
`homologyMap R k` of the homeomorphism. -/
noncomputable def homologyIsoOfHomeomorph {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (k : ℕ) : Homology R (TopCat.of A) k ≅ Homology R (TopCat.of B) k :=
  ((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).mapIso
    (TopCat.isoOfHomeo e)

theorem homologyIsoOfHomeomorph_hom {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (k : ℕ) :
    (homologyIsoOfHomeomorph R e k).hom.hom = homologyMap R k (TopCat.ofHom (e : C(A, B))) :=
  rfl
```

R2. Generalize `homotopic_of_contractibleSpace` to `{X : Type*} {W : Type*}`; the proof is unchanged.

R3. Docstring of `prodFst`: add "Definitionally `TopCat.prodFst (X := Y) (Y := TopCat.of W)`."

R4. `docs/references.md`, row `Hatcher2002`: add "homotopy invariance of singular homology (§2.1, Corollary 2.11) and Mayer–Vietoris (§2.2) (recalled, unverified numbering)".

## Attempts that failed

- Inside a tactic block, `have e2 := (… .mapIso (TopCat.isoOfHomeo (bridgeP₂ Y)) ≪≫ homologyProdContractibleIso …).toLinearEquiv` fails: the source object is a metavariable when `isoOfHomeo` elaborates, and `↑Y × ↑W₂` is not unified with `↑↧(↑Y × ↑W₂)`. A top-level definition with the target type written out works. R1 removes the friction.
- A ten-line proof of the rung statement that avoids homotopy: none. Without contractibility the inverse composite is false in general (W = two points), so the hypothesis carries the content.
