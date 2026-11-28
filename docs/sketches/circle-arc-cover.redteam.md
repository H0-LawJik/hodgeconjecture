# Red team: `circle-arc-cover` (sub-rung of `torus-singular-cohomology`, order 1)

Date: 2026-11-27. Worktree `circle-arc-cover`, candidate commit `4cfb2ba` on `track/circle-arc-cover`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4` (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain` unchanged against `main`). Issue #239.

Target: `HodgeLadder/General/CircleArcs.lean`, namespace `HodgeLadder.CircleArcs`: `U₀`, `V₀`, `W₁`, `W₂`, `coe_eq_coe_iff_of_mem_Ico`, `coe_mem_image_iff`, `isOpen_U₀`, `isOpen_V₀`, `U₀_union_V₀`, `contractibleSpace_compl_singleton`, the instances `contractibleSpace_U₀`, `contractibleSpace_V₀`, `contractibleSpace_W₁`, `contractibleSpace_W₂`, `U₀_inter_V₀`, `isOpen_W₁`, `isOpen_W₂`, `disjoint_W₁_W₂`, `W₁HomeomorphIoo`, `W₂HomeomorphIoo`, `quarter_mem_W₁`, `threeQuarter_mem_W₂`, `quarter_mem_U₀_inter_V₀`, `circle_arc_cover`. The ledger row is still `open` with no module.

Read: the Lean file; `docs/sketches/torus-singular-cohomology.md` (steps 1, 4, 5 and the sub-rung table); the sibling `HodgeLadder/General/MayerVietorisRank.lean` on `track/mayer-vietoris-finrank` (`302ef42`) and `HodgeLadder/General/HomologyProdContractible.lean` on `track/homology-prod-contractible` (`2a41eef`); Mathlib `Topology/Instances/AddCircle/Defs.lean` (`coe_eq_coe_iff_of_mem_Ico`, `openPartialHomeomorphCoe`), `Topology/Homotopy/Contractible.lean`, `Analysis/SpecialFunctions/Complex/Circle.lean`; `docs/conventions.md`, `docs/references.md`, `docs/gaps.md` (categories "Topology" and "Singular homology, cohomology and simplicial cochains").

Scratch (directory `scratch-rt-hpc-cac/` in the `homology-prod-contractible` worktree, deleted at the end; the three branches' oleans were combined by symlink into one search path so a single file could import all three modules):

| File | What | Result |
|---|---|---|
| `Consumer.lean` | the `circle-cylinder-homology` chain on `X = TopCat.of (Y × UnitAddCircle)`, `Y : TopCat.{0}`, `U = univ ×ˢ U₀`, `V = univ ×ˢ V₀`: openness and cover; `finrank_homology_succ_add_le` applied at these `U`, `V`; the bridge `↥(univ ×ˢ U₀) ≃ₜ Y × ↥U₀` and `H_k(U; ℚ) ≅ H_k(Y; ℚ)`; the section `s : Y ⟶ TopCat.of ↥(U ∩ V)`, `y ↦ (y, ↑(1/4))`, with `s ≫ subsetIntersectionToLeft X U V ≫ p = 𝟙 Y` by `ext; rfl`; the pieces `P₁ = {p | p.1.2 ∈ W₁}`, `P₂ = {p | p.1.2 ∈ W₂}` of `↥(U ∩ V)` as a disjoint open cover, `↥P₁ ≃ₜ Y × ↥W₁`, `↥P₂ ≃ₜ Y × ↥W₂`, and the closed bound `dim H_k(U ∩ V) ≤ 2 dim H_k(Y)` through `finrank_homology_le_of_disjoint` | compiles with no `sorry`; whole file about 4 s |
| `Axioms.lean` | `#print axioms` on `circle_arc_cover`, `contractibleSpace_compl_singleton`, `W₁HomeomorphIoo`, `W₂HomeomorphIoo`, `quarter_mem_U₀_inter_V₀`, `coe_mem_image_iff`; probes `U₀ ≠ univ`, `W₁ ∪ W₂ ≠ univ`, `ContractibleSpace (↥U₀ × ↥V₀)` by `inferInstance` | `[propext, Classical.choice, Quot.sound]` each; probes compile |
| `Clash.lean` | `coe_eq_coe_iff_of_mem_Ico` under `open AddCircle HodgeLadder.CircleArcs`, once at `Ico 0 1` and once at `Ico 0 (0 + 1)` | both resolve by type; no ambiguity error |

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`. The checker names no declaration of this rung yet (ledger row `open`, `declarations: []`), so the axioms above come from the scratch `#print axioms`.

**Verdict: pass with changes.** The statement is the standard two-arc cover of the circle, every clause is non-vacuous, no sign or scalar enters, and the consumer chain into `circle-cylinder-homology` elaborates and closes its overlap bound against the sibling statements as they stand. The required changes are the ledger entry, the gaps row and a conventions row.

## Findings

1. **Literature.** The cover is the one used for H_*(S¹) by Mayer–Vietoris (`Hatcher2002` §2.2, the circle example; locator recalled, unverified): S¹ = A ∪ B with A, B arcs (each contractible) and A ∩ B two disjoint contractible arcs. Field by field: S¹ is `UnitAddCircle = AddCircle (1 : ℝ) = ℝ/ℤ`; A = `{↑0}ᶜ`, B = `{↑(1/2)}ᶜ`, open (`isOpen_compl_singleton`, T1) and contractible (`contractibleSpace_compl_singleton`, through `openPartialHomeomorphCoe 1 a`, whose source is `Ioo a (a + 1)` and target `{↑a}ᶜ`); A ∩ B = `W₁ ∪ W₂` with `W₁ = ↑(0, 1/2)`, `W₂ = ↑(1/2, 1)`, open (`QuotientAddGroup.isOpenMap_coe`), disjoint, each homeomorphic to an open interval. Match. The extra clauses `↑(1/4) ∈ W₁`, `↑(3/4) ∈ W₂` are the section point the sketch's step 5 needs and the nonemptiness of each arc.

2. **Hypotheses.** The rung has none; every clause is a closed statement about fixed sets. Satisfiability is the truth of the conjunction, checked.

3. **Trivial truth.** Tried and failed to find one. `ContractibleSpace` carries `Nonempty (X ≃ₕ Unit)`, so it forces nonemptiness and the four contractibility clauses cannot hold on empty sets. `U₀ ≠ univ` and `W₁ ∪ W₂ ≠ univ` both compile (`Axioms.lean`), so neither the cover nor the overlap identity is the trivial `univ = univ`. `disjoint_W₁_W₂` together with `quarter_mem_W₁` and `threeQuarter_mem_W₂` shows the overlap has two nonempty pieces, which is the content the Mayer–Vietoris count reads (2 b_j(Y) for the overlap). A wrong arc, for example `W₂ = ↑(1/2, 3/2)`, would break `disjoint_W₁_W₂`; a wrong complement point (`V₀ = {↑1}ᶜ`, equal to `U₀`) would leave the overlap connected and break `U₀_inter_V₀`.

4. **Interface rung.** Not applicable; no structure.

5. **Checker.** Run above. The ledger row must list the declarations below (required change A) for the checker to read their axioms; the scratch `#print axioms` already gives the three standard ones.

6. **Conventions.** No sign. One normalization: the circle is `ℝ/ℤ` with period 1, so the four points are ↑0, ↑(1/2), ↑(1/4), ↑(3/4) in period-1 coordinates. The truth of every clause depends only on these points being pairwise distinct mod 1 and on 1/4 ∈ (0, 1/2), 3/4 ∈ (1/2, 1). The period matters downstream, where `coordChar` is `x ↦ exp(2πi x)` (`AddCircle.toCircle`, period 1); `docs/conventions.md` has no row naming the period of `UnitAddCircle`, so I add one (change C). The arc identity holds for any period up to rescaling the endpoints; nothing in `circle-cylinder-homology` reads an orientation of the arcs.

7. **Equality first.** `U₀ ∪ V₀ = univ` and `U₀ ∩ V₀ = W₁ ∪ W₂` are set equalities, proved exactly. The rung is a step toward `circle-cylinder-homology` (ledger row present, `depends_on` includes this rung), which is itself a step toward the dimension equalities `finrank_cohomology_one_torus` and `finrank_cohomology_two_torus` of `torus-singular-cohomology`.

7b. **Non-vacuity.** The smallest test that fails on a degenerate cover is `disjoint_W₁_W₂` with `quarter_mem_W₁` and `threeQuarter_mem_W₂`: all three exist in the file. No further test is owed.

8. **Composition with the consumers.** Elaborated to closed proofs in `Consumer.lean`:
   - Spelling. `finrank_homology_succ_add_le` is stated on `Homology ℚ (TopCat.of ↥U) (k + 1)` with `U : Set X`, `X = TopCat.of (Y × UnitAddCircle)`; `homologyProdContractibleIso` is stated on `TopCat.of (Y × W)`. The bridge is `(Homeomorph.Set.prod Set.univ U₀).trans ((Homeomorph.Set.univ Y).prodCongr (Homeomorph.refl _)) : ↥(univ ×ˢ U₀) ≃ₜ Y × ↥U₀`, then `((singularHomologyFunctor (ModuleCat.{0} ℚ) k).obj (ModuleCat.of ℚ ℚ)).mapIso (TopCat.isoOfHomeo _)`, then `homologyProdContractibleIso Y ↥U₀ ℚ ⟨_, quarter_mem_U₀_inter_V₀.1⟩ k`. The `ContractibleSpace ↥U₀` instance is found by `contractibleSpace_U₀`.
   - Overlap. `↥(U ∩ V)` is a subtype of the cylinder, not of `Y × (U₀ ∩ V₀)`; the consumer covers it by `P₁`, `P₂` (preimages of `W₁`, `W₂` under the second coordinate), proves cover from `U₀_inter_V₀` and disjointness from `disjoint_W₁_W₂`, and builds `↥P₁ ≃ₜ Y × ↥W₁` by hand (eight lines; `fun_prop` fails on the inverse because of the dependent membership proof, `Continuous.subtype_mk` twice works). No lemma of this rung is missing for that step.
   - Section. `quarter_mem_U₀_inter_V₀` gives the membership proof of `y ↦ (y, ↑(1/4))`; the identity `s ≫ subsetIntersectionToLeft X U V ≫ p = 𝟙 Y` is `ext; rfl`.
   - Owed lemma: a homology isomorphism from a homeomorphism, `homologyIsoOfHomeomorph`, used four times (U, V, P₁, P₂). It is not in upstream or the ladder at the pin; it belongs to `homology-prod-contractible` (recommended change there, Lean text compiled) or to `circle-cylinder-homology`. Nothing here owes it.
   - Universes: every set lives in `UnitAddCircle : Type`, so `TopCat.of ↥U₀ : TopCat.{0}` matches the sibling statements (`X : TopCat.{0}`).

9. **Mathlib and upstream equivalents.** Mathlib at the pin has `Circle.isPathConnected_compl_singleton` (path-connected, on `Circle`) and no `ContractibleSpace` instance or lemma for the circle minus a point; `contractibleSpace_compl_singleton` is new. `HodgeLadder.CircleArcs.coe_eq_coe_iff_of_mem_Ico` is the `a = 0`, `p = 1` case of Mathlib's `AddCircle.coe_eq_coe_iff_of_mem_Ico` and shares its last name component; `Clash.lean` shows overload resolution picks by type under `open AddCircle HodgeLadder.CircleArcs`, so it is a pin-walk clash candidate and no error today. `coe_mem_image_iff` has no Mathlib namesake.

10. **Placement.** `HodgeLadder/General/`, layer 0 (`python3 tools/pinwalk.py --hubs` prints layer 0, downstream 0). Gaps category: "Topology", first row by layer order (the existing first row, `HodgeLadder.Glpos.PathConnected`, is also layer 0; put this one after it). The category's diff list lacks the Mathlib directories this module reads. The root import is present (last line of `HodgeLadder.lean`); `track/mayer-vietoris-finrank` also edits the end of that file from an older base, so expect a one-line merge conflict there.

11. **Pin drift.** Written and checked at the current pin; nothing to diff. Drift targets at a bump: `AddCircle.openPartialHomeomorphCoe` (source and target), `AddCircle.coe_eq_coe_iff_of_mem_Ico`, `AddCircle.eq_coe_Ico`, `Convex.contractibleSpace`; a change to any of them breaks the build of this file.

12. **Minor.** `contractibleSpace_compl_singleton` is stated for `UnitAddCircle` only; the proof works for `AddCircle p` with `0 < p` by replacing `a + 1` with `a + p`. No consumer needs it; optional.

## Required changes

A. `ledger/ladder.json`, rung `circle-arc-cover`: set `status` to `checked`, `module` to `HodgeLadder.General.CircleArcs`, `contributors` to `["claude-code"]`, and

```json
"declarations": [
  "HodgeLadder.CircleArcs.U₀",
  "HodgeLadder.CircleArcs.V₀",
  "HodgeLadder.CircleArcs.W₁",
  "HodgeLadder.CircleArcs.W₂",
  "HodgeLadder.CircleArcs.coe_eq_coe_iff_of_mem_Ico",
  "HodgeLadder.CircleArcs.coe_mem_image_iff",
  "HodgeLadder.CircleArcs.isOpen_U₀",
  "HodgeLadder.CircleArcs.isOpen_V₀",
  "HodgeLadder.CircleArcs.U₀_union_V₀",
  "HodgeLadder.CircleArcs.contractibleSpace_compl_singleton",
  "HodgeLadder.CircleArcs.contractibleSpace_U₀",
  "HodgeLadder.CircleArcs.contractibleSpace_V₀",
  "HodgeLadder.CircleArcs.U₀_inter_V₀",
  "HodgeLadder.CircleArcs.isOpen_W₁",
  "HodgeLadder.CircleArcs.isOpen_W₂",
  "HodgeLadder.CircleArcs.disjoint_W₁_W₂",
  "HodgeLadder.CircleArcs.W₁HomeomorphIoo",
  "HodgeLadder.CircleArcs.W₂HomeomorphIoo",
  "HodgeLadder.CircleArcs.contractibleSpace_W₁",
  "HodgeLadder.CircleArcs.contractibleSpace_W₂",
  "HodgeLadder.CircleArcs.quarter_mem_W₁",
  "HodgeLadder.CircleArcs.threeQuarter_mem_W₂",
  "HodgeLadder.CircleArcs.quarter_mem_U₀_inter_V₀",
  "HodgeLadder.CircleArcs.circle_arc_cover"
],
"note": "Checked 2026-11-27. Sketch: docs/sketches/torus-singular-cohomology.md (order 1, step 1). In UnitAddCircle = ℝ/ℤ: U₀ = {↑0}ᶜ and V₀ = {↑(1/2)}ᶜ are open, cover and are contractible (contractibleSpace_compl_singleton, any point, through AddCircle.openPartialHomeomorphCoe 1 a onto Ioo a (a + 1)); U₀ ∩ V₀ = W₁ ∪ W₂ with W₁ = ↑(0, 1/2), W₂ = ↑(1/2, 1) open, disjoint, homeomorphic to open intervals and contractible; ↑(1/4) ∈ W₁, ↑(3/4) ∈ W₂, ↑(1/4) ∈ U₀ ∩ V₀ (the section point of circle-cylinder-homology). circle_arc_cover bundles the clauses. Exact set identities, no sign. The consumer chain into circle-cylinder-homology (bridge Homeomorph.Set.prod univ U₀ then Homeomorph.Set.univ, the overlap split by the preimages of W₁, W₂, the section y ↦ (y, ↑(1/4))) was elaborated with closed proofs in red-team scratch. Red team: docs/sketches/circle-arc-cover.redteam.md, pass with changes. General, kept local (decision 0011); about 3 s to elaborate."
```

B. `docs/gaps.md`, category "Topology": append to the "Diff at a bump" line, after `LinearAlgebra/Matrix/GeneralLinearGroup/`, the text `, Topology/Instances/AddCircle/, Topology/Homotopy/Contractible.lean, Analysis/Convex/Contractible.lean` (each in backticks, as the existing entries), and add this row after the `HodgeLadder.Glpos.PathConnected` row:

```
| `HodgeLadder.CircleArcs.contractibleSpace_compl_singleton` (the circle minus any point is contractible), `U₀`, `V₀`, `W₁`, `W₂` with `isOpen_U₀`, `isOpen_V₀`, `U₀_union_V₀`, `U₀_inter_V₀`, `isOpen_W₁`, `isOpen_W₂`, `disjoint_W₁_W₂`, `W₁HomeomorphIoo`, `W₂HomeomorphIoo`, the four `ContractibleSpace` instances, `quarter_mem_W₁`, `threeQuarter_mem_W₂`, `quarter_mem_U₀_inter_V₀`, `circle_arc_cover`; helpers `coe_eq_coe_iff_of_mem_Ico` (the `a = 0`, `p = 1` case of Mathlib's `AddCircle.coe_eq_coe_iff_of_mem_Ico`, same last name component; resolves by type under `open AddCircle`), `coe_mem_image_iff` | `HodgeLadder.General.CircleArcs` | 0 | general topology of `UnitAddCircle`; Mathlib at the pin has `Circle.isPathConnected_compl_singleton` and no contractibility result for the circle minus a point; rung `circle-arc-cover`, for `circle-cylinder-homology` | 2026-11-27 |
```

C. `docs/conventions.md`, register table: add this row after the row "Torus cycle and winding classes".

```
| Circle coordinate and the two-arc cover | Mathlib `UnitAddCircle = AddCircle (1 : ℝ)` (ℝ/ℤ, period 1), `AddCircle.toCircle` (x ↦ exp(2πi x)); this repository, `HodgeLadder.CircleArcs` (rung `circle-arc-cover`) | points are read in period-1 coordinates: U₀ = {↑0}ᶜ, V₀ = {↑(1/2)}ᶜ, W₁ = ↑(0, 1/2), W₂ = ↑(1/2, 1), section point ↑(1/4) ∈ W₁; no orientation of the arcs is used | none for `circle-arc-cover` and for the dimension counts of `circle-cylinder-homology` (only distinctness of the points mod 1 enters); the period fixes `coordChar` and the winding classes of `torus-singular-cohomology` (row "Torus cycle and winding classes") | checked (red team 2026-11-27, `docs/sketches/circle-arc-cover.redteam.md`) |
```

## Recommended changes (optional)

R1. State `contractibleSpace_compl_singleton` for `AddCircle p` with `[Fact (0 < p)]` and keep the `UnitAddCircle` form as its instance; the proof is the same with `a + p`.

R2. In the module docstring, name the consumer bridge `Homeomorph.Set.prod Set.univ U₀` so the next prover finds it without the red-team file.

## Attempts that failed

- A `▸` on `U₀_inter_V₀` toward `q.2.1 ∈ W₁ ∪ W₂` in the consumer bridge: rejected (neither side in the goal); `U₀_inter_V₀.symm ▸` works. Bookkeeping for the consumer only.
- `fun_prop` on the inverse of `↥P₁ ≃ₜ Y × ↥W₁`: fails on the dependent membership proof; `Continuous.subtype_mk` twice works.
- Looking for a short proof of `circle_arc_cover` that ignores the definitions: none; each conjunct needs its own lemma.
