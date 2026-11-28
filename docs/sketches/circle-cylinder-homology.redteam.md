# Red team: `circle-cylinder-homology` (sub-rung of `torus-singular-cohomology`, order 2)

Date: 2026-11-28. Worktree `circle-cylinder-homology`, candidate commit `7849a17` on `track/circle-cylinder-homology`, one commit on top of `main` `19a4bda`; the branch adds only `HodgeLadder/General/CircleCylinderHomology.lean` (namespace `HodgeLadder.CircleCylinder`). Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, unchanged against `main`. Issue #248.

Read: the Lean file; its three inputs `HodgeLadder/General/{CircleArcs,HomologyProdContractible,MayerVietorisRank}.lean` and their red-team files; `docs/sketches/torus-singular-cohomology.md` (steps 3 to 6, sub-rung table); the ledger rows of this rung and of `torus-homology-bound`; upstream `HodgeConjecture/Definitions/AlgebraicTopology/Singular/Cohomology.lean` (`Homology`, `homologyMap`), `HodgeConjecture/Lemmas/AlgebraicTopology/Singular/HomologyZeroNaturality.lean`, `Other/AlgebraicTopology/Singular/MayerVietoris.lean` (`subsetIntersectionToLeft`); Mathlib `AlgebraicTopology/SingularHomology/HomologyZero.lean`, `Topology/Homeomorph/Lemmas.lean`; `docs/conventions.md`, `docs/references.md`, `docs/gaps.md`.

Scratch (directory `scratch-rt-cch/` in the worktree, deleted at the end; `lake env lean`):

| File | What | Result |
|---|---|---|
| `Axioms.lean` | `#print axioms` on the 12 headline and bridge declarations; `#check` of the headline | `[propext, Classical.choice, Quot.sound]` each; about 4 s |
| `Lower.lean` | `finrank_range_overlap_zero_add_one_le` (rank φ₀ + 1 ≤ dim H₀(U) + dim H₀(V) for nonempty U, through the augmentation), `one_le_finrank_homology_one_circle`, `finrank_homology_one_circle : finrank ℚ (Homology ℚ (TopCat.of UnitAddCircle) 1) = 1` | compiles, no `sorry`, no warning, standard axioms; about 5 s; needs `import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.HomologyZeroNaturality` |
| `Torus.lean` | the consumer `torus-homology-bound` in full: `torusSuccHomeo n : UnitAddTorus (Fin (n + 1)) ≃ₜ UnitAddTorus (Fin n) × UnitAddCircle` (`Fin.appendHomeomorph n 1`, `Homeomorph.funUnique`) and `torus_bound n : ∀ k, FiniteDimensional ℚ H_k(Tⁿ) ∧ finrank ℚ H_k(Tⁿ) ≤ n.choose k` by induction on n | compiles, no `sorry`, standard axioms; about 5 s |

`python3 tools/check.py --no-build` on the worktree: `ACCEPTED: all checks passed`. The checker names no declaration of this rung yet (ledger row `open`, `declarations: []`), so the axioms above come from the scratch `#print axioms`. `lake build HodgeLadder.General.CircleCylinderHomology` is current; the file elaborates in about 4 s, far under the 10-minute split threshold.

**Verdict: pass with changes.** The headline is the inequality form of the Künneth count b_{k+1}(Y × S¹) = b_{k+1}(Y) + b_k(Y), proved from the exact Mayer–Vietoris count with every inequality in the right direction, with its finite-dimensionality companion, standard axioms, and no sign. The missing degree 0 costs the consumer nothing: the full torus bound closes in scratch on top of the candidate as it stands. The one substantive gap is the nonvacuity test: `dim H_1(S¹) ≤ 1` would also hold if positive-degree homology vanished, so the required changes add the matching lower bound (written and compiled below), giving `dim H_1(S¹; ℚ) = 1`. The rest is ledger, root import, roadmap, gaps and conventions text.

## Findings

1. **Literature.** For a space Y, H_n(Y × S¹; ℚ) ≅ H_n(Y; ℚ) ⊕ H_{n−1}(Y; ℚ), by Künneth over a field or by Mayer–Vietoris on the cover Y × (two arcs) (`Hatcher2002` §3.B for Künneth, §2.2 for the Mayer–Vietoris sequence; locators recalled, unverified). Field by field against `finrank_homology_prod_circle_le`: the space is `TopCat.of (Y × UnitAddCircle)` with `Y : TopCat.{0}` and the product topology; the coefficient ring is ℚ through upstream's `AlgebraicTopology.Singular.Homology ℚ` (Mathlib's singular homology with unnormalized chains, harmless for dimensions); n = k + 1 ≥ 1; the conclusion is `≤` where the literature has `=`, and the finiteness hypotheses on H_{k+1}(Y) and H_k(Y) are the literature's finiteness of b_{k+1}(Y) and b_k(Y). The companion `finiteDimensional_homology_prod_circle` is the finiteness half of the same isomorphism. Match, in the weaker inequality form the sketch asks for (step 5, "the inequality form used here is derived in this sketch").

2. **Correctness of the count.** `MayerVietoris.finrank_homology_succ_add_le` on U = Y × U₀, V = Y × V₀ reads dim H_{k+1}(X) + r_{k+1} + r_k ≤ dim H_{k+1}(U) + dim H_{k+1}(V) + dim H_k(U ∩ V), with r_j = rank (i_* : H_j(U ∩ V) → H_j(U)) on the left. The file supplies dim H_{k+1}(U) = dim H_{k+1}(V) = b_{k+1}(Y) (`homologyCylUEquiv`, `homologyCylVEquiv`, equalities), dim H_k(U ∩ V) ≤ 2 b_k(Y) (`finrank_homology_overlap_le`, upper bound on a right-hand term) and r_j ≥ b_j(Y) for j = k, k + 1 (`finrank_le_finrank_range_overlap`, lower bounds on left-hand terms). Then dim H_{k+1}(X) ≤ 2 b_{k+1} + 2 b_k − b_{k+1} − b_k = b_{k+1} + b_k. Every bound enters on the side where it helps; `omega` closes it, and no step needs an upper bound on a rank. The rank step is `finrank_le_finrank_range_of_comp_eq_id` with s = H_j(section), f = i_*, p = H_j(pr₁ on U), from `overlapSection_comp : s ≫ i ≫ pr₁ = 𝟙 Y` (`ext; rfl`) and functoriality; it needs H_j(U) finite-dimensional, supplied from the equivalence. The section point ↑(1/4) lies in W₁ ⊂ U₀ ∩ V₀ (`quarter_mem_U₀_inter_V₀`). The overlap split P₁, P₂ uses `U₀_inter_V₀` and `disjoint_W₁_W₂`; both pieces are `Y × (contractible arc)` through `sliceHomeo`, whose inverses are `rfl`.

3. **Hypotheses.** Both instance hypotheses are needed for the finiteness conclusion: by Künneth each of H_{k+1}(Y) and H_k(Y) is a summand of H_{k+1}(Y × S¹), so either being infinite-dimensional makes the cylinder's infinite-dimensional. The `finrank` bound alone is in fact true with no hypotheses (an infinite-dimensional cylinder group has `finrank` 0), but proving that needs the reverse inequality and is not required. Satisfiable: Y = point (the file's own test, with `subsingleton_homology_succ_of_totallyDisconnected` and `finiteDimensional_homology_zero_of_pathConnected`), and every torus Tⁿ in every degree (`Torus.lean`).

4. **Trivial truth.** Tried and failed. The bound is trivially true whenever `finrank ℚ H_{k+1}(Y × S¹) = 0`, the same vacuity mode as `finrank_homology_succ_add_le` (red team `mayer-vietoris-finrank`, finding 5); under the hypotheses the companion makes the space finite-dimensional, so the `finrank` is its dimension and the bound has content. No definition unfolds to `True`, there is no `ℕ∞` coercion, and the index k is free. The weakness is in the test (finding 7).

5. **Interface rung.** Not applicable; no structure, no axiom.

6. **Checked-rung mechanics.** All 32 declarations of the file use the three standard axioms (scratch `#print axioms`; the checker will repeat it once the ledger names them). The ledger row is still the placeholder: file `HodgeLadder/Circle/Cylinder/Homology.lean`, module `HodgeLadder.Circle.Cylinder.Homology`, `declarations: []`. The candidate sits at `HodgeLadder/General/CircleCylinderHomology.lean`, which fits its siblings (general singular-homology facts about an arbitrary Y, kept local by decision 0011); change 4 sets the real module.

7. **Nonvacuity (7b).** The candidate's test `finrank_homology_one_circle_le` gives `dim H_1(S¹; ℚ) ≤ 1`, which would also hold if `Homology ℚ · 1` were zero on every space, so it does not catch a vacuous bound. The smallest test that does is `finrank ℚ (Homology ℚ (TopCat.of UnitAddCircle) 1) = 1`. Options for the lower half, cheapest first:
   - (a) **Mayer–Vietoris plus the augmentation (taken; compiled in `Lower.lean`).** At Y = point the exact count `finiteDimensional_homology_succ_and_finrank_eq` reads dim H_1(S¹) + r₁ + r₀ = 0 + 0 + 2, with dim H_0(U ∩ V) = 2 from `finrank_homology_eq_of_disjoint` and r₁ = 0 from `finrank_homology_overlap_le` at degree 1. The bound r₀ ≤ 1 comes from upstream's `TopCat.singularHomology₀ε_naturality` and `TopCat.singularHomology₀ε_epi` (`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/HomologyZeroNaturality.lean`, already in the default build closure: the name resolves under `import HodgeLadder` at `main`, and not under `HodgeLadder.General.LocalOrientation` alone): the overlap map (i_*, −j_*) lands in the kernel of (a, b) ↦ ε a + ε b, which is onto ℚ, so its rank is at most dim H_0(U) + dim H_0(V) − 1. About 70 lines, 5 s.
   - (b) **Winding class and duality.** No degree-1 evaluation on S¹ exists at the pin: `HodgeLadder.Cup.torusEval` is a degree-2 functional on a torus, and naturality of `windingClass` is the later rung `winding-class-pullback`. Not available.
   - (c) **The torus.** `HodgeLadder.Torus.coordWinding_cup_ne_zero` gives H²(T²; ℚ) ≠ 0, hence H_2(T²; ℚ) ≠ 0 through upstream's `cohomologyEquivDualHomology`. That is a positive-degree nonvacuity check for the consumer `torus-homology-bound` at n = k = 2 (bound 1, value ≥ 1); it does not test this rung at S¹. Change 8 records it on the consumer.

8. **Degree 0 and the consumer.** The rung bounds only degrees k + 1 ≥ 1; b_0(Y × S¹) is not covered. The consumer does not need it. In `Torus.lean` the induction proves, for every n, `∀ k, FiniteDimensional ℚ H_k(Tⁿ) ∧ finrank ℚ H_k(Tⁿ) ≤ n.choose k`, case by case: k = 0 at every n from `MayerVietoris.finiteDimensional_homology_zero_of_pathConnected` and `finrank_homology_zero_of_pathConnected` (`UnitAddTorus (Fin n)` is path-connected by Mathlib's Pi instance, also at n = 0), giving 1 ≤ n.choose 0 = 1; k = j + 1 at n = 0 from `subsingleton_homology_succ_of_totallyDisconnected` (value 0 ≤ 0); k = j + 1 at n + 1 from `homologyIsoOfHomeomorph` along `torusSuccHomeo n`, then `finiteDimensional_homology_prod_circle (torus n) j` and `finrank_homology_prod_circle_le (torus n) j` with the induction hypothesis at j + 1 and at j (both finiteness instances and both bounds), then `Nat.choose_succ_succ'`: n.choose (j + 1) + n.choose j = (n + 1).choose (j + 1). The hypothesis at j = 0 is the degree-0 clause, so the conjunction must be proved for all k at once, which the induction does. The bound with k + 1 therefore suffices for every k ≥ 1 given b_0(Tⁿ) = 1.

9. **Bridges and Mathlib equivalents.** `prodSetHomeo` is `Homeomorph.Set.prod univ S` followed by `Homeomorph.Set.univ`, both Mathlib; the composite is not in Mathlib. `sliceHomeo` (a subtype of a subtype `A ⊆ Y × S¹` cut by the second coordinate, when `A ⊇ Y × S`) has no Mathlib counterpart at the pin: `Homeomorph.Set.prod` handles `s ×ˢ t` only, and `IsEmbedding.toHomeomorphOfSurjective` would give a version with non-`rfl` inverses; the hand-built one is the better spelling. `homologyEquivOfHomeomorphProd` (H_j(A) ≃ H_j(Y) for A ≃ₜ Y × W, W contractible) composes the ladder's `homologyIsoOfHomeomorph` and `homologyProdContractibleIso`; neither Mathlib nor upstream has homology of a product. It is general in A and W and would sit naturally in `HodgeLadder.General.HomologyProdContractible`; keeping it here is fine for a one-file pull request. Its forward map is `homologyMap` of the homeomorphism followed by the projection, but no statement here reads it beyond `finrank`, so the choice of `Classical.arbitrary W` for the inverse is immaterial. `cylUFst` is the projection on the subtype, distinct from `HodgeLadder.prodFst`; no name clash (namespaced). Layer: the module imports three layer-0 modules, so it is layer 1 by `tools/pinwalk.py`'s rule ("1 + the largest layer of its imports"); `pinwalk.py` does not list it yet because it is not root-imported.

10. **Signs and conventions.** No sign enters a statement. Upstream's overlap map (i_*, −j_*) enters only through ranks (row "Singular Mayer–Vietoris (homology)"); the proof bounds rank i_* from below, and the sign does not change it. Period-1 coordinates on the circle and the section point ↑(1/4) are fixed by the row "Circle coordinate and the two-arc cover", which already names this rung's dimension counts as convention-free. The lower bound of change 1 adds the degree-0 augmentation ε (class of a point ↦ 1, Mathlib's `TopCat.singularHomology₀ε`); it enters only through the dimension of a kernel, and any nonzero rescaling of ε gives the same kernel. Change 7 records it.

11. **Equality first.** The rung is an inequality. The equality it is a step toward is the Künneth count b_{k+1}(Y × S¹) = b_{k+1}(Y) + b_k(Y); no rung states it, and the ladder does not need it, because `torus-singular-cohomology` reaches its equalities (dim H¹(Tⁿ) = n, dim H²(Tⁿ) = n.choose 2) from this upper bound plus linear independence of winding classes and their cups (`torus-winding-duality`). The point case of the equality, dim H_1(S¹; ℚ) = 1, is change 1. A general equality rung would need the upper bound r_j ≤ b_j(Y) on the overlap map, which in turn needs the identification of both inclusions P_i → U with the identity of Y in homology; not proposed here.

12. **Pin drift.** None: the candidate was built and probed at the current pin. The new upstream inputs of change 1 (`singularHomology₀ε_naturality`, `singularHomology₀ε_epi`) are in `HodgeConjecture/Lemmas/AlgebraicTopology/Singular/`, already in the singular category's "Diff at a bump" line.

## Required changes

1. **Lower bound and the equality test.** Add `public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.HomologyZeroNaturality` to the imports, and append before `end HodgeLadder.CircleCylinder` (the proofs are the ones compiled in `Lower.lean`; under the file's `open`s the names `MayerVietoris.*` resolve as written):

   ```lean
   /-- **Rank of the degree-zero overlap map.** For an open cover with `U` nonempty, the overlap map
   `(i_*, -j_*) : H_0(U ∩ V) → H_0(U) × H_0(V)` lands in the kernel of `(a, b) ↦ ε a + ε b`
   (`ε` the augmentation, natural by `TopCat.singularHomology₀ε_naturality`), which is onto `ℚ`,
   so `rank φ₀ + 1 ≤ dim H_0(U) + dim H_0(V)`. No sign enters: `ε` is used only through its
   kernel. -/
   theorem finrank_range_overlap_zero_add_one_le {X : TopCat.{0}} (U V : Set X) [Nonempty U]
       [FiniteDimensional ℚ (Homology ℚ (TopCat.of U) 0)]
       [FiniteDimensional ℚ (Homology ℚ (TopCat.of V) 0)] :
       finrank ℚ (LinearMap.range (LinearMap.prod
           (homologyMap ℚ 0 (subsetIntersectionToLeft X U V))
           (-homologyMap ℚ 0 (subsetIntersectionToRight X U V)))) + 1 ≤
         finrank ℚ (Homology ℚ (TopCat.of U) 0) + finrank ℚ (Homology ℚ (TopCat.of V) 0) := by
     let εU := ((TopCat.of U).singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom
     let εV := ((TopCat.of V).singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom
     let εW := ((TopCat.of ↥(U ∩ V)).singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom
     let ψ : (Homology ℚ (TopCat.of U) 0 × Homology ℚ (TopCat.of V) 0) →ₗ[ℚ] ℚ :=
       LinearMap.coprod εU εV
     have nL : ∀ x, εU (homologyMap ℚ 0 (subsetIntersectionToLeft X U V) x) = εW x := fun x =>
       congrArg (fun φ => ModuleCat.Hom.hom φ x)
         (TopCat.singularHomology₀ε_naturality (subsetIntersectionToLeft X U V) (ModuleCat.of ℚ ℚ))
     have nR : ∀ x, εV (homologyMap ℚ 0 (subsetIntersectionToRight X U V) x) = εW x := fun x =>
       congrArg (fun φ => ModuleCat.Hom.hom φ x)
         (TopCat.singularHomology₀ε_naturality (subsetIntersectionToRight X U V) (ModuleCat.of ℚ ℚ))
     have hle : LinearMap.range (LinearMap.prod
           (homologyMap ℚ 0 (subsetIntersectionToLeft X U V))
           (-homologyMap ℚ 0 (subsetIntersectionToRight X U V))) ≤ LinearMap.ker ψ := by
       rintro _ ⟨x, rfl⟩
       change εU (homologyMap ℚ 0 (subsetIntersectionToLeft X U V) x) +
         εV (-(homologyMap ℚ 0 (subsetIntersectionToRight X U V) x)) = 0
       rw [map_neg, nL x, nR x, add_neg_cancel]
     have hsurj : Function.Surjective ψ := by
       have := (TopCat.of U).singularHomology₀ε_epi (ModuleCat.of ℚ ℚ)
       have hs : Function.Surjective εU := (ModuleCat.epi_iff_surjective _).1 this
       intro r
       obtain ⟨a, ha⟩ := hs r
       exact ⟨(a, 0), by simp [ψ, ha]⟩
     have rn := LinearMap.finrank_range_add_finrank_ker ψ
     rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
       Module.finrank_prod] at rn
     have := Submodule.finrank_mono hle
     omega

   /-- **Nonvacuity test, lower bound.** `1 ≤ dim H_1(S¹; ℚ)`: the exact Mayer–Vietoris count on the
   cylinder over a point reads `dim H_1(S¹) + rank φ₁ + rank φ₀ = 0 + 0 + 2`, with `rank φ₁ = 0`
   (`H_1` of the overlap is zero) and `rank φ₀ ≤ 1` (`finrank_range_overlap_zero_add_one_le`). -/
   theorem one_le_finrank_homology_one_circle :
       1 ≤ finrank ℚ (Homology ℚ (TopCat.of UnitAddCircle) 1) := by
     let P := TopCat.of PUnit.{1}
     have : Subsingleton (Homology ℚ P (0 + 1)) :=
       MayerVietoris.subsingleton_homology_succ_of_totallyDisconnected _ 0
     have := MayerVietoris.finiteDimensional_homology_zero_of_pathConnected P
     have hP0 := MayerVietoris.finrank_homology_zero_of_pathConnected P
     have : Nonempty (cylU P) := ⟨⟨(PUnit.unit, ((1 / 4 : ℝ) : UnitAddCircle)), trivial,
       quarter_mem_U₀_inter_V₀.1⟩⟩
     have := (homologyCylUEquiv P (0 + 1)).symm.finiteDimensional
     have := (homologyCylVEquiv P (0 + 1)).symm.finiteDimensional
     have := (homologyCylUEquiv P 0).symm.finiteDimensional
     have := (homologyCylVEquiv P 0).symm.finiteDimensional
     have := finiteDimensional_homology_overlap P 0
     have := finiteDimensional_homology_overlap P (0 + 1)
     obtain ⟨-, h⟩ := MayerVietoris.finiteDimensional_homology_succ_and_finrank_eq
       (isOpen_cylU P) (isOpen_cylV P) (cylU_union_cylV P) 0
     have h0 := finrank_range_overlap_zero_add_one_le (X := cyl P) (cylU P) (cylV P)
     rw [(homologyCylUEquiv P 0).finrank_eq, (homologyCylVEquiv P 0).finrank_eq, hP0] at h0
     rw [(homologyCylUEquiv P (0 + 1)).finrank_eq, (homologyCylVEquiv P (0 + 1)).finrank_eq,
       finrank_zero_of_subsingleton (M := Homology ℚ P (0 + 1))] at h
     have := (homologyP₁Equiv P 0).symm.finiteDimensional
     have := (homologyP₂Equiv P 0).symm.finiteDimensional
     have hW := MayerVietoris.finrank_homology_eq_of_disjoint (isOpen_P₁ P) (isOpen_P₂ P)
       (P₁_union_P₂ P) (disjoint_P₁_P₂ P) 0
     rw [(homologyP₁Equiv P 0).finrank_eq, (homologyP₂Equiv P 0).finrank_eq, hP0] at hW
     have hW1 := finrank_homology_overlap_le P (0 + 1)
     rw [finrank_zero_of_subsingleton (M := Homology ℚ P (0 + 1))] at hW1
     have r1 := LinearMap.finrank_range_le (LinearMap.prod
       (homologyMap ℚ (0 + 1) (subsetIntersectionToLeft (cyl P) (cylU P) (cylV P)))
       (-homologyMap ℚ (0 + 1) (subsetIntersectionToRight (cyl P) (cylU P) (cylV P))))
     rw [(homologyPointProdCircleEquiv 1).symm.finrank_eq]
     change finrank ℚ (Homology ℚ (TopCat.of ↥(cylU P ∩ cylV P)) 0) = 2 at hW
     change finrank ℚ (Homology ℚ (TopCat.of ↥(cylU P ∩ cylV P)) (0 + 1)) ≤ 2 * 0 at hW1
     change 1 ≤ finrank ℚ (Homology ℚ (cyl P) (0 + 1))
     omega

   /-- **Nonvacuity test, value.** `dim H_1(S¹; ℚ) = 1`, the point case of the Künneth count
   `b_1(pt × S¹) = b_1(pt) + b_0(pt)`; it fails if positive-degree homology vanished. -/
   theorem finrank_homology_one_circle :
       finrank ℚ (Homology ℚ (TopCat.of UnitAddCircle) 1) = 1 :=
     le_antisymm finrank_homology_one_circle_le one_le_finrank_homology_one_circle
   ```

2. **Module docstring.** After the sentence ending "with finite dimension." in the first paragraph insert: "Only degrees `k + 1 ≥ 1` are bounded; `b_0(Y × S¹)` is not covered here, and the torus induction (`torus-homology-bound`) treats degree `0` by path-connectedness (`MayerVietoris.finrank_homology_zero_of_pathConnected`)." In "Main results" replace the last bullet by: "`HodgeLadder.CircleCylinder.finiteDimensional_homology_one_circle`, `HodgeLadder.CircleCylinder.finrank_homology_one_circle_le`, `HodgeLadder.CircleCylinder.one_le_finrank_homology_one_circle`, `HodgeLadder.CircleCylinder.finrank_homology_one_circle`: the nonvacuity test at `Y = pt`, `dim H_1(S¹; ℚ) = 1` with finite dimension; the lower bound uses `HodgeLadder.CircleCylinder.finrank_range_overlap_zero_add_one_le`, the degree-zero rank bound from the augmentation."

3. **Root import.** Add `public import HodgeLadder.General.CircleCylinderHomology` to `HodgeLadder.lean`, next to `HodgeLadder.General.MayerVietorisRank`.

4. **Ledger entry `circle-cylinder-homology`.** `"status": "checked"`, `"module": "HodgeLadder.General.CircleCylinderHomology"`, `"contributors": ["claude-code"]`, `"declarations"` under `HodgeLadder.CircleCylinder.`: `homologyEquivOfHomeomorphProd`, `prodSetHomeo`, `sliceHomeo`, `cyl`, `cylU`, `cylV`, `isOpen_cylU`, `isOpen_cylV`, `cylU_union_cylV`, `homologyCylUEquiv`, `homologyCylVEquiv`, `overlap`, `P₁`, `P₂`, `isOpen_P₁`, `isOpen_P₂`, `P₁_union_P₂`, `disjoint_P₁_P₂`, `mem_overlap_of_mem_inter`, `homologyP₁Equiv`, `homologyP₂Equiv`, `finiteDimensional_homology_overlap`, `finrank_homology_overlap_le`, `overlapSection`, `cylUFst`, `overlapSection_comp`, `finrank_le_finrank_range_overlap`, `finiteDimensional_homology_prod_circle`, `finrank_homology_prod_circle_le`, `homologyPointProdCircleEquiv`, `finiteDimensional_homology_one_circle`, `finrank_homology_one_circle_le`, `finrank_range_overlap_zero_add_one_le`, `one_le_finrank_homology_one_circle`, `finrank_homology_one_circle`. Note:

   > Checked 2026-11-28. Sketch: docs/sketches/torus-singular-cohomology.md (order 2, step 5). For Y : TopCat.{0} with H_{k+1}(Y; ℚ) and H_k(Y; ℚ) finite-dimensional, H_{k+1}(Y × S¹; ℚ) is finite-dimensional (finiteDimensional_homology_prod_circle) with dim ≤ b_{k+1}(Y) + b_k(Y) (finrank_homology_prod_circle_le), the inequality form of the Künneth count. Proof: the exact Mayer–Vietoris count on U = Y × U₀, V = Y × V₀; dim H_j(U) = dim H_j(V) = b_j(Y) (homologyEquivOfHomeomorphProd through prodSetHomeo); the overlap is the disjoint open union of P₁ ≃ₜ Y × W₁ and P₂ ≃ₜ Y × W₂ (sliceHomeo), so dim H_j(U ∩ V) ≤ 2 b_j(Y); the section y ↦ (y, ↑(1/4)) gives rank i_{*,j} ≥ b_j(Y). Degrees k + 1 ≥ 1 only; torus-homology-bound treats degree 0 by path-connectedness. No sign: upstream's (i, −j) enters ranks only. Nonvacuity: finrank_homology_one_circle, dim H_1(S¹; ℚ) = 1, the upper bound at Y = point with a lower bound from the exact count and the degree-zero augmentation (finrank_range_overlap_zero_add_one_le, upstream TopCat.singularHomology₀ε_naturality). The consumer torus-homology-bound was closed in red-team scratch on top of this file. Red team: docs/sketches/circle-cylinder-homology.redteam.md, pass with changes. General, kept local (decision 0011); about 4 s to elaborate.

5. **Roadmap row.** Replace the last cell of the `circle-cylinder-homology` row by: "b_{k+1}(Y × S¹) ≤ b_{k+1}(Y) + b_k(Y) with finite dimension, k + 1 ≥ 1; test dim H_1(S¹; ℚ) = 1; `HodgeLadder.General.CircleCylinderHomology`", and its status cell by `checked`.

6. **Gaps row.** In `docs/gaps.md`, category "Singular homology, cohomology and simplicial cochains", after the `HodgeLadder.General.MayerVietorisRank` row, add:

   > | `HodgeLadder.CircleCylinder.homologyEquivOfHomeomorphProd` (H_j(A) ≃ H_j(Y) for A ≃ₜ Y × W, W contractible), `prodSetHomeo` (`↥(univ ×ˢ S) ≃ₜ Y × ↥S`), `sliceHomeo` (the part of `A ⊆ Y × S¹` over `S`, when `A ⊇ Y × S`, is `Y × S`, inverses `rfl`), `finrank_range_overlap_zero_add_one_le` (rank of the degree-zero overlap map, any open cover with `U` nonempty); the cylinder cover `cyl`, `cylU`, `cylV`, `overlap`, `P₁`, `P₂` with their lemmas and equivalences, `overlapSection`, `cylUFst`, `overlapSection_comp`, `finiteDimensional_homology_overlap`, `finrank_homology_overlap_le`, `finrank_le_finrank_range_overlap`, `finiteDimensional_homology_prod_circle`, `finrank_homology_prod_circle_le`, `homologyPointProdCircleEquiv`, `finiteDimensional_homology_one_circle`, `finrank_homology_one_circle_le`, `one_le_finrank_homology_one_circle`, `finrank_homology_one_circle` | `HodgeLadder.General.CircleCylinderHomology` | 1 | neither Mathlib nor upstream has homology of a product or of the circle at the pin; Mathlib has `Homeomorph.Set.prod` and no subtype-of-subtype slice homeomorphism; `homologyEquivOfHomeomorphProd` would sit next to `homologyProdContractibleIso`; rung `circle-cylinder-homology`, for `torus-homology-bound` | 2026-11-28 |

7. **Conventions.** In `docs/conventions.md`, row "Circle coordinate and the two-arc cover", append to the "Depends" cell: "`circle-cylinder-homology` uses the section point ↑(1/4) and the split U₀ ∩ V₀ = W₁ ∪ W₂ only; its lower bound for dim H_1(S¹) reads Mathlib's augmentation `TopCat.singularHomology₀ε` (class of a point ↦ 1) only through its kernel, so no rescaling of it matters", and set its status cell to "checked (red teams 2026-11-27 `circle-arc-cover`, 2026-11-28 `circle-cylinder-homology`)".

8. **Consumer note.** Append to the ledger note of `torus-homology-bound`: "Red team circle-cylinder-homology (2026-11-28): the induction closes in scratch on top of the cylinder file, proving ∀ k, FiniteDimensional ℚ H_k(Tⁿ) ∧ finrank ≤ n.choose k at once (the degree-k+1 step needs the hypothesis at k + 1 and at k); k = 0 at every n by MayerVietoris.finiteDimensional_homology_zero_of_pathConnected and finrank_homology_zero_of_pathConnected; k ≥ 1 at n = 0 by subsingleton_homology_succ_of_totallyDisconnected; the step by homologyIsoOfHomeomorph along (Fin.appendHomeomorph n 1).symm then Homeomorph.funUnique (Fin 1) UnitAddCircle, and Nat.choose_succ_succ'. Nonvacuity test: at n = k = 2 the bound is 1 and HodgeLadder.Torus.coordWinding_cup_ne_zero with upstream cohomologyEquivDualHomology gives H_2(T²; ℚ) ≠ 0, so dim H_2(T²; ℚ) = 1."

## What was tried and did not work

- Proving the headline in under ten lines without Mayer–Vietoris: no route; the only short proof is the vacuous case `finrank = 0`, excluded under the hypotheses by the companion.
- A degree-1 evaluation of the winding class on S¹ for the lower bound: none exists at the pin (`torusEval` is degree 2 on a torus; `windingClass` naturality is open in `winding-class-pullback`).
- The lower-bound proof's first draft: `simp only [LinearMap.prod_apply, …]` followed by `erw [nL, nR]` left the second component unrewritten (`Function.prod` form); the `change` to the explicit sum, then `rw [map_neg, nL x, nR x, add_neg_cancel]`, closes it. The final `omega` first failed on `0 + 1` against `1` and on `overlap P` against `TopCat.of ↥(cylU P ∩ cylV P)`; the three `change` lines fix both.
- Compiling the lower bound without importing `HomologyZeroNaturality`: `Unknown constant TopCat.singularHomology₀ε_naturality`. The module is upstream's and already in the closure of `import HodgeLadder` (checked in scratch), so the import costs no build time.
