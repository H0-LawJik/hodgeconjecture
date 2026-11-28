# Red team: `mayer-vietoris-finrank`

Date: 2026-11-27. Candidate: commit `302ef42` on `track/mayer-vietoris-finrank`, file `HodgeLadder/General/MayerVietorisRank.lean` (namespace `HodgeLadder.MayerVietoris`, 21 declarations), branched from `main` `8eba28e`. Pin unchanged: upstream `2ead713`, Lean and Mathlib `v4.35.0-rc4`. Probes ran with `lake env lean` in a scratch directory under the worktree, deleted afterwards. Plan: `docs/sketches/torus-singular-cohomology.md`, steps 3 and 4.

**Verdict: pass with changes.** The exact count is correct, honest about finiteness and exactly the sketch's step 3 sharpened to an equality; the disjoint case is an equivalence in every degree, which is step 4 sharpened the same way. All 21 declarations use the three standard axioms. The only sign is upstream's `(i, −j)`, and it enters ranks only. The changes are one inaccurate docstring sentence, a nonvacuity test for the exact count (written and compiled below), a conventions row, the gaps row and pin-walk text, the ledger and root import, and one test requirement passed down to `circle-cylinder-homology`.

## Findings

1. **Signs first.** The only sign in the file is upstream's `(i, −j)`. It appears in `sumHomologyEquiv_comp_overlap` (overlap map `x ↦ (i_* x, −j_* x)`) and, as `-homologyMap ℚ _ (subsetIntersectionToRight X U V)`, in the two rank terms of `finiteDimensional_homology_succ_and_finrank_eq`. The sum map is `(x, y) ↦ (ι_U)_* x + (ι_V)_* y` with no sign (`sum_comp_sumHomologyEquiv_symm`). The connecting map `singularMayerVietorisBoundary` appears in no statement; its sign is used nowhere. Nothing else carries a sign.

2. **Statement against the literature.** `Hatcher2002` §2.2 (recalled, unverified; the references row has no §2.2 locator for Mayer–Vietoris yet): for X = int A ∪ int B, the sequence ⋯ → H_n(A ∩ B) → H_n(A) ⊕ H_n(B) → H_n(X) → H_{n−1}(A ∩ B) → ⋯ is exact, with Φ(x) = (x, −x) and Ψ(x, y) = x + y. Field by field against the Lean:
   - X ↔ `X : TopCat.{0}`; A, B ↔ `U V : Set X` with `IsOpen U`, `IsOpen V`, `U ∪ V = Set.univ` (the open case of Hatcher's interior condition).
   - H_n ↔ upstream `AlgebraicTopology.Singular.Homology ℚ` (unnormalized singular chains, the same homology); coefficients ℚ (Hatcher's sequence holds for any coefficients).
   - Φ ↔ `LinearMap.prod (homologyMap ℚ n (subsetIntersectionToLeft X U V)) (-homologyMap ℚ n (subsetIntersectionToRight X U V))`: the same sign, on the second component.
   - Ψ ↔ `LinearMap.coprod (homologyMap ℚ n (topologicalSubsetInclusion X U)) (homologyMap ℚ n (topologicalSubsetInclusion X V))`: the same, no sign.
   - The count itself is linear algebra on three exactness points; the literature has no statement in this form (the sketch marks it derived). Its arithmetic, checked by hand: with B = H_{k+1}(U) × H_{k+1}(V), D = H_k(U ∩ V), dim H_{k+1}(X) = rank Ψ + rank ∂ = (dim B − rank φ_{k+1}) + (dim D − rank φ_k). This is the Lean equality.
   - The sketch's step 3 asks for `dim H_{k+1}(X) + rank i_{*,k+1} + rank i_{*,k} ≤ …` with H_{k+1}(X) finite-dimensional: `finrank_homology_succ_add_le` and `finiteDimensional_homology_succ`, token for token. Step 4 asks for the sum map onto in every degree: `bijective_coprod_homologyMap_of_disjoint` gives bijective, and `finrank_homology_le_of_disjoint` is the requested bound.

3. **Hypotheses satisfiable.** `finrank_homology_zero_bool` instantiates the disjoint theorems (Bool, `{true}`, `{false}`, value 2). For the exact count, the point covered by `univ` twice satisfies every hypothesis at k = 0 (H_1 of a totally disconnected space is zero, H_0 of a path-connected one is ℚ); the test in change 2 compiles in about 6 s and reads `rank φ₀ = 1` off the count.

4. **No hidden finiteness in the equality.** Every `finrank` in `finiteDimensional_homology_succ_and_finrank_eq` is of a finite-dimensional space: the three hypotheses, H_{k+1}(X) through the conclusion's first conjunct, `range φ_{k+1}` inside the finite-dimensional B, `range φ_k` as the image of the finite-dimensional D. The general lemma `finrank_add_finrank_range_of_exact` asks for exactly B and D finite and derives C; it needs nothing about A or E. A probe that tries `infer_instance`, `simp` and `aesop` on `FiniteDimensional ℚ (Homology ℚ X (k + 1))` from the three instances fails, so the first conjunct carries content.

5. **Vacuity mode of the bound.** `finrank_homology_succ_add_le` alone is trivially true whenever `finrank ℚ (Homology ℚ X (k + 1)) = 0`: then `rank i_{*,k+1} ≤ dim H_{k+1}(U)` (`Submodule.finrank_le`) and `rank i_{*,k} ≤ dim H_k(U ∩ V)` (`LinearMap.finrank_range_le`) close it by `omega` (checked in scratch, three lines). Its content is therefore the upper bound on a space known to be finite-dimensional, which `finiteDimensional_homology_succ` supplies. The module docstring says finite-dimensionality "is part of every conclusion that reads a `Module.finrank`"; that is false for `finrank_homology_succ_add_le`, `finrank_homology_eq_of_disjoint` and `finrank_homology_le_of_disjoint`. Change 1 corrects the sentence; the theorems are fine as companions.

6. **Trivial proofs tried.** On the exact count and the finite-dimensionality conclusion: `infer_instance`, `simp`, `aesop` (all fail). No definition in a statement unfolds to `True`; there is no `ℕ∞` coercion; the index types are spaces of the user's choosing, and the empty case is handled correctly (`subsingleton_homology_of_isEmpty` is used for U ∩ V = ∅ in the disjoint proof and nowhere else). Every hypothesis is used: openness and the cover through upstream's exactness theorems and `twoSubsetSmallChainInclusion_homology_isIso`, disjointness through the empty overlap.

7. **Checker and axioms.** `python3 tools/check.py --no-build` on the branch: `ACCEPTED: all checks passed` (the rung is not yet in the ledger, so the checker does not name its declarations). `#print axioms` on all 21 declarations, against an olean newer than the source: each is `[propext, Classical.choice, Quot.sound]`. The module elaborates in about 5 s.

8. **Consumer fit (`circle-cylinder-homology`).** Elaborated in scratch with no `sorry`:
   - The cylinder step: from `finrank_homology_succ_add_le` with `dim H_{k+1}(U) = dim H_{k+1}(V) = b₁`, `dim H_k(U ∩ V) ≤ 2 b₀`, `b₁ ≤ rank i_{*,k+1}`, `b₀ ≤ rank i_{*,k}`, `omega` gives `dim H_{k+1}(X) ≤ b₁ + b₀`, and `finiteDimensional_homology_succ` gives finiteness.
   - The overlap: for `W₁ W₂ : Set (TopCat.of ↥(U ∩ V))` open, covering, disjoint, `finiteDimensional_homology_of_disjoint` and `finrank_homology_le_of_disjoint` apply to the space `TopCat.of ↥(U ∩ V)` directly; the consumer then transports along homeomorphisms `TopCat.of ↥W_i ≃ₜ Y × arc`.
   - The rank from a section: a general lemma `finrank_le_finrank_range_of_comp_eq_id` (p ∘ f ∘ s = id gives dim C ≤ rank f, with B finite-dimensional) and the homology form through upstream's `homologyMap_comp`, `homologyMap_id`, rewriting `s ≫ i ≫ p = 𝟙 Y`. The rung lacks this lemma; option O1 offers it here, since it is general linear algebra and the consumer needs it.

9. **Nonvacuity of step 3 in positive degree.** No space with nonzero H_1 is available to this rung without the arc cover and contractibility (rungs `circle-arc-cover`, `homology-prod-contractible`). The real exercise of the bound is the circle: `circle-cylinder-homology` at Y = point gives dim H_1(S¹) ≤ 1, and with the winding lower bound dim H_1(S¹) = 1; with rank φ₀ = 1 (upstream's `singularHomologyMap_zero_epi` for the path-connected arc U₀) the exact count gives that equality directly. Change 2 adds the cheap point test here; change 7 records the circle test as a requirement of the consumer.

10. **`erw`.** Six `erw` calls in two proofs (`sumHomologyEquiv_comp_overlap`: `biprod.lift_fst`, `biprod.lift_snd`; `sum_comp_sumHomologyEquiv_symm`: `biprod.inl_desc`, `biprod.inr_desc`, and the two `LinearMap.comp_apply, LinearMap.coprod_apply` lines). The mismatch, read from a failed `simp`: upstream's `homologyMap` produces `ℚ`-linear maps over `CommRing.toCommSemiring.toSemiring`, the file's `LinearMap.prod` over `Rat.semiring`, and the biproduct morphisms differ by the same path. Under drift an `erw` that no longer fires breaks the build; it cannot change a statement. An `erw`-free spelling of the first proof compiles (option O3). The second proof is left as is.

11. **Compile cost and drift.** Importing `Other.AlgebraicTopology.Singular.MayerVietoris` adds two upstream modules to the default build's closure, measured by an import-closure script over `HodgeLadder`, `LefschetzPort` and upstream: `Other.AlgebraicTopology.Singular.Excision.Field` (about 3 s) and the Mayer–Vietoris module (about 5 s). Library `Other` sits outside upstream's statement-import guard (`CheckStatementImports` checks only `HodgeConjecture.Statement`), so an upstream commit can change it with no statement-level check failing. The headline statements name two `Other` definitions, `subsetIntersectionToLeft` and `subsetIntersectionToRight`; everything else they name is upstream `HodgeConjecture/Definitions` (`Homology`, `homologyMap`) or `HodgeConjecture/Lemmas` (`topologicalSubsetInclusion`). The proofs also read `singularMayerVietorisShortComplex`, `singularMayerVietorisHomologySumIso`, `singularMayerVietoris_overlap_map_eq`, `singularMayerVietoris_sum_map_eq`, the three `singularMayerVietoris_exact_*` theorems and `twoSubsetSmallChainInclusion_homology_isIso`. A respelling of the overlap sign upstream would break `sumHomologyEquiv_comp_overlap` at build time; it would change no statement's truth, since the statements are phrased through `homologyMap` of the inclusions. Upstream's own proofs in that module use `set_option backward.isDefEq.respectTransparency false`; a toolchain that drops the option breaks upstream first. The singular category's "Diff at a bump" line already names `Other/AlgebraicTopology/Singular/`; change 4 names the declarations to diff.

12. **Mathlib and upstream equivalents.** Grep at the pin:
    - `finrank_add_finrank_range_of_exact`: none. Mathlib has the short exact case `ModuleCat.free_shortExact_finrank_add` and rank-nullity `LinearMap.finrank_range_add_finrank_ker` (used); no four-term count.
    - `finrank_range_le_finrank_range_prod`: none. `LinearMap.range_prod_le` is the other direction.
    - `subsingleton_homology_of_isEmpty`: derivable from Mathlib's `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` (positive degree) with `singularHomologyFunctorZeroOfTotallyDisconnectedSpace` (degree 0, the empty coproduct); upstream's `homologyEmptySubspaceIso` is relative homology. The direct proof is shorter; keep it.
    - `finiteDimensional_homology_zero_of_pathConnected`, `finrank_homology_zero_of_pathConnected`: none; they read Mathlib's `IsIso` instance for `TopCat.singularHomology₀ε`.
    - `biprod_inl_biprodIsoProd_hom`, `biprod_inr_biprodIsoProd_hom`: none; Mathlib has `ModuleCat.biprodIsoProd_inv_comp_fst`, `_snd` only.
    - Name clash: `python3 tools/pinwalk.py --clash .lake/packages/mathlib/Mathlib` reports no candidate for these names; the namespace `HodgeLadder.MayerVietoris` is new (the port has `TopCat.Sheaf.MayerVietoris`, a different namespace).

13. **Placement and layer.** `HodgeLadder/General/` fits: general singular-homology lemmas kept local (decision 0011). The ledger's placeholder module `HodgeLadder.Mayer.Vietoris.Finrank` should be replaced by the actual one. The module imports only Mathlib and upstream: layer 0 (`tools/pinwalk.py`, rule "0 for a module that imports only Mathlib or upstream"). It is not yet imported from `HodgeLadder.lean`. The branch is one commit behind `main` (`30ea512`, ext-map-cocycle); the branch changes only the Lean file, so a rebase is clean.

14. **Equality first (decision 0004).** The rung proves the exact count `finiteDimensional_homology_succ_and_finrank_eq` and the disjoint equality `finrank_homology_eq_of_disjoint` with the equivalence `homologyEquivOfDisjoint`; no scalar. The inequalities are steps toward `torus-homology-bound` (b_k(Tⁿ) ≤ n.choose k) and then the equality `finrank_cohomology_two_torus` in `torus-singular-cohomology`, which exists as an open rung.

15. **Pin drift.** Checked at the current pin `2ead713`; no drift to diff.

## Required changes

1. **Module docstring.** Replace the sentence "Finite-dimensionality enters as explicit instance hypotheses and is part of every conclusion that reads a `Module.finrank`, since `Module.finrank` is `0` on an infinite-dimensional space." by:

   > Finite-dimensionality enters as explicit instance hypotheses. `Module.finrank` is `0` on an infinite-dimensional space, so each upper bound on a `finrank` of `H_k(X)` has a companion finite-dimensionality theorem for the same space: `finiteDimensional_homology_succ` for `finrank_homology_succ_add_le`, and `finiteDimensional_homology_of_disjoint` for `finrank_homology_le_of_disjoint` and `finrank_homology_eq_of_disjoint`. The exact count carries finite-dimensionality in its conclusion.

   Append to the docstring of `finrank_homology_succ_add_le`: "Read it with `finiteDimensional_homology_succ`: for an infinite-dimensional `H_{k+1}(X)` the `finrank` is `0` and the bound is empty."

2. **Nonvacuity test of the exact count.** Add, after `finrank_homology_zero_of_pathConnected` (compiled in scratch against the candidate, about 6 s):

   ```lean
   /-- Rational singular homology of a totally disconnected space vanishes in positive degree. -/
   theorem subsingleton_homology_succ_of_totallyDisconnected (Y : TopCat.{0})
       [TotallyDisconnectedSpace Y] (n : ℕ) : Subsingleton (Homology ℚ Y (n + 1)) :=
     ModuleCat.isZero_iff_subsingleton.mp
       (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
         (ModuleCat.{0} ℚ) (n + 1) (ModuleCat.of ℚ ℚ) Y (by omega))

   /-- **Nonvacuity test of the exact count.** For the point covered by `univ` twice, the count at
   `k = 0` reads `0 + 0 + rank φ₀ = 0 + 0 + 1`, so the overlap map `(i_*, -j_*)` on `H_0` has rank
   one. -/
   theorem finrank_range_overlap_zero_punit :
       finrank ℚ (LinearMap.range
         (LinearMap.prod (homologyMap ℚ 0 (subsetIntersectionToLeft (TopCat.of PUnit.{1})
             Set.univ Set.univ))
           (-homologyMap ℚ 0 (subsetIntersectionToRight (TopCat.of PUnit.{1})
             Set.univ Set.univ)))) = 1 := by
     have hU : IsOpen (Set.univ : Set (TopCat.of PUnit.{1})) := isOpen_univ
     have hp : PathConnectedSpace
         (TopCat.of ↥((Set.univ : Set (TopCat.of PUnit.{1})) ∩ Set.univ)) :=
       { nonempty := ⟨⟨PUnit.unit, trivial, trivial⟩⟩
         joined := fun x y => by rw [Subsingleton.elim x y] }
     have := finiteDimensional_homology_zero_of_pathConnected
       (TopCat.of ↥((Set.univ : Set (TopCat.of PUnit.{1})) ∩ Set.univ))
     have := subsingleton_homology_succ_of_totallyDisconnected
       (TopCat.of ↥(Set.univ : Set (TopCat.of PUnit.{1}))) 0
     have := subsingleton_homology_succ_of_totallyDisconnected (TopCat.of PUnit.{1}) 0
     obtain ⟨-, h⟩ := finiteDimensional_homology_succ_and_finrank_eq hU hU (Set.union_self _) 0
     have h1 := Submodule.finrank_le (LinearMap.range
       (LinearMap.prod (homologyMap ℚ (0 + 1) (subsetIntersectionToLeft (TopCat.of PUnit.{1})
           Set.univ Set.univ))
         (-homologyMap ℚ (0 + 1) (subsetIntersectionToRight (TopCat.of PUnit.{1})
           Set.univ Set.univ))))
     have e0 : finrank ℚ (Homology ℚ (TopCat.of PUnit.{1}) (0 + 1)) = 0 :=
       finrank_zero_of_subsingleton
     have e1 : finrank ℚ (Homology ℚ (TopCat.of ↥(Set.univ : Set (TopCat.of PUnit.{1}))) (0 + 1)) =
       0 := finrank_zero_of_subsingleton
     have e2 := finrank_homology_zero_of_pathConnected
       (TopCat.of ↥((Set.univ : Set (TopCat.of PUnit.{1})) ∩ Set.univ))
     rw [Module.finrank_prod] at h1
     omega
   ```

   Add both to "Main results" in the module docstring. A count missing either rank term gives a different value here, so the test fails on a wrong statement.

3. **Conventions row.** Add to the register of `docs/conventions.md`:

   > | Singular Mayer–Vietoris (homology) | upstream `Other/AlgebraicTopology/Singular/MayerVietoris.lean`: `singularMayerVietorisShortComplex` (the pushout short complex `C(U ∩ V) → C(U) ⊞ C(V) → C(U) + C(V)`), `singularMayerVietorisHomologySumIso` (`mapBiprod` of the homology functor), `singularMayerVietoris_overlap_map_eq`, `singularMayerVietoris_sum_map_eq`, `singularMayerVietorisBoundary` (the short exact sequence's `δ` after `(twoSubsetSmallHomologyIso …).inv`); this repository's `HodgeLadder.MayerVietoris.sumHomologyEquiv` (that iso, then `ModuleCat.biprodIsoProd`) | overlap map `x ↦ (i_* x, −j_* x)` (`sumHomologyEquiv_comp_overlap`), sum map `(x, y) ↦ (ι_U)_* x + (ι_V)_* y` with no sign (`sum_comp_sumHomologyEquiv_symm`); the same as `Hatcher2002` §2.2, Φ(x) = (x, −x), Ψ(x, y) = x + y (recalled, unverified); the sign of the connecting map is unused | none for rung `mayer-vietoris-finrank`: it uses only ranks and bijectivity, and (i_*, −j_*) and (i_*, j_*) differ by the automorphism (a, b) ↦ (a, −b), so they have the same rank; no statement names the boundary map. A later rung that states an identity through `singularMayerVietorisBoundary` depends on its sign and must extend this row | read from source; checked in scratch (red team 2026-11-27, `mayer-vietoris-finrank`) |

4. **Gaps row and pin-walk text.** In `docs/gaps.md`, category "Singular homology, cohomology and simplicial cochains", append to the "Diff at a bump" line, before the Tau Ceti clause:

   > ; in `Other/AlgebraicTopology/Singular/MayerVietoris.lean` (library `Other`, outside upstream's statement-import guard) diff `subsetIntersectionToLeft`, `subsetIntersectionToRight` (named in the statements of `HodgeLadder.General.MayerVietorisRank`), `singularMayerVietorisShortComplex`, `singularMayerVietorisHomologySumIso`, `singularMayerVietoris_overlap_map_eq`, `singularMayerVietoris_sum_map_eq`, `singularMayerVietoris_exact_sum`, `singularMayerVietoris_exact_ambient`, `singularMayerVietoris_exact_overlap` and `twoSubsetSmallChainInclusion_homology_isIso`; Mathlib `Algebra/Category/ModuleCat/Free.lean` and `LinearAlgebra/Dimension/` for a four-term rank count

   and add the row (first in the table, layer 0):

   > | `HodgeLadder.MayerVietoris.finrank_add_finrank_range_of_exact` (rank count along four exact terms over a field), `finrank_range_le_finrank_range_prod` (rank of a component at most the rank of the pair), `finrank_le_finrank_range_of_comp_eq_id` if option O1 is taken; `sumHomologyEquiv`, `sumHomologyEquiv_comp_overlap`, `sum_comp_sumHomologyEquiv_symm`, `biprod_inl_biprodIsoProd_hom`, `biprod_inr_biprodIsoProd_hom`, `finiteDimensional_homology_succ_and_finrank_eq`, `finiteDimensional_homology_succ`, `finrank_homology_succ_add_le` (dimension counts from upstream's singular Mayer–Vietoris); `subsingleton_homology_of_isEmpty`, `subsingleton_homology_succ_of_totallyDisconnected`, `finiteDimensional_homology_zero_of_pathConnected`, `finrank_homology_zero_of_pathConnected`; `bijective_sumChainMap_homology_of_disjoint`, `bijective_coprod_homologyMap_of_disjoint`, `homologyEquivOfDisjoint` with `_apply`, `finiteDimensional_homology_of_disjoint`, `finrank_homology_eq_of_disjoint`, `finrank_homology_le_of_disjoint` (a disjoint open cover, every degree) | `HodgeLadder.General.MayerVietorisRank` | 0 | upstream's Mayer–Vietoris (library `Other`) proves exactness and states no dimension count; Mathlib has the short exact count `ModuleCat.free_shortExact_finrank_add` and rank-nullity, no four-term count; the empty-space vanishing also follows from Mathlib's `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` with `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`, the direct proof is shorter; Mathlib has `ModuleCat.biprodIsoProd_inv_comp_fst`, `_snd` and no `inl`, `inr` form; rung `mayer-vietoris-finrank` | 2026-11-27 |

5. **Root import, ledger, roadmap.** Add `public import HodgeLadder.General.MayerVietorisRank` to `HodgeLadder.lean`. Ledger entry `mayer-vietoris-finrank`: `"status": "checked"`, `"module": "HodgeLadder.General.MayerVietorisRank"`, `"contributors": ["claude-code"]`, `"declarations"` the 21 names of the candidate under `HodgeLadder.MayerVietoris.` (`finrank_add_finrank_range_of_exact`, `sumHomologyEquiv`, `sumHomologyEquiv_comp_overlap`, `finiteDimensional_homology_succ_and_finrank_eq`, `finrank_range_le_finrank_range_prod`, `finiteDimensional_homology_succ`, `finrank_homology_succ_add_le`, `subsingleton_homology_of_isEmpty`, `bijective_sumChainMap_homology_of_disjoint`, `biprod_inl_biprodIsoProd_hom`, `biprod_inr_biprodIsoProd_hom`, `sum_comp_sumHomologyEquiv_symm`, `bijective_coprod_homologyMap_of_disjoint`, `homologyEquivOfDisjoint`, `homologyEquivOfDisjoint_apply`, `finiteDimensional_homology_of_disjoint`, `finrank_homology_eq_of_disjoint`, `finrank_homology_le_of_disjoint`, `finiteDimensional_homology_zero_of_pathConnected`, `finrank_homology_zero_of_pathConnected`, `finrank_homology_zero_bool`) plus `subsingleton_homology_succ_of_totallyDisconnected` and `finrank_range_overlap_zero_punit` from change 2 and any taken from options O1 and O2. Note:

   > Checked 2026-11-27. Exact count finiteDimensional_homology_succ_and_finrank_eq: for an open cover X = U ∪ V with H_{k+1}(U), H_{k+1}(V), H_k(U ∩ V) finite-dimensional over ℚ, H_{k+1}(X) is finite-dimensional and dim H_{k+1}(X) + rank φ_{k+1} + rank φ_k = dim H_{k+1}(U) + dim H_{k+1}(V) + dim H_k(U ∩ V), φ_n = (i_*, −j_*); the sketch's bound finrank_homology_succ_add_le follows, with finiteness from finiteDimensional_homology_succ. Disjoint cover: homologyEquivOfDisjoint, H_k(U) × H_k(V) ≃ H_k(X) by the sum of the inclusions, every degree (degree 0 through HomologicalComplex.epi_homologyMap_of_epi_of_not_rel). Sign: upstream's (i, −j) enters ranks only; the boundary map appears in no statement (conventions row "Singular Mayer–Vietoris (homology)"). Nonvacuity: finrank_homology_zero_bool (dim H_0(Bool) = 2 from the disjoint equality) and finrank_range_overlap_zero_punit (rank φ₀ = 1 read off the exact count at the point). Positive-degree exercise deferred to circle-cylinder-homology at Y = point (dim H_1(S¹) ≤ 1). Imports upstream Other.AlgebraicTopology.Singular.MayerVietoris (library Other, outside upstream's statement-import guard; about 8 s added to the default build): drift-check its declarations at each pin bump (docs/gaps.md, singular category). Red team: docs/sketches/mayer-vietoris-finrank.redteam.md, pass with changes.

   `docs/roadmap.md` row: status `checked`, last column "exact Mayer–Vietoris count with finite dimension; disjoint covers as an equivalence in every degree".

6. **References.** In `docs/references.md`, row `Hatcher2002`, add §2.2 to the locator column and append to the content column: "; the Mayer–Vietoris sequence for X = int A ∪ int B with Φ(x) = (x, −x) and Ψ(x, y) = x + y (§2.2; recalled, unverified)".

7. **Consumer test.** Append to the ledger note of `circle-cylinder-homology`: "Nonvacuity requirement (red team mayer-vietoris-finrank, change 7): instantiate at Y = point to get FiniteDimensional ℚ (Homology ℚ (TopCat.of UnitAddCircle) 1) and dim ≤ 1; this is the first positive-degree exercise of finrank_homology_succ_add_le. The rank bound from a section needs p ∘ f ∘ s = id ⇒ dim ≤ rank f (finrank_le_finrank_range_of_comp_eq_id, mayer-vietoris-finrank option O1, or a local copy)."

8. **Rebase.** Rebase `track/mayer-vietoris-finrank` onto `main` `30ea512` before the pull request; only the Lean file differs, so no conflict is expected, and the ledger and roadmap edits of change 5 go on top.

## Options (recommended, not required)

- **O1 (finding 8).** The section lemma, compiled in scratch:

  ```lean
  /-- **Rank from a section.** If `p ∘ f ∘ s = id`, then `dim C ≤ rank f`. -/
  theorem finrank_le_finrank_range_of_comp_eq_id {K A B C : Type*} [Field K] [AddCommGroup A]
      [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
      (s : C →ₗ[K] A) (f : A →ₗ[K] B) (p : B →ₗ[K] C) (h : p ∘ₗ f ∘ₗ s = LinearMap.id)
      [FiniteDimensional K B] :
      finrank K C ≤ finrank K (LinearMap.range f) := by
    have hle : LinearMap.range (p ∘ₗ f ∘ₗ s) ≤ (LinearMap.range f).map p := by
      rintro _ ⟨x, rfl⟩
      exact ⟨f (s x), ⟨s x, rfl⟩, rfl⟩
    rw [h, LinearMap.range_id] at hle
    have := Submodule.finrank_mono hle
    rw [finrank_top] at this
    exact this.trans (Submodule.finrank_map_le _ _)
  ```

  Its homology use is `apply finrank_le_finrank_range_of_comp_eq_id (homologyMap ℚ k s) _ (homologyMap ℚ k p)` followed by `rw [← homologyMap_comp, ← homologyMap_comp, Category.assoc, h, homologyMap_id]` for `h : s ≫ subsetIntersectionToLeft X U V ≫ p = 𝟙 Y` (checked).

- **O2 (drift pins).** The two `Other` names in the statements, pinned by `rfl` (compiled in scratch):

  ```lean
  /-- Pin: upstream's `subsetIntersectionToLeft` is the inclusion `U ∩ V → U`. -/
  theorem subsetIntersectionToLeft_apply (x : ↥(U ∩ V)) :
      ((subsetIntersectionToLeft X U V x : ↥U) : X) = x := rfl
  /-- Pin: upstream's `subsetIntersectionToRight` is the inclusion `U ∩ V → V`. -/
  theorem subsetIntersectionToRight_apply (x : ↥(U ∩ V)) :
      ((subsetIntersectionToRight X U V x : ↥V) : X) = x := rfl
  ```

  (with `variable (X : TopCat.{0}) (U V : Set X)` in scope). A respelling upstream then breaks the build at the pin.

- **O3 (`erw`-free overlap proof).** In `sumHomologyEquiv_comp_overlap`, each branch compiles as

  ```lean
  · have := congrArg (fun φ => ModuleCat.Hom.hom (φ ≫ biprod.fst) x) h
    rw [← hfst] at this
    exact this.trans (congrArg (fun φ => ModuleCat.Hom.hom φ x) (biprod.lift_fst _ _))
  ```

  and the same with `snd`. It moves the instance-path unification into `exact`; its sensitivity to drift is the same, and it has no `erw`. Plain `rw [biprod.lift_fst]` and `simp only [biprod.lift_fst]` fail (instance path `CommRing.toCommSemiring.toSemiring` against `Rat.semiring`).

## What was tried

- `#print axioms` on all 21 declarations (standard three each); `python3 tools/check.py --no-build` (exit 0).
- The consumer shape of step 5 (cylinder bound, overlap through the disjoint theorems on `TopCat.of ↥(U ∩ V)`, rank from a section): compiled.
- The vacuity mode of the bound under `finrank = 0`: compiled in three lines (finding 5). `infer_instance`, `simp`, `aesop` on the finite-dimensionality conclusion: fail.
- Point test of the exact count: compiled after three repairs (a duplicated `rw` target because U = V, a `let` that `omega` treated as a separate atom, a missing `Subsingleton` instance for H_1 of the point).
- `erw` replacements: `rw`, `simp only`, `rw [Category.assoc, …]` fail; the `exact … .trans` form compiles.
- Elaboration time: the candidate about 5 s; upstream `Excision.Field` about 3 s and `MayerVietoris` about 5 s with `lake env lean`.
- Import closure: a script over the import graph lists the two upstream modules new to the default build.
