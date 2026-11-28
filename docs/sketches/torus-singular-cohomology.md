# Sketch: `torus-singular-cohomology`

Rung `torus-singular-cohomology` (issue #230, T1 node C6, `docs/notes/2026-11-27-t1-plan.md`). Thinker session one, 2026-11-27, at `main` `b9ae5a1` (upstream `2ead713`, Lean and Mathlib `v4.35.0-rc4`). This is a plan with elaborated statements; it proves nothing.

## Statement

**Plain words.** On the real torus Tⁿ = `UnitAddTorus (Fin n)`, let aᵢ ∈ H¹(Tⁿ; ℚ) be the winding class of x ↦ exp(2πi xᵢ). For n ≥ 2 the aᵢ form a basis of H¹, so dim H¹ = n. For every n the products aᵢ ⌣ aⱼ with i < j form a basis of H², so dim H² = n(n − 1)/2. Each product is pinned by its value on the coordinate 2-torus T_kl (k ≠ l): ⟨aᵢ ⌣ aⱼ, T_kl⟩ = [i = k][j = l] − [i = l][j = k]. The ledger's cases n = 2 and n = 4 are instances. Cohomology is upstream's `AlgebraicTopology.Singular.Cohomology ℚ`, the cup is the ladder's `HodgeLadder.Cup.cupSing` (Tau Ceti, front face times back face), the winding class is `HodgeLadder.Cup.windingClass`, the evaluation is `HodgeLadder.Cup.torusEval`.

**Proposed Lean** (namespace `HodgeLadder.Torus`; elaborated with `sorry` proofs against the current build, scratch file deleted):

```lean
abbrev torus (n : ℕ) : TopCat.{0} := TopCat.of (UnitAddTorus (Fin n))
noncomputable def coordChar {n : ℕ} (i : Fin n) : C(torus n, ℂ) :=
  ⟨fun x => ((AddCircle.toCircle (x i) : Circle) : ℂ),
    continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp (continuous_apply i))⟩
theorem coordChar_ne_zero {n : ℕ} (i : Fin n) (x : torus n) : coordChar i x ≠ 0
noncomputable def coordWinding {n : ℕ} (i : Fin n) : AlgebraicTopology.Singular.Cohomology ℚ (torus n) 1 :=
  Cup.windingClass (coordChar i) (coordChar_ne_zero i)
noncomputable def coordTorus {n : ℕ} (k l : Fin n) : C(ℝ × ℝ, torus n)  -- (s,t) ↦ update (update 0 k s) l t
theorem coordTorus_one_left {n : ℕ} (k l : Fin n) (t : ℝ) : coordTorus k l (1, t) = coordTorus k l (0, t)
theorem coordTorus_one_right {n : ℕ} (k l : Fin n) (s : ℝ) : coordTorus k l (s, 1) = coordTorus k l (s, 0)
theorem torusEval_coordTorus_cup {n : ℕ} {k l : Fin n} (hkl : k ≠ l) (i j : Fin n) :
    Cup.torusEval (coordTorus_one_left k l) (coordTorus_one_right k l)
        (Cup.cupSing (torus n) (coordWinding i) (coordWinding j) 2 rfl) =
      (if i = k ∧ j = l then 1 else 0) - (if i = l ∧ j = k then 1 else 0)
noncomputable def coordCup {n : ℕ} (p : {p : Fin n × Fin n // p.1 < p.2}) :
    AlgebraicTopology.Singular.Cohomology ℚ (torus n) 2 :=
  Cup.cupSing (torus n) (coordWinding p.1.1) (coordWinding p.1.2) 2 rfl
theorem linearIndependent_coordWinding {n : ℕ} (hn : 2 ≤ n) : LinearIndependent ℚ (coordWinding (n := n))
theorem span_coordWinding {n : ℕ} (hn : 2 ≤ n) : Submodule.span ℚ (Set.range (coordWinding (n := n))) = ⊤
theorem finrank_cohomology_one_torus {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ (torus n) 1) = n
theorem linearIndependent_coordCup (n : ℕ) : LinearIndependent ℚ (coordCup (n := n))
theorem span_coordCup (n : ℕ) : Submodule.span ℚ (Set.range (coordCup (n := n))) = ⊤
theorem finrank_cohomology_two_torus (n : ℕ) :
    Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ (torus n) 2) = n.choose 2
```

The headline results are the `LinearIndependent` and `span = ⊤` pairs; the `finrank` equalities follow from them. `Module.finrank` is 0 on an infinite-dimensional space, so a `finrank` statement alone would be weaker than it reads (vacuity guard). The statement covers all n, which contains the ledger's n = 2, 4.

## Why the ladder needs it

`weil-surface-reduction` takes `finrank ℂ H_dR^1(A) = 4` and "H²_dR spanned by cups of H¹ classes" as hypotheses. `elliptic-curve-cohomology` (C7) and `elliptic-square-cohomology` (C8) produce them for E and E × E by transporting this rung along E(ℂ) ≅ T², (E × E)(ℂ) ≅ T⁴, Ψ and `deRhamBaseChangeEquiv`. `weil-elliptic-square-nonzero` (F2) needs the independence half in degree 2; `weil-surface` (G3) and `elliptic-product-test` reuse the rung unchanged. Lower bounds are already in reach (`torusEval`); the span (upper bound) is the missing content.

## Proof idea

Route: upper bounds in homology by upstream's singular Mayer–Vietoris and homotopy invariance, then the universal coefficient equivalence, then independence from `torusEval`. Dimension count plus independence gives the span, so no Künneth formula and no cross product is needed.

1. **Arcs.** In S¹ = `UnitAddCircle`, U₀ = {↑0}ᶜ and V₀ = {↑(1/2)}ᶜ are open, cover S¹ and are contractible (homeomorphic to open intervals through `AddCircle.openPartialHomeomorphCoe`). U₀ ∩ V₀ = W₁ ∪ W₂, the images of (0, 1/2) and (1/2, 1): open, disjoint, contractible.
2. **Contractible factor.** For contractible W, H_k(Y × W; ℚ) ≅ H_k(Y; ℚ): Y × W ≃ₕ Y × PUnit ≃ₜ Y, then `AlgebraicTopology.singularChainHomotopyEquivOfHomotopyEquiv`.
3. **Mayer–Vietoris count.** For an open cover X = U ∪ V and i : U ∩ V → U, exactness at H_{k+1}(U) ⊕ H_{k+1}(V), at H_{k+1}(X) and at H_k(U ∩ V) gives dim H_{k+1}(X) + rank i_{*,k+1} + rank i_{*,k} ≤ dim H_{k+1}(U) + dim H_{k+1}(V) + dim H_k(U ∩ V), with H_{k+1}(X) finite-dimensional. The overlap map is (i_*, −j_*) under `singularMayerVietorisHomologySumIso`, so its rank is at least rank i_*.
4. **Disjoint cover.** If U ∩ V = ∅, the sum map H_k(U) ⊕ H_k(V) → H_k(X) is onto: for k ≥ 1 by exactness at H_k(X) (the boundary lands in H_{k−1}(∅) = 0); for k = 0 by `HomologicalComplex.epi_homologyMap_of_epi_of_not_rel` on the epi X₂ → X₃ of the short exact sequence, then `twoSubsetSmallHomologyIso`.
5. **Cylinder step.** For X = Y × S¹ with U = univ ×ˢ U₀, V = univ ×ˢ V₀: dim H_j(U), dim H_j(V) = b_j(Y) (steps 1, 2, `Homeomorph.Set.prod`); dim H_j(U ∩ V) ≤ 2 b_j(Y) (step 4 on the two pieces). With s(y) = (y, ↑(1/4)) ∈ U ∩ V and the projection p : U → Y, p ∘ i ∘ s = id, so rank i_{*,j} ≥ b_j(Y) by `homologyMap_comp`, `homologyMap_id`. Step 3 gives b_{k+1}(Y × S¹) ≤ b_{k+1}(Y) + b_k(Y). No homotopy-invariance statement about the restriction maps is needed; only dimensions enter.
6. **Induction.** T^{n+1} ≃ₜ Tⁿ × S¹ (`Fin.appendHomeomorph n 1`, `Homeomorph.funUnique`). Base T⁰ = point: H_k = 0 for k ≥ 1 (`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`); H₀(Tⁿ) ≅ ℚ for all n (`AddCircle.pathConnectedSpace`, the `IsIso` instance of `TopCat.singularHomology₀ε`). Pascal's rule gives b_k(Tⁿ) ≤ n.choose k, with finite dimension.
7. **Cohomology bound.** `cohomologyEquivDualHomology` and `Subspace.dual_finrank_eq`: dim H^k(Tⁿ) = b_k ≤ n.choose k, finite-dimensional.
8. **Duality on coordinate tori.** g = coordChar i satisfies g ∘ T_kl = exp(2πi π) with π = s, t or 0; `simplexIncrement_torus` and `val_windingTC_of_increment` give the edge values π(1,0) − π(0,0) and π(1,1) − π(1,0); `torusEval_cupSing` turns them into the determinant formula of the statement.
9. **Independence and span.** If Σ c_ij (aᵢ ⌣ aⱼ) = 0 over i < j, evaluating on T_kl gives c_kl = 0. If Σ cᵢ aᵢ = 0, cup on the right with a_m (m ≠ k, needs n ≥ 2) and evaluate on T_km: c_k = 0 (needs `cupSing` additive in the first slot, from its definition as a composite of linear maps). Then step 7 and `LinearIndependent.span_eq_top_of_card_eq_finrank'`, with #{(i, j) : i < j} = n.choose 2.

### Where to state it (caller question 3)

On `UnitAddTorus (Fin n)`. The 𝔾ₘⁿ route gives no saving: the checked 𝔾ₘ² rungs prove lower bounds only, (ℂˣ)ⁿ is homotopy equivalent to Tⁿ and needs the same upper bound, and E(ℂ) is homeomorphic to T², which (ℂˣ)² is not. Stating on E or E × E needs objects that do not exist yet (C3) and ties topology to algebraic geometry. Consumers reach E through a transport corollary (sub-rung `winding-class-pullback`): for h : Y ≃ₜ Tⁿ, the winding classes of coordChar i ∘ h form a basis of H¹(Y), and their cups one of H²(Y).

## What Mathlib has

Grep-checked at the pin. Mathlib: `UnitAddTorus`, `UnitAddCircle`, `AddCircle.toCircle`, `AddCircle.toCircle_apply_mk`, `AddCircle.continuous_toCircle`, `AddCircle.pathConnectedSpace`, `AddCircle.openPartialHomeomorphCoe`, `OpenPartialHomeomorph.toHomeomorphSourceTarget`, `Convex.contractibleSpace`, `ContractibleSpace.hequiv_unit`, `ContinuousMap.HomotopyEquiv.prodCongr`, `Homeomorph.prodPUnit`, `Homeomorph.Set.prod`, `Fin.appendHomeomorph`, `Homeomorph.funUnique`, `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`, `TopCat.singularHomology₀Iso`, `TopCat.singularHomology₀ε`, `AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`, `HomologicalComplex.epi_homologyMap_of_epi_of_not_rel`, `Subspace.dual_finrank_eq`, `LinearIndependent.span_eq_top_of_card_eq_finrank'`.

Upstream (`HodgeConjecture` and library `Other`): `AlgebraicTopology.Singular.Homology`, `homologyMap`, `homologyMap_comp`, `homologyMap_id`, `cohomologyMap`, `cohomologyEquivDualHomology`, `cohomologyEquivDualHomology_cohomologyMap`, `AlgebraicTopology.singularChainHomotopyEquivOfHomotopyEquiv`; in `Other.AlgebraicTopology.Singular.MayerVietoris`: `singularMayerVietorisShortComplex_shortExact`, `twoSubsetSmallHomologyIso`, `singularMayerVietorisBoundary`, `singularMayerVietoris_exact_sum`, `singularMayerVietoris_exact_ambient`, `singularMayerVietoris_exact_overlap`, `singularMayerVietorisHomologySumIso`, `singularMayerVietoris_overlap_map_eq`, `subsetIntersectionToLeft`. That module is not compiled by the ladder's default build yet; `lake build Other.AlgebraicTopology.Singular.MayerVietoris` finished in seconds on this tree.

Ladder: `HodgeLadder.Cup.windingClass`, `windingTC`, `val_windingTC_of_increment`, `simplexIncrement_torus`, `torusEval`, `torusEval_cupSing`, `cupSing`, `cupSing_gradedComm`, `torus_h0`, `torus_h1`, `torus_h2`. The port vendors Tau Ceti's `SSet.eilenbergZilberHomotopyEquiv` (both homotopies), the input of the Künneth fallback.

Differences from the literature: singular homology here uses unnormalized chains (Mathlib), harmless for dimensions. `finrank` is 0 on infinite-dimensional spaces, hence the finite-dimensionality conclusions in steps 3 to 7.

## What is missing

No dimension count from Mayer–Vietoris, no homology of a product with a contractible factor, no homology computation of any torus or circle, no algebraic Künneth formula (grep for Künneth returns nothing in Mathlib, upstream or the port), no naturality or additivity lemma for `windingClass`, no `cupSing` additivity lemma.

## Sub-rungs

| Order | Id | Statement (one line) | Size | depends_on | Reuses |
|---|---|---|---|---|---|
| 1 | `circle-arc-cover` | U₀ = {↑0}ᶜ, V₀ = {↑(1/2)}ᶜ open, cover, contractible; U₀ ∩ V₀ = W₁ ∪ W₂ open, disjoint, contractible; ↑(1/4) ∈ W₁ | small | none | `openPartialHomeomorphCoe`, `Convex.contractibleSpace` |
| 1 | `homology-prod-contractible` | `Nonempty (Homology ℚ (TopCat.of (Y × W)) k ≅ Homology ℚ Y k)` for `[ContractibleSpace W]` | small | none | `singularChainHomotopyEquivOfHomotopyEquiv` |
| 1 | `mayer-vietoris-finrank` | `finrank_homology_succ_add_le` (step 3) and `finrank_homology_le_of_disjoint` (step 4), both elaborated | medium | none | upstream MV |
| 2 | `circle-cylinder-homology` | `finrank_homology_prod_circle_le`: H_{k+1}(Y × S¹) finite, dim ≤ b_{k+1}(Y) + b_k(Y), given both finite | medium | the three above | `Homeomorph.Set.prod` |
| 3 | `torus-homology-bound` | `finiteDimensional_homology_torus n k`, `finrank_homology_torus_le n k : … ≤ n.choose k` | small | `circle-cylinder-homology` | `Fin.appendHomeomorph` |
| 1 | `torus-winding-duality` | `coordChar`, `coordWinding`, `coordTorus` and `torusEval_coordTorus_cup` | medium | `winding-torus-cup` | `simplexIncrement_torus` |
| 4 | `torus-singular-cohomology` | this rung: the six theorems above | medium | `torus-homology-bound`, `torus-winding-duality` | `cohomologyEquivDualHomology` |
| 5 | `winding-class-pullback` | `cohomologyMap ℚ 1 f (windingClass g hg) = windingClass (g.comp f.hom) _`; `windingClass (g * g') = windingClass g + windingClass g'`; for `rot x = ![-x 1, x 0]`, rot^* a₀ = −a₁, rot^* a₁ = a₀; transport along h : Y ≃ₜ Tⁿ | medium | `torus-singular-cohomology` | `logIncrement_of_exp` |

Every Lean statement in the table elaborated in scratch with `sorry` proofs, except the W₁, W₂ clauses of `circle-arc-cover` (only `ContractibleSpace ↥({a}ᶜ : Set UnitAddCircle)` was elaborated); the transport elaborated as `span_windingClass_of_homeomorph`. "Needs object" applies only downstream (C7, C8 instantiate Y = E(ℂ), (E × E)(ℂ)); nothing here mentions E. First dispatch: `mayer-vietoris-finrank` (the only piece touching an API not yet used by the ladder), in parallel with `torus-winding-duality`, `circle-arc-cover`, `homology-prod-contractible`. Total about seven sessions.

`rot` is multiplication by i in the basis (ω₁, ω₂) = (c, ic): i(sω₁ + tω₂) = −tω₁ + sω₂. C7 reads x₁ ↦ −x₂, x₂ ↦ x₁ from it.

### Kill criteria

| Event | Consequence |
|---|---|
| `mayer-vietoris-finrank` released twice (upstream MV maps do not meet upstream `homologyMap` on subspace inclusions up to `change`) | switch to Künneth: `SSet.eilenbergZilberHomotopyEquiv`, `TopCat.toSSet` on products, plus algebraic Künneth over ℚ (absent; large); one thinker session on it |
| Künneth route without a stated route after that session | the plan's criterion (§7) fires: F1 and G3 blocked, `weil-surface-reduction` stays the checked form of T1 |
| `circle-cylinder-homology` over 10 minutes of kernel time | split the subtype bookkeeping (U ∩ V inside Y × S¹) into its own rung |
| pin bump changes `Other.AlgebraicTopology.Singular.MayerVietoris` | red-team drift check; library `Other` sits outside upstream's statement-import guard |

### Sign and normalization risks

| Risk | Where it enters | How it is pinned |
|---|---|---|
| orientation of T_kl | the order (k, l): T_lk = T_kl ∘ swap evaluates to the negative | `torusEval_coordTorus_cup` is an exact formula with both orders; conventions row "Torus cycle and winding classes" |
| order of generators of H² | basis aᵢ ⌣ aⱼ with i < j; aⱼ ⌣ aᵢ = −aᵢ ⌣ aⱼ (`cupSing_gradedComm`, (−1)^{1·1}) | span and rank are insensitive; F2's elements carry explicit signs and must use `coordCup` |
| Ψ in degree (1, 1) | Ψ(x ∪ y) = −cupSing(Ψx)(Ψy) (conventions row "Sheaf–singular comparison Ψ") | span transport is insensitive (−1 is a unit); eigenspace membership in F2 is too, since f^* commutes with Ψ |
| winding direction and rational retraction | exp(2πi xᵢ) winds +1 along the front edge; increments here are integers, read exactly by `rationalProjection` | edge values are exact; rows "Winding number", "Orientation against winding" |
| rot and the CM sign | ω₂ = iω₁ versus ω₂ = −iω₁ swaps the signs of rot^* | C7 states only (ellipticI^*)² = −1 for T1, independent of this choice |
| Mayer–Vietoris sign (i, −j) | the overlap map | enters ranks only |

## Sources

- Mayer–Vietoris, homotopy invariance, H*(Tⁿ) as an exterior algebra and Künneth: `Hatcher2002` §2.2, §3.2, §3.B (section locators recalled, unverified).
- E(ℂ) ≅ ℂ/Λ (for the transport): `Silverman2009` ch. VI; abelian surfaces as ℂ²/Λ: `Mumford1970` §1 (locators unverified).
- Complex orientation (v, iv): `MilnorStasheff1974` (section unverified).
- The induction b_k(Y × S¹) = b_k(Y) + b_{k−1}(Y) is standard; the inequality form used here is derived in this sketch (unverified against a text).
