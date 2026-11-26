# Sketch: `local-class-product`

Date: 2026-11-26. Front `cup`, decisions 0008 and 0009, rung 5. Companion sketch: `docs/sketches/cycle-class-multiplicative.md` (global assembly, tests, kill criterion). This is a plan. Nothing in it is checked, and each identity below is a target.

## Statement

**Plain words.** Let a, b ≥ 0, c = a + b, and split ℂ^c = ℂ^a × ℂ^b by `Fin.append` (first a complex coordinates, then b). Let u_k ∈ H^{2k}(ℂ^k, ℂ^k ∖ 0; ℚ) be upstream's normalized local class `normalizedRelativeCoclass (standardComplexLocalClass ℚ k) _`, the class that pairs to 1 with upstream's complex orientation class. Pull u_a back along the first block projection to H^{2a}(ℂ^c, A) with A = {z' ≠ 0}, and u_b along the second to H^{2b}(ℂ^c, B) with B = {z'' ≠ 0}, so A ∪ B = ℂ^c ∖ 0. Then the relative cup product of the two pullbacks is u_c, with sign +. In a holomorphic chart adapted to two transversal submanifolds Z, W of codimensions a, b, the same identity says: the relative cup of the normal-projection coclasses of Z and W is the normal-projection coclass of Z ∩ W.

**Upstream's normalization at the pin** (`docs/cycle-class.md`): the orientation of ℂ^k is `complexRealHomeomorph` (Re z₀, Im z₀, Re z₁, …); the reference cycle is `standardLocalClass` (affine simplex with vertices e₀, …, e_{d−1}, (−1, …, −1)) moved by it (`standardComplexLocalClass`). Its edge matrix has determinant (−1)^d (d + 1) (computed by hand for every d, unverified in Lean), so it is the standard orientation exactly when d is even, which matches the register row "Complex orientation of ℂ^p". Mathlib has no local orientation of its own here, so there is no definition to differ from.

**Literature.** For open A, B ⊆ X the relative cup H^k(X, A) × H^l(X, B) → H^{k+l}(X, A ∪ B) [`Hatcher2002` §3.2]. The Thom class of a product of oriented bundles is the cross product of the Thom classes, and the complex orientation comes from the real basis (v₁, iv₁, v₂, iv₂, …) [`MilnorStasheff1974` §§10, 14; section numbers unverified]. Cross products, shuffle maps, and their evaluation [`Hatcher2002` §3.B, `Bredon1993` ch. VI; chapter numbers unverified].

**Proposed Lean, model form.** Elaborated with `lake env lean` on a scratch file inside the worktree (deleted). Upstream's `Other.AlgebraicTopology.Singular.Excision.Triad` and the three `Cap` files it needs are not built in the shared cache, so they were compiled from copies; a prover's `lake build` builds them. The statement uses upstream's triad cap product, so it needs no new definition; the cup form follows from the adjunction in `triad-relative-cup` and `normalizedRelativeCoclass_unique`.

```lean
-- setA a b = {z | (fun i : Fin a => z (Fin.castAdd b i)) ≠ 0}, setB a b likewise with Fin.natAdd a,
-- subsets of Fin (a + b) → ℂ; projA, projB the block projections as maps of pairs to
-- puncturedPair ℂ a and puncturedPair ℂ b; u k = normalizedRelativeCoclass
-- (standardComplexLocalClass ℚ k) (standardComplexLocalClass_ne_zero k); orient a b =
-- standardComplexLocalClass ℚ (a + b) moved to (ℂ^{a+b}, setA ∪ setB) by the identity
-- (setA ∪ setB = {0}ᶜ) and recast to degree 2 * a + 2 * b by Nat.mul_add.
theorem local_class_cross_cap (a b : ℕ) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (setB a b)) (2 * b)
      (relativeCohomologyMap ℚ (2 * b) (projB a b) (u b))
      (unionRelativeTriadCapCohomologyLinear ℚ (TopCat.of (Fin (a + b) → ℂ)) (setA a b) (setB a b)
        (2 * a) (2 * b)
        (triadToUnionRelativeChainMap_quasiIso_of_isOpen _ _ _ (isOpen_setA a b) (isOpen_setB a b))
        (relativeCohomologyMap ℚ (2 * a) (projA a b) (u a)) (orient a b)) = 1
```

**Chart form** (the rung id `local-class-product` itself): for a complex normed space E, an open M-chart φ : `OpenPartialHomeomorph M (E × (Fin a → ℂ) × (Fin b → ℂ))` with Z = {φ₂ = 0} and W = {φ₃ = 0} on its source, and W' ⊆ source open: `relCup2 (chartNormalProjectionCoclass … Z) (chartNormalProjectionCoclass … W) = chartNormalProjectionCoclass … (Z ∩ W)` on (W'; W' ∖ Z, W' ∖ W), the union read as W' ∖ (Z ∩ W) by the identity. It cannot elaborate until `triad-relative-cup` defines `relCup2`.

## Why the ladder needs it

Upstream's cycle class [Z] is characterized by its local classes along Z_reg (`cycleComponentSupportedInjectiveClass_unique`). The route of `cycle-class-multiplicative` computes [Z] ∪ [W] on the singular side as a relative cup into H^{2c}(X, X ∖ T), T = Z ∩ W, and compares its local classes with those of [T]; at each point of T(ℂ) that comparison is the chart form. The sign of this rung is the one sign in `cycle-class-multiplicative` that the checked comparisons do not fix: their (−1)^{pq} is 1 in even degrees.

## The sign of the cross product of complex orientations (decision 0009)

Expected **+** for every a, b, in four steps, each a kernel check in the sub-rungs below:

1. Block compatibility: under `Fin.append`, the real coordinates of ℂ^a then ℂ^b are those of ℂ^{a+b} in order, so the block identification is the identity on real coordinates. (With the real-parts-first ordering it would be a permutation of sign (−1)^{ab}.)
2. Real cross product: s_m × s_n = s_{m+n} for all m, n, with s_d the reference simplex. The identity (m, n)-shuffle simplex has a block-triangular edge matrix with determinant det(s_m) · det(s_n), of sign (−1)^m (−1)^n = (−1)^{m+n}, the sign of s_{m+n}.
3. Evaluation: ⟨pr₁*φ ⌣ pr₂*ψ, x × y⟩ = ⟨φ, x⟩ ⟨ψ, y⟩ with Alexander–Whitney front and back faces and no sign (the register's singular cup and cap rows). Koszul conventions [`Dold1972`, unverified] insert (−1)^{|ψ||x|}, which is 1 for |x| = 2a.
4. Factor order: (−1)^{(2a)(2b)} = 1, so Z first or W first gives the same class.

Proposed register row for the red team: "Cross product of complex orientations | `cross-orientation` | s_a × s_b = s_{a+b} under `Fin.append`, sign +, also in real dimensions m, n of any parity | `local-class-product`, `cycle-class-multiplicative` | open".

## Proof idea

1. GL⁺_d(ℝ) is path-connected (from Mathlib's transvection decomposition).
2. An affine automorphism with positive determinant fixes the local orientation (transported back to 0); negative determinant gives −1. Hence an affine d-simplex with y in its interior has class sign(det) · (−1)^d · s_d at y.
3. The shuffle map descends to relative chains: C(P, A) ⊗ C(Q, B) → C(P × Q)/(C(A × Q) + C(P × B)); this gives x × y in upstream's `TriadRelativeHomology` and, by `triadToUnionRelativeHomologyMap`, in H(P × Q, A × Q ∪ P × B).
4. Cap evaluation: ⟨pr₂*ψ, pr₁*φ ⌢ (x × y)⟩ = ⟨φ, x⟩⟨ψ, y⟩, from Alexander–Whitney after shuffle being homotopic to the identity through a natural homotopy (so it preserves the relative subcomplexes).
5. Orientation: s_m × s_n = s_{m+n}. Move the base point along a segment inside the image of the open prism (convex, disjoint from the image of its boundary) into the interior of the identity-shuffle simplex; there every other shuffle simplex vanishes in relative chains, and step 2 applies with the block determinant of the sign section. The complex form follows by block compatibility.
6. Model: steps 4 and 5 with `normalizedRelativeCoclass_pairing_self` give `local_class_cross_cap`.
7. Chart form: `triad-relative-cup` naturality along the normal projections (`chartNormalProjectionPair`) and the cup–cap adjunction reduce it to step 6.

## What exists (checked by `grep` at the pin)

| Source | Declarations |
|---|---|
| Mathlib | `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`, `Matrix.diagonal_transvection_induction_of_det_ne_zero`, `IsManifold.maximalAtlas` |
| upstream statement library | `standardLocalClass`, `standardComplexLocalClass`, `complexRealHomeomorph`, `puncturedPair`, `normalizedRelativeCoclass`, `normalizedRelativeCoclass_pairing_self`, `normalizedRelativeCoclass_unique`, `span_standardComplexLocalClass_eq_top`, `standardComplexLocalClass_ne_zero`, `chartNormalProjectionPair`, `chartNormalProjectionCoclass`, `chartNormalProjectionCoclass_restrict`, `exists_open_chartNormalProjectionCoclass_eq`, `relativeHomologyMap_complexMatrix_standardComplexLocalClass`, `nonempty_complexIsotopyToOne` |
| upstream `Other` | `triadToUnionRelativeChainMap_quasiIso_of_isOpen`, `triadToUnionRelativeHomologyMap`, `unionRelativeTriadCapCohomologyLinear`, `unionRelativeTriadCapCohomologyLinear_on_comparison`, `standardOrientationBallClass_restrict`, `convexSupport_translation_ne` |
| Tau Ceti in `port/` | `TopCat.shuffle`, `TopCat.shuffle_naturality`, `TopCat.shuffle_alexanderWhitney`, `SSet.shuffleAlexanderWhitneyHomotopy`, `SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality`, `SSet.eilenbergZilberHomotopyEquiv` |
| this repository | `HodgeLadder.Cup.relCupSing`, `forgetRel`, `relDiagonal`, `relCupSing_naturality` |

## What is missing

Path-connectedness of GL⁺_d(ℝ); the real local-orientation sign of an affine map; the shuffle cross product on pairs; the relative-relative cup `relCup2` (upstream's triad file says it stops short of the customary triad pairing; it supplies excision, and the cup is new); the dual of the triad quasi-isomorphism over ℚ (look in upstream `HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.Field` first).

## Sub-rungs

| Id | Statement | Route | Depends on |
|---|---|---|---|
| `glpos-path-connected` | a real square matrix with det > 0 is joined to 1 by a path in GL⁺ (Mathlib candidate) | transvections t ↦ E(t·c); positive diagonal; pairs of −1 by rotation | |
| `real-affine-orientation` | an affine automorphism of ℝ^d acts on the transported local class by sign(det); an affine simplex around y has class sign(det)(−1)^d s_d | step 2 | `glpos-path-connected` |
| `relative-cross-chain` | shuffle cross product H_m(P, A) ⊗ H_n(Q, B) → `TriadRelativeHomology` and → H_{m+n}(P × Q, A × Q ∪ P × B) | step 3 | `tauceti-cup-backport` |
| `cap-cross-evaluation` | ⟨pr₂*ψ, pr₁*φ ⌢ (x × y)⟩ = ⟨φ, x⟩⟨ψ, y⟩, no sign | step 4 | `relative-cross-chain` |
| `cross-orientation` | s_a × s_b = `standardComplexLocalClass ℚ (a + b)` via `orient`, sign +; real form s_m × s_n = s_{m+n} | step 5 | `real-affine-orientation`, `relative-cross-chain` |
| `local-class-cross-model` | `local_class_cross_cap` above | step 6 | `cap-cross-evaluation`, `cross-orientation` |
| `triad-relative-cup` | `relCup2 : H^p(X, A) × H^q(X, B) → H^{p+q}(X, A ∪ B)` for open A, B; `forgetRel` compatibility with `cupSing`; restriction to `relCupSing`; naturality for maps of triads; ⟨relCup2 φ ψ, z⟩ = ⟨ψ, φ ⌢ z⟩ | AW descends to the triad complex; dual of upstream's triad excision | `relative-singular-cup` |
| `local-class-product` | chart form above | step 7 | `local-class-cross-model`, `triad-relative-cup` |

Smallest sign-visible instance: `local-class-cross-model` at a = b = 1 (ℂ², real dimension 4, six shuffle simplices). A prover can try it before the general case.

## Sources

`Hatcher2002` (§3.2 relative cup, §3.B cross products), `MilnorStasheff1974` (Thom class of a product, complex orientation; section numbers unverified), `Bredon1993` (cross and cap products; unverified), `Dold1972` (Koszul sign conventions; unverified), `Fulton1998` ch. 19 (why: the cycle map is a ring homomorphism; numbering unverified). The determinant (−1)^d (d + 1) and the block determinant are hand computations, unverified in Lean.
