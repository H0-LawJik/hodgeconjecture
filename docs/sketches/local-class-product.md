# Sketch: `local-class-product`

Date: 2026-11-26. Front `cup`, decisions 0008, 0009 and 0010, rung 5. Red team: pass with changes (`docs/sketches/cycle-class-multiplicative.redteam.md`), implemented below. Companion sketch: `docs/sketches/cycle-class-multiplicative.md` (global assembly, tests, kill criterion). This is a plan. Nothing in it is checked, and each identity below is a target.

## Statement

**Plain words.** Let a, b ≥ 0, c = a + b, and split ℂ^c = ℂ^a × ℂ^b by `Fin.append` (first a complex coordinates, then b). Let u_k ∈ H^{2k}(ℂ^k, ℂ^k ∖ 0; ℚ) be upstream's normalized local class `normalizedRelativeCoclass (standardComplexLocalClass ℚ k) _`, the class that pairs to 1 with upstream's complex orientation class. Pull u_a back along the first block projection to H^{2a}(ℂ^c, A) with A = {z' ≠ 0}, and u_b along the second to H^{2b}(ℂ^c, B) with B = {z'' ≠ 0}, so A ∪ B = ℂ^c ∖ 0. Then the relative cup product of the two pullbacks is u_c, with sign +. In a holomorphic chart adapted to two transversal submanifolds Z, W of codimensions a, b, the same identity says: the relative cup of the normal-projection coclasses of Z and W is the normal-projection coclass of Z ∩ W.

**Upstream's normalization at the pin** (`docs/cycle-class.md`): the orientation of ℂ^k is `complexRealHomeomorph` (Re z₀, Im z₀, Re z₁, …); the reference cycle is `standardLocalClass` (affine simplex with vertices e₀, …, e_{d−1}, (−1, …, −1)) moved by it (`standardComplexLocalClass`). Its edge matrix has determinant (−1)^d (d + 1) (computed by hand for every d, unverified in Lean), so it is the standard orientation exactly when d is even, which matches the register row "Complex orientation of ℂ^p". Mathlib has no local orientation of its own here, so there is no definition to differ from.

**Literature.** For open A, B ⊆ X the relative cup H^k(X, A) × H^l(X, B) → H^{k+l}(X, A ∪ B) [`Hatcher2002` §3.2]. The Thom class of a product of oriented bundles is the cross product of the Thom classes, and the complex orientation comes from the real basis (v₁, iv₁, v₂, iv₂, …) [`MilnorStasheff1974` §§10, 14; section numbers unverified]. Cross products, shuffle maps, and their evaluation [`Hatcher2002` §3.B, `Bredon1993` ch. VI; chapter numbers unverified].

**Proposed Lean, model form.** Elaborated with `lake env lean` on a scratch file inside the worktree (deleted). Upstream's `Other.AlgebraicTopology.Singular.Excision.Triad` and the three `Cap` files it needs are not built in the shared cache, so they were compiled from copies; a prover's `lake build` builds them (build them once, from one worktree, before parallel work starts; section "Pins and drift"). The statement uses upstream's triad cap product, so it needs no new definition; the cup form follows from the adjunction `triad-relative-cup-cap` and `normalizedRelativeCoclass_unique`.

Helper definitions (the red team elaborated the statement with exactly these, scratch S3):

```lean
def setA (a b : ℕ) : Set (Fin (a + b) → ℂ) := {z | (fun i : Fin a => z (Fin.castAdd b i)) ≠ 0}
def setB (a b : ℕ) : Set (Fin (a + b) → ℂ) := {z | (fun j : Fin b => z (Fin.natAdd a j)) ≠ 0}
noncomputable def projA (a b : ℕ) :
    TopPair.ofSubset (X := TopCat.of (Fin (a + b) → ℂ)) (setA a b) ⟶ puncturedPair ℂ a :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun z i => z (Fin.castAdd b i), by fun_prop⟩) fun _ h => h
noncomputable def u (k : ℕ) : RelativeCohomology ℚ (puncturedPair ℂ k) (2 * k) :=
  normalizedRelativeCoclass (standardComplexLocalClass ℚ k) (standardComplexLocalClass_ne_zero k)
noncomputable def orient (a b : ℕ) : RelativeHomology ℚ
    (TopPair.ofSubset (X := TopCat.of (Fin (a + b) → ℂ)) (setA a b ∪ setB a b)) (2 * a + 2 * b) :=
  (Nat.mul_add 2 a b) ▸ relativeHomologyMap ℚ (2 * (a + b))
    (TopPair.isoOfSubset (Homeomorph.refl _) (fun z => union_eq a b z)).hom
    (standardComplexLocalClass ℚ (a + b))
```

`projB` follows the pattern of `projA` with `Fin.natAdd a`. `union_eq a b z` (membership in setA ∪ setB is membership in {0}ᶜ) takes about eight lines by `Fin.addCases`; `isOpen_setA`, `isOpen_setB` are preimages of {0}ᶜ under continuous maps. Spell the ambient space `(X := TopCat.of _)` in every `TopPair.ofSubset`: left implicit, elaboration of the statement exceeds 200000 heartbeats.

```lean
theorem local_class_cross_cap (a b : ℕ) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (setB a b)) (2 * b)
      (relativeCohomologyMap ℚ (2 * b) (projB a b) (u b))
      (unionRelativeTriadCapCohomologyLinear ℚ (TopCat.of (Fin (a + b) → ℂ)) (setA a b) (setB a b)
        (2 * a) (2 * b)
        (triadToUnionRelativeChainMap_quasiIso_of_isOpen _ _ _ (isOpen_setA a b) (isOpen_setB a b))
        (relativeCohomologyMap ℚ (2 * a) (projA a b) (u a)) (orient a b)) = 1
```

**Chart form** (the rung id `local-class-product` itself): for a complex normed space E, an open M-chart φ : `OpenPartialHomeomorph M (E × (Fin a → ℂ) × (Fin b → ℂ))` with Z = {φ₂ = 0} and W = {φ₃ = 0} on its source, and W' ⊆ source open: `relCup2 (chartNormalProjectionCoclass … Z) (chartNormalProjectionCoclass … W) = chartNormalProjectionCoclass … (Z ∩ W)` on (W'; W' ∖ Z, W' ∖ W), the union read as W' ∖ (Z ∩ W) by the identity. It cannot elaborate until `triad-relative-cup` defines `relCup2`. Route (decision 0010): the product of two supported classes is `relCup2` on upstream's triad excision. The checked general-V formula has one supported factor, so it cannot produce a class supported on Z ∩ W; it is off this rung's path.

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
4. Cap evaluation: ⟨pr₂*ψ, pr₁*φ ⌢ (x × y)⟩ = ⟨φ, x⟩⟨ψ, y⟩, from Alexander–Whitney after shuffle being homotopic to the identity through a natural homotopy. Singular chains here are unnormalized, so Alexander–Whitney after shuffle is the identity only up to that homotopy (`SSet.shuffleAlexanderWhitneyHomotopy`), and the relative form needs the homotopy to preserve C(A) ⊗ C(Q) + C(P) ⊗ C(B); naturality in each factor gives this, and the docstring of `cap-cross-evaluation` says so.
5. Orientation: s_m × s_n = s_{m+n}. Move the base point along a segment inside the image of the open prism (convex, disjoint from the image of its boundary) into the interior of the identity-shuffle simplex; there every other shuffle simplex vanishes in relative chains, and step 2 applies with the block determinant of the sign section. The complex form follows by block compatibility.
6. Model: steps 4 and 5 with `normalizedRelativeCoclass_pairing_self` give `local_class_cross_cap`.
7. Chart form: `triad-relative-cup-naturality` along the normal projections (`chartNormalProjectionPair`) and the cup–cap adjunction `triad-relative-cup-cap` reduce it to step 6.

## What exists (checked by `grep` at the pin)

| Source | Declarations |
|---|---|
| Mathlib | `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`, `Matrix.diagonal_transvection_induction_of_det_ne_zero`, `IsManifold.maximalAtlas` |
| upstream statement library | `standardLocalClass`, `standardComplexLocalClass`, `complexRealHomeomorph`, `puncturedPair`, `normalizedRelativeCoclass`, `normalizedRelativeCoclass_pairing_self`, `normalizedRelativeCoclass_unique`, `span_standardComplexLocalClass_eq_top`, `standardComplexLocalClass_ne_zero`, `chartNormalProjectionPair`, `chartNormalProjectionCoclass`, `chartNormalProjectionCoclass_restrict`, `exists_open_chartNormalProjectionCoclass_eq`, `relativeHomologyMap_complexMatrix_standardComplexLocalClass`, `nonempty_complexIsotopyToOne` |
| upstream `Other` (outside upstream's statement guard; pinned and drift-listed below) | `triadToUnionRelativeChainMap_quasiIso_of_isOpen` (`Singular/Excision/Triad.lean`, unbuilt in the shared cache), `triadToUnionRelativeHomologyMap`, `unionRelativeTriadCapCohomologyLinear`, `unionRelativeTriadCapCohomologyLinear_on_comparison` (`Singular/Cap/Triad.lean`, unbuilt), `capHom` (`Singular/Cap/Simplicial.lean`, unbuilt), `standardOrientationBallClass_restrict`, `convexSupport_translation_ne` (`LocalHomology/EuclideanNeighborhoodOrientation.lean`, built) |
| Tau Ceti in `port/` | `TopCat.shuffle`, `TopCat.shuffle_naturality`, `TopCat.shuffle_alexanderWhitney`, `SSet.shuffleAlexanderWhitneyHomotopy`, `SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality`, `SSet.eilenbergZilberHomotopyEquiv` |
| this repository | `HodgeLadder.Cup.relCupSing`, `forgetRel`, `relDiagonal`, `relCupSing_naturality` |

## What is missing

Path-connectedness of GL⁺_d(ℝ) (checked since 2026-11-26 as `glpos-path-connected`); the real local-orientation sign of an affine map; the shuffle cross product on pairs; the relative-relative cup `relCup2` (upstream's triad file says it stops short of the customary triad pairing; it supplies excision, and the cup is new); the dual of the triad quasi-isomorphism over ℚ (look in upstream `HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.Field` first).

## Sub-rungs

| Id | Statement | Route | Depends on |
|---|---|---|---|
| `glpos-path-connected` | a real square matrix with det > 0 is joined to 1 by a path in GL⁺ (Mathlib candidate) | transvections t ↦ E(t·c); positive diagonal; pairs of −1 by rotation | |
| `real-affine-orientation` | an affine automorphism of ℝ^d acts on the transported local class by sign(det); an affine simplex around y has class sign(det)(−1)^d s_d. First Lean lemma: the edge determinant of `standardAffineSimplex d` is (−1)^d (d + 1) | step 2 | `glpos-path-connected` |
| `relative-cross-chain` | shuffle cross product H_m(P, A) ⊗ H_n(Q, B) → `TriadRelativeHomology` and → H_{m+n}(P × Q, A × Q ∪ P × B). First Lean lemma: the identity shuffle has coefficient +1 in `shuffleChain` | step 3 | `tauceti-cup-backport` |
| `cap-cross-evaluation` | ⟨pr₂*ψ, pr₁*φ ⌢ (x × y)⟩ = ⟨φ, x⟩⟨ψ, y⟩, no sign; the docstring records the unnormalized-chain homotopy of step 4. First: the `rfl` pins of section "Pins and drift", unless `triad-relative-cup-cap` added them | step 4 | `relative-cross-chain` |
| `cross-orientation` | s_a × s_b = `standardComplexLocalClass ℚ (a + b)` via `orient`, sign +; real form s_m × s_n = s_{m+n}. First Lean lemmas: `complexRealHomeomorph_append` (below) and det of the identity-shuffle simplex of s_m × s_n = det(s_m) · det(s_n) | step 5 | `real-affine-orientation`, `relative-cross-chain` |
| `local-class-cross-model` | `local_class_cross_cap` above | step 6 | `cap-cross-evaluation`, `cross-orientation` |
| `triad-relative-cup` | `relCup2 : H^p(X, A) × H^q(X, B) → H^{p+q}(X, A ∪ B)` for open A, B; `forgetRel (relCup2 a b) = cupSing (forgetRel a) (forgetRel b)`; `relCup2` with B = ∅ is `relCupSing` | AW descends to the triad complex; dual of upstream's triad excision | `relative-singular-cup` |
| `triad-relative-cup-naturality` | `relCup2` is natural for maps of triads (open A, B, A', B'), no sign | pullback of the triad complex | `triad-relative-cup` |
| `triad-relative-cup-cap` | ⟨relCup2 φ ψ, z⟩ = ⟨ψ, φ ⌢ z⟩ for `unionRelativeTriadCapCohomologyLinear`, no sign. First: the `rfl` pins below, unless `cap-cross-evaluation` added them | chain-level identity front/back faces; excision on both sides | `triad-relative-cup` |
| `local-class-product` | chart form above | step 7 | `local-class-cross-model`, `triad-relative-cup`, `triad-relative-cup-naturality`, `triad-relative-cup-cap` |

Smallest sign-visible instance: `local-class-cross-model` at a = b = 1 (ℂ², real dimension 4, six shuffle simplices). A prover can try it before the general case.

Block compatibility, the first lemma of `cross-orientation` (statement elaborated 2026-11-26 against `HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.ComplexClass`):

```lean
theorem complexRealHomeomorph_append (a b : ℕ) (u : Fin a → ℂ) (v : Fin b → ℂ) :
    complexRealHomeomorph (a + b) (Fin.append u v) = fun i =>
      Fin.append (complexRealHomeomorph a u) (complexRealHomeomorph b v)
        (Fin.cast (Nat.add_mul a b 2) i)
```

## Pins and drift

The declarations this plan uses from upstream's library `Other` are outside upstream's statement guard, and four of their files (`Singular/Cap/{Simplicial,Relative,Triad}.lean`, `Singular/Excision/Triad.lean`) are not built in the shared package cache. They compile at the pin from copies in about 70 seconds with the standard axioms (red team, section 5).

- **Build once.** A prover's first `lake build` of a file that imports them writes their `.olean` files into the shared package cache. Build them once, from one worktree, before parallel work on these rungs starts.
- **`rfl` pins**, at the start of the first rung that uses them (`cap-cross-evaluation` or `triad-relative-cup-cap`): the formula of `capHom` (φ(front p-face) • back q-face) and `unionRelativeTriadCapCohomologyLinear` unfolded through `triadCapCohomologyLinear` and the inverse of the excision quasi-isomorphism.
- **Drift list** for the next pin bump, in addition to the definitions in `docs/conventions.md`: `capHom`, `relativeCapLift`, `triadCapHom`, `triadCapShortComplexHom`, `triadCapCohomologyLinear`, `unionRelativeTriadCapCohomologyLinear`, `triadUnionExcisionHomologyEquiv` (`Other/AlgebraicTopology/Singular/Cap/`), `triadToUnionRelativeChainMap` and `triadToUnionRelativeChainMap_quasiIso_of_isOpen` (`Other/.../Excision/Triad.lean`), `standardLocalClass`, `standardSingularSimplex`, `piCoordCLE`, `normalizedRelativeCoclass`, `normalizedDual`, `linearDualHomologyEquiv`, `cycleComponentSupportedClassNormalizationIso`, `cycleComponentSmoothSupportAmbientOpen`, and Tau Ceti's `shuffleChain` in `port/`. For `triad-relative-cup` (red team 2026-11-26): `triadSubspaceChainMap`, `triadRelativeChainComplex`, `triadRelativeChainProjection`, `triadRelativeChainProjection_triadToUnionRelativeChainMap`, `relativeChainProjection_empty_isIso`, `TopPair.ofSubset`, `TopPair.isoOfSubset`, `TopPair.ofSubsetHom`, `relativeChainProjection`, `relativeCohomologyMap`, `HomologicalComplex.linearDualMap`, `linearDualMap_comp`, `linearDualHomologyEquiv_naturality`, `TopPair.Homotopy.relativeChainProjection_naturality`.
- **Drift list** for the next pin bump, in addition to the definitions in `docs/conventions.md`: `capHom`, `relativeCapLift`, `triadCapHom`, `triadCapShortComplexHom`, `triadCapCohomologyLinear`, `unionRelativeTriadCapCohomologyLinear`, `triadUnionExcisionHomologyEquiv` (`Other/AlgebraicTopology/Singular/Cap/`), `triadToUnionRelativeChainMap` and `triadToUnionRelativeChainMap_quasiIso_of_isOpen` (`Other/.../Excision/Triad.lean`), `standardLocalClass`, `standardSingularSimplex`, `piCoordCLE`, `normalizedRelativeCoclass`, `normalizedDual`, `linearDualHomologyEquiv`, `cycleComponentSupportedClassNormalizationIso`, `cycleComponentSmoothSupportAmbientOpen`, and Tau Ceti's `shuffleChain` in `port/`. Added by `relative-cross-chain` (red team, section 8): the bodies of Tau Ceti `SSet.shuffleChain`, `SSet.stdSimplex.cone`, `prodCone`, `prodConeChain`, `SSet.shuffle`, `TopCat.shuffle` (`HodgeLadder.Relative.CrossChain` reads `cone` and `prodCone` through `import all`); Mathlib `TensorSigns (ComplexShape.down ℕ)`, `ιTensorObj`, the `ModuleCat` left unitor, `Functor.LaxMonoidal.μ TopCat.toSSet`; upstream `relativeChainFunctor`, `relativeChainProjection`, `TopPair.ofSubset`, `TopPair.ofSubsetHom`, `triadSubspaceChainMap`, `triadRelativeChainComplex`, `triadRelativeChainProjection`, `triadToUnionRelativeChainMap`, `triadToUnionRelativeHomologyMap`, and `TopPair.Homotopy.relativeChainProjectionComponentIsCokernel`, `relativeChainProjection_naturality`.

## Red-team changes (2026-11-26), as implemented

Verdict `docs/sketches/cycle-class-multiplicative.redteam.md`, pass with changes. For this sketch:

| Change | Where it is now |
|---|---|
| A: singular-side route, general-V formula off the critical path | decision 0010; "Chart form" above |
| B: helper definitions of the cap model | "Proposed Lean, model form" |
| E: split `triad-relative-cup` into definition with `forgetRel`, naturality, cap adjunction | sub-rungs table; ledger `triad-relative-cup-naturality`, `triad-relative-cup-cap` |
| H: `Other` declarations marked, pins, drift list, build once | "What exists", "Pins and drift" |
| I: hand computations 1 to 5 as Lean lemmas inside named rungs | sub-rungs table; `complexRealHomeomorph_append`; ledger notes of `real-affine-orientation`, `relative-cross-chain`, `cross-orientation`, `cap-cross-evaluation`, `triad-relative-cup-cap` |
| unnormalized chains in `cap-cross-evaluation` | proof idea, step 4 |

## glpos-path-connected: statement

Checked 2026-11-26 in `HodgeLadder.Glpos.PathConnected` by the route below; statement red team `docs/sketches/glpos-path-connected.redteam.md` (pass with changes C1 to C3, implemented). The statement is unchanged from the one posted for the red team.

```lean
theorem HodgeLadder.Glpos.joinedIn_one_of_det_pos {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : 0 < A.det) :
    JoinedIn {M : Matrix n n ℝ | 0 < M.det} 1 A

theorem HodgeLadder.Glpos.isPathConnected_setOf_det_pos {n : Type*} [Fintype n] [DecidableEq n] :
    IsPathConnected {M : Matrix n n ℝ | 0 < M.det}
```

The second is a corollary of the first: `⟨1, by simp, fun _ hA ↦ joinedIn_one_of_det_pos hA⟩`. Tests in the same module: `not_joinedIn_det_ne_zero_fin_one` (the `det ≠ 0` form fails at `Fin 1` for `diagonal ![-1]`) and `joinedIn_one_diagonal_neg_one_neg_one`. Classical source: [`Hall2015`; section unverified].

**Why this form.** `real-affine-orientation` follows upstream's complex proof in `HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ComplexClassLinearInvariance`: `complexMatrixPuncturedPairHomotopy` takes a path `C(unitInterval, Matrix (Fin d) (Fin d) ℂ)` from `1` to `A` with `det ≠ 0` at each `t` and returns a homotopy of punctured pairs from the identity to the map of `A`. From `h : JoinedIn {M | 0 < M.det} 1 A` the real version gets `h.somePath : Path 1 A` (a continuous map from the unit interval, with `source` and `target`) and `h.somePath_mem t : 0 < (h.somePath t).det`, hence `det ≠ 0` by `ne_of_gt`. The path starts at `1`, the direction upstream's homotopy uses. The ambient space is `Matrix n n ℝ` with its product topology, where `mulVec` and `Continuous.matrix_det` live, so the consumer needs no coercion out of a subtype or a group of units. A general finite index type costs nothing; the consumer takes `n = Fin d`.

| Alternative | Why set aside |
|---|---|
| `PathConnectedSpace (Matrix.GLPos n ℝ)` | the units topology and two coercions back to matrices stand between the statement and `mulVec`; it follows from the matrix form if a later rung wants it |
| a local structure `RealIsotopyToOne A`, copying upstream's `ComplexIsotopyToOne` | a new local structure for data `JoinedIn` already packages |
| a negative-determinant clause (`A` joined to a fixed reflection within `det < 0`) | the consumer derives it: for a reflection `R` with `R * R = 1`, apply the rung to `R * A` and map the path by left multiplication by `R` (`JoinedIn.map`) |

**What the pin has.** Mathlib: the subgroup `Matrix.GLPos` (`mem_glpos`, `GLPos.det_ne_zero`), with no connectedness result; `JoinedIn.trans`, `JoinedIn.mono`, `JoinedIn.map`, `JoinedIn.mul` (pointwise product of paths, via `Path.mul`), `Continuous.matrix_det`; the transvection decomposition `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec` and the inductions `Matrix.diagonal_transvection_induction` (diagonal case with `det (diagonal D) = det M`) and `Matrix.diagonal_transvection_induction_of_det_ne_zero`. `IsPathConnected` appears for balls, spheres, complements of subspaces and unitary balls in C⋆-algebras, none for real matrices of positive determinant (grep of `.lake/packages/mathlib/Mathlib` for `GLPos`, `GL⁺`, `IsPathConnected`, `JoinedIn`). Upstream has the complex analogue `Matrix.nonempty_complexIsotopyToOne` (invertible complex matrices, diagonal entries joined to 1 by `exp (t * log z)`). Over ℝ a negative diagonal entry has no such path, and that sign bookkeeping is the new part.

**Proof route.** Write S = {M | 0 < M.det}.

1. Products: from `JoinedIn S 1 A` and `JoinedIn S 1 B` get `JoinedIn S 1 (A * B)` by `JoinedIn.mul` and `JoinedIn.mono`, since `S * S ⊆ S` (`det_mul`, `mul_pos`).
2. Transvections: `s ↦ transvection i j (s * c)` has determinant 1 (`det_transvection_of_ne`), as in upstream's complex proof.
3. Induction: `diagonal_transvection_induction` with `P M := 0 < M.det ∧ JoinedIn S 1 M`; the diagonal case has `∏ D i = det A > 0`.
4. Positive diagonals: the straight line `t ↦ diagonal (fun i ↦ (1 - t) + t * D i)` has positive entries, so positive determinant.
5. Sign flip: for `i ≠ j`, `W = transvection i j (-1) * transvection j i 1 * transvection i j (-1)` is the quarter turn in the (i, j)-plane and `W * W` is the diagonal matrix with −1 at i and j and 1 elsewhere. By steps 1 and 2 it is joined to 1 in S; left multiplication by `diagonal D` (`JoinedIn.map`, determinant > 0) joins `diagonal D` to `diagonal D'`, with `D'` equal to `D` with the entries at i and j negated. In Lean this identity is `quarterTurn_mul_self`, at general `n`, by entrywise case analysis.
6. Strong induction on the number of negative entries of `D`: two or more, apply step 5 to two of them; exactly one is impossible since the product would be negative; none is step 4.

A rotation path `θ ↦ R_{ij}(θ)` in step 5 needs the determinant of a plane rotation inside a general `n × n` matrix, more work than step 2 on six transvections. QR with the connectedness of SO(n) is longer.

**Checks for the red team.** `rfl`, `trivial`, `simp`, `aesop`, `decide`, `grind`, `exact?` and `exact JoinedIn.refl _` fail on the statement. The hypothesis holds for `A = 1`. The variant with `det ≠ 0` in place of `0 < det` is false (the diagonal matrix with one entry −1 is separated from 1 by the intermediate value theorem on `det` along a path), which a red team can state as a negative check. For empty `n` the determinant is 1 and both sides are trivial; nothing in the consumer uses that case. Both declarations are listed in `docs/gaps.md` "General lemmas kept local" (decision 0011); the ledger module is `HodgeLadder.Glpos.PathConnected` (the brief's default path splits the id at every hyphen).
## triad-relative-cup: statement
Statement phase, 2026-11-26. Module `HodgeLadder/Cup/TriadCup.lean` (the ledger's `module` is set when the rung is proved). The definitions are complete and sorry-free with the standard axioms; the three theorems have `sorry` bodies. The file is not imported from `HodgeLadder.lean`. Elaboration with `lake env lean`: about 7 seconds for the whole file, once `HodgeLadder.Cup.RelativeCup` and upstream's `Other` triad files are built. `rfl`, `simp`, `aesop`, `decide` fail on each theorem.
**Definitions.** For `X : TopCat.{0}` and `A B : Set X`:
| Declaration | Meaning |
| `triadChains X A B` | upstream's `triadRelativeChainComplex ℚ X A B`, the cokernel of C(A) ⊞ C(B) → C(X) |
| `triadDiagonal X A B` | C(X)/(C(A) + C(B)) → C(X, A) ⊗ C(X, B): the Alexander–Whitney diagonal `awX X` followed by `relativeChainProjection` on both factors, descended through `cokernel.desc` (C(A) dies in the first factor, C(B) in the second, by naturality of the diagonal) |
| `homologyMap_linearDualMap_bijective` | over ℚ, the dual of a quasi-isomorphism is bijective on cohomology (through upstream's `linearDualHomologyEquiv_naturality`); a general lemma, to be listed in `docs/gaps.md` "General lemmas kept local" when the rung lands |
| `triadExcisionCoh X A B hA hB n` | H^n(X, A ∪ B) ≅ H^n(Hom(C(X)/(C(A) + C(B)), ℚ)); its forward map is the pullback along upstream's `triadToUnionRelativeChainMap` (induced by the identity of C(X)), bijective by `triadToUnionRelativeChainMap_quasiIso_of_isOpen` |
| `relCup2 X A B hA hB a b n h` | `(triadExcisionCoh n).inv ((triadCohIso n).inv (cup ℚ (triadDiagonal X A B) (λ_ _).hom p q n h (relCohIso _ p a) (relCohIso _ q b)))` |
| `unionEmptyIso X A` | `TopPair.ofSubset (A ∪ ∅) ≅ TopPair.ofSubset A`, upstream's `TopPair.isoOfSubset` of `Homeomorph.refl X` |
**Statements.**
def relCup2 (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (a : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset B) q) (n : ℕ) (h : p + q = n) :
    RelativeCohomology ℚ (TopPair.ofSubset (A ∪ B)) n
theorem forgetRel_relCup2 (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (a : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset B) q) (n : ℕ) (h : p + q = n) :
    forgetRel (TopPair.ofSubset (A ∪ B)) n (relCup2 X A B hA hB a b n h) =
      cupSing X (forgetRel (TopPair.ofSubset A) p a) (forgetRel (TopPair.ofSubset B) q b) n h
theorem relCup2_empty (hA : IsOpen A) {p q : ℕ}
    (a : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset (∅ : Set X)) q) (n : ℕ) (h : p + q = n) :
    relCup2 X A ∅ hA isOpen_empty a b n h =
      relativeCohomologyMap ℚ n (unionEmptyIso X A).hom
        (relCupSing (TopPair.ofSubset A) a (forgetRel (TopPair.ofSubset (∅ : Set X)) q b) n h)
theorem forgetRel_empty_bijective (q : ℕ) :
    Function.Bijective (forgetRel (TopPair.ofSubset (∅ : Set X)) q)
**Conventions.** Order: the A-relative factor is first and contributes the front p-face, the B-relative factor the back q-face, with no sign; this is the order and sign of `cupSing` (row "Singular cup product") and of `relCupSing` (row "Relative singular cup product", relative factor first). The comparisons carry no sign: `triadExcisionCoh` is the pullback along a chain map induced by the identity of C(X), `unionEmptyIso` is the identity of X, and `forgetRel` on (X, ∅) is the pullback along the projection C(X) → C(X)/C(∅). So B = ∅ is read in two steps: the pair (X, A ∪ ∅) is (X, A) through `unionEmptyIso`, pulled back by `relativeCohomologyMap`, and H^q(X, ∅) is H^q(X) through `forgetRel`, bijective by the third theorem. The hypotheses are ambient openness of A and B, as in the ledger; upstream's excision also holds when A and B are open in A ∪ B (`triadToUnionRelativeChainMap_quasiIso_of_openCover`), a generalization left for later.
**Route.**
1. `forgetRel_relCup2`. The triad projection π : C(X) → C(X)/(C(A) + C(B)) followed by upstream's comparison is the projection to C(X, A ∪ B) (`triadRelativeChainProjection_triadToUnionRelativeChainMap`). Dualizing, `forgetRel (triadExcisionCoh⁻¹ y)` is the pullback of y along π, so forgetRel ∘ relCup2 is the pullback along π of the triad cup. Since π ≫ `triadDiagonal` = `awX X` ≫ (proj_A ⊗ proj_B) (`cokernel.π_desc`), Tau Ceti's `cup_naturality` with e = π, f = proj_A, g = proj_B turns it into the cup along `awX X` of `forgetRel a` and `forgetRel b`, which is `cupSing` by `tcCup_eq`. The `dualIsoYoneda` transports are handled as in `forgetRel_relCupSing` and `relCohIso_map`.
2. `forgetRel_empty_bijective`. C(∅) is the zero complex (no singular simplices in ∅), so the projection C(X) → C(X, ∅) is an isomorphism and its dual is an isomorphism on cohomology.
3. `relCup2_empty`. Apply the injective map `triadExcisionCoh.hom`. Both sides become pullbacks to the triad complex C(X)/(C(A) + C(∅)): the left side is the triad cup of a and b; the right side is the pullback of `relCupSing a (forgetRel b)` along the map τ : C(X)/(C(A) + C(∅)) → C(X, A) induced by the identity of C(X). Tau Ceti's `cup_naturality` with e = τ, D = `relDiagonal`, D' = `triadDiagonal`, f = 𝟙 and g the inverse of C(X) → C(X, ∅) (step 2) gives the identity, after `τ ≫ relDiagonal = triadDiagonal ≫ (𝟙 ⊗ g)`, checked on generators through `cokernel.π`.
**Checked (2026-11-26).** Red team `docs/sketches/triad-relative-cup.redteam.md`, pass with changes, implemented. The three theorems are proved, with the cocycle formula required by finding 3: `triadCupCycles`, `triadExcisionCoh_relCup2_homologyπ` (through triad excision, `relCup2 [c] [d]` is the class of `triadCupCycles c d`) and `triadProj_cupCochain` (that cochain pulled back to C(X) is the Alexander–Whitney cup of c and d pulled back to C(X)). Together with injectivity of `triadExcisionCoh.hom` they determine `relCup2`; the two compatibility theorems alone do not, since forgetRel loses the relative information (counterfeit on S¹ ⊔ {pt} in the verdict). C(∅) = 0 comes from upstream's `relativeChainProjection_empty_isIso` (`Other/AlgebraicTopology/Singular/EmptySubspace.lean`). Non-vacuity: `torusEval_relCup2_winding` in `HodgeLadder.Tests.TriadCupTorus`, value 1 at A = B = ∅; the swapped product gives −1. Elaboration of the proved file: about 20 seconds.
**Drift list.** Add to section "Pins and drift": `triadSubspaceChainMap`, `triadRelativeChainComplex`, `triadRelativeChainProjection`, `triadRelativeChainProjection_triadToUnionRelativeChainMap` (`Other/.../Cap/Triad.lean`), `relativeChainProjection_empty_isIso` (`Other/.../Singular/EmptySubspace.lean`), `TopPair.ofSubset`, `TopPair.isoOfSubset`, `TopPair.ofSubsetHom`, `relativeChainProjection`, `relativeCohomologyMap`, `HomologicalComplex.linearDualMap`, `linearDualMap_comp`, `linearDualHomologyEquiv_naturality`, `TopPair.Homotopy.relativeChainProjection_naturality`. A change of `triadToUnionRelativeChainMap` away from "induced by the identity of C(X)", or a sign in `isoOfSubset`, would change the truth of the identities.
## relative-cross-chain: statement
Date: 2026-11-26. Phase 1 (statement), branch `track/relative-cross-chain` from `8b3a2fa`. File `HodgeLadder/Relative/CrossChain.lean`, module `HodgeLadder.Relative.CrossChain`, namespace `HodgeLadder.Relative`; not yet imported from `HodgeLadder.lean`. The ledger's `module` hint reads `HodgeLadder/Relative/Cross/Chain.lean`; the maintainer picks one of the two names when the rung is posted. The whole file elaborates with `lake env lean` in 6 to 11 seconds (wall clock, warm cache; 25 seconds on the first run). Status at the statement pass: the identity-shuffle sign and the simplex formula proved, five statements open. Red team: pass with changes (`docs/sketches/relative-cross-chain.redteam.md`). **Checked 2026-11-26** (section "relative-cross-chain: proofs" below).
**Choices.** Coefficients ℚ and spaces in `TopCat.{0}`, as upstream's triad files and every consumer use them. The product is the cartesian monoidal product `P ⊗ Q` of `TopCat`, whose points are pairs (`TopCat.tensor_apply` is `rfl`), since Tau Ceti's `TopCat.shuffle` lands in `Sing (X ⊗ Y)`. A relative cycle is given as an ambient chain `x` together with a cycle `zx` of upstream's relative complex with `iCycles zx = relativeChainProjection x`; every class of H_m(P, A) has this form, because `homologyπ` and the cokernel projection are surjective in `ModuleCat`. No openness is assumed: the cross product into the triad complex exists for all subsets, and openness enters only through upstream's excision (`triadToUnionRelativeChainMap_quasiIso_of_isOpen`) when a consumer inverts the comparison. The map into triad homology is fixed by an `∃!` statement, and `relCross` is its witness; consumers use `relCross_homologyπ` and uniqueness only. This keeps data `sorry` out of the file: the one definition that depends on an open proof is a choice from a Prop.
### Proved now
/-- The coefficient of the simplex `x` (identity on its summand, zero on the others). -/
def simplexCoeff (K : SSet.{w}) (T : C) {n : ℕ} (x : K _⦋n⦌) : (K.chainComplex T).X n ⟶ T :=
  Cofan.IsColimit.desc (K.isColimitChainComplexXCofan T n) fun y => if y = x then 𝟙 T else 0
/-- The identity (p, q)-shuffle: vertices (min i p, i - p), i = 0, …, n. -/
def idShuffle (p q n : ℕ) (h : p + q = n) : ((Δ[p] : SSet.{w}) ⊗ Δ[q]) _⦋n⦌
theorem shuffleChain_idShuffle_coeff (T : C) (p q n : ℕ) (h : p + q = n) :
    SSet.shuffleChain T p q n h ≫
        simplexCoeff ((Δ[p] : SSet.{w}) ⊗ Δ[q]) T (idShuffle p q n h) = 𝟙 T
def crossChainMap (P Q : TopCat.{0}) :
    SingularChainComplex ℚ P ⊗ SingularChainComplex ℚ Q ⟶ SingularChainComplex ℚ (P ⊗ Q) :=
  TopCat.shuffle P Q (𝟙_ (ModuleCat.{0} ℚ)) (𝟙_ (ModuleCat.{0} ℚ)) ≫
    ((SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).map (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom).app _
def shuffleBilin (P Q : TopCat.{0}) (m n : ℕ) :
    (SingularChainComplex ℚ P).X m →ₗ[ℚ] (SingularChainComplex ℚ Q).X n →ₗ[ℚ]
      (SingularChainComplex ℚ (P ⊗ Q)).X (m + n) :=
  (TensorProduct.mk ℚ _ _).compr₂
    (ιTensorObj (SingularChainComplex ℚ P) (SingularChainComplex ℚ Q) m n (m + n) rfl ≫
      (crossChainMap P Q).f (m + n)).hom
theorem shuffleBilin_ι {P Q : TopCat.{0}} {p q : ℕ} (σ : (TopCat.toSSet.obj P) _⦋p⦌)
    (τ : (TopCat.toSSet.obj Q) _⦋q⦌) :
    shuffleBilin P Q p q
        (((TopCat.toSSet.obj P).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom (1 : ℚ))
        (((TopCat.toSSet.obj Q).ιChainComplex (R := ModuleCat.of ℚ ℚ) τ).hom (1 : ℚ)) =
      (SSet.shuffleChain (ModuleCat.of ℚ ℚ) p q (p + q) rfl ≫
        (SSet.chainComplexMap
          ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
            Functor.LaxMonoidal.μ TopCat.toSSet P Q) (ModuleCat.of ℚ ℚ)).f (p + q)).hom (1 : ℚ)
Helpers, also proved: `ι_simplexCoeff_self`, `ι_simplexCoeff_of_ne`, `eq_idShuffle_iff` (a simplex is `idShuffle` iff its vertices are (min i p, i - p)), `prodCone_whiskerRight_succ`, `prodCone_whiskerLeft_one`, `tensorHom_mem_union`. The proof of `shuffleChain_idShuffle_coeff` follows the recursion of `shuffleChain`: the base cases are Tau Ceti's `shuffleChain_zero_left` and `shuffleChain_zero_right`; in the step, the horizontal cone sends `idShuffle p (q + 1)` to `idShuffle (p + 1) (q + 1)` and no other simplex there, and every simplex of the vertical cone has second coordinate at least 1 at vertex 1, where the identity shuffle has 0. Tau Ceti's `SSet.stdSimplex.prodCone` has no exposed body, so the file reads it through a private `import all` of `LefschetzPort.TauCeti.AlgebraicTopology.SimplicialSet.Shuffle`; this adds no axiom.
### Stated, proof open
With `leftProdSet A Q := {z : ↑(P ⊗ Q) | fst P Q z ∈ A}` (that is, A × Q), `rightProdSet P B := {z | snd P Q z ∈ B}` (P × B) and `crossUnionPair A B := TopPair.ofSubset (X := P ⊗ Q) (leftProdSet A Q ∪ rightProdSet P B)`:
theorem exists_triadCycle_shuffle {P Q : TopCat.{0}} (A : Set P) (B : Set Q) {m n : ℕ}
    (x : (SingularChainComplex ℚ P).X m) (y : (SingularChainComplex ℚ Q).X n)
    (zx : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).cycles m)
    (hx : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx =
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x)
    (zy : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles n)
    (hy : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy =
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y) :
    ∃ z : (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).cycles
        (m + n),
      ((triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).iCycles
          (m + n)).hom z =
        ((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f
          (m + n)).hom (shuffleBilin P Q m n x y)
`exists_unionCycle_shuffle` is the same with the cycle taken in `(relativeChainFunctor ℚ).obj (crossUnionPair A B)` and `relativeChainProjection ℚ (crossUnionPair A B)`.
`IsRelCross A B m n f` says, for a bilinear `f : H_m(P, A) →ₗ H_n(Q, B) →ₗ TriadRelativeHomology ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) (m + n)`: for all `x y zx zy z` with `hx`, `hy` as above and `iCycles z = triadRelativeChainProjection (shuffleBilin P Q m n x y)`, `f (homologyπ zx) (homologyπ zy) = homologyπ z`. Then:
theorem existsUnique_relCross {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ) :
    ∃! f, IsRelCross A B m n f
def relCross (A : Set P) (B : Set Q) (m n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset A) m →ₗ[ℚ] RelativeHomology ℚ (TopPair.ofSubset B) n →ₗ[ℚ]
      TriadRelativeHomology ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) (m + n) :=
  (existsUnique_relCross A B m n).exists.choose
theorem relCross_homologyπ (A : Set P) (B : Set Q) (m n : ℕ) :
    IsRelCross A B m n (relCross A B m n)          -- proved from the ∃!
def relCrossUnion (A : Set P) (B : Set Q) (m n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset A) m →ₗ[ℚ] RelativeHomology ℚ (TopPair.ofSubset B) n →ₗ[ℚ]
      RelativeHomology ℚ (crossUnionPair A B) (m + n) :=
  (relCross A B m n).compr₂
    (triadToUnionRelativeHomologyMap ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) (m + n))
`relCrossUnion_homologyπ`: with `hx`, `hy` as above and `z` a cycle of `(relativeChainFunctor ℚ).obj (crossUnionPair A B)` with `iCycles z = relativeChainProjection (shuffleBilin P Q m n x y)`, `relCrossUnion A B m n (homologyπ zx) (homologyπ zy) = homologyπ z`.
theorem relCrossUnion_naturality {P P' Q Q' : TopCat.{0}} (f : P ⟶ P') (g : Q ⟶ Q')
    {A : Set P} {A' : Set P'} {B : Set Q} {B' : Set Q'}
    (hf : ∀ a ∈ A, f a ∈ A') (hg : ∀ b ∈ B, g b ∈ B') {m n : ℕ}
    (x : RelativeHomology ℚ (TopPair.ofSubset A) m)
    (y : RelativeHomology ℚ (TopPair.ofSubset B) n) :
    relCrossUnion A' B' m n (relativeHomologyMap ℚ m (TopPair.ofSubsetHom f hf) x)
        (relativeHomologyMap ℚ n (TopPair.ofSubsetHom g hg) y) =
      relativeHomologyMap ℚ (m + n)
        (TopPair.ofSubsetHom (f ⊗ₘ g) (tensorHom_mem_union f g hf hg))
        (relCrossUnion A B m n x y)
**Trivial proofs fail** (scratch copy, deleted): `refine ⟨0, ?_, ?_⟩ <;> simp [IsRelCross]` on `existsUnique_relCross`; `simp` on `IsRelCross A B m n 0` (no progress); `exact ⟨0, by simp⟩`, `simp` and `exact ⟨_, rfl⟩` on `exists_triadCycle_shuffle`; `rfl` and `simp [relCrossUnion]` on the naturality. The zero map does not satisfy `IsRelCross` in general: for P = Q = a point, A = B = ∅ and m = n = 0 the shuffle of the two vertices is the vertex of the product (`TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero`), whose class is nonzero (by hand, not checked in Lean).
### Signs
| Fact | Status |
| The identity shuffle has coefficient +1 in `SSet.shuffleChain` (register row "Shuffle map") | proved, `shuffleChain_idShuffle_coeff` |
| Coefficient change ℚ ⊗ ℚ ≅ ℚ by the left unitor sends 1 ⊗ 1 to 1, so the singular shuffle of two simplices is the simplicial shuffle chain pushed forward, with no sign | proved, `shuffleBilin_ι` |
| The cross product on homology is [x] × [y] = [shuffle(x ⊗ y)], no sign; its boundary obeys d(x ⊗ y) = dx ⊗ y + (−1)^m x ⊗ dy (Mathlib's tensor differential), which is why the product of relative cycles is a cycle | stated; the Leibniz rule is Tau Ceti's `SSet.shuffle` being a chain map |
| Naturality in both pairs, no sign | stated, `relCrossUnion_naturality` |
| (1, 1) check: Tau Ceti's `ιChainComplex_tensorHom_ιChainComplex_shuffle_f_one_one` gives (s₁x, s₀y) − (s₀x, s₁y); its + term is `idShuffle 1 1 2` (vertices (0, 0), (1, 0), (1, 1)) | consistent with the proved coefficient |
### Route for the proofs
1. **Chain level.** `crossChainMap` sends the image of C(A) ⊗ C(Q) into the image of C(A × Q), and the image of C(P) ⊗ C(B) into that of C(P × B): `TopCat.shuffle_naturality` along the inclusion A ↪ P and the identity of Q, plus naturality of the coefficient change, and the factorization of the inclusion `A ⊗ Q ⟶ P ⊗ Q` through `(TopPair.ofSubset (leftProdSet A Q)).snd`.
2. **`exists_triadCycle_shuffle`.** By `hx`, d x lies in the image of C(A) (kernel of the cokernel projection in `ModuleCat` is the range), likewise d y in C(B). The chain-map property of `crossChainMap` and the Leibniz rule give d(shuffle x y) = shuffle(dx, y) ± shuffle(x, dy), and step 1 sends both into C(A × Q) + C(P × B). Treat m + n = 0 separately (the differential out of degree 0 is zero). Build `z` with `liftCycles`.
3. **`existsUnique_relCross`.** Existence: descend `crossChainMap ≫ triadRelativeChainProjection` to a chain map `C(P, A) ⊗ C(Q, B) ⟶ triadRelativeChainComplex` (step 1, both cokernels, right exactness of `⊗` in `ModuleCat` degreewise), and compose with the map H_m(K) × H_n(L) → H_{m+n}(K ⊗ L) built on cycles by `ιTensorObj`; it is new and general (record it in `docs/gaps.md` "General lemmas kept local", decision 0011). Uniqueness: `moduleCat_homologyπ_surjective`, surjectivity of the cokernel projection, and step 2.
4. **`exists_unionCycle_shuffle`, `relCrossUnion_homologyπ`.** Push the triad cycle along `triadToUnionRelativeChainMap` (`triadRelativeChainProjection_triadToUnionRelativeChainMap`) and use `homologyπ_naturality`.
5. **Naturality.** On representatives, from `TopCat.shuffle_naturality`, `TopCat.shuffle_coefficient_naturality` and `relCrossUnion_homologyπ`; every class has a representative.
**Downstream use.** `cap-cross-evaluation` uses `relCross` with upstream's `triadCapCohomologyLinear` on `TriadRelativeHomology ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)`, and `unionRelativeTriadCapCohomologyLinear_on_comparison` for the union form; `cross-orientation` uses `relCrossUnion`, `relCrossUnion_naturality` (to move between ℂ^k and ℝ^{2k} along `complexRealHomeomorph`), `shuffleBilin_ι` and `shuffleChain_idShuffle_coeff`. Questions for the red team: (i) whether `local-class-cross-model` also needs naturality at the triad level (maps of triads), which upstream does not define; (ii) whether consumers want the product as `P ⊗ Q` or as `TopCat.of (P × Q)` (definitionally equal); (iii) the file name.
## relative-cross-chain: proofs
Date: 2026-11-26. All five open statements are proved, with the standard axioms, in `HodgeLadder.Relative.CrossChain`, now imported from `HodgeLadder.lean`. The file elaborates in 9 to 14 seconds.
| Step | Lean |
| Leibniz rule on chains, with Mathlib's tensor differential, in the three cases (both degrees positive, a vertex chain on either side) | `shB_d_succ_succ`, `shB_d_zero_succ`, `shB_d_succ_zero`, from Tau Ceti's `ιTensorObj_d_of_rel`, `_of_not_rel_left`, `_of_not_rel_right` and the chain-map property of `crossChainMap` |
| Naturality of the shuffle product on chains | `crossChainMap_naturality`, `shB_naturality` (Tau Ceti `TopCat.shuffle_naturality`, coefficient naturality) |
| Chains of A × Q and of P × B vanish in the triad complex | `triadProj_shB_left`, `triadProj_shB_right`, through `leftProdLift`, `rightProdLift` and `triadSubspaceChainMap_triadRelativeChainProjection` |
| The shuffle product descends to relative chains | `relMu` (`descendBilin` along both cokernel projections; surjectivity and kernel from upstream's `relativeChainProjectionComponentIsCokernel`) |
| Cycles to cycles, boundaries to boundaries | `relMu_cycle`, `relMu_boundary_left`, `relMu_boundary_right` |
| Bilinear map on homology, any complex shape | `homologyBilin`, `homologyBilin_homologyπ` |
| The five statements | `exists_triadCycle_shuffle` (`triadCycleMk`), `exists_unionCycle_shuffle` (`cyclesMap` of upstream's comparison), `existsUnique_relCross` (witness `relCrossAux`), `relCrossUnion_homologyπ`, `relCrossUnion_naturality` |
Also added: `shuffleBilin_vertex` (the red team's degree (0, 0) normalization, its proof text verbatim), and register citations in the docstrings of the equality lemmas. The triad-level naturality is the new open rung `relative-cross-triad-naturality`.

## Sources

`Hatcher2002` (§3.2 relative cup, §3.B cross products), `MilnorStasheff1974` (Thom class of a product, complex orientation; section numbers unverified), `Bredon1993` (cross and cap products; unverified), `Dold1972` (Koszul sign conventions; unverified), `Fulton1998` ch. 19 (why: the cycle map is a ring homomorphism; numbering unverified). The determinant (−1)^d (d + 1) and the block determinant are hand computations, unverified in Lean.
