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
| `local-class-cross-model` | product form (restated 2026-11-26, red team of `cap-cross-evaluation`, C4): on ℂ^a × ℂ^b with `leftProdSet {0}ᶜ _`, `rightProdSet _ {0}ᶜ`, the triad cap of pr₁^* u_a with s_a × s_b, paired with pr₂^* u_b, is 1; the statement of `HodgeLadder.Tests.capCross_complex_model` (checked). `local_class_cross_cap` above, on ℂ^{a+b}, is superseded: the move to ℂ^{a+b} is made in `local-class-product` on the union pair, by upstream functoriality, `cross_orientation_complex` and the pullback lemma for `normalizedRelativeCoclass` along an isomorphism of pairs | step 6 | `cap-cross-evaluation`, `cross-orientation` |
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
- **Drift list** for the next pin bump, in addition to the definitions in `docs/conventions.md`: `capHom`, `relativeCapLift`, `triadCapHom`, `triadCapShortComplexHom`, `triadCapCohomologyLinear`, `unionRelativeTriadCapCohomologyLinear`, `triadUnionExcisionHomologyEquiv` (`Other/AlgebraicTopology/Singular/Cap/`), `triadToUnionRelativeChainMap` and `triadToUnionRelativeChainMap_quasiIso_of_isOpen` (`Other/.../Excision/Triad.lean`), `standardLocalClass`, `standardSingularSimplex`, `piCoordCLE`, `normalizedRelativeCoclass`, `normalizedDual`, `linearDualHomologyEquiv`, `cycleComponentSupportedClassNormalizationIso`, `cycleComponentSmoothSupportAmbientOpen`, and Tau Ceti's `shuffleChain` in `port/`. Added by `relative-cross-chain` (red team, section 8): the bodies of Tau Ceti `SSet.shuffleChain`, `SSet.stdSimplex.cone`, `prodCone`, `prodConeChain`, `SSet.shuffle`, `TopCat.shuffle` (`HodgeLadder.Relative.CrossChain` reads `cone` and `prodCone` through `import all`); Mathlib `TensorSigns (ComplexShape.down ℕ)`, `ιTensorObj`, the `ModuleCat` left unitor, `Functor.LaxMonoidal.μ TopCat.toSSet`; upstream `relativeChainFunctor`, `relativeChainProjection`, `TopPair.ofSubset`, `TopPair.ofSubsetHom`, `triadSubspaceChainMap`, `triadRelativeChainComplex`, `triadRelativeChainProjection`, `triadToUnionRelativeChainMap`, `triadToUnionRelativeHomologyMap`, and `TopPair.Homotopy.relativeChainProjectionComponentIsCokernel`, `relativeChainProjection_naturality`. Added by `cross-orientation` (red team, section 8): `Complex.piBasisOneI` (`complexRealHomeomorph_finProdFinEquiv` unfolds it, so a reordering of upstream's real basis of ℂ^p breaks the build). Added by `relative-cross-triad-naturality` (red team, section 8): upstream `singularChainComplexFunctor` (the `rfl` of `singChainFunctor_map_eq_chainComplexMap`), `chainPairFunctor`, `TopPair.ofSubset` (`.map`, `.snd`), `TopPair.ofSubsetHom`, `TopPair.Hom.snd`, `triadSubspaceChainMap` (the `rfl` of `triadSubspaceChainMap_eq` reads its `biprod.desc` body), `triadSubspaceChainMap_triadRelativeChainProjection`, `triadRelativeChainProjection_triadToUnionRelativeChainMap`, `TopPair.Homotopy.relativeChainProjection_naturality`.

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

## real-affine-orientation: statement

Statement elaborated 2026-11-26 in `HodgeLadder/Local/RealAffineOrientation.lean` (namespace `HodgeLadder.RealAffine`); statement red team `docs/sketches/real-affine-orientation.redteam.md` (pass with changes 1 to 5, implemented). Checked 2026-11-26 with the statements unchanged; see "real-affine-orientation: proofs" below. The ledger module is `HodgeLadder.Local.RealAffineOrientation` (the brief's default path `HodgeLadder/Real/Affine/Orientation.lean` splits the id at every hyphen).

Notation: E(v) is the edge matrix of an ordered list v₀, …, v_d in ℝ^d, column i equal to v_{i+1} − v₀; s_d is upstream's reference simplex (`standardAffineSimplex d`, vertices e₀, …, e_{d−1}, (−1, …, −1)); o_y is upstream's `standardLocalClass ℚ d` moved to H_d(ℝ^d, ℝ^d ∖ {y}; ℚ) by `translationPointComplementPairMap (Fin d → ℝ) y` (x ↦ x + y). Matrices act on column vectors by `mulVec`.

```lean
def edgeMatrix {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j i => v i.succ j - v 0 j

theorem det_edgeMatrix_standardAffineSimplex (d : ℕ) :
    (edgeMatrix fun k => standardAffineSimplex d (StdSimplex.single k)).det =
      (-1) ^ d * (d + 1)

theorem relativeHomologyMap_realMatrix_standardLocalClass (d : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0) :
    relativeHomologyMap ℚ d (realMatrixPuncturedPairMap d A hA) (standardLocalClass ℚ d) =
      (SignType.sign A.det : ℚ) • standardLocalClass ℚ d

theorem relativeHomologyMap_affinePointPairMap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det ≠ 0) (c y : Fin d → ℝ) :
    relativeHomologyMap ℚ d (affinePointPairMap A hA c y)
        (relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) y)
          (standardLocalClass ℚ d)) =
      (SignType.sign A.det : ℚ) •
        relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) (A *ᵥ y + c))
          (standardLocalClass ℚ d)

theorem affineSimplex_homologyπ {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ)
    (hv : (edgeMatrix v).det ≠ 0) (y : Fin d → ℝ) (w : Fin (d + 1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hy : ∑ i, w i • v i = y)
    (z : ((relativeChainFunctor ℚ).obj (pointPair d y)).cycles d)
    (hz : (((relativeChainFunctor ℚ).obj (pointPair d y)).iCycles d).hom z =
      ((relativeChainProjection ℚ (pointPair d y)).f d).hom
        (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
          (affineSingularSimplex v)).hom (1 : ℚ))) :
    (((relativeChainFunctor ℚ).obj (pointPair d y)).homologyπ d).hom z =
      ((SignType.sign (edgeMatrix v).det : ℚ) * (-1) ^ d) •
        relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) y)
          (standardLocalClass ℚ d)
```

Local definitions: `pointPair d y` (an `abbrev` for `TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) {y}ᶜ`, the target of upstream's translation map; at y = 0 it is `puncturedPair ℝ d`), `affineSimplexMap v t = ∑ tᵢ • vᵢ`, `affineSingularSimplex v` (that map as a singular d-simplex of `TopCat.of (Fin d → ℝ)`, via `toSSetObjEquiv`), `realMatrixPuncturedPairMap` (the real copy of upstream's `complexMatrixPuncturedPairMap`, by `TopPair.ofSubsetHom`), `affinePointPairMap A hA c y : pointPair d y ⟶ pointPair d (A *ᵥ y + c)` (x ↦ A x + c), `vertexSwapMatrix d` (column j is the vertex `swap 0 1 j` of s_d), `openSimplex v` (the points ∑ wᵢ vᵢ with every wᵢ > 0, ∑ wᵢ = 1). The file also states `exists_affineSimplex_cycle` (the cycle z of `affineSimplex_homologyπ` exists, same hypotheses), `exists_affineSimplex_openSimplex_cycle` (σ_v is a relative cycle of (ℝ^d, ℝ^d ∖ openSimplex v) when det E(v) ≠ 0) and the route lemma `relativeHomologyMap_vertexSwap_standardLocalClass` (the vertex swap sends `standardLocalClass ℚ (n + 1)` to its negative).

**Proved at the statement stage** (standard axioms, `#print axioms`): `det_edgeMatrix_standardAffineSimplex`; `sign_det_edgeMatrix_standardAffineSimplex_mul` (the scalar of `affineSimplex_homologyπ` at v = the vertices of s_d is sign((−1)^d (d + 1)) · (−1)^d = 1); `det_vertexSwapMatrix` (det = −1 in every dimension n + 1); `affineSimplexMap_standardAffineSimplex` (s_d is the affine simplex on its own vertices); `convex_openSimplex`; `zero_mem_openSimplex_standardAffineSimplex` (weights 1/(d + 1)); `relativeHomologyMap_point_eq_translate` (for convex U ∋ 0, y and x ∈ H_n(ℝ^d, ℝ^d ∖ U), restriction of x to y is the translate by y of its restriction to 0; upstream's `convexSupportTranslationPairHomotopy` and `relativeHomologyMap_comp`). The six statements left open then (`relativeHomologyMap_vertexSwap_standardLocalClass`, `relativeHomologyMap_realMatrix_standardLocalClass`, `relativeHomologyMap_affinePointPairMap`, `exists_affineSimplex_openSimplex_cycle`, `exists_affineSimplex_cycle`, `affineSimplex_homologyπ`) are now proved.

**Signs, and where each comes from.**

| Sign | Value | Source |
|---|---|---|
| det E(s_d) | (−1)^d (d + 1) | Lean proof: adding every row to row 0 leaves (0, …, 0, −(d + 1)) there (column i < d − 1 of E(s_d) is e_{i+1} − e₀, the last is (−1, …, −1) − e₀); Laplace along row 0 leaves (−1)^{d−1} · (−(d + 1)) times an identity minor. Agrees with the red team's column computation and its rational check for d ≤ 7; d = 1 gives −2, d = 2 gives 3 |
| vertex swap R | det R = −1; R_* o₀ = −o₀ | R permutes the vertices of s_d by the transposition (0 1) (for d = 1, R = −1; for d ≥ 2, R exchanges coordinates 0 and 1 and fixes (−1, …, −1)). Linear maps preserve barycentric combinations, so R ∘ s_d = s_d ∘ (0 1) as singular simplices. For the (d + 1)-simplex ρ = s_d on the vertex sequence 0, 1, 0, 2, …, d: face 0 is s_d ∘ (0 1), face 2 is s_d, face 1 (sequence 0, 0, 2, …, d) and faces k ≥ 3 omit a vertex of s_d, so they lie in a face of s_d and miss 0. In relative chains ∂ρ = s_d ∘ (0 1) + s_d |
| det A > 0 | + | `glpos-path-connected`: a path from 1 to A in {det > 0} gives a homotopy of pairs from the identity to A, as in upstream's `complexMatrixPuncturedPairHomotopy` |
| det A < 0 | − | A = (A R) R with det(A R) = −det A > 0: the + case after the vertex swap |
| affine x ↦ A x + c | sign(det A), no further sign | the map of pairs (ℝ^d, ℝ^d ∖ {y}) → (ℝ^d, ℝ^d ∖ {A y + c}) is translation by −y, then A, then translation by A y + c; translations by −y then y compose to the identity map of pairs |
| affine simplex around y | sign(det E(v)) · (−1)^d | F(x) = M x + c with M = E(v) E(s_d)⁻¹ sends s_d's vertices to v, so F ∘ s_d = σ_v. p = F⁻¹(y) has the same positive barycentric weights for s_d, so p and 0 lie in the open reference simplex U (convex; the boundary image of s_d misses it). By the move lemma the class of s_d at p is o_p; F sends it to sign(det M) o_y, and sign(det M) = sign(det E(v)) · sign(det E(s_d)) = sign(det E(v)) · (−1)^d |
| reference simplex in that formula | 1 | `sign_det_edgeMatrix_standardAffineSimplex_mul` (proved) |

**How `cross-orientation` reads it.** The real form `cross_orientation_real m n` (relative-cross-chain red team, section 2) is an identity at 0 in H_{m+n}(ℝ^{m+n}, ℝ^{m+n} ∖ {0}). Take the cross product of the cycles of `exists_affineSimplex_openSimplex_cycle` for s_m and s_n, so the class lives on (ℝ^{m+n}, ℝ^{m+n} ∖ U) with U = openSimplex(s_m) × openSimplex(s_n) the open prism (convex by `convex_openSimplex`, containing 0 by `zero_mem_openSimplex_standardAffineSimplex`), and restricts at 0 to the cross product of the two `standardLocalClass`es by naturality; `relativeHomologyMap_point_eq_translate` moves it from 0 to a point y inside the open identity-shuffle simplex. At y every other shuffle simplex lies in ℝ^{m+n} ∖ {y} (two simplices of the prism triangulation meet in a common face, which misses the open identity simplex), and the identity shuffle has coefficient +1 (`shuffleChain_idShuffle_coeff`), so the restricted cycle is the hz-cycle of the identity-shuffle simplex σ_id. `affineSimplex_homologyπ` gives sign(det E(σ_id)) · (−1)^{m+n} · o_y, and the first lemma of `cross-orientation` makes det E(σ_id) = det E(s_m) · det E(s_n), of sign (−1)^{m+n}; the scalar is 1. Example at m = n = 1: σ_id has vertices (1, 1), (−1, 1), (−1, −1), edge columns (−2, 0) and (−2, −2), det 4 = (−2)(−2). Over ℚ this distinguishes + from − because `standardLocalClass_ne_zero_of_pos` makes o_y nonzero.

**Route for the proofs.** (a) `relativeHomologyMap_vertexSwap_standardLocalClass`: the chain identity above, with faces as `StdSimplex.map i.succAbove` as in upstream's `standardOrientationBallFace_projection`, and the faces' supports by `standardAffineSimplex_ne_zero_of_coord_zero`. (b) `relativeHomologyMap_realMatrix_standardLocalClass`: copy upstream's `complexMatrixPuncturedPairHomotopy` over ℝ with `h.somePath` and `h.somePath_mem` (glpos red team, finding 7), then (a) for det < 0. (c) `relativeHomologyMap_affinePointPairMap`: factor the pair map through translations (`TopPair.Hom` ext), `relativeHomologyMap_comp`, (b). (d) `exists_affineSimplex_openSimplex_cycle`: faces of σ_v miss openSimplex v, as in `standardLocalChain_boundary` (a face point with a zero barycentric weight equal to y would give a second barycentric expression of y, excluded by det E(v) ≠ 0); `exists_affineSimplex_cycle` by restriction along `supportInclusionPairMap`. (e) `affineSimplex_homologyπ`: the class of s_d on (ℝ^d, ℝ^d ∖ U), U the open reference simplex (from (d)), its restriction to 0 is `standardLocalClass` (as `standardOrientationBallClass_restrict_zero`), the move lemma to p, chain naturality for F ∘ s_d = σ_v, (c), and uniqueness of z from `iCycles` mono.

**Alternatives set aside.**

| Alternative | Why set aside |
|---|---|
| a local definition `affineSimplexLocalClass v y` | the cycle-hypothesis form needs no new class; it matches `relCrossUnion_homologyπ`, which is what the consumer has in hand; `exists_affineSimplex_cycle` keeps it non-vacuous |
| two statements, det > 0 and det < 0 | `SignType.sign` holds both; a consumer rewrites with `sign_pos` or `sign_neg` |
| the coordinate reflection diag(−1, 1, …, 1) for the negative case | it moves e₀ to −e₀, off the vertex set of s_d, so there is no chain identity; the vertex swap permutes the vertices |
| dropping hv | by hand the identity should hold for det E(v) = 0 too (both sides 0: σ_v lies in a hyperplane; unverified), but the proof would need the vanishing of H_d on a lower-dimensional subspace; a degenerate simplex has no interior point, so the consumer does not need it |
| any coefficient ring | the consumer and upstream's complex analogue work over ℚ |

**Checks for the red team.** `rfl`, `simp`, `aesop`, `decide`, `trivial`, `grind`, `norm_num` and `exact?` fail on each of the six open statements (six errors per tactic, run on a copy of the file). Hypotheses of `affineSimplex_homologyπ` are met by the vertices of s_d, y = 0, wᵢ = 1/(d + 1) (`affineSimplexMap_standardAffineSimplex`, `exists_affineSimplex_cycle`), where it returns `standardLocalClass` itself. Sign-visible instances: d = 1 with v = (−1, 1) has E(v) = (2) and class −o_y; the reference order v = (1, −1) has class o_y. Proposed register row: "Real local orientation and affine maps | `real-affine-orientation` | x ↦ A x + c (A by `mulVec`) sends o_y to sign(det A) o_{Ay+c}; an affine simplex around y has class sign(det E(v)) (−1)^d o_y, E(v) with columns v_{i+1} − v₀ | `cross-orientation`, `local-class-product` | stated".

## real-affine-orientation: proofs

Checked 2026-11-26, after a rebase on `main` (so `HodgeLadder.Relative.CrossChain` is in scope). `lake env lean` on the file takes about 7 s wall time; every declaration uses the three standard axioms only. The red team's changes, as implemented:

| Change | Declarations |
|---|---|
| 1: reference pins and the reference instance | `affineSingularSimplex_standardAffineSimplex`, `translationPointComplementPairMap_zero`, `exists_affineSimplex_cycle_standard`, `affineSimplex_homologyπ_standard` (the red team's text, one line rewrapped) |
| 2: cancelling the translation | `relativeHomologyMap_translation_injective` (translation by −y, `translateBackPairMap`, is a left inverse as maps of pairs) |
| 3: the open-simplex class at a point | `affineSimplex_openSimplex_restrict` (restriction along `supportInclusionPairMap`, then `affineSimplex_homologyπ`), with the corollary `openSimplex_standard_restrict_zero` (class `standardLocalClass ℚ d` at 0) |
| 4: rebase and fit check | below |
| 5: records | `Hatcher2002` row (§2.2, unverified) in `docs/references.md`; the Sources line below |

Route as proved, step by step:

- (a) `relativeHomologyMap_vertexSwap_standardLocalClass`. `vertexSwapMatrix_mulVec_standardAffineSimplex` gives R ∘ s_d = s_d ∘ swap(0 1) through `affineSimplexMap_map` and `vertexSwapMatrix_mulVec_single`; the last vertex uses ∑ₖ sₖ = 0. `stdMapSimplex n g` is s_{n+1} on a vertex sequence g. `swapPrism n` is the sequence 0, 1, 0, 2, …, n + 1, and three lemmas control its faces: face 0 is the swap, face 2 is the identity, and every other face omits a vertex (`stdMapSimplex_ne_zero`, `relProj_ι_eq_zero`). The cycle sum z₁ + z₀ is then `toCycles` of the prism and has class 0.
- (b) `relativeHomologyMap_realMatrix_standardLocalClass`. `realMatrixPuncturedPairHomotopy` copies upstream's complex homotopy, with the path `h.somePath` from `joinedIn_one_of_det_pos`. For det < 0, A = (A R⁻¹) R with det(A R⁻¹) = −det A, through `realMatrixPuncturedPairMap_comp` and `_congr`.
- (c) `relativeHomologyMap_affinePointPairMap`. `translation_comp_affinePointPairMap` is an identity of maps of pairs, x ↦ A(x + y) + c = A x + (A y + c), so it needs no homotopy. `relativeHomologyMap_affinePairMap` is the same with the image point named.
- (d) The cycle lemmas. `exists_affineSimplex_cycle_of_faces` covers positive dimension, and `exists_affineSimplex_cycle_zero` covers dimension 0 (the differential out of degree 0 is zero). Faces miss the open simplex by `weights_eq_of_det_ne_zero`.
- (e) `affineSimplex_homologyπ`. M = E(v) E(s_d)⁻¹ and c = v₀ − M s₀, and `affine_transport_combination` gives M (∑ aᵢ sᵢ) + c = ∑ aᵢ vᵢ whenever ∑ aᵢ = 1. The steps are: the open-reference-simplex cycle of s_d; its restriction to 0 is `standardLocalCycle`, by `iCycles` injectivity; the move lemma takes it to p = ∑ wᵢ sᵢ; the push along `affinePairMap M _ c p y`, whose simplex is σ_v; and sign(det M) = sign(det E(v)) · sign(det E(s_d)) = sign(det E(v)) · (−1)^d (`sign_inv_real`).

**Fit check with `relCrossUnion_homologyπ`.** This elaborated in a scratch file inside the worktree importing `HodgeLadder.Relative.CrossChain` (since deleted). The open-simplex cycles of s_m and s_n feed `hx` and `hy` with no cast:

```lean
example (m n : ℕ)
    (z : ((relativeChainFunctor ℚ).obj (HodgeLadder.Relative.crossUnionPair
      (P := TopCat.of (Fin m → ℝ)) (Q := TopCat.of (Fin n → ℝ))
      (openSimplex fun k => standardAffineSimplex m (Convexity.StdSimplex.single k))ᶜ
      (openSimplex fun k => standardAffineSimplex n (Convexity.StdSimplex.single k))ᶜ)).cycles
        (m + n)) : True := by
  have hm : (edgeMatrix fun k => standardAffineSimplex m (Convexity.StdSimplex.single k)).det ≠ 0 := by
    rw [det_edgeMatrix_standardAffineSimplex]; positivity
  have hn : (edgeMatrix fun k => standardAffineSimplex n (Convexity.StdSimplex.single k)).det ≠ 0 := by
    rw [det_edgeMatrix_standardAffineSimplex]; positivity
  obtain ⟨zx, hzx⟩ := exists_affineSimplex_openSimplex_cycle _ hm
  obtain ⟨zy, hzy⟩ := exists_affineSimplex_openSimplex_cycle _ hn
  have := fun hz => HodgeLadder.Relative.relCrossUnion_homologyπ _ _ _ _ zx zy z hzx hzy hz
  trivial
```

Exchanging `hzx` and `hzy` fails to elaborate, so the check is not vacuous. `cross-orientation` composes as follows:

1. `relCrossUnion_homologyπ` on these cycles.
2. Restriction from the complement of the open prism to a point y of the open identity-shuffle simplex, via `relativeHomologyMap_point_eq_translate` with U the product of the two open simplices.
3. `affineSimplex_homologyπ` at y, with the block determinant.
4. `relativeHomologyMap_translation_injective` to return to 0.
5. On the other side, the restriction at 0 of the cross product of the two open-simplex classes is the cross product of the two `standardLocalClass`es, by `relCrossUnion_naturality` and `openSimplex_standard_restrict_zero`.

**What failed on the way.**
- `rw` with chain-level lemmas failed when the goal mixed `TopPair.fst` with `TopCat.of (Fin d → ℝ)`, or the two `Ring ℚ` instance paths. `erw`, or `refine (lemma …).trans ?_`, works.
- `relProj_ι_eq_zero` applied to a face with its implicit arguments left to unification hit the heartbeat limit. Naming the space and the simplex fixes it.
- `pointPair` used before its definition was silently auto-bound and made two statements time out. Definitions now come first.

## cross-orientation: statement

Date: 2026-11-26. Phase 1 (statement), branch `track/cross-orientation` from `79df873`. File `HodgeLadder/Local/CrossOrientation.lean`, module `HodgeLadder.Local.CrossOrientation`, namespace `HodgeLadder.CrossOrientation`; not yet imported from `HodgeLadder.lean`. The brief's default path `HodgeLadder/Cross/Orientation.lean` splits the id at its hyphen; the file sits next to `HodgeLadder.Local.RealAffineOrientation`, whose lemmas it reads, and the maintainer picks the name when the rung is posted. `lake env lean` on the file takes about 5 s (warm cache). Status at the statement pass: ten declarations proved with the three standard axioms, three statements open. Statement red team: pass with changes (`docs/sketches/cross-orientation.redteam.md`). **Checked 2026-11-26** with the statements unchanged; see "cross-orientation: proofs" below.

**Choices.** Coefficients ℚ, spaces in `TopCat.{0}`, the product `P ⊗ Q` of `relCrossUnion`, as in `relative-cross-chain`. The real form is the red team's sign-visible test of `relative-cross-chain` verbatim. The complex form uses upstream's classes as they stand, in degree `2 * k`, and reads the right side through `Nat.mul_add 2 a b : 2 * (a + b) = 2 * a + 2 * b`, the same `▸` cast upstream uses in `standardComplexLocalClass`. The block determinant is stated for any two vertex lists, so it is a block-triangular identity with no reference to s_d; the s_m × s_n instance is a corollary.

### Statements

```lean
theorem complexRealHomeomorph_append (a b : ℕ) (u : Fin a → ℂ) (v : Fin b → ℂ) :
    complexRealHomeomorph (a + b) (Fin.append u v) = fun i =>
      Fin.append (complexRealHomeomorph a u) (complexRealHomeomorph b v)
        (Fin.cast (Nat.add_mul a b 2) i)

def shuffleVertices {m n : ℕ} (v : Fin (m + 1) → Fin m → ℝ) (w : Fin (n + 1) → Fin n → ℝ) :
    Fin (m + n + 1) → Fin (m + n) → ℝ :=
  fun k => Fin.append (v ⟨min k.val m, by omega⟩) (w ⟨k.val - m, by omega⟩)

theorem det_edgeMatrix_shuffleVertices {m n : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (w : Fin (n + 1) → Fin n → ℝ) :
    (edgeMatrix (shuffleVertices v w)).det = (edgeMatrix v).det * (edgeMatrix w).det

theorem appendMap_idShuffle {m n : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (w : Fin (n + 1) → Fin n → ℝ) :
    (((SSet.yonedaEquiv.symm (affineSingularSimplex v) ⊗ₘ
          SSet.yonedaEquiv.symm (affineSingularSimplex w)) ≫
        Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of (Fin m → ℝ)) (TopCat.of (Fin n → ℝ)) ≫
          TopCat.toSSet.map (appendMap m n)).app _ (idShuffle m n (m + n) rfl)) =
      affineSingularSimplex (shuffleVertices v w)

theorem eq_idShuffle_of_shuffleBarycenter {m n : ℕ} (x : ((Δ[m] : SSet.{0}) ⊗ Δ[n]) _⦋m + n⦌)
    (t : Fin (m + n + 1) → ℝ) (ht : ∀ k, 0 ≤ t k) (ht1 : ∑ k, t k = 1)
    (h : ∑ k, t k • Fin.append (standardAffineSimplex m (StdSimplex.single (x.1 k)))
        (standardAffineSimplex n (StdSimplex.single (x.2 k))) = shuffleBarycenter m n) :
    x = idShuffle m n (m + n) rfl

theorem cross_orientation_real (m n : ℕ) :
    relativeHomologyMap ℚ (m + n) (TopPair.ofSubsetHom (appendMap m n) (appendMap_mem m n))
      (relCrossUnion (P := TopCat.of (Fin m → ℝ)) (Q := TopCat.of (Fin n → ℝ))
        ({0}ᶜ : Set (Fin m → ℝ)) ({0}ᶜ : Set (Fin n → ℝ)) m n
        (standardLocalClass ℚ m) (standardLocalClass ℚ n)) =
      standardLocalClass ℚ (m + n)

theorem cross_orientation_complex (a b : ℕ) :
    relativeHomologyMap ℚ (2 * a + 2 * b)
      (TopPair.ofSubsetHom (complexAppendMap a b) (complexAppendMap_mem a b))
      (relCrossUnion (P := TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
        ({0}ᶜ : Set (Fin a → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)) (2 * a) (2 * b)
        (standardComplexLocalClass ℚ a) (standardComplexLocalClass ℚ b)) =
      (Nat.mul_add 2 a b) ▸ standardComplexLocalClass ℚ (a + b)
```

Local definitions: `appendMap m n` and `complexAppendMap a b`, `(u, v) ↦ Fin.append u v` from `TopCat.of (Fin m → 𝕜) ⊗ TopCat.of (Fin n → 𝕜)`; `appendMap_mem`, `complexAppendMap_mem` (the union of the two punctured products lands in the punctured target); `shuffleBarycenter m n`, the point ∑ₖ (1/(m + n + 1)) · `shuffleVertices` s_m s_n k.

### Proved now

| Declaration | Content |
|---|---|
| `complexRealHomeomorph_finProdFinEquiv` | coordinate `finProdFinEquiv (i, j)` of `complexRealHomeomorph p z` is `basisOneI.repr (z i) j` (Re for j = 0, Im for j = 1), from `Basis.repr_reindex_apply` and `smulTower'_repr_mk` |
| `complexRealHomeomorph_append` | statement (1), by `Fin.addCases` on the complex index: index 2i + j of block a stays 2i + j, index 2(a + i) + j becomes 2a + (2i + j) |
| `edgeMatrix_shuffleVertices` | E(σ_id) is `reindex finSumFinEquiv` of `fromBlocks E(v) B 0 E(w)`, B with every column v_m − v₀ |
| `det_edgeMatrix_shuffleVertices` | statement (2): `det_reindex_self`, `det_fromBlocks_zero₂₁` |
| `det_edgeMatrix_shuffleVertices_standard` | at s_m, s_n: (−1)^m (m + 1) · (−1)^n (n + 1) |
| `sign_det_edgeMatrix_shuffleVertices_standard_mul` | sign(det E(σ_id)) · (−1)^{m+n} = 1, the scalar of `affineSimplex_homologyπ` at σ_id |
| `appendMap_idShuffle` | the identity-shuffle singular simplex of two affine simplices, as `shuffleBilin_ι` writes it, pushed along `appendMap`, is the affine simplex on `shuffleVertices`, same vertex order (`Functor.Monoidal.μ_fst`, `μ_snd`, `toSSetObjEquiv`) |
| `affineSimplexMap_map_apply`, `appendMap_mem`, `complexAppendMap_mem` | helpers |

### Signs

| Sign | Value | Source |
|---|---|---|
| block identification ℂ^a × ℂ^b → ℂ^{a+b} on real coordinates | identity, no permutation | `complexRealHomeomorph_append` (proved). With real parts first it would be a permutation of sign (−1)^{ab} |
| identity-shuffle coefficient | +1 | `shuffleChain_idShuffle_coeff` (checked, `relative-cross-chain`) |
| coefficient change ℚ ⊗ ℚ → ℚ | 1 ⊗ 1 ↦ 1 | `shuffleBilin_ι` (checked) |
| vertex order of σ_id | (v_{min(k,m)}, w_{k−m}), first factor first | `appendMap_idShuffle` (proved), `idShuffle` |
| det E(σ_id) | det E(v) · det E(w), no further sign | `det_edgeMatrix_shuffleVertices` (proved): block upper triangular because the first factor comes first in the vertex order and in the coordinates |
| det E(s_d) | (−1)^d (d + 1) | `det_edgeMatrix_standardAffineSimplex` (checked) |
| class of σ_id at a point of its open simplex | sign(det E(σ_id)) · (−1)^{m+n} = 1 times o_y | `affineSimplex_homologyπ` (checked), `sign_det_edgeMatrix_shuffleVertices_standard_mul` (proved) |
| other shuffle simplices at the barycenter | 0 in C(ℝ^{m+n}, ℝ^{m+n} ∖ {y}) | `eq_idShuffle_of_shuffleBarycenter` (open); checked numerically below |
| translation back to 0 | none | `relativeHomologyMap_point_eq_translate`, `relativeHomologyMap_translation_injective` (checked) |
| degree casts p · 2 = 2 · p, 2(a + b) = 2a + 2b | none (transport along an equation of degrees) | to be proved by `subst` |

Product of the signs: +1 for every m, n, so the real form is stated with +, and the complex form inherits it.

**Numerical check** (Python, floating point with exact integer determinants, every pair 0 ≤ m, n ≤ 3, 16 cases): det E(σ_id) equals (−1)^m (m + 1) (−1)^n (n + 1) in all 16; the scalar sign(det E(σ_id)) · (−1)^{m+n} is 1 in all 16; and a linear program over every pair of monotone vertex maps (a, b) of length m + n + 1 other than the identity shuffle, degenerate ones included, finds no t ≥ 0 with ∑ t = 1 reaching the barycenter. That is the content of `eq_idShuffle_of_shuffleBarycenter` for those sizes.

### Route for the proofs

1. **`eq_idShuffle_of_shuffleBarycenter`.** The two components of the point have unique barycentric weights in s_m and s_n (`weights_eq_of_det_ne_zero`): α = (1/N, …, 1/N, (n + 1)/N) and β = ((m + 1)/N, 1/N, …, 1/N), N = m + n + 1. Since x.1 and x.2 are monotone, the set where x.1 ≤ i and the set where x.2 ≤ j are prefixes of Fin N, so the partial sums S_k = t₀ + … + t_k take the N values 1/N, 2/N, …, N/N at strictly increasing indices; there are N indices, so S_k = (k + 1)/N, and then x.1 k = min k m, x.2 k = k − m (`eq_idShuffle_iff`).
2. **Only σ_id survives at y.** For the barycenter y: precomposing the chain map of the pair of affine simplices with ι_x and the projection to C(ℝ^{m+n}, ℝ^{m+n} ∖ {y}) gives 0 for x ≠ idShuffle (step 1 with t the weights of a point of the realized simplex; `relProj_ι_eq_zero`). Coproduct extensionality then writes the projected shuffle chain as `simplexCoeff (idShuffle)` followed by ι of σ_id, and `shuffleChain_idShuffle_coeff`, `shuffleBilin_ι`, `appendMap_idShuffle` turn it into the projected affine simplex σ_id with coefficient 1.
3. **Real form.** Cycles of s_m, s_n on the complements of their open simplices (`exists_affineSimplex_openSimplex_cycle`); `relCrossUnion_homologyπ` gives their cross class; pushed by `appendMap` it lives on (ℝ^{m+n}, ℝ^{m+n} ∖ U), U = {z | first block ∈ openSimplex s_m, second block ∈ openSimplex s_n}, convex (`convex_openSimplex`, linear preimages), containing 0 (`zero_mem_openSimplex_standardAffineSimplex`) and y (its block weights are α and β, all positive). Its restriction at 0 is the left side of `cross_orientation_real`, by `relCrossUnion_naturality` along the support inclusions and `openSimplex_standard_restrict_zero`; at y it is o_y, by step 2, `affineSimplex_homologyπ` and `sign_det_edgeMatrix_shuffleVertices_standard_mul`. `relativeHomologyMap_point_eq_translate` and `relativeHomologyMap_translation_injective` finish.
4. **Complex form.** `standardComplexLocalClass ℚ k` is the cast of the inverse of `standardComplexRealPairIso k` applied to `standardLocalClass ℚ (k * 2)`. Move both factors by `relCrossUnion_naturality` along the inverse homeomorphisms, with a degree-cast lemma for relCrossUnion (by `subst`); the square (complexRealHomeomorph a × complexRealHomeomorph b) then `appendMap (a * 2) (b * 2)` then the reindex along `Fin.cast (Nat.add_mul a b 2)` equals `complexAppendMap a b` then `complexRealHomeomorph (a + b)` is `complexRealHomeomorph_append`; `cross_orientation_real (a * 2) (b * 2)`; and the reindex sends `standardLocalClass ℚ d` to the cast of `standardLocalClass ℚ d'` for d = d' (by `subst`, the reindex is then the identity).

### Checks for the red team

- `rfl`, `simp`, `aesop`, `decide`, `trivial`, `grind`, `norm_num` and `exact?` fail on each of the three open statements (three errors per tactic, on a copy of the file).
- `#print axioms`: the ten proved declarations and the four definitions use `propext`, `Classical.choice`, `Quot.sound` only.
- Right sides are nonzero: `standardLocalClass_ne_zero_of_pos` for the real form when m + n > 0, and for the complex form `standardComplexLocalClass_ne_zero (a + b)` through a one-line cast lemma (elaborated in scratch, every a, b). So both identities separate + from − and from 0.
- `python3 tools/check.py --no-build` rejects only the three `sorry`s of this file.

Questions for the red team: (i) whether `eq_idShuffle_of_shuffleBarycenter` should read the realized point through `affineSimplexMap`, as `appendMap_idShuffle` does, or keep the explicit vertex sum; (ii) whether the complex form should also be stated with `orient`-style transport to `setA ∪ setB` for `local-class-cross-model`, or whether that rung does the transport; (iii) the file name.

## cross-orientation: proofs

Date: 2026-11-26. All three open statements are proved with the statements as posted, with the three standard axioms, in `HodgeLadder.Local.CrossOrientation`, now imported from `HodgeLadder.lean`; `lake env lean` on the file takes about 7 s. `python3 tools/check.py` exits 0. The sign is + in every case, kernel-checked; no proof step produced a −1 or a dependence on a, b.

| Statement | Route as proved |
|---|---|
| `eq_idShuffle_of_shuffleBarycenter` | the red team's argument. `prefix_mass_eq`: barycentric weights regrouped along a vertex map (`sum_smul_comp_eq`) are unique (`weights_eq_of_det_ne_zero`), so both blocks give the t-mass of every vertex prefix. A predicate Q i k (x.1 k < i for i ≤ m, x.2 k < i − m above) is downward closed, hence `k < L i` with L i its count (`lowerSet_iff_lt_card`); its t-mass is i/N for all i ≤ N, so L i = i (`eq_of_prefix_values`), and `eq_idShuffle_iff` closes |
| `relProj_shuffle_eq` | coproduct extensionality on the chains of Δ[m] ⊗ Δ[n]: the push along `affineShuffleMap` followed by the projection to C(ℝ^{m+n}, ℝ^{m+n} ∖ {y}) equals `simplexCoeff (idShuffle)` followed by the identity-shuffle simplex, because every other simplex misses y (`toSSetObjEquiv_affineShuffleMap`, the previous row, `relProj_ι_eq_zero`); then `shuffleChain_idShuffle_coeff` |
| `cross_orientation_real` | open-simplex cycles of s_m, s_n; `relCrossUnion_naturality` along the support inclusions (`relCrossUnion_supportInclusion`) and `openSimplex_standard_restrict_zero` rewrite the left side as the restriction at 0 of the pushed class on the complement of `openPrism m n`; `relativeHomologyMap_translation_injective` and `relativeHomologyMap_point_eq_translate` move to y = `shuffleBarycenter m n` (`convex_openPrism`, `zero_mem_openPrism`, `shuffleBarycenter_mem_openPrism`); `relCrossUnion_homologyπ`, `shuffleBilin_ι`, `relProj_shuffle_eq`; `affineSimplex_homologyπ` with scalar `sign_det_edgeMatrix_shuffleVertices_standard_mul` = 1 |
| `cross_orientation_complex` | `relCrossUnion_naturality` along (complexRealHomeomorph a)⁻¹, (complexRealHomeomorph b)⁻¹; the square of pair maps commutes by `complexRealHomeomorph_append`, through `reindexPair (Nat.add_mul a b 2)`; `cross_orientation_real (a * 2) (b * 2)`; the degree casts `Nat.mul_comm`, `Nat.mul_add`, `Nat.add_mul` are read through `HEq` (`rel_cast_heq`, `relHom_heq`, `relCrossUnion_heq`, `reindexPair_heq`), each proved by `subst`, so they carry no scalar |
| `cross_orientation_orient` (C2) | `complexAppendMap_mem_union`, the identity map of pairs `isoOfSubset (Homeomorph.refl _)` with `union_eq`, and `cross_orientation_complex`; `setA`, `setB`, `orient` are defined here, as the red team asked, and `local-class-cross-model` should import them |

C1: `HodgeLadder/Tests/CrossOrientation.lean` holds `standardLocalClass_ne_neg_of_pos` and `cast_standardComplexLocalClass_ne_zero` (the red team's text), under the new test rung `cross-orientation-test`; the checker resolves a rung's declarations against its own module, so the tests take a separate rung, as other test modules do. C3: the ledger note cites the verdict; `Complex.piBasisOneI` is on the drift list above.

**What failed on the way.** `rw` with `relCrossUnion_naturality` on `supportInclusionPairMap` failed (keyed matching through `TopCat.of`) and `erw` timed out; a specialized lemma applied by `congrArg` works. Rewriting `relativeHomologyMap_comp` backwards on the cross class failed on a type that is correct only up to unfolding `crossUnionPair`; `relativeHomologyMap_homologyπ` applied twice by `.trans` works. Membership proofs written as `fun _ ha hb => ha (h hb)` with `h : Z ⊆ W` do not type-check at reducible transparency inside a rewrite motive; giving them as hypotheses avoids it.

## relative-cross-triad-naturality: statement

Date: 2026-11-26. Phase 1 (statement), branch `track/relative-cross-triad-naturality` from `c486870`. File `HodgeLadder/Relative/CrossTriadNaturality.lean`, module `HodgeLadder.Relative.CrossTriadNaturality`, namespace `HodgeLadder.Relative`, flat beside `HodgeLadder.Relative.CrossChain`; not yet imported from `HodgeLadder.lean`. The ledger's `file` hint reads `HodgeLadder/Relative/Cross/Triad/Naturality.lean`; the maintainer picks one name when the rung is posted. `lake env lean` on the file takes 4 to 6 seconds (wall clock, warm cache). Status: every declaration below is proved, with the three standard axioms (`#print axioms` on a scratch copy, deleted); the file has no `sorry`. Red team: pass with changes (`docs/sketches/relative-cross-triad-naturality.redteam.md`). **Checked 2026-11-26** (section "relative-cross-triad-naturality: red-team changes, as implemented" below). `union_mem` was renamed `triadMap_mem_union` (change 1); the text below uses the new name.

**Statements.** They are the red team's change 2 (`docs/sketches/relative-cross-chain.redteam.md`) with one refinement: the ambient chain map is written `singChainFunctor.map f` (the abbreviation of `HodgeLadder.Relative.CrossChain`) where the red team wrote `SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)`. The two are equal by `rfl` (`singChainFunctor_map_eq_chainComplexMap`, in the file), and the first form is the one `shB_naturality` and upstream's `relativeChainProjection_naturality` use, so rewriting works without `erw`.

```lean
def triadChainMap {X Y : TopCat.{0}} (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y}
    (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    triadRelativeChainComplex ℚ X A B ⟶ triadRelativeChainComplex ℚ Y A' B' :=
  cokernel.desc _ (singChainFunctor.map f ≫ triadRelativeChainProjection ℚ Y A' B')
    (triadSubspaceChainMap_map_triadRelativeChainProjection f hA hB)

@[reassoc]
lemma triadRelativeChainProjection_triadChainMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    triadRelativeChainProjection ℚ X A B ≫ triadChainMap f hA hB =
      singChainFunctor.map f ≫ triadRelativeChainProjection ℚ Y A' B' :=
  cokernel.π_desc _ _ _

lemma triadMap_mem_union {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    ∀ x ∈ A ∪ B, f x ∈ A' ∪ B'

lemma triadChainMap_triadToUnionRelativeChainMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    triadChainMap f hA hB ≫ triadToUnionRelativeChainMap ℚ Y A' B' =
      triadToUnionRelativeChainMap ℚ X A B ≫
        (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f (triadMap_mem_union f hA hB))

theorem relCross_naturality {P P' Q Q' : TopCat.{0}} (f : P ⟶ P') (g : Q ⟶ Q')
    {A : Set P} {A' : Set P'} {B : Set Q} {B' : Set Q'}
    (hf : ∀ a ∈ A, f a ∈ A') (hg : ∀ b ∈ B, g b ∈ B') {m n : ℕ}
    (x : RelativeHomology ℚ (TopPair.ofSubset A) m)
    (y : RelativeHomology ℚ (TopPair.ofSubset B) n) :
    relCross A' B' m n (relativeHomologyMap ℚ m (TopPair.ofSubsetHom f hf) x)
        (relativeHomologyMap ℚ n (TopPair.ofSubsetHom g hg) y) =
      (HomologicalComplex.homologyMap
        (triadChainMap (f ⊗ₘ g) (A' := leftProdSet A' Q') (B' := rightProdSet P' B')
          (fun _ hz => hf _ hz) (fun _ hz => hg _ hz)) (m + n)).hom
        (relCross A B m n x y)
```

Added beyond change 2, all proved: `triadChainMap_id` (the identity of `X` gives `𝟙`) and `triadChainMap_comp` (a composite of maps of triads gives the composite), which a consumer moving the cross product along a chain of homeomorphisms uses; the helpers `triadSubspaceChainMap_eq` (upstream's `C(A) ⊞ C(B) ⟶ C(X)` as a `biprod.desc` of singular chain maps, `rfl`), `subsetLeft_triadRelativeChainProjection`, `subsetRight_triadRelativeChainProjection` (chains of A, of B vanish in the triad complex, for any triad), `singChainFunctor_map_subset` (the chain map of f restricted to S ⟶ S'), and `triadSubspaceChainMap_map_triadRelativeChainProjection` (the descent obligation).

**Trivial proofs fail** (scratch copy, deleted): `rfl` and `simp` on `triadChainMap_triadToUnionRelativeChainMap` (`rfl` fails, `simp` makes no progress); `simp` and `rfl` on `triadChainMap f hA hB = 0` (no progress, not definitional); `rfl`, `simp [relCross, triadChainMap]` and `aesop` on `relCross_naturality` (all fail, goals remain at the `Exists.choose` of `relCross`). Non-vacuity of the chain map: `triadChainMap_id` makes it the identity at `f = 𝟙`, so it is nonzero whenever the triad complex is.

**Signs.** None enters. `triadChainMap` is the cokernel descent of the singular chain map of f, which carries no sign; the comparison is the cokernel descent of the identity; and the naturality is the chain-level identity `shB_naturality` (Tau Ceti's `TopCat.shuffle_naturality` with coefficient naturality) read through `relCross_homologyπ`. Register row "Relative homology cross product" covers it; no new row.

**Route as proved.**

| Statement | Route |
|---|---|
| descent obligation | `biprod.hom_ext'`; on each summand, the chain map of `(TopPair.ofSubset S).map ≫ f` factors through `(TopPair.ofSubset S').map` (`ext; rfl` on spaces), and chains of `S'` vanish in the target triad complex |
| `triadRelativeChainProjection_triadChainMap` | `cokernel.π_desc` |
| `triadChainMap_id`, `triadChainMap_comp`, `triadChainMap_triadToUnionRelativeChainMap` | cancel the epimorphism `triadRelativeChainProjection` (an instance through `inferInstanceAs (Epi (cokernel.π _))`), then the projection lemma, upstream's `triadRelativeChainProjection_triadToUnionRelativeChainMap` and `TopPair.Homotopy.relativeChainProjection_naturality` |
| `relCross_naturality` | on representatives, as `relCrossUnion_naturality`: lift both classes to ambient chains, take triad cycles from `exists_triadCycle_shuffle` on both sides, apply `relCross_homologyπ` twice, and compare the cycles by `moduleCat_iCycles_injective`, `shB_naturality` and the projection lemma |

**What failed on the way.** `rw [biprod.inl_desc_assoc]` on upstream's `triadSubspaceChainMap` fails: its summands are typed through `(chainPairFunctor ℚ).obj (TopPair.ofSubset A)).left`, and `erw` there times out. Restating it as `biprod.desc (singChainFunctor.map _) (singChainFunctor.map _)` by `rfl` and closing each summand by `Eq.trans` works. `rw` with lemmas whose middle object is `(TopPair.ofSubset S).fst` (syntactically not `X`) fails on motive types; composing equalities by `congrArg (_ ≫ ·)` and `Category.assoc` in term mode works.

**Downstream use.** `local-class-cross-model`, in its current form on `TopCat.of (Fin (a + b) → ℂ)` with `setA`, `setB`, moves `relCross` along the `Fin.append` homeomorphism with `relCross_naturality` and `triadChainMap_comp`, and moves the comparison with `triadChainMap_triadToUnionRelativeChainMap`. It still needs naturality of upstream's triad cap under `triadChainMap`, which this rung does not state (red team of `relative-cross-chain`, question (i)). Parallel track `triad-relative-cup-naturality` works on `relCup2`; if it needs a chain map of triad complexes for a map of triads, `triadChainMap` here is that map (same `cokernel.desc`), and it should import this module or `HodgeLadder.Relative.CrossTriadNaturality` should move both into one file when the two rungs are posted.

**Questions for the red team.** (i) Is the `singChainFunctor.map f` form acceptable in place of `SSet.chainComplexMap (TopCat.toSSet.map f) _` (equal by `rfl`, lemma in the file)? (ii) File name: flat `CrossTriadNaturality.lean` or the ledger's `Cross/Triad/Naturality.lean`. (iii) Should `relCrossUnion_naturality` be rederived here from `relCross_naturality` and the compatibility lemma, or left as the independent proof in `CrossChain`?

## relative-cross-triad-naturality: red-team changes, as implemented

Verdict `docs/sketches/relative-cross-triad-naturality.redteam.md`, pass with changes, none weakening a statement. Answers to the prover's questions: the `singChainFunctor.map f` form is accepted; the flat file name `HodgeLadder/Relative/CrossTriadNaturality.lean` is kept (ledger `module` set, which fixes the `file` hint of `tools/next.py`); `relCrossUnion_naturality` stays as checked, and its rederivation from `relCross_naturality` (red-team scratch, four lines) is recorded in the ledger note only.

| Change | Where it is now |
|---|---|
| 1: rename `union_mem` to `triadMap_mem_union` | `HodgeLadder.Relative.CrossTriadNaturality` |
| 2: homology form of the comparison lemma | `triadToUnionRelativeHomologyMap_triadChainMap`, the red team's text verbatim |
| 3: new rung `triad-cap-naturality` | ledger (open, foundation, depends on this rung), roadmap row; added to the `depends_on` of `local-class-cross-model`, whose note now records the cup-side route that avoids it |
| 4: non-vacuity along `complexAppendMap` | `HodgeLadder/Tests/CrossTriadNaturality.lean`, rung `relative-cross-triad-naturality-test`: `complexAppendMap_mem_setA`, `complexAppendMap_mem_setB`, `orient_eq_triadToUnion_triadChainMap`, `orient_ne_zero`, `triadChainMap_relCross_orientation_ne_zero` |
| 5: one chain map | `triadChainMap` is the canonical map; `triad-relative-cup-naturality` imports it after this rung merges |
| 6: ledger, drift list, gaps | ledger `checked`; drift list in "Pins and drift" above; `docs/gaps.md` "General lemmas kept local" |

Statements of `triad-cap-naturality` (change 3, elaborated by the red team at the pin):

```lean
theorem triadCapCohomologyLinear_triadChainMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') (p q : ℕ)
    (α : RelativeCohomology ℚ (TopPair.ofSubset A') p)
    (z : TriadRelativeHomology ℚ X A B (p + q)) :
    triadCapCohomologyLinear ℚ Y A' B' p q α
        ((HomologicalComplex.homologyMap (triadChainMap f hA hB) (p + q)).hom z) =
      relativeHomologyMap ℚ q (TopPair.ofSubsetHom f hB)
        (triadCapCohomologyLinear ℚ X A B p q
          (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hA) α) z)

theorem unionRelativeTriadCapCohomologyLinear_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') (p q : ℕ)
    (hX : QuasiIso (triadToUnionRelativeChainMap ℚ X A B))
    (hY : QuasiIso (triadToUnionRelativeChainMap ℚ Y A' B'))
    (α : RelativeCohomology ℚ (TopPair.ofSubset A') p)
    (z : RelativeHomology ℚ (TopPair.ofSubset (A ∪ B)) (p + q)) :
    unionRelativeTriadCapCohomologyLinear ℚ Y A' B' p q hY α
        (relativeHomologyMap ℚ (p + q)
          (TopPair.ofSubsetHom f (triadMap_mem_union f hA hB)) z) =
      relativeHomologyMap ℚ q (TopPair.ofSubsetHom f hB)
        (unionRelativeTriadCapCohomologyLinear ℚ X A B p q hX
          (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hA) α) z)
```

The proof also needs naturality of upstream's `relativeCochainCohomologyEquiv`, which the pin lacks (it has the absolute `cochainCohomologyEquiv_naturality` only).

`lake env lean` takes about 5 seconds on each of the two files. `python3 tools/check.py` exits 0 with both modules imported from `HodgeLadder.lean`.
## cap-cross-evaluation: statement
Date: 2026-11-26. Phase 1 (statement), branch `track/cap-cross-evaluation` from `c486870`. File `HodgeLadder/Cup/CapCrossEvaluation.lean`, module `HodgeLadder.Cup.CapCrossEvaluation`, namespace `HodgeLadder.CapCross`; not yet imported from `HodgeLadder.lean`. The brief's default path `HodgeLadder/Cap/Cross/Evaluation.lean` splits the id at its hyphens; the maintainer picks the name when the rung is posted. `lake env lean` on the file takes 4 to 7 s (warm cache). Status at the statement pass: the two homology statements are proved from one chain-level statement, which is open; four representative lemmas, the excision helper and six private pins are proved with the three standard axioms. Statement red team: pass with changes (`docs/sketches/cap-cross-evaluation.redteam.md`). **Checked 2026-11-26** with the statements unchanged; see "cap-cross-evaluation: proofs" below.
**Choices.** Coefficients ℚ, spaces in `TopCat.{0}`, the product `P ⊗ Q` with `leftProdSet A Q` (A × Q) and `rightProdSet P B` (P × B) of `relative-cross-chain`. This is the product form that the ledger note of `local-class-cross-model` names as the way around triad-level naturality: on P = ℂ^a, Q = ℂ^b, A = B = {0}ᶜ the pairs `TopPair.ofSubset A` are upstream's `puncturedPair ℂ a` by `abbrev`, so the model on the product needs no transport (scratch check below). The two projections are maps of pairs defined here (`prFstPair`, `prSndPair`, by `TopPair.ofSubsetHom` of `fst`, `snd`). The cap enters in two forms: upstream's sum-relative `triadCapCohomologyLinear` (no openness), and the customary `unionRelativeTriadCapCohomologyLinear`, which takes a proof `hExc` of the excision quasi-isomorphism as an argument; a consumer passes `quasiIso_triadToUnion_prod_of_isOpen hA hB`, and since `hExc` is a proposition the identity does not depend on it. The pairing is upstream's `relativeCohomologyEquivDualHomology` on both sides.
### Statements
def prFstPair {P : TopCat.{0}} (A : Set P) (Q : TopCat.{0}) :
    TopPair.ofSubset (X := P ⊗ Q) (leftProdSet A Q) ⟶ TopPair.ofSubset A :=
  TopPair.ofSubsetHom (fst P Q) fun _ h => h
def prSndPair (P : TopCat.{0}) {Q : TopCat.{0}} (B : Set Q) :
    TopPair.ofSubset (X := P ⊗ Q) (rightProdSet P B) ⟶ TopPair.ofSubset B :=
  TopPair.ofSubsetHom (snd P Q) fun _ h => h
-- open: the chain-level identity
theorem cap_cross_evaluation_cocycle {P Q : TopCat.{0}} (A : Set P) (B : Set Q) {m n : ℕ}
    (φ : RelativeCochain ℚ (TopPair.ofSubset A) m)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset A) m φ = 0)
    (ψ : RelativeCochain ℚ (TopPair.ofSubset B) n)
    (hψ : relativeCoboundary ℚ (TopPair.ofSubset B) n ψ = 0)
    (x : (SingularChainComplex ℚ P).X m) (y : (SingularChainComplex ℚ Q).X n)
    (zx : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).cycles m)
    (hx : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx =
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x)
    (zy : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles n)
    (hy : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy =
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y) :
    (((relativeChainFunctor ℚ).map (prSndPair P B)).f n).hom.dualMap ψ
        (triadCap ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) m n
          ((((relativeChainFunctor ℚ).map (prFstPair A Q)).f m).hom.dualMap φ)
          (((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f
            (m + n)).hom (shuffleBilin P Q m n x y))) =
      φ (((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x) *
        ψ (((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y)
-- proved from cap_cross_evaluation_cocycle
theorem cap_cross_evaluation_triad {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ)
    (φ : RelativeCohomology ℚ (TopPair.ofSubset A) m)
    (ψ : RelativeCohomology ℚ (TopPair.ofSubset B) n)
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (X := P ⊗ Q) (rightProdSet P B)) n
        (relativeCohomologyMap ℚ n (prSndPair P B) ψ)
        (triadCapCohomologyLinear ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) m n
          (relativeCohomologyMap ℚ m (prFstPair A Q) φ) (relCross A B m n x y)) =
      relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset A) m φ x *
        relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) n ψ y
-- the rung's statement; proved from the triad form
theorem cap_cross_evaluation {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ)
    (hExc : QuasiIso
      (triadToUnionRelativeChainMap ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)))
    (φ : RelativeCohomology ℚ (TopPair.ofSubset A) m)
    (ψ : RelativeCohomology ℚ (TopPair.ofSubset B) n)
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (X := P ⊗ Q) (rightProdSet P B)) n
        (relativeCohomologyMap ℚ n (prSndPair P B) ψ)
        (unionRelativeTriadCapCohomologyLinear ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)
          m n hExc (relativeCohomologyMap ℚ m (prFstPair A Q) φ) (relCrossUnion A B m n x y)) =
      relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset A) m φ x *
        relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) n ψ y
### Proved now
| Declaration | Content |
| `cap_cross_evaluation` | from the triad form: `relCrossUnion x y` is `triadToUnionRelativeHomologyMap (relCross x y)` by `rfl`, then upstream's `unionRelativeTriadCapCohomologyLinear_on_comparison` |
| `cap_cross_evaluation_triad` | from the cocycle form: representatives of φ, ψ (`moduleCatHomologyClass_surjective`, `relativeCochainCohomologyEquiv`), of x, y (`moduleCat_homologyπ_surjective`, `relProj_surjective`), the triad cycle of `exists_triadCycle_shuffle` and `relCross_homologyπ`, then the three lemmas below |
| `relEval_class` | upstream's pairing on representatives: ⟨class of φc, homologyπ z⟩ = φc(iCycles z), no sign (`linearDualHomologyEquiv_class_apply_class`) |
| `relativeCohomologyMap_class` | upstream's pullback on representatives: the class of φc goes to the class of φc ∘ f_* (`linearDualCochainComplexScIso_naturality`, which is `rfl` upstream, and `moduleCatHomologyClass_naturality`) |
| `triadCap_class_homologyπ` | upstream's sum-relative triad cap on representatives: the class of the cycle `triadCap φc (iCycles z)`, read off the middle term `triadCapHom` of `triadCapShortComplexHom`, so the factors (−1)^p of the outer terms do not enter |
| `homologyπ_eq_class` | for a short complex of modules, `homologyπ z` is the explicit class of `iCycles z` (Mathlib `moduleCatCyclesIso_inv_π`) |
| `quasiIso_triadToUnion_prod_of_isOpen` | for open A, B, the excision hypothesis on (P × Q; A × Q, P × B), from upstream's `triadToUnionRelativeChainMap_quasiIso_of_isOpen` |
| private pins | `capHom` = coproduct desc of φ(front face) • back face; `frontFace`, `backFace` through `frontInclusion` (vertex i ↦ i) and `backInclusion` (i ↦ p + i); `relativeCapLift` = `Simplicial.cap` of the cochain pulled back along the relative projection; `triadCapLiftHom` = that, then the projection to C(X, B); `unionRelativeTriadCapCohomologyLinear` = `triadCapCochainCohomologyLinear` of `relativeCochainCohomologyEquiv.symm α`, applied to the inverse of `isoOfQuasiIsoAt` of the comparison. All by `rfl`; replace by `HodgeLadder.Cup.TriadCapPins` (rung `triad-relative-cup-cap`) once it lands |
So the rung reduces to one chain-level identity, `cap_cross_evaluation_cocycle`, and the reduction is checked.
### Signs
| Fact | Value | Source |
|---|---|---|
| cap on a simplex | φ(front p-face) · back q-face, no sign | `capHom_pin` (proved by `rfl`), register row "Triad cap product" |
| cap on homology | the middle term `triadCapHom`; the (−1)^p of the outer terms does not reach homology | `triadCap_class_homologyπ` (proved) |
| evaluation | ⟨[φ], [x]⟩ = φ(x), no sign | `relEval_class` (proved), row "Universal-coefficient evaluation" |
| pullback | [φ] ↦ [φ ∘ f_*], no sign | `relativeCohomologyMap_class` (proved) |
| cross product | [x] × [y] = [shuffle(x ⊗ y)]; identity shuffle +1 | `relCross_homologyπ`, `shuffleChain_idShuffle_coeff` (checked), rows "Shuffle map", "Relative homology cross product" |
| the identity-shuffle term | φ(x) · ψ(y): its front m-face projects to x under pr₁ and its back n-face to y under pr₂ (vertices (min(k, m), k − m)) | `idShuffle`; to be used in the proof |
| other shuffle terms | each is ±φ(degenerate) · ψ(degenerate); single terms need not vanish, their sum does on cocycles and relative cycles | route below |
| Koszul evaluation | (−1)^{|ψ||x|} = (−1)^{nm}, which upstream's cap and pairing do not insert | `Dold1972`, unverified; the identity has no sign in every degree, also for m, n odd |
The identity has + in every degree, so `local-class-cross-model` gets 1 · 1 = 1 with no parity condition. The degree twist ε(k) = (−1)^{k(k−1)/2} of some conventions does not appear: upstream's pairing is plain evaluation.
### Route for the proof of `cap_cross_evaluation_cocycle`
Write α = φ ∘ relProj_A, β = ψ ∘ relProj_B (absolute cocycles on P, Q vanishing on C(A), C(B)).
1. **Cap to Alexander–Whitney.** For a chain c of degree m + n on P ⊗ Q: β(pr₂_* (pr₁^* α ⌢ c)) = ε_{α,β}(AW c), with AW Tau Ceti's `TopCat.alexanderWhitney` and ε_{α,β} the functional on (C(P) ⊗ C(Q))_{m+n} that is α ⊗ β on the (m, n) summand and 0 on the others (to be defined by `HomologicalComplex.mapBifunctorDesc`, coefficients by the left unitor). On a simplex it is `capHom_pin` against `TopCat.ιChainComplex_alexanderWhitney_f`: Tau Ceti's p-th term uses `SimplexCategory.subinterval 0 p` and `subinterval p (n − p)`, which agree with upstream's `frontInclusion`, `backInclusion` on vertices (an `ext` lemma, with the cast (m + n) − m = n).
2. **AW after shuffle.** `TopCat.shuffle_alexanderWhitney` turns AW ∘ shuffle into the simplicial composite, and `SSet.shuffleAlexanderWhitneyHomotopy` gives AW ∘ shuffle − id = d h + h d.
3. **The two homotopy terms vanish.** ε_{α,β} ∘ d = 0 in degree m + n + 1, since d(a ⊗ b) = da ⊗ b + (−1)^i a ⊗ db (Mathlib's tensor differential) and α, β are cocycles. For h d: d(x ⊗ y) = dx ⊗ y ± x ⊗ dy with dx in the image of C(A) and dy in the image of C(B) (`exists_of_relProj_eq_zero`, `relProj_d`); by `shuffleAlexanderWhitneyHomotopy_hom_naturality` along A ↪ P (and B ↪ Q), h maps C(A) ⊗ C(Q) into the image of C(A) ⊗ C(Q), where ε_{α,β} vanishes because α does on C(A); likewise for B. Degree m + n = 0 is the case of the zero differential.
4. **The identity term.** ε_{α,β}(x ⊗ y) = α(x) β(y).
A second route avoids the tensor functional: replace φ, ψ by cohomologous normalized cocycles (Mathlib's `AlgebraicTopology.DoldKan.PInfty`, natural, homotopic to the identity, zero on degenerate simplices), and note that for a simplex s of Δ[m] ⊗ Δ[n] in degree m + n other than `idShuffle`, the first projection of its front m-face or the second projection of its back n-face is degenerate (a monotone self-map of [m] or [n] other than the identity is not injective, `SimplexCategory.eq_σ_comp_of_not_injective`); then only `shuffleChain_idShuffle_coeff` remains, through `simplexCoeff`. It needs the naturality of the normalization homotopy, which is worth checking in Mathlib before choosing it. The first route uses only declarations that exist and is the planned one.
### Checks for the red team
- `rfl`, `simp`, `simp [triadCap, shuffleBilin]`, `ring` and `exact?` fail on `cap_cross_evaluation_cocycle` (copy of the file, deleted); `rfl`, `simp`, `simp [relativeCohomologyEquivDualHomology]`, `norm_num` and `exact?` fail on the triad form stated with a `sorry` body. `simp` on the triad form rewrites pr₂^* to the homology side and stops at a genuine cap.
- `#print axioms`: `relEval_class`, `relativeCohomologyMap_class`, `triadCap_class_homologyπ`, `homologyπ_eq_class`, `quasiIso_triadToUnion_prod_of_isOpen` use `propext`, `Classical.choice`, `Quot.sound` only; `cap_cross_evaluation` adds `sorryAx` through the one open statement.
- `python3 tools/check.py --no-build` rejects only the `sorry` of this file.
- Consumer shape (scratch, deleted), the product form of the model: with P = `TopCat.of (Fin a → ℂ)`, Q = `TopCat.of (Fin b → ℂ)`, A = B = {0}ᶜ, φ, ψ upstream's `normalizedRelativeCoclass (standardComplexLocalClass ℚ k) (standardComplexLocalClass_ne_zero k)`, x, y the classes `standardComplexLocalClass ℚ k`, the left side of `cap_cross_evaluation` equals 1 by `rw [cap_cross_evaluation, normalizedRelativeCoclass_pairing_self, normalizedRelativeCoclass_pairing_self, mul_one]`. This is the model on ℂ^a × ℂ^b with the cross class; `cross_orientation_complex` identifies that class with the orientation class of ℂ^{a+b} after the push along `complexAppendMap`.
- Non-vacuity: at P = Q = a point, A = B = ∅, m = n = 0 both sides are the products of the values on the vertex (`shuffleBilin_vertex`), so the identity is not 0 = 0; the consumer check above has right side 1.
Questions for the red team: (i) the form of `local-class-cross-model`. On ℂ^a ⊗ ℂ^b with the cross class s_a × s_b its identity follows from this rung alone (scratch check above), and the sign content of decision 0009 then sits in `cross_orientation_complex`. Bringing it to ℂ^{a+b} with `setA`, `setB`, `orient` needs a naturality of upstream's triad cap along the homeomorphism of triads `complexAppendMap` (upstream has none), or `relative-cross-triad-naturality` together with it. Which form should the ledger record? (ii) whether the four representative lemmas belong in `docs/gaps.md` "General lemmas kept local" (they are statements about upstream's own API); (iii) the file name.

## cap-cross-evaluation: proofs

Date: 2026-11-26. `cap_cross_evaluation_cocycle` is proved with the statement as posted, by the homotopy route the red team checked; with it the three statements are checked with the three standard axioms in `HodgeLadder.Cup.CapCrossEvaluation`, now imported from `HodgeLadder.lean`, and the red team's two tests (C1, verbatim) are checked in `HodgeLadder.Tests.CapCrossEvaluation` under the new test rung `cap-cross-evaluation-test`. `lake env lean` on the rung file takes about 10 s. No step produced a sign.

| Step | Lean |
|---|---|
| The left side is a functional of the shuffle chain | `capEval α β`, c ↦ β(pr₂_*(pr₁^*α ⌢ c)), with α = φ ∘ relProj_A, β = ψ ∘ relProj_B; reached from the triad cap by `triadCap_projection_apply`, `relativeChainProjection_naturality` (`relProj_map_apply`) and the identity of the pulled-back cochain with `Simplicial.cochainMap` |
| Cap to Alexander–Whitney | `alexanderWhitney_tensorEval`: on chains with coefficients ℚ ⊗ ℚ, `TopCat.alexanderWhitney` followed by `tensorEval α β` (Tau Ceti `tensorCochain` with the left unitor) is the coefficient change followed by `capEval α β`. Per simplex: `TopCat.ιChainComplex_alexanderWhitney_f`, `SSet.ιChainComplex_alexanderWhitney_f`, the summand p = m (the others vanish by `ιTensorObj_tensorCochain_of_ne_left`), the degree m + n − m read through a free variable as in Tau Ceti's `ιChainComplex_alexanderWhitneyDiagonal_f_tensorCochain`; upstream's `frontInclusion`, `backInclusion` are Mathlib's `subinterval 0 m`, `subinterval m n` (`frontInclusion_eq_subinterval`, `backInclusion_eq_subinterval`) |
| AW ∘ EZ = d h + h d + id | `TopCat.shuffle_alexanderWhitney`, `(SSet.shuffleAlexanderWhitneyHomotopy _ _ _ _).comm` |
| d h dies | `tensorEval_d_eq_zero`: Tau Ceti's `d_comp_tensorCochain` with d ≫ α = 0 and d ≫ β = 0 (from `hφ`, `hψ` and `relProj_d`) |
| h d dies | `d_ιTensorObj_mem`: in the four degree cases (`ιTensorObj_d_of_rel`, `_of_not_rel_left`, `_of_not_rel_right`; m = n = 0 has no boundary), d(x ⊗ y) lies in the image of C(A) ⊗ C(Q) plus that of C(P) ⊗ C(B), from `exists_d_eq_of_cycle`; `tensorEval_homotopy_left`, `_right`: `SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality` along `toSSet.map` of A → P (resp. B → Q) and `tensorHom_f_comp_tensorCochain` with α ∘ i_A = 0 (resp. β ∘ i_B = 0) |
| identity term | `ιTensorObj_tensorCochain`: (α ⊗ β)(x ⊗ y) = α(x) β(y) |

Upstream's subspace chain map `((chainPairFunctor ℚ).obj (TopPair.ofSubset A)).hom` is `SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset A).map) (ModuleCat.of ℚ ℚ)` by `rfl` (private `subspaceChainMap_pin`), as the red team asked; so is `singChainFunctor.map`, and `SingularChainComplex ℚ P` is `(TopCat.toSSet.obj P).chainComplex (𝟙_ (ModuleCat ℚ))`.

**What failed on the way.** Rewriting with `ModuleCat.hom_ofHom`, `LinearMap.comp_apply`, `cochainMap_apply` or `map_smul` in the per-simplex computation failed, because the ℚ-module instances of `ModuleCat.of ℚ ℚ`, of `𝟙_ (ModuleCat ℚ)` and of `SingularChainComplex` agree only up to unfolding; `change` to an explicit form, `erw` of the linear-map lemmas on single terms, and `ac_rfl` for the final commutation (where `ring` failed for the same reason) work. `erw` with `tensorHom_tmul` timed out; two `rfl` lemmas for `(f ⊗ₘ g) ≫ λ` and `λ ≫ f` on `r ⊗ₜ t` replace it. `rw [zero_add]` after the Leibniz rule rewrote a `0 + n'` inside the degree proof of `ιTensorObj`; `Eq.trans ?_ (zero_add _).symm` avoids it.

## triad-relative-cup-cap: statement

Statement phase, 2026-11-26; checked 2026-11-26 (paragraph "Proved after the red team" below). Two new modules, both now imported from `HodgeLadder.lean`: `HodgeLadder/Cup/TriadCapPins.lean` (the shared `rfl` pins of upstream's triad cap, all proved) and `HodgeLadder/Cup/TriadCupCap.lean` (the adjunction). The ledger's `module` was `null`; it is now `HodgeLadder.Cup.TriadCupCap`. Elaboration with `lake env lean`: about 4 seconds for each file, once `HodgeLadder.Cup.TriadCup` and upstream's `Other/AlgebraicTopology/Singular/Cap/Triad.lean` are built (both are, in the shared cache and in the worktree).

**The adjunction.** For `X : TopCat.{0}` and `A B : Set X`:

```lean
theorem relCup2_eval_eq_eval_triadCap (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (φ : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (ψ : RelativeCohomology ℚ (TopPair.ofSubset B) q)
    (z : RelativeHomology ℚ (TopPair.ofSubset (A ∪ B)) (p + q)) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (A ∪ B)) (p + q)
        (relCup2 X A B hA hB φ ψ (p + q) rfl) z =
      relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) q ψ
        (unionRelativeTriadCapCohomologyLinear ℚ X A B p q
          (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB) φ z)
```

Both pairings are upstream's universal-coefficient evaluation `relativeCohomologyEquivDualHomology` (= `linearDualHomologyEquiv` of the relative chain complex; register row "Universal-coefficient evaluation", ⟨[c], [x]⟩ = c(x), no sign), on (X, A ∪ B) on the left and on (X, B) on the right. The cap is upstream's `unionRelativeTriadCapCohomologyLinear` with the excision proof `triadToUnionRelativeChainMap_quasiIso_of_isOpen`, the term in the statement of `local_class_cross_cap` (rung `local-class-cross-model`, open); any other proof of `QuasiIso` is the same term by proof irrelevance. Sign: none. Source: `Hatcher2002` §3.3 (section recalled), ψ(σ ⌢ φ) = (φ ⌣ ψ)(σ) with σ ⌢ φ = φ(σ|[v₀, …, v_p]) σ|[v_p, …, v_{p+q}], in the relative form C_n(X, A + B) × C^p(X, A) → C_{n−p}(X, B).

Corollary `relCup2_dual_eq`: the same identity as linear forms, `relativeCohomologyEquivDualHomology … (relCup2 φ ψ) = (relativeCohomologyEquivDualHomology … ψ).comp (unionRelativeTriadCapCohomologyLinear … φ)`, by `LinearMap.ext`.

**Use in `local-class-product`.** With φ, ψ the pullbacks of u_a, u_b along `projA`, `projB` and z = `orient a b`, `local_class_cross_cap` says the right side is 1 (p = 2a, q = 2b, so p + q is `2 * a + 2 * b` syntactically, the degree of `orient`). The adjunction gives `relativeCohomologyEquivDualHomology … (relCup2 … (2 * a + 2 * b) rfl) (orient a b) = 1`, which is the hypothesis `hβ` of upstream's `normalizedRelativeCoclass_unique`; with `span_standardComplexLocalClass_eq_top` transported along the identity pair map, the cup is the normalized class of `orient`, the cup form.

**Pins** (`HodgeLadder.Cup.TriadCapPins`, red-team hand computation 5; general in `R : Type u` and the universe, so `cap-cross-evaluation` can import them in place of its private copies):

| Step | Pins |
|---|---|
| simplex cap | `frontInclusion_val` (vertex i ↦ i), `backInclusion_val` (vertex i ↦ p + i), `frontFace_eq`, `backFace_eq`, `capHom_eq` (the cofan of x ↦ φ(front x) • back x), `cap_eq`, `cap_chainOfSimplex_eq` (the formula on a simplex, right side written out), `chainOfSimplex_eq` (the generator 1 of its summand) |
| triad complex | `triadSubspaceChainMap_pin` (`biprod.desc` of the two inclusions), `triadRelativeChainComplex_eq`, `triadRelativeChainProjection_eq` (cokernel and its projection), `triadToUnionRelativeChainMap_eq`, `triadRelativeChainProjection_triadToUnionRelativeChainMap_eq` (the comparison is induced by the identity of C(X)) |
| relative cap | `relativeCochainToAbsolute_eq` (dual of the relative projection), `relativeCapLift_eq` |
| triad chain level | `triadCapLiftHom_eq` (lift then C(X) → C(X, B)), `triadCap_eq`, `triadRelativeChainProjection_triadCapHom_eq` (φ ⌢ [c] = [φ̃ ⌢ c]) |
| signs | `triadCapShortComplexHom_τ₂_eq` (middle map `triadCapHom`, no sign), `triadCapShortComplexHomSucc_τ₁_eq`, `_τ₃_eq`, `triadCapShortComplexHomZero_τ₁_eq` (outer maps (−1)^p • `triadCap`) |
| descent | `triadCapHomologyMap_eq`, `triadCapCocycleHomologyLinear_eq`, `triadCapCochainCohomologyLinear_eq`, `triadCapCohomologyExplicitLinear_mk`, `relativeCohomologyCycleToCocycle_val`, `triadCapCohomologyLinear_eq`, `relativeCochainCohomologyEquiv_symm_eq` (the inverse is `homologyMap` of `linearDualCochainComplexScIso`, the identification `linearDualHomologyEquiv` also goes through) |
| excision inverse | `triadToUnionRelativeHomologyMap_eq`, `triadUnionExcisionHomologyEquiv_symm_eq` (`(isoOfQuasiIsoAt τ n).inv`), `unionRelativeTriadCapCohomologyLinear_eq`, and the composite `unionRelativeTriadCapCohomologyLinear_apply_eq` |

All 33 are `rfl` except `cap_chainOfSimplex_eq`, `triadRelativeChainProjection_triadCapHom_eq`, `triadCapShortComplexHom_τ₂_eq`, `triadRelativeChainProjection_triadToUnionRelativeChainMap_eq`, which restate an upstream lemma with its right-hand side written out, so that a change of the upstream formula breaks the statement. Standard axioms. Drift list addition for the next bump: `chainOfSimplex`, `triadCapShortComplexHomZero` (the other pinned names are already on it).

**Proved now** (`HodgeLadder.Cup.TriadCupCap`, standard axioms):

| Declaration | Content |
|---|---|
| `frontInclusion_eq_subinterval`, `backInclusion_eq_subinterval` | upstream's cap faces are Mathlib's `SimplexCategory.subinterval 0 p` and `subinterval p q`, the faces of Tau Ceti's Alexander–Whitney diagonal |
| `cupCochain_eq_capLift` | chain level, no sign: `cupCochain ℚ (awX X) (λ_ _).hom p q (p + q) rfl (proj_A ≫ φ) (proj_B ≫ ψ) = ofHom (relativeCapLift φ) ≫ proj_B ≫ ψ` on C_{p+q}(X); proof on simplices from `cochainValuesEquiv_cupCochain_alexanderWhitneyDiagonal` and `iota_capHom` |
| `relCup2_eval_eq_eval_triadCap` from `triadEval_relCup2` | write z = τ_*(w) with w = (isoOfQuasiIsoAt τ (p + q)).inv z; the right side is the sum-relative cap at w by `rfl`; upstream's `HomologicalComplex.linearDualHomologyEquiv_naturality` along τ moves the left side to the triad complex, where `triadExcisionCoh.hom` is the dual of τ by definition |

**Proved after the red team** (2026-11-26). `triadEval_relCup2`, with the helpers `relativeCochainCohomologyEquiv_symm_homologyπ` and `relativeCohomologyEquivDualHomology_triadCapCohomologyLinear_homologyπ`, is proved along the route of the verdict `docs/sketches/triad-relative-cup-cap.redteam.md` (Appendix A): one bridge lemma on the cap side, both pairings through the port's `HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply`. The rung is `checked`. The seven pins of Appendix B are in `HodgeLadder.Cup.TriadCapPins` (rung `triad-cap-pins`; the subspace-map pin is `triadSubspaceChainMap_pin`, to stay distinct from `HodgeLadder.Relative.triadSubspaceChainMap_eq`), and the non-vacuity corollary of Appendix C is `HodgeLadder.Tests.exists_eval_relCup2_ne_zero` (rung `triad-relative-cup-cap-test`).

## Sources

`Hatcher2002` (§3.2 relative cup, §3.B cross products), `MilnorStasheff1974` (Thom class of a product, complex orientation; section numbers unverified), `Bredon1993` (cross and cap products; unverified), `Dold1972` (Koszul sign conventions; unverified), `Fulton1998` ch. 19 (why: the cycle map is a ring homomorphism; numbering unverified). The determinant (−1)^d (d + 1) is checked in Lean (`det_edgeMatrix_standardAffineSimplex`). The block determinant is a hand computation with an exact check for 1 ≤ m, n ≤ 4 (red team of `real-affine-orientation`); it is to be checked in Lean in `cross-orientation`.
