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

## Sources

`Hatcher2002` (§3.2 relative cup, §3.B cross products), `MilnorStasheff1974` (Thom class of a product, complex orientation; section numbers unverified), `Bredon1993` (cross and cap products; unverified), `Dold1972` (Koszul sign conventions; unverified), `Fulton1998` ch. 19 (why: the cycle map is a ring homomorphism; numbering unverified). The determinant (−1)^d (d + 1) and the block determinant are hand computations, unverified in Lean.
