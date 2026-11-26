# Red team: `triad-relative-cup` (statement)

Date: 2026-11-26. Worktree branch `track/triad-relative-cup` at base `8b3a2fa`, uncommitted `HodgeLadder/Cup/TriadCup.lean` and the section "triad-relative-cup: statement" of `docs/sketches/local-class-product.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713` (the package source in `.lake/packages` is at the same commit), Lean and Mathlib `v4.35.0-rc4`.

Read: the ledger entries `triad-relative-cup`, `triad-relative-cup-naturality`, `triad-relative-cup-cap`; the statement file; the sketch section; decision 0010; finding 15 of `docs/sketches/cycle-class-multiplicative.redteam.md`; `docs/conventions.md`; `docs/references.md`; the checked `HodgeLadder/Cup/{SingularCup,RelativeCup,RelCupCocycle,RelCupNaturality}.lean`; at the pin `Other/AlgebraicTopology/Singular/Cap/Triad.lean` (`triadSubspaceChainMap`, `triadRelativeChainComplex`, `triadRelativeChainProjection`, `triadToUnionRelativeChainMap`, `triadRelativeChainProjection_triadToUnionRelativeChainMap`, `unionRelativeTriadCapCohomologyLinear`), `Other/AlgebraicTopology/Singular/Excision/Triad.lean` (`triadToUnionRelativeChainMap_quasiIso_of_isOpen`, `_of_openCover`), `Other/AlgebraicTopology/Singular/EmptySubspace.lean`, `HodgeConjecture/Mathlib/Topology/Category/TopPair.lean` (`ofSubsetHom`, `isoOfSubset`), `Definitions/AlgebraicTopology/Singular/Cohomology.lean` (`RelativeCohomology`, `relativeCohomologyMap`, `relativeChainProjection`), `Definitions/Algebra/Homology/LinearDual.lean` (`linearDualMap`, `linearDualMap_comp`).

Scratch (inside the worktree, deleted afterwards): RT1 elaborates the file and prints axioms of the definitions; RT2 proves `forgetRel_relCup2`; RT3 proves `forgetRel_empty_bijective`; RT4 states and proves a cocycle formula for `relCup2`; RT5 proves `relCup2_empty`; RT6 elaborates the statements of `triad-relative-cup-naturality` and `triad-relative-cup-cap` against `relCup2`; a consolidated file with all proofs and a torus test compiles sorry-free (Appendix).

**Verdict: pass with changes.** `relCup2` is Hatcher's relative cup H^p(X, A) × H^q(X, B) → H^{p+q}(X, A ∪ B) for open A, B, with the A factor first, front face of the A cochain times back face of the B cochain, and no sign. No comparison map in the construction carries a sign or a scalar. The three theorems are true as stated: all three are proved in scratch with the standard axioms (Appendix), so the rung can land as `checked` in one step. The changes: the two compatibility theorems do not determine `relCup2` (finding 3), so add the cocycle formula, already proved in scratch, to the rung; fix the ledger title and one sentence of the sketch; settle where the empty-subspace lemma lives; add a non-vacuity test; add the register row (done).

## 1. Is this the statement the literature makes?

Source: [`Hatcher2002` §3.2]. For A, B open in X, the cup product of cochains C^k(X, A; R) × C^l(X, B; R) → C^{k+l}(X, A + B; R), where C^n(X, A + B) consists of the cochains on X that vanish on sums of chains in A and chains in B. The inclusion C^n(X, A ∪ B) ⊆ C^n(X, A + B) induces an isomorphism on cohomology when A and B are open (Hatcher derives it from the small-chains result, Prop. 2.21, and the five lemma). The cup is (φ ⌣ ψ)(σ) = φ(σ|[v₀, …, v_k]) · ψ(σ|[v_k, …, v_{k+l}]), with no sign. (Page numbers and the exact proposition number of the excision step are recalled from the book, not re-read; status of the citation: as in `docs/references.md`.)

| Hatcher | Lean | Check |
|---|---|---|
| R a commutative ring | ℚ | narrower, sufficient; rationality is used only by `homologyMap_linearDualMap_bijective` (dualizing a quasi-isomorphism) |
| H^k(X, A; R) | `RelativeCohomology ℚ (TopPair.ofSubset A) p`, the cohomology of Hom(C(X)/C(A), ℚ) (upstream) | same object |
| H^l(X, B; R) | same, for B | same |
| target H^{k+l}(X, A ∪ B) | `RelativeCohomology ℚ (TopPair.ofSubset (A ∪ B)) n` with `h : p + q = n` | same; the degree is passed with a proof, as in `cupSing` and `relCupSing` |
| C^n(X, A + B) | Hom(`triadRelativeChainComplex ℚ X A B`, ℚ), the cokernel of C(A) ⊞ C(B) → C(X) (`triadSubspaceChainMap` is `biprod.desc` of the two inclusions, so its image is C(A) + C(B)) | same complex |
| φ ⌣ ψ on C(X, A + B) | Tau Ceti `cup` along `triadDiagonal` = `cokernel.desc` of `awX X ≫ (proj_A ⊗ proj_B)`, μ = `(λ_ _).hom` | same formula: `triadProj_cupCochain` (Appendix, proved) says the triad cup cochain pulled back to C(X) is the Alexander–Whitney cup of the two pulled-back cochains, and the register row "Singular cup product" pins that as φ(front) · ψ(back) |
| C^n(X, A ∪ B) → C^n(X, A + B) induced by inclusion | `triadExcisionCoh.hom` = homology of `linearDualMap (triadToUnionRelativeChainMap ℚ X A B)`; the chain map is induced by the identity of C(X) (`triadRelativeChainProjection_triadToUnionRelativeChainMap`) | same map |
| it is an isomorphism for A, B open | `triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB`, then `homologyMap_linearDualMap_bijective` | same theorem, over ℚ |
| relative cup = inverse of that isomorphism after the cochain cup | `relCup2 = (triadExcisionCoh).inv ∘ (triadCohIso).inv ∘ cup` | same composite |

The factor order is Hatcher's: the first argument is the A-relative class and is evaluated on the front face. Field by field the definition is the literature's. With B = ∅ the cochain formula is the one-sided relative cup H^p(X, A) × H^q(X) → H^{p+q}(X, A), which is `relCupSing` (register row "Relative singular cup product"); `relCup2_empty` states that with the two identifications made explicit.

## 2. Can the hypotheses be satisfied?

Yes, for every space: A = B = ∅ with `isOpen_empty`; and on the ladder's spaces, A = X(ℂ) ∖ Z and B = X(ℂ) ∖ W for closed analytic Z, W. The theorems quantify over all classes a, b, so there is no hypothesis on them. A non-vacuous instance, compiled in the consolidated scratch file:

```lean
include h₁ h₂ in
theorem torusEval_relCup2_winding (a₁ a₂ : RelativeCohomology ℚ (TopPair.ofSubset (∅ : Set Y)) 1)
    (ha₁ : forgetRel _ 1 a₁ = windingClass g₁ hg₁) (ha₂ : forgetRel _ 1 a₂ = windingClass g₂ hg₂) :
    torusEval hT₁ hT₂ (forgetRel (TopPair.ofSubset ((∅ : Set Y) ∪ ∅)) 2
      (relCup2 Y ∅ ∅ isOpen_empty isOpen_empty a₁ a₂ 2 rfl)) = 1 := by
  rw [forgetRel_relCup2, ha₁, ha₂]
  exact torusEval_cupSing_winding hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂
```

The lifts a₁, a₂ exist by `forgetRel_empty_bijective`. Swapping the factors gives −1 (`torusEval_cupSing_winding_swap`), so the test detects a swap of the factors.

## 3. Is the conclusion trivially true for a reason unrelated to the mathematics?

No. The sketch reports that `rfl`, `simp`, `aesop`, `decide` fail; the proofs that do work (Appendix) use the content: `forgetRel_relCup2` takes about 35 lines through the identity π ≫ τ = proj_{A∪B}, `cokernel.π_desc` for the triad diagonal and Tau Ceti's `cup_naturality`; `relCup2_empty` takes about 55 lines through the factorization τ' ≫ `relDiagonal` = `triadDiagonal` ≫ (𝟙 ⊗ proj_∅⁻¹) and the vanishing of C(∅). `forgetRel_empty_bijective` is two lines once C(∅) = 0 is known (about 15 lines, from the barycenter of Δⁿ). No definition unfolds to `True`, no index type is empty, there is no `ℕ∞`, and `hA`, `hB` are used (only through excision, which is where Hatcher uses openness).

The two compatibility theorems do not pin `relCup2` down. `forgetRel : H^n(X, A ∪ B) → H^n(X)` has kernel the image of δ : H^{n−1}(A ∪ B) → H^n(X, A ∪ B), and `relCup2_empty` constrains only B = ∅. Counterfeit: X = S¹ ⊔ {z}, A and B disjoint open arcs of S¹. Then H^1(X, A) ≅ ℚ, H^0(X, B) ≅ ℚ (the indicator of {z}), and the kernel of forgetRel in H^1(X, A ∪ B) is one-dimensional, spanned by δc for c a class separating the two arcs. The bilinear map (a, b) ↦ relCup2 a b + λ(a)μ(b)·δc (λ, μ nonzero functionals, and the correction set to 0 whenever B = ∅) satisfies both theorems and differs from `relCup2`. A class of this kind is exactly what `local-class-product` needs: the product it uses lives in H^{2p+2q}(X, X ∖ T) and is evaluated on a local orientation class, information that forgetRel discards. So the rung as posted certifies the definition only through its text, and the downstream value is fixed by `triad-relative-cup-cap` (pairing against all of H_n(X, A ∪ B) is faithful over ℚ by upstream's `relativeCohomologyEquivDualHomology`) or by a cocycle formula.

The cocycle formula is cheap and is proved in scratch (Appendix): `triadExcisionCoh_relCup2_homologyπ` (through triad excision, `relCup2 [c] [d]` is the class of the triad cup cocycle `triadCupCycles c d`) and `triadProj_cupCochain` (that cocycle, pulled back along the epimorphism C(X) → C(X)/(C(A) + C(B)), is the Alexander–Whitney cup of c and d pulled back to C(X)). Together with the injectivity of `triadExcisionCoh.hom`, the surjectivity of `homologyπ` and the injectivity of pulling back along an epimorphism, they determine `relCup2` as Hatcher's product. They are the triad analogues of the checked `relCupSing_homologyπ` and `relProj_cupCochain` (rung `relative-cup-cocycle`), and `triad-relative-cup-cap` will start from them. Recommended change 1.

## 4. Interface rung

Not applicable: no structure, no axioms. The definitions are explicit.

## 5. Checker

The rung is not checked. `python3 tools/check.py --no-build` in the worktree: the sorry scan rejects `TriadCup.lean:152, 168, 173` (the three statement-phase sorries, expected), and the axioms step fails because the worktree's `.lake/build` lacks `HodgeLadder/Normalization/ChartStep.olean` (environment, unrelated to this file). `#print axioms` in scratch, on the file as written: `triadDiagonal`, `triadCohIso`, `triadExcisionCoh`, `relCup2`, `unionEmptyIso`, `homologyMap_linearDualMap_bijective` depend on `[propext, Classical.choice, Quot.sound]`. In the consolidated proved file, `forgetRel_relCup2`, `relCup2_empty`, `forgetRel_empty_bijective`, `triadExcisionCoh_relCup2_homologyπ`, `triadProj_cupCochain` and the torus test have the same three axioms. The declarations are the ones the ledger title means; the ledger's `declarations` list is empty and `module` is `null`, to be filled when the rung lands.

## 6. Conventions

| Convention | Where | Check | Truth depends on it? |
|---|---|---|---|
| Alexander–Whitney diagonal, front face times back face | `awX X`, Tau Ceti `TopCat.alexanderWhitneyDiagonal` with u = `(λ_ _).inv` | row "Singular cup product" (checked formula `cochainValuesEquiv_cupCochain_alexanderWhitneyDiagonal`) | yes: both identities |
| factor order: A factor is the left tensor factor | `triadDiagonal` = `cokernel.desc (awX X ≫ (proj_A ⊗ proj_B))` | matches `cupSing` (first argument front) and `relCupSing` (relative factor first) | yes: swapping changes `forgetRel_relCup2` by (−1)^{pq} through `cupSing_gradedComm`, and `relCup2_empty` would not typecheck |
| multiplication μ = `(λ_ _).hom` | `relCup2` | same μ as `cupSing`, `relCupSing` | yes, scale |
| upstream cochains to Tau Ceti cochains | `dualIsoYoneda`, degreewise `ModuleCat.homLinearEquiv.symm`, differentials agree by `rfl` | no degree sign; the same transport is used for A, B, the triad complex and C(X) | yes; with a degree sign ε(n) on one side only, the identities would fail by ε(p)ε(q)ε(n) |
| coboundary δφ = φ ∘ ∂ | upstream `linearDualCochainComplex` | row "Singular coboundary" | no sign enters |
| triad excision | `triadExcisionCoh.hom` = dual of `triadToUnionRelativeChainMap`, induced by 𝟙_{C(X)} | `triadRelativeChainProjection_triadToUnionRelativeChainMap` at the pin; inverse of a bijection, no choice | yes; no sign or scalar |
| B = ∅ identifications | `unionEmptyIso` = `TopPair.isoOfSubset (Homeomorph.refl X)`; its ambient map is `𝟙 X` by `rfl` (used in the scratch proof); `forgetRel` on (X, ∅) is the dual of the isomorphism C(X) → C(X)/C(∅) | no sign | yes: `relCup2_empty` |
| direction of `relativeCohomologyMap` | upstream: `relativeCohomologyMap ℚ n f : H^n(Q) → H^n(P)` for `f : P ⟶ Q` | `(unionEmptyIso X A).hom : (X, A ∪ ∅) ⟶ (X, A)` pulls H^n(X, A) back to H^n(X, A ∪ ∅), as the statement needs | typing only |

Borrowed results and their conventions: `triadToUnionRelativeChainMap_quasiIso_of_isOpen` is a quasi-isomorphism statement about the very map used, so no convention enters; `cup_naturality` (Tau Ceti) is sign-free (pullback of both factors and of the diagonal); `linearDualHomologyEquiv_naturality` is used only to prove bijectivity. New register row "Triad relative cup product (relCup2)" added; the row "Triad cap product" now names `triad-relative-cup-cap` for the adjunction.

## 7. Equality first

Both theorems are identities between classes, with no scalar and no sign, proved exactly in scratch. The rung is a definition with its compatibilities, not an inclusion. Its role: the product step of `local-class-product`, on the way to the identity `cycle-class-multiplicative` ([Z] ∪ [W] = [T]); both rungs exist (open).

## 7b. Non-vacuity

Smallest test that fails if `relCup2` were zero or had the factors swapped: `torusEval_relCup2_winding` above, from this repository's checked `torusEval_cupSing_winding`, `windingClass`, `torusEval` (`HodgeLadder/Cup/WindingTorus.lean`) and upstream's `TopPair.ofSubset`, `isOpen_empty`. It does not exist yet; it compiles in scratch (recommended change 4). It covers only A = B = ∅. The smallest sign-visible test with both subspaces nonempty is `local-class-cross-model` at a = b = 1 (open), which goes through `triad-relative-cup-cap`.

## 8. Pin drift

Not applicable: the rung has no checked version to compare against. The definitions use, at `2ead713`: `triadSubspaceChainMap`, `triadRelativeChainComplex`, `triadRelativeChainProjection`, `triadToUnionRelativeChainMap`, `triadRelativeChainProjection_triadToUnionRelativeChainMap`, `triadToUnionRelativeChainMap_quasiIso_of_isOpen` (library `Other`, outside upstream's statement guard), `TopPair.ofSubset`, `TopPair.isoOfSubset`, `TopPair.ofSubsetHom`, `relativeChainProjection`, `relativeCohomologyMap`, `HomologicalComplex.linearDualMap` and `linearDualMap_comp` (a `rfl` lemma, contravariant), `linearDualHomologyEquiv`, `linearDualHomologyEquiv_naturality`. The proofs add `TopPair.Homotopy.relativeChainProjection_naturality`. Add these to the drift list of the sketch's section "Pins and drift" (the sketch already proposes the first four and `isoOfSubset`). A change of `triadToUnionRelativeChainMap` away from "induced by the identity" or a sign in `isoOfSubset` would change the truth of the identities; both are read from source at the pin.

## Findings

1. **Definition matches the literature** (§1). `relCup2` is Hatcher's relative cup for open A, B, A factor first, no sign. No change.
2. **No sign in the identifications.** `dualIsoYoneda` has no degree sign (componentwise `homLinearEquiv`, differentials equal by `rfl`); `triadExcisionCoh` and `unionEmptyIso` are induced by identities; `forgetRel` on (X, ∅) is the dual of an isomorphism. No change.
3. **The two compatibilities do not characterize `relCup2`** (§3, counterfeit on S¹ ⊔ {z}). Add the cocycle formula to this rung (change 1).
4. **All three theorems are true**; proofs in the Appendix, standard axioms. The rung can move from statement to `checked` in one pull request.
5. **`relCup2_empty` is the right normalization.** B = ∅ gives `relCupSing a (forgetRel b)` read on (X, A) through the identity of X, with no sign; `forgetRel` on (X, ∅) is the identification H^q(X, ∅) ≅ H^q(X) induced by C(X) ≅ C(X, ∅), which is the standard one.
6. **Ledger title is imprecise.** "relCup2 a b = relCupSing a b when B = ∅" does not typecheck: b lives in H^q(X, ∅), and the target pair is (X, A ∪ ∅). Change 2.
7. **Sketch says the ledger entry names `HodgeLadder/Triad/Relative/Cup.lean`.** The ledger's `module` is `null`. Change 3.
8. **Empty subspace.** `forgetRel_empty_bijective` needs C(∅) = 0. Upstream proves it (`relativeChainProjection_empty_isIso`, `Other/AlgebraicTopology/Singular/EmptySubspace.lean`), but that file is not built in the shared package cache. Either import it (one upstream `Other` file to compile; its imports are built) or keep the local copy from the Appendix (`emptyChain_zero`, about 15 lines) and record it in `docs/gaps.md` "General lemmas kept local" as a copy of the upstream lemma. If kept local, prefer a `lemma` and a local `haveI` over a global `instance projEmpty_isIso`, so a later import of upstream's file does not add a second instance. Change 5.
9. **Duplicate helper.** The proofs need the pullback-through-`dualIsoYoneda` lemma; it exists as `homologyMap_dualIsoYoneda_apply` in `HodgeLadder/Cup/RelCupNaturality.lean`. Import that module and drop the restatement.
10. **Downstream fit.** RT6 elaborates the naturality statement (with `TopPair.ofSubsetHom f` on (X', A' ∪ B') → (X, A ∪ B), (X', A') → (X, A), (X', B') → (X, B)) and the cap adjunction against upstream's `unionRelativeTriadCapCohomologyLinear ℚ X A B p q (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB) φ z` with `relCup2 … (p + q) rfl`; both typecheck. The pairs (X, X ∖ Z), (X, X ∖ W) are of the form `TopPair.ofSubset` with open subsets, and A ∪ B = X ∖ (Z ∩ W) needs the identity-on-points iso already planned (`unionComplIso`). Ambient openness is what every planned use has; upstream's cap takes `hExcision : QuasiIso (triadToUnionRelativeChainMap ℚ X A B)` instead, and by proof irrelevance the two agree. A generalization to `IsOpen` in A ∪ B (`triadToUnionRelativeChainMap_quasiIso_of_openCover`) can wait. No change.
11. **`homologyMap_linearDualMap_bijective`** is general (any quasi-isomorphism of ℚ-chain complexes); list it in `docs/gaps.md` "General lemmas kept local", as the sketch says.

## Recommended changes

1. Add to `HodgeLadder/Cup/TriadCup.lean` and to the rung's `declarations`: `triadCupCycles`, `triadExcisionCoh_relCup2_homologyπ`, `triadProj_cupCochain` (exact Lean in the Appendix, compiled).
2. Ledger title: "The relative-relative singular cup relCup2 : H^p(X, A) × H^q(X, B) → H^{p+q}(X, A ∪ B) for open A, B, defined through upstream's triad excision, with forgetRel (relCup2 a b) = cupSing (forgetRel a) (forgetRel b), relCup2 a b = relCupSing a (forgetRel b) on (X, A ∪ ∅) = (X, A) when B = ∅, and the cocycle formula".
3. Sketch, section "triad-relative-cup: statement", first paragraph: replace "(the ledger entry names `HodgeLadder/Triad/Relative/Cup.lean`; the module path is set when the rung is proved)" with "(the ledger's `module` is set when the rung is proved)".
4. Add `torusEval_relCup2_winding` (§2) to `HodgeLadder/Tests/`, importing `HodgeLadder.Cup.WindingTorus`.
5. Empty subspace: as in finding 8, and record the choice in `docs/gaps.md`.
6. Replace the restated pullback helper by `homologyMap_dualIsoYoneda_apply` (finding 9); the Appendix already does.

## What was tried

- Trivial closers on the three theorems: the sketch's `rfl`, `simp`, `aesop`, `decide` fail; not repeated. A ten-line proof of `forgetRel_relCup2` was not found; the working proof needs the excision factorization and `cup_naturality`.
- A wrong product satisfying both theorems: found on paper (§3); not formalized, since the theorems' insufficiency is a fact about the kernel of forgetRel and needs no Lean.
- A degree sign in `dualIsoYoneda` or the Tau Ceti Yoneda differential: excluded by the `rfl` in `dualIsoYoneda`'s commutation proof.
- The first attempts at `relCup2_empty` failed on `Functor.map_id` resolving to the core `Functor` (qualify as `CategoryTheory.Functor.map_id`) and on `simp` not simplifying `proj ≫ inv proj` under the tensor (use `erw [IsIso.hom_inv_id]`). The `cohIso_forgetRel` rewrites need `erw`, since `(TopPair.ofSubset A).fst` and `X` agree only up to unfolding.

## Appendix: proofs compiled in scratch

Import changes: replace `public import HodgeLadder.Cup.RelativeCup` by `public import HodgeLadder.Cup.RelCupNaturality` and add `import Mathlib.Geometry.Convex.ConvexSpace.Barycenter` (prebuilt Mathlib module, for `Convexity.StdSimplex.barycenter`). The block below replaces everything from the docstring of `forgetRel_relCup2` to `end HodgeLadder.Cup` (it restates `unionEmptyIso` unchanged). The torus test needs `public import HodgeLadder.Cup.WindingTorus`; move it to a test module.

```lean
set_option backward.isDefEq.respectTransparency false in
/-- **Forgetting the subspaces carries `relCup2` to the singular cup product**, no sign:
`forgetRel (relCup2 a b) = cupSing (forgetRel a) (forgetRel b)` in `H^{p+q}(X)`. -/
theorem forgetRel_relCup2 (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (a : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset B) q) (n : ℕ) (h : p + q = n) :
    forgetRel (TopPair.ofSubset (A ∪ B)) n (relCup2 X A B hA hB a b n h) =
      cupSing X (forgetRel (TopPair.ofSubset A) p a) (forgetRel (TopPair.ofSubset B) q b) n h := by
  have key : ∀ z, forgetRel (TopPair.ofSubset (A ∪ B)) n z =
      HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        (triadRelativeChainProjection ℚ X A B)) n ((triadExcisionCoh X A B hA hB n).hom z) := by
    intro z
    unfold forgetRel
    rw [← triadRelativeChainProjection_triadToUnionRelativeChainMap,
      HomologicalComplex.linearDualMap_comp, HomologicalComplex.homologyMap_comp]
    rfl
  rw [relCup2, key, Iso.inv_hom_id_apply]
  apply (cohIso X n).toLinearEquiv.injective
  change (cohIso X n).hom _ = (cohIso X n).hom _
  rw [cupSing, Iso.inv_hom_id_apply]
  have e1 := cohIso_forgetRel (TopPair.ofSubset A) p a
  have e2 := cohIso_forgetRel (TopPair.ofSubset B) q b
  have e3 := homologyMap_dualIsoYoneda_apply (triadRelativeChainProjection ℚ X A B) n
    ((triadCohIso X A B n).inv
      (TauCeti.ChainComplex.cup ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
        ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b)))
  have hD : triadRelativeChainProjection ℚ X A B ≫ triadDiagonal X A B =
      awX X ≫ (relativeChainProjection ℚ (TopPair.ofSubset A) ⊗ₘ
        relativeChainProjection ℚ (TopPair.ofSubset B)) := cokernel.π_desc _ _ _
  have hn := TauCeti.ChainComplex.cup_naturality (k := ℚ) (D := triadDiagonal X A B)
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (awX X) (triadRelativeChainProjection ℚ X A B)
    (relativeChainProjection ℚ (TopPair.ofSubset A))
    (relativeChainProjection ℚ (TopPair.ofSubset B)) hD p q n h
    ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b)
  have e4 : HomologicalComplex.homologyMap (dualIsoYoneda (triadChains X A B)).hom n
      ((triadCohIso X A B n).inv
        (TauCeti.ChainComplex.cup ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
          ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b))) =
      TauCeti.ChainComplex.cup ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
          ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b) :=
    Iso.inv_hom_id_apply (triadCohIso X A B n) _
  change HomologicalComplex.homologyMap (dualIsoYoneda _).hom n _ = _
  rw [e3, e4, tcCup_eq]
  erw [e1, e2]
  exact hn.symm

/-- The pair `(X, A ∪ ∅)` is the pair `(X, A)`: the identity of `X`, which maps `A ∪ ∅` onto
`A` (upstream `TopPair.isoOfSubset`). -/
def unionEmptyIso : TopPair.ofSubset (A ∪ (∅ : Set X)) ≅ TopPair.ofSubset A :=
  TopPair.isoOfSubset (Homeomorph.refl X) (fun x => by simp)

/-- The chain map of the empty subspace is zero (no singular simplices in `∅`). -/
lemma emptyChain_zero :
    ((chainPairFunctor ℚ).obj (TopPair.ofSubset (∅ : Set X))).hom = 0 := by
  have hE : ∀ n : ℕ, IsEmpty ((TopCat.toSSet.obj (TopPair.ofSubset (∅ : Set X)).snd).obj
      (Opposite.op (SimplexCategory.mk n))) := fun n => by
    constructor
    intro σ
    exact (((TopPair.ofSubset (∅ : Set X)).snd.toSSetObjEquiv
      (Opposite.op (SimplexCategory.mk n))) σ Convexity.StdSimplex.barycenter).2
  apply HomologicalComplex.hom_ext
  intro n
  change (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (∅ : Set X)).map)
    (ModuleCat.of ℚ ℚ)).f n = 0
  apply SSet.chainComplex_hom_ext
  intro σ
  exact (hE n).false σ |>.elim

/-- The projection `C(X) → C(X, ∅)` is an isomorphism. -/
instance projEmpty_isIso : IsIso (relativeChainProjection ℚ (TopPair.ofSubset (∅ : Set X))) :=
  cokernel.π_of_zero (emptyChain_zero X)

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back along `f` then `g` with `g ≫ f = 𝟙` is the identity on cohomology. -/
lemma yo_cancel {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (M : ModuleCat.{0} ℚ) (f : K ⟶ L)
    (g : L ⟶ K) (hgf : g ≫ f = 𝟙 L) (n : ℕ)
    (x : (L.linearYonedaObj ℚ M).homology n) :
    HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor ℚ M).map g.op) n
      (HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor ℚ M).map f.op) n x)
      = x := by
  have h1 : (TauCeti.ChainComplex.linearYonedaFunctor ℚ M).map f.op ≫
      (TauCeti.ChainComplex.linearYonedaFunctor ℚ M).map g.op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, hgf, op_id, CategoryTheory.Functor.map_id]
  have h2 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) h1
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at h2
  exact ConcreteCategory.congr_hom h2 x

set_option backward.isDefEq.respectTransparency false in
/-- **`relCup2` with `B = ∅` is `relCupSing`**, no sign: on `(X, A ∪ ∅)`, identified with
`(X, A)` by `unionEmptyIso` (the identity of `X`), `relCup2 a b` is `relCupSing a (forgetRel b)`,
where `forgetRel : H^q(X, ∅) → H^q(X)` is the identification of `forgetRel_empty_bijective`. -/
theorem relCup2_empty (hA : IsOpen A) {p q : ℕ}
    (a : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset (∅ : Set X)) q) (n : ℕ) (h : p + q = n) :
    relCup2 X A ∅ hA isOpen_empty a b n h =
      relativeCohomologyMap ℚ n (unionEmptyIso X A).hom
        (relCupSing (TopPair.ofSubset A) a (forgetRel (TopPair.ofSubset (∅ : Set X)) q b) n h) := by
  let P0 := TopPair.ofSubset (∅ : Set X)
  let g : (relativeChainFunctor ℚ).obj P0 ⟶ SingularChainComplex ℚ X :=
    inv (relativeChainProjection ℚ P0)
  let e : triadChains X A ∅ ⟶ (relativeChainFunctor ℚ).obj (TopPair.ofSubset A) :=
    triadToUnionRelativeChainMap ℚ X A ∅ ≫ (relativeChainFunctor ℚ).map (unionEmptyIso X A).hom
  have hπe : triadRelativeChainProjection ℚ X A ∅ ≫ e =
      relativeChainProjection ℚ (TopPair.ofSubset A) := by
    simp only [e]
    rw [triadRelativeChainProjection_triadToUnionRelativeChainMap_assoc]
    erw [TopPair.Homotopy.relativeChainProjection_naturality]
    have : (TopPair.Hom.fst (unionEmptyIso X A).hom) = 𝟙 X := rfl
    erw [this, CategoryTheory.Functor.map_id, Category.id_comp]
  have hD : e ≫ relDiagonal (TopPair.ofSubset A) =
      triadDiagonal X A ∅ ≫ (𝟙 _ ⊗ₘ g) := by
    have : Epi (triadRelativeChainProjection ℚ X A ∅) := by
      change Epi (cokernel.π _); infer_instance
    rw [← cancel_epi (triadRelativeChainProjection ℚ X A ∅), ← Category.assoc, hπe,
      relProj_relDiagonal]
    erw [← Category.assoc, cokernel.π_desc]
    rw [Category.assoc, tensorHom_comp_tensorHom]
    simp only [g]
    erw [IsIso.hom_inv_id]
    rfl
  -- reduce through the excision isomorphism
  apply (triadExcisionCoh X A ∅ hA isOpen_empty n).toLinearEquiv.injective
  apply (triadCohIso X A ∅ n).toLinearEquiv.injective
  change (triadCohIso X A ∅ n).hom ((triadExcisionCoh X A ∅ hA isOpen_empty n).hom _) =
    (triadCohIso X A ∅ n).hom ((triadExcisionCoh X A ∅ hA isOpen_empty n).hom _)
  rw [relCup2, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  have hr : ∀ z, (triadExcisionCoh X A ∅ hA isOpen_empty n).hom
      (relativeCohomologyMap ℚ n (unionEmptyIso X A).hom z) =
      HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap e) n z := by
    intro z
    simp only [e, HomologicalComplex.linearDualMap_comp, HomologicalComplex.homologyMap_comp]
    rfl
  rw [hr]
  change _ = HomologicalComplex.homologyMap (dualIsoYoneda _).hom n _
  rw [homologyMap_dualIsoYoneda_apply]
  have e5 : HomologicalComplex.homologyMap
      (dualIsoYoneda ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A))).hom n
      (relCupSing (TopPair.ofSubset A) a (forgetRel P0 q b) n h) =
      TauCeti.ChainComplex.cup ℚ (relDiagonal (TopPair.ofSubset A)) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
        p q n h ((relCohIso (TopPair.ofSubset A) p).hom a) ((cohIso X q).hom (forgetRel P0 q b)) :=
    Iso.inv_hom_id_apply (relCohIso (TopPair.ofSubset A) n) _
  erw [e5]
  have hn := TauCeti.ChainComplex.cup_naturality (k := ℚ) (D := relDiagonal (TopPair.ofSubset A))
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (triadDiagonal X A ∅) e (𝟙 _) g hD p q n h
    ((relCohIso (TopPair.ofSubset A) p).hom a)
    ((cohIso X q).hom (forgetRel P0 q b))
  erw [← hn]
  have e6 := cohIso_forgetRel P0 q b
  erw [e6]
  rw [CategoryTheory.op_id]
  erw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id, ConcreteCategory.id_apply]
  congr 1
  exact (yo_cancel _ (relativeChainProjection ℚ P0) g (IsIso.inv_hom_id _) q _).symm

/-- Forgetting the empty subspace, `H^q(X, ∅) → H^q(X)`, is bijective. -/
theorem forgetRel_empty_bijective (q : ℕ) :
    Function.Bijective (forgetRel (TopPair.ofSubset (∅ : Set X)) q) := by
  exact homologyMap_linearDualMap_bijective _ q

/-- The triad cup of two relative cocycles, a cocycle on the triad complex. -/
def triadCupCycles {p q : ℕ}
    (c : (RelativeCochainComplex ℚ (TopPair.ofSubset A)).cycles p)
    (d : (RelativeCochainComplex ℚ (TopPair.ofSubset B)).cycles q) (n : ℕ) (h : p + q = n) :
    (triadChains X A B).linearDualCochainComplex.cycles n :=
  HomologicalComplex.cyclesMap (dualIsoYoneda (triadChains X A B)).inv n
    (TauCeti.ChainComplex.cupCycles ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
      (HomologicalComplex.cyclesMap
        (dualIsoYoneda ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A))).hom p c)
      (HomologicalComplex.cyclesMap
        (dualIsoYoneda ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B))).hom q d))

set_option backward.isDefEq.respectTransparency false in
/-- **`relCup2` on cocycles** is, through triad excision, the class of the triad cup cocycle. -/
theorem triadExcisionCoh_relCup2_homologyπ (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}
    (c : (RelativeCochainComplex ℚ (TopPair.ofSubset A)).cycles p)
    (d : (RelativeCochainComplex ℚ (TopPair.ofSubset B)).cycles q) (n : ℕ) (h : p + q = n) :
    (triadExcisionCoh X A B hA hB n).hom
        (relCup2 X A B hA hB ((RelativeCochainComplex ℚ (TopPair.ofSubset A)).homologyπ p c)
          ((RelativeCochainComplex ℚ (TopPair.ofSubset B)).homologyπ q d) n h) =
      (triadChains X A B).linearDualCochainComplex.homologyπ n (triadCupCycles X A B c d n h) := by
  rw [relCup2, Iso.inv_hom_id_apply]
  unfold triadCohIso relCohIso triadCupCycles
  simp only [HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_inv]
  have hπ : ∀ {K L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (m : ℕ) (x : K.cycles m),
      HomologicalComplex.homologyMap φ m (K.homologyπ m x) =
        L.homologyπ m (HomologicalComplex.cyclesMap φ m x) := by
    intro K L φ m x
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
  erw [hπ, hπ]
  erw [TauCeti.ChainComplex.cup_homologyπ, hπ]

/-- On chains: the triad cup cochain, pulled back to `C(X)`, is the Alexander–Whitney cup of the
two cochains pulled back to `C(X)`. -/
lemma triadProj_cupCochain {p q : ℕ}
    (φ : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).X p ⟶ ModuleCat.of ℚ ℚ)
    (ψ : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).X q ⟶ ModuleCat.of ℚ ℚ)
    (n : ℕ) (h : p + q = n) :
    TauCeti.ChainComplex.cupCochain ℚ (awX X) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h
        ((relativeChainProjection ℚ (TopPair.ofSubset A)).f p ≫ φ)
        ((relativeChainProjection ℚ (TopPair.ofSubset B)).f q ≫ ψ) =
      (triadRelativeChainProjection ℚ X A B).f n ≫
        TauCeti.ChainComplex.cupCochain ℚ (triadDiagonal X A B) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
          p q n h φ ψ := by
  have hD : triadRelativeChainProjection ℚ X A B ≫ triadDiagonal X A B =
      awX X ≫ (relativeChainProjection ℚ (TopPair.ofSubset A) ⊗ₘ
        relativeChainProjection ℚ (TopPair.ofSubset B)) := cokernel.π_desc _ _ _
  exact TauCeti.ChainComplex.cupCochain_naturality (k := ℚ) (D := triadDiagonal X A B)
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (awX X) (triadRelativeChainProjection ℚ X A B)
    (relativeChainProjection ℚ (TopPair.ofSubset A))
    (relativeChainProjection ℚ (TopPair.ofSubset B)) hD p q n h φ ψ



section Test
variable {Y : TopCat.{0}} {T : C(ℝ × ℝ, Y)} (hT₁ : ∀ t, T (1, t) = T (0, t))
  (hT₂ : ∀ s, T (s, 1) = T (s, 0)) (g₁ g₂ : C(Y, ℂ)) (hg₁ : ∀ y, g₁ y ≠ 0) (hg₂ : ∀ y, g₂ y ≠ 0)
  (h₁ : ∀ p, g₁ (T p) = Complex.exp (ChernWinding.twoPiI * (p.1 : ℂ)))
  (h₂ : ∀ p, g₂ (T p) = Complex.exp (ChernWinding.twoPiI * (p.2 : ℂ)))

include h₁ h₂ in
/-- Non-vacuity and factor order of `relCup2` with `A = B = ∅`: `⟨a₁ ⌣ a₂, T⟩ = 1`. -/
theorem torusEval_relCup2_winding (a₁ a₂ : RelativeCohomology ℚ (TopPair.ofSubset (∅ : Set Y)) 1)
    (ha₁ : forgetRel _ 1 a₁ = windingClass g₁ hg₁) (ha₂ : forgetRel _ 1 a₂ = windingClass g₂ hg₂) :
    torusEval hT₁ hT₂ (forgetRel (TopPair.ofSubset ((∅ : Set Y) ∪ ∅)) 2
      (relCup2 Y ∅ ∅ isOpen_empty isOpen_empty a₁ a₂ 2 rfl)) = 1 := by
  rw [forgetRel_relCup2, ha₁, ha₂]
  exact torusEval_cupSing_winding hT₁ hT₂ g₁ g₂ hg₁ hg₂ h₁ h₂
end Test```
