# Red team: `triad-relative-cup-naturality` (statement pass)

Date: 2026-11-26. Worktree branch `track/triad-relative-cup-naturality` at base `c486870`, uncommitted `HodgeLadder/Cup/TriadCupNaturality.lean` and the section "triad-relative-cup-naturality: statement" of `docs/sketches/local-class-product.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713` (the package source in `.lake/packages` is at the same commit), Lean and Mathlib `v4.35.0-rc4`. During this pass the parallel rung `relative-cross-triad-naturality` merged to `main` as `d89ec00` (#130); its `HodgeLadder/Relative/CrossTriadNaturality.lean` was read at that commit.

Read: the ledger entries `triad-relative-cup-naturality`, `triad-relative-cup`, `relative-cross-triad-naturality`, `local-class-product`, `cycle-class-multiplicative`; the statement file; the sketch section; `docs/sketches/triad-relative-cup.redteam.md`, `supported-pair-forget.redteam.md`; `docs/sketches/cycle-class-multiplicative.md` (steps 3 to 6, glue statements); `docs/conventions.md` rows "Pair spellings of (X, X ∖ Z)", "Triad relative cup product" and, on `main`, "Map of triads on triad chains"; `docs/references.md`; the checked `HodgeLadder/Cup/{TriadCup,RelCupNaturality,SupportedPairForget}.lean`, `HodgeLadder/Normalization/Germ.lean` (`transport_supportedClass_eq_chartNormalProjectionCoclass`); at the pin `HodgeConjecture/Mathlib/Topology/Category/TopPair.lean` (`ofSubsetHom`, `isoOfSubset`), `Definitions/AlgebraicTopology/Singular/Cohomology.lean` (`relativeCohomologyMap`), `Lemmas/AlgebraicTopology/Singular/Cohomology.lean` (`relativeCohomologyMap_id`, `_comp`), `Definitions/AlgebraicTopology/LocalHomology/FundamentalClass.lean` (`neighborhoodSupportComplementPair`), `Definitions/AlgebraicTopology/LocalHomology/NormalProjectionCoclass.lean` (`neighborhoodSupportInclusionPairMap`, `chartNormalProjectionPair`, `chartNormalProjectionCoclass`); Tau Ceti `cup_naturality` (`port/LefschetzPort/TauCeti/Algebra/Homology/Monoidal/Cup.lean:210`).

Scratch: six files in `scratch_rt/` inside the worktree, compiled with `lake env lean` against the worktree build (about 6 to 12 s each) and deleted afterwards. Nothing under `.lake/packages` was touched and no upstream or Mathlib module was built.

| File | Content | Result |
|---|---|---|
| RT1 | trivial tactics on `relCup2_naturality`; a proof by the planned route with the local `triadChainsMap` | trivial tactics fail; the proof compiles, standard axioms |
| RT2 | a copy of `main`'s `CrossTriadNaturality.lean` (lines 4 to 200, identical to `d89ec00`) next to this file; bridge tests; `triadChainMap_triadDiagonal` and `relCup2_naturality` restated and proved with `Relative.triadChainMap` | all compile, standard axioms; the two maps agree by `rfl` at default transparency only |
| RT3 | `cycle-class-multiplicative` step 6 in the consumer's spellings, with `unionComplIso` (Closeds form, change D of `supported-pair-forget`) and its V form; a spelling-seam probe | step 6 closes by two `rw` lines; the probe shows a silent seam (finding 7) |
| RT4 | `#print axioms` on every proved declaration of the file; the case f = 𝟙 | standard axioms; f = 𝟙 reduces to `rfl` |
| RT5 | `local-class-product` step 7: `relCup2_naturality` along the normal projection of a chart `M → E × ℂ^{a+b}` with A = `setA a b`, B = `setB a b` | elaborates term for term |
| RT6 | the compatibility lemma with V any subset | compiles; consumers with V : Opens rewrite with it |

**Verdict: pass with changes.** `relCup2_naturality` is full-strength naturality of Hatcher's relative cup for maps of triads with open subspaces, A factor first on both sides, no sign, and it is true as stated: the planned route proves it in about 30 lines with the standard axioms (RT1, and RT2 with the merged `Relative.triadChainMap`). `relCup2_naturality_of_fst` covers every map of `TopPair.ofSubset` pairs (by `eq_ofSubsetHom`), and `relCup2_restrict` is the form `cycle-class-multiplicative` step 6 needs, in spellings that `rw` accepts (RT3). The changes are structural: after the rebase onto `d89ec00`, use the merged chain map and drop the four duplicates (change 1, exact Lean below); move the one lemma that needs `SupportedPairForget` to the consumer (change 2); record two upstream candidates (change 4) and the consumer glue (change 3).

## 1. Is this the statement the literature makes?

Source: [`Hatcher2002` §3.2]. The relative cup product H^k(X, A; R) × H^l(X, B; R) → H^{k+l}(X, A ∪ B; R) is defined for A, B open in X (through C^n(X, A + B)), and cup products are natural: for f : X → Y, f*(α ⌣ β) = f*α ⌣ f*β, with the remark that the same holds for relative cup products (Proposition 3.10; the number is recalled from the book and was not re-read, citation status as in `docs/references.md`). For the relative-relative product the natural maps are maps of triads f : (X'; A', B') → (X; A, B), f(A') ⊆ A, f(B') ⊆ B, and f* on the target is the pullback along (X', A' ∪ B') → (X, A ∪ B).

| Literature | Lean | Check |
|---|---|---|
| R a commutative ring | ℚ | narrower, as in `relCup2`; rationality enters only through triad excision on cohomology |
| map of triads f : (X'; A', B') → (X; A, B) | `f : X' ⟶ X` in `TopCat.{0}`, `hfA : ∀ x ∈ A', f x ∈ A`, `hfB : ∀ x ∈ B', f x ∈ B` | same data; f need not be open, injective or surjective, and A' may be smaller than f⁻¹(A) |
| A, B open in X; A', B' open in X' | `hA hB hA' hB'` | needed to form the product on both sides; Hatcher assumes the same (or CW subcomplexes, excluded here) |
| f* : H^p(X, A) → H^p(X', A') | `relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hfA)`, precomposition with the chain map of f (upstream docstring) | same map, contravariant, no sign |
| f* : H^q(X, B) → H^q(X', B') | the same with `hfB` | same |
| f* : H^n(X, A ∪ B) → H^n(X', A' ∪ B') | `relativeCohomologyMap ℚ n (TopPair.ofSubsetHom f (mem_union_of_mem f hfA hfB))` | same; the membership proof is irrelevant (RT2: `rfl` against `Relative.triadMap_mem_union`) |
| ⌣ on both sides | `relCup2 X A B hA hB` and `relCup2 X' A' B' hA' hB'`, same degrees `p q n`, same `h : p + q = n` | same product (register row "Triad relative cup product") |
| f*(a ⌣ b) = f*a ⌣ f*b | the equation, a in the first slot on both sides | same order, no sign, no scalar |

Strength. Every map of `TopPair.ofSubset` pairs is `TopPair.ofSubsetHom` of its ambient map (`eq_ofSubsetHom`, proved), so `relCup2_naturality_of_fst` states naturality for all maps of pairs that share one ambient map, which is all maps of triads in this framework. Naturality cannot hold for three maps with different ambient maps, so nothing stronger of this shape exists. Because A ≠ B in general, writing the factors in the other order on the right does not type-check; at A = B = ∅ it would, and it would be false (`torusEval_cupSing_winding_swap` gives −1 against +1).

`relCup2_restrict` is the instance f = inclusion of V : Set Y, A = Z.compl, B = W.compl, A' = {w | w.1 ∉ Z}, B' = {w | w.1 ∉ W}. It is a corollary, so it is as strong as the general statement.

## 2. Can the hypotheses be satisfied?

Yes, for every map. f = 𝟙 X with A' = A, B' = B (RT4, the statement reduces to `rfl` after `relativeCohomologyMap_id`); any f with A' = B' = ∅; the inclusion of any subset V with the complements of two closed sets (`relCup2_restrict`, proved from the main statement); and the consumer instance of `local-class-product` step 7, the normal projection w ↦ (e w).2 of a chart e : M → E × ℂ^{a+b} on V ⊆ e.source with A = `setA a b`, B = `setB a b` (RT5: the membership proofs are one line each, from the chart condition, and `relCup2_naturality` elaborates term for term). The classes range over whole cohomology groups, which are nonzero for the torus (`torusEval_relCup2_winding`).

## 3. Is the conclusion trivially true for a reason unrelated to the mathematics?

No. In RT1, `first | rfl | (simp; done) | (simp [relCup2]; done) | aesop | decide | grind` fails on `relCup2_naturality` (aesop: exhaustive search). The proof that works uses the content: injectivity of `triadExcisionCoh X' A' B'`, the triad excision square `triadChainsMap_triadToUnion`, Alexander–Whitney naturality (`TopCat.alexanderWhitneyDiagonal_naturality`) inside `triadChainsMap_triadDiagonal`, and Tau Ceti's `cup_naturality`. No definition unfolds to `True`, no index type is empty, there is no `ℕ∞`. Every hypothesis is used: `hA hB` and `hA' hB'` through triad excision on X and X'; `hfA hfB` to form the three maps of pairs. The proved helpers carry no hidden content: `eq_ofSubsetHom` holds because the subspace inclusion is injective, which is the mathematical reason, and `neighborhoodSupportInclusionPairMap_comp_ofSubsetIsoNeighborhoodTop_inv` is an equality of maps of pairs that are all the identity on points (`ext; rfl`).

The proof of `relCup2_naturality` by the planned route, compiled in RT1 against the file as written:

```lean
set_option backward.isDefEq.respectTransparency false in
theorem relCup2_naturality ... := by
  apply (triadExcisionCoh X' A' B' hA' hB' n).toLinearEquiv.injective
  apply (triadCohIso X' A' B' n).toLinearEquiv.injective
  change (triadCohIso X' A' B' n).hom ((triadExcisionCoh X' A' B' hA' hB' n).hom _) =
    (triadCohIso X' A' B' n).hom ((triadExcisionCoh X' A' B' hA' hB' n).hom _)
  have hL : ∀ z, (triadExcisionCoh X' A' B' hA' hB' n).hom
      (relativeCohomologyMap ℚ n (TopPair.ofSubsetHom f (mem_union_of_mem f hfA hfB)) z) =
      HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap (triadChainsMap f hfA hfB)) n
        ((triadExcisionCoh X A B hA hB n).hom z) := by
    intro z
    have e := congrArg (fun φ => HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap φ) n) (triadChainsMap_triadToUnion f hfA hfB)
    simp only [HomologicalComplex.linearDualMap_comp, HomologicalComplex.homologyMap_comp] at e
    exact (ConcreteCategory.congr_hom e z).symm
  rw [hL, relCup2, Iso.inv_hom_id_apply, relCup2, Iso.inv_hom_id_apply]
  change HomologicalComplex.homologyMap (dualIsoYoneda _).hom n _ = _
  rw [homologyMap_dualIsoYoneda_apply]
  have e4 : ∀ c, HomologicalComplex.homologyMap (dualIsoYoneda (triadChains X A B)).hom n
      ((triadCohIso X A B n).inv c) = c := fun c => Iso.inv_hom_id_apply (triadCohIso X A B n) c
  rw [e4, Iso.inv_hom_id_apply, relCohIso_map, relCohIso_map]
  have hn := TauCeti.ChainComplex.cup_naturality (k := ℚ) (D := triadDiagonal X A B)
    (μ := (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) (triadDiagonal X' A' B') (triadChainsMap f hfA hfB)
    ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hfA))
    ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hfB))
    (triadChainsMap_triadDiagonal f hfA hfB) p q n h
    ((relCohIso (TopPair.ofSubset A) p).hom a) ((relCohIso (TopPair.ofSubset B) q).hom b)
  exact hn.symm
```

Attempts that failed on the way: `erw [Iso.inv_hom_id_apply]` does not fire on `homologyMap (dualIsoYoneda _).hom n ((triadCohIso X A B n).inv c)` (the two are equal by definition of `triadCohIso`, not syntactically), so `e4` states the cancellation; `exact (cup_naturality … _ _).symm` with the classes left as holes fails on a ring-instance path (`Rat.commRing.toRing` against `Rat.instDivisionRing.toRing`), and naming the classes in `have hn` fixes it. After change 1 the same proof works with `Relative.triadChainMap`, `Relative.triadChainMap_triadToUnionRelativeChainMap` and `triadChainMap_triadDiagonal` in place of the local names (RT2, standard axioms).

## 4. Interface rung

Not applicable: no structure, no axioms.

## 5. Checker

The rung is not checked. `python3 tools/check.py --no-build` in the worktree: one failure, `REJECTED (sorry: HodgeLadder/Cup/TriadCupNaturality.lean:189)`, the statement-phase `sorry` of `relCup2_naturality`; everything else accepted. `#print axioms` (RT4): `mem_of_pairHom`, `eq_ofSubsetHom`, `eq_ofSubsetHom_of_fst`, `triadChainsMap`, `triadProj_triadChainsMap`, `triadChainsMap_triadDiagonal`, `triadChainsMap_triadToUnion`, `restrictToNeighborhood`, `isOpen_neighborhoodComplement`, `neighborhoodSupportInclusionPairMap_comp_ofSubsetIsoNeighborhoodTop_inv` depend on `[propext, Classical.choice, Quot.sound]`; `mem_union_of_mem` on none; `relCup2_naturality_of_fst` and `relCup2_restrict` add `sorryAx`, through `relCup2_naturality` only. The ledger entry has `declarations: []` and `module: null`; the declarations above are the ones its title means.

## 6. Conventions

| Convention | Where it enters | Register | Truth depends on it? |
|---|---|---|---|
| factor order of `relCup2`: A factor first, front p-face times back q-face, μ = `(λ_ _).hom` | both sides | row "Triad relative cup product" | the order is preserved on both sides, so the identity holds for either choice; a mismatch of orders between the sides would make it false (at A = B = ∅ by −1) |
| `relativeCohomologyMap`: pullback by precomposition with the chain map of the map of pairs, contravariant, no sign | the three pullbacks | upstream docstring; new row "Triad relative cup naturality" | an equality: a sign or scalar in the pullback would change it. There is none at the pin (`relativeCochainComplexMap` is `linearDualMap` of the chain map) |
| triad excision `triadExcisionCoh`: dual of `triadToUnionRelativeChainMap`, induced by the identity of C(X) | inside `relCup2` on X and X' | row "Triad relative cup product" | the same comparison on both sides; the square `triadChainsMap_triadToUnion` has no sign |
| triad chain map of f | the proof | `main` row "Map of triads on triad chains" | no sign, no scalar; its note on the two local names needs the update of change 1 |
| `dualIsoYoneda`: no degree sign | the proof | row "Triad relative cup product" | cancels between the sides |
| pair spellings: `Z.compl` on Y, `neighborhoodSupportComplementPair V Z` and `{w : V \| w.1 ∉ Z}` on V | `restrictToNeighborhood`, `relCup2_restrict` | row "Pair spellings of (X, X ∖ Z)", updated this pass (finding 7) | no result's truth; which rewrites typecheck |

No cited result enters with a convention of its own: the borrowed inputs are upstream's `triadToUnionRelativeChainMap_quasiIso_of_isOpen` (library `Other`, already registered), `TopPair.Homotopy.relativeChainProjection_naturality`, Tau Ceti's `alexanderWhitneyDiagonal_naturality` and `cup_naturality`; none carries a sign. Register edits this pass: new row "Triad relative cup naturality"; row "Pair spellings of (X, X ∖ Z)" extended with the silent-elaboration seam.

## 7. Equality first

The rung is an identity between classes in H^n(X', A' ∪ B'; ℚ), proved exactly in RT1 and RT2, not up to a scalar. The docstrings say "no sign"; the sign convention it inherits is that of `relCup2` (A first). It is a step toward the identities `local-class-product` (chart form, step 7) and `cycle-class-multiplicative` (step 6); both rungs exist and are open.

## 7b. Non-vacuity

The equation is between nonzero classes as soon as the classes are: at f = 𝟙, A = B = ∅ both sides are the class of `torusEval_relCup2_winding` (value 1), which exists. The case f = 𝟙 is the trivial case of the statement (RT4), so it does not test the map.

Smallest test along a map that is not the identity, with exact upstream and local names: Y = `HodgeLadder.Tests.puncturedSquare`, f its coordinate swap, A = B = A' = B' = ∅, a₁, a₂ lifts of `windingClass coordOne` and `windingClass coordTwo` (`forgetRel_empty_bijective`); then `relCup2_naturality` with `forgetRel_relativeCohomologyMap` (checked, `SupportedPairForget`) and `torusEval_relCup2_winding` gives `torusEval standardTorus_one_left standardTorus_one_right (forgetRel _ 2 (relativeCohomologyMap ℚ 2 (TopPair.ofSubsetHom swap _) (relCup2 _ ∅ ∅ _ _ a₁ a₂ 2 rfl))) = −1`, which fails if the pulled-back product were zero or if the factors were swapped. It does not exist: it needs the pullback of a winding class, `windingClass (g.comp f) = cohomologyMap f (windingClass g)` in some form, which is not in the tree (`grep` over `HodgeLadder` and `port`). The decisive test with nonempty subspaces is downstream: `local-class-product` at a = b = 1, where step 7 moves the subspaces along the normal projection. Optional rung (change 5); not blocking, since the statement has no sign or order to choose that the types leave open.

## 8. Pin drift

None. The worktree, the shared package source and `lake-manifest.json` are at `2ead713`, the pin at which `triad-relative-cup` was checked and the register rows were read. The merged `relative-cross-triad-naturality` (`d89ec00`) is at the same pin, and the copy tested in RT2 is identical to it in lines 4 to 200 (`diff`, whitespace only). The upstream definitions this rung depends on (`TopPair.ofSubsetHom`, `relativeCohomologyMap`, `relativeCochainComplexMap`, `neighborhoodSupportComplementPair`, `neighborhoodSupportInclusionPairMap`, `triadRelativeChainComplex`, `triadToUnionRelativeChainMap`) were read at the pin.

## Findings

1. **Correct and full strength.** The statement is naturality of the relative-relative cup for maps of triads with open subspaces, A first, no sign; it is true (RT1, RT2) and covers every map of `TopPair.ofSubset` pairs through `relCup2_naturality_of_fst`.
2. **The planned route is sound** and takes about 30 lines (section 3). The cohomology-level step uses the triad excision square on chains and `cup_naturality` along the triad chain map; no homotopy argument is needed.
3. **`triadChainsMap` and `Relative.triadChainMap` are the same term at default transparency only.** `example : triadChainsMap f hfA hfB = Relative.triadChainMap f hfA hfB := rfl` compiles; `with_reducible_and_instances rfl` fails, and `rw [Relative.triadChainMap_triadToUnionRelativeChainMap]` fails on a goal written with `triadChainsMap` (RT2). An `abbrev` of one in terms of the other would leave two spellings on `main` with this seam; delete the local map (change 1). `exact` of the old lemmas at the new spelling works, and so does `rw` of `main`'s lemma on a goal carrying this file's union proof (proof irrelevance).
4. **Duplicates after the rebase.** `ambientChainMap f` is `singChainFunctor.map f` (`HodgeLadder.Relative.CrossChain`); `mem_union_of_mem` is `Relative.triadMap_mem_union` (same binders and conclusion); `triadProj_triadChainsMap` is `Relative.triadRelativeChainProjection_triadChainMap`; `triadChainsMap_triadToUnion` is `Relative.triadChainMap_triadToUnionRelativeChainMap`. Only `triadChainsMap_triadDiagonal` is new content.
5. **Prover question (i), `V : Opens Y` or any subset: keep `V : Set Y`.** `cycle-class-germ` delivers restrictions to `W : Opens` spelled `(W : Set (ComplexPoint X))`, and upstream's `neighborhoodSupportInclusionPairMap`, `chartNormalProjectionCoclass` take `Set`. RT3 applies `relCup2_restrict (V : Set Y)` for `V : Opens Y` with no cast lemma. The compatibility lemma can take `V : Set Y` too (RT6, same proof).
6. **Prover question (ii), union on V: leave it to the consumer.** `relCup2` lands in `TopPair.ofSubset (A ∪ B)` by definition, so the faithful naturality statement keeps the union spelling; stating it on `neighborhoodSupportComplementPair V (Z ∩ W)` would bake in a pair isomorphism and a choice between `Z ⊓ W` (Closeds) and `Z ∩ W` (Set). The consumer needs two things beside `unionComplIso`: its V form and one commuting square, both the identity on points; RT3 proves step 6 with them in two `rw` lines (change 3, exact Lean).
7. **Silent spelling seam.** In RT3, a statement `relCup2 (TopCat.of Y) (Z.compl : Set Y) (W.compl : Set Y) … a b` with `a` typed on `TopPair.ofSubset ((Z : Set Y)ᶜ)` elaborates (the types agree at default transparency), and `rw [relCup2_restrict]` then fails with "did not find an occurrence". The elaborator does not catch the mismatch; only the rewrite does. This file's spellings are consistent (the classes are on `Z.compl`, the codomain of `supportedEquivPair`); consumers must type their classes on `Z.compl` too. Recorded in row "Pair spellings of (X, X ∖ Z)".
8. **Prover question (iii), importing `SupportedPairForget`: works, but move the lemma.** It costs about 1 s of import load, and it makes this triad module, and `local-class-product` which imports it for step 7, depend on the sheaf-side supported stack (`SupportedFinal`, `SupportedAgreement`, upstream's supported injective and singular models) and on rung `supported-pair-forget`, which the ledger's `depends_on` does not list. Only `neighborhoodSupportInclusionPairMap_comp_ofSubsetIsoNeighborhoodTop_inv` needs it, and its one consumer, `cycle-class-multiplicative`, already depends on `supported-pair-forget` (change 2).
9. **Consumer fit.** Step 7 of `local-class-product` (RT5) and step 6 of `cycle-class-multiplicative` (RT3) both close in the stated spellings; the `rw` route of the sketch is the one to use for step 6.
10. **Upstream candidates.** `mem_of_pairHom` and `eq_ofSubsetHom` are general facts about upstream's `TopPair.ofSubsetHom` (file `HodgeConjecture/Mathlib/Topology/Category/TopPair.lean`); list them in `docs/gaps.md` "To upstream".

## Recommended changes

1. **Rebase onto `d89ec00` and use the merged chain map.** Add `public import HodgeLadder.Relative.CrossTriadNaturality`; delete `ambientChainMap`, `triadChainsMap`, `triadProj_triadChainsMap`, `triadChainsMap_triadToUnion`, `mem_union_of_mem`; replace the diagonal square by the following (RT2, standard axioms) and use `Relative.triadMap_mem_union` in `relCup2_naturality`, `relCup2_restrict`; the proof of `relCup2_naturality` is section 3 with the names substituted (RT2 compiles it).

```lean
set_option backward.isDefEq.respectTransparency false in
/-- **The triad diagonal is natural for maps of triads**: `Relative.triadChainMap` followed by the
diagonal of `(X; A, B)` is the diagonal of `(X'; A', B')` followed by the tensor product of the
relative chain maps of `f`. No sign. -/
theorem triadChainMap_triadDiagonal {X X' : TopCat.{0}} (f : X' ⟶ X) {A B : Set X}
    {A' B' : Set X'} (hfA : ∀ x ∈ A', f x ∈ A) (hfB : ∀ x ∈ B', f x ∈ B) :
    HodgeLadder.Relative.triadChainMap f hfA hfB ≫ triadDiagonal X A B =
      triadDiagonal X' A' B' ≫ ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hfA) ⊗ₘ
        (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hfB)) := by
  have : Epi (triadRelativeChainProjection ℚ X' A' B') := by
    change Epi (cokernel.π _); infer_instance
  rw [← cancel_epi (triadRelativeChainProjection ℚ X' A' B'),
    HodgeLadder.Relative.triadRelativeChainProjection_triadChainMap_assoc]
  erw [cokernel.π_desc, ← Category.assoc (cokernel.π _), cokernel.π_desc]
  have hn := TopCat.alexanderWhitneyDiagonal_naturality f (λ_ (𝟙_ (ModuleCat.{0} ℚ))).inv
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc, Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  rw [TopPair.Homotopy.relativeChainProjection_naturality,
    TopPair.Homotopy.relativeChainProjection_naturality]
  rfl
```

   Then, on `main`'s row "Map of triads on triad chains", replace the sentence "Parallel track `triad-relative-cup-naturality` defines the same map as `HodgeLadder.Cup.triadChainsMap` (`cokernel.map`); the two agree by cancelling the triad projection" with "`relCup2_naturality` (rung `triad-relative-cup-naturality`) uses it, with `triadChainMap_triadDiagonal`". (The row is not in this worktree's base, so this pass did not edit it.)

2. **Move the compatibility lemma to the consumer** and drop `public import HodgeLadder.Cup.SupportedPairForget` from this module. State it there over any subset (RT6):

```lean
theorem neighborhoodSupportInclusionPairMap_comp_ofSubsetIsoNeighborhoodTop_inv
    {Y : Type} [TopologicalSpace Y] (V : Set Y) (Z : Closeds Y) :
    neighborhoodSupportInclusionPairMap (W := V) (V := ((⊤ : Opens Y) : Set Y))
        (fun _ _ => trivial) (Z : Set Y) ≫ (ofSubsetIsoNeighborhoodTop Z).inv =
      restrictToNeighborhood V Z := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext <;> rfl
```

   If the prover keeps it here instead, add `supported-pair-forget` to the ledger's `depends_on` for this rung.

3. **Record the step-6 glue for `cycle-class-multiplicative`** (sketch section "Glue statements", or that rung's ledger note), beside `unionComplIso`. RT3 compiles all three (with the local `mem_union_of_mem` in place of `Relative.triadMap_mem_union`, the same map by proof irrelevance) and closes step 6 (modulo the `sorry` of this rung) with `rw [compat, compat, compat]; rw [← relCup2_restrict, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp, unionComplIso_restrict]`:

```lean
noncomputable def unionComplIso {Y : Type} [TopologicalSpace Y] {Z W T : Closeds Y}
    (hT : T = Z ⊓ W) :
    TopPair.ofSubset (X := TopCat.of Y) ((Z.compl : Set Y) ∪ (W.compl : Set Y)) ≅
      TopPair.ofSubset (X := TopCat.of Y) (T.compl : Set Y) :=
  TopPair.isoOfSubset (Homeomorph.refl Y) (fun y => by subst hT; simp [Closeds.compl]; tauto)

noncomputable def unionComplIsoNeighborhood {Y : Type} [TopologicalSpace Y] (V : Set Y)
    {Z W T : Closeds Y} (hT : T = Z ⊓ W) :
    TopPair.ofSubset (X := TopCat.of V)
        ({w : V | w.1 ∉ (Z : Set Y)} ∪ {w : V | w.1 ∉ (W : Set Y)}) ≅
      neighborhoodSupportComplementPair V (T : Set Y) :=
  TopPair.isoOfSubset (Homeomorph.refl V) (fun w => by subst hT; simp; tauto)

theorem unionComplIso_restrict {Y : Type} [TopologicalSpace Y] (V : Set Y)
    {Z W T : Closeds Y} (hT : T = Z ⊓ W) :
    restrictToNeighborhood V T ≫ (unionComplIso hT).inv =
      (unionComplIsoNeighborhood V hT).inv ≫
        TopPair.ofSubsetHom (subsetInclusion V)
          (HodgeLadder.Relative.triadMap_mem_union (subsetInclusion V)
            (mem_compl_of_neighborhood V Z) (mem_compl_of_neighborhood V W)) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext <;> rfl
```

4. **`docs/gaps.md` "To upstream":** `HodgeLadder.Cup.mem_of_pairHom`, `HodgeLadder.Cup.eq_ofSubsetHom` (and `eq_ofSubsetHom_of_fst`), target upstream `HodgeConjecture/Mathlib/Topology/Category/TopPair.lean`.

5. **Optional test rung** `triad-relative-cup-naturality-test`: the swap test of section 7b, after a pullback lemma for `windingClass` exists. Not a condition of this pass.

6. **Sketch text.** In the section "triad-relative-cup-naturality: statement", the `triadChainsMap` row ("or makes `triadChainsMap` an `abbrev` of it") becomes "replaced by `Relative.triadChainMap`; an `abbrev` would leave a rewrite seam (red team, finding 3)", and the import list loses `SupportedPairForget` after change 2.

Nothing in the statements of `relCup2_naturality`, `relCup2_naturality_of_fst` or `relCup2_restrict` changes except the name of the union membership proof, which is proof-irrelevant.
