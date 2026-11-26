# Red team: `relative-cross-triad-naturality` (statement and proof)

Date: 2026-11-26. Worktree `track/relative-cross-triad-naturality` from `c486870` (the current `main`), uncommitted: `HodgeLadder/Relative/CrossTriadNaturality.lean` (244 lines) and the section "relative-cross-triad-naturality: statement" of `docs/sketches/local-class-product.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same as `main` (`git diff c486870 -- lakefile.toml lake-manifest.json lean-toolchain` is empty). Phase: the prover finished statements and proofs together, sorry-free.

Read: the Lean file; the sketch section; `docs/sketches/relative-cross-chain.redteam.md` (change 2 and question (i)); `HodgeLadder/Relative/CrossChain.lean` (`singChainFunctor`, `shB_naturality`, `relCross`, `relCrossUnion`, `tensorHom_mem_union`, `relCrossUnion_naturality`); `HodgeLadder/Local/CrossOrientation.lean` (`complexAppendMap`, `setA`, `setB`, `orient`, `cross_orientation_orient`); `HodgeLadder/Tests/CrossOrientation.lean`; the ledger entries of this rung, `relative-cross-chain`, `cross-orientation`, `cap-cross-evaluation`, `local-class-cross-model`, `triad-relative-cup-naturality`; `docs/conventions.md` rows "Relative homology cross product", "Triad cap product", "Triad relative cup product"; `docs/references.md`. At the pin, upstream: `Other/AlgebraicTopology/Singular/Cap/Triad.lean` (`triadSubspaceChainMap`, `triadRelativeChainComplex`, `triadRelativeChainProjection`, `triadCapLiftHom`, `triadCapHom`, `triadCapCohomologyLinear`, `triadToUnionRelativeChainMap`, `triadToUnionRelativeHomologyMap`, `triadUnionExcisionHomologyEquiv`, `unionRelativeTriadCapCohomologyLinear`, `unionRelativeTriadCapCohomologyLinear_on_comparison`), `Other/.../Cap/Naturality.lean` (`relativeCapHom_naturality`, `relativeCapHomologyMap_naturality`, `cochainCohomologyEquiv_naturality`), `Other/.../Cap/Relative.lean` (`relativeCochainCohomologyEquiv`), `Lemmas/AlgebraicTopology/Singular/RelativeHomotopyInvariance.lean` (`relativeChainProjection_naturality`), `Lemmas/AlgebraicTopology/Singular/Cohomology.lean` (`relativeHomologyMap`, `relativeHomologyMap_id`, `relativeHomologyMap_comp`), `Mathlib/Topology/Category/TopPair.lean` (`ofSubsetHom`). Also the parallel worktree `triad-relative-cup-naturality` (`HodgeLadder/Cup/TriadCupNaturality.lean`, uncommitted), read only.

Scratch (inside the worktree under `scratch_rt/`, deleted afterwards): RT1, a copy of the file with `#print axioms` on all fourteen declarations; RT2, consumer shapes: the homology form of the comparison lemma, a rederivation of `relCrossUnion_naturality`, the proposed triad cap naturality (statement) and its union form (proved from it); RT3, quick proofs of the main statements; RT4, the shape `local-class-cross-model` reads, and a non-vacuity test along a map that is not the identity, both proved.

**Verdict: pass with changes.** The statements are change 2 of the `relative-cross-chain` red team, unchanged up to a `rfl` rewrite of the ambient chain map. They are true, proved with the three standard axioms, and nothing in them is trivially true. No sign enters. The changes rename `union_mem`, add the homology form of the comparison lemma (the form `local-class-cross-model` uses), add a non-vacuity test, open one new rung for naturality of upstream's triad cap (stated exactly below), and reconcile a duplicate chain map with the parallel track `triad-relative-cup-naturality`. None weakens a statement.

## 1. Is this the statement the literature makes?

**Source.** [`Hatcher2002` §3.B; page numbers unverified]: the cross product is natural, (f × g)_*(x × y) = f_* x × g_* y, induced at the chain level by naturality of the shuffle (Eilenberg–Zilber) map. In the relative case a map of pairs f : (P, A) → (P', A'), g : (Q, B) → (Q', B') makes f × g a map of triads (P × Q; A × Q, P × B) → (P' × Q'; A' × Q', P' × B'), and the natural chain map descends to the sum-relative quotients C(P × Q)/(C(A × Q) + C(P × B)). [`Bredon1993` ch. VI; unverified] states the same naturality with the same shuffle normalization.

**Diff against change 2.** I compared the file with the Lean block of change 2 in `docs/sketches/relative-cross-chain.redteam.md`, declaration by declaration.

| Declaration | Change 2 | File | Agrees |
|---|---|---|---|
| `triadChainMap` | `cokernel.desc _ (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) ≫ triadRelativeChainProjection ℚ Y A' B') (by sorry)` | `cokernel.desc _ (singChainFunctor.map f ≫ triadRelativeChainProjection ℚ Y A' B') (triadSubspaceChainMap_map_triadRelativeChainProjection f hA hB)` | yes, up to `rfl` (below); the obligation is now proved |
| `triadRelativeChainProjection_triadChainMap` | right side `SSet.chainComplexMap … ≫ triadRelativeChainProjection …`, `@[reassoc]`, `cokernel.π_desc` | right side `singChainFunctor.map f ≫ …`, same attribute and proof | yes, up to `rfl` |
| `union_mem` | as in the file | identical text | yes (rename proposed, finding 6) |
| `triadChainMap_triadToUnionRelativeChainMap` | statement only | identical statement, proved | yes |
| `relCross_naturality` | membership proofs `fun z hz => …` | `fun _ hz => …` | yes, identical up to a binder name |

Binders, implicitness, the subsets `leftProdSet A' Q'`, `rightProdSet P' B'` on the target, the degree `m + n`, and the direction of every equation are unchanged. The file adds `triadChainMap_id`, `triadChainMap_comp`, `singChainFunctor_map_eq_chainComplexMap` and five helpers.

**The `singChainFunctor` refinement is harmless.** `singChainFunctor` is an `abbrev` in `HodgeLadder.Relative.CrossChain` for `(AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)`. Its `map f` is definitionally `SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)`: `singChainFunctor_map_eq_chainComplexMap` is proved by `rfl` and RT1 elaborates it. Since the two forms are definitionally equal, `triadChainMap` is the same term either way, and the projection lemma's two forms are interchangeable by `rw [singChainFunctor_map_eq_chainComplexMap]`. The functor form is the better one for consumers: upstream's `relativeChainProjection_naturality` is stated with `((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map (TopPair.Hom.fst a)` (read at the pin, `RelativeHomotopyInvariance.lean:197`), and `shB_naturality` uses `singChainFunctor.map`. The simplicial form appears in upstream's `relativeCapHom_naturality`, which a prover of change 3 will meet; the `rfl` lemma covers it.

**Field by field against the literature.**

| Literature | Lean | Agrees |
|---|---|---|
| a map of triads, f(A) ⊆ A', f(B) ⊆ B' | `f : X ⟶ Y`, `hA : ∀ a ∈ A, f a ∈ A'`, `hB : ∀ b ∈ B, f b ∈ B'` | yes; no openness, as the literature needs none at chain level |
| induced map C(X)/(C(A) + C(B)) → C(Y)/(C(A') + C(B')) | `cokernel.desc` of `singChainFunctor.map f ≫ triadRelativeChainProjection ℚ Y A' B'` through upstream's `triadRelativeChainComplex ℚ X A B = cokernel (triadSubspaceChainMap ℚ X A B)` | yes; the obligation (chains of A and of B go to zero) is proved by `biprod.hom_ext'` and the factorization of `f` through `A'`, `B'` |
| compatibility with C(X, A ∪ B) → C(Y, A' ∪ B') | `triadChainMap_triadToUnionRelativeChainMap`, along `TopPair.ofSubsetHom f (union_mem f hA hB)` | yes, no sign |
| (f × g) as a map of triads of products | `f ⊗ₘ g` with `leftProdSet A Q → leftProdSet A' Q'` by `hf`, `rightProdSet P B → rightProdSet P' B'` by `hg` | yes; `fst (f ⊗ₘ g) z = f (fst z)` by `rfl` (red team of `relative-cross-chain`, RT2) |
| f_* x × g_* y = (f × g)_*(x × y) | `relCross_naturality` | yes, no sign, first factor first on both sides |

## 2. Can the hypotheses be satisfied?

Yes, for every map and every triad that admits one. `hA`, `hB` hold for `f = 𝟙 X` (`triadChainMap_id`), for any f with `A = B = ∅`, and in the consumer instance `complexAppendMap a b : TopCat.of (Fin a → ℂ) ⊗ TopCat.of (Fin b → ℂ) ⟶ TopCat.of (Fin (a + b) → ℂ)` with `leftProdSet {0}ᶜ _ → setA a b`, `rightProdSet _ {0}ᶜ → setB a b` (RT4, proved in three lines each: `Fin.append_left`, `Fin.append_right`). In `relCross_naturality` the classes `x`, `y` range over whole homology groups; `hf`, `hg` are the hypotheses of `TopPair.ofSubsetHom` and are satisfied by any map of pairs.

## 3. Is anything trivially true?

No. The prover's attempts and mine (RT3) all fail.

| Target | Attempt | Result |
|---|---|---|
| `relCross_naturality` | `first \| rfl \| (simp [relCross, triadChainMap]; done) \| aesop` | `rfl` fails, `simp` leaves goals, `aesop` fails after exhaustive search |
| `triadChainMap_triadToUnionRelativeChainMap` | `first \| rfl \| (simp; done) \| aesop` | all fail |
| `triadChainMap f hA hB = 0` | `first \| rfl \| simp \| aesop` | all fail (it is false: test below) |

No definition unfolds to `True`, there is no `ℕ∞` coercion, no empty index type. `hf` and `hg` are used to build the maps of pairs on the left side and the triad map on the right; dropping either makes the statement ill-typed.

**Non-vacuity beyond `triadChainMap_id`.** `triadChainMap_id` shows the chain map is the identity at `f = 𝟙`, so it is nonzero whenever the triad complex is. RT4 proves the stronger test along a map that is not the identity, with the three standard axioms:

```lean
theorem orient_eq_triadToUnion_triadChainMap (a b : ℕ) :
    orient a b =
      triadToUnionRelativeHomologyMap ℚ (TopCat.of (Fin (a + b) → ℂ)) (setA a b) (setB a b)
        (2 * a + 2 * b)
        ((HomologicalComplex.homologyMap
          (triadChainMap (complexAppendMap a b) (complexAppendMap_mem_setA a b)
            (complexAppendMap_mem_setB a b)) (2 * a + 2 * b)).hom
          (relCross (P := TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
            ({0}ᶜ : Set (Fin a → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)) (2 * a) (2 * b)
            (standardComplexLocalClass ℚ a) (standardComplexLocalClass ℚ b))) := by
  rw [triadToUnionRelativeHomologyMap_triadChainMap, ← cross_orientation_orient]
  rfl

theorem triadChainMap_relCross_orientation_ne_zero (a b : ℕ) :
    (HomologicalComplex.homologyMap
          (triadChainMap (complexAppendMap a b) (complexAppendMap_mem_setA a b)
            (complexAppendMap_mem_setB a b)) (2 * a + 2 * b)).hom
          (relCross (P := TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
            ({0}ᶜ : Set (Fin a → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)) (2 * a) (2 * b)
            (standardComplexLocalClass ℚ a) (standardComplexLocalClass ℚ b)) ≠ 0 := by
  intro h
  apply orient_ne_zero a b
  rw [orient_eq_triadToUnion_triadChainMap, h, map_zero]
```

with `orient_ne_zero` proved in RT4 from upstream's `standardComplexLocalClass_ne_zero` by applying the inverse of the identity isomorphism of pairs (`relativeHomologyMap_comp`, `Iso.hom_inv_id`, `relativeHomologyMap_id`) and a degree-cast lemma by `subst`, the pattern of `HodgeLadder.Tests.cast_standardComplexLocalClass_ne_zero`. So the triad push-forward that `local-class-cross-model` reads is nonzero for every a, b, and the cross product feeding it is nonzero. The full text is in change 4.

## 4. Interface rung?

Not applicable: the file declares no structure and assumes no input.

## 5. Checker and axioms

`python3 tools/check.py --no-build` in the worktree: `ACCEPTED: all checks passed`. The new module is not yet imported from `HodgeLadder.lean` or named in the ledger, so of the checker's passes only the sorry scan covers it (clean); the axioms come from RT1. `lake env lean HodgeLadder/Relative/CrossTriadNaturality.lean`: no output, about 5 seconds warm. No `sorry`, `native_decide`, `axiom`, `unsafe` or `set_option` in the file.

RT1 (`#print axioms`, a copy of the file): `triadSubspaceChainMap_eq`, `subsetLeft_triadRelativeChainProjection`, `subsetRight_triadRelativeChainProjection`, `singChainFunctor_map_subset`, `triadSubspaceChainMap_map_triadRelativeChainProjection`, `triadChainMap`, `triadRelativeChainProjection_triadChainMap`, `triadRelativeChainProjection_triadChainMap_assoc`, `singChainFunctor_map_eq_chainComplexMap`, `triadChainMap_id`, `triadChainMap_comp`, `triadChainMap_triadToUnionRelativeChainMap`, `relCross_naturality`: `[propext, Classical.choice, Quot.sound]`. `union_mem`: no axioms. Every declaration is the one the ledger note of this rung names (`triadChainMap`, `triadRelativeChainProjection_triadChainMap`, `triadChainMap_triadToUnionRelativeChainMap`, `relCross_naturality`, with `union_mem` under its new name); the rest are additions.

## 6. Conventions

| Convention | Where | Choice, read from source | Truth depends on it | Register |
|---|---|---|---|---|
| Chain map of a map of spaces | upstream `singularChainComplexFunctor`, `SSet.chainComplexMap` | σ ↦ f ∘ σ on singular simplices, coefficient 1 | yes, an identity of classes; no sign is possible | new row "Map of triads on triad chains" |
| Triad quotient and comparison | upstream `triadRelativeChainProjection` (`cokernel.π`), `triadToUnionRelativeChainMap` (cokernel descent of `relativeChainProjection`) | no sign, no scalar | yes | same row; already in "Relative homology cross product" |
| Shuffle naturality | Tau Ceti `TopCat.shuffle_naturality` through `crossChainMap_naturality`, `shB_naturality` | (f × g)_* ∘ shuffle = shuffle ∘ (f_* ⊗ g_*), no sign | yes | "Relative homology cross product", updated |
| Factor order | `relCross A B` with `x` on `P` first, on both sides of `relCross_naturality` | unchanged by the map | swapping would give (−1)^{mn} | already recorded |

No sign enters the rung: every map in it is either a cokernel descent of an unsigned chain map or the shuffle, applied with the same factor order on both sides. The truth of `relCross_naturality` as an exact equality depends on the shuffle being natural with no sign, which is the checked `shB_naturality`. Register edits this pass: row "Relative homology cross product" (status, triad-level naturality); new row "Map of triads on triad chains"; row "Triad cap product" (naturality under `triadChainMap` missing at the pin, change 3).

## 7. Equality first

All results are exact equalities of morphisms or of classes, with no scalar. The rung is a step toward the model identity `local-class-cross-model` (= 1) and through it `local-class-product` (sign +). It is not sufficient for that model on its own: change 3 is the missing step.

## 7b. Non-vacuity

The smallest test that would fail if the triad push-forward were zero is `triadChainMap_relCross_orientation_ne_zero a b`, already at a = 0, b = 1; a = b = 1 is the first case where both factors have positive dimension. It uses upstream's `standardComplexLocalClass`, `standardComplexLocalClass_ne_zero`, `relativeHomologyMap_comp`, `relativeHomologyMap_id`, `triadToUnionRelativeHomologyMap`, and this repository's `cross_orientation_orient`. It does not exist in the tree; RT4 proved it (change 4). A test that would separate `+` from `−` in `relCross_naturality` cannot exist as a statement about this rung alone, because the rung has no sign to choose: a wrong sign would make it false, and it is kernel-checked.

## 8. Pin drift

None. The file was written and checked at `2ead713`, the current pin, from `main` at `c486870`. On the next bump add to the drift list in `docs/sketches/local-class-product.md`: upstream `singularChainComplexFunctor` (the `rfl` of `singChainFunctor_map_eq_chainComplexMap`), `chainPairFunctor`, `TopPair.ofSubset` (`.map`, `.snd`), `TopPair.ofSubsetHom`, `TopPair.Hom.snd`, `triadSubspaceChainMap` (the `rfl` of `triadSubspaceChainMap_eq` reads its `biprod.desc` body), `triadSubspaceChainMap_triadRelativeChainProjection`, `triadRelativeChainProjection_triadToUnionRelativeChainMap`, `TopPair.Homotopy.relativeChainProjection_naturality`. A change to any of these breaks the build; it cannot change a statement silently, since every statement here is a `Prop` about upstream objects with no local definition other than the `cokernel.desc`.

## Questions from the prover

- **(i) `singChainFunctor.map f` in place of `SSet.chainComplexMap (TopCat.toSSet.map f) _`.** Accepted; section 1.
- **(ii) File name.** Keep the flat `HodgeLadder/Relative/CrossTriadNaturality.lean`, module `HodgeLadder.Relative.CrossTriadNaturality`, beside `HodgeLadder.Relative.CrossChain` (the `relative-cross-chain` red team made the same call, question (iii)). Correct the ledger's `file` hint `HodgeLadder/Relative/Cross/Triad/Naturality.lean` when posting. Optional later split, finding 7.
- **(iii) Rederive `relCrossUnion_naturality`?** No. It is checked and named in the ledger of `relative-cross-chain`; replacing its proof is churn. RT2 rederived it from `relCross_naturality` and the comparison lemma in four lines with the three standard axioms, which shows the two forms agree (the union membership proof `union_mem (f ⊗ₘ g) …` and `tensorHom_mem_union f g hf hg` give the same map of pairs by proof irrelevance). Record that in the ledger note; do not add the rederivation as a declaration.

## What `local-class-cross-model` needs, and what is still missing

The model statement lives on `Y = TopCat.of (Fin (a + b) → ℂ)` with `setA`, `setB`, and reads `unionRelativeTriadCapCohomologyLinear ℚ Y (setA a b) (setB a b) (2a) (2b) hY (projA^* u_a) (orient a b)`, paired with `projB^* u_b`. The route through this rung:

1. `orient a b = triadToUnion_Y (h^triad_* (relCross x y))`, h = `complexAppendMap a b`: proved in RT4 (`orient_eq_triadToUnion_triadChainMap`), from `cross_orientation_orient` and the homology form of `triadChainMap_triadToUnionRelativeChainMap` (change 2).
2. `unionRelativeTriadCapCohomologyLinear_on_comparison` (upstream) turns the left side into `triadCapCohomologyLinear ℚ Y (setA a b) (setB a b) … (projA^* u_a) (h^triad_* (relCross x y))`. Only the target needs excision (`hY`); the product side needs none.
3. **Missing:** naturality of upstream's triad cap under `triadChainMap` (change 3), giving `h_*(triadCap_{P ⊗ Q} (h^* projA^* u_a) (relCross x y))` with h restricted to (P ⊗ Q, rightProdSet) → (Y, setB).
4. Pair with `projB^* u_b`: naturality of upstream's evaluation `relativeCohomologyEquivDualHomology` (through `linearDualHomologyEquiv_naturality`, listed in the drift list) and `relativeCohomologyMap` functoriality, so that h ≫ projA and h ≫ projB become the maps of pairs given by the two projections of P ⊗ Q (equal by `ext; rfl` on `Fin.append`).
5. `cap-cross-evaluation` on P ⊗ Q, then `normalizedRelativeCoclass_pairing_self` on each factor.

Steps 1, 2 and 4 exist or are routine. Step 3 is a new rung on this route.

**An alternative route avoids step 3, and this rung too.** `local-class-product` reads the cup form, so the model can be computed on P ⊗ Q and moved to ℂ^{a+b} on the cohomology side: state the cap model on `TopCat.of (Fin a → ℂ) ⊗ TopCat.of (Fin b → ℂ)` with `leftProdSet {0}ᶜ _`, `rightProdSet _ {0}ᶜ` (both open, so excision holds there), where `cap-cross-evaluation` applies directly; pass to `relCup2` on P ⊗ Q by `triad-relative-cup-cap`; pull `relCup2` on ℂ^{a+b} back along `complexAppendMap` by `triad-relative-cup-naturality` (open subsets on both triads); and pair with `orient a b = h_*(relCrossUnion x y)` (`cross_orientation_orient`) by naturality of the evaluation pairing, ⟨γ, h_* c⟩ = ⟨h^* γ, c⟩. That route uses `relCrossUnion` and no triad-level push-forward. The thinker chooses; record the choice in the ledger note of `local-class-cross-model`. The cap route needs this rung and change 3; the cup route needs neither, but puts the whole transport on `triad-relative-cup-naturality` and `triad-relative-cup-cap`, both open.

## Findings

1. The statements are change 2 exactly, with `singChainFunctor.map f` for the definitionally equal `SSet.chainComplexMap (TopCat.toSSet.map f) _`; the refinement is harmless and matches upstream's naturality lemma (section 1).
2. All fourteen declarations are proved with the three standard axioms (`union_mem` with none); the file has no `sorry` and compiles without warnings (section 5).
3. Nothing is trivially true; quick proofs fail on both main statements, and `triadChainMap` is nonzero along `complexAppendMap` (sections 3, 7b).
4. No sign enters anywhere (section 6).
5. `relCross_naturality` and the comparison lemma are what `local-class-cross-model`, on its cap route, needs to move the cross product to `orient`, provided the homology form of the comparison lemma is added (change 2); RT4 proves the consumer shape.
6. `union_mem` is too generic for a public name in `HodgeLadder.Relative`. Nothing clashes at the pin (no `union_mem` declaration in Mathlib, upstream, `port/` or `HodgeLadder/`), but `union_mem` is a binder name in Mathlib (`Bornology.ofBounded`) and reads as a lemma about `Set.union`. The local naming pattern is `tensorHom_mem_union` (`CrossChain`); rename to `triadMap_mem_union` (change 1).
7. The parallel track `triad-relative-cup-naturality` defines the same chain map as `HodgeLadder.Cup.triadChainsMap` (`cokernel.map` of the same squares; its projection lemma `triadProj_triadChainsMap` has the same right side, with `ambientChainMap f`, an `abbrev` for the same functor's `map f`). Its docstring calls this rung's `triadChainMap` a "homology" map; it is a chain map. Two names for one map will cost a bridge later. Recommend that whichever rung posts second either uses the first's map or proves the bridge (change 5).
8. Naturality of upstream's triad cap under `triadChainMap` is not at the pin. `local-class-cross-model` as stated (cap form on ℂ^{a+b}) needs it; it should be a new rung with the statement of change 3. A cup-side route through `triad-relative-cup-naturality` avoids it (section "What `local-class-cross-model` needs"); the thinker chooses. Upstream also lacks naturality of `relativeCochainCohomologyEquiv` (it has the absolute `cochainCohomologyEquiv_naturality` only), which the proof of change 3 will need.
9. `relCrossUnion_naturality` should stay as checked; the rederivation in RT2 is recorded, not added (questions, (iii)).
10. No pin drift (section 8).

## Recommended changes

1. **Rename** `union_mem` to `triadMap_mem_union`, with its docstring unchanged, and update its one use in `triadChainMap_triadToUnionRelativeChainMap`:

```lean
/-- A map of triads `(X; A, B) → (Y; A', B')` is a map of pairs `(X, A ∪ B) → (Y, A' ∪ B')`. -/
lemma triadMap_mem_union {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    ∀ x ∈ A ∪ B, f x ∈ A' ∪ B' := by
  rintro x (h | h)
  exacts [Or.inl (hA x h), Or.inr (hB x h)]
```

2. **Homology form of the comparison lemma** (proved in RT2 and used in RT4; add after `triadChainMap_triadToUnionRelativeChainMap`):

```lean
/-- **`triadChainMap` commutes with upstream's comparison on homology**: the triad push-forward
followed by `triadToUnionRelativeHomologyMap` is the comparison followed by the push-forward
along the map of pairs `(X, A ∪ B) → (Y, A' ∪ B')`. No sign. -/
lemma triadToUnionRelativeHomologyMap_triadChainMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') (n : ℕ)
    (z : TriadRelativeHomology ℚ X A B n) :
    triadToUnionRelativeHomologyMap ℚ Y A' B' n
        ((HomologicalComplex.homologyMap (triadChainMap f hA hB) n).hom z) =
      relativeHomologyMap ℚ n (TopPair.ofSubsetHom f (triadMap_mem_union f hA hB))
        (triadToUnionRelativeHomologyMap ℚ X A B n z) := by
  have h := congrArg (fun φ : triadRelativeChainComplex ℚ X A B ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (A' ∪ B')) =>
        (HomologicalComplex.homologyMap φ n).hom z)
    (triadChainMap_triadToUnionRelativeChainMap f hA hB)
  simp only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h
  exact h
```

3. **New rung `triad-cap-naturality`** (kind `foundation`, depends on `relative-cross-triad-naturality`; if the thinker keeps the cap route, add it to the `depends_on` of `local-class-cross-model` and replace the "also naturality of upstream's triad cap … which upstream lacks" sentence of that rung's note with the rung id). Both statements elaborate at the pin (RT2); the union form is proved from the triad form in five lines with `triadUnionExcisionHomologyEquiv` surjectivity, `triadToUnionRelativeHomologyMap_triadChainMap` and `unionRelativeTriadCapCohomologyLinear_on_comparison` twice (RT2, axioms `sorryAx` only through the triad form):

```lean
/-- **Projection formula for upstream's triad cap**: for a map of triads `f`, capping with `α`
after the triad push-forward is the push-forward of capping with `f^* α`. No sign. -/
theorem triadCapCohomologyLinear_triadChainMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') (p q : ℕ)
    (α : RelativeCohomology ℚ (TopPair.ofSubset A') p)
    (z : TriadRelativeHomology ℚ X A B (p + q)) :
    triadCapCohomologyLinear ℚ Y A' B' p q α
        ((HomologicalComplex.homologyMap (triadChainMap f hA hB) (p + q)).hom z) =
      relativeHomologyMap ℚ q (TopPair.ofSubsetHom f hB)
        (triadCapCohomologyLinear ℚ X A B p q
          (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hA) α) z)

/-- The same for upstream's customary triad cap on `H_{p+q}(X, A ∪ B)`, given excision on both
triads. No sign. -/
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

   Route for the triad form: at chain level, `(triadChainMap f hA hB).f (p + q) ≫ triadCapHom ℚ Y A' B' p q φ = triadCapHom ℚ X A B p q (relativeCochainMap ℚ (TopPair.ofSubsetHom f hA) p φ) ≫ ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hB)).f q`, by cancelling the epimorphism `(triadRelativeChainProjection ℚ X A B).f (p + q)` (`triadRelativeChainProjectionComponentIsCokernel`), then `triadRelativeChainProjection_triadCapHom`, `relativeChainProjection_naturality`, `relativeCochainToAbsolute_relativeCochainMap` and `Simplicial.cap_naturality`, as in upstream's `relativeCapHom_naturality`; then homology through `triadCapShortComplexHom` and `Simplicial.homologyMap_eq_of_τ₂_eq`, and the cohomology argument through a relative form of `cochainCohomologyEquiv_naturality` for `relativeCochainCohomologyEquiv`, which upstream lacks and the rung must prove (it is a `linearDualMap` naturality; `linearDualHomologyEquiv_naturality` is the model). Sign: none; upstream's (−1)^p factors on the outer terms of `triadCapShortComplexHomSucc` appear identically on both sides. Register row "Triad cap product" names this rung.

4. **Non-vacuity test** (proved in RT4, standard axioms). Put it in `HodgeLadder/Tests/CrossTriadNaturality.lean` (imports `HodgeLadder.Relative.CrossTriadNaturality`, `HodgeLadder.Local.CrossOrientation`, `HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity`), or, if the maintainer prefers, move `orient_eq_triadToUnion_triadChainMap` and the two membership lemmas into `local-class-cross-model`, which uses them. The two theorems are in section 3; the helpers:

```lean
lemma complexAppendMap_mem_setA (a b : ℕ) :
    ∀ z ∈ leftProdSet (P := TopCat.of (Fin a → ℂ)) ({0}ᶜ : Set (Fin a → ℂ))
        (TopCat.of (Fin b → ℂ)), complexAppendMap a b z ∈ setA a b := by
  intro z hz h
  exact hz (funext fun i => (Fin.append_left z.1 z.2 i).symm.trans (congrFun h i))

lemma complexAppendMap_mem_setB (a b : ℕ) :
    ∀ z ∈ rightProdSet (TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
        ({0}ᶜ : Set (Fin b → ℂ)), complexAppendMap a b z ∈ setB a b := by
  intro z hz h
  exact hz (funext fun j => (Fin.append_right z.1 z.2 j).symm.trans (congrFun h j))

theorem orient_ne_zero (a b : ℕ) : orient a b ≠ 0 := by
  have key : ∀ {d d' : ℕ} (h : d = d')
      (x : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (Fin (a + b) → ℂ))
        (setA a b ∪ setB a b)) d), x ≠ 0 → (h ▸ x) ≠ 0 := by
    intro d d' h x hx; subst h; exact hx
  apply key
  intro h0
  apply standardComplexLocalClass_ne_zero (a + b)
  have := congrArg (relativeHomologyMap ℚ (2 * (a + b))
    (TopPair.isoOfSubset (Homeomorph.refl _) (fun z => union_eq a b z)).inv) h0
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, Iso.hom_inv_id,
    relativeHomologyMap_id] at this
  simpa using this
```

   (RT4 ran these in namespace `HodgeLadder.CrossOrientation` with `open HodgeLadder.Relative`.)

5. **One chain map, not two.** Before the second of `relative-cross-triad-naturality` and `triad-relative-cup-naturality` is posted, either make `HodgeLadder.Cup.triadChainsMap` an `abbrev` for `HodgeLadder.Relative.triadChainMap` (importing this module), or add the bridge, which closes by cancelling the triad projection:

```lean
theorem triadChainsMap_eq_triadChainMap {X X' : TopCat.{0}} (f : X' ⟶ X) {A B : Set X}
    {A' B' : Set X'} (hfA : ∀ x ∈ A', f x ∈ A) (hfB : ∀ x ∈ B', f x ∈ B) :
    HodgeLadder.Cup.triadChainsMap f hfA hfB = HodgeLadder.Relative.triadChainMap f hfA hfB
```

   (expected proof: `cancel_epi` of `triadRelativeChainProjection ℚ X' A' B'`, then `triadProj_triadChainsMap` and `triadRelativeChainProjection_triadChainMap`, closing by `rfl`; not run, the two files are in different worktrees). Correct that file's docstring, which calls `triadChainMap` a homology map. A later optional split: `triadChainMap` and its lemmas need only upstream's `Cap/Triad.lean` and the singular chain functor, so a module `HodgeLadder/Relative/TriadChainMap.lean` would let the cup track use it without importing Tau Ceti's shuffle.

6. **Ledger, when posting.** `module` `HodgeLadder.Relative.CrossTriadNaturality` (flat; correct the `file` hint); declarations: `triadChainMap`, `triadRelativeChainProjection_triadChainMap`, `triadMap_mem_union`, `triadChainMap_triadToUnionRelativeChainMap`, `triadToUnionRelativeHomologyMap_triadChainMap`, `relCross_naturality`, `triadChainMap_id`, `triadChainMap_comp`, `singChainFunctor_map_eq_chainComplexMap`, and the helpers; note "no sign", the rederivation of `relCrossUnion_naturality` (RT2), and the new rung `triad-cap-naturality`. Import the module from `HodgeLadder.lean`. Add the section 8 names to the drift list in `docs/sketches/local-class-product.md`.

Register (`docs/conventions.md`), this pass: row "Relative homology cross product" (status: triad-level naturality); new row "Map of triads on triad chains"; row "Triad cap product" (naturality missing at the pin, change 3).
