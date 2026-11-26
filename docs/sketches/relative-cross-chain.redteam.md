# Red team: `relative-cross-chain` (statement pass)

Date: 2026-11-26. Worktree `track/relative-cross-chain` from `8b3a2fa`, uncommitted: `HodgeLadder/Relative/CrossChain.lean` and the section "relative-cross-chain: statement" of `docs/sketches/local-class-product.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, Tau Ceti vendored at `7433fc3`. Phase: statement, before the five open proofs.

Read: the Lean file; the sketch section and the rest of `docs/sketches/local-class-product.md`; `docs/sketches/cycle-class-multiplicative.redteam.md` (shuffle sign, unnormalized chains); `docs/conventions.md` rows "Shuffle map", "Cross product of complex orientations", "Triad cap product"; `docs/references.md`; the ledger entries of `relative-cross-chain`, `cap-cross-evaluation`, `cross-orientation`, `local-class-cross-model`, `tauceti-cup-backport`, `triad-relative-cup`; decision 0011; `tools/check.py`. At the pin: upstream `Definitions/AlgebraicTopology/Singular/Cohomology.lean` (`SingularChainComplex`, `relativeChainFunctor`, `relativeChainProjection`), `Mathlib/Topology/Category/TopPair.lean` (`ofSubsetHom`, `isoOfSubset`), `Definitions/AlgebraicTopology/LocalHomology/{FundamentalClass,ComplexClass}.lean` (`puncturedPair`, `standardComplexLocalClass`), `Lemmas/AlgebraicTopology/LocalHomology/PuncturedEuclidean.lean` (`standardLocalClass_ne_zero_of_pos`), and in `Other`: `Singular/Cap/Triad.lean` (whole triad section and the comparison), `Singular/Excision/Triad.lean` (the quasi-isomorphism theorem), `Singular/Cap/Naturality.lean`. Tau Ceti in `port/`: `SimplicialSet/Shuffle.lean`, `Singular/Shuffle.lean`, `Singular/KoszulBraiding.lean`. Mathlib: `Algebra/Homology/ComplexShapeSigns.lean`.

Scratch (inside the worktree, deleted afterwards): RT1 the file with `#print axioms`; RT2 consumer shapes (`P ⊗ Q` against `TopCat.of (P × Q)`, the real form of `cross-orientation`, a point test, triad-level naturality); RT3 trivial proofs; RT4 the degree (0, 0) normalization lemma, proved.

**Verdict: pass with changes.** The statements are the literature's relative homology cross product, built through the sum-relative triad complex and then upstream's comparison map, with no sign beyond the Eilenberg–Zilber shuffle signs. The `∃!` is true: I checked by hand that the class does not depend on the ambient lift or on the representing cycle, and uniqueness follows from `exists_triadCycle_shuffle`. Nothing in the file is trivially true. The proved part (identity-shuffle coefficient `+1`, the simplex formula) is exactly what `cross-orientation` reads. The changes add a triad-level naturality that `local-class-cross-model` needs, a degree-zero normalization lemma (proved in scratch, text below), docstring citations of the register, and records. None weakens a statement.

## 1. Is this the statement the literature makes?

**Source.** [`Hatcher2002` §3.B; page numbers unverified]: the homology cross product H_i(X; R) ⊗ H_j(Y; R) → H_{i+j}(X × Y; R) is induced by a chain map C(X) ⊗ C(Y) → C(X × Y), natural in both spaces, sending a pair of vertices to the vertex of the product and satisfying ∂(a × b) = ∂a × b + (−1)^i a × ∂b. In the relative case the chain map sends C(A) ⊗ C(Y) + C(X) ⊗ C(B) into C(A × Y) + C(X × B), so it gives C(X, A) ⊗ C(Y, B) → C(X × Y)/(C(A × Y) + C(X × B)) → C(X × Y, A × Y ∪ X × B), and the relative cross product H_i(X, A) ⊗ H_j(Y, B) → H_{i+j}(X × Y, A × Y ∪ X × B) is the composite in homology. The second map is an isomorphism in homology when {A × Y, X × B} is excisive, for instance when A and B are open. [`Dold1972`, `Bredon1993` ch. VI; sections unverified] use the Eilenberg–Zilber shuffle map with the same normalization. Tau Ceti cites Eilenberg–Mac Lane 1953, Eilenberg–Zilber 1953 and Weibel §8.5 for `SSet.shuffle`.

| Literature | Lean | Agrees |
|---|---|---|
| spaces X, Y, subsets A, B (no openness) | `P Q : TopCat.{0}`, `A : Set P`, `B : Set Q` | yes; openness enters only when a consumer inverts the comparison |
| X × Y | `P ⊗ Q` (cartesian monoidal product of `TopCat`) | yes; RT2: `(P ⊗ Q : TopCat.{0}) = TopCat.of (P × Q)`, `fst P Q z = z.1`, `snd P Q z = z.2`, all by `rfl` |
| A × Y, X × B | `leftProdSet A Q = {z | fst P Q z ∈ A}`, `rightProdSet P B = {z | snd P Q z ∈ B}` | yes |
| C(X × Y)/(C(A × Y) + C(X × B)) | upstream `triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)` = coker(C(A') ⊞ C(B') → C(X)), whose image is the sum of the two images | yes |
| comparison to C(X × Y, A × Y ∪ X × B) | upstream `triadToUnionRelativeHomologyMap` (induced by the identity of ambient chains, `triadRelativeChainProjection_triadToUnionRelativeChainMap`) on `crossUnionPair A B = TopPair.ofSubset (leftProdSet A Q ∪ rightProdSet P B)` | yes; upstream's `TopPair.ofSubset (A ∪ B)` with these A, B is this pair syntactically |
| shuffle chain map, vertex to vertex, Koszul boundary | Tau Ceti `TopCat.shuffle` (a morphism of chain complexes for Mathlib's tensor product), then the coefficient map `λ_ : ℚ ⊗ ℚ ≅ ℚ` | yes; section 6 |
| [x] × [y] = [shuffle(x ⊗ y)] | `IsRelCross`, `relCross_homologyπ`, `relCrossUnion_homologyπ` | yes, no sign |
| first factor first | `x` on `P` is the first argument, and the identity shuffle moves in `P` first | yes |
| naturality in both pairs | `relCrossUnion_naturality`, along `TopPair.ofSubsetHom (f ⊗ₘ g)` | yes, no sign |

The relative cross product into the triad group exists for all subsets, as stated; the composite with the comparison is the literature's map whenever the literature defines one. The module docstring says excision makes the comparison an isomorphism "when `A` and `B` are open": upstream's theorem `triadToUnionRelativeChainMap_quasiIso_of_isOpen` takes `IsOpen (leftProdSet A Q)` and `IsOpen (rightProdSet P B)`, which follow from openness of A and B by continuity of the projections (change 5).

## 2. Can the hypotheses be satisfied?

Yes, for every A, B, m, n. Every class of H_m(P, A) is `homologyπ zx` for a cycle `zx` (homology projection surjective in `ModuleCat`), and every relative chain is the projection of an ambient chain (`cokernel.π` surjective), so `hx` and `hy` can be met for every pair of classes; `x = 0`, `zx = 0` meets them trivially. The cycle `z` is supplied by `exists_triadCycle_shuffle`. The universes are forced (`ℚ : Type`), and upstream's whole relative-homology layer is at universe 0.

Instances that carry content, elaborated in RT2:

- Point test: `relCrossUnion (P := TopCat.of PUnit.{1}) (Q := TopCat.of PUnit.{1}) (∅ : Set PUnit.{1}) ∅ 0 0 ≠ 0` elaborates. By the degree-zero lemma of change 3 (proved in RT4) the cross product of the two vertex classes is the vertex class of the product, which is nonzero (by hand, through the augmentation; not checked in Lean).
- Sign-visible test (the real form of `cross-orientation`), elaborated with `appendMap m n : TopCat.of (Fin m → ℝ) ⊗ TopCat.of (Fin n → ℝ) ⟶ TopCat.of (Fin (m + n) → ℝ)`, `(u, v) ↦ Fin.append u v` (continuity proved in RT2):

```lean
theorem cross_orientation_real (m n : ℕ) :
    relativeHomologyMap ℚ (m + n) (TopPair.ofSubsetHom (appendMap m n) (appendMap_mem m n))
      (relCrossUnion (P := TopCat.of (Fin m → ℝ)) (Q := TopCat.of (Fin n → ℝ))
        ({0}ᶜ : Set (Fin m → ℝ)) ({0}ᶜ : Set (Fin n → ℝ)) m n
        (standardLocalClass ℚ m) (standardLocalClass ℚ n)) =
      standardLocalClass ℚ (m + n)
```

  Upstream's `standardLocalClass ℚ d : RelativeHomology ℚ (puncturedPair ℝ d) d`, and `puncturedPair` is an `abbrev` for `TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) {0}ᶜ`, so it feeds `relCrossUnion` with no cast. At m = n = 1 the right side is nonzero (`standardLocalClass_ne_zero_of_pos 2`), so over ℚ the test distinguishes `+` from `−` and from the zero map.

## 3. Is anything trivially true?

No. Attempts (RT3, and the prover's, all failed):

| Target | Attempt | Result |
|---|---|---|
| `IsRelCross A B m n 0` | `intro x y zx zy z _ _ _; simp` | `simp` made no progress |
| `existsUnique_relCross` | `refine ⟨0, fun .. => ?_, fun g _ => ?_⟩ <;> aesop` | aesop fails, goals remain |
| `relCrossUnion_naturality` | `simp [relCrossUnion, relCross]` | unsolved goals |
| prover's list | `refine ⟨0, ?_, ?_⟩ <;> simp`, `exact ⟨0, by simp⟩`, `exact ⟨_, rfl⟩`, `rfl` | fail |

No definition unfolds to `True`, there is no `ℕ∞` coercion, and no index type is empty. Every hypothesis of `IsRelCross` is used: dropping `hx` would let `x` be any chain, and the claimed class would then depend on `x`.

`shuffleChain_idShuffle_coeff` is not vacuous: `simplexCoeff` is the identity on the summand of its simplex (`ι_simplexCoeff_self`) and zero on the others, so a coefficient `−1` or `0` would make the statement false for `T = ModuleCat.of ℚ ℚ`.

**The `∃!` is sound** (by hand, the content of proof step 3). Let x, x' be two lifts of zx. Then x − x' lies in the kernel of the cokernel projection, which in `ModuleCat` is the range of C(A) → C(P). By `TopCat.shuffle_naturality` along the inclusion of A and the identity of Q, together with the factorization of `A ⊗ Q ⟶ P ⊗ Q` through the subspace `leftProdSet A Q`, the shuffle of (x − x') ⊗ y lies in the range of C(A × Q), so the triad projection kills it. `iCycles` is a monomorphism, so z is the same. Next let zx' = zx + d w̄ be a homologous cycle, with w̄ lifted to w ∈ C_{m+1}(P). Then x' = x + dw + a with a in C(A), and

shuffle(dw ⊗ y) = d shuffle(w ⊗ y) − (−1)^{m+1} shuffle(w ⊗ dy).

Here dy lies in the range of C(B) (by `hy`), so the last term lies in C(P × B), and the two triad classes are equal. The same steps work in the second variable. Bilinearity comes from `shuffleBilin` and linearity of `homologyπ`. Uniqueness holds because every pair of classes has representatives, and `exists_triadCycle_shuffle` gives a z for each. So the map has no hidden choice of representatives.

**Robustness of the `.choose` design.** `relCross` is `Exists.choose` of a proof of a `Prop`. By proof irrelevance, replacing the `sorry` in `existsUnique_relCross` with a real proof does not change `relCross` up to definitional equality, so no statement downstream of it moves when the proofs land. `#print axioms relCross` currently lists `sorryAx` (RT1), as it must; the proved declarations use the three standard axioms only.

## 4. Interface rung?

Not applicable: the file declares no structure and assumes no input. The proof plan uses only checked Tau Ceti declarations and upstream `Other` declarations (`triadToUnionRelativeHomologyMap`, and `triadToUnionRelativeChainMap_quasiIso_of_isOpen` for consumers), which compile at the pin with the standard axioms (red team of `cycle-class-multiplicative`, section 5; their `.olean` files are now in the shared cache).

## 5. Checker

Statement phase, so the rung is not yet checkable. `python3 tools/check.py --no-build` in the worktree rejects, as expected: the sorry scan names the five open proofs (lines 310, 326, 358, 400, 424), and the axioms and import-clash checks fail because the prover's background `lake build` had not yet written `HodgeLadder/Cup/SupportedForget.olean`; that failure is unrelated to this file. RT1 (`lake env lean` on a copy): `shuffleChain_idShuffle_coeff` and `shuffleBilin_ι` use `[propext, Classical.choice, Quot.sound]`; `relCross` and `relCross_homologyπ` add `sorryAx`. The checker rejects any `sorry` on `main`, so the file lands only when all five proofs are done, with every declaration named in the ledger.

The `import all LefschetzPort.TauCeti.AlgebraicTopology.SimplicialSet.Shuffle` is acceptable. It is a private import within this package. It exposes the bodies of `SSet.stdSimplex.cone` and `prodCone` to this file only; it is not re-exported, adds no axiom, and changes no instance (the shuffle file's instances are `local`). No public route exists at the pin. `cone_apply_zero` and `cone_apply_succ` are public, but `prodCone x = (cone x.1, cone x.2)` is not, and the public `δ_zero_prodCone` and `δ_succ_prodCone` give the vertices after the first but not vertex 0. A public lemma would need a non-proof edit to the vendored file, which `docs/port-tauceti.md` does not allow. The cost: a re-vendor of Tau Ceti that changes `prodCone`'s body breaks this proof at build time. It cannot change a statement silently. Record it (change 6).

## 6. Conventions

| Convention | Where | Choice, read from source | Truth depends on it | Register |
|---|---|---|---|---|
| Tensor differential | Mathlib `instance : TensorSigns (ComplexShape.down ℕ)` and the `TotalComplexShape c c c` instance (`ComplexShapeSigns.lean`) | ε₁ = 1, ε₂(p, q) = (−1)^p: d(x ⊗ y) = dx ⊗ y + (−1)^p x ⊗ dy | the chain-map property of the shuffle and of Alexander–Whitney; the Koszul braiding (−1)^{pq}; the cycle property of relative products (proof step 2) | new row "Tensor product of chain complexes" |
| Shuffle signs | Tau Ceti `SSet.shuffleChain` (`shuffleChain_succ_succ`: a first vertical step carries (−1)^{p+1} before p + 1 remaining horizontal steps) | (−1)^N, N = (vertical, later horizontal) pairs; the identity shuffle is `+` | yes, for `cross-orientation` | row "Shuffle map" updated: now a Lean lemma |
| Chain-map property | `TopCat.shuffle` is a morphism in `ChainComplex (ModuleCat ℚ) ℕ` with Mathlib's monoidal structure | compatible with the Koszul differential by its type; checked in `tauceti-cup-backport` | yes | covered by the new row |
| Coefficient change | `crossChainMap`: `(chainComplexFunctor).map (λ_ (𝟙_ _)).hom` | 1 ⊗ 1 ↦ 1 (`ModuleCat.MonoidalCategory.leftUnitor_hom_apply`, used in `shuffleBilin_ι`); λ and ρ agree on the unit, so no choice | yes, the scale of the product | new row "Relative homology cross product" |
| Quotients | upstream `relativeChainProjection`, `triadRelativeChainProjection` (`cokernel.π`), `triadToUnionRelativeChainMap` (`cokernel` descent of the identity) | no sign, no scalar | yes | same row |
| Factor order | `relCross A B` with `x` on `P` first | x × y in H(P × Q); swapping factors gives (−1)^{mn} by Tau Ceti `TopCat.tensorBraiding_hom_comp_shuffle` | identities that swap factors | same row |

**The sign of the whole map.** (b) pins one coefficient, the one `cross-orientation` reads: at a point inside the identity-shuffle simplex every other prism simplex vanishes in the local relative group. The remaining coefficients are fixed by Tau Ceti's recursion, which is on the drift list. In homology the sign is pinned independently of that chain formula: a natural chain map C(P) ⊗ C(Q) → C(P × Q) that is a chain map for the Koszul differential and sends a pair of vertices to the vertex of the product is unique up to natural chain homotopy (acyclic models [`Hatcher2002` §3.B, `Dold1972`; unverified]). So any cross product with the literature's vertex normalization and boundary formula agrees with `relCross` exactly, with no sign. The vertex normalization is change 3; the boundary formula is the type of `TopCat.shuffle`. The prior red team's counts (every shuffle simplex of s_m × s_n times its sign has orientation sign(s_m) sign(s_n), for small (m, n)) are consistent with this.

**Sign of the identity-shuffle simplex in degree (1, 1).** Tau Ceti's `ιChainComplex_tensorHom_ιChainComplex_shuffle_f_one_one` gives (s₁x, s₀y) − (s₀x, s₁y). The vertex maps are s₁ = [0, 1, 1] and s₀ = [0, 0, 1], so the + term has vertex pairs (0, 0), (1, 0), (1, 1), which is `idShuffle 1 1 2` (vertices (min i 1, i − 1)). This agrees with (b).

No result here depends on a convention that the register does not list after this pass.

## 7. Equality first

`relCross_homologyπ`, `relCrossUnion_homologyπ` and `relCrossUnion_naturality` are equalities of classes, exact, with no scalar; `shuffleChain_idShuffle_coeff` is an exact equality of morphisms (`= 𝟙 T`). The rung is a step toward the identity of `local-class-product` (sign +), through `cap-cross-evaluation`, `cross-orientation` and `local-class-cross-model`, all open in the ledger. CLAUDE.md asks equality statements to cite their register row in the docstring; the three docstrings do not yet (change 4).

## 7b. Non-vacuity

The smallest test that would fail if the cross product were zero or had the wrong sign is `cross_orientation_real 1 1` (section 2, elaborated). It belongs to `cross-orientation` and does not exist yet. It reads upstream's `standardLocalClass`, `puncturedPair`, `relativeHomologyMap`, `TopPair.ofSubsetHom` and `standardLocalClass_ne_zero_of_pos`. The smallest test that would fail if the map were zero is the point test, and change 3 is the lemma it needs; it has been proved in RT4. Neither test exists in the tree. Add the first to the ledger note of `cross-orientation`.

## 8. Pin drift

None. The file was written and elaborated at `2ead713`, which is the current pin, against Tau Ceti `7433fc3`, which is the vendored commit. On the next bump add to the drift list: Tau Ceti `SSet.shuffleChain`, `SSet.stdSimplex.cone`, `prodCone`, `prodConeChain`, `SSet.shuffle`, `TopCat.shuffle` (bodies, since this file reads `cone` and `prodCone` through `import all`); Mathlib `TensorSigns (ComplexShape.down ℕ)`, `ιTensorObj`, `ModuleCat` left unitor, `Functor.LaxMonoidal.μ TopCat.toSSet`; upstream `relativeChainFunctor`, `relativeChainProjection`, `TopPair.ofSubset`, `TopPair.ofSubsetHom`, `triadSubspaceChainMap`, `triadRelativeChainComplex`, `triadRelativeChainProjection`, `triadToUnionRelativeChainMap`, `triadToUnionRelativeHomologyMap`.

## Questions from the sketch

- **(i) Does `local-class-cross-model` need triad-level naturality?** Yes, in its current form. Its statement lives on `TopCat.of (Fin (a + b) → ℂ)` with `setA`, `setB`, and `unionRelativeTriadCapCohomologyLinear` inverts the excision map there. The cross product lives on `ℂ^a ⊗ ℂ^b` with `leftProdSet`, `rightProdSet`. Moving it along the `Fin.append` homeomorphism needs (a) a chain map of triad complexes for a map of triads, compatible with the comparison, so that e_X⁻¹(h_* (e (relCross x y))) = h^triad_* (relCross x y), and (b) naturality of upstream's triad cap under that map. Upstream defines neither (no triad maps in `Cap/Triad.lean` or `Cap/Naturality.lean`). (a) belongs in this rung (change 2); (b) belongs in `cap-cross-evaluation` or `local-class-cross-model`. The alternative is to state the model on `TopCat.of (Fin a → ℂ) ⊗ TopCat.of (Fin b → ℂ)`, where e⁻¹ (relCrossUnion x y) = relCross x y holds directly. The thinker chooses; record the choice in the ledger note of `local-class-cross-model`.
- **(ii) `P ⊗ Q` or `TopCat.of (P × Q)`?** Keep `P ⊗ Q`; `TopCat.shuffle` lands there. The two are equal by `rfl`, and so are the projections (RT2), so consumers can write either.
- **(iii) File name.** `HodgeLadder/Relative/CrossChain.lean`, module `HodgeLadder.Relative.CrossChain`, flat like `HodgeLadder.Cup.RelativeCup`. Correct the ledger's `module` hint `HodgeLadder/Relative/Cross/Chain.lean` when posting.
- **Naturality in the form `cross-orientation` needs.** Yes. The complex form moves both factors along `complexRealHomeomorph`. `standardComplexLocalClass` is a `▸` cast of `(relativeHomologyFunctor R (p * 2)).mapIso (standardComplexRealPairIso p)` applied to `standardLocalClass`, and `relCrossUnion_naturality` takes maps of the form `TopPair.ofSubsetHom`. The consumer also needs a one-line degree-cast lemma (by `subst`) for the `Nat.mul_comm` casts, and the pair map `crossUnionPair → puncturedPair` along `Fin.append` (RT2 shape), which is plain functoriality of `relativeHomologyMap`.

## Findings

1. The statements match the literature's relative homology cross product field by field (section 1), for all subsets, through the triad group.
2. The `∃!` is true and has no hidden choice: lift independence and cycle independence check by hand, and uniqueness follows from `exists_triadCycle_shuffle` (section 3).
3. Nothing is trivially true; four quick proofs fail (section 3).
4. The sign is pinned twice: the chain-level formula by Tau Ceti's recursion, with (b) proving the coefficient `cross-orientation` reads; and the homology map by the vertex normalization and the Koszul chain-map property, independently of the chain formula. Mathlib's tensor differential is d(x ⊗ y) = dx ⊗ y + (−1)^p x ⊗ dy, read from source, and the shuffle is a chain map for it by its type (section 6).
5. The (1, 1) check of the sketch is correct (section 6).
6. `local-class-cross-model` as stated needs triad-level naturality, which upstream lacks (questions, (i)).
7. `import all` is justified, and its cost is a build break on a re-vendor, not a silent change (section 5).
8. Equality docstrings do not cite the register (section 7).
9. No drift (section 8).

## Recommended changes

1. **Ledger** (when posting): `module` `HodgeLadder.Relative.CrossChain`; `declarations` the proved and stated names, plus those of changes 2 and 3; note the sign-visible test of `cross-orientation` (section 2) in that rung's ledger note.

2. **Triad-level naturality** (add to this rung; `relCrossUnion_naturality` then follows from it and the compatibility lemma). Elaborated in RT2 with the proof obligations as `sorry`; the obligation of `triadChainMap` is true by `biprod` extensionality and naturality of the subspace inclusions.

```lean
/-- A map `f : X ⟶ Y` with `f '' A ⊆ A'` and `f '' B ⊆ B'` induces a chain map of upstream's
sum-relative triad complexes. -/
noncomputable def triadChainMap {X Y : TopCat.{0}} (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y}
    (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    triadRelativeChainComplex ℚ X A B ⟶ triadRelativeChainComplex ℚ Y A' B' :=
  cokernel.desc _ (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) ≫
    triadRelativeChainProjection ℚ Y A' B') (by sorry)

@[reassoc]
lemma triadRelativeChainProjection_triadChainMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    triadRelativeChainProjection ℚ X A B ≫ triadChainMap f hA hB =
      SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) ≫
        triadRelativeChainProjection ℚ Y A' B' :=
  cokernel.π_desc _ _ _

lemma union_mem {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    ∀ x ∈ A ∪ B, f x ∈ A' ∪ B' := by
  rintro x (h | h)
  exacts [Or.inl (hA x h), Or.inr (hB x h)]

lemma triadChainMap_triadToUnionRelativeChainMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y} (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    triadChainMap f hA hB ≫ triadToUnionRelativeChainMap ℚ Y A' B' =
      triadToUnionRelativeChainMap ℚ X A B ≫
        (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f (union_mem f hA hB))

/-- **Naturality of the relative cross product at the triad level**, no sign. -/
theorem relCross_naturality {P P' Q Q' : TopCat.{0}} (f : P ⟶ P') (g : Q ⟶ Q')
    {A : Set P} {A' : Set P'} {B : Set Q} {B' : Set Q'}
    (hf : ∀ a ∈ A, f a ∈ A') (hg : ∀ b ∈ B, g b ∈ B') {m n : ℕ}
    (x : RelativeHomology ℚ (TopPair.ofSubset A) m)
    (y : RelativeHomology ℚ (TopPair.ofSubset B) n) :
    relCross A' B' m n (relativeHomologyMap ℚ m (TopPair.ofSubsetHom f hf) x)
        (relativeHomologyMap ℚ n (TopPair.ofSubsetHom g hg) y) =
      (HomologicalComplex.homologyMap
        (triadChainMap (f ⊗ₘ g) (A' := leftProdSet A' Q') (B' := rightProdSet P' B')
          (fun z hz => hf _ hz) (fun z hz => hg _ hz)) (m + n)).hom
        (relCross A B m n x y)
```

   If the maintainer prefers to keep this rung as it is, open `relative-cross-triad-naturality` with these declarations, depending on `relative-cross-chain`, and add it to the `depends_on` of `local-class-cross-model`. In either case the ledger note of `local-class-cross-model` should say that it also needs naturality of upstream's triad cap under `triadChainMap`, unless the model is restated on the product space.

3. **Degree-zero normalization** (proved in RT4, standard axioms; add after `shuffleBilin_ι`):

```lean
/-- **Vertex normalization**: the shuffle product of two singular vertices is the vertex of the
product, with coefficient `1` (register row "Relative homology cross product"). -/
theorem shuffleBilin_vertex {P Q : TopCat.{0}} (σ : (TopCat.toSSet.obj P) _⦋0⦌)
    (τ : (TopCat.toSSet.obj Q) _⦋0⦌) :
    shuffleBilin P Q 0 0
        (((TopCat.toSSet.obj P).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom (1 : ℚ))
        (((TopCat.toSSet.obj Q).ιChainComplex (R := ModuleCat.of ℚ ℚ) τ).hom (1 : ℚ)) =
      ((TopCat.toSSet.obj (P ⊗ Q)).ιChainComplex (R := ModuleCat.of ℚ ℚ)
        ((Functor.LaxMonoidal.μ TopCat.toSSet P Q).app _
          ((σ, τ) : (TopCat.toSSet.obj P ⊗ TopCat.toSSet.obj Q) _⦋0⦌))).hom (1 : ℚ) := by
  rw [shuffleBilin_ι]
  erw [SSet.shuffleChain_zero_zero (ModuleCat.of ℚ ℚ) rfl
      (SSet.yonedaEquiv (𝟙 _), SSet.yonedaEquiv (𝟙 _)), SSet.ι_chainComplexMap_f]
  change (((TopCat.toSSet.obj (P ⊗ Q)).ιChainComplex (R := ModuleCat.of ℚ ℚ)
    ((Functor.LaxMonoidal.μ TopCat.toSSet P Q).app _
      (((SSet.yonedaEquiv.symm σ).app _ (SSet.yonedaEquiv (𝟙 _)),
        (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (𝟙 _))) :
          (TopCat.toSSet.obj P ⊗ TopCat.toSSet.obj Q) _⦋0⦌))).hom (1 : ℚ)) = _
  rw [SSet.yonedaEquiv_symm_app_id, SSet.yonedaEquiv_symm_app_id]
```

4. **Docstrings.** Cite the register rows "Relative homology cross product" and "Shuffle map" in the docstrings of `relCross_homologyπ`, `relCrossUnion_homologyπ`, `relCrossUnion_naturality` and `shuffleChain_idShuffle_coeff`, and say "no sign" in the first two.

5. **Module docstring.** Replace "excision makes it an isomorphism when `A` and `B` are open" with "upstream's `triadToUnionRelativeChainMap_quasiIso_of_isOpen` makes it an isomorphism when `leftProdSet A Q` and `rightProdSet P B` are open, in particular when `A` and `B` are open".

6. **Records.** `docs/gaps.md` "General lemmas kept local": `simplexCoeff`, `idShuffle`, `shuffleChain_idShuffle_coeff` (any preadditive category with coproducts), `triadChainMap`, and the map H_m(K) ⊗ H_n(L) → H_{m+n}(K ⊗ L) of proof step 3 once written. `docs/port-tauceti.md`: one line saying `HodgeLadder.Relative.CrossChain` reads `cone` and `prodCone` through `import all`, so a re-vendor must rebuild it. Add the section 8 names to the drift list in `docs/sketches/local-class-product.md`.

Register (`docs/conventions.md`), this pass: row "Shuffle map" updated; new rows "Tensor product of chain complexes" and "Relative homology cross product".
