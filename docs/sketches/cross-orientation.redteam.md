# Red team: `cross-orientation` (statement pass)

Date 2026-11-26. Target: `HodgeLadder/Local/CrossOrientation.lean` (namespace `HodgeLadder.CrossOrientation`, uncommitted, not imported from the root) and the section "cross-orientation: statement" of `docs/sketches/local-class-product.md`, on branch `track/cross-orientation` from `79df873`. Pin: upstream `Paul-Lez/HodgeConjecture` at `2ead713`, the same as `main` and as the red teams of `real-affine-orientation` and `relative-cross-chain`.

**The sign is +.** I tried to make it −1 by every route I could find and none works. In the real form, s_m × s_n = s_{m+n} under `Fin.append` holds with sign + in every pair of real dimensions. I recomputed it three ways. By hand: the block determinant. By exact arithmetic: the full Tau Ceti shuffle chain, every term, for 0 ≤ m, n ≤ 4, read at six random points of the open prism for each pair. In Lean: the proved lemmas. In the complex form the sign depends on no choice at all. Any ℂ-linear identification ℂ^a × ℂ^b ≅ ℂ^{a+b} gives the same class, because upstream proves that invertible complex matrices fix `standardComplexLocalClass`. The block order cannot matter either, since (−1)^{(2a)(2b)} = 1. A sign (−1)^{ab} needs a real coordinate order that is not the complex orientation, such as real parts first, and upstream does not use one. Nothing in the statements forces + by convention. The real form's + depends on two first-factor-first choices, and flipping either one alone flips the sign by (−1)^{mn}. Both choices are fixed by checked or proved declarations.

**Verdict: pass with changes.** All three open statements are true as written, exactly signed, sign-visible and not trivially provable. The changes add non-vacuity lemmas that the ledger can name, an optional corollary in the `orient` form that `local-class-cross-model` reads, and records. None weakens a statement.

Scratch work: files inside the worktree importing the built module `HodgeLadder.Local.CrossOrientation` (olean newer than the source), checked with `lake env lean`, then deleted. RT1: elaborated statement, axioms, the cast tests, non-vacuity, sign separation. RT2: trivial tactics, and the `orient` corollary. RT3: which upstream lemmas the module imports. Python (exact rationals, plus `scipy` linear programs) in the session scratchpad, outside the repository.

## 1. Is this the statement the literature makes?

Literature. The cross product of local orientations of ℝ^m and ℝ^n is the local orientation of ℝ^{m+n} = ℝ^m × ℝ^n with the product orientation (first factor's basis first). The Eilenberg–Zilber shuffle map gives the identity shuffle (all first-factor steps first) the sign + [`Hatcher2002` §3.B; `Bredon1993`; `Dold1972`; sections unverified]. The canonical orientation of a complex vector space comes from the real basis (v₁, iv₁, v₂, iv₂, …). For V ⊕ W it is the product of the orientations of V and W, and the Thom class of a product bundle is the cross product of the Thom classes [`MilnorStasheff1974`, section numbers unverified]. So the cross product of complex orientation classes is the complex orientation class, with sign +.

| Field | Literature | Lean | Match |
|---|---|---|---|
| Real local class | a generator of H_d(ℝ^d, ℝ^d ∖ 0) | upstream `standardLocalClass ℚ d`: the class of t ↦ (t_j − t_d)_j, vertices e₀, …, e_{d−1}, (−1, …, −1), coefficient 1 | yes. It is the standard orientation exactly when d is even (det E(s_d) = (−1)^d (d + 1), checked). The real form compares upstream's class with itself, so this reference sign cancels: the identity is s_m × s_n = s_{m+n}, with no orientation convention left in it |
| Complex local class | the complex orientation of ℂ^p | upstream `standardComplexLocalClass ℚ p`: `standardLocalClass ℚ (p * 2)` moved by the inverse of `standardComplexRealPairIso p`, built from `complexRealHomeomorph p = (Complex.piCoordCLE p).toHomeomorph`, coordinates (Re z₀, Im z₀, Re z₁, …), cast from degree p * 2 to 2 * p | yes. s_{2p} is the standard orientation of ℝ^{2p}, and consecutive (Re, Im) is the basis (e₀, ie₀, e₁, ie₁, …). It is the class cycle classes are normalized by (`docs/cycle-class.md` step 1: `normalizedRelativeCoclass` of `standardComplexLocalClass`) |
| Cross product | shuffle (Eilenberg–Zilber) map, first factor first, identity shuffle + | `HodgeLadder.Relative.relCrossUnion` (checked): Tau Ceti `SSet.shuffleChain`, the left unitor ℚ ⊗ ℚ ≅ ℚ, upstream's triad-to-union comparison, no further sign | yes (red team of `relative-cross-chain`; section 6 below recomputes the chain's signs) |
| Identification | ℝ^m × ℝ^n = ℝ^{m+n}, (u, v) ↦ (u, v); ℂ^a × ℂ^b = ℂ^{a+b} | `appendMap m n`, `complexAppendMap a b`: z ↦ `Fin.append z.1 z.2` (RT1: both `rfl`) | yes, first factor first. It matches `local-class-cross-model`: its `projA` reads `Fin.castAdd b`, the first block, and its `setA` is the first factor's puncture |
| Degree | 2a + 2b = 2(a + b) | left side in degree `2 * a + 2 * b` with no cast; right side `(Nat.mul_add 2 a b) ▸ standardComplexLocalClass ℚ (a + b)` | yes; the cast cannot carry a scalar (section 3) |

Full strength. The complex form is the identity that decision 0009 asks for: an exact equality of upstream's normalized classes, with no "up to a scalar", for every a, b ≥ 0. Its sign does not depend on the identification within the ℂ-linear ones (section 6, item 4). A rung stating it for every invertible complex matrix applied after `complexAppendMap` would be stronger. It follows at once from `cross_orientation_complex` and upstream's `relativeHomologyMap_complexMatrix_standardComplexLocalClass`, so it is not needed as a separate rung.

**Could an equally natural identification give (−1)^{ab}?** Only one that does not give the complex orientation on each factor. With real parts first on every ℂ^p, (Re z₀, …, Re z_{p−1}, Im z₀, …, Im z_{p−1}), each class would be (−1)^{p(p−1)/2} times the complex orientation, and p(p−1)/2 at p = a + b equals a(a−1)/2 + b(b−1)/2 + ab. The product would then carry (−1)^{ab}. Upstream uses consecutive pairs (pinned: `HodgeLadder.Pins.complexRealHomeomorph_eq`). Under the proved `complexRealHomeomorph_append` the block identification is the identity on real coordinates. The other two variations change nothing. (Im, Re) in every coordinate changes each class by (−1)^p, and (−1)^a (−1)^b = (−1)^{a+b}. The second block first is complex-linear. So + holds for every orientation-consistent choice.

**Which one does the downstream need?** Cycle classes are normalized by `standardComplexLocalClass` read through holomorphic charts. Upstream's `relativeHomologyMap_complexDifferentiable_standardComplexLocalClass` makes that reading chart-independent (`docs/cycle-class.md`, "Chart independence"). In `local-class-product` the normal coordinates of Z ∩ W are (φ₂, φ₃), appended. Any holomorphic reordering of them gives the same class. So the transversal-intersection identity [Z] ∪ [W] = [Z ∩ W] needs exactly this sign +. Under a real-parts-first normalization upstream's cycle classes would be multiplicative only up to (−1)^{ab}, and the rung would have caught that. It is not the case at the pin.

## 2. Can the hypotheses be satisfied?

`cross_orientation_real` and `cross_orientation_complex` have no hypotheses beyond m, n, a, b : ℕ. `eq_idShuffle_of_shuffleBarycenter` is satisfiable: x = `idShuffle m n (m + n) rfl` and t constant 1/(m + n + 1) satisfy `ht`, `ht1`, `h` (h is then the definition of `shuffleBarycenter` after `Fin.append` of the vertices, which is `shuffleVertices`). Every pair of monotone vertex maps is a simplex of `Δ[m] ⊗ Δ[n]`, so the universally quantified x ranges over degenerate simplices too. The proved lemmas have no hypotheses, apart from the vertex lists of `det_edgeMatrix_shuffleVertices` and `appendMap_idShuffle`, which any list meets.

## 3. Is anything trivially true?

No.

- RT2: `first | rfl | simp | trivial | decide` on both open identities fails ("Expected type must not contain free variables" from the last alternative), and `aesop` makes no progress on either. The prover reports the same for `grind`, `norm_num` and `exact?` on all three open statements.
- **Sign visibility, real.** RT1 proves `standardLocalClass ℚ (m + n) ≠ -standardLocalClass ℚ (m + n)` for 0 < m + n, from upstream's `standardLocalClass_ne_zero_of_pos`. It also proves that the stated real form and its negation (right side `-standardLocalClass ℚ (m + n)`) cannot both hold at m = n = 1. So the identity separates + from −. It separates both from 0 by `standardLocalClass_ne_zero_of_pos`.
- **Sign visibility, complex.** RT1 proves `(Nat.mul_add 2 a b) ▸ standardComplexLocalClass ℚ (a + b) ≠ 0` for every a, b. The proof: a cast lemma by `subst`, then upstream's `standardComplexLocalClass_ne_zero (a + b)`. So the complex form is sign-visible at every (a, b), including a = b = 0, where both sides are the point class.
- **The cast.** RT1 proves `((Nat.mul_add 2 1 1) ▸ standardComplexLocalClass ℚ (1 + 1)) = standardComplexLocalClass ℚ (1 + 1)` by `rfl`. At numerals the cast is the identity. RT1 also proves `h ▸ (c • x) = c • (h ▸ x)` for any degree equation h by `subst h; rfl`. Transport along an equation of degrees is `Eq.rec` on a proof-irrelevant equation in ℕ, so it cannot hide a sign. `#check` with `pp.proofs` shows that the motive rewrites only the degree argument (`2 * a + 2 * b`), and the pair `puncturedPair ℂ (a + b)` is left alone.
- **Unused hypotheses.** None. In `eq_idShuffle_of_shuffleBarycenter`, `ht` is needed (without t ≥ 0, non-convex combinations reach the barycenter from other vertex maps), and so are `ht1` and `h`.

## 4. Interface rung?

No. The rung defines no structure and assumes no `Prop`. Not applicable.

## 5. Checker

`python3 tools/check.py --no-build` on the worktree: every ledger-named declaration is accepted, and the only rejection is the sorry scan on `HodgeLadder/Local/CrossOrientation.lean` lines 279, 294, 309: the three open statements. RT1 `#print axioms`: `complexRealHomeomorph_append`, `appendMap_idShuffle` and `sign_det_edgeMatrix_shuffleVertices_standard_mul` use `propext`, `Classical.choice`, `Quot.sound` only, and `cross_orientation_real` adds `sorryAx`, as expected. The rung is `open` in the ledger with no declarations. When it is posted, the ledger's `module` and `declarations` must name the file's declarations. The file must be imported from `HodgeLadder.lean` (propagation map, "Prove a rung").

## 6. Conventions and every sign, recomputed

| # | Sign | My value | How I recomputed it | Truth depends on it? |
|---|---|---|---|---|
| 1 | identity-shuffle coefficient in Tau Ceti `shuffleChain` | +1 | read the recursion (`shuffleChain_succ_succ`: horizontal cone with +, vertical cone with (−1)^{p+1}; base cases with +) and re-implemented it in Python: the identity shuffle has coefficient 1 for all m, n ≤ 4 (also the checked `shuffleChain_idShuffle_coeff`) | yes |
| 2 | vertex order of the identity-shuffle simplex | k ↦ (v_{min(k,m)}, w_{k−m}) | `idShuffle` definition; the proved `appendMap_idShuffle` pushes it to the affine simplex on `shuffleVertices` | yes: with the second factor first in the vertex order alone, det carries (−1)^{mn} |
| 3 | edge determinant of the identity-shuffle simplex | det E(v) · det E(w) | by hand. Columns i < m are (v_{i+1} − v₀, 0), and columns m + i are (v_m − v₀, w_{i+1} − w₀). Rows are the first block, then the second (`Fin.append`). So E = [[E(v), B], [0, E(w)]], block upper triangular. Exact rationals for m, n ≤ 4 agree, for example m = n = 2 gives 9 = 3 · 3 and m = 3, n = 4 gives −20 = (−4) · 5 (also the proved `det_edgeMatrix_shuffleVertices`) | yes: with the second block first in the coordinates alone, (−1)^{mn} |
| 4 | coordinate order of ℂ^a × ℂ^b in ℂ^{a+b} | identity | `finProdFinEquiv (i, j)` has value 2i + j. Index 2i + j of block a stays 2i + j, and index 2(a + i) + j becomes 2a + (2i + j). Proved as `complexRealHomeomorph_append` (it unfolds `Complex.piBasisOneI`, so a change of upstream's basis breaks it) | no for the complex form's truth within ℂ-linear identifications (upstream `relativeHomologyMap_complexMatrix_standardComplexLocalClass`). Yes against a real-parts-first convention, (−1)^{ab} |
| 5 | class of an affine simplex at an interior point | sign(det E) · (−1)^d · o_y | checked `affineSimplex_homologyπ`; (−1)^d = sign det E(s_d) | yes |
| 6 | scalar at the identity-shuffle simplex | sign((−1)^m (m+1) (−1)^n (n+1)) · (−1)^{m+n} = 1 | by hand; proved `sign_det_edgeMatrix_shuffleVertices_standard_mul` | yes |
| 7 | the whole shuffle chain at a generic point | scalar 1 | Python: for 0 ≤ m, n ≤ 4, every term of the re-implemented shuffle chain of s_m × s_n has c · sign(det E) = (−1)^{m+n}, a coherent fundamental chain of the prism. At six random rational points of the open prism (product of open simplices) per pair, exactly one term contains the point, and the local degree divided by sign det E(s_{m+n}) is 1. This checks the route's claim that the class over U, read at any point of U, is s_{m+n}, and the claim does not depend on the barycenter | yes |
| 8 | other simplices at the barycenter | absent | proof below; Python LP over every pair of monotone vertex maps of length m + n + 1, degenerate ones included, for 0 ≤ m, n ≤ 3 (up to 14400 pairs at (3, 3)): only the identity shuffle reaches the barycenter | route only |
| 9 | coefficient change ℚ ⊗ ℚ → ℚ | 1 ⊗ 1 ↦ 1 | checked `shuffleBilin_ι` | yes |
| 10 | translation back to 0 | none | checked `relativeHomologyMap_point_eq_translate`, `relativeHomologyMap_translation_injective` | no sign possible (translation is homotopic to the identity on the convex U) |
| 11 | degree casts `Nat.add_mul a b 2`, `Nat.mul_add 2 a b`, upstream `Nat.mul_comm p 2` | none | section 3 (`rfl` at numerals; casts commute with scalars) | no |

Hand instance m = n = 1. s₁ runs from 1 to −1, det E = −2. Identity shuffle: (1, 1), (−1, 1), (−1, −1), edges (−2, 0) and (−2, −2), det 4 > 0. s₂ = (1, 0), (0, 1), (−1, −1), edges (−1, 1) and (−2, −1), det 3 > 0. The other shuffle (1, 1), (1, −1), (−1, −1) has coefficient −1 and det −4, so it contributes the same orientation, and the square is coherently oriented. The barycenter (−1/3, 1/3) lies above the diagonal, off the second triangle. Scalar +1.

**`eq_idShuffle_of_shuffleBarycenter` is true as stated, degenerate simplices included.** Write N = m + n + 1. The vertices of s_m are affinely independent (det E(s_m) = (−1)^m (m + 1) ≠ 0), so the first block of `h` fixes the weights α_j = Σ_{x.1 k = j} t_k = (1/N, …, 1/N, (n+1)/N). Likewise β = ((m+1)/N, 1/N, …, 1/N). Since x.1 and x.2 are monotone, {k : x.1 k ≤ j} and {k : x.2 k ≤ j} are prefixes [0, L) of Fin N. Their t-sums S(L) take the values (j+1)/N for j < m, (m+1+j)/N for j < n, and N/N: N distinct values in (0, 1]. S is nondecreasing in L (t ≥ 0), so distinct values sit at distinct L ∈ {1, …, N} in the same order. That forces S(L) = L/N, hence t_k = 1/N, x.1 k = min k m and x.2 k = k − m (truncated), which is `eq_idShuffle_iff`. The cases m = 0 and n = 0 are covered: one weight vector is then trivial, and the x component is constant by `Fin 1`. The docstring's sketch is this argument.

Conventions register. My findings sharpen the row "Cross product of complex orientations": they add which choices the real sign depends on and the independence of the complex sign from the ℂ-linear identification, and they update the status. I edited the row. The rows "Shuffle map", "Relative homology cross product", "Real local orientation and affine maps" and "Complex orientation of ℂ^p" match what the file uses, and I left them unchanged.

## 7. Equality first

Both target identities are exact equalities of classes, with + and no scalar. They are the sign of decision 0009, a step toward the identity of `local-class-product` (chart form), through `local-class-cross-model` (open; depends on `cap-cross-evaluation`, `cross-orientation`, `relative-cross-triad-naturality`). `eq_idShuffle_of_shuffleBarycenter` is a route lemma (an equality of simplices). The proved determinant lemmas are exact.

## 7b. Non-vacuity

The smallest test that would fail if the real form were trivially true or had the wrong sign: `cross_orientation_real 1 1` with upstream's `standardLocalClass_ne_zero_of_pos 2`. For the complex form: `cross_orientation_complex 1 1` with `standardComplexLocalClass_ne_zero 2` through the cast. The real test sits in degree 2 with two shuffle simplices; the complex test sits in real dimension 4 with six. Neither sign-separation lemma is in the tree, and `HodgeLadder.Local.CrossOrientation` imports neither upstream lemma (RT3: `standardLocalClass_ne_zero_of_pos`, `standardComplexLocalClass_ne_zero` and `relativeHomologyMap_complexMatrix_standardComplexLocalClass` are unknown identifiers there). Change C1 adds them in a test module.

## 8. Pin drift

None. The rung is stated against `2ead713`, the pin on `main`, and its dependencies were red-teamed at the same commit. Definitions read at the pin: `standardAffineSimplex`, `standardSingularSimplex`, `standardLocalClass`, `puncturedPair` (`Definitions/.../FundamentalClass.lean`); `complexRealHomeomorph`, `standardComplexRealPairIso`, `standardComplexRealRelativeHomologyIso`, `standardComplexLocalClass` (`Definitions/.../ComplexClass.lean`); `Complex.piBasisOneI`, `Complex.piCoordCLE` (`Lemmas/LinearAlgebra/ComplexOrientation.lean`); Tau Ceti `shuffleChain`, `cone`, `prodCone` in `port/`. For the next pin bump add `Complex.piBasisOneI` to the drift list of `local-class-product`: `complexRealHomeomorph_finProdFinEquiv` unfolds it, so a reordering breaks the build, which is the intended alarm.

## 9. Verdict: pass with changes

C1 (non-vacuity in the tree). Add `HodgeLadder/Tests/CrossOrientation.lean`, importing `HodgeLadder.Local.CrossOrientation`, `HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean` and `HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity` (both built in the shared cache). Text elaborated in RT1, standard axioms:

```lean
/-- Over `ℚ` the local class is not its own negative in positive dimension, so
`cross_orientation_real` separates `+` from `-`. -/
theorem standardLocalClass_ne_neg_of_pos (d : ℕ) (hd : 0 < d) :
    standardLocalClass ℚ d ≠ -standardLocalClass ℚ d := by
  intro e
  have h2 : (2 : ℚ) • standardLocalClass ℚ d = 0 := by rw [two_smul]; nth_rw 2 [e]; simp
  exact standardLocalClass_ne_zero_of_pos _ hd ((smul_eq_zero.1 h2).resolve_left (by norm_num))

/-- The right side of `cross_orientation_complex` is nonzero for every `a, b`. -/
theorem cast_standardComplexLocalClass_ne_zero (a b : ℕ) :
    ((Nat.mul_add 2 a b) ▸ standardComplexLocalClass ℚ (a + b) :
      RelativeHomology ℚ (puncturedPair ℂ (a + b)) (2 * a + 2 * b)) ≠ 0 := by
  have key : ∀ {d d' : ℕ} (h : d = d') (x : RelativeHomology ℚ (puncturedPair ℂ (a + b)) d),
      x ≠ 0 → (h ▸ x : RelativeHomology ℚ (puncturedPair ℂ (a + b)) d') ≠ 0 := by
    intro d d' h x hx; subst h; exact hx
  exact key _ _ (standardComplexLocalClass_ne_zero (a + b))
```

Name both in the ledger entry when the rung is posted (as a test rung or under `nonvacuity-tests`).

C2 (optional, for the consumer). `local-class-cross-model` as recorded reads `orient a b` on `(ℂ^{a+b}, setA ∪ setB)`. The bridge is a corollary of `cross_orientation_complex` by functoriality of `relativeHomologyMap` (the `isoOfSubset (Homeomorph.refl _)` square) and a cast lemma. RT2 elaborates the statement, with the sketch's `setA`, `setB`, `union_eq` and `orient` and this membership lemma (proved in RT2):

```lean
lemma complexAppendMap_mem_union (a b : ℕ) :
    ∀ z ∈ leftProdSet (P := TopCat.of (Fin a → ℂ)) ({0}ᶜ : Set (Fin a → ℂ))
        (TopCat.of (Fin b → ℂ)) ∪
      rightProdSet (TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)),
      complexAppendMap a b z ∈ setA a b ∪ setB a b := by
  rintro z (hz | hz)
  · left
    intro h
    exact hz (funext fun i => (Fin.append_left z.1 z.2 i).symm.trans (congrFun h i))
  · right
    intro h
    exact hz (funext fun j => (Fin.append_right z.1 z.2 j).symm.trans (congrFun h j))

theorem cross_orientation_orient (a b : ℕ) :
    relativeHomologyMap ℚ (2 * a + 2 * b)
      (TopPair.ofSubsetHom (complexAppendMap a b) (complexAppendMap_mem_union a b))
      (relCrossUnion (P := TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
        ({0}ᶜ : Set (Fin a → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)) (2 * a) (2 * b)
        (standardComplexLocalClass ℚ a) (standardComplexLocalClass ℚ b)) =
      orient a b
```

If the consumer is restated on `TopCat.of (Fin a → ℂ) ⊗ TopCat.of (Fin b → ℂ)`, as the ledger note of `local-class-cross-model` suggests, `cross_orientation_complex` is the form it needs and C2 can wait. Either way `setA`, `setB` and `orient` belong in the file that first states a theorem about them. They should not be defined twice.

C3 (records). When the rung is posted, its ledger note should cite this file. It should say that the complex sign is independent of the ℂ-linear identification (upstream `relativeHomologyMap_complexMatrix_standardComplexLocalClass`) and that the real sign rests on two first-factor-first choices (`idShuffle`, `Fin.append`). Add `Complex.piBasisOneI` to the drift list in `docs/sketches/local-class-product.md`, "Pins and drift". Import the module from `HodgeLadder.lean`.

Answers to the prover's questions. (i) Keep the explicit vertex sum in `eq_idShuffle_of_shuffleBarycenter`. `affineSimplexMap_map_apply` turns the realized simplex into exactly that sum, and the explicit form keeps the lemma free of `StdSimplex`. (ii) See C2: the transport to `setA ∪ setB` is a corollary and need not change the stated complex form. (iii) `HodgeLadder/Local/CrossOrientation.lean`, next to `RealAffineOrientation`, is a sound name. Module names do not have to match rung ids.

What I tried that failed to break the statement:

- a −1 from the shuffle sign of the identity simplex: it is +1, by the checked lemma and by re-implementation;
- a −1 from the vertex order or the block order: each one alone would give (−1)^{mn}, and the two choices are aligned;
- a −1 from upstream's reference simplex having sign (−1)^d: it cancels, since both sides use it;
- a −1 from the complex coordinate order: consecutive (Re, Im) gives the identity, and real parts first is not upstream's convention;
- a −1 or 0 hidden in the `▸` casts: transport of a degree index, `rfl` at numerals;
- a trivial proof: none closes;
- other shuffle simplices or degenerate simplices at the barycenter: none reaches it, by proof and by LP for m, n ≤ 3.
