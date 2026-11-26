# Red team: `real-affine-orientation` (statement pass)

Date 2026-11-26. Target: `HodgeLadder/Local/RealAffineOrientation.lean` (namespace `HodgeLadder.RealAffine`, uncommitted, not imported from the root) and the section "real-affine-orientation: statement" of `docs/sketches/local-class-product.md`. Pin: upstream `Paul-Lez/HodgeConjecture` at `2ead713`, the same as `main`.

**Verdict: pass with changes.** Every statement is true as written, exactly signed, and agrees with the literature once upstream's reference simplex is read with its sign (−1)^d. I recomputed every sign independently (section 6). The reference instance of `affineSimplex_homologyπ` (v the vertices of s_d, y = 0) is proved in scratch with the three standard axioms, and the scalar there is 1 with upstream's `standardLocalClass` itself on the right. That proof is the sign pin this rung lacked, so change 1 adds it. Changes 2 and 3 add three lemmas `cross-orientation` needs and the file does not supply. None of the changes weakens a statement.

Scratch work: copies of the file with tests appended, checked with `lake env lean` (about 5 s each), then deleted from the worktree. Named RT1 to RT4 below.

## 1. Is this the statement the literature makes?

The literature fact is that a linear automorphism A of ℝ^d acts on the local homology H_d(ℝ^d, ℝ^d ∖ {0}) by its local degree, which is sign(det A); an affine simplex [v₀, …, v_d] with y in its interior represents the local orientation at y given by the sign of det(v₁ − v₀, …, v_d − v₀) [`Hatcher2002` §2.2 (degree, local degree); section unverified, and the `references.md` row for `Hatcher2002` lists only §3.2, see change 5]. Neither fact has a separate key in `docs/references.md`; both are standard and marked unverified here.

Field by field:

| Field | Literature | Lean | Match |
|---|---|---|---|
| Local class | a generator μ₀ of H_d(ℝ^d, ℝ^d ∖ 0), normally the standard orientation | upstream `standardLocalClass ℚ d`, by definition `homologyπ (standardLocalCycle ℚ d 1)`, the class of the singular simplex t ↦ (t_j − t_d)_j with vertices e₀, …, e_{d−1}, (−1, …, −1) | yes, with the reference sign (−1)^d: o₀ is the standard orientation exactly when d is even |
| Point y | μ_y, the image of μ₀ under translation | `relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) y) (standardLocalClass ℚ d)`, translation x ↦ x + y | yes |
| Linear action | A_* μ₀ = sign(det A) μ₀ | `relativeHomologyMap_realMatrix_standardLocalClass`, A by `mulVec`, any invertible A, coefficient ℚ | yes; the sign is independent of the reference orientation, because A_* is multiplication by a scalar on a rank-one ℚ-module |
| Affine action | F(x) = A x + c sends μ_y to sign(det A) μ_{F(y)} | `relativeHomologyMap_affinePointPairMap` | yes |
| Affine simplex | class of [v₀, …, v_d] at an interior y is sign(det E(v)) relative to the standard orientation | `affineSimplex_homologyπ`: sign(det E(v)) · (−1)^d · o_y, interior given by positive barycentric weights `w` | yes: relative to o_y the sign is sign(det E(v)) / sign(det E(s_d)) = sign(det E(v)) · (−1)^d |

Strength: every A, c, y and every nondegenerate v. Two strengthenings exist and are optional (change 6): coefficients in any commutative ring (upstream's `standardLocalClass` is defined for any `R`), and dropping `hv` from `affineSimplex_homologyπ` (section 3).

## 2. Can the hypotheses be satisfied?

Yes, in every statement, and in Lean for the main one.

- RT1 proves, with standard axioms, that upstream's reference singular simplex is the affine simplex on its own vertices (`affineSingularSimplex (fun k => standardAffineSimplex d (StdSimplex.single k)) = standardSingularSimplex d`), and that the cycle of `affineSimplex_homologyπ` exists at the reference: `z = (standardLocalCycle ℚ d).hom 1` meets `hz` at y = 0. With `zero_mem_openSimplex_standardAffineSimplex` (weights 1/(d + 1)) and `det_edgeMatrix_standardAffineSimplex` (det ≠ 0), every hypothesis of `affineSimplex_homologyπ` is met.
- `relativeHomologyMap_realMatrix_standardLocalClass`: A = 1, or the vertex swap.
- `relativeHomologyMap_affinePointPairMap`: A = 1, c = 0, any y.
- `exists_affineSimplex_openSimplex_cycle`, `exists_affineSimplex_cycle`: the reference simplex.
- The d = 1 sign-visible instance: v = (−1, 1), y = 0, w = (1/2, 1/2); E(v) = (2), so the class is −o₀. The reference order v = (1, −1) has E = (−2) and class +o₀.

## 3. Is anything trivially true?

No. RT2 ran `rfl`, `simp`, `aesop`, `grind`, `decide`, `norm_num`, `trivial` and `simp_all` (each followed by `done`, inside `fail_if_success`) on each of the six open statements: 48 attempts, none closes a goal. A control (`(1 : ℕ) = 1`) confirms that `fail_if_success` reports a success. `exact?` (RT3) finds only the sorry'd declarations themselves (it suggests `relativeHomologyMap_vertexSwap_standardLocalClass n` for the vertex swap), which says nothing about triviality.

Sign visibility. RT1 proves `standardLocalClass ℚ (n + 1) ≠ -standardLocalClass ℚ (n + 1)` from upstream's `standardLocalClass_ne_zero_of_pos`, so the vertex-swap identity has content: if it held for a trivial reason, o would be 2-torsion, and over ℚ it would be zero. RT1 also derives `False` from the unsigned variant (A_* o = o for every invertible A) together with the vertex-swap statement, so the sign in `relativeHomologyMap_realMatrix_standardLocalClass` is load-bearing (this test is conditional on the sorry'd vertex swap).

Hypotheses. No definition unfolds to `True`; there is no `ℕ∞`; d = 0 is a genuine case, true for every statement (det of the empty matrix is 1, the pair is (point, ∅), translation is the identity).

| Hypothesis | Used? |
|---|---|
| `hw`, `hw1` in `affineSimplex_homologyπ` | yes: for y outside the closed simplex σ_v misses y, the chain projects to 0, `z = 0` meets `hz`, and the conclusion would read 0 = ±o_y, false for d > 0 |
| `hv` in the two cycle-existence statements | yes: d = 2, v = (0, 0), (1, 0), (2, 0), y = (1, 0); the face [v₁, v₂] meets the open simplex, so the relative boundary is nonzero |
| `hv` in `affineSimplex_homologyπ` | not needed for truth: for degenerate v the simplex lies in an affine hyperplane H through y, its class comes from H_d(H, H ∖ y) = 0, and sign(0) = 0 (by hand). Keeping `hv` restricts to the case the consumer uses; dropping it would be a stronger statement (change 6) |

## 4. Interface rung?

Not applicable: no structure, no assumed `Prop` input. The route uses upstream's `convexSupportTranslationPairHomotopy`, `TopPair.Homotopy.relativeHomologyMap_apply_eq`, the checked `glpos-path-connected`, and chain-level identities.

## 5. Checker

Not a checked rung. `python3 tools/check.py --no-build` in the worktree: the sorry scan rejects the six `sorry`s (lines 273, 285, 299, 362, 374, 395), as expected at the statement stage; the axioms step failed for an unrelated reason (`HodgeLadder/Tests/ProjectivePlane.olean` is not built in the worktree). In RT1, `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every proved declaration of the file: `det_edgeMatrix_standardAffineSimplex`, `sign_det_edgeMatrix_standardAffineSimplex_mul`, `det_vertexSwapMatrix`, `affineSimplexMap_standardAffineSimplex`, `convex_openSimplex`, `zero_mem_openSimplex_standardAffineSimplex`, `relativeHomologyMap_point_eq_translate`, and for the scratch lemmas of change 1.

## 6. Conventions, with every sign recomputed

| Sign | Recomputation | Value | Agrees |
|---|---|---|---|
| det E(s_d) | exact rational elimination (Python `fractions`), d = 1, …, 8: −2, 3, −4, 5, −6, 7, −8, 9. By hand d = 1: E = (−1 − 1) = −2; d = 2: columns (−1, 1), (−2, −1), det 1 + 2 = 3 | (−1)^d (d + 1) | yes; also the Lean theorem, standard axioms |
| reference scalar sign(det E(s_d)) · (−1)^d | (−1)^d · (−1)^d | 1 | yes; `sign_det_edgeMatrix_standardAffineSimplex_mul`, and RT1 proves the full reference instance |
| Is the (−1)^d tied to upstream? | `standardLocalClass` is by definition the class of `standardSingularSimplex d`, which is `toSSetObjEquiv.symm ⟨standardAffineSimplex d, _⟩`; `standardAffineSimplex d t j = t_{castSucc j} − t_{last}` puts vertex k at e_k (k < d) and (−1, …, −1) (k = d). No separate upstream lemma ties the class to the simplex: the tie is the definition, and RT1's `affineSingularSimplex_standardAffineSimplex` pins it | (−1)^d | yes |
| vertex swap R | column j of R is vertex swap(0 1)(j) of s_d. d = 1: R = (−1). d ≥ 2: the permutation matrix of (0 1), fixing (−1, …, −1). Exact check d = 1, …, 7: det R = −1, R maps vertex k to vertex swap(k), R² = 1 | det R = −1 | yes; `det_vertexSwapMatrix` |
| R_* o₀ | R ∘ s_d = s_d ∘ (0 1) (R is linear and permutes the vertices). ρ on the vertex sequence 0, 1, 0, 2, …, d: face 0 is (1, 0, 2, …, d) = R ∘ s_d, face 2 is s_d, face 1 is (0, 0, 2, …, d) (misses vertex 1), faces k ≥ 3 miss vertex k − 1; the faces other than 0 and 2 lie in proper faces of s_d and miss 0. So ∂ρ ≡ R ∘ s_d + s_d. Faces 0 and 2 carry the same sign under (−1)^i and under (−1)^{i+1}, so the relation does not depend on the face-sign convention. d = 1: ρ = (0, 1, 0), face 1 is the constant at e₀ = 1 ≠ 0 | −o₀ | yes |
| det A > 0 | t ↦ A_t on a path from 1 to A inside {det > 0} is a homotopy of pairs of (ℝ^d, ℝ^d ∖ 0) | + | yes |
| det A < 0 | A = (A R) R, since R² = 1 and det(A R) = −det A > 0; A_* o = (A R)_* (R_* o) = −o | − | yes |
| `mulVec` against `vecMul`, E against Eᵀ | det is transpose-invariant | none | the choice is harmless |
| affine x ↦ A x + c | F ∘ T_y = T_{Ay+c} ∘ A as maps of pairs (A(x + y) + c = A x + (A y + c)), so F_* o_y = T_{Ay+c,*} (A_* o) exactly, with no homotopy | sign(det A) | yes |
| affine simplex around y | M = E(v) E(s_d)⁻¹, c = v₀ − M s₀: F(s_{i+1}) − F(s₀) = M E(s_d) e_i = E(v) e_i, so F ∘ s_d = σ_v. p = F⁻¹(y) = ∑ wᵢ sᵢ lies with 0 in the convex open reference simplex; the move lemma gives the class o_p at p; F_* o_p = sign(det M) o_y and sign(det M) = sign(det E(v)) · sign(det E(s_d)) | sign(det E(v)) · (−1)^d | yes |
| d = 1 checks | v = (−1, 1): E = (2), scalar (+1)(−1) = −1; v = (1, −1): E = (−2), scalar (−1)(−1) = +1. Independently through ∂ : H₁(ℝ, ℝ ∖ 0) → H̃₀(ℝ ∖ 0): ∂(s₁) = [−1] − [1] and ∂(−1, 1) = [1] − [−1] = −∂(s₁) | as stated | yes |
| m = n = 1 (the `cross-orientation` reading) | `idShuffle` has vertex i at (min(i, m), i − m) (all first-factor steps first; `HodgeLadder/Relative/CrossChain.lean` on `main`). For s₁ × s₁ with `Fin.append`: vertices (1, 1), (−1, 1), (−1, −1); columns (−2, 0), (−2, −2); det 4 = (−2)(−2); scalar sign(4) · (−1)² = 1 | + | yes |
| block determinant, general m, n | E(σ_id) is block upper triangular [[E(a), (a_m − a₀) 1ᵀ], [0, E(b)]]; exact check 1 ≤ m, n ≤ 4: det E(σ_id) = det E(s_m) det E(s_n) in all 16 cases, and the class scalar is 1 in all 16. With the other order (second factor first) the determinant would carry (−1)^{mn} | + | yes |
| `SignType` to ℚ | `SignType.cast`: −1, 0, 1 | none | yes |

Truth dependence: every statement here is an identity, so each convention in the table (vertex order of s_d, column order of E, direction of the translation, the barycentric parametrization t ↦ ∑ tᵢ vᵢ with vertex i at `StdSimplex.single i`) matters; the transpose and `mulVec`/`vecMul` choices do not. The register row "Real local orientation and affine maps" is added to `docs/conventions.md` (status stated), and the row "Real determinant and the topology of real matrices" now points to it.

Borrowed inputs and their conventions: `convexSupportTranslationPairHomotopy` (restriction to y is homotopic to restriction to 0 followed by x ↦ x + y; read from source, same translation direction as `translationPointComplementPairMap`); `glpos-path-connected` (a path from 1 to A, the direction `complexMatrixPuncturedPairHomotopy` uses: a homotopy from `𝟙` to the matrix map); upstream's `relativeHomologyMap_complexMatrix_standardComplexLocalClass` is the complex analogue, sign +, consistent because a complex matrix has real determinant |det|² > 0.

## 7. Equality first

Each statement is an identity in H_d with an exact scalar (±1 as `SignType.sign`), with the sign in the docstring and in the register row. Nothing is stated up to a scalar. The (−1)^d is upstream's reference sign and is fixed by the reference instance (change 1).

## 7b. Non-vacuity test

Smallest test that fails if `affineSimplex_homologyπ` had the wrong reference sign or were trivially true: its reference instance, which RT1 proves with standard axioms (change 1, `affineSimplex_homologyπ_standard`). It reads upstream's `standardLocalClass`, `standardLocalCycle`, `standardLocalCycle_inclusion`, `standardSingularSimplex`, `standardAffineSimplex`, `translationPointComplementPairMap`, `relativeChainProjection`, `relativeChainFunctor`. With `standardLocalClass_ne_zero_of_pos` it would fail for the scalar −1. The smallest sign-visible test of the open part is the d = 1 instance v = (−1, 1) (class −o₀); it needs the vertex-swap lemma and does not exist yet. Neither test is in the tree.

## 8. Pin drift

Same pin: `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are identical between the branch base `1cf5060` and `main` (`4a98067`); upstream `2ead713`. Upstream declarations used, all read at `2ead713`: `standardAffineSimplex`, `standardSingularSimplex`, `standardLocalCycle`, `standardLocalClass` (`HodgeConjecture`), `standardLocalCycle_inclusion`, `standardLocalClass_ne_zero_of_pos`, `puncturedPair`, `relativeHomologyMap`, `relativeChainProjection`, `supportInclusionPairMap`, `TopPair.ofSubsetHom`, and `translationPointComplementPairMap`, `convexSupportTranslationPairHomotopy` from library `Other` (not under upstream's statement-import guard). A change of vertex order or of translation direction upstream would change these statements' truth; change 1's `affineSingularSimplex_standardAffineSimplex` and `translationPointComplementPairMap_zero` break the build if it happens.

The branch base predates `relative-cross-chain`, so `HodgeLadder/Relative/CrossChain.lean` is absent from the worktree. RT1 checks the type fit by hand: the chain `((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ) (affineSingularSimplex v)).hom 1` elaborates as an element of `(SingularChainComplex ℚ (TopCat.of (Fin d → ℝ))).X d`, the type of `x` in `relCrossUnion_homologyπ`, and its projection to `TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) A` typechecks; `pointPair d 0 = puncturedPair ℝ d` is `rfl`. So the cycle form of `exists_affineSimplex_openSimplex_cycle` is the `hx` form of `relCrossUnion_homologyπ` with `A = (openSimplex v)ᶜ`.

## Findings on fit with `cross-orientation`

1. The point 0 is outside the open identity-shuffle simplex of s_m × s_n for m, n ≥ 1: writing the product barycenter in the vertices of σ_id gives weight 1/(n + 1) − m/(m + 1) ≤ 0 on the vertex (m, 0). So the consumer computes at y ≠ 0 and must cancel the translation T_y to return to 0. The file has no lemma for that (change 2).
2. The consumer needs the restriction of the open-simplex class of s_d to 0 to be `standardLocalClass ℚ d` (to identify the cross product of the two open-simplex classes, restricted to 0, with the cross product of the two `standardLocalClass`es). Route step (e) proves the general restriction internally; state it (change 3).
3. Everything else in the sketch's reading holds: the open prism is convex (`convex_openSimplex`, product of convex sets) and contains 0; `relativeHomologyMap_point_eq_translate` has the right shape for a class of (ℝ^{m+n}, ℝ^{m+n} ∖ U); the identity shuffle has coefficient +1 (`shuffleChain_idShuffle_coeff`); the other shuffle simplices meet σ_id in common faces and miss its open simplex.

## 9. Verdict: pass with changes

1. **Add the reference pins and the reference instance (proved in RT1, standard axioms).** The four blocks below compile appended to the file as it stands (checked after writing this record); `standardLocalCycle_inclusion` comes from `HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClass`, imported transitively through `Other.AlgebraicTopology.LocalHomology.EuclideanNeighborhoodOrientation`. Import it directly when narrowing imports.

```lean
/-- Upstream's reference singular simplex is the affine simplex on its own vertices. -/
theorem affineSingularSimplex_standardAffineSimplex (d : ℕ) :
    affineSingularSimplex (fun k => standardAffineSimplex d (StdSimplex.single k)) =
      standardSingularSimplex d := by
  unfold affineSingularSimplex standardSingularSimplex
  congr 1
  ext t j
  exact congrFun (congrFun (affineSimplexMap_standardAffineSimplex d) t) j

/-- Translation by `0` is the identity map of pairs. -/
theorem translationPointComplementPairMap_zero (d : ℕ) :
    translationPointComplementPairMap (Fin d → ℝ) 0 = 𝟙 (puncturedPair ℝ d) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x; exact Subtype.ext (add_zero (x.1 : Fin d → ℝ))
  · ext x; exact add_zero (M := Fin d → ℝ) x

/-- The reference cycle: `affineSimplex_homologyπ`'s hypotheses hold at the reference simplex. -/
theorem exists_affineSimplex_cycle_standard (d : ℕ) :
    ∃ z : ((relativeChainFunctor ℚ).obj (pointPair d 0)).cycles d,
      (((relativeChainFunctor ℚ).obj (pointPair d 0)).iCycles d).hom z =
        ((relativeChainProjection ℚ (pointPair d 0)).f d).hom
          (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
            (affineSingularSimplex fun k => standardAffineSimplex d (StdSimplex.single k))).hom
              (1 : ℚ)) := by
  refine ⟨(standardLocalCycle ℚ d).hom 1, ?_⟩
  have h := congrArg (fun f => f.hom (1 : ℚ)) (standardLocalCycle_inclusion ℚ d)
  rw [affineSingularSimplex_standardAffineSimplex]
  exact h

/-- **The sign pin.** `affineSimplex_homologyπ` at the reference simplex and `y = 0`: scalar `1`,
class `standardLocalClass ℚ d` itself. -/
theorem affineSimplex_homologyπ_standard (d : ℕ)
    (z : ((relativeChainFunctor ℚ).obj (pointPair d 0)).cycles d)
    (hz : (((relativeChainFunctor ℚ).obj (pointPair d 0)).iCycles d).hom z =
      ((relativeChainProjection ℚ (pointPair d 0)).f d).hom
        (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
          (affineSingularSimplex fun k => standardAffineSimplex d (StdSimplex.single k))).hom
            (1 : ℚ))) :
    (((relativeChainFunctor ℚ).obj (pointPair d 0)).homologyπ d).hom z =
      ((SignType.sign (edgeMatrix fun k => standardAffineSimplex d (StdSimplex.single k)).det : ℚ)
          * (-1) ^ d) •
        relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) 0)
          (standardLocalClass ℚ d) := by
  rw [sign_det_edgeMatrix_standardAffineSimplex_mul, one_smul, translationPointComplementPairMap_zero,
    relativeHomologyMap, CategoryTheory.Functor.map_id]
  have hinj : Function.Injective
      (((relativeChainFunctor ℚ).obj (pointPair d 0)).iCycles d).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hzz : z = (standardLocalCycle ℚ d).hom 1 := by
    have h := congrArg (fun f => f.hom (1 : ℚ)) (standardLocalCycle_inclusion ℚ d)
    rw [affineSingularSimplex_standardAffineSimplex] at hz
    exact hinj (hz.trans h.symm)
  subst hzz
  rfl
```

2. **Add the cancellation of translation** (stated in RT4; proof: translation by −y is an inverse map of pairs, or the composite with `affinePointPairMap 1 _ (-y) y` after a cast of `1 *ᵥ y + -y = 0`):

```lean
/-- Translation by `y` is injective on relative homology. -/
theorem relativeHomologyMap_translation_injective {d : ℕ} (n : ℕ) (y : Fin d → ℝ) :
    Function.Injective
      (relativeHomologyMap ℚ n (translationPointComplementPairMap (Fin d → ℝ) y))
```

3. **Add the restriction of the open-simplex class** (stated in RT4, with its reference case at 0 derived from it there in five lines, using change 1 and the proved scalar lemma):

```lean
theorem affineSimplex_openSimplex_restrict {d : ℕ} (v : Fin (d + 1) → Fin d → ℝ)
    (hv : (edgeMatrix v).det ≠ 0) (y : Fin d → ℝ) (hy : y ∈ openSimplex v)
    (z : ((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).cycles d)
    (hz : (((relativeChainFunctor ℚ).obj
          (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).iCycles d).hom z =
        ((relativeChainProjection ℚ
            (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).f d).hom
          (((TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))).ιChainComplex (R := ModuleCat.of ℚ ℚ)
            (affineSingularSimplex v)).hom (1 : ℚ))) :
    relativeHomologyMap ℚ d
        (supportInclusionPairMap (TopCat.of (Fin d → ℝ)) (Set.singleton_subset_iff.mpr hy))
        ((((relativeChainFunctor ℚ).obj
          (TopPair.ofSubset (X := TopCat.of (Fin d → ℝ)) (openSimplex v)ᶜ)).homologyπ d).hom z) =
      ((SignType.sign (edgeMatrix v).det : ℚ) * (-1) ^ d) •
        relativeHomologyMap ℚ d (translationPointComplementPairMap (Fin d → ℝ) y)
          (standardLocalClass ℚ d)
```

   It follows from `affineSimplex_homologyπ` by the chain-level restriction (`relativeChainProjection_supportInclusion`, `iCycles` mono), as upstream's `standardOrientationBallCycle_restrict_zero` does for the ball. Add its reference corollary `openSimplex_standard_restrict_zero` (class `standardLocalClass ℚ d` at 0) next to it.

4. **Rebase on `main` before the proofs**, so `relCrossUnion_homologyπ` is in scope, and record in the sketch an elaborated fit check: `exists_affineSimplex_openSimplex_cycle` for s_m and s_n feeding `hx`, `hy` of `relCrossUnion_homologyπ`.

5. **Records.** In `docs/references.md`, extend the `Hatcher2002` row with "§2.2 (degree, local degree; unverified)". In the sketch's "Sources" line, replace "The determinant (−1)^d (d + 1) and the block determinant are hand computations, unverified in Lean" by: the determinant is checked in Lean (`det_edgeMatrix_standardAffineSimplex`); the block determinant is a hand computation with an exact check for 1 ≤ m, n ≤ 4 (this red team), to be checked in `cross-orientation`. Ledger (when posting): module `HodgeLadder.Local.RealAffineOrientation`, declarations including those of changes 1 to 3; the register row is added (status stated, to become checked with the rung).

6. **Optional strengthenings, as new rungs or in place before posting:** coefficients in any commutative ring `R` with the sign cast to `R` (the route is ring-independent); `affineSimplex_homologyπ` without `hv` (both sides 0 when det E(v) = 0, by hand). Neither is needed by `cross-orientation`.

## What I tried that failed

- `congr 2` on the two `toSSetObjEquiv.symm` terms left a heterogeneous goal; `congr 1` with `ext t j` works.
- `ext x; exact add_zero (x : Fin d → ℝ)` for the translation by 0: the type ascription did not coerce the `TopCat` carrier, so `AddZeroClass` failed to synthesize; `add_zero (M := Fin d → ℝ) x` works.
- `HomologicalComplex.moduleCat_iCycles_injective` is a Tau Ceti port lemma, absent from this file's imports; `ModuleCat.mono_iff_injective` with the `Mono` instance of `iCycles` replaces it.
- Unfolding `relativeHomologyMap` and rewriting `Functor.map_id` inside a hypothesis rewrote the first occurrence (the restriction map); a separate `relativeHomologyMap ℚ d (𝟙 _) = LinearMap.id` by `simp` works.
- An independent homological check of (−1)^d beyond d = 1 (through iterated connecting maps) was not attempted; the sign in general rests on the determinant computation and the local-degree theorem, both recomputed above.
