# Red team: `cap-cross-evaluation` (statement pass)

Date 2026-11-26. Target: `HodgeLadder/Cup/CapCrossEvaluation.lean` (namespace `HodgeLadder.CapCross`, uncommitted, not imported from the root) and the section "cap-cross-evaluation: statement" of `docs/sketches/local-class-product.md`, on branch `track/cap-cross-evaluation` from `c486870`. Pin: upstream `Paul-Lez/HodgeConjecture` at `2ead713`, the same as `main` and as the red teams of `relative-cross-chain` and `cross-orientation`.

**The sign is +, in every degree, odd m and n included.** I recomputed the chain-level identity independently, by exact rational linear algebra on unnormalized simplicial chains, degenerate simplices included. Over 193,680 instances there were no failures. In 8,150 of them a non-identity shuffle term is nonzero by itself, so the cancellation the docstring describes is actually exercised. In 2 instances m·n is odd and the right side is nonzero, so a Koszul (−1)^{mn} is excluded. Dropping the cocycle hypotheses breaks the identity in 41 of 50 random trials, and dropping the relative-cycle hypotheses in 18 of 90. The hypotheses carry weight.

**Verdict: pass with changes.** The three statements are the literature's identity, at full strength and exactly signed, in the conventions upstream fixes. None of them is trivially provable. The consumer check goes through. The changes add two non-vacuity lemmas that compiled verbatim in scratch, records, and a restatement of the consumer rung `local-class-cross-model` in product form. None weakens a statement.

Scratch work: copies of the rung file in the worktree, extended with test declarations and checked with `lake env lean`, then deleted. The rung module has no `.olean` in this worktree, so a file that imports it does not elaborate; the copies inline it. RT1 ran the consumer check, the `hExc` proof-irrelevance check, satisfiability, the `puncturedPair` defeq, `#print axioms` and trivial tactics on the triad form. RT2 ran the real m = n = 1 instance and trivial tactics on the cocycle form. RT3 checked the proposed test lemmas of change C1 verbatim. Python (exact `fractions`, own row reduction) ran in the session scratchpad, outside the repository.

## 1. Is this the statement the literature makes?

Literature. For pairs (P, A), (Q, B), with p₁, p₂ the projections of P × Q, the cohomology cross product is φ × ψ = p₁*φ ⌣ p₂*ψ. The cap is σ ⌢ φ = φ(σ|[v₀, …, v_k]) σ|[v_k, …, v_{k+l}], adjoint to the cup: ψ(σ ⌢ φ) = (φ ⌣ ψ)(σ) [`Hatcher2002` §3.3, p. 249, unverified page]. The relative cap H_n(X, A ∪ B) × H^k(X, A) → H_{n−k}(X, B) needs A, B open [`Hatcher2002` §3.3]. The cross product is dual to the homology cross product: ⟨φ × ψ, x × y⟩ = ⟨φ, x⟩⟨ψ, y⟩ [`Hatcher2002` §3.B; `Bredon1993` ch. VI; unverified]. Read through the adjunction, this is the rung's identity ⟨p₂*ψ, p₁*φ ⌢ (x × y)⟩ = ⟨φ, x⟩⟨ψ, y⟩. Authors who evaluate a tensor of cochains on a tensor of chains with the Koszul rule get (−1)^{|ψ||x|} = (−1)^{nm} instead [`Dold1972`, section unverified].

| Field | Literature | Lean | Match |
|---|---|---|---|
| Cap, chain level | front k-face evaluated, back face kept, no sign (Hatcher writes σ ⌢ φ) | upstream `Simplicial.capHom`: `φ (chainOfSimplex (frontFace X x)) • chainOfSimplex (backFace X x)`, front = vertices 0, …, p (`frontInclusion`: i ↦ i), back = p, …, p + q (`backInclusion`: i ↦ p + i); pinned by `rfl` (`capHom_pin`, `frontFace_pin`, `backFace_pin`) | yes. The cochain is written on the left, the formula is Hatcher's |
| Cap, relative and triad | relative cochain on (X, A), chain modulo A and B, result modulo B | `relativeCapLift` = `Simplicial.cap` of the cochain pulled back along the relative projection; `triadCapLiftHom` = that, then the projection to C(X, B); `triadCapHom` descends it to C(X)/(C(A) + C(B)) (pins `relativeCapLift_pin`, `triadCapLiftHom_pin`) | yes |
| Cap, homology | the map induced on cycles | `triadCapCohomologyLinear` through `triadCapShortComplexHom`, whose middle term is `triadCapHom` (upstream `triadCapShortComplexHom_τ₂`); the (−1)^p of `triadCapShortComplexHomSucc` sits on τ₁ and τ₃ only, where it makes the square commute (∂(φ ⌢ c) = (−1)^p φ ⌢ ∂c for a cocycle φ). Read off on representatives by `triadCap_class_homologyπ` (proved) | yes, no sign on homology |
| Union cap | H^p(X, A) × H_{p+q}(X, A ∪ B) → H_q(X, B), A and B open | `unionRelativeTriadCapCohomologyLinear` = the sum-relative cap after the inverse of `isoOfQuasiIsoAt` of the excision comparison (`unionRelativeTriadCap_pin`, `rfl`); `hExc` is the quasi-isomorphism, a `Prop` | yes. The union form is upstream's customary cap; `hExc` is a hypothesis exactly where openness enters the literature |
| Pullbacks | p₁*φ, p₂*ψ | `relativeCohomologyMap ℚ m (prFstPair A Q)`, `relativeCohomologyMap ℚ n (prSndPair P B)`; `prFstPair` = `TopPair.ofSubsetHom (fst P Q)`, `prSndPair` = `TopPair.ofSubsetHom (snd P Q)`; on representatives φ ↦ φ ∘ f_* (`relativeCohomologyMap_class`, proved) | yes. φ, on the first factor, is the one capped (front face); ψ, on the second, is paired with the result (back face). This is the order of p₁*φ ⌣ p₂*ψ |
| Cross product | x × y = [EZ(x ⊗ y)], identity shuffle + | `relCross` (triad), `relCrossUnion` = `triadToUnionRelativeHomologyMap ∘ relCross` (checked, `relative-cross-chain`; definitional, used by `rfl` in the proof of `cap_cross_evaluation`) | yes |
| Pairing | ⟨[φ], [x]⟩ = φ(x) | upstream `relativeCohomologyEquivDualHomology` = `linearDualHomologyEquiv`; on representatives `relEval_class` (proved) | yes, plain evaluation, no ε(k) = (−1)^{k(k−1)/2} twist |
| Coefficients, spaces | any ring, any spaces | ℚ, `TopCat.{0}`, arbitrary subsets A, B (triad form), any proof of excision (union form) | sufficient for the ladder. The triad form holds with no openness, which is stronger than the textbook statement |

Full strength. `cap_cross_evaluation` is an exact equality in ℚ for all classes in all degrees. A version over a general field is a different rung and nothing downstream needs it.

**Is the absence of (−1)^{mn} consistent with upstream?** Yes. Every factor that could carry a sign is unsigned at the pin: the cap is Hatcher's, the pairing is plain evaluation, the pullbacks are composition, and the shuffle gives the identity shuffle +1. A Koszul sign enters only through a Koszul evaluation (α ⊗ β)(a ⊗ b) = (−1)^{|β||a|} α(a)β(b) of a tensor of cochains, and no upstream definition involved here uses one. The m = n = 1 case by hand: Tau Ceti's `ιChainComplex_tensorHom_ιChainComplex_shuffle_f_one_one` gives EZ(σ ⊗ τ) = (s₁σ, s₀τ) − (s₀σ, s₁τ). On the first simplex the front 1-face projects to σ and the back 1-face to τ. On the second they are the constant 1-simplices at σ(0) and τ(1). So the left side is φ(σ)ψ(τ) − φ(c_{σ(0)})ψ(c_{τ(1)}). A 1-cocycle vanishes on a constant 1-simplex: δφ(c₂) = φ(c₁) − φ(c₁) + φ(c₁). The left side is therefore +φ(σ)ψ(τ). A Koszul convention would give −φ(σ)ψ(τ) here.

## 2. Can the hypotheses be satisfied?

`cap_cross_evaluation_triad` has none. `cap_cross_evaluation` needs `hExc`: RT1 gives it at A = B = ∅ by `quasiIso_triadToUnion_prod_of_isOpen isOpen_empty isOpen_empty`, and at the consumer's punctured spaces by `isOpen_compl_singleton`. RT1 also shows by `rfl` that two proofs of `hExc` (the rung's helper and upstream's `triadToUnionRelativeChainMap_quasiIso_of_isOpen` with the preimage proofs) give the same instance of the theorem: the statement does not depend on the proof. `cap_cross_evaluation_cocycle`: φ = ψ = 0 with any relative cycles; the nontrivial instances are those of section 6, and representatives of any classes satisfy it (this is how `cap_cross_evaluation_triad` uses it).

## 3. Is anything trivially true?

No.

- RT1: on the triad form, `first | rfl | (simp; done) | (simp [relCross, triadCapCohomologyLinear]; done) | (norm_num; done) | trivial` fails. RT2: on the cocycle form, `first | rfl | (simp; done) | (simp [triadCap, shuffleBilin]; done) | (norm_num; done)` fails. The prover reports `exact?` failing on both. The prover's attempts with `ring` and `simp [relativeCohomologyEquivDualHomology]` also failed.
- No definition unfolds to `True`. The two sides are elements of ℚ, with no `ℕ∞` and no coercion. The index types are nonempty.
- Non-vacuity, value. RT1: on ℂ^a × ℂ^b, with upstream's normalized coclasses and complex orientation classes, the left side of `cap_cross_evaluation` is 1, by `rw [cap_cross_evaluation, normalizedRelativeCoclass_pairing_self, normalizedRelativeCoclass_pairing_self, mul_one]`, for every a, b. So the identity is not 0 = 0.
- Non-vacuity, sign. RT2: on ℝ¹ × ℝ¹ with `standardLocalClass ℚ 1` and its normalized coclass, the left side is 1, by `rw [cap_cross_evaluation, normalizedRelativeCoclass_pairing_self, mul_one]`. Here m·n = 1 is odd. A (−1)^{mn} statement would give −1 ≠ 1 over ℚ, so the rung's statement and its Koszul variant cannot both hold. The degrees of the consumer are even (2a, 2b), where the two agree, so this odd-degree test is the one that separates the two conventions.
- Unused hypotheses. Python, section 6: with arbitrary cochains and chains in bidegree (2, 1), 41 of 50 random trials fail. With cocycles but chains that are not relative cycles, on (Δ², vertex 0) × Δ², 18 of 90 trials fail. `hφ`, `hψ`, `hx`, `hy` are needed.
- `hExc` is used: it is the argument of `unionRelativeTriadCapCohomologyLinear`.

## 4. Interface rung

Not applicable. No structure, no axioms.

## 5. Checker

`python3 tools/check.py --no-build` (with the scratch files removed): `REJECTED (sorry: HodgeLadder/Cup/CapCrossEvaluation.lean:280)`, the one open statement, and nothing else. `#print axioms` (RT1): `relEval_class`, `relativeCohomologyMap_class`, `triadCap_class_homologyπ`, `homologyπ_eq_class`, `quasiIso_triadToUnion_prod_of_isOpen`, `prFstPair` use `propext`, `Classical.choice`, `Quot.sound`. `cap_cross_evaluation_triad` and `cap_cross_evaluation` add `sorryAx` only through `cap_cross_evaluation_cocycle`. The ledger names no declarations yet (status `open`). When the rung is checked, list `prFstPair`, `prSndPair`, `quasiIso_triadToUnion_prod_of_isOpen`, `homologyπ_eq_class`, `relEval_class`, `relativeCohomologyMap_class`, `triadCap_class_homologyπ`, `cap_cross_evaluation_cocycle`, `cap_cross_evaluation_triad`, `cap_cross_evaluation` (namespace `HodgeLadder.CapCross`), and the two test lemmas of C1.

## 6. Conventions, and the cocycle form on unnormalized chains

| Convention | Register row | Where the statement reads it | Truth depends on it? |
|---|---|---|---|
| Cap: front face evaluated, back face kept, no sign | "Cap product", "Triad cap product" | `triadCap`, through `capHom` | yes. With the cochain on the back face, the identity needs the other factor order, and with a sign it fails |
| Homology cap from the middle term | "Triad cap product" | `triadCapCohomologyLinear` | yes; a (−1)^p on τ₂ would give (−1)^m |
| Evaluation, no twist | "Universal-coefficient evaluation" | both sides | yes; ε(k) twists would give ε(m + n) vs ε(m)ε(n) = (−1)^{mn} ε(m + n) |
| Shuffle: identity shuffle +, lattice-path sign (−1)^N | "Shuffle map" | `shuffleBilin` inside `relCross` | yes |
| Tensor differential d(a ⊗ b) = da ⊗ b + (−1)^p a ⊗ db | "Tensor product of chain complexes" | chain-map property of shuffle and AW, used by the proof route | the identity holds for the shuffle map determined by this rule; the computed signs (−1)^N are those of this rule |
| Coefficients ℚ ⊗ ℚ ≅ ℚ by the left unitor | "Relative homology cross product" | `crossChainMap` | yes; 1 ⊗ 1 ↦ 1 |
| Factor order: φ on P (front), ψ on Q (back) | new row "Cap–cross evaluation" (added) | `prFstPair`, `prSndPair` | yes |

Added the row "Cap–cross evaluation" to `docs/conventions.md`.

**Independent computation.** Model: simplicial sets Δ^N, 1 ≤ N ≤ 3, simplices all monotone maps [k] → [N], degenerate ones included (unnormalized chains). Subcomplexes: ∅, a vertex, an edge, the boundary, a horn-like union. The cap is front face times back face; the shuffle sums over lattice paths with sign (−1)^N, N the pairs (vertical step, later horizontal step), as in the register. For each pair of pairs and each bidegree 0 ≤ m ≤ 3, 0 ≤ n ≤ 2, I computed bases of the relative cocycles and of the chains whose boundary lies in the subcomplex, and checked the bilinear identity on all basis quadruples. Results:

- 193,680 instances, 0 failures. 84 have a nonzero right side; 2 of those have m·n odd.
- 8,150 instances have a nonzero single non-identity shuffle term, so the terms cancel in the sum and do not vanish one by one. This confirms the docstring: single terms survive, and the sum vanishes on cocycles and relative cycles.
- Every non-identity lattice path has a vertical step among its first m steps, so it also has a horizontal step among its last n. The first projection of its front m-face and the second projection of its back n-face are then both degenerate, as the docstring says ("φ(degenerate) · ψ(degenerate)").

**The homotopy route (sketch, step 3) is sound.** Mathlib's `Homotopy f g` has `f.f i = dNext i h + prevD i h + g.f i`. So Tau Ceti's `shuffleAlexanderWhitneyHomotopy : Homotopy (shuffle ≫ alexanderWhitney) (𝟙 _)` gives AW ∘ EZ − id = dh + hd exactly, with no sign. Write ε = α ⊗ β on bidegree (m, n), with α = φ ∘ relProj_A and β = ψ ∘ relProj_B. The term ε(d h(x ⊗ y)) vanishes because ε ∘ d = δα ⊗ β ± α ⊗ δβ = 0. For the term ε(h d(x ⊗ y)): d(x ⊗ y) = dx ⊗ y + (−1)^m x ⊗ dy, with dx in the image of C(A) and dy in the image of C(B). `SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality` along `toSSet.map` of A ↪ P (and B ↪ Q) moves h past the inclusion. ε vanishes on the image of C(A)_m ⊗ C(Q)_n because α ∘ i_* = 0, and likewise for B. In degree m + n = 0 the homotopy component of degree −1 is zero. Two details for the prover:

- The file must import `LefschetzPort.TauCeti.AlgebraicTopology.SimplicialSet.EilenbergZilber` and the singular Alexander–Whitney module.
- Upstream's subspace chain map `((chainPairFunctor ℚ).obj (TopPair.ofSubset A)).hom` has to be identified with `SSet.chainComplexMap (toSSet.map ι)` (or the singular-chain functor's map of the inclusion) before the naturality lemma applies. Check this by `rfl` first. If it fails, it is a lemma about upstream's definition and goes in the drift list.

## 7. Equality first

The rung is an identity in ℚ, stated exactly, with no scalar. It is the evaluation step of the equality `local-class-product` (relCup2 of the two normal-projection coclasses = the coclass of Z ∩ W), through `local-class-cross-model` and `triad-relative-cup-cap`. Both are open rungs in the ledger.

## 7b. Non-vacuity

The smallest test lemma that fails if the statement were trivially true, in upstream's API: `capCross_real_one_one` (change C1), the left side at ℝ¹ × ℝ¹ equal to 1, from `normalizedRelativeCoclass_pairing_self` and `standardLocalClass_ne_zero_of_pos`. It is sign-visible because m·n = 1 is odd. The complex product form `capCross_complex_model` gives 1 for every a, b; with even degrees it shows non-vacuity but cannot separate + from (−1)^{mn}. Neither exists yet. Both compiled verbatim in RT3, below the rung's code, with the imports `HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity` and `HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean`.

**Elaboration pitfall (RT1).** Writing the consumer with `prSndPair (TopCat.of (Fin a → ℂ)) ({0}ᶜ : Set (Fin b → ℂ))`, which leaves Q implicit, hits a deterministic timeout at `isDefEq` (200000 heartbeats). Lean has to solve `↑?Q =?= (Fin b → ℂ)`. Naming the spaces by `abbrev` (or `(Q := …)`) and giving `normalizedRelativeCoclass (X := puncturedPair ℂ b)` elaborates at once. This is the same failure the ledger note of `local-class-cross-model` records for `TopPair.ofSubset`.

## 8. Pin drift

The statement was elaborated at the current pin `2ead713`. There is no earlier check, so there is no drift to diff. The rung reads library `Other`, which is outside upstream's statement guard. Drift list for the next pin bump, added to the one in the sketch:

- Upstream `Other/AlgebraicTopology/Singular/Cap/`:
  - `Simplicial.capHom`, `frontFace`, `backFace`, `frontInclusion`, `backInclusion` (pinned here).
  - `relativeCapLift`, `triadCapLiftHom`, `triadCapHom`, `triadCap`, `triadCap_projection_apply`.
  - `triadCapShortComplexHom` (with `Zero`, `Succ`), `triadCapShortComplexHom_τ₂`.
  - `triadCapCohomologyLinear`, `triadCapCohomologyLinear_on_cycle`, `triadCapCochainCohomologyLinear`, `relativeCochainCohomologyEquiv`, `relativeCohomologyCycleToCocycle`.
  - `unionRelativeTriadCapCohomologyLinear` (pinned here), `unionRelativeTriadCapCohomologyLinear_on_comparison`, `triadToUnionRelativeHomologyMap`, and `Excision/Triad.lean` `triadToUnionRelativeChainMap_quasiIso_of_isOpen`.
- Upstream statement library: `relativeCohomologyEquivDualHomology`, `linearDualHomologyEquiv`, `ShortComplex.linearDualHomologyEquiv_class_apply_class`, `linearDualCochainComplexScIso` and its naturality, `relativeCohomologyMap`, `relativeCochainComplexMap`, `relativeCoboundary`, `relativeChainProjection`, `chainPairFunctor`, `TopPair.ofSubsetHom`.
- Tau Ceti in `port/`: `SSet.shuffleAlexanderWhitneyHomotopy`, `SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality`, `TopCat.shuffle_alexanderWhitney`, `TopCat.alexanderWhitney`, `SSet.ιChainComplex_alexanderWhitney_f`.
- Mathlib: the `Homotopy` sign convention (`comm`), `ShortComplex.moduleCatCyclesIso_inv_π`, `moduleCatHomologyClass`.

## Questions of the prover

**(i) Form of `local-class-cross-model`: state it on ℂ^a × ℂ^b.** The product form is `capCross_complex_model` of C1, a three-line corollary of this rung. Then `local-class-cross-model` carries no content of its own: the sign content of decision 0009 sits in `cross_orientation_complex` (checked), and the evaluation sits here. The ℂ^{a+b} form in the ledger, with `setA`, `setB`, `orient`, moves the triad cap along `complexAppendMap`. Upstream's `Cap/Naturality.lean` has absolute and relative cap naturality (`capHomologyMap_naturality`, `relativeCapHomologyMap_naturality`) and nothing for triads. So that form needs a new triad-cap naturality rung on top of `relative-cross-triad-naturality`. The downstream does not need it:

- The chart form of `local-class-product` already splits the normal coordinates as `(Fin a → ℂ) × (Fin b → ℂ)`.
- `triad-relative-cup-naturality` along the normal projections lands on the product triad (P × Q; A × Q, P × B).
- The passage to ℂ^{a+b}, where `chartNormalProjectionCoclass` for Z ∩ W lives, can then be made on the single pair (P × Q, A × Q ∪ P × B) ≅ (ℂ^{a+b}, ℂ^{a+b} ∖ 0). On that pair upstream's functoriality of `relativeCohomologyMap` and the naturality of the pairing suffice: `cross_orientation_complex` sends s_a × s_b to the orientation class, and the pullback of a normalized coclass along an isomorphism of pairs is the normalized coclass of the preimage class, a short lemma.

Recommendation (C4): record `local-class-cross-model` with the statement of `capCross_complex_model`, drop `relative-cross-triad-naturality` from its `depends_on` (that rung stays useful elsewhere), and add the iso-pullback lemma for `normalizedRelativeCoclass` to the route of `local-class-product`. This changes an open, unattempted rung's statement to a different one and weakens nothing that is checked. The maintainer may prefer to keep the ℂ^{a+b} form as a separate optional rung.

**(ii) The representative lemmas belong in `docs/gaps.md` "General lemmas kept local".** `relEval_class`, `relativeCohomologyMap_class` and `triadCap_class_homologyπ` are statements about upstream's own API, with destination upstream. `homologyπ_eq_class` is about `ShortComplex (ModuleCat R)` and its destination is Mathlib; search Mathlib for an existing form before filing it (C3).

**(iii) File name.** `HodgeLadder/Cup/CapCrossEvaluation.lean` with namespace `HodgeLadder.CapCross` is consistent with `Cup/TriadCupCap.lean` and `Local/CrossOrientation.lean`. No objection.

## 9. Verdict: pass with changes

| Change | What |
|---|---|
| C1 | Add the two test lemmas below (in the rung file or `HodgeLadder/Tests/CapCross.lean`) and name them in the ledger, or in a test rung `cap-cross-evaluation-test` |
| C2 | When `triad-relative-cup-cap` lands, replace the six private pins with `HodgeLadder.Cup.TriadCapPins`: `capHom_pin` ↦ `capHom_eq`; `frontFace_pin` ↦ `frontFace_eq`, `frontInclusion_val`; `backFace_pin` ↦ `backFace_eq`, `backInclusion_val`; `relativeCapLift_pin` ↦ `relativeCapLift_eq`; `triadCapLiftHom_pin` ↦ `triadCapLiftHom_eq`; `unionRelativeTriadCap_pin` ↦ `unionRelativeTriadCapCohomologyLinear_apply_eq` with `relativeCochainCohomologyEquiv_symm_eq` (that pin spells the cohomology identification as `homologyMap (linearDualCochainComplexScIso _ p).hom` where this file has `relativeCochainCohomologyEquiv.symm`). Not blocking |
| C3 | `docs/gaps.md` "General lemmas kept local": rows for `relEval_class`, `relativeCohomologyMap_class`, `triadCap_class_homologyπ` (to upstream) and `homologyπ_eq_class` (to Mathlib) |
| C4 | Ledger: restate `local-class-cross-model` in product form as in question (i), drop `relative-cross-triad-naturality` from its `depends_on`, and add the spelling pitfall of section 7b to its note; on `cap-cross-evaluation`, add the declarations of section 5 when checked and the Tau Ceti Eilenberg–Zilber imports to the note |
| C5 | Register row "Cap–cross evaluation" (done in this pass) |

C1, exact Lean (RT3, compiled verbatim after the rung's code; imports `HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity`, `HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean`):

```lean
namespace HodgeLadder.Tests

open CategoryTheory MonoidalCategory AlgebraicTopology.Singular HodgeLadder.Relative
  HodgeLadder.CapCross

/-- `ℂ^a` as an object of `TopCat`. -/
abbrev capCrossCx (a : ℕ) : TopCat.{0} := TopCat.of (Fin a → ℂ)

/-- `ℂ^a ∖ {0}`. -/
abbrev capCrossCxPunct (a : ℕ) : Set (capCrossCx a) := ({0}ᶜ : Set (Fin a → ℂ))

/-- `ℝ^d` as an object of `TopCat`. -/
abbrev capCrossRe (d : ℕ) : TopCat.{0} := TopCat.of (Fin d → ℝ)

/-- `ℝ^d ∖ {0}`. -/
abbrev capCrossRePunct (d : ℕ) : Set (capCrossRe d) := ({0}ᶜ : Set (Fin d → ℝ))

/-- Sign-visible instance of `cap_cross_evaluation` in odd degrees `m = n = 1`: the left side is
`1`, where a Koszul sign `(-1)^{mn}` would give `-1`. -/
theorem capCross_real_one_one :
    relativeCohomologyEquivDualHomology ℚ
        (TopPair.ofSubset (X := capCrossRe 1 ⊗ capCrossRe 1)
          (rightProdSet (capCrossRe 1) (capCrossRePunct 1))) 1
      (relativeCohomologyMap ℚ 1 (prSndPair (capCrossRe 1) (capCrossRePunct 1))
        (normalizedRelativeCoclass (X := puncturedPair ℝ 1) (standardLocalClass ℚ 1)
          (standardLocalClass_ne_zero_of_pos 1 one_pos)))
      (unionRelativeTriadCapCohomologyLinear ℚ (capCrossRe 1 ⊗ capCrossRe 1)
        (leftProdSet (capCrossRePunct 1) (capCrossRe 1))
        (rightProdSet (capCrossRe 1) (capCrossRePunct 1)) 1 1
        (quasiIso_triadToUnion_prod_of_isOpen (A := capCrossRePunct 1) (B := capCrossRePunct 1)
          isOpen_compl_singleton isOpen_compl_singleton)
        (relativeCohomologyMap ℚ 1 (prFstPair (capCrossRePunct 1) (capCrossRe 1))
          (normalizedRelativeCoclass (X := puncturedPair ℝ 1) (standardLocalClass ℚ 1)
            (standardLocalClass_ne_zero_of_pos 1 one_pos)))
        (relCrossUnion (capCrossRePunct 1) (capCrossRePunct 1) 1 1
          (standardLocalClass ℚ 1) (standardLocalClass ℚ 1))) = 1 := by
  rw [cap_cross_evaluation, normalizedRelativeCoclass_pairing_self, mul_one]

/-- The product form of `local-class-cross-model`: on `ℂ^a × ℂ^b`, the triad cap of the pulled-back
normalized local class of `ℂ^a` with the cross product of the complex orientation classes, paired
with the pulled-back normalized local class of `ℂ^b`, is `1`, for every `a`, `b`. -/
theorem capCross_complex_model (a b : ℕ) :
    relativeCohomologyEquivDualHomology ℚ
        (TopPair.ofSubset (X := capCrossCx a ⊗ capCrossCx b)
          (rightProdSet (capCrossCx a) (capCrossCxPunct b))) (2 * b)
      (relativeCohomologyMap ℚ (2 * b) (prSndPair (capCrossCx a) (capCrossCxPunct b))
        (normalizedRelativeCoclass (X := puncturedPair ℂ b) (standardComplexLocalClass ℚ b)
          (standardComplexLocalClass_ne_zero b)))
      (unionRelativeTriadCapCohomologyLinear ℚ (capCrossCx a ⊗ capCrossCx b)
        (leftProdSet (capCrossCxPunct a) (capCrossCx b))
        (rightProdSet (capCrossCx a) (capCrossCxPunct b)) (2 * a) (2 * b)
        (quasiIso_triadToUnion_prod_of_isOpen (A := capCrossCxPunct a) (B := capCrossCxPunct b)
          isOpen_compl_singleton isOpen_compl_singleton)
        (relativeCohomologyMap ℚ (2 * a) (prFstPair (capCrossCxPunct a) (capCrossCx b))
          (normalizedRelativeCoclass (X := puncturedPair ℂ a) (standardComplexLocalClass ℚ a)
            (standardComplexLocalClass_ne_zero a)))
        (relCrossUnion (capCrossCxPunct a) (capCrossCxPunct b) (2 * a) (2 * b)
          (standardComplexLocalClass ℚ a) (standardComplexLocalClass ℚ b))) = 1 := by
  rw [cap_cross_evaluation, normalizedRelativeCoclass_pairing_self,
    normalizedRelativeCoclass_pairing_self, mul_one]

end HodgeLadder.Tests
```

The proofs are `rw` chains through the open `cap_cross_evaluation`, so they check with the standard axioms once the cocycle form is proved. In the real lemma one `rw` with `normalizedRelativeCoclass_pairing_self` rewrites both factors, since they are the same instance; a second one fails.

**What failed on the way.** The consumer check with Q left implicit timed out (section 7b). A scratch file importing `HodgeLadder.Cup.CapCrossEvaluation` failed for lack of its `.olean`; inlining the module works. I did not try a Lean proof of the cocycle form; the Python computation and the homotopy argument above are the evidence that it is true.
