# Red team: `local-class-product` and `cycle-class-multiplicative` (plan)

Date: 2026-11-26. Branch `track/cycle-mult` at `a293d22` (parent `b8c7b29`; `main` has since moved to `1f13d86`). Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Targets: `docs/sketches/local-class-product.md`, `docs/sketches/cycle-class-multiplicative.md`, the 17 new rungs and 3 rewired rungs in `ledger/ladder.json` (`git diff b8c7b29 a293d22`), decisions 0008 and 0009.

Read: both sketches, decisions 0008 and 0009, `docs/conventions.md`, `docs/references.md`, the red-team verdict on the supported comparison, the general-V worktree (uncommitted: `SupportedOpen*.lean`, sketch section "The comparison on a general open"), and at the pin: `Cycle/FundamentalClass.lean`, `LocalHomology/ComplexClass.lean`, `LocalHomology/FundamentalClass.lean` (`standardLocalClass`), `LinearAlgebra/ComplexOrientation.lean` (`piCoordCLE`), `LocalHomology/NormalProjectionCoclass.lean`, `NormalProjectionOverlap.lean`, `Cycle/Local/Purity.lean`, `Singular/Cohomology.lean`, `Algebra/Homology/LinearDual*.lean`, `SmoothPair/CoclassSection.lean`, `SmoothSupportPurity.lean`, `SingularClosedFiltration.lean`, `ComplexPoint/Manifold.lean`, and in `Other`: `Singular/Cap/{Simplicial,Relative,Triad}.lean`, `Singular/Excision/Triad.lean`, `Cohomology/SupportSheafNormalization.lean`, `Cycle/FundamentalClass.lean`, `Cycle/Component/PointClassNormalization.lean`, `Hodge/CodimensionZero*.lean`; Tau Ceti's `SimplicialSet/Shuffle.lean` in `port/`.

Scratch (all inside the worktree, deleted afterwards): S1 elaborates the general theorem and `fundamental-class-unit` and tries trivial proofs; S2 checks the degree unification in `ht`; S3 compiles copies of the four unbuilt upstream `Other` files (renamed modules, about 70 seconds in total) and elaborates the cap model with explicit helper definitions; S4 checks the real coordinate order of `complexRealHomeomorph`; S5 discharges the hypotheses of the general theorem at a = b = 0. A Python script checked the determinants and the shuffle orientations.

**Verdict: pass with changes.** The singular-side route is sound, and every complete route to the rung needs it or an equivalent: the general-V product formula multiplies a supported class by an absolute class, so its products stay supported on one factor's support, and the rung needs a class supported on Z ∩ W. The expected sign + holds for every a and b. It rests on four conventions, each read from source and checked by hand or in scratch: consecutive (Re, Im) coordinates, the reference simplex, Tau Ceti's shuffle sign, and the unsigned cap and evaluation. The changes below fix gaps in the test instances, rung sizes, and the record. None of them weakens a statement.

## 1. Is this the statement the literature makes?

Literature: for X nonsingular the cycle map A^*(X) → H^{2*}(X) is a ring homomorphism, and a transversal intersection of Z and W along an integral T has multiplicity one, so [Z] · [W] = [T] [`Fulton1998` Cor. 19.2 and §8.2; numbering unverified]. The relative cup H^k(X, A) × H^l(X, B) → H^{k+l}(X, A ∪ B) for open A, B: [`Hatcher2002` §3.2].

| Literature | Lean (elaborated in S1) | Source |
|---|---|---|
| X smooth projective integral of dimension d | `X : Over (Spec ↧ℂ)`, `IsIntegral`, `Smooth`, `IsProjective`, `SmoothOfRelativeDimension d` | upstream |
| Z, W, T integral, codimensions a, b, a + b | scheme points `x w t`, `Order.coheight _ = ↑a`, `↑b`, `↑a + ↑b` in ℕ∞; S2 shows the class `cycleComponentSheafClass X t ht` unifies at degree p = a + b | upstream |
| T = Z ∩ W as sets | `hT` on `cycleComponentAnalyticClosedSupport` | upstream supports |
| transversal along T | `htr`: at each y ∈ T(ℂ) a chart in Mathlib's `IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω` in which Z is {first a coordinates = 0} and W is {next b = 0} | Mathlib atlas, upstream charted space |
| (implicit) T lies in the smooth loci of Z and W | `hxreg`, `hwreg`: T(ℂ) ⊆ `cycleComponentSmoothSupportAmbientOpen` | upstream |
| [Z] ∪ [W] = [T] | `cup [Z] [W] (2 * (a + b)) _ = [T]`, Yoneda cup of the ladder | local `cup`, upstream classes |

Field by field the statement is the transversal case of the literature with one irreducible component. `hxreg` and `hwreg` add nothing in substance: a reduced variety that is an analytic submanifold near y is algebraically smooth at y. The pin does not have that implication, so stating them is correct. The statement is narrower than the literature in one respect, which it states openly: T is a single integral component of multiplicity one. Decision 0009 names exactly this case.

The model statement of `local-class-cross-model` uses only upstream objects: `normalizedRelativeCoclass`, `standardComplexLocalClass`, `relativeCohomologyMap`, `relativeCohomologyEquivDualHomology`, and the triad cap `unionRelativeTriadCapCohomologyLinear` with excision `triadToUnionRelativeChainMap_quasiIso_of_isOpen` from `Other`. It matches the literature's ⟨pr₁*u_a ⌣ pr₂*u_b, o_{a+b}⟩ = 1 through the unsigned cap φ ⌢ σ = φ(front) · back: ⟨ψ, φ ⌢ σ⟩ = (φ ⌣ ψ)(σ) in Hatcher's convention.

## 2. Can the hypotheses be satisfied?

- **a = b = 0, every X.** S5 proves `hT` and `htr` for x = w = t = the generic point, from upstream's `cycleComponentAnalyticClosedSupport_genericPoint_eq_top`, Mathlib's `IsManifold.chart_mem_maximalAtlas` and `mem_chart_source`. `hxreg` reduces to `y ∉ cycleComponentSingularAnalyticClosedFiltration X (genericPoint X.left) 0`. That is true, because the reduced closure of the generic point is X and X is smooth, but the pin has no lemma for it. Both sides of this instance are nonzero by upstream's `cycleComponentSheafClass_genericPoint_ne_zero`.
- **ℙ¹ × ℙ¹ (decision 0009's case).** The hypotheses hold mathematically. In Lean, beyond what the ledger lists (product, Segre, product homeomorphism), the instance needs:
  1. the product chart in `IsManifold.maximalAtlas`. No upstream file mentions `maximalAtlas` (grep at the pin); its charts `localChart` come from étale coordinates chosen with `Classical.choice`, so analytic compatibility of an algebraic affine chart with them is a separate statement. It is missing even for ℙ¹ (`complInftyHomeomorph` is only a homeomorphism);
  2. `hxreg`, `hwreg`: (∞, ∞) is outside the singular locus of each fibre's reduced closure. This needs the closed subscheme `cycleComponentι` computed on an affine chart. Rung `p1p1-fibres-transversal` does not mention it.

## 3. Is the conclusion trivially true?

No. S1 tried `rfl`, `simp; done`, `Subsingleton.elim` and `subst hT; rfl` on the general theorem, and `rfl`, `simp [one]`, `Subsingleton.elim` on `fundamental-class-unit`; all fail. S3 tried `rfl`, `simp`, `decide` and `norm_num` on the cap model. `simp` rewrites by `relativeCohomologyEquivDualHomology_relativeCohomologyMap` and stops at a genuine evaluation. Every hypothesis is used by the route (`hd` already in the index bounds). The `ℕ∞` coercion in `ht` is harmless: S2 checks that the stated class lives in degree 2(a + b), also when `ht` is written `((a + b : ℕ) : ℕ∞)`. If a + b > d no t exists, and `hd` rules that case out anyway. If Z(ℂ) ∩ W(ℂ) = ∅, `hT` cannot hold, since T(ℂ) is nonempty.

## 4. Interface rung?

Not applicable. No structure, no axioms (decision 0003). `relCup2` is a definition, which is allowed; add it to `docs/gaps.md` "To upstream" when it is defined, as the cup counterpart of upstream's triad cap.

## 5. Checker

`python3 tools/check.py --no-build` on the branch: `ACCEPTED: all checks passed`. The plan adds no declarations. The ledger validates, and the new rungs are `open` with empty declaration lists. In S3 the two `Other` inputs report `[propext, Classical.choice, Quot.sound]`: `triadToUnionRelativeChainMap_quasiIso_of_isOpen` and `unionRelativeTriadCapCohomologyLinear`. A grep of the four files finds no `sorry`, `axiom`, `native_decide` or `unsafe`.

## 6. Conventions

| Convention | Where read | Result | Truth depends on it? |
|---|---|---|---|
| Real coordinates of ℂ^p | `piCoordCLE` = `(basisOneI.smulTower' (Pi.basisFun ℂ _)).reindex finProdFinEquiv` | S4, kernel-checked in scratch: coordinate `finProdFinEquiv (i, 0)` is Re z_i, `(i, 1)` is Im z_i, and `finProdFinEquiv (i, j) = 2i + j`; for p = 2 the vector is (Re z₀, Im z₀, Re z₁, Im z₁). So under `Fin.append` the real coordinates of ℂ^a then ℂ^b are those of ℂ^{a+b} in order. The block identification is the identity, with no (−1)^{ab} | yes, for the sign of `cross-orientation` |
| Reference simplex | `standardLocalClass`: affine simplex e₀, …, e_{d−1}, (−1, …, −1) | edge determinant (−1)^d (d + 1): hand derivation (add the first d − 1 edge columns to the last) and exact rational check for d = 1, …, 7 | yes, through its sign (−1)^d |
| Shuffle map | Tau Ceti `SSet.shuffleChain` (port): lattice path with sign (−1)^N, N = pairs (vertical step, later horizontal step) | the identity shuffle (all horizontal steps first) has sign +; for (m, n) ∈ {(1,1), (2,2), (1,3), (2,3), (3,2)}, every shuffle simplex of s_m × s_n times its sign has the same orientation, sign(s_m) · sign(s_n); the identity-shuffle simplex has the sign of s_{m+n} for all 1 ≤ m, n ≤ 4 | yes |
| Cross product of orientations | sketch, rung `cross-orientation` | s_m × s_n = s_{m+n}, sign +, for every m, n of any parity, since sign(s_m) sign(s_n) = (−1)^{m+n} = sign(s_{m+n}); complex form by the identity block | yes; equality of classes |
| Cap product | `Other/.../Cap/Simplicial.lean` `capHom`: φ(front p-face) • back q-face | unsigned on chains. The triad cap's homology map uses `τ₂ = triadCapHom` with no sign; the factors (−1)^p sit on τ₁ and τ₃ (`triadCapShortComplexHomSucc`) and do not reach homology | yes |
| Evaluation pairing | `relativeCohomologyEquivDualHomology` = `linearDualHomologyEquiv`; `linearDualHomologyEquiv_class_apply_class` | ⟨[φ], [x]⟩ = φ(x), no sign | yes, for `normalizedRelativeCoclass` and every pairing to 1 |
| Singular cup, coboundary | register rows | front times back, δφ = φ ∘ ∂ | yes |
| Yoneda against singular cup | `cup_singular_comparison` | (−1)^{pq}, here (−1)^{(2a)(2b)} = 1 | no in even degrees, by the checked identity |
| Forget the support | `supported_forget_compat` | forgetRel ∘ Φ = Ψ ∘ forgetSupport, no sign | yes; checked |
| Koszul evaluation of tensors | `Dold1972`, unverified | (−1)^{|ψ||x|} = 1 for |x| = 2a | no |

These conventions combine to the sign +. A degree twist ε(n) = (−1)^{n(n−1)/2} in the evaluation would also cancel, since ε(2a) ε(2b) = (−1)^{a+b} = ε(2a + 2b). So the sign does not hinge on that choice either.

One subtlety the sketch records only implicitly: Alexander–Whitney after shuffle is the identity on normalized chains only. Singular chains here are unnormalized, so `cap-cross-evaluation` must use the natural homotopy (`SSet.shuffleAlexanderWhitneyHomotopy`), and its relative form needs that homotopy to preserve C(A) ⊗ C(Q) + C(P) ⊗ C(B). Naturality in each factor gives this; the rung's docstring should say so.

Hand computations that should become Lean lemmas at the start of the rung that uses them:

1. `complexRealHomeomorph (a + b) (Fin.append u v)` equals the cast of `Fin.append (complexRealHomeomorph a u) (complexRealHomeomorph b v)`. S4's general formula gives this in a few lines; put it in `cross-orientation`.
2. The edge determinant of `standardLocalClass`'s simplex is (−1)^d (d + 1); put it in `real-affine-orientation`.
3. The determinant of the identity-shuffle simplex of s_m × s_n is det(s_m) · det(s_n); put it in `cross-orientation`.
4. The identity shuffle has coefficient +1 in Tau Ceti's `shuffleChain`; put it in `relative-cross-chain`.
5. `rfl` pins of `unionRelativeTriadCapCohomologyLinear` (through `triadCapCohomologyLinear` and the excision inverse) and of `capHom`'s formula, added to the pins, since `Other` is unguarded (section 8).

Register: the "Cross product of complex orientations" row is updated with these results. New rows: "Universal-coefficient evaluation", "Shuffle map" and "Triad cap product" (this pass).

## 7. Equality first

Both rungs are identities, exact, with sign + and no scalar. The inclusions in the route (relCup2 lands in H(X, (X ∖ Z) ∪ (X ∖ W)), then the set equality from `hT`) are identifications of the same pair and carry no sign. Section 9, change 9 asks for a proof that they are sign-free.

## 7b. Non-vacuity

- Smallest sign-visible test: `local-class-cross-model` at a = b = 1 (ℂ², six shuffle simplices). It does not exist yet; the statement elaborates (S3).
- Codimension-zero test: `fundamental-class-unit`. Upstream's `cycleComponentSheafClass_genericPoint_ne_zero` exists, so both sides are nonzero.
- Test that rules out a trivially true product (the square-zero gap of `cup-product`): [pt] ≠ 0 in top degree together with a transversal instance. In the plan these are `p1p1-point-class-nonzero` and `cycle-class-multiplicative-p1p1`; neither exists.

## 8. Pin drift

None. The plan was read at `2ead713`, which is the current pin. On the next bump, add to the diff list: `Other/AlgebraicTopology/Singular/Cap/{Simplicial,Relative,Triad}.lean` (`capHom`, `relativeCapLift`, `triadCapHom`, `triadCapShortComplexHom`, `triadCapCohomologyLinear`, `unionRelativeTriadCapCohomologyLinear`, `triadUnionExcisionHomologyEquiv`), `Other/.../Excision/Triad.lean` (`triadToUnionRelativeChainMap`, the quasi-isomorphism theorem), `standardLocalClass`, `standardSingularSimplex`, `piCoordCLE`, `normalizedRelativeCoclass`, `normalizedDual`, `linearDualHomologyEquiv`, `cycleComponentSupportedClassNormalizationIso`, `cycleComponentSmoothSupportAmbientOpen`, and Tau Ceti's `shuffleChain`.

The branch is one commit behind `main` (#90), and the general-V worktree edits the same roadmap block (rows above `local-class-product`). Rebase before posting.

## 9. Findings

### Route (attack 1)

1. **The route is sound and complete in outline.** Steps 1 to 7 use, in order: the checked absolute comparison (sign 1), the checked forget compatibility, a two-support product on the singular side, the set equality `hT`, upstream's normalization read through its singular transport, a local computation at each point of T(ℂ), and upstream's uniqueness (`cycleComponentSupportedInjectiveClass_unique`, which is in `Other` and is immediate from the definition). Off T the sections vanish because the local cohomology sheaf has zero stalks there. The statement of record is untouched, and the rung's conclusion involves only `cup` and upstream classes, so `relCup2` stays inside proofs and enters no statement of record.
2. **The general-V product formula cannot replace this route.** Φ_V(α ∪ β) = (−1)^{pq} relCupSing(Φ_V α)(β|_V) has one supported factor, so α_Z ∪ [W] lands in H_Z. Comparing it with [T] would need either a product H_Z × H_W → H_T, or a lift from H_Z to H_T, and degree 2(a + b) > 2a has no purity to make that lift unique. Every complete route therefore needs a two-support product. The singular triad cup is the one with upstream support (checked triad excision over ℚ). A sheaf-side two-support product would need `sheaf-tensor-exact`, ℤ[X, X ∖ Z] ⊗ ℤ[X, X ∖ W] ≅ ℤ[X, X ∖ T], and still the same singular local computation, because upstream normalizes classes on the singular side.
3. **Where V-generality enters.** Steps 4 and 5 need restriction to small opens, through upstream's transport and its naturality (`supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section`, `sectionCohomologyToSheafSection_restriction`) plus `transport_eq_flasqueModel` at ⊤. The general-V formula is not needed for the sheaf-side cup of record (the statement compares absolute classes), for cycle classes on the sheaf side (normalized through upstream's transport), or for compatibility of `relCup2` with the Yoneda product (only `forgetRel (relCup2 a b) = cupSing (forgetRel a) (forgetRel b)` is used, and the checked absolute comparison links that to `cup`). The general-V branch's `flasqueModelOpen` and `cohomologyMap_inclusion_singClass` are optional aids for `cycle-class-germ`.
4. **Foundations compared.**

| | Singular-side (plan) | General-V |
|---|---|---|
| new definitions | `relCup2` | none (`supCupY` exists) |
| new topology | shuffle on pairs, cap evaluation, GL⁺ path, affine orientation sign | the same orientation inputs, for any local computation |
| new glue | `normalization-singular`, `cycle-class-germ`, `supported-pair-forget` | the same, plus Φ_V against upstream's transport at V |
| leaves unproved | nothing for the rung | the two-support product, so the rung itself |

   **Recommendation:** adopt the singular-side route for `cycle-class-multiplicative`. Finish and merge the general-V branch on its own merits; it is checked work and harmless, but take it off this rung's critical path. The maintainer chose the general-V route before this plan, so record the change in a decision (0010, amending 0009 rung 5: the local product is formed on the singular side through `relCup2`); the ledger notes alone do not record a change of route.
5. **Kill criterion.** It is preserved. The sketch's phrase "closed or reopened on a corrected normalization" must mean a new rung under a decision record, with the original marked `refuted` and its statement left as it is. State it that way.

### Signs (attack 2)

6. **The sign + is confirmed** for the cross product of complex orientations and for the whole chain (section 6), by reading the source and by scratch and numeric checks. The kernel check remains open in `cross-orientation`. The register row is updated, with status open.
7. Turn the five hand computations of section 6 into Lean lemmas inside the named rungs. The block identity (item 1) is short: S4's formula proves the coordinate statement.

### Statements (attack 3)

8. **Elaborated.** The general theorem and `fundamental-class-unit` elaborate as written (S1). The cap model elaborates (S3) with these definitions, which the sketch only describes in comments; put them in the sketch:

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

   `projB` follows the same pattern with `Fin.natAdd a`. `union_eq` (setA ∪ setB = {0}ᶜ) takes eight lines by `Fin.addCases`. Spell the ambient space `(X := TopCat.of _)` explicitly in every `TopPair.ofSubset`; left implicit, elaboration of the statement exceeds 200000 heartbeats.
9. **`normalization-singular` has no Lean text** in the sketch or ledger ("statement elaborated", but the scratch file was deleted). Record it before posting. State the pair identifications (`TopPair.ofSubset` against `neighborhoodSupportComplementPair`, and the rewrite along `hT`) as lemmas that are the identity on points.
10. **The ledger title of `cycle-class-multiplicative`** still reads "(first case: two fibres on ℙ¹ × ℙ¹)". The rung is now the general transversal theorem, and the first instance is a separate rung. Update the title.
11. **Hypotheses at a = b = 0** need one missing lemma, `cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤`. Add a test rung `cycle-class-multiplicative-codim-zero` that discharges all hypotheses on every X (S5 does two of the three) and derives [X] ∪ [X] = [X]. It is the cheapest instance that shows the hypotheses can be met in Lean.
12. **Transversal test rungs need two more items each.** For both `p1p1-fibres-transversal` and any ℙ² variant: (i) the algebraic affine chart lies in the maximal analytic atlas, measured against upstream's étale-coordinate `localChart` (new foundation rung, for example `affine-chart-analytic`, needed also for ℙ¹); (ii) the intersection point lies off the singular locus of each component's reduced closure.
13. Optional, for later: a statement with several components, [Z] ∪ [W] = Σ [T_i] for a transversal intersection with components T_i. It is the next case of the literature and gives a degree test (line and conic in ℙ²). It should be a new rung, not a change to this one.

### Sizes, dependencies, order, `Other` (attack 4)

14. **The dependency graph is acyclic and every id exists** (script over the whole ledger, 120 rungs).
15. **Split oversized rungs.** `triad-relative-cup` holds a definition and four properties: split it into the definition with `forgetRel` compatibility, naturality for maps of triads, and the cap adjunction. `cycle-class-germ` includes moving a maximal-atlas chart on X(ℂ) into upstream's `E × (Fin c → ℂ)` form on the complex points of the open subscheme X ∖ Z_sing; name that step. `fibre-class-pullback` needs pullback of supported classes compatible with forgetSupport and with normalization, which is a foundation. Make it `kind: foundation` with its own sub-rungs.
16. **Upstream already has the point-class normalization in `Other`**: `cycleComponentSupportedInjectiveClass_point_normalization` and `analyticComponentPointSupportedInjectiveCoclass_relative` give upstream's transport of a point's supported class as an explicit relative coclass on (X, X ∖ Z). In both first cases T is a point, so use these for T and add them to the sketch's table. `cycle-class-germ` is then needed only for Z and W.
17. **ℙ² before ℙ¹ × ℙ¹.** With two coordinate lines in ℙ², [L₀] ∪ [L₁] = [pt] and [pt] ≠ 0 already rule out the square-zero product. That path avoids `complex-points-prod`, the Segre embedding and `fibre-class-pullback`, and it reuses `smoothOfRelativeDimension_toSpec` (any n). Integrality needs the irreducibility argument for three charts. Both cases share the hard inputs: H³ of the complement of a point, the chart compatibility, and the smooth-locus fact. Recommend a decision record that puts ℙ² first, with new rungs `cycle-class-multiplicative-p2` and `cup-positive-degree-test-p2`; the ℙ¹ × ℙ¹ rungs stay open.
18. **`Other` files.** The four unbuilt files (`Cap/Simplicial`, `Cap/Relative`, `Cap/Triad`, `Excision/Triad`) compile at the pin from copies in about 70 seconds, with standard axioms (section 5). They are outside upstream's statement guard. Mitigation: `rfl` pins (section 6, item 5) and the drift list (section 8). A prover's first `lake build` writes their `.olean` files into the shared package cache; build them once, from one worktree, before parallel work starts. The sketch's "What exists" table lists as "upstream" several declarations that live in `Other` (`cycleComponentSupportedClassNormalizationIso_apply`, `cycleComponentSupportedInjectiveClass_unique`, `complexSupportInjectiveCohomologySheafIsoRelative_section_apply`, `sectionCohomologyToSheafSection_restriction`, `standardOrientationBallClass_restrict`, `convexSupport_translation_ne`, `coheight_genericPoint_eq_zero`, `cycleComponentSheafClass_genericPoint_ne_zero`); mark them. Those are built in the cache.

### References (attack 5)

19. **All cited keys exist in `docs/references.md`.** The five new keys (`Bredon1993`, `Bredon1997`, `Dold1972`, `Iversen1986`, `MilnorStasheff1974`) carry "unverified" for chapter and section numbers, and the sketches repeat the mark where they rely on them. The `Hatcher2002` row correctly adds §3.2 (relative cup for open A, B) and §3.B (homology cross product). For `Fulton1998` the precise places are Cor. 19.2 (cycle map is a ring homomorphism) and §8.2 (transversal multiplicity one); keep them marked unverified until checked against the book. No claim in either sketch is called "known" without a key.

## Recommended changes (summary)

| # | Change | Where |
|---|---|---|
| A | Decision 0010: singular-side local product; general-V formula off the critical path of `cycle-class-multiplicative`; kill-criterion wording (finding 5) | `docs/decisions/`, 0009 consequences |
| B | Record the Lean text of `normalization-singular` and the cap model's helper definitions (findings 8, 9) | both sketches |
| C | Update the title of `cycle-class-multiplicative` (finding 10) | ledger, roadmap |
| D | Add `cycle-class-multiplicative-codim-zero` and `affine-chart-analytic`; add the smooth-locus and atlas items to `p1p1-fibres-transversal` (findings 11, 12) | ledger, roadmap, sketch |
| E | Split `triad-relative-cup`; make `fibre-class-pullback` a foundation with sub-rungs (finding 15) | ledger |
| F | Use upstream's point-class normalization for T (finding 16) | sketch |
| G | Decision on ℙ² first, with `cycle-class-multiplicative-p2` and `cup-positive-degree-test-p2` (finding 17) | decision, ledger |
| H | Mark `Other` declarations; add pins and drift list; build `Other` once before parallel work (finding 18) | sketch, pins, handoff |
| I | Turn the five hand computations into Lean lemmas inside the named rungs (finding 7) | rung docstrings |
| J | Rebase on `main` and reconcile with the general-V roadmap rows before posting | branch |
