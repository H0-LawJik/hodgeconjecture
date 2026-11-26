# Roadmap: the ladder

Each row is a live rung in `ledger/ladder.json`. Status words: `checked` (the checker accepts the declarations), `stated` (statement sorry-free, proof open), `open`, `refuted`, `dead`. Dead rungs stay in the ledger with their reason; decision 0003 retired thirteen of them.

| Rung | Kind | Status | Depends on | What it needs |
|---|---|---|---|---|
| `upstream-statement` | statement | stated | | upstream `HodgeConjecture`, `LefschetzOneOne`, `HodgeConjectureInDimensionLE` at the pinned commit |
| `statements-consistent` | reduction | checked | `upstream-statement` | done in `HodgeLadder.Upstream.Statements` |
| `cycle-class-pins` | test | checked | `upstream-statement` | done in `HodgeLadder.CycleClass.Pins`; see `docs/cycle-class.md` |
| `known-half-statement` | statement | stated | `upstream-statement` | `CycleClassesAreHodge`, `HodgeConjectureEquality`, `LefschetzOneOneEquality` |
| `equality-reductions` | reduction | checked | `known-half-statement` | equality ↔ upstream inclusion ∧ known half |
| `lefschetz-upstream-verify` | case | checked | `upstream-statement` | reproduce the build of upstream PR #228 at `c7d5c94b`; axiom audit; red-team verdict |
| `nonvacuity-tests` | test | checked | `upstream-statement` | done in `HodgeLadder.Tests`: Spec ℂ meets the hypotheses; Hdg^0 = span ≠ 0 for every X |
| `divisor-chern-exact` | foundation | checked | `lefschetz-upstream-verify` | the class of a Cartier divisor equals the rational image of c₁(𝒪(D)) exactly on the pinned cycle class, sign determined |
| `lefschetz-port` | foundation | checked | `lefschetz-upstream-verify`, `divisor-chern-exact` | port the upstream stack (PRs #217–#226, #9, #230, #228) from v4.33.1 to the current pin; coordinate with upstream first |
| `lefschetz-1-1` | case | checked | `lefschetz-port`, `nonvacuity-tests` | done in `HodgeLadder.Lefschetz.OneOne` (`lefschetzOneOne_holds`; the inclusion, a step) |
| `chern-classes-are-hodge` | foundation | checked | `lefschetz-port`, `divisor-chern-exact` | done in `HodgeLadder.Hodge.ChernClasses`: F¹ = ker(H_dR → ℍ(𝒪)); rational c₁ and Cartier divisor classes are Hodge |
| `ufd-descent` | foundation | checked | | done in `HodgeLadder.Algebra.UFDDescent` (Mori's descent, local case) |
| `analytic-stalk-ufd` | foundation | checked | `lefschetz-port` | done in `HodgeLadder.Divisor.AnalyticStalk` |
| `local-factoriality` | foundation | checked | `ufd-descent`, `analytic-stalk-ufd` | done in `HodgeLadder.Divisor.LocalFactoriality` |
| `prime-divisor-ideal-sheaf` | foundation | checked | `local-factoriality` | done in `HodgeLadder.Divisor.PrimeDivisorSmooth`: the ideal sheaf of D is invertible, represented by Cartier data with divisor −D |
| `unit-extension-of-invertible` | foundation | checked | `lefschetz-port` | a unit extension E with L^an ≅ E.section for every invertible L |
| `prime-divisors-cartier` | foundation | checked | `chern-classes-are-hodge`, `local-factoriality`, `prime-divisor-ideal-sheaf`, `unit-extension-of-invertible` | assembly: `CycleClassesAreHodgeOne` |
| `lefschetz-1-1-equality` | case | checked | `lefschetz-1-1`, `divisor-chern-exact`, `equality-reductions`, `chern-classes-are-hodge`, `prime-divisors-cartier` | `theorem : LefschetzOneOneEquality`; the checkpoint's definition of done |
| `cycle-classes-are-hodge` | foundation | open | `known-half-statement`, `cycle-class-pins` | `theorem : CycleClassesAreHodge` |
| `lefschetz-1-1-integral` | case | open | `lefschetz-port`, `divisor-chern-exact` | image of c₁ on Pic equals the integral Hodge classes in H² |
| `projective-space-test` | test | open | `upstream-statement`, `projective-line-test` | Hdg^1(ℙ^n) = span, both one-dimensional; split into the ℙ¹ rungs below (`docs/sketches/projective-space-test.md`) |
| `projective-line-witness` | test | checked | `upstream-statement` | ℙ¹ = `ProjectiveSpace.toBase (Fin 2) (Spec ℂ)` is integral, smooth of relative dimension one, projective; Oka charts and base change |
| `projective-line-point` | test | checked | `projective-line-witness` | a point of coheight one whose analytic complement is homeomorphic to ℂ |
| `forget-support-exact` | foundation | checked | `upstream-statement` | done in `HodgeLadder.Tests.ForgetSupport`: forgetSupport injective in degree n + 1, surjective in degree n, when H^n of the open complement vanishes |
| `contractible-open-acyclic` | foundation | checked | `upstream-statement` | done in `HodgeLadder.Tests.ContractibleAcyclic`: H'^q(U; ℚ) = 0 for q > 0 and U ⊆ X(ℂ) a contractible open, through the flasque singular-cochain resolution on U |
| `projective-line-class-nonzero` | test | checked | `projective-line-point`, `forget-support-exact`, `contractible-open-acyclic` | the class of a point is nonzero in H²(ℙ¹; ℚ); the degree-two non-vacuity test |
| `projective-line-h2` | test | checked | `projective-line-class-nonzero` | dim H²(ℙ¹; ℚ) = 1 and it equals the span; one-dimensionality of H²_pt on the sheaf side |
| `projective-line-test` | test | checked | `projective-line-h2`, `lefschetz-1-1`, `chern-classes-are-hodge` | Hdg^1(ℙ¹) = span, both one-dimensional; needs the point class to be Hodge |
| `clifford-exterior-spin` | foundation | checked | `lefschetz-1-1-equality` | done in `HodgeLadder.Markman.CliffordSpin`: the Clifford algebra of the split form on Dual R M × M acts on ∧M by contraction plus wedge (`spinAction`), the generator squares to f x with sign +, and the action respects parity; for the Markman inventory (`docs/notes/2026-11-24-spinors-characters-tests.md`) |
| `clifford-exterior-chevalley` | foundation | open | `clifford-exterior-spin` | Chevalley: `spinAction` is bijective for M finite free; needs a spanning set of 2^{2n} monomials for the Clifford algebra, absent from Mathlib at the pin |
| `elliptic-product-test` | test | open | `lefschetz-1-1-equality` | dim Hdg^1(E₁ × E₂) = 2 + rank Hom(E₁, E₂) while h^{1,1} = 4; needs the cup product and Künneth for constant-sheaf cohomology (inventory §5) |
| `cup-front` | front | open | `upstream-statement` | ring structure on H^*(X; ℚ), decision 0008 |
| `rational-ext-equiv` | foundation | checked | `cup-front` | H^n(X; ℚ) ≅ Ext^n(ℚ_X, ℚ_X) in sheaves of ℚ-vector spaces |
| `cup-product` | foundation | checked | `rational-ext-equiv` | cup product: associative, unital, bilinear |
| `cup-pullback` | foundation | checked | `cup-product` | Pullback along a morphism of complex schemes on H^*(X; ℚ) is multiplicative for the cup product |
| `sheaf-tensor-exact` | foundation | checked | `cup-front` | The tensor product of sheaves of ℚ-vector spaces on X(ℂ) is exact in each variable; the unit is ℚ_X |
| `supported-cup` | foundation | checked | `cup-product`, `cup-pullback` | Product of a supported class in H_[Z]^p(X; ℚ) with an absolute class |
| `tauceti-cup-backport` | foundation | checked | `cup-front` | Tau Ceti's singular cup product and its graded commutativity, vendored into port/ at the pin |
| `cochain-cup-upstream` | foundation | checked | `tauceti-cup-backport` | The cup product on upstream's singular cochains, through a cochain isomorphism with Tau Ceti's model |
| `cochain-sheaf-right-mult` | foundation | checked | `cochain-cup-upstream` | Right multiplication by a global cocycle as a morphism of complexes of sheaves on the sheafified singular cochains |
| `right-mult-cocycle` | foundation | checked | `cochain-sheaf-right-mult` | Right multiplication by a global cocycle as a degree-q cocycle of the Hom complex Hom(S_ℤ, S_ℤ), components (−1)^{pq} r_p |
| `right-mult-unit` | foundation | checked | `right-mult-cocycle` | ι ≫ R_b is the Hom-complex cocycle of the global section b |
| `cocycle-class-comp` | foundation | checked | `right-mult-cocycle` | The derived-category class of a Hom-complex cocycle is compatible with pre- and postcomposition by chain maps |
| `step2-cocycle-class` | foundation | checked | `cocycle-class-comp` | Upstream's step 2 sends the class of a Hom-complex cocycle z : ℤ[0] → S_ℤ to the homology class of the global section z names, for every K-injective resolution |
| `ext-class-right-mult` | foundation | checked | `right-mult-unit`, `step2-cocycle-class` | r_b ∘ ι = ι[q] ∘ ε([b]) in the derived category, for ι : ℚ_X → S• the singular-cochain resolution |
| `iota-upstream` | foundation | checked | `ext-class-right-mult` | ι_ℤ composed with upstream's integer-constant isomorphism equals ℤ_X → ℚ_X followed by upstream's ι |
| `cocycle-class-mul` | foundation | checked | `cocycle-class-comp` | The derived-category class of a composite of Hom-complex cocycles is the composite of their classes, with no sign |
| `named-cocycle-comp` | foundation | checked | `cocycle-class-mul`, `ext-class-right-mult` | The cocycle naming a composed with right multiplication by b is (−1)^{pq} times the cocycle naming a ∪ b |
| `ab-ext-yoneda` | foundation | checked | `cup-product` | The Yoneda cup in sheaves of abelian groups: α ∪ β is α followed by the forgotten endomorphism class of β |
| `kappa-cancel` | foundation | checked | `ab-ext-yoneda` | ℚ ⊗ (ℤ_Y → ℚ_Y) is an isomorphism, and precomposition with ℤ_Y → ℚ_Y is injective on Ext^n(ℚ_Y, M) for every sheaf M of ℚ-vector spaces, in particular M = ℚ_Y |
| `one-is-kappa` | foundation | checked | `kappa-cancel` | The unit oneY of H^0(Y; ℚ) is the class of ℤ_Y → ℚ_Y, so every β is κ followed by its endomorphism class forgetEnd(e β) |
| `ext-derived-bridge` | foundation | checked | `one-is-kappa` | Mathlib's Ext classes between constant sheaves and upstream's Hypercohomology classes agree in the derived category of sheaves of abelian groups on X(ℂ), through single versus extended complexes and upstream's ULift identification |
| `end-class-right-mult` | foundation | checked | `ab-ext-yoneda`, `ext-class-right-mult`, `iota-upstream`, `kappa-cancel`, `one-is-kappa`, `ext-derived-bridge` | The forgotten endomorphism class of [b], followed by ι, is ι followed by R_b |
| `cup-global-comparison` | foundation | checked | `end-class-right-mult`, `named-cocycle-comp`, `ab-ext-yoneda`, `ext-derived-bridge` | Upstream's steps 1 and 2 send cup x y to (−1)^{pq} times the class named by a ∪ b |
| `step3-named-class` | foundation | checked | `ext-class-right-mult` | Upstream's full comparison sends the class named by a global cocycle c to the singular class of c |
| `cup-top-open` | foundation | checked | `step3-named-class`, `cochain-cup-upstream` | The singular cup of the singular classes of a and b is the singular class of a ∪ b |
| `cup-step3` | foundation | checked | `cup-global-comparison`, `step3-named-class`, `cup-top-open` | Upstream's step 3 on named classes, compatible with cupGlobal and the singular cup |
| `cup-singular-comparison-absolute` | foundation | checked | `cup-global-comparison`, `cup-step3` | Ψ(x ∪ y) = (−1)^{pq} · cupSing (Ψ x) (Ψ y) |
| `relative-singular-cup` | foundation | checked | `cochain-cup-upstream` | The relative singular cup H^p(X, A) × H^q(X) → H^{p+q}(X, A) on upstream's RelativeCochainComplex, compatible with forgetting A and with cupSing |
| `support-cone-right-mult` | foundation | dead | `right-mult-cocycle` | Right multiplication by a global cocycle on upstream's natural singular support cone, as a Hom-complex cocycle compatible with the cone maps |
| `support-ab-yoneda` | foundation | checked | `ab-ext-yoneda`, `supported-cup` | The supported cup supCup α y is α followed by forgetEnd (e y) in sheaves of abelian groups |
| `support-named-class` | foundation | dead | `support-cone-right-mult`, `step3-named-class` | Upstream's supported comparison sends the class named by a relative cocycle to its relative singular class |
| `cup-comparison-projective-line` | test | checked | `cup-singular-comparison-absolute`, `cup-graded-commutative`, `projective-line-test` | The cup comparison and graded commutativity apply to upstream's ℙ¹ |
| `cup-odd-degree-test` | test | open | `cup-singular-comparison-absolute` | A nonzero product of two classes in H¹(X; ℚ) |
| `supported-sections-right-mult` | foundation | dead | `right-mult-cocycle` | Right multiplication by a global cocycle preserves the sections of the singular cochain sheaves supported in Z, as a map of complexes |
| `supported-step2-cocycle-class` | foundation | checked | `step2-cocycle-class` | the supported-sections model of `relH` on the class of a Hom-complex cocycle, K-injective and flasque forms |
| `supported-sections-class` | foundation | checked | `supported-step2-cocycle-class`, `support-ab-yoneda`, `cup-global-comparison` | Through upstream's relHAddEquivSupportedSectionsHomologyOfFlasque, supCup α y is the class of the supported cocycle of α times b |
| `supported-named-cocycle-comp` | foundation | checked | `named-cocycle-comp`, `supported-step2-cocycle-class` | the section named by `cocycleComp z R_b` is `(−1)^{pq}` times `b` acting on the section named by `z` |
| `supported-raw-map` | foundation | checked | | A map Θ of short complexes from the relative dual-cochain sequence of (X, U) to upstream's supported-sections sequence of the singular cochain sheaves over ⊤, with the raw-to-sheaf maps in the middle and last terms |
| `cone-map-lemmas` | foundation | checked | | `mapArrowHom` is `mappingCone.map`; exact functors commute with the cone comparison |
| `supported-cone-compat` | foundation | checked | `supported-raw-map` | Upstream's cone identifications in supportedRationalSingularSectionCohomologyEquivRelative compose, on cone homology, to the mapping-cone map of Θ |
| `supported-singular-class` | foundation | checked | `supported-cone-compat` | Upstream's supported singular equivalence sends the class of Θ₁ c to the relative class of c, for every relative cocycle c |
| `relative-cup-cocycle` | foundation | checked | `relative-singular-cup` | `relCupSing` on cocycle classes; the relative cup forgets to the Alexander–Whitney cup |
| `supported-relative-cup` | foundation | checked | `supported-singular-class`, `relative-singular-cup` | Upstream's supported singular equivalence sends the class of b acting on Θ₁ c to relCupSing [c] [b] |
| `supported-singular-model` | foundation | checked | `relative-singular-cup` | The cohomology of the sections of the singular cochain sheaves supported in Z is relative singular cohomology H^n(X, X ∖ Z), compatibly with relCupSing |
| `cup-singular-comparison` | foundation | checked | `cup-singular-comparison-absolute`, `supported-cup` | The supported cup product against the relative singular cup product |
| `cup-comparison-supported-pair` | foundation | checked | `cup-singular-comparison` | the supported comparison on `H^n(X, X ∖ Z; ℚ)` (`TopPair.ofSubset`), with `Ψ β` on `X`; `relCupSing` is natural for maps of pairs |
| `cup-comparison-supported-test` | test | checked | `cup-comparison-supported-pair` | ℙ¹: the supported comparison applies for every closed `Z`; the class of a point times `1` is nonzero |
| `supported-model-agreement` | foundation | checked | `cup-singular-comparison` | `Φ` agrees with upstream's cycle-class transport |
| `step1-of-hom` | foundation | checked | `ext-derived-bridge`, `cocycle-class-mul` | `Ψ`'s step 1 on a class named by a cocycle out of `ℤ_X[0]` |
| `forget-support-cocycle` | foundation | checked | | forgetting the support precomposes a cocycle representative with `ℤ_X → ℤ[X, X ∖ Z]` |
| `constant-generator` | foundation | checked | | evaluation at `1` out of `ℤ_Y`; the terminal isomorphism sends the generator of `ℤ[⊤]` to `1` |
| `supported-forget-compat` | foundation | checked | `cup-singular-comparison` | forgetting the support commutes with `Φ` against `Ψ`, sign fixed |
| `local-class-product` | foundation | open | `cup-singular-comparison` | The product of normalized local classes of transversal components is the normalized local class of the intersection |
| `cup-hodge-filtration` | foundation | open | `cup-product` | Cup products respect the Hodge filtration: F^p ∪ F^q ⊆ F^{p+q}, so products of Hodge classes are Hodge classes |
| `cup-positive-degree-test` | test | open | `cup-pullback`, `cycle-class-multiplicative` | On ℙ¹ × ℙ¹, pr₁*[pt] ∪ pr₂*[pt] ≠ 0 |
| `cup-graded-commutative` | foundation | checked | `cup-singular-comparison-absolute` | α ∪ β = (−1)^{pq} β ∪ α |
| `cycle-class-multiplicative` | foundation | open | `local-class-product` | class of an intersection is the cup product of classes |
| `hard-lefschetz` | foundation | open | `upstream-statement` | Kähler geometry and the Lefschetz decomposition on upstream cohomology; the cup product (front `cup`); inventory before sub-rungs |
| `dimension-le-three` | case | open | `lefschetz-1-1`, `hard-lefschetz` | `HodgeConjectureInDimensionLE 3` |
| `markman-statement` | front | open | `lefschetz-1-1-equality` | Markman's theorem on upstream definitions; inventory written (`docs/notes/2026-11-25-markman-inventory.md`); blocked on front `cup`; target sequence T1 to T5 (inventory §6) |

## Order of attack

Done: M0 and M1 (`lefschetz-upstream-verify`, `nonvacuity-tests`, `lefschetz-port`, `divisor-chern-exact`, `lefschetz-1-1`, `lefschetz-1-1-equality`), the divisor chain behind it, and the ℙ¹ test (`projective-line-test`). The Markman inventory is written.

1. Front `cup` (decision 0008): `rational-ext-equiv`, then `cup-product`, then `cup-graded-commutative` and `cycle-class-multiplicative`. It blocks M2 and M3 (inventory §4, gap 1).
2. `clifford-exterior-spin` is checked (the Clifford action on ∧*H with parity); `clifford-exterior-chevalley` (∧*H is the spin module) is next on this track.
3. After the cup front: the inventory's target sequence T1 to T5 (§6), T1 first (Weil classes on abelian surfaces of Weil type). These rungs are not yet in the ledger; post them as each one's inputs exist. `markman-statement` stays open until then.
4. `cycle-classes-are-hodge` can start now. `projective-space-test` for n ≥ 2 and `lefschetz-1-1-integral` are the remaining M1+ rungs.
5. `hard-lefschetz` is the long pole for `dimension-le-three`; it also needs the cup product. Inventory before sub-rungs.
6. `elliptic-product-test` needs the cup product and Künneth; it cannot be the first abelian rung (inventory §5).

## Watch signals

- The upstream pin moves: diff the definitions in `docs/conventions.md` between commits before bumping.
- A rung sitting `open` with no issue for a month: post sub-rungs or mark it `dead` with a reason.
- Any rung marked `checked` whose declarations no longer pass the axiom check after a bump: CI fails, and the fix goes before any new work.
