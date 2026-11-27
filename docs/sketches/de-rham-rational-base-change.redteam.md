# Red team: `de-rham-rational-base-change` and `de-rham-p2-top-rank`

Date: 2026-11-27. Worktree `de-rham-base-change`, branch `track/de-rham-base-change`, base `main` at `2058b7c`, with the uncommitted modules `HodgeLadder/Hodge/DeRhamRationalBaseChange.lean` (79 lines) and `HodgeLadder/Tests/DeRhamP2TopRank.lean` (57 lines), the two ledger entries, the two roadmap rows and the new section "de-rham-rational-base-change and de-rham-p2-top-rank: checked" of `docs/sketches/cup-hodge-filtration.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, the same as on `main`.

Read: both modules; `HodgeLadder/Hodge/DeRhamRationalIndependent.lean` (the conditional forms); `HodgeLadder/Hodge/DeRhamRationalSpan.lean` (`deRhamRationalSpan_of_simplicialComplexSpan`); `HodgeLadder/Tests/ProjectivePlane.lean` (the three instances); `HodgeLadder/Tests/OddDegreeTorus.lean`, `HodgeLadder/Cup/OddDegree.lean`, `HodgeLadder/Cup/Product.lean`, `HodgeLadder/Cup/CupSingular.lean` (for the `gm2` question); upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (lines 620 to 725: `fieldCohomologyModule`, `deRham_complex_smul_eq`, `deRhamHypercohomologyComplexModule`, `deRhamHypercohomologyModule`, `deRhamHypercohomologyIsScalarTower`, `fieldToDeRhamCohomology`, `fieldToDeRhamCohomologyLinear`) and `Definitions/AlgebraicGeometry/ProjectiveSpace.lean` (`Presentation`, `IsProjective`); Mathlib `LinearAlgebra/TensorProduct/Lift.lean` (`liftBaseChange`); the red-team records `de-rham-rational-independent.redteam.md` (findings 7, 7b), `de-rham-rational-span.redteam.md` (7b), `cycle-class-sign-test-p2.redteam.md`; `docs/conventions.md`; `docs/references.md`.

Scratch files (in the worktree under a scratch directory, `lake env lean` against the built modules, deleted afterwards):

| File | What | Result |
|---|---|---|
| RT1 | `#print axioms` of the seven declarations; `(deRhamBaseChangeEquiv X n).toLinearMap = liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)`; the ℂ-action in the statement against `hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c)`; `pp.explicit` of the ℙ² theorem and of `finrank_deRham_eq_finrank_rat projectivePlane 4`; five trivial proofs; `Nontrivial` and `FiniteDimensional` from the value 1; the ℙ² rank from an arbitrary bijective additive `f : H⁴(ℙ²; ℚ) →+ ℚ` | standard axioms on all seven; both `rfl` checks accepted; instances `isIntegral_projectiveSpace 2`, `smooth_projectiveSpace 2`, `isProjective_projectiveSpace 2` and `deRhamHypercohomologyComplexModule`; `simp`, `decide`, `rfl`, `aesop` fail on the ℙ² goal and `simp` on the general rank equality; both consequences and the arbitrary-`f` version accepted (24 s) |
| RT2 | `with_reducible exact` of the rung theorems against statements written with explicit upstream instances: `fieldCohomologyModule ℚ projectivePlane 4`, `deRhamHypercohomologyComplexModule projectivePlane 4`, and `liftBaseChange` with `deRhamHypercohomologyModule ℚ X n`, `deRhamHypercohomologyComplexModule X n`, `deRhamHypercohomologyIsScalarTower ℚ X n` | all accepted |
| RT3 | the `gm2` test: ℚ-independence of the two winding classes from checked lemmas, then ℂ-independence of their de Rham images | accepted, standard axioms, about 25 lines (87 s; finding 7) |
| RT4 | `finrank ℂ H_dR⁴(ℙ²) = 1` from `span_range_fieldToDeRhamCohomology_rat`, `fieldToDeRhamCohomology_rat_injective` and `planeDegreeLinearEquiv`, without `de-rham-rational-independent` | accepted, 25 lines (finding 2) |

`python3 tools/check.py --no-build` in the worktree after deleting the scratch files: `ACCEPTED: all checks passed` (15 s). The run names all seven declarations of the two rungs, each with `[Classical.choice, Quot.sound, propext]`.

**Verdict: pass with changes.** The Lean is correct as written and needs no change to a statement or proof. The changes are a dependency list, one wrong sentence about the `gm2` test in the ledger and sketch, two stale docstring words in the checked module `DeRhamRationalIndependent`, and one sentence of scope on the ℙ² test.

## Findings

1. **The statement is the literature's, with the projectivity hypothesis of the ledger.** Literature: for a space with finite-type integral homology, universal coefficients give H^n(X; ℚ) ⊗_ℚ ℂ ≅ H^n(X; ℂ) by the canonical map [`Hatcher2002` §3.1 to §3.3; section unverified]; the holomorphic Poincaré lemma makes ℂ_X → Ω•_X a resolution, so H^n(X; ℂ) ≅ ℍ^n(X^an, Ω•) [`Voisin2002` vol. I; chapter and theorem number unverified]. A compact complex manifold has finite-type homology; for X smooth projective, X(ℂ) is one.

   | Field | Literature | Lean |
   |---|---|---|
   | X | smooth projective complex variety, X(ℂ) connected | `X : Over (Spec ↧ℂ)`, `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`; `IsProjective` is upstream's (a closed immersion into some `ℙ(Fin (d + 1); T)` over the base) |
   | rational cohomology | H^n(X(ℂ); ℚ) | upstream `H^n(X; ℚ)` with `fieldCohomologyModule` (RT2, reducible) |
   | de Rham side | ℍ^n(X^an, Ω•) with ℂ acting by multiplication | upstream `H_dR^↑n(X)` with `deRhamHypercohomologyComplexModule` (RT1, RT2): c acts by `scalarHolomorphicDeRhamComplexInt X c`, multiplication on forms, no conjugation |
   | the map | m ⊗ c ↦ c · (image of m under constants into 0-forms) | `LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)`, `c ⊗ₜ m ↦ c • ι m` (Mathlib `liftBaseChange_tmul`, `rfl`); the ℚ-structure on the target is upstream's restriction of scalars and the tower is upstream's `deRhamHypercohomologyIsScalarTower` (RT2) |
   | conclusion | the map is an isomorphism; dim_ℂ = dim_ℚ | `Function.Bijective`, `LinearEquiv` `deRhamBaseChangeEquiv`, and `Module.finrank ℂ H_dR^n(X) = Module.finrank ℚ H^n(X; ℚ)` |

   The literature writes H^n(X; ℚ) ⊗_ℚ ℂ, the Lean ℂ ⊗[ℚ] H^n(X; ℚ). The two differ by the swap of tensor factors, with no sign. The two theorem names and statements match the ledger title and the target names of the previous note word for word.

   `deRhamBaseChangeEquiv` is the canonical map: `(deRhamBaseChangeEquiv X n).toLinearMap = LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)` closes by `rfl` (RT1), and `deRhamBaseChangeEquiv_tmul` states the value on pure tensors. A linear map out of ℂ ⊗[ℚ] M is determined by its values on pure tensors, so `_tmul` pins the equivalence completely. The equivalence's inverse is `LinearEquiv.ofBijective`'s inverse, which is noncomputable, and no statement relies on a formula for it.

   Projectivity: the literature statement needs only finite-type homology, so it is true for every smooth integral X with that property (for example `gm2`). The rung keeps `IsProjective` because the ladder's finiteness input is `module_finite_singularHomology` for compact X(ℂ) (port, `ProjectiveFiniteHomology.lean`), used inside `deRhamRationalSpan_of_simplicialComplexSpan`. The hypothesis is used: it supplies `T2Space`, paracompactness and finite generation there. That matches the ledger title.

2. **What the ℙ² test establishes, and what it does not.**
   - **Both degenerate cases are excluded.** From `finrank_deRham_four_projectivePlane`, `Module.nontrivial_of_finrank_eq_succ` gives `Nontrivial H_dR⁴(ℙ²)` and `Module.finite_of_finrank_eq_succ` gives `FiniteDimensional ℂ H_dR⁴(ℙ²)` (RT1, one line each). Mathlib's `finrank` is 0 on a module that is not finite, so the value 1 rules out H_dR⁴ = 0 and an infinite-dimensional H_dR⁴ alike. Literature value: b₄(ℙ²) = 1 [`Hatcher2002` §3.2, the ring H*(ℂP²)], and in Hodge terms ℍ⁴(Ω•) = H²(Ω²) = H^{2,2} ≅ ℂ.
   - **No dependence on `planeDegree`'s normalization.** The proof reads only `planeDegree_bijective`. RT1 reproves the theorem from an arbitrary bijective additive `f : H⁴(ℙ²; ℚ) →+ ℚ`, so neither the value `deg [pt] = 1` nor the sign or scale of `planeDegree` enters. `AddMonoidHom.toRatLinearMap` needs no hypothesis on the ℚ-structures, since a ℚ-module structure on an abelian group is unique.
   - **No degenerate reason.** No definition unfolds to a constant: `simp`, `decide`, `rfl`, `aesop` fail (RT1), and `decide` is stuck at `Nat.beq` on `finrank`. The two inputs are substantial: `planeDegree_bijective` is the Mayer–Vietoris computation of `cycle-class-sign-test-p2` (H³ = H⁴ = 0 of ℙ²(ℂ) ∖ pt), and the rank equality is bijectivity of a map whose surjectivity is `simplicial-complex-span`. The index `H_dR^4` in the ℙ² statement is `(4 : ℤ)` and in the rank equality `((4 : ℕ) : ℤ)`; they agree by `Nat.cast` reduction, the `.trans` typechecks, and no coercion is load-bearing.
   - **What it separates.** The value 1 also follows from the span (`de-rham-rational-span`), ℚ-injectivity (`de-rham-injective`) and the degree isomorphism, with no use of `de-rham-rational-independent`: H⁴(ℙ²; ℚ) = ℚ·e, so H_dR⁴ = span_ℂ {ι e}, and ι e ≠ 0 (RT4, 25 lines). It therefore cannot separate ℂ-independence from ℚ-injectivity, as the sketch says. It does separate the span theorem and the ladder's ℂ-structure from three failures: H_dR⁴(ℙ²) = 0 (rank 0), an infinite-dimensional H_dR⁴(ℙ²) (rank 0), and a ℂ-structure for which H_dR⁴ has rank ≥ 2 while ι has a one-dimensional ℚ-source (excluded by the span). The first was already excluded by the existing check `∃ y ≠ 0`; the other two are new. The ladder note's "fails if the span statement holds for a degenerate reason" is accurate.

3. **Hypotheses and instances.** `pp.explicit` of `finrank_deRham_eq_finrank_rat projectivePlane 4` shows the instances `isIntegral_projectiveSpace 2`, `smooth_projectiveSpace 2`, `isProjective_projectiveSpace 2` from `HodgeLadder.Tests.ProjectivePlane`, found through `projectivePlane = projectiveSpace 2` (`Fin 3` against `Fin (2 + 1)`). `IsIntegral`, `Smooth` and `IsProjective` are `Prop`-valued classes, so no choice of instance can change a statement's meaning; what matters is that the classes are upstream's and Mathlib's, which they are. The data instances are upstream's up to reducible unfolding (RT2): `hypercohomologyAddCommGroup`, `deRhamHypercohomologyComplexModule`, `fieldCohomologyModule`, `deRhamHypercohomologyModule`, `deRhamHypercohomologyIsScalarTower`. Neither file declares an instance, a local instance or an attribute. `isProjective_projectiveSpace` uses the identity presentation, which is a closed immersion, so the hypothesis is the literature's projectivity on this instance. The hypotheses are satisfiable, with ℙ² as the instance.

4. **Proof hygiene.** `#print axioms` on all seven: `[propext, Classical.choice, Quot.sound]` (RT1 and `tools/check.py`). The proofs are one-line applications of checked declarations, with no `set_option`. Trivial proofs fail (finding 2). The rank equality for general X: `simp` makes no progress. No hypothesis is unused: `IsProjective` is consumed by `deRhamRationalSpan_of_simplicialComplexSpan` (finding 1).

5. **Ledger `depends_on`.**
   - `de-rham-rational-base-change`: `["de-rham-rational-independent", "simplicial-complex-span"]` is right. The proof applies `bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_simplicialComplexSpan` and `finrank_deRham_eq_finrank_rat_of_simplicialComplexSpan` (module of `de-rham-rational-independent`) to `simplicialComplexSpan`. `de-rham-rational-span` enters through `de-rham-rational-independent`, which lists it.
   - `de-rham-p2-top-rank`: the proof uses `finrank_deRham_eq_finrank_rat` (`de-rham-rational-base-change`) and `planeDegree_bijective` (`cycle-class-sign-test-p2`), and nothing else. `de-rham-injective` is unused; listing it misstates where injectivity enters, and the note already says so. `de-rham-rational-span` is used only through `de-rham-rational-base-change`. Required: `"depends_on": ["de-rham-rational-base-change", "cycle-class-sign-test-p2"]`, the same list in the roadmap row and in the rung table of `docs/sketches/cup-hodge-filtration.md`. The note keeps naming `de-rham-rational-span` as the rung the test probes, and RT4 as the alternative route through `de-rham-injective` (change B).

6. **Pin drift. None.** `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are unchanged against `main` `2058b7c`; `.lake/packages/HodgeConjecture` is at `2ead713`, the commit the earlier red teams of `de-rham-rational-span`, `de-rham-rational-independent` and `cycle-class-sign-test-p2` read. The upstream definitions these rungs depend on (`fieldCohomologyModule`, `field_smul_eq`, `deRham_complex_smul_eq`, `deRhamHypercohomologyComplexModule`, `deRhamHypercohomologyModule`, `deRhamHypercohomologyIsScalarTower`, `fieldToDeRhamCohomology`, `fieldToDeRhamCohomologyLinear`, `IsProjective`, `ProjectiveSpace.Presentation`) were read at that commit. A future respelling of the ℂ-action would break `deRham_complex_smul_eq` (`rfl` upstream) and the `rfl` pin `constantCoefficientSheafComplexIntMap_mulLeft` of the ladder, which is the drift alarm for this rung.

7. **The `gm2` follow-up: the right next test, and its input is available now.**
   - **Is it the right test?** For `de-rham-rational-independent`, yes. It is the smallest instance with two ℚ-independent classes in one degree, which is the shape that would fail for a ℚ-injective map with ℂ-dependent image (the map ℚ² → ℂ, (a, b) ↦ a + b√2 of that rung's docstring). `gm2` is not projective, so it goes through `linearIndependent_fieldToDeRhamCohomology_rat_of_smooth` and tests nothing in `de-rham-rational-base-change`. A separating test for the base-change rank needs a projective X with b_n ≥ 2, for example `2 ≤ finrank ℂ H_dR²(ℙ¹ × ℙ¹)`; its input, ℚ-independence of pr₁*[pt] and pr₂*[pt], needs their product nonzero, which is the open rung `cup-positive-degree-test`. That is later work.
   - **What it needs.** `LinearIndependent ℚ ![x₁, x₂]` in `H^1(gm2; ℚ)`, with `x₁ = sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero` and `x₂ = sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero`.
   - **It is available.** The ledger note and the sketch say the ladder lacks it and that `gm2_cup_ne_zero` and `gm2_cup_swap_ne` give only nonvanishing and x₁ ≠ x₂. That is wrong. In degree 1, `cup_gradedComm` gives x ∪ x = −(x ∪ x), so x ∪ x = 0 over ℚ. `add_cup` and `cup_add` make the cup additive in each factor, so it is ℚ-linear in each factor (`AddMonoidHom.toRatLinearMap`). From a x₁ + b x₂ = 0, cupping with x₂ on the right gives a (x₁ ∪ x₂) = 0, cupping with x₁ on the left gives b (x₁ ∪ x₂) = 0, and `gm2_cup_ne_zero` gives a = b = 0. RT3 checks it, standard axioms:

     ```lean
     theorem rt_cup_self_one (x : H^1(gm2; ℚ)) : cup x x 2 rfl = 0 := by
       have h := cup_gradedComm (X := gm2) x x (show 1 + 1 = 2 from rfl)
       norm_num at h
       have h2 : (2 : ℚ) • cup x x 2 rfl = 0 := by
         rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
       exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

     noncomputable def rt_cupLeft (y : H^1(gm2; ℚ)) : H^1(gm2; ℚ) →+ H^2(gm2; ℚ) :=
       AddMonoidHom.mk' (fun x ↦ cup x y 2 rfl) (fun a b ↦ add_cup a b y 2 rfl)
     noncomputable def rt_cupRight (x : H^1(gm2; ℚ)) : H^1(gm2; ℚ) →+ H^2(gm2; ℚ) :=
       AddMonoidHom.mk' (fun y ↦ cup x y 2 rfl) (fun a b ↦ cup_add x a b 2 rfl)

     theorem rt_winding_independent :
         LinearIndependent ℚ ![sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero,
           sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero] := by
       set x₁ := sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero
       set x₂ := sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero
       have hne : cup x₁ x₂ 2 rfl ≠ 0 := gm2_cup_ne_zero
       rw [LinearIndependent.pair_iff]
       intro a b hab
       have hR := congrArg (rt_cupLeft x₂).toRatLinearMap hab
       have hL := congrArg (rt_cupRight x₁).toRatLinearMap hab
       simp only [map_add, map_smul, map_zero] at hR hL
       change a • cup x₁ x₂ 2 rfl + b • cup x₂ x₂ 2 rfl = 0 at hR
       change a • cup x₁ x₁ 2 rfl + b • cup x₁ x₂ 2 rfl = 0 at hL
       rw [rt_cup_self_one, smul_zero, add_zero] at hR
       rw [rt_cup_self_one, smul_zero, zero_add] at hL
       exact ⟨(smul_eq_zero.mp hR).resolve_right hne, (smul_eq_zero.mp hL).resolve_right hne⟩

     theorem rt_gm2_deRham_independent :
         LinearIndependent ℂ (fieldToDeRhamCohomology ℚ gm2 1 ∘
           ![sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero,
             sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero]) :=
       linearIndependent_fieldToDeRhamCohomology_rat_of_smooth gm2 1 rt_winding_independent
     ```

     Imports: `HodgeLadder.Tests.OddDegreeTorus`, `HodgeLadder.Cup.CupSingular`, `HodgeLadder.Hodge.DeRhamRationalIndependent`; opens `CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder HodgeLadder.Tests HodgeLadder.Cup`. The proof uses the sign of `cup_gradedComm`: in degree (1, 1) it is (−1)^{1·1} = −1, which gives x ∪ x = −(x ∪ x); a sign +1 would give the empty identity x ∪ x = x ∪ x and no vanishing. Proposed new rung (change E).

8. **Equality first (decision 0004).** `de-rham-rational-base-change` is an identity: `deRhamBaseChangeEquiv` is an exact ℂ-linear equivalence, pinned on pure tensors by `deRhamBaseChangeEquiv_tmul`, with no scalar and no sign, and it closes the equality that `de-rham-rational-span` (inclusion `⊤ ≤ span`) and `de-rham-rational-independent` (injectivity) were steps toward. `de-rham-p2-top-rank` is an exact equality of natural numbers. The rank equality of the base-change rung is exact but carries a dimension count only with finiteness: both sides are 0 when both spaces are infinite-dimensional. For X projective both are finite-dimensional in mathematics; the ladder has it only in degree 4 of ℙ² (finding 2). T1's eigenspace count reads `dim_ℂ H¹_dR = dim_ℚ H¹(X; ℚ)` and needs that number to be the real one. Proposed new rung (change F): `FiniteDimensional ℚ H^n(X; ℚ)` for smooth projective integral X, from `module_finite_singularHomology`, Ψ and universal coefficients; with this rung it gives `FiniteDimensional ℂ H_dR^n(X)`.

9. **Conventions.** No sign occurs in either proof.

   | Convention | Row in `docs/conventions.md` | Truth depends on it? |
   |---|---|---|
   | ℂ-structure on `H_dR^n(X)` | "Complex structure on H_dR and on complex constant cohomology" | no: with a conjugated action, `liftBaseChange` becomes c ⊗ m ↦ c̄ • ι m, which is the original map after the ℚ-linear bijection c ⊗ m ↦ c̄ ⊗ m of the source; bijective iff the original is; finrank unchanged |
   | ℚ-structure on `H^n(X; ℚ)` and on `H_dR^n(X)` | "Rational structure on constant-sheaf cohomology" | no: unique on an abelian group |
   | ι = `algebraMap ℚ ℂ` then constants into 0-forms | "Rational-to-de Rham map and the range of F^p" | no: a nonzero scalar on ι (for example (2πi)^p) changes neither bijectivity nor rank |
   | `liftBaseChange`: ℂ on the left factor, c ⊗ m ↦ c • l m; `finrank` = 0 on a module that is not finite | new row "Base change ℂ ⊗_ℚ M and the rank of an infinite-dimensional space" (added by this pass) | bijectivity: no (the literature's M ⊗ ℂ differs by a swap, no sign). Rank equality: its content does, since both sides are 0 when both are infinite-dimensional (finding 8) |
   | degree map on H⁴(ℙ²) | "Degree on H⁴(ℙ²)" | no: only bijectivity is used (finding 2) |

   No cited or assumed input: every input is checked Lean at the pin.

## Required changes

A. **`depends_on` of `de-rham-p2-top-rank`.** In `ledger/ladder.json`:

   ```json
   "depends_on": [
     "de-rham-rational-base-change",
     "cycle-class-sign-test-p2"
   ],
   ```

   The same pair in the `de-rham-p2-top-rank` row of `docs/roadmap.md` and of the rung table in `docs/sketches/cup-hodge-filtration.md`.

B. **Scope of the ℙ² test.** In the `de-rham-p2-top-rank` ledger note, replace "de-rham-injective is not used by the proof (injectivity enters through de-rham-rational-independent)." by: "The proof reads finrank_deRham_eq_finrank_rat and planeDegree_bijective only. The value also follows from span_range_fieldToDeRhamCohomology_rat (de-rham-rational-span), fieldToDeRhamCohomology_rat_injective (de-rham-injective) and planeDegreeLinearEquiv without de-rham-rational-independent (red team scratch RT4), so the test does not exercise ℂ-independence." Add the same sentence, in prose, after the second paragraph of the module docstring of `HodgeLadder/Tests/DeRhamP2TopRank.lean` (docstring only).

C. **The `gm2` sentence.** In the `de-rham-rational-base-change` ledger note, delete everything from "Optional sharper test" to the end and replace it with: "The optional separating test of the red team of de-rham-rational-independent, finding 7b, is the new rung de-rham-rational-independent-test-gm2; gm2 is not projective, so it tests de-rham-rational-independent and not this rung." In the section "What it tests" of `docs/sketches/cup-hodge-filtration.md`, replace "the `gm2` test of finding 7b stays optional and unposted, with its missing input recorded in the ledger note of `de-rham-rational-base-change`" by "the `gm2` test of finding 7b is posted as `de-rham-rational-independent-test-gm2`; its input, ℚ-independence of the two winding classes, follows from `gm2_cup_ne_zero`, `add_cup`, `cup_add` and `cup_gradedComm` (red team of `de-rham-rational-base-change`, finding 7)".

D. **Stale docstring words in `HodgeLadder/Hodge/DeRhamRationalIndependent.lean`.** Two places say the base-change rung is "stated": the last bullet of the module docstring, "(rung `de-rham-rational-base-change`, stated)", and the section header "Toward the base-change identity (rung `de-rham-rational-base-change`, stated)". Replace "stated" in both by "checked in `HodgeLadder.Hodge.DeRhamRationalBaseChange`". Docstrings only; no declaration changes, so the checked record of `de-rham-rational-independent` is unaffected.

E. **New rung `de-rham-rational-independent-test-gm2`** (kind `test`, status `open`, `depends_on`: `de-rham-rational-independent`, `cup-odd-degree-gm2`, `cup-graded-commutative`, `cup-product`): `LinearIndependent ℂ (fieldToDeRhamCohomology ℚ gm2 1 ∘ ![sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero, sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero])`, with the ℚ-independence lemma as a named declaration. The proof of finding 7 is ready. It may land in this pull request or the next one; the roadmap row and an issue follow the propagation map. All four ids exist in the ledger.

## Recommended, not required

F. New rung `rational-cohomology-finite-dimensional` (foundation): `FiniteDimensional ℚ H^n(X; ℚ)` for smooth projective integral X, from `module_finite_singularHomology`, Ψ (`rationalCohomologyAddEquivSingularCohomology`) and universal coefficients over ℚ; with `deRhamBaseChangeEquiv` it gives `FiniteDimensional ℂ H_dR^n(X)`, and the rank equality then counts dimensions in every degree. T1's eigenspace count needs it.
