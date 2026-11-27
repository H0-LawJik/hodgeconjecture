# Red team: de-rham-rational-independent (statement and proof)

Date: 2026-11-27. Branch `track/de-rham-rational-independent`, base main `0a5c936`, upstream pin `2ead713`. Under review: `HodgeLadder/Hodge/DeRhamRationalIndependent.lean` (158 lines, 8 declarations, not yet imported from the root) and the section "de-rham-rational-independent: statement" of `docs/sketches/cup-hodge-filtration.md`.

**Verdict: pass with changes.** The statement is the injectivity half of `ℂ ⊗_ℚ H^n(X; ℚ) ≅ H_dR^n(X)`, stated against upstream's map and upstream's ℚ- and ℂ-structures with no conjugation. The proof is kernel-checked with the standard three axioms, uses no finiteness, and its `_of_smooth` versions are true as stated. The changes are bookkeeping: the ledger dependency (the prover's proposal drops a dependency the proof does use, finding 5), the root import, two `docs/gaps.md` rows and the sketch tables.

## What was tried

| Attempt | Result |
|---|---|
| Read the module, the sketch section, `DeRhamRationalSpan.lean`, `General/SimplicialCochainSpan.lean`, upstream `Filtration.lean` (lines 60 to 260, 470 to 500, 600 to 740, 810 to 850), the port's `SingularCochainCoefficientChange.lean` (lines 95 to 125, 420 to 450) and the diff of #192 on that file | every map and action in the statement unfolds to upstream's definitions; findings 1 and 3 |
| Scratch module importing the built module (olean 13:20, source 13:19): `#print axioms` on all eight declarations | all eight `[propext, Classical.choice, Quot.sound]` |
| Same scratch: `(inferInstance : Module ℚ H^n(X; ℚ)) = fieldCohomologyModule ℚ X n` and `(inferInstance : Module ℂ H_dR^n(X)) = deRhamHypercohomologyComplexModule X n`, each by `with_reducible rfl`; `q • α = Sheaf.H.map (fieldScalarSheaf ℚ X q) n α` by `rfl` | accepted; no instance diamond in the statement |
| Same scratch: the rung's statement re-elaborated outside any `respectTransparency` block, closed by `with_reducible exact linearIndependent_fieldToDeRhamCohomology_rat X n hv` | accepted |
| Satisfiability: `IsIntegral projectivePlane.left ∧ Smooth projectivePlane.hom ∧ IsProjective projectivePlane.hom` by `inferInstance` | accepted |
| Non-vacuous instance: `LinearIndependent ℂ (fieldToDeRhamCohomology ℚ projectivePlane (2 * 2) ∘ ![[pt]])` from the rung, `linearIndependent_unique_iff` and `projectivePlane_point_class_ne_zero` | accepted (two lines) |
| Trivial proofs: `simpa using hv`; `hv.map' (fieldToDeRhamCohomologyLinear ℚ X n) (ker_fieldToDeRhamCohomologyLinear_rat X n)` | both fail: the first leaves `LinearIndependent ℚ v` against a `LinearIndependent ℂ` goal; the second gives ℚ-independence of the image only. `LinearIndependent.map_of_injective_injective` would need a map `i : ℂ → ℚ` with `j (i r • m) = r • j m`, which does not exist |
| Assembly toward the identity: `Function.Bijective (liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n))` from the span equality, then `Module.finrank ℂ H_dR^n(X) = Module.finrank ℚ H^n(X; ℚ)`, then the projective case from `hS : SimplicialComplexSpan` through `deRhamRationalSpan_of_simplicialComplexSpan` | accepted, standard axioms, 12 lines in all (finding 7) |
| `python3 tools/check.py --no-build` in the worktree | `ACCEPTED: all checks passed` (13 s); the module is not yet in the ledger, so its axioms are not in that run, and are covered by the scratch row above |

The scratch elaborated in about 41 s. Scratch files were kept in the worktree and deleted.

## Findings

1. **Is this the literature's statement? Yes, its injectivity half.** Literature: for any space, `H^n(X; ℚ) ⊗_ℚ ℂ → H^n(X; ℂ)` is injective, and an isomorphism when the integral homology is of finite type (universal coefficients, [Hatcher2002] §3.1, section unverified; the row lists §§3.2 and 3.3); `H^n(X; ℂ) ≅ ℍ^n(X^an, Ω•)` by the holomorphic Poincaré lemma ([Voisin2002] vol. I, chapter unverified). Field by field:

   | Field | Literature | Lean |
   |---|---|---|
   | rational cohomology | Betti cohomology of X(ℂ), a ℚ-vector space | upstream `H^n(X; ℚ)` with `fieldCohomologyModule`: q acts by `Sheaf.H.map (fieldScalarSheaf ℚ X q)`, the change of coefficients along `mulLeft q` (checked `with_reducible rfl`) |
   | de Rham cohomology | H^n(X; ℂ) or H^n_dR, with its usual ℂ-structure | upstream `H_dR^n(X)` with `deRhamHypercohomologyComplexModule`: c acts by `scalarHolomorphicDeRhamComplexInt X c`, multiplication on forms, no conjugation (checked `with_reducible rfl`; conjugation is the separate `deRhamConj`) |
   | map | inclusion of constants, no twist | `fieldToDeRhamCohomology ℚ X n`, `algebraMap ℚ ℂ` and constants into 0-forms (conventions row "Rational-to-de Rham map") |
   | conclusion | `ℂ ⊗_ℚ H^n(X; ℚ) → H^n_dR` injective | `LinearIndependent ℚ v → LinearIndependent ℂ (ι ∘ v)`; equivalently `Function.Injective (LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n))` |

   The `liftBaseChange` form is stated on the right structures: the source is `ℂ ⊗[ℚ] H^n(X; ℚ)` with ℂ acting on the left factor, the target carries `deRhamHypercohomologyComplexModule`, and the `IsScalarTower ℚ ℂ H_dR^n(X)` is upstream's `deRhamHypercohomologyIsScalarTower` for the restriction of scalars that `fieldToDeRhamCohomologyLinear` is linear for. The map is `c ⊗ m ↦ c • ι m`. The module proves independence implies injectivity through a base-changed basis; the converse also holds (it is the base change of a ℚ-independent family), so the docstring's "equivalent form" is correct. With `de-rham-rational-span`, the scratch row above gives the bijection and `finrank ℂ H_dR^n = finrank ℚ H^n(X; ℚ)`, which is the count T1 needs (finding 7). This is the statement T1 needs.

2. **No finiteness, and the `_of_smooth` versions.** The mathematics agrees with the Lean. For any space and any family of classes, a ℚ-linear functional φ : ℂ → ℚ is an additive map of coefficients; pushing a complex relation Σ zᵢ (ratScaled zᵢ)_* vᵢ = 0 along φ gives Σ φ(zᵢ) vᵢ = 0, so φ(zᵢ) = 0 for every φ and zᵢ = 0. Equivalently: ℂ is a direct sum of copies of ℚ, each finite subsum is a direct summand of the coefficients, and cohomology commutes with finite direct sums. Only the span half needs finite-type homology. No step uses a finiteness instance: the file mentions no `Module.Finite` or `FiniteDimensional`; `Module.forall_dual_apply_eq_zero_iff` needs only that ℂ is a free ℚ-module; `Module.Basis.ofVectorSpace` needs no finiteness. The `_of_smooth` theorems are therefore true as stated, with `IsIntegral X.left` and `Smooth X.hom`, which upstream's `ι` needs to be defined. They are stronger than the rung and are the right declarations to name in the ledger (finding 5). The projective theorem takes `{ι : Type}` as the ledger says; the `_of_smooth` one takes `{ι : Type*}`.

3. **The `rfl` step, the `respectTransparency` blocks, and the scalar actions.**
   - `constantCoefficientSheafComplexIntMap_mulLeft` equates the port's `constantCoefficientSheafComplexIntMap X (AddMonoidHom.mulLeft r)` (built from `constantSheaf (Opens.grothendieckTopology _) AddCommGrpCat`) with upstream's `fieldScalarComplex ℚ X r` (built from `TopCat.Sheaf.constantFunctor`). Both sides are `extendMap` of `single₀.map` of the constant-sheaf map of `ofHom (mulLeft r)`, and the kernel accepts `rfl`. Since upstream's ℚ-action is defined from `mulLeft q`, the equation is the intended one. It also serves as a pin: an upstream respelling of `fieldScalarSheaf` breaks the build here.
   - `hypercohomologyAddEquivConstantCohomology_symm_smul` is stated for `q • α` with upstream's `SMul K (H^n(X; K))`, the one that `fieldCohomologyModule` is built from by `Module.ofMinimalAxioms`; in `hrel` the scalar comes from `hv`'s module, and `linearIndependent_iff'.mp hv s _ hrel` typechecks only if the two agree. They are the same action.
   - `smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt` rewrites `g j • ι (v j)` with upstream's `deRham_complex_smul_eq`, the action of `deRhamHypercohomologyComplexModule` (finding 1).
   - `set_option backward.isDefEq.respectTransparency false` is set on `constantCoefficientSheafComplexIntMap_comp` and on `linearIndependent_fieldToDeRhamCohomology_rat_of_smooth`. The option changes elaboration only; every term is rechecked by the kernel. The rung's own theorem is outside both blocks, and its statement re-elaborated without the option is closed by `with_reducible exact` with the declaration (scratch). The two hypercohomology spellings `ℍ^n(X; constantFieldSheafComplexInt ℚ X)` and `ℍ^n(X; constantCoefficientSheafComplexInt X ℚ)` agree by unfolding, which is the reason for the option, the same finding as in `de-rham-rational-span`.

4. **Axioms, trivial proofs, unused hypotheses.** All eight declarations: `[propext, Classical.choice, Quot.sound]`. Two short proof attempts fail (table above). Hypotheses: `hv` is used (the family `![x, x]` has a dependent image, so it cannot be dropped); `IsIntegral` and `Smooth` are needed for `ι` to exist. `IsProjective` is unused in the rung's theorem by design: it is the ledger's hypothesis, and the stronger `_of_smooth` theorem is the one proved. That is no vacuity sign, since the stronger statement is true (finding 2). The conclusion is not vacuous: ℙ² satisfies all three instances, and the singleton family [pt] is an instance with nonzero image (scratch).

5. **Ledger `depends_on`: the prover's proposal is incomplete.** The proof calls `constantCoefficientSheafComplexIntMap X (ratScaled z)` and `constantCoefficientSheafComplexIntMap X φ.toAddMonoidHom` with additive maps that are not ring maps. Before #192 that definition took `f : R →+* S` (diff of `SingularCochainCoefficientChange.lean`, the section variable at line 67), and these calls would not typecheck. The in-place generalization is the content of `betti-additive-naturality`. The sketch's sentence "The ledger's dependency on `betti-additive-naturality` is not used" is wrong as worded: that rung's theorem `scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange` is unused, and its generalized definitions are used. The proof also uses `smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt` from `HodgeLadder.Hodge.DeRhamRationalSpan`, a checked lemma that does not depend on `SimplicialComplexSpan` (standard axioms in the span red team, finding 5, and here through the main theorem). Required: `depends_on: ["betti-additive-naturality", "de-rham-rational-span"]`. A `checked` rung depending on a `stated` one has precedent in the ledger (for example `equality-reductions` on `known-half-statement`), and the note below says which part is used.

6. **Decision 0011.** `constantCoefficientSheafMap_comp` and `constantCoefficientSheafComplexIntMap_comp` (functoriality of the port's change of coefficients in additive maps) and `toAddMonoidHom_comp_ratScaled` (a ℚ-linear functional after `ratScaled z` is `mulLeft (φ z)`) are general lemmas with no counterpart in the port, upstream or Mathlib at the pin (grep for `_comp` lemmas on these names in `port/` and upstream: none; Mathlib supplies only `Functor.map_comp`). They need a row in `docs/gaps.md` "General lemmas kept local". `constantCoefficientSheafComplexIntMap_mulLeft` is a `rfl` pin between a port definition and an upstream one and belongs in the same row, so a pin bump looks at it first.

7. **Equality first.** The rung is an injectivity, a step toward the identity `ℂ ⊗_ℚ H^n(X; ℚ) ≃ₗ[ℂ] H_dR^n(X)` by `liftBaseChange` (bijectivity, no scalar). No rung for that identity exists. The scratch proved it from the span equality in five lines and the rank equality in two more, and the projective case from `SimplicialComplexSpan` with standard axioms, so it can be posted now as `stated` with the `Prop`-and-conditional pattern, and becomes `checked` with `simplicial-complex-span`. Proposed rung `de-rham-rational-base-change` (foundation, stated, depends on `de-rham-rational-independent`, `de-rham-rational-span`):

   ```lean
   theorem bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_span
       [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
       (hspan : Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤) :
       Function.Bijective (LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n))
   theorem finrank_deRham_eq_finrank_rat_of_simplicialComplexSpan (hS : SimplicialComplexSpan)
       [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
       Module.finrank ℂ H_dR^n(X) = Module.finrank ℚ H^n(X; ℚ)
   ```

   The scratch proofs: bijectivity is `⟨injective_liftBaseChange_…_of_smooth X n, _⟩` with `LinearMap.range_eq_top`, `Submodule.span_le` and `⟨1 ⊗ₜ x, by simp; rfl⟩`; the rank is `LinearEquiv.ofBijective` with `Module.finrank_baseChange`. `de-rham-p2-top-rank` could then depend on it.

7b. **Non-vacuity test.** Existing and smallest: the singleton [pt] on ℙ² (scratch, two lines, from `HodgeLadder.Tests.projectivePlane_point_class_ne_zero` and `linearIndependent_unique_iff`). It does not separate this rung from `de-rham-injective`, because every Betti number of ℙ² is at most 1, and in rank one ℂ-independence of a single vector is nonvanishing. A test that would fail for an injective map that is not ℂ-independent (the √2 example) needs two ℚ-independent classes in one degree. Optional test rung `de-rham-rational-independent-test-gm2`: on `HodgeLadder.Tests.gm2` (smooth integral, not projective, so through `_of_smooth`), `LinearIndependent ℂ (fieldToDeRhamCohomology ℚ gm2 1 ∘ ![sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero, sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero])`. Its missing input is ℚ-independence of the two winding classes in `H^1(gm2; ℚ)`, which the ladder does not have at this commit (`gm2_cup_ne_zero` and `gm2_cup_swap_ne` give nonvanishing and x₁ ≠ x₂ only). Not required for this rung.

8. **Pin drift. None.** `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are unchanged between `16f29dc` (the span red team's base) and `0a5c936`; `.lake/packages/HodgeConjecture` is at `2ead713`. The upstream definitions the rung depends on (`fieldCohomologyModule`, `field_smul_eq`, `fieldScalarSheaf`, `fieldScalarComplex`, `hypercohomologyAddEquivConstantCohomology_symm_smul`, `deRhamHypercohomologyComplexModule`, `fieldToDeRhamCohomology`, `fieldToDeRhamCohomologyLinear`, `complexConstantCohomologyDeRhamAddEquiv`) were read at that commit. The port changed between those commits only by the #192 generalization, which the proof needs (finding 5).

9. **Conventions.** Used, with truth dependence:

   | Convention | Row in `docs/conventions.md` | Truth depends on it? |
   |---|---|---|
   | ℂ-structure on `H_dR^n(X)` | "Complex structure on H_dR and on complex constant cohomology" (annotated by this pass) | no: a conjugated action has the same independent families |
   | ℚ-structure on `H^n(X; ℚ)` | "Rational structure on constant-sheaf cohomology" (added by this pass) | no: a ℚ-module structure on an abelian group is unique |
   | `ι` = `algebraMap ℚ ℂ` then constants into 0-forms | "Rational-to-de Rham map and the range of F^p" | no: a nonzero scalar on `ι` preserves independence |
   | change of coefficients along `ratScaled z` and along φ | "Change of coefficients along an additive map" | no: the identities used are exact, and any sign would cancel in a relation equal to 0 |

   No cited result is assumed: every input is checked Lean at the pin.

## Required changes

1. **Root import.** Add `public import HodgeLadder.Hodge.DeRhamRationalIndependent` to `HodgeLadder.lean`, then run `python3 tools/check.py` with the build.

2. **Ledger entry** for `de-rham-rational-independent`:

   | Field | Value |
   |---|---|
   | status | `checked` |
   | module | `HodgeLadder.Hodge.DeRhamRationalIndependent` |
   | declarations | `HodgeLadder.linearIndependent_fieldToDeRhamCohomology_rat`, `HodgeLadder.linearIndependent_fieldToDeRhamCohomology_rat_of_smooth`, `HodgeLadder.injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat`, `HodgeLadder.injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_smooth` |
   | depends_on | `betti-additive-naturality`, `de-rham-rational-span` |
   | contributors | `claude-code` |

   Note text: "Checked 2026-11-27, standard axioms. The `_of_smooth` theorems need only IsIntegral and Smooth; IsProjective is unused, and no finiteness, Hausdorffness or comparison with singular cohomology enters. Route: a ℚ-linear functional φ : ℂ → ℚ is an additive map of coefficients; pushing a relation Σ zᵢ • ι vᵢ = 0, read in complex constant cohomology through smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt and complexConstantCohomologyDeRhamAddEquiv, along φ gives Σ φ(zᵢ) • vᵢ = 0. Uses the port's additive constantCoefficientSheafComplexIntMap (generalized in betti-additive-naturality; that rung's comparison theorem is not used) and the checked step-1 lemma of de-rham-rational-span (not SimplicialComplexSpan). Independence over ℂ, insensitive to conjugating the ℂ-action and to nonzero scalars on ι. Red team 2026-11-27: docs/sketches/de-rham-rational-independent.redteam.md." Bump `updated`.

3. **`docs/gaps.md`, "General lemmas kept local"**, one row:

   | Local declaration | Module | Why local | Opened |
   |---|---|---|---|
   | `HodgeLadder.constantCoefficientSheafMap_comp`, `HodgeLadder.constantCoefficientSheafComplexIntMap_comp` (the port's change of coefficients on the constant sheaf and on the integer-indexed complex composes along additive maps); `HodgeLadder.toAddMonoidHom_comp_ratScaled` (φ ∘ ratScaled z = mulLeft (φ z) for φ : ℂ →ₗ[ℚ] ℚ); `HodgeLadder.constantCoefficientSheafComplexIntMap_mulLeft` (`rfl` pin: along `mulLeft r` it is upstream's `fieldScalarComplex ℚ X r`) | `HodgeLadder.Hodge.DeRhamRationalIndependent` | no composition lemma for these port definitions in the port, upstream or Mathlib at the pin; the pin ties the port's constant-sheaf spelling to upstream's ℚ-action; a pin bump or re-port checks for upstream versions and reruns the `rfl`; used by `de-rham-rational-independent` | 2026-11-27 |

4. **Sketch** (`docs/sketches/cup-hodge-filtration.md`). (a) In "de-rham-rational-independent: statement", replace the sentence "The ledger's dependency on `betti-additive-naturality` is not used." and the two sentences after it with: "The proof does not use the comparison theorem of `betti-additive-naturality`; it uses that rung's generalization of `constantCoefficientSheafComplexIntMap` to additive maps, and the checked step 1 of `de-rham-rational-span`. Dependencies: `betti-additive-naturality`, `de-rham-rational-span`." (b) In the proposed ledger table of that section, set "Depends on" to `betti-additive-naturality`, `de-rham-rational-span` and "Status" to checked after this pass. (c) In the sub-rung table of the `de-rham-rational-span` section (the row now reading "open | `betti-additive-naturality` | statement in red team finding 1"), set status checked, the same dependencies, and the module.

5. **Roadmap row and status block** per the propagation map for a proved rung.

Recommended, not required: post `de-rham-rational-base-change` (finding 7) as a `stated` rung with the conditional statements above, since T1's eigenspace count reads the rank equality and the scratch proof is 12 lines; and the optional `gm2` test of finding 7b.
