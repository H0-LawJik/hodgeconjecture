# Red team: `supported-pair-forget` (statement pass)

Date: 2026-11-26. Worktree at `8b3a2fa` plus the uncommitted `HodgeLadder/Cup/SupportedPairForget.lean` and the sketch section "supported-pair-forget: statement" in `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Targets: (a) `HodgeLadder.Cup.forgetRel_supportedEquivPair`, (b) `HodgeLadder.Cup.supportedEquivPair_eq_transport`, and the helpers `ofSubsetIsoNeighborhoodUniv`, `ofSubsetIsoNeighborhoodUniv_fst_apply`, `ofSubsetIsoNeighborhoodUniv_hom_comp_inv`, `forgetRel_relativeCohomologyMap`. Inputs read: the new file; `SupportedPair.lean` (`topPairIso`, `pairCohIso`, `fst_topOpen`, `supportedEquivPair`); `SupportedForgetFinal.lean` (`supported_forget_compat`); `SupportedAgreement.lean` (`transport_eq_flasqueModel`); `RelativeCup.lean` (`forgetRel`); `Normalization/Singular.lean`, `Normalization/Germ.lean` (the consumers' spelling); the ledger entries of this rung, `cup-comparison-supported-pair`, `supported-forget-compat`, `supported-model-agreement`, `triad-relative-cup`, `cycle-class-multiplicative`; conventions row "Supported comparison Φ". Upstream at the pin: `Support/SingularSectionCohomology.lean` (`openIntersectionPairIsoSupportComplement`, `supportedRationalSingularSectionCohomologyEquivRelative`, `…SupportComplement`), `Cycle/Transport/CohomologySheaf.lean` (`complexSupportInjectiveSectionCohomologyEquiv`), `LocalHomology/FundamentalClass.lean` (`neighborhoodSupportComplementPair`, an `abbrev` for `TopPair.ofSubset (X := TopCat.of W) {w | w.1 ∉ S}`), `Mathlib/Topology/Category/TopPair.lean` (`isoOfSubset`), `Cohomology/WithSupport.lean` (sheaf `forgetSupport`), `Singular/Cohomology.lean` (`relativeCohomologyMap_comp`, `relativeCohomologyToAbsolute`, singular `forgetSupport`, `CohomologyWithSupport`), `Cycle/FundamentalClass.lean` (`cycleComponentSheafClass`), `Other/…/GlobalSections.lean` (Ψ), `ComplexPoint/ProjectiveParacompact.lean`, `ComplexPoint/ProjectiveHausdorff.lean`.

Scratch: two files in the worktree root, compiled with `lake env lean` and deleted. To import `HodgeLadder.Normalization.Germ` the three local modules `Normalization.{ChartStep,Singular,Germ}` were built in the worktree (67 s; `lake build --no-build` first confirmed that no upstream or Mathlib module needed building). Nothing under `.lake/packages` was touched; `SupportedForget` was not rebuilt.

**Verdict: pass with changes.** Both statements are true, exact, sign-free, and the relocations `cycle-class-multiplicative` needs: scratch proves (a) and (b) verbatim in four to five lines each from the checked `supported_forget_compat` and `transport_eq_flasqueModel`, and both are non-vacuous on upstream's own cycle classes. The prover's flag finds a real seam with a second half: (b) is well typed only through default-transparency unfolding of the domain spelling `(↑Z)ᶜ` against `↑Z.compl`, a seam `rw` cannot see through, and it already breaks one-line downstream rewrites. Change A (re-spell the helper iso on both ends) removes it; scratch checks the changed statement, its proof and the downstream rewrites.

## 1. Is this the statement of the literature?

Literature fact: for X a space, Z closed, the comparison H^n_Z(X; ℚ) (sheaf cohomology with supports) ≅ H^n(X, X ∖ Z; ℚ) commutes with forgetting supports against the absolute comparison H^n(X; ℚ_X) ≅ H^n_sing(X; ℚ), and is natural under restriction to opens (`Iversen1986`, `Bredon1997`; sections unverified). (a) is the square; (b) says the two Lean models of the supported comparison (this repository's Φ and upstream's cycle-class transport) agree after identifying the pairs.

| Literature | Lean | Local or upstream |
|---|---|---|
| H^n_Z(X; ℚ) | `H_[Z]^n(X; ℚ)` = `TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) Z ℚ_X n` | upstream |
| forget supports, sheaf side | `forgetSupport ℚ X Z n` elaborates to `AlgebraicGeometry.ComplexPoint.forgetSupport` (checked with `pp.fullNames`), the map in upstream's definition `cycleComponentSheafClass = forgetSupport ℚ X Z_x (2p) (cycleComponentSupportedInjectiveClass X x hx)` | upstream |
| H^n(X; ℚ_X) ≅ H^n_sing(X; ℚ) | Ψ = `rationalCohomologyAddEquivSingularCohomology X n`, codomain `Cohomology ℚ (TopCat.of (ComplexPoint X)) n`, that is, on X itself | upstream `Other` |
| H^n(X, X ∖ Z) → H^n(X) | `forgetRel P n` = `ModuleCat.ofHom (relativeCohomologyToAbsolute ℚ P n)` (scratch: `rfl`); on `P = TopPair.ofSubset Sᶜ` it is upstream's singular `forgetSupport ℚ Y S n` (scratch: `rfl`) | local name for an upstream map |
| pair (X, X ∖ Z) | `TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (Z.compl : Set (ComplexPoint X))`, the codomain pair of `supportedEquivPair` with the same elaborated term (rewrite test in the spelling of `cup_singular_comparison_supported_pair` passes) | upstream constructor |
| Φ | `supportedEquivPair X Z n` = `flasqueModel` then upstream's `supportedRationalSingularSectionCohomologyEquivRelative … Z.compl ⊤ n` then `pairCohIso` | local, checked |
| upstream's transport T | `complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ n ∘ rationalSupportAddEquivSupportedInjectiveHomology X Z n`, into `RelativeCohomology ℚ (neighborhoodSupportComplementPair ((⊤ : Opens _) : Set _) Z) n`, the form of `normalization_singular` and `cycle-class-germ` | upstream |
| identification of pairs | `ofSubsetIsoNeighborhoodUniv S` = `isoOfSubset (Homeomorph.Set.univ Y).symm`, identity on points | local helper over upstream `isoOfSubset` |

(a) reads Ψ on X, which is what step 2 of `cycle-class-multiplicative` needs: scratch closes `Ψ (cycleComponentSheafClass X x hx) = forgetRel (TopPair.ofSubset …) (2p) (supportedEquivPair X Z_x (2p) (cycleComponentSupportedInjectiveClass X x hx))` by `exact (forgetRel_supportedEquivPair X _ _ _).symm`. The checked `supported_forget_compat` reads Ψ on the open ⊤ through `singularCochainComplexIsoTopOpen`; (a) removes that read-off with the checked `fst_topOpen`.

## 2. Can the hypotheses be satisfied?

Yes. `HodgeLadder.Tests.exists_smooth_projective_integral : ∃ X : Over (Spec ↧ℂ), IsIntegral X.left ∧ Smooth X.hom ∧ IsProjective X.hom` (checked, Spec ℂ). For projective X, `T2Space (ComplexPoint X)` is upstream's instance `IsProjective.complexPoint_t2Space` (scratch: `show_term infer_instance`), and `∀ U, ParacompactSpace U` is upstream's `openParacompactSpace X`. Any closed Z works, for example `cycleComponentAnalyticClosedSupport X x`.

Hypotheses per statement: (a) carries `[T2Space]`, `[∀ U, ParacompactSpace U]` and no `IsProjective`; both instances are needed to form Φ and Ψ, and the statement is the more general for not assuming projectivity. (b) carries `IsProjective`, which upstream's transport requires (its section variables); `T2Space` for Φ is then found from `IsProjective`. The `[∀ U, ParacompactSpace U]` binder of (b) is implied by `IsProjective` through `openParacompactSpace X`; it is a `Prop` instance, so any two inhabitants agree and the binder costs a caller one `letI := openParacompactSpace X` (the pattern of `Normalization/Singular.lean`). Keep it.

## 3. Trivially true?

No route unrelated to the mathematics closes either statement. Tried in scratch:

| Attempt | Result |
|---|---|
| (a) `simp [supportedEquivPair, forgetRel]` | unsolved goal |
| (a), (b) `rfl`, `exact supported_forget_compat …`, `exact transport_eq_flasqueModel …` | fail (prover's record; the checked statements live on other pairs) |
| `RelativeCohomology` or `H_[Z]^n` subsingleton, a hypothesis unused, a definition unfolding to `True` | none: section 7b exhibits nonzero values of both sides |

Both statements do have short proofs, and the proofs go through the substantive checked lemmas, which is what a relocation rung should look like. Scratch, compiled at the pin:

```lean
-- (a), verbatim statement
set_option backward.isDefEq.respectTransparency false in
  refine (forgetRel_relativeCohomologyMap (topPairIso (TopCat.of (ComplexPoint X)) Z.compl).hom n
    (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤ n
      (flasqueModel X Z n α))).trans ?_
  rw [supported_forget_compat X Z n α]
  exact fst_topOpen _ _ _ _

-- (b), verbatim statement (and the same four lines for change A with the renamed helper)
set_option backward.isDefEq.respectTransparency false in
  rw [transport_eq_flasqueModel]
  have e := congrArg (fun f => relativeCohomologyMap ℚ n f) (ofSubsetIsoNeighborhoodUniv_hom_comp_inv Z)
  simp only [relativeCohomologyMap_comp] at e
  exact (LinearMap.congr_fun e _).symm
```

The planned route for (b) in the sketch (`change` to the two pullbacks, then `rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, …]`) fails at the first rewrite as currently stated; see finding 2. The `change` step itself succeeds, which confirms that upstream's `…SupportComplement` unfolds to R followed by `relativeCohomologyMap ℚ n (openIntersectionPairIsoSupportComplement _ Z Z.isClosed ⊤).inv`.

## 4. Interface axioms

Not an interface rung; no structure, no axioms.

## 5. Axioms of the proved helpers

`#print axioms` in scratch, for `ofSubsetIsoNeighborhoodUniv`, `ofSubsetIsoNeighborhoodUniv_fst_apply`, `ofSubsetIsoNeighborhoodUniv_hom_comp_inv`, `forgetRel_relativeCohomologyMap`: each `[propext, Classical.choice, Quot.sound]`. `tools/check.py` was not run: the module is not yet imported from `HodgeLadder.lean` and the rung is `open`, so the checker names none of these declarations.

## 6. Conventions

| Convention | Where | Check | Truth depends on it? |
|---|---|---|---|
| Φ (row "Supported comparison Φ") | `supportedEquivPair` | used as checked; no new choice | (a), (b) are identities, so yes; both are exact relocations of checked identities with no sign |
| Ψ (row "Sheaf–singular comparison Ψ") | upstream `Other` | (a) reads it on X, the codomain of the definition itself | yes; no change of model |
| Upstream transport T (row "Normalization iso against the singular transport") | upstream | (b) uses T at V = ⊤ in the exact spelling of `normalization_singular` | yes; no sign added |
| Forget supports | sheaf: upstream `forgetSupport` (restriction along `Z.compl ≤ ⊤` then `addEquivTerminal`); singular: dual of `relativeChainProjection` | both are the upstream maps; `forgetRel` is `relativeCohomologyToAbsolute` by `rfl` | yes; neither carries a sign |
| Pair isomorphisms | `ofSubsetIsoNeighborhoodUniv`, `topPairIso`, `openIntersectionPairIsoSupportComplement` | each is the identity on points on both components (`_fst_apply` by `rfl`, `_hom_comp_inv` by `ext; rfl`); the induced chain maps are maps of singular simplices along identities, so their duals introduce no sign | an identity on points cannot change a sign or scalar |
| Pair spellings of (X, X ∖ Z) | four spellings, see the new row "Pair spellings of (X, X ∖ Z)" | added by this pass | no effect on truth; decides which rewrites work (finding 2) |

## 7. Equality first

Both targets are identities, stated exactly: no scalar, no sign, no "up to". The degree is the same `n` on both sides, and (a) confirms there is no degree twist between Φ and Ψ (as `supported_forget_compat` already did on ⊤). They are steps toward the identity `[Z] ∪ [W] = [T]` (rung `cycle-class-multiplicative`, open); (a) feeds its step 2, (b) its step 4.

## 7b. Non-vacuity

The smallest tests, both compiled in scratch at projective X with `letI := openParacompactSpace X`, neither yet in the tree:

* (b): `supportedEquivPair X (cycleComponentAnalyticClosedSupport X x) (2 * p) (cycleComponentSupportedInjectiveClass X x hx) ≠ 0` for every scheme point x, from (b), `relativeCohomologyMap` of the inverse iso, and the checked `HodgeLadder.Normalization.toSheaf_transport_supportedClass_ne_zero`. Both sides of (b) are then nonzero.
* (a): at the generic point, `forgetRel (TopPair.ofSubset …) (2 * 0) (supportedEquivPair X Z_η (2 * 0) (cycleComponentSupportedInjectiveClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))) ≠ 0`, from (a), Ψ injective, upstream's `forgetSupport_injective_of_eq_top` with `cycleComponentAnalyticClosedSupport_genericPoint_eq_top` (`Other`), and the checked `HodgeLadder.Normalization.normalization_genericPoint_ne_zero`. Both sides of (a) are then nonzero.

They would fail if either side were identically zero. Change C puts them in the tree.

## 8. Pin drift

None. Every dependency (`supported-forget-compat`, `supported-model-agreement`, `cup-comparison-supported-pair`, `normalization-singular`, `cycle-class-germ`) was checked at `2ead713`, the current pin, and the upstream declarations read above are at that commit.

## Findings

1. **The statements are the right relocations.** (a) is `supported_forget_compat` with ⊤ replaced by `TopPair.ofSubset` and Ψ read on X; (b) is `transport_eq_flasqueModel` with upstream's (⊤, ⊤ ∖ Z) pulled back to `TopPair.ofSubset`. Both proved verbatim in scratch from the checked lemmas (section 3). The LHS pair of (a) is the pair of `supportedEquivPair` term for term: `rw [forgetRel_supportedEquivPair]` fires on a goal spelled as in `cup_singular_comparison_supported_pair`.
2. **The spelling gap in (b) has two seams, and one of them blocks `rw`.** Codomain: `neighborhoodSupportComplementPair Set.univ ↑Z` against upstream's `… ((⊤ : Opens _) : Set _) ↑Z`. Scratch: `((⊤ : Opens Y) : Set Y) = Set.univ` fails `with_reducible rfl` and passes `with_reducible_and_instances rfl`, so `rw` and `simp` (instances transparency for keyed matching) see through it, and a downstream rewrite through `neighborhoodSupportInclusionPairMap (V := ↑⊤)` worked. Domain: `ofSubsetIsoNeighborhoodUniv (Z : Set _)` starts at `TopPair.ofSubset (↑Z)ᶜ`, while `supportedEquivPair` lands in `TopPair.ofSubset ↑Z.compl`; `(↑Z.compl : Set Y) = (↑Z)ᶜ` passes plain `rfl` and fails `with_reducible_and_instances rfl` (`Closeds.compl` is a plain `def`). So the two sides of (b) live in syntactically different types, and (b) elaborates only because `Eq` unifies them at default transparency. Observed failures: the sketch's planned `rw [← LinearMap.comp_apply, …]` for (b) ("target expression is not type-correct under the `implicit` transparency level": `H^n(…, ↑Z.compl; ℚ)` against `H^n(…, (↑Z)ᶜ; ℚ)`), and, downstream, `rw [map_zero] at h'` on `relativeCohomologyMap ℚ _ (ofSubsetIsoNeighborhoodUniv _).inv 0` in the non-vacuity test. Term-mode `exact` and `.trans` work around both. Under change A the same tests pass with plain `rw`.
3. **The statement is well typed for the right reason.** The identification is the identity on points (`_fst_apply` by `rfl`; `_hom_comp_inv` by `ext; rfl` against `topPairIso`), so no sign or scalar can enter (section 6).
4. **Hypotheses are correct.** `IsProjective` in (b) only; `T2Space` in (a) only, found from `IsProjective` in (b); the paracompact binder of (b) is redundant and harmless (section 2).
5. **Non-vacuous** on upstream's cycle classes, both statements (section 7b).
6. **Same seam ahead in `cycle-class-multiplicative`.** Its sketch states `unionComplIso` on `Zᶜ ∪ Wᶜ` and `Tᶜ` for `Z W T : Set Y`. `relCup2` of two Φ-classes will land on `TopPair.ofSubset (↑Z.compl ∪ ↑W.compl)`, which `unionComplIso (Z := ↑Z)` reaches only at default transparency, as in finding 2. Not a defect of this rung; see change D.
7. **Sketch inaccuracy.** The sketch says "the ledger entry names `HodgeLadder.Supported.Pair.Forget`"; the ledger entry has `"module": null`. Fix the sentence when posting.

## Recommended changes

A (required). Replace the pair helper by one whose endpoints are spelled as `supportedEquivPair` and as upstream's transport at V = ⊤, and restate (b) with it. Compiled in scratch at the pin, with the four-line proof of section 3:

```lean
/-- The isomorphism of pairs `(Y, Y ∖ Z) ≅ (⊤, ⊤ ∖ Z)` given by the identity of `Y`. The domain is
spelled as the codomain of `supportedEquivPair`, the codomain as upstream's
`neighborhoodSupportComplementPair` at `V = ⊤`, the target of
`complexSupportInjectiveSectionCohomologyEquiv X Z ⊤`. -/
def ofSubsetIsoNeighborhoodTop {Y : Type} [TopologicalSpace Y] (Z : Closeds Y) :
    TopPair.ofSubset (X := TopCat.of Y) (Z.compl : Set Y) ≅
      neighborhoodSupportComplementPair ((⊤ : Opens Y) : Set Y) (Z : Set Y) :=
  TopPair.isoOfSubset (Homeomorph.Set.univ Y).symm (fun _ => Iff.rfl)

theorem ofSubsetIsoNeighborhoodTop_hom_comp_inv {Y : Type} [TopologicalSpace Y] (Z : Closeds Y) :
    (ofSubsetIsoNeighborhoodTop Z).hom ≫
        (openIntersectionPairIsoSupportComplement (TopCat.of Y) Z Z.isClosed ⊤).inv =
      (topPairIso (TopCat.of Y) Z.compl).hom := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl

theorem supportedEquivPair_eq_transport [IsProjective X.hom]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    supportedEquivPair X Z n α =
      relativeCohomologyMap ℚ n (ofSubsetIsoNeighborhoodTop Z).hom
        (complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ n
          (rationalSupportAddEquivSupportedInjectiveHomology X Z n α))
```

Add the `_fst_apply` lemma for the new name (`rfl`). The general `ofSubsetIsoNeighborhoodUniv (S : Set Y)` may stay as a helper for `Set`-spelled consumers; it should not appear in (b). Update the ledger note and the sketch table, which name `ofSubsetIsoNeighborhoodUniv`.

B (recommended). Keep the generic inverse lemma used in the downstream tests, so consumers move between the two sides of (b) by `rw`:

```lean
theorem relativeCohomologyMap_inv_hom_apply {P Q : TopPair.{0}} (e : P ≅ Q) (n : ℕ)
    (x : RelativeCohomology ℚ Q n) :
    relativeCohomologyMap ℚ n e.inv (relativeCohomologyMap ℚ n e.hom x) = x := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, e.inv_hom_id, relativeCohomologyMap_id]
  rfl
```

C (required for posting). Add the two non-vacuity tests of section 7b as named theorems, in a module that may import `HodgeLadder.Normalization.Germ` and `Other.AlgebraicGeometry.Hodge.CodimensionZeroComparison` (for example `HodgeLadder/Tests/SupportedPairForget.lean`), and name them in the ledger entry. The scratch proof of the (b) test under change A:

```lean
  letI := openParacompactSpace X
  intro h
  apply toSheaf_transport_supportedClass_ne_zero X x hx
  rw [supportedEquivPair_eq_transport] at h
  have h' := congrArg (relativeCohomologyMap ℚ _ (ofSubsetIsoNeighborhoodTop
    (cycleComponentAnalyticClosedSupport X x)).inv) h
  rw [relativeCohomologyMap_inv_hom_apply, map_zero] at h'
  rw [h', map_zero]
  exact map_zero _
```

and of the (a) test:

```lean
  letI := openParacompactSpace X
  rw [forgetRel_supportedEquivPair]
  intro h
  apply normalization_genericPoint_ne_zero X
  have h1 := (rationalCohomologyAddEquivSingularCohomology X _).injective (h.trans (map_zero _).symm)
  have h2 := forgetSupport_injective_of_eq_top ℚ X _
    (cycleComponentAnalyticClosedSupport_genericPoint_eq_top X) _ (h1.trans (map_zero _).symm)
  rw [h2, map_zero]
```

D (for `cycle-class-multiplicative`, not this rung). State `unionComplIso` for `Z W T : Closeds Y` with `hT : T = Z ⊓ W`, on `TopPair.ofSubset ((Z.compl : Set Y) ∪ (W.compl : Set Y)) ≅ TopPair.ofSubset (T.compl : Set Y)`, so that it meets `relCup2` of two `supportedEquivPair` classes term for term; and spell `triad-relative-cup`'s pairs so that `A := (Z.compl : Set Y)` is accepted without unfolding. Untested in scratch.

E. Fix the sketch sentence of finding 7.
