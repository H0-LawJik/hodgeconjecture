# Red team: `supported-pair-named` (R5 of `supported-pullback-transport`, issue #260)

Date: 2026-11-28. Candidate `958222b` on `track/supported-pair-named`: `HodgeLadder/Supported/Pair/Named.lean` (namespace `HodgeLadder.Supported`), declarations `supportedEquivPair_of_named`, `exists_named`, `exists_supportedEquivPair_eq` and two local instances `namedHasDerivedCategory`, `namedSiteHasDerivedCategory`. Not root-imported, not in the ledger. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the pin of `main` at `d1c59da` (the branch adds one file over `d1c59da`, so there is no drift to check). Inputs read: the new file; `docs/sketches/supported-pullback-transport.md` (R5 statement, table, kill criteria, signs table); `HodgeLadder/Cup/SupportedConeCompat.lean` (`supported_singular_class_hom`, `supported_singular_class`); `HodgeLadder/Cup/SupportedFinal.lean` (`flasqueModel`, `supCocycle`, `exists_supported_rep`); `HodgeLadder/Cup/SupportedStep2.lean` (`relHSupportedOfFlasque_mk`); `HodgeLadder/Cup/SupportedPair.lean` (`topPairIso`, `pairCohIso`, `supportedEquivPair`); `HodgeLadder/Cup/SupportedPairForget.lean` (`supportedEquivPair_eq_transport`); `HodgeLadder/Supported/SingularCochainPullback.lean` (`RelCochain`, `PairCocycle`); R3 on `track/supported-pullback-named` (`PullbackNamed.lean`, instance choice); upstream `Definitions/AlgebraicTopology/Singular/RelativeCochainCone.lean`, `RelativeCochainConeNaturality.lean` and `Lemmas/.../RelativeCochainConeNaturality.lean` (`relativeDualCochainCohomologyEquiv`, `relativeDualCochainHomologyIsoCone`, `relativeDualCochainCohomologyEquiv_naturality`); `docs/conventions.md` rows "Supported comparison Φ", "Pair spellings of (X, X ∖ Z)", "Hom-complex composition and derived classes"; `docs/gaps.md`.

Scratch: `scratch-rt-spn/` in the worktree (four files, compiled with `lake env lean`, deleted at the end). Nothing under `.lake/packages` touched.

**Verdict: pass with changes.** The statement is the sketch's R5 verbatim, exact, with no sign and no scalar, and its right side uses the identifications inside `supportedEquivPair` itself (`topPairIso`, upstream's `relativeDualCochainCohomologyEquiv`, `mapHomologyIso`), the form R6 needs with upstream's `relativeDualCochainCohomologyEquiv_naturality`. The hypothesis `hβ` is used and satisfiable; a nonzero instance costs 12 lines and compiles. The kill criterion does not fire. Changes: a nonzero lemma, the sketch's module name, R3's derived-category instances, lower heartbeat options, a precise sign sentence, and ledger, gaps and conventions text.

## Findings

1. **Statement against the sketch.** The Lean statement of `supportedEquivPair_of_named` equals the sketch's R5 block term for term (`β`, `y : RelCochain X Z p`, `hy` on `(relSeq … Z.compl ⊤).X₁.d`, `hβ` naming `β.hom ≫ (Q.map (iotaQ X))⟦p⟧'` by `ShiftedHom.map (equivHomShift.symm (supCocycle X Z ((rawMap …).τ₁.f p y) _)) Q`, right side `relativeCohomologyMap ℚ p (topPairIso _ Z.compl).hom (relativeDualCochainCohomologyEquiv ℚ (openInclusionPair _ (Opens.infLELeft ⊤ Z.compl)) p ((mapHomologyIso … (forget₂ …)).hom (cls _ p (p+1) _ y hy)))`). `Z` comes from a section variable; the elaborated signature is the same.

2. **Literature reading.** The fact is the computation of the comparison H^p_Z(X; ℚ) ≅ H^p(X, X ∖ Z; ℚ), built from the resolution of ℚ_X by sheafified singular cochains, on a class represented by a relative cocycle: the comparison sends it to the relative class of that cocycle [`Bredon1997`, ch. III; `Iversen1986`; sections unverified, as in the sketch]. Field by field: H^p_Z is upstream's `H_[Z]^p(X; ℚ)`; "represented by y" is `hβ` (the Hom-complex cocycle `supCocycle (rawMap y)` out of the pair sheaf ℤ[X, X ∖ Z] names β after the augmentation `iotaQ X`); "the relative class of y" is upstream's `relativeDualCochainCohomologyEquiv`, which is `extendHomologyIso` of the relative dual-cochain complex (no cone, no sign: read at the pin), moved along `forget₂` by `mapHomologyIso` and to `TopPair.ofSubset (Z.compl)` by `topPairIso`, the identity on points (conventions row "Pair spellings", spelling (1)).

3. **Form needed by R6.** R6 states `supportedEquivPair X' Z' n (supportedPullback g … α) = relativeCohomologyMap ℚ n (TopPair.ofSubsetHom (pointMap g) _) (supportedEquivPair X Z n α)` (ledger note of `supported-pullback-transport`), so both sides go through `supportedEquivPair`, whose last step is `pairCohIso` = `relativeCohomologyMap` along `topPairIso.hom` (`pairCohIso_hom_apply`, `rfl`). R5's right side uses exactly that iso, and its inner term is in the domain of upstream's `relativeDualCochainCohomologyEquiv_naturality` (`(relativeDualCochainShortComplexInt R X).X₁.homology n`). R6 applies R5 once on X with `y := x` from `exists_supported_rep`, once on X' with `y := (relPullback g Z Z' hZ).f p x` and `hβ` from R3 plus R4. The coordinator's brief calls `supportedEquivPair_eq_transport` upstream's; it is local (`HodgeLadder.Cup`, rung `supported-pair-forget`) and uses the other helper `ofSubsetIsoNeighborhoodTop`, which R6 does not need: the ledger states R6 with `supportedEquivPair` on both sides, and `supportedEquivPair_eq_transport` converts to upstream's transport afterwards.

4. **Sign.** None, and there is no place for one to hide. The proof is three checked equalities: `relHSupportedOfFlasque_mk` (flasque model of a named class = class of its Hom-complex cocycle under `homComplexPairSheafIsoSupportedSections`), `cls_eq` through `e.inv_hom_id` (the iso round trip on `s₀`), and `supported_singular_class`. I read `supported_singular_class_hom`: `shortExactHomologyIsoCone` occurs at both ends, once for `supSeq` inside upstream's `supportedRationalSingularSectionCohomologyEquivRelative` and once inside upstream's `relativeDualCochainHomologyIsoCone` (definition at the pin: it is `shortExactHomologyIsoCone (relativeDualCochainShortComplexInt R X) …`). `shortExactHomologyIsoCone_naturality` along `rawMap` and `map_shortExactHomologyIsoCone` along `forget₂` match the two, and `supported_singular_class` then cancels `relativeDualCochainHomologyIsoCone` against its inverse (`Iso.hom_inv_id_apply`). Whatever ε(n) Mathlib's `rotateHomotopyEquiv` carries cancels between the two ends; R5's statement contains no cone at all. So R6's "common ε(n)" is 1 on the nose. The module docstring's phrase "where it is absent" is imprecise; change C. Kill criterion (sign or scalar in R5): does not fire.

5. **Trivial-proof attempts.** The conclusion is an equality in `RelativeCohomology ℚ (TopPair.ofSubset Z.compl) p`, a ℚ-module, with no `True`, no coercion and no empty index. Scratch `probe_hyp_used` proves that dropping `hβ` makes the statement false whenever `H_[Z]^p` has a nonzero class (β' = 0 against the cocycle of a nonzero class), so `hβ` is load-bearing. `probe_no_neg`: `supportedEquivPair β ≠ −supportedEquivPair β` for β ≠ 0, so a variant with a −1 would be false on every nonzero instance.

6. **Non-vacuity.** `exists_named` shows `hβ` is satisfiable for every relative cocycle `y`, including y = 0, so on its own it allows the trivial instance 0 = 0. A nonzero instance is cheap. Scratch `probe_nonzero_of` (12 lines, standard axioms): for every β ≠ 0 there are `y`, `hy` with `hβ` and the right side ≠ 0, from `exists_supported_rep` and injectivity of `supportedEquivPair`. With `probe_cycle` (`cycleComponentSupportedInjectiveClass X x hx ≠ 0`, three lines from `HodgeLadder.Tests.supportedEquivPair_supportedClass_ne_zero`) this gives a nonzero instance on every smooth integral projective X and every scheme point x, for example a point of ℙ¹ in degree 2. The generic lemma needs no new import; change A adds it. The concrete instance would import `HodgeLadder.Tests.SupportedPairForget` and belongs in a test file only if a consumer wants it; the ledger note can cite the two-step argument.

7. **Smallest test lemma.** The smallest lemma that fails on a trivially true statement is change A's `exists_named_ne_zero` instantiated at `cycleComponentSupportedInjectiveClass` (upstream API: `cycleComponentSupportedInjectiveClass`, `cycleComponentAnalyticClosedSupport`; ladder: `HodgeLadder.Tests.supportedEquivPair_supportedClass_ne_zero`, checked). It does not exist yet; change A.

8. **Consistency with `exists_supported_rep`.** For any α, `exists_supported_rep` yields x with `flasqueModel α = cls (rawMap x)` and α named by `supCocycle (rawMap x)`; R5 at (α, x) restates the first conjunct after `supported_singular_class`. The two uses of `Cocycle.equivHomShift` (right shift, no sign; conventions row "Hom-complex composition and derived classes") are the same in R3, R5 and `exists_supported_rep`, so the naming convention is shared.

9. **Derived-category instances.** The file defines its own `namedHasDerivedCategory`, `namedSiteHasDerivedCategory` (both `HasDerivedCategory.standard`). R3 (`PullbackNamed.lean`) activates `HodgeLadder.Cup.finHasDerivedCategory` and `finSiteHasDerivedCategory` from `SupportedFinal` so that its statement uses the same instance terms as `exists_supported_rep`. The two are defeq (scratch: `hβ` from `exists_supported_rep` passes to R5 as an argument), but R6 will meet both spellings, and the two new instances are public, exposed declarations the ledger does not name. Scratch `FinInst.lean`: the file compiles unchanged with `attribute [local instance] HodgeLadder.Cup.finHasDerivedCategory HodgeLadder.Cup.finSiteHasDerivedCategory` in place of the two instances. Change B.

10. **Heartbeats and kernel time.** `lake env lean -Dprofiler=true` at the pin: 78 s wall, 52 to 56 s of type checking (28.9 s `supportedEquivPair_of_named`, 13.6 s `exists_named`, 9.3 s `exists_supportedEquivPair_eq`), 16 s tactic execution. Below the sketch's 600 s split threshold. Scratch: with every `maxHeartbeats` removed the main theorem times out at `whnf` (200000) and `exists_named` compiles; with 1000000 on the main theorem and nothing on `exists_named` the file compiles (with R3's instances as well). CLAUDE.md forbids no heartbeat option; `supported_singular_class` uses 1000000; `exists_supported_rep` uses 2000000. Lower both; change B. `backward.isDefEq.respectTransparency false` copies `exists_supported_rep` and is acceptable; it was not tested for removal.

11. **Placement.** The sketch names the module `HodgeLadder.Supported.PairNamed` (its R5 header line), and R3 sits at `HodgeLadder/Supported/PullbackNamed.lean`; `Pair/Named.lean` is `next.py`'s fallback from a null `module`. One flat directory keeps R1 to R6 as siblings. Change D.

12. **Ledger dependencies.** The entry lists only `singular-cochain-pullback` (for the `RelCochain` abbreviation). The proof uses `exists_supported_rep`, `flasqueModel`, `supCocycle` (`cup-singular-comparison`), `relHSupportedOfFlasque_mk` (`supported-step2-cocycle-class`), `supported_singular_class` (`supported-singular-class`), `supportedEquivPair`, `topPairIso`, `pairCohIso_hom_apply` (`cup-comparison-supported-pair`), all checked. Change E.

13. **Gaps.** No general lemma: every declaration is specific to the ladder's supported comparison, so no row in "General lemmas kept local" (the #212 layout and the Layer column do not apply; `python3 tools/pinwalk.py --hubs` puts the module at layer 23, zero downstream modules). The kernel time is in the range "Known weaknesses" records (`iotaQ_comp_singularPullbackInt` 37 s, `Supported.Pullback` 164 s); change F adds one row.

14. **Conventions.** Conventions used: the Hom-complex naming `Cocycle.equivHomShift` (row exists, no sign); the cone identifications of Φ through `shortExactHomologyIsoCone` (row "Supported comparison Φ", any sign cancels, checked by `supported_singular_class`); the pair spelling (1) `TopPair.ofSubset (Z.compl : Set _)` and `topPairIso` (row "Pair spellings", identity on points); `forget₂ (ModuleCat ℚ) AddCommGrpCat` through `mapHomologyIso` (no sign; additive functor). The result is an equality, so its truth depends on each; each matches the definitions it is stated against. No new row is needed; change G appends R5's computation to the row "Supported comparison Φ".

15. **Checker.** `python3 tools/check.py --no-build` in the worktree: `ACCEPTED: all checks passed` (the new module is not root-imported, so the checker does not yet cover it). `#print axioms` in scratch on `supportedEquivPair_of_named`, `exists_named`, `exists_supportedEquivPair_eq`: `[propext, Classical.choice, Quot.sound]`. Recheck after changes A to E with the file root-imported.

16. **Pin drift.** None: the branch has the pin of `main` (`2ead713`) and adds one file over `d1c59da`.

## Required changes

A. Add to the file, after `exists_supportedEquivPair_eq` (scratch-compiled as `probe_nonzero_of`; the proof is the five lines below):

```lean
/-- **A nonzero instance**: every nonzero supported class is named by a relative cocycle whose
relative class on `(X, X ∖ Z)` is nonzero, so `supportedEquivPair_of_named` holds with both sides
nonzero. With `HodgeLadder.Tests.supportedEquivPair_supportedClass_ne_zero` this applies to
upstream's supported cycle class of every scheme point of a smooth projective `X`. -/
theorem exists_named_ne_zero {p : ℕ} (β : H_[Z]^p(X; ℚ)) (h0 : β ≠ 0) :
    ∃ (y : RelCochain X Z p)
      (hy : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) y = 0),
      β.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (supCocycle X Z ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p y)
            (map_d_eq_zero _ y hy))) DerivedCategory.Q ∧
      relativeCohomologyMap ℚ p (topPairIso (TopCat.of (ComplexPoint X)) Z.compl).hom
        (relativeDualCochainCohomologyEquiv ℚ
          (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl)) p
          ((ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
            (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl))).X₁.sc p)
            (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
            (cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) y hy))) ≠ 0 := by
  obtain ⟨y, hy, -, hβ⟩ := exists_supported_rep X Z β
  refine ⟨y, hy, hβ, ?_⟩
  rw [← supportedEquivPair_of_named X Z β y hy hβ]
  intro h
  exact h0 ((supportedEquivPair X Z p).injective (h.trans (map_zero _).symm))
```

List it under "Main results" and in the ledger declarations.

B. Replace the two local instances `namedHasDerivedCategory`, `namedSiteHasDerivedCategory` with

```lean
attribute [local instance] HodgeLadder.Cup.finHasDerivedCategory
  HodgeLadder.Cup.finSiteHasDerivedCategory
```

as R3 does; set `maxHeartbeats 1000000` on `supportedEquivPair_of_named` and remove the `maxHeartbeats` option from `exists_named` (scratch: both compile at the pin). If either fails on rebuild, keep the old option on that declaration and say so in the ledger note.

C. In the module docstring replace the sentence beginning "The `ε(n)` that `shortExactHomologyIsoCone` could carry" with: "`shortExactHomologyIsoCone` enters twice inside `supported_singular_class`, for the supported-sections sequence and inside upstream's `relativeDualCochainHomologyIsoCone`; its naturality along `rawMap` and along `forget₂` matches the two, so any sign it carries cancels, and the statement here contains no cone. No other step can introduce a factor."

D. Move the file to `HodgeLadder/Supported/PairNamed.lean`, module `HodgeLadder.Supported.PairNamed` (the sketch's name, flat beside `PullbackNamed`), and add `public import HodgeLadder.Supported.PairNamed` to `HodgeLadder.lean`.

E. Ledger entry `supported-pair-named`: `module` `HodgeLadder.Supported.PairNamed`; `declarations` `HodgeLadder.Supported.supportedEquivPair_of_named`, `HodgeLadder.Supported.exists_named`, `HodgeLadder.Supported.exists_supportedEquivPair_eq`, `HodgeLadder.Supported.exists_named_ne_zero`; `depends_on` `singular-cochain-pullback`, `cup-singular-comparison`, `supported-step2-cocycle-class`, `supported-singular-class`, `cup-comparison-supported-pair`; note: "Checked 2026-11-28. If β ∈ H_[Z]^p(X; ℚ) is named through iotaQ X by supCocycle (rawMap y) for a relative cocycle y on (X(ℂ), X(ℂ) ∖ Z), then supportedEquivPair X Z p β is the relative class of y, read by upstream's relativeDualCochainCohomologyEquiv and moved along topPairIso; exact, no sign, no scalar. The cone identifications enter only through supported_singular_class, where shortExactHomologyIsoCone occurs at both ends and cancels, so R6's common ε(n) is 1. exists_named: the hypothesis holds for some β for every y; exists_named_ne_zero: every nonzero β gives a nonzero instance (with supportedEquivPair_supportedClass_ne_zero, on every smooth projective X). Kernel type checking about 52 s for the file, 29 s for the main theorem (maxHeartbeats 1000000). Red team docs/sketches/supported-pair-named.redteam.md."

F. `docs/gaps.md`, "Known weaknesses", one row: "| `HodgeLadder.Supported.PairNamed` takes about 80 s to elaborate, 52 s of it kernel type checking (`supportedEquivPair_of_named` 29 s, `exists_named` 14 s, `exists_supportedEquivPair_eq` 9 s; `lake env lean -Dprofiler=true`, 2026-11-28), and the main theorem needs `maxHeartbeats 1000000`; same cause as `Supported.Pullback`, types restating `H_[Z]^p(X; ℚ)` and the flasque model at `TopCat.of (ComplexPoint X)`. A leaf until R6; accepted | Rebuild time on edits; importers read the `.olean` | 2026-11-28 |" (update the numbers if change B moves them).

G. `docs/conventions.md`, row "Supported comparison Φ", append to the result column: "On a class named by `supCocycle (rawMap y)` through `iotaQ X`, `supportedEquivPair` is the relative class of `y` under upstream's `relativeDualCochainCohomologyEquiv` and `topPairIso`, with no sign (`supportedEquivPair_of_named`, rung `supported-pair-named`)."

## What I tried

| Attempt | Result |
|---|---|
| Nonzero instance in degree `2 * p` with `((2 * p : ℕ) : ℤ)` casts | elaboration mismatch between `↑(2 * p)` and `2 * ↑p` in `mapHomologyIso … .sc`; restated over a general degree `n` |
| `probe_nonzero_of` over general `n`, any β ≠ 0 | compiles, standard axioms |
| `probe_cycle` (`cycleComponentSupportedInjectiveClass X x hx ≠ 0`) | compiles, standard axioms |
| `probe_hyp_used` (statement without `hβ` is false) | compiles, standard axioms |
| `probe_no_neg` (a −1 variant is false on β ≠ 0) | compiles, standard axioms |
| file with no `maxHeartbeats` | main theorem times out at `whnf`; `exists_named` compiles |
| file with 1000000 on the main theorem, none on `exists_named`, R3's instances | compiles |
| search for a sign inside the proof | none: the proof is `relHSupportedOfFlasque_mk`, `cls_eq`, `supported_singular_class`, `pairCohIso_hom_apply`; the only cone isomorphisms are inside `supported_singular_class` and cancel |
