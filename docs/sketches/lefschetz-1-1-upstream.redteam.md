# Red team: upstream rational Lefschetz (1,1) (rung `lefschetz-upstream-verify`)

Date: 2026-11-24. Source-only audit; nothing was built and neither clone was modified.

- MAIN = Paul-Lez/HodgeConjecture `2ead713`, Lean/Mathlib v4.35.0-rc4 (statement of record:
  `HodgeConjecture/Variants.lean` `LefschetzOneOne`, `HodgeConjecture/Statement.lean`).
- PROOF = branch `codex/lefschetz-one-one-proper-gaga` `c7d5c94b`, Lean/Mathlib v4.33.1
  (final theorem `Other/AlgebraicGeometry/LefschetzOneOne.lean:35` `lefschetzOneOne`).
- Our local `.lake/packages/mathlib` is tagged v4.35.0-rc4, the same as MAIN; I used it to
  diff Mathlib definitions against PROOF's v4.33.1 copy.

**Verdict: pass with changes.** PROOF proves a statement whose surface form matches
`LefschetzOneOne` and whose definitions on the Hodge side match MAIN. Its cycle-class definition
is a different Lean term from MAIN's, though, and on PROOF itself the theorem is tied to no
statement-of-record constant. "Paul-Lez definitions tested against Lefschetz (1,1)" is **not
done** until the changes in §6 land.

## 1. Statement match

**Surface form.** MAIN `Variants.lean:44-46`:
`def LefschetzOneOne : Prop := ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom], Hdg^1(X; ℚ) ≤ algebraicCycleClassSpan X 1`.
PROOF `LefschetzOneOne.lean:35-37`: the same binders as theorem arguments, the same conclusion.
The match is textual and nothing more. **PROOF deletes `def LefschetzOneOne`** (diff of
`Variants.lean`, hunk at line 39; commit "State the Lefschetz theorem directly"), so nowhere on
PROOF is there a `theorem _ : LefschetzOneOne`. Nothing checks the theorem against the def.

**Hodge side: semantically identical.** `Definitions/AlgebraicGeometry/Hodge/Filtration.lean`
differs only in: imports of vendored copies of the Mathlib `↧` elaborator and `SmallShiftedHom`
(`HodgeConjecture/Mathlib/CategoryTheory/{ConcreteCategory/Notation,Localization/SmallShiftedHom}.lean`,
only on PROOF); proof scripts (`simp` in place of `change`/`rw`); `Sheaf.H.map.{0}` written
`Sheaf.H.map`; and `local instance : HasExt.{0} …` (MAIN :292) becoming the global
`instance analyticHasExt` plus `analyticHasSmallSingleShiftedHom` (PROOF :284-295). `HasExt`
is a `Prop` (`abbrev HasExt : Prop`, Mathlib `Ext/Basic.lean:55`), so changing the instance
cannot change `Ext`. The notation `H^` is identical (`Sheaf.H.{0} ((TopCat.Sheaf.constantFunctor
↧(ComplexPoint X)).obj (AddCommGrpCat.of K)) n`, MAIN :301, PROOF :301), and so are `F^`, `Ω•`,
`hodgeFiltration`, `deRhamConj`, `hodgePiece` and `hodgeClasses` (PROOF :783-926).
`ComplexPoint/Basic.lean` changes only an import, so the analytic topology `Point.analyticTopology`
(:257) is the same. `ProjectiveSpace.lean` (`Presentation`, `IsProjective`) changes only
`f.1.coeff 0` to `coeff 0 f.1`. The relative pair cohomology `relH` (`Pair.lean`) is unchanged;
MAIN only adds lemmas. Orientation (`LocalHomology/FundamentalClass.lean`) differs only by the
Mathlib rename `StdSimplex`/`stdSimplex`. `ComplexClass.lean` is byte-identical.

**Cycle side: different terms.** This is the "cycle API around closed immersions" refactor.
- `CycleComponentSupportedCohomology`. MAIN `FundamentalClass.lean:42-43`:
  `AddCommGrpCat.of (H_[Z(ℂ)]^(2p)(X; ℚ))`, an Ext group. PROOF :68-79: the degree-`2p` homology
  of global sections of `complexSupportInjectiveComplex X Z`, an injective-resolution model.
- `cycleComponentSupportedClassNormalizationIso`. MAIN: `≃+` built from
  `cycleComponentSupportExtensionIso` and `rationalSupportAddEquivSupportedRelativeCohomologySheafSectionOnOpen`
  on `relH`. PROOF :95-102: `≅` built from the injective-model restriction
  (`SupportExtension.lean:184`) and `complexSupportInjectiveCohomologySheafIsoRelative` (:44-52).
- `cycleComponentSheafClass`. MAIN `forgetSupport (Φ_M⁻¹ s)`. PROOF :136-139
  `forgetSupport (cycleComponentSheafSupportedClass …)`, which is
  `(rationalSupportAddEquivSupportedInjectiveHomology …).symm (Φ_P⁻¹ s)` (:125-130,
  `WithSupport.lean` PROOF :69-77). In both, `s = cycleComponentSmoothSupportCoclassSection`,
  whose definition differs only by one import.
- `supportRelativeCohomologySheaf` (`𝓗_[S]^n`). MAIN wraps it through the new
  `TopCat.Sheaf.SupportedCohomologySheaf`/`CohomologySheafOfOpens` (`Sheaf/Cohomology.lean`, only on
  MAIN). PROOF uses `presheafToSheaf.obj (supportRelativeCohomologyPresheaf X S n)` directly. The
  values agree up to functor eta; the terms are not syntactically equal.
- `algebraicCycleClassSpan` (the `sSup` of the spans of `cycleComponentSheafClass`) is textually
  identical.

**Can the cycle-side change alter truth?** Not for this statement, on a mathematical argument that
is not formalized. Both classes have the form `Φ⁻¹(s)` for additive isomorphisms `Φ_M, Φ_P` from
`H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` (PROOF transports back to this same type) onto the same group
`Γ(U, 𝓗^{2p}_S)`. That group is a 1-dimensional ℚ-space, because `Z_reg(ℂ)` is connected
(`Voisin2002`, cycle class map). So `Φ_P ∘ Φ_M⁻¹` is multiplication by a nonzero rational, the
two classes differ by that scalar, and `algebraicCycleClassSpan` is the same submodule. The
one-dimensionality is not proved in Lean anywhere I found. The scalar can be −1: PROOF itself
proves that one comparison between two support models carries a minus sign
(`BettiSupportedOrdinarySign.lean` `rationalCohomologyAmbient_forgetSupport_of_singular_signed`,
"is the negative of the actual positive dual-relative cochain inclusion"). Any **equality**
proved on PROOF, such as `[D] = c₁`, must be re-proved after a port and cannot be transferred.
- On MAIN, `cycleComponentSupportExtensionIso` is data that lives under `Lemmas/` (MAIN
  `FundamentalClass.lean:10` imports `Lemmas/.../SupportExtension`). That breaks the
  Definitions/Lemmas convention, and `scripts/PropOnlyDefinitions.lean` should flag it.

**Mathlib v4.33.1 vs v4.35.0-rc4.** I spot-checked the files that define the statement's
primitives: `Sites/SheafCohomology/Basic.lean` (`Sheaf.H` is the same `Ext` from constant
`ULift ℤ`), `Sites/ConstantSheaf`, `Ext/Basic`, `Ext/EnoughInjectives`,
`Localization/SmallShiftedHom`, `Morphisms/Smooth`, `Properties`, `Order/KrullDimension`,
`StupidTrunc`, `Sheafification`, `Topology/Sheaves/Abelian` and `Morphisms/ClosedImmersion`.
The differences are deprecations, `convert!`/`convert`, `↧` spellings and new instances; none
changes a definition. The spot check is not exhaustive: I did not diff the whole Mathlib import
closure (`ProjectiveSpectrum/Scheme.lean` has 48 changed lines that I did not read).

## 2. Notation, elaboration, axiom gate

- At the theorem site no local notation, instance or attribute touches the statement. The file
  only `open`s `CategoryTheory AlgebraicGeometry ComplexPoint`. `Hdg^` is scoped notation for
  `hodgeClasses K f p` (`Filtration.lean:926`), and `algebraicCycleClassSpan` is a plain def.
  A second `H^` notation exists in `AlgebraicTopology.Singular` (`Lemmas/.../Singular/Cohomology.lean:73`)
  but is not opened here, and the statement does not use `H^` anyway.
- The `Module ℚ` structure comes from `fieldCohomologyModule` (`Filtration.lean:630`). A ℚ-module
  structure on an additive group is unique, and the kernel checks the `≤` type match regardless.
  The grep found no other `LE`/`PartialOrder`/`Module` instance on these types in the closure.
- The many `local instance … : TopologicalSpace (ComplexPoint X) := Point.analyticTopology` lines
  (for example `IntegralCohomology.lean`, `HolomorphicUnitExtension.lean`) restate the global instance.
- `↧` is a term elaborator (`HodgeConjecture/Mathlib/CategoryTheory/ConcreteCategory/Notation.lean:108-121`)
  that emits `FooCat.of x`; it adds no declarations.
- I grepped the whole PROOF tree (`HodgeConjecture`, `Other` including `Other/Oka`, `scripts`,
  `HodgeGuide`) for `sorry`, `axiom`, `opaque`, `implemented_by`, `extern`, `native_decide`,
  `ofReduceBool`, `unsafe`, `skipKernelTC`, `debug.`, `addDecl`, `modifyEnv`, `run_cmd` and
  `#eval`. Every hit is in prose or docstrings (for example `Oka/AnalyticSpace/OpenSubspace.lean:177`
  sits inside a doc comment), apart from `run_cmd`/`run_meta` in the two report/gate scripts.
- Axiom gate: `scripts/CheckLefschetzOneOneAxioms.lean` runs `Lean.collectAxioms` on root
  `lefschetzOneOne` (the only declaration with that name) and throws on anything outside
  `propext, Classical.choice, Quot.sound`. It is a default target in `lakefile.toml:7`, so
  `lake build` fails if the check fails. `sorryAx` would also be caught, which makes the unused
  `import Mathlib.Util.AssertNoSorry` redundant.
  **Unverified:** I did not run it, so I have no axioms line. There is also a module-system
  question. The gate is a non-`module` file importing `module` files, and it reports axioms only if
  the theorem bodies are visible to the importer. I believe non-module imports load everything,
  but I did not check this.

## 3. Vacuity

- **Hypotheses satisfiable?** Mathematically yes: `Over.mk (𝟙 (Spec ↧ℂ))` (ℙ⁰ presentation), and
  ℙ¹. **No Lean witness exists in either repo.** I searched for `IsProjective (…)` constructions,
  `Presentation` terms and `example`s.
- **Is `H^2(X;ℚ)` = 0 by accident?** I found no definitional degeneracy: the topology is the sup of
  chart topologies of pointwise convergence (`ComplexPoint/Basic.lean:239-259`), the constant sheaf
  is the sheafified constant presheaf (`Sheaf/Constant.lean:64-73`), `Sheaf.H` is Mathlib's Ext,
  and universes are fixed at 0. **But no repo proves any degree-2 class nonzero.**
- **Is `Hdg^1` = ⊥ or the span = ⊤ by accident?** Neither is excluded formally. The proof follows
  the classical route and takes no shortcut through either accident. A vacuous statement would
  still accept that proof, though, so its route is no evidence against vacuity.
- **Sanity checks that exist (both repos):** `Other/AlgebraicGeometry/Hodge/CodimensionZeroNonvanishing.lean`
  has `cycleComponentSmoothSupportCoclassSection_ne_zero` (every component's local class is
  nonzero), `cycleComponentSheafClass_genericPoint_ne_zero`, `algebraicCycleClassSpan_zero_eq_top`
  and `rationalHodgeClasses_zero_eq_algebraicCycleClassSpan` (codimension 0). There are also
  `rationalCohomologyUnit_ne_zero` (H⁰), point-class normalization
  (`Cycle/Component/PointClassNormalization.lean`) and `maximalCodimensionBorelMooreFundamentalClass_ne_zero`
  (Borel–Moore homology, not cohomology). The `HodgeGuide/*` `example … := rfl` checks only tie
  guide copies to definitions.
- **Missing.** Proposed `nonvacuity-tests`, in their API (all conditional on an existing `X`):
  1. `instance : IsProjective (𝟙 (Spec ↧ℂ))`, then
     `example : ∃ X : Over (Spec ↧ℂ), IsIntegral X.left ∧ Smooth X.hom ∧ IsProjective X.hom`.
     Better, the same for `Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))`.
  2. For `X` of dimension `d` and a closed point `x` with `hx : Order.coheight x = d`:
     `cycleComponentSheafClass X x hx ≠ 0`. For curves this gives `H^(2*1)(X; ℚ) ≠ 0`, and with (3)
     it gives `Hdg^1(X; ℚ) ≠ ⊥`.
  3. `algebraicCycleClassSpan X p ≤ Hdg^p(X; ℚ)`, the classical reverse inclusion (`Voisin2002`).
  4. Long term, to exclude span = ⊤: some `X` with `Hdg^1(X; ℚ) ≠ ⊤`, for example `E × E` with
     `H^{2,0} ≠ 0`.

## 4. Conventions register (PROOF)

| Convention | Where | Value | Does the final theorem depend on it? |
|---|---|---|---|
| ℤ → 𝒪 | `HolomorphicExponentialSequence.lean:33-45` | `n ↦ (n : ℂ)` (Int cast) | no |
| 𝒪 → 𝒪ˣ | `HolomorphicExponential.lean:76-78`, `Geometry/Manifold/HolomorphicLogarithm.lean:149-170` | `f ↦ exp(2πi f)` | no |
| c₁ | `HolomorphicFirstChernClass.lean:21-23` | `Sheaf.H.δ (holomorphicExponentialSequence_shortExact X d) 1`, Mathlib's Ext connecting map, no extra sign | no |
| Extension ↔ H¹(𝒪ˣ) | `HolomorphicUnitExtension.lean` `cohomologyClass := E.shortExact.extClass`, `firstChernClass` via `sheafCohomologyEquivExt` | Mathlib `extClass` | no |
| Complex orientation | `LocalHomology/ComplexClass.lean` `complexRealHomeomorph` | consecutive `(Re z₀, Im z₀, Re z₁, …)`; simplex with vertices `e₀…e_{d-1}, (−1,…,−1)`, which has sign `(−1)^d`, so positive for `d = 2p` | no |
| Fundamental class | `FundamentalClass.lean` (PROOF :104-139) | local classes evaluate to `1` on the complex-orientation normal classes | no (any nonzero scalar per component gives the same span) |
| Winding | `ChernWindingCochain.lean:163-218` | `(1/2πi) ∮ d log g` | no |
| Winding normalization | `ChernWindingBoundary.lean:178` `windingRelativeClass_eq_chartNormalProjectionCoclass` | winding class = normal coclass when the winding period on the normal 1-sphere is `1` | no |
| Model sign | `BettiSupportedOrdinarySign.lean:35` | proved `−1` between the singular support comparison and the positive cochain inclusion | no (but see §1) |
| Divisor–Chern [9/11] | `DivisorClassCompatibility.lean:38` `HasDivisorClassOfCartierData`, proved at `ChernRelativeFinalAssembly.lean:37` | for every `c` with `c.Represents L` and `L^an ≅ E.sectionSheafOfModules`: `sheafCycleClassOnCycles … 1 c.divisor = integralToRationalCohomology X 2 E.firstChernClass`, sign **+** | no (equality inside the proof; the final span is insensitive) |

`Represents` (`CartierDataRepresents.lean`) means the local sections `fᵢ gᵢ` glue to a rational
section with divisor `c.divisor`, so `L ≅ 𝒪(D)`. That is the usual direction. The PR [9/11]
identity is therefore the literature's `c₁(𝒪(D)) = [D]`, taken in the formalization's own c₁.
No proof connects that c₁ to a textbook c₁ with a fixed sign, and none is needed.
**Imported as an unproved assumption:** none that I found. `lefschetzOneOne` takes only `X`
and the three instances, so every `Prop` obligation (`HasRationalWindingPeriod`,
`HasChernLocalModel`, …) is discharged inside the proof. The gate (§2) would confirm this
once run.

## 5. Proof-architecture risks

The final theorem's truth depends only on the definitions in its type. A weak or vacuous
intermediate `Prop` either fails to compose or is harmless. Still:
- `hasIntegralDenominatorClearing` (`ProjectiveFiniteHomology.lean:43`) proves
  `HasIntegralDenominatorClearing` (`LefschetzOneOneObligations.lean`): every `α : H^2(X;ℚ)` has
  `m ≠ 0` and `β : H^2(X;ℤ)` with `β ↦ m • α`. This is finite generation of `H²(X,ℤ)`; it is exactly
  what is needed and is not weakened.
- `analyticLineBundlesAlgebraize` (`GAGAProper.lean:88`): every invertible module over the
  project's `holomorphicRingSheaf` is the analytification of an invertible algebraic sheaf. It is
  derived from `analyticCoherentSheavesAlgebraize`, which is Oka's `gaga₃_proper`
  (`Oka/Analytification/GAGA/Proper/Equivalence.lean:68`): for `IsProperℂ X`, every coherent
  analytic sheaf is `≅` the analytification of a coherent sheaf. That is Serre's GAGA Théorème 3,
  essential surjectivity (unverified key; add `Serre1956` to `docs/references.md`). It is not
  weakened. Its `RelativeAnalyticSerre` hypothesis is discharged by `relativeAnalyticSerre`. A
  vacuous `IsCoherent` or `IsInvertible` would have to survive `E.sectionSheafOfModules_isInvertible`
  and the invertible-to-coherent bridge, both proved. I read the statements but not those proofs.
- `hasDivisorOfUnitExtension_of_algebraicModel` (`LefschetzOneOneReduction.lean:48`) is a
  two-line composition. `hasDivisorClassOfCartierData` is stronger than needed: it covers
  *every* representing Cartier datum.
- `exists_holomorphicUnitExtension_of_integral_hodgeClass` (`HolomorphicUnitExtensionHodgeClass.lean:43`)
  is where `Hdg^1` enters (the image in `H²(𝒪)` vanishes). I did not read the proof of
  `exists_holomorphicFirstChernClass_of_integral_hodgeClass`.

## 6. Verdict and follow-ups

**pass with changes**, as an audit of PROOF against its own definitions. The build and the
axioms line are not reproduced here, per instructions. Ranked follow-ups before treating
"Paul-Lez definitions tested against Lefschetz (1,1)" as done:
1. **Port to MAIN `2ead713`** (`lefschetz-port`) and restore the link to the statement of record:
   `theorem lefschetzOneOne' : LefschetzOneOne := fun X _ _ _ => lefschetzOneOne X`, with the axiom
   gate pointed at it. Until then nothing proves MAIN's proposition.
2. During the port, either prove a bridge between MAIN's and PROOF's `cycleComponentSheafClass`
   (equality, or equality up to a stated nonzero scalar), or re-prove every equality that mentions
   the cycle class. In particular, re-prove the [9/11] identity and read its sign afresh (§1, §4).
3. Reproduce the build and record the gate's axioms line in `docs/sketches/lefschetz-1-1-upstream.md`.
   Add a positive control: a scratch file with a `sorry`-dependent theorem fed to
   `assert_standard_axioms` must fail. That settles the module-system visibility question.
4. Land the `nonvacuity-tests` in §3, items 1–3; item 4 can wait.
5. Add keys `Serre1956` (GAGA) and a Lefschetz (1,1)/exponential-sequence source
   (`GriffithsHarris1978`) to `docs/references.md`.
6. Upstream hygiene: move `cycleComponentSupportExtensionIso` (data) out of `Lemmas/` on MAIN, or
   whitelist it in `PropOnlyDefinitions`.

Could not verify: the build itself; the gate output; whether non-module imports see theorem
bodies; the full Mathlib v4.33.1→v4.35.0-rc4 definitional diff; the internal proofs of
GAGA-3 and the Hodge-class-to-extension step.
