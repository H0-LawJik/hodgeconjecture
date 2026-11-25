# Red team: rungs `lefschetz-port` and `lefschetz-1-1`

Date: 2026-11-24. Branch `port/lefschetz` at `fe7704b` (PR #28). Pin: upstream main `2ead713`, Lean and
Mathlib v4.35.0-rc4 (`lakefile.toml`, ledger toolchain block agree). Verified source of the port:
upstream branch head `c7d5c94b` (record `lefschetz-1-1-upstream.md`). No Lean file, ledger entry or
`.lake/` content was edited. Scratch Lean files were compiled with `lake env lean` against the
built tree; they are described below by what they test, and their outputs are quoted.

**Verdict: pass with changes.** The checked theorem is upstream's `LefschetzOneOne`, elaborated
term for term. The divisor–Chern identity is an exact equality with sign +, on main's cycle class
of record. Both use only the three standard axioms, and no hypothesis is smuggled in. I found no
change that alters the meaning of a statement named in the ledger. All required changes are to
documentation and hygiene.

Findings: **0 high, 2 medium, 7 low**, plus 1 informational.

## 1. Statement fidelity

| Test | Method | Result |
|---|---|---|
| Declared type of `HodgeLadder.lefschetzOneOne_holds` | `getConstInfo`, compare with `.const ``LefschetzOneOne []` | `true`: the type is the upstream constant itself |
| Is there a shadow `LefschetzOneOne`? | scan every constant in the environment whose name ends in `LefschetzOneOne` | only `[LefschetzOneOne]`, from module `HodgeConjecture.Variants` |
| Port theorem `lefschetzOneOne` vs the body of upstream's `def LefschetzOneOne` | structural diff of the two `Expr`s, under binders, skipping subterm pairs that are both proofs | first syntactic difference is `ValuationRing.isLocalRing ℂ` vs `LefschetzOneOne._proof_1` (both proofs of `IsLocalRing ℂ`); **0 non-proof differences** |
| Upstream statement text re-elaborated with every port import loaded | `elabTerm` on `∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom], Hdg^1(X; ℚ) ≤ algebraicCycleClassSpan X 1` in a file importing `HodgeLadder.Lefschetz.OneOne`, then the same diff | **0 non-proof differences**. The port's global instances (below) do not change how the statement elaborates |
| Where the statement's definitions live | `getModuleIdxFor?` | `algebraicCycleClassSpan`: `HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass`; `hodgeClasses`: `HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration`; `cycleComponentSheafClass`: upstream `FundamentalClass`; `sheafCycleClassOnCycles`: upstream `Other.AlgebraicGeometry.Cycle.SheafClass` |
| Staged file at a path that exists on main | path check of all 680 staged files against `.lake/packages/HodgeConjecture/{Other,HodgeConjecture}/` | none |

Because the type is the upstream constant, the kernel check is against upstream's elaborated
`Prop`. Nothing elaborated later can change it. The re-elaboration test also covers future files
that restate the statement text while the port is imported.

**Hypotheses satisfiable:** yes. `HodgeLadder.Tests.exists_smooth_projective_integral` (checked,
`HodgeLadder/Tests/Witness.lean:76`) gives `Spec ℂ` with upstream's instances.

**Trivially true?** Each of these attempts failed to close `LefschetzOneOne`: `simp`, `exact le_top`,
`intro a ha; simp_all`, `simp [hodgeClasses] at ha`, `Subsingleton.elim a 0 ▸ zero_mem _`. Instance
search for `Subsingleton (H^(2*1)(X; ℚ))` also fails. No definition unfolds to `True` and no
hypothesis goes unused: the proof consumes `Hdg^1` membership at
`exists_rationalSheafCycleClassOnCycles_eq_of_obligations`.

## 2. Port changes: proof-only or definition-changing

Method: `diff` of every staged file against the verified head, after rewriting `LefschetzPort.` to
`Other.` (and `LefschetzPort.HC.` to `HodgeConjecture.`). Each hunk was then classified by its
enclosing declaration, and by whether it falls in the signature or the body.

- 362 files are identical. 306 differ, and in 264 of them the only change is the import of
  `Supplement/AnalyticExt`.
- 2 staged files have no counterpart at the head: `AlgebraicGeometry/ChernWindingRawBoundary.lean`
  and `AlgebraicGeometry/HolomorphicExponentialSupportWinding.lean` (finding L3).
- Every file that defines a constant in the divisor–Chern statement differs from the head **only
  by that import line**. These are `DivisorClassCompatibility`, `IntegralCohomology`,
  `HolomorphicFirstChernClass`, `HolomorphicExponential`, `HolomorphicExponentialSequence`,
  `CartierDataRepresents`, `DivisorOfRationalSection`, `AnalytificationModules`,
  `HolomorphicLineBundle*`, `CategoryTheory/Sites/SheafCohomology/Connecting`,
  `BettiSupportedOrdinarySign`, `ComplexSupportedOrdinaryComparison`, `LefschetzOneOneObligations`,
  `ProjectiveFiniteHomology`, `GAGAProper` and `ChernRelativeFinalAssembly`. The one exception is
  `HolomorphicUnitExtension.cohomologyClass`, listed below.

Every `def`, `abbrev` and `instance` whose body or signature changed:

| Declaration (file:line) | Change | Classification |
|---|---|---|
| `HolomorphicUnitExtension.cohomologyClass` (`AlgebraicGeometry/HolomorphicUnitExtension.lean:64`), `rationalChernShiftedHom` (`ChernRelativeClass.lean:67`) | `E.shortExact.extClass` → `ShortComplex.ShortExact.extClass.{0} E.shortExact` | definitionally equal. At the head the universe was fixed to 0 by the global `HasExt.{0}` instance; the port fixes it by an explicit universe. `HasExt` is `Prop` (checked: `HasExt : (C : Type u_3) → [Category C] → [Abelian C] → Prop`) |
| `ChernWinding.simplexMap`, `simplexPullback` (`ChernWindingCochain.lean:54,59`) | codomain type `C(stdSimplex ℝ _, Y)` → `C(Convexity.StdSimplex ℝ _, Y)` | follows Mathlib's new topological simplex. The body `Y.toSSetObjEquiv _ σ` is unchanged |
| `ChernWinding.simplexIncrement` (`ChernWindingCochain.lean:79`) | `stdSimplex.vertex 0/1` → `Convexity.StdSimplex.single 0/1` | same vertices, same order (0 → 1). The winding +1 theorem is re-checked at the pin |
| `HasChernLocalModel` (`ChernLocalModel.lean:214`), `HasChernWindingNaturality` (`ChernLocalModelWinding.lean:348`) | the branch's injective-model normalization iso → main's `cycleComponentSupportedClassNormalizationIso` after `(componentTransport X x).symm` | **definition-changing**. Both are `Prop`-valued intermediate obligations, proved unconditionally inside the port. `componentTransport` is an `≃+`, so no scalar enters. Irrelevant to the truth of the named statements, whose types are fixed (§4) |
| `ComplexAnalytic.relChartRingHom` (new, `Oka/.../RelativeProjectiveAn.lean:93`); `relProjectiveSpaceChart`, `isIso_SpecMap_relChartRingEquiv` and an anonymous instance | `CommRingCat.ofHom (relChartRingEquiv m N).toRingHom` named once as an `abbrev` | definitionally equal (an `abbrev` of the same term). The new `IsIso` proof is `Prop` |
| `restrictExtendSMulHom` (`Oka/Geometry/RingedSpace/LocallyRingedSpace/HomSheaf.lean:267`) | values wrapped in `End.of`; identities through `End.ext` | same data. `End X` is now a one-field structure in Mathlib, and `End.of` is its constructor |
| `integralChainsCoproductDiagramIso` (`AlgebraicTopology/OpenCoverOrderedCechBicomplex.lean:595`) | `NatIso.ofComponents (fun _ ↦ Iso.refl _) …` → `Discrete.natIso (fun _ ↦ Iso.refl _)` | same components (identities). Naturality is a proof |
| `uliftCastSuccEmb`, `UIIsoSpec`, `homotopyOfPrecompQuasiIso`, `homotopyEquivOfMapBetweenContractibleSpaces` | proof fields or heartbeat options only | proof-only |
| `etalePresentedAlgebraEquiv` (`Oka/Analytification/StandardEtale.lean:439`), `standardEtalePairRingIsScalarTower` (`:416`) | `letI` of an `Ideal.IsTwoSided` instance (`Prop`); explicit `(R := …)` on `rfl` | proof-only |
| `coverSmallScalarSingularChainInclusion_mono`, `isIso_openSheafRestrictionCounit_app`, `preservesInjectiveObjects_restrictAb` | `Prop` instances, proofs changed | proof-only |
| removed `stdSimplexNonempty`, `stdSimplexContractibleSpace`, `stdSimplexLocallyPathConnectedSpace` (head `ChernWindingCochain.lean:43-56`) | replaced by `Supplement/StdSimplex` | `Prop` instances |

Signatures of theorems changed in two ways only. Some follow Mathlib renames
(`Convexity.StdSimplex`, `.weights`, `p.coeff m`). The others route through main's class: six
statements in `ChernComponent*` and `ChernLocalModel` now carry `componentTransport`, and the RHS of
the bridge `cycleComponentSheafClass_eq_injectiveModel` changed. None is a statement named in the
ledger.

Supplements (10 files): every declaration is a `theorem`/`lemma` or a `Prop` instance, with these
exceptions:
- `componentTransport` (`Supplement/NormalizationTransport.lean:30`): an `abbrev` for main's
  `rationalSupportAddEquivSupportedInjectiveHomology … (2 * 1)`.
- `stdSimplexHomeomorph` (`Supplement/StdSimplex.lean:46`): used only to transfer `Prop` instances;
  it has 0 uses outside its own file.
- The five `def`s in `Supplement/CochainSubdivision.lean`, which match the head's additions to
  main's file text for text.

Global instances the port adds:
- `analyticHasExt` (`Supplement/AnalyticExt.lean:28`): `HasExt.{0}`, `Prop`.
- `LefschetzPort.polynomialQuotientIdealIsTwoSided` and `polynomialPolynomialQuotientIdealIsTwoSided`
  (`Supplement/QuotientPolynomialTwoSided.lean:31,36`): `Ideal.IsTwoSided`, `Prop`.
- `relBaseSubmoduleAddSubgroupClass` (`RelativeProjectiveAnFunctions.lean:367`): `AddSubgroupClass`,
  `Prop` (checked). It is global, not local (finding L2).

An instance scan of the environment counts 303 `Prop`-valued and 100 data-valued global instances
declared in `LefschetzPort.*`. All the data-valued ones come from files identical to the head
(finding L7).

Elaborator options:
- `backward.isDefEq.respectTransparency false` appears 377 times in `port/`, and the port added 1
  of them (`Oka/Topology/Sheaves/...`).
- `backward.defeqAttrib.useBackward` is inherited.
- 11 `erw` were added, and 12 heartbeat options were added or raised.

All of these act on the elaborator only. The kernel re-checks every term, as the axioms lines
confirm.

## 3. Sign and normalization conventions

The divisor–Chern statement (`DivisorClassCompatibility.lean:39`, unchanged from the head apart
from one import):

  `sheafCycleClassOnCycles ⟨X⟩ 1 c.divisor = integralToRationalCohomology X 2 E.firstChernClass`,
  sign +.

I traced every constant reachable from its type by unfolding port definitions (89 non-theorem port
constants). The non-port `ComplexPoint` constants it reaches are upstream's
`sheafCycleClassOnCycles`, `holomorphicFunctionSheaf`, `integerToFieldConstantSheaf` and
`AnalyticAdditiveSheaf`. Each sign-bearing convention, read from the source at the pin:

| Convention | Source | Value | Equality-sensitive? |
|---|---|---|---|
| ℤ → 𝒪 | `HolomorphicExponentialSequence.lean` `integerConstantsToHolomorphicPresheaf` | `Int.castAddHom ℂ` | yes |
| 𝒪 → 𝒪ˣ | `Geometry/Manifold/HolomorphicLogarithm.lean:150-170` | `f ↦ exp(2πi f)` | yes |
| connecting map | **port's** `CategoryTheory.Sheaf.H.δ` (`CategoryTheory/Sites/SheafCohomology/Connecting.lean:24`): `hS.extClass.postcomp _ rfl` | no extra sign; same body as Mathlib's `H.δ` (`ExactSequences.lean:60`, `hS.extClass.postcomp _ h`) | yes (finding M1) |
| extension → H¹(𝒪ˣ) | `cohomologyClass := extClass.{0}`; `firstChernClass := holomorphicFirstChernClass ((sheafCohomologyEquivExt …).symm E.cohomologyClass)` | Mathlib `extClass`; `ULift ℤ ≅ ℤ` by `AddEquiv.ulift` (+) | yes |
| ℤ → ℚ coefficients | `integralToRationalCohomology = Sheaf.H.map (integerToFieldConstantSheaf ℚ X 1)`; upstream `integerToFieldConstantSheaf q` is `zmultiplesAddHom K q` | `n ↦ n • 1` | yes (scalar `q = 1`) |
| divisor direction | `CartierData.Represents` (`CartierDataRepresents.lean:35`): `u • gᵢ = gⱼ ⇒ u·fⱼ = fᵢ`, so `s = fᵢ gᵢ` glues and `L ≅ 𝒪(D)`; `ordFun` is Mathlib's `Scheme.ord` (order of vanishing, positive at zeros) | `L ≅ 𝒪(D)`, not `𝒪(−D)` | yes |
| Ext model → injective model | main's `rationalSupportAddEquivSupportedInjectiveHomology`; bridge `cycleComponentSheafClass_eq_injectiveModel` (`CycleClassExtComparison.lean:53`), proved by `rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport` (`SupportedExtForgetComparison.lean:73`) | exact, no scalar | yes |
| cone model vs singular support model | `rationalCohomologyAmbient_forgetSupport_of_singular_signed` (`BettiSupportedOrdinarySign.lean:36`), used at `ComplexSupportedOrdinaryComparison.lean:191` | −1, inside the proof | no (proof-internal; the final identity is checked) |

**Could a sign have been absorbed by a port change?** No. The statement's type is fixed and
kernel-checked, and every definition in it is the head's text (or main's). The only port change
inside them is the explicit universe in `cohomologyClass`, which is definitionally equal. A sign
error in an intermediate lemma cannot survive: the final equality either checks or fails to
compose.

What the equality *means* depends on the conventions in the table. Two compensating errors would
have to sit in the statement's definitions: for example, an inverted extension-to-bundle direction
together with a negated c₁. I read both sides. `Represents` gives `𝒪(D)` and δ has no extra sign.
The cycle class is pinned to the complex orientation (`HodgeLadder.Pins`). So the checked identity
is the literature's `c₁(𝒪(D)) = [D]` (`GriffithsHarris1978`), with c₁ as the formalization defines it
(the formalization's c₁ is not compared with a textbook c₁ anywhere).

Rows added to `docs/conventions.md`: the ℤ → ℚ coefficient map; extension → H¹(𝒪ˣ); the Cartier
direction (`Represents`, `ord`); the exact Ext → injective bridge; the cone-vs-singular −1, now with
its use site. I corrected the "Connecting homomorphism sign" row to cite the port's copy and
refreshed the "Cycle-class model" status.

## 4. Vacuity of intermediate obligations

`lefschetzOneOne` (`port/LefschetzPort/AlgebraicGeometry/LefschetzOneOne.lean:36`) takes only `X`
and the three instances. Every obligation is a closed theorem; `#check` shows only `X` and
instances as arguments:

| Theorem | Statement | Axioms |
|---|---|---|
| `hasIntegralDenominatorClearing` | `∀ X …, HasIntegralDenominatorClearing X`, which unfolds to `∀ α : H^2(X; ℚ), ∃ m β, m ≠ 0 ∧ integralToRationalCohomology X 2 β = m • α` | standard |
| `analyticLineBundlesAlgebraize` | `∀ X …, AnalyticLineBundlesAlgebraize X`, which unfolds to: every invertible `holomorphicRingSheaf`-module is `≅` the analytification of an invertible algebraic sheaf | standard |
| `hasDivisorClassOfCartierData` | `∀ {X} …, HasDivisorClassOfCartierData X` | standard |
| `exists_rationalSheafCycleClassOnCycles_eq_of_obligations` | `HasIntegralDenominatorClearing X → HasDivisorOfUnitExtension X → ∀ α ∈ Hdg^1(X; ℚ), ∃ D, rationalSheafCycleClassOnCycles … 1 D = α` | standard |
| `cycleComponentSheafClass_eq_injectiveModel` | the bridge, an equality | standard |

The glue lemmas (`hasAlgebraicModel_of_…`, `hasDivisorOfUnitExtension_of_algebraicModel`,
`hasDivisorOfAlgebraicModel_of_divisorClass`, `hasDivisorClassOfSomeCartierData_of_cartierData`)
are implications between these `Prop`s, and every premise is discharged in
`LefschetzOneOne.lean:39-48`.

## 5. Hidden escapes

`grep` over `port/` and `HodgeLadder/` for `sorry`, `axiom` declarations, `native_decide`,
`implemented_by`, `@[extern`, `unsafe`, `opaque`, `skipKernelTC`, `debug.`, `ofReduceBool`,
`addDecl`, `modifyEnv`, `run_cmd`, `run_meta`, `run_elab`, `#eval` and `elab_rules`. There are no
hits in code. The hits are:
- `#eval` inside a docstring code block (`Oka/AnalyticSpace/OpenSubspace.lean:177`).
- The word "axiom" in prose (`Oka/AnalyticSpace/Finite.lean:218`).
- Local notations, plus one `scoped macro` (`Oka/AlgebraicGeometry/Modules/CocycleTwist.lean:59`,
  restriction notation in an Oka namespace).

No `set_option` touches the kernel. `python3 tools/check.py --no-build` exits 0. Axioms lines:
- `lefschetzOneOne`: `[Classical.choice, Quot.sound, propext]`.
- `HodgeLadder.lefschetzOneOne_holds`: the same.
- `AlgebraicGeometry.ComplexPoint.hasDivisorClassOfCartierData`: the same.

The declarations named in the ledger are the ones meant: `lefschetzOneOne` is root-level in
`LefschetzPort.AlgebraicGeometry.LefschetzOneOne`, and the other two are as named.

## 6. Upstream drift and duplicates

No staged file copies a main file: there are no path collisions, and `stage2.py` copies only
modules absent from main. Of the constants in the divisor–Chern statement, none duplicates a main
declaration under a new name (`grep` of main for each name). The two declarations staged from
main's private or extended files are `Supplement/RelativeCochainCone` (a re-declared `private`
lemma) and `Supplement/SheafClass` (two span lemmas). Both are `Prop`.

Duplicates of **Mathlib** do exist; see M1 and L7.

The port was checked at the current pin, so there is no pin drift to diff. The upstream red team's
partial Mathlib v4.33.1 → v4.35.0-rc4 diff is superseded, because the whole proof is re-checked at
the pin.

## 7. Equality first and non-vacuity

- `divisor-chern-exact` is an identity, proved exactly: the checked type is an `=` with no scalar,
  and the Ext → injective step is an `≃+`.
- `lefschetz-1-1` is an inclusion. The equality it is a step toward is `lefschetz-1-1-equality`
  (exists, `open`), which needs `CycleClassesAreHodgeOne`.
- The smallest test that would fail if `LefschetzOneOne` held for a degenerate reason is a
  positive-dimensional `X` with `Hdg^1(X; ℚ) ≠ ⊥` (for ℙ¹ or ℙ²: `cycleComponentSheafClass X x hx ≠ 0`
  for a point or line, plus `cycleComponentSheafClass X x hx ∈ Hdg^1(X; ℚ)`). Together with some `X`
  where `algebraicCycleClassSpan X 1 ≠ ⊤`, it would rule out both degenerate readings. **It does not
  exist.** The existing `HodgeLadder.Tests.*` are codimension 0, and `projective-space-test` is
  `open` (informational I1).

## Findings

### Medium

**M1. The port redefines a Mathlib declaration: `CategoryTheory.Sheaf.H.δ`.**
`port/LefschetzPort/CategoryTheory/Sites/SheafCohomology/Connecting.lean:24` declares
`CategoryTheory.Sheaf.H.δ (hS) (n)`. Mathlib at the pin declares the same name with a different
signature, `δ hS n₀ n₁ h` (`Mathlib/CategoryTheory/Sites/SheafCohomology/ExactSequences.lean:60`).
Mathlib v4.33.1 did not have that file.

Failure scenario, reproduced: a file containing
`import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences` and
`import LefschetzPort.AlgebraicGeometry.LefschetzOneOne` fails with "environment already contains
'CategoryTheory.Sheaf.H.δ' from Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences". The
same failure hits any HodgeLadder module, or any future upstream pin, whose closure reaches
Mathlib's long exact sequence. In that case `lefschetz-1-1` stops building.

The conventions register also cites Mathlib's δ, while `holomorphicFirstChernClass` uses the
port's. The bodies agree (`extClass.postcomp`, no sign), so no truth changes today. Fix: rename the
port's copy, or replace it with Mathlib's `H.δ hS 1 2 rfl` and a one-line equality lemma. The
register row is corrected here.

**M2. "The port changes proofs only" is inaccurate.**
The claim appears in `ledger/ladder.json:180`, `HodgeLadder/Lefschetz/OneOne.lean:16` and
`docs/port-lefschetz.md` (parts 5, 6, 11: "No statement changed"). Section 2 lists what the port
actually changed:
- two `Prop`-valued obligation definitions (`HasChernLocalModel`, `HasChernWindingNaturality`);
- about 30 intermediate theorem signatures (six re-routed through `componentTransport`; the rest
  follow Mathlib renames);
- the RHS of the bridge;
- data-definition types and bodies (`simplexMap`, `simplexIncrement`, `restrictExtendSMulHom`,
  `integralChainsCoproductDiagramIso`, `relChartRingHom`).

None of these alters a statement named in the ledger (§1, §3). But a reader who trusts "proofs only"
would not re-audit `HasChernLocalModel`, which is where main's normalization enters.

Failure scenario: a future port step changes an intermediate `Prop` the same way, lets it go
unaudited on the strength of the stated policy, and a sign enters an obligation that is later
cited on its own. Fix: reword to "no statement of record and no ledger-named statement changed;
intermediate obligations were re-stated on main's cycle class (list in the port log, part 8/9)".

### Low

- **L1. Conventions register incomplete or stale** (`docs/conventions.md:18,21`). It lacked rows
  for the ℤ → ℚ coefficient map, extension → H¹(𝒪ˣ), the Cartier direction, and the exact bridge.
  The −1 lemma's "still open" status was stale, since part 9 uses it. Failure scenario: an identity
  rung built on `integralToRationalCohomology` (for example `lefschetz-1-1-integral`) passes review
  without anyone checking the scalar. **Done in this pass.**
- **L2. "Local" instance that is global.** `relBaseSubmoduleAddSubgroupClass`
  (`Oka/Analytification/GAGA/Proper/RelativeProjectiveAnFunctions.lean:367`) is a global `instance`,
  but the port log (part 11, item e) calls it local. It is `Prop`, so it is harmless. Fix the log,
  or make it `local instance` / `attribute [local instance]`.
- **L3. Two dead modules.** `AlgebraicGeometry/ChernWindingRawBoundary.lean` and
  `HolomorphicExponentialSupportWinding.lean` have no counterpart at the verified head. Only each
  other and the root `port/LefschetzPort.lean:96,160` import them. They are built but unaudited
  against the head. Failure scenario: they drift or break a future bump for no benefit. Delete them,
  or record their source commit in the port log.
- **L4. The checker's `sorry` scan misses `port/`.** `tools/check.py:20,56` scans `HodgeLadder/`
  only. A `sorry` in a port module that no named declaration uses would pass `check.py` with only
  a `lake build` warning. My `grep` finds 0 today. Add `port/` to `check_no_sorry`.
- **L5. Stale lakefile comment.** `lakefile.toml:26` says `LefschetzPort` is "Not a default
  target", but line 3 makes it one.
- **L6. Stale ledger note.** `ledger/ladder.json:199` says `nonvacuity-tests` "is checked on its
  branch (PR 27)". PR 27 is merged (`f7ff3e8`).
- **L7. Data instances on Mathlib's `Sheaf`, in Mathlib's namespace.** `CategoryTheory/Sites/Forget.lean:23,35,74`
  declares global `Sheaf.homFunLike`, `Sheaf.concreteCategory` (underlying type: the sigma of all
  sections) and `Sheaf.hasForget₂`. These are inherited from the head unchanged. They do not change
  `LefschetzOneOne`'s elaboration (§1, re-elaboration test). Failure scenario: Mathlib adds its own
  `ConcreteCategory (Sheaf J A)`. That gives either a name clash (as in M1) or a non-defeq instance
  diamond in later port or HodgeLadder statements. Note it for the upstream contribution; rename
  into a `LefschetzPort` namespace, or scope it.

### Informational

- **I1.** No degree-2 non-vacuity test exists (§7). This is known and tracked by
  `projective-space-test` and `cycle-classes-are-hodge`, and it is not a defect of the port.

## Attempts that failed (kept for the record)

- Proving `LefschetzOneOne` by `simp`, `le_top`, `simp_all`, unfolding `hodgeClasses`, and a
  subsingleton argument: all fail (§1).
- Finding a non-proof difference between the port's statement and upstream's body: none, either as
  elaborated in the port or as re-elaborated text with the port loaded.
- Finding a data-valued instance added by the port (as opposed to inherited): none; the added ones
  are `HasExt`, `IsTwoSided`, `AddSubgroupClass`, `ContractibleSpace`, `LocallyPathConnectedSpace`.
- Finding a port `def` in the divisor–Chern statement whose text differs from the head: only
  `cohomologyClass` (explicit universe, definitionally equal).

## Required changes (for `pass`)

1. M1: rename or replace the port's `CategoryTheory.Sheaf.H.δ`.
2. M2: reword "proofs only" in the ledger note, the `OneOne.lean` module docstring and the port log.
3. L2–L6: the one-line fixes listed above.
