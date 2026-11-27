# Red team: `complex-point-nonempty` (foundation)

Date: 2026-11-27. Worktree `complex-point-nonempty` at base `0786e81` (= `main`), uncommitted `HodgeLadder/General/ComplexPoint.lean`, `docs/sketches/complex-point-nonempty.md`, and the ledger, roadmap, gaps and root-import edits. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`.

Read: the ledger entry; the module and the sketch; upstream `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean` (`Point`, `ComplexPoint`) and `Other/AlgebraicGeometry/ComplexPoint/ProjectiveConnected.lean` (`instNonemptyComplexPoint`); Mathlib `AlgebraicGeometry/AlgClosed/Basic.lean` (`residueFieldIsoBase`, `pointOfClosedPoint`, `pointEquivClosedPoint`); the originals in `HodgeLadder/Tests/DeRhamUnitNonzero.lean` and `HodgeLadder/Hodge/WedgeSheafify.lean`; `tools/check.py`; `docs/conventions.md`, `docs/references.md`.

Scratch (directory `scratch_rt/`, deleted afterwards; 4 to 17 s each with `lake env lean`):

| File | What it tried | Result |
|---|---|---|
| Light | the four non-ladder imports of the module only; `infer_instance`, `trivial`, `simp`, `decide`, `aesop` on the rung statement; the proof of `nonempty_complexPoint_of_locallyOfFiniteType` copied verbatim; `ComplexPoint X = (Over.mk (𝟙 (Spec ↧ℂ)) ⟶ X)` by `rfl`; `z.left ≫ X.hom = 𝟙 _` from `Over.w z`; the empty scheme `Over.mk (Scheme.emptyTo (Spec ↧ℂ))` has no complex point | every trivial tactic fails; the proof compiles with those four imports; the definition is as the sketch says; the structure map is respected; the empty-scheme counterexample checks. One defect: `open ... ComplexPoint` is an error in that import set (no namespace `AlgebraicGeometry.ComplexPoint` exists yet), so the split file must drop it (change 2) |
| Heavy | imports the module; `infer_instance` for `Nonempty (ComplexPoint X)`; `#check` of the six originals against their primed forms; `#print axioms HodgeLadder.nonempty_complexPoint_iff`; witness `HodgeLadder.Tests.point` | `infer_instance` fails, so the module's closure does not already hold the instance; each primed signature is its original with the `[Nonempty (ComplexPoint X)]` binder deleted and nothing else changed; standard axioms; `nonempty_complexPoint Tests.point` checks |
| Up | imports `Other.AlgebraicGeometry.ComplexPoint.ProjectiveConnected` only; `infer_instance` for the rung statement under `[IsIntegral X.left] [Smooth X.hom]` | succeeds: upstream's instance closes the posted statement outright (finding 6) |

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`; the nine ledger declarations each report `[Classical.choice, Quot.sound, propext]`. The olean postdates the source by 5 s, so the axioms line reads the file under review.

## 1. Is this the statement the literature makes?

The literature fact is the Nullstellensatz in scheme form: a nonempty scheme locally of finite type over an algebraically closed field k has a k-point, and its k-points are its closed points (`Stacks`; tag not verified here). Field by field:

| Piece | Lean | Literature |
|---|---|---|
| `ComplexPoint X` | upstream `abbrev ComplexPoint X := Point ℂ X`, `Point R X := Over.mk (𝟙 (Spec ↧R)) ⟶ X` (checked by `rfl`) | a morphism Spec ℂ → X over Spec ℂ |
| Structure map respected | a morphism in `Over (Spec ↧ℂ)` carries `z.left ≫ X.hom = 𝟙`; `Over.homMk z.1 z.2` uses exactly the section equation `p ≫ X.hom = 𝟙 _` of `pointEquivClosedPoint` | a section of the structure morphism |
| Hypotheses | `[IsIntegral X.left] [Smooth X.hom]` (rung), `[Nonempty X.left] [LocallyOfFiniteType X.hom]` (general) | nonempty, locally of finite type |

`nonempty_complexPoint` is the ledger title verbatim. Pass.

## 2. Is the route sound?

`pointEquivClosedPoint` is stated for `X : Scheme.{u}`, `K : Type u`, `[Field K] [IsAlgClosed K]`, `f : X ⟶ Spec ↧K`, `[LocallyOfFiniteType f]`. Here u = 0, K = ℂ, `IsAlgClosed ℂ` comes from `Mathlib.Analysis.Complex.Polynomial.Basic` (`Complex.isAlgClosed`), and f = `X.hom`, the structure map of record, with `LocallyOfFiniteType` from `Smooth` through `LocallyOfFinitePresentation`. Nothing is satisfied in a degenerate way: the closed point comes from `LocallyOfFiniteType.jacobsonSpace` and `nonempty_inter_closedPoints` on `Set.univ`, which is open and nonempty. The proof is the text of upstream's `instNonemptyComplexPoint` with `[IsIntegral X.left]` replaced by `[Nonempty X.left]`; upstream uses integrality only for nonemptiness. Pass.

## 3. The `iff` form

Forward: `z.left (IsLocalRing.closedPoint ℂ)` is a point of `X.left`, which needs no finiteness. Backward: the general lemma. Holds as stated. `Nonempty X.left` cannot be dropped from the general lemma: the empty scheme over Spec ℂ (locally of finite type, as any morphism from ∅ is) has no complex point, checked in Light. Pass.

## 4. Trivial proofs and axioms

Hypotheses are satisfiable: `Tests.point = Over.mk (𝟙 (Spec ↧ℂ))` carries `IsIntegral` and `Smooth` (rung `nonvacuity-tests`), and `nonempty_complexPoint Tests.point` checks. The conclusion is not trivially true: `infer_instance`, `trivial`, `simp`, `decide` and `aesop` all fail in the light import set, and `infer_instance` fails in the module's own closure. No `ℕ∞` coercion, empty index or unused hypothesis: integrality is used for `Nonempty X.left`, smoothness for local finite type. Axioms standard. Pass.

## 5. Corollaries

`#check` of each pair (Heavy): `fieldToHolomorphicDeRhamComplexInt_ne_zero'`, `rationalDeRhamUnit_ne_zero'`, `nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero'`, `fieldToHolomorphicDeRhamComplexInt_ne_neg'`, `rationalDeRhamUnit_ne_neg'` (namespace `HodgeLadder.Tests`) and `wedgeSheaf_ne_zero'` (namespace `HodgeLadder`, as its original) have the originals' binders and conclusions with only `[Nonempty (ComplexPoint X)]` removed; `wedgeSheaf` is at `TopologicalSpace.dim ↥X.left` in both. The originals are unchanged. Pass.

## 6. Import weight and upstream reuse

Three facts, all checked:

- The module's docstring says the local copy "imports nothing from `Other`", and the sketch says it "does not pull in `Other`". Both are false as written: `HodgeLadder.Hodge.WedgeSheafify` brings in 15 `Other` modules transitively (for example `Other.AlgebraicGeometry.Cohomology.HypercohomologyNaturality`, `Other.AlgebraicGeometry.Cohomology.WithSupport`), 531 modules in all. It does not bring in `ProjectiveConnected`.
- The library root already imports upstream's instance: `HodgeLadder.Tests.CodimensionZero` imports `Other.AlgebraicGeometry.Hodge.CodimensionZeroNonvanishing`, which reaches `Other.AlgebraicGeometry.ComplexPoint.ProjectiveConnected` through `CodimensionZeroComparison` and `CodimensionZero`. So a file importing `HodgeLadder` can already call the unprimed originals on a smooth integral `X` with the point found by instance search.
- Upstream's instance closes the posted statement `nonempty_complexPoint` by `infer_instance` (Up). The local copy's real gains are the weaker hypothesis `Nonempty X.left`, the sharp `iff`, and, after a split, a light import set. These are legitimate reasons to keep it under decision 0011; the reason recorded must be the true one.

Recommendation: split. The three lemmas go into a light `HodgeLadder/General/ComplexPoint.lean` with only the four non-ladder imports (verified to compile in about 4 s); the six corollaries go into a new `HodgeLadder/Tests/ComplexPointNonempty.lean` that imports it and `HodgeLadder.Hodge.WedgeSheafify`. Keep the local proof of `nonempty_complexPoint` (it would otherwise need `ProjectiveConnected` and its `Manifold` and `ProjectiveCompact` imports), and record that upstream's instance proves it too.

## 7. Equality first; non-vacuity

Not an identity or an inclusion; an existence statement that removes a hypothesis from checked nonvacuity tests (decision 0004 does not apply). Smallest test that fails if the statement were trivially true: the empty-scheme counterexample (Light), which shows the content lies in `Nonempty X.left`; with the iff it pins the statement down exactly. It is not in the module; adding it is optional (change 5).

## 8. Conventions

None. No sign, scalar or normalization enters an existence statement, and `docs/conventions.md` needs no new row. The only borrowed result, `pointEquivClosedPoint`, is stated against Mathlib's `Spec`, `LocallyOfFiniteType` and closed points, the same objects upstream's `Point` is built from.

## 9. `depends_on`, gaps row, pin drift

- `depends_on: [de-rham-unit-nonzero, wedge-sheafify]` is right for the rung as posted (the corollaries need both); the core lemma depends on no rung.
- The gaps row's reason ("the local copy drops integrality") is true but incomplete; it must also say that upstream's instance proves `nonempty_complexPoint` and is already in the root's closure (change 3).
- Pin drift: none. The rung was checked at `2ead713`, the current pin; `lakefile.toml` is not touched. At a future bump the proof depends on `ComplexPoint = Point ℂ` with `Point` the over-morphisms from `Over.mk (𝟙 _)` (a change breaks `Over.homMk z.1 z.2` at build time) and on Mathlib's `pointEquivClosedPoint` signature; neither can change truth silently.

## Verdict: `pass with changes`

Required:

1. **Correct the false import claim.** Remove "imports nothing from `Other`" from the module docstring and "does not pull in `Other`" from the sketch's "Upstream overlap" section and the ledger note. Replace with: the light file imports no `Other` module and no ladder module; upstream's `instNonemptyComplexPoint` proves `nonempty_complexPoint` by `inferInstance` and is already in the library root's closure (through `HodgeLadder.Tests.CodimensionZero`); the local copy is kept for the weaker hypothesis `Nonempty X.left`, the iff, and the light import.
2. **Split the module.** `HodgeLadder/General/ComplexPoint.lean`: imports `HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.Basic`, `Mathlib.AlgebraicGeometry.AlgClosed.Basic`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Mathlib.Analysis.Complex.Polynomial.Basic` only; `open CategoryTheory AlgebraicGeometry` (drop `ComplexPoint` and `TopologicalSpace` from the `open`; `ComplexPoint` is an error there); the three lemmas. New `HodgeLadder/Tests/ComplexPointNonempty.lean`: `public import HodgeLadder.General.ComplexPoint` and `public import HodgeLadder.Hodge.WedgeSheafify`, the six corollaries with unchanged names. Root imports both. Ledger `module` becomes `HodgeLadder.Tests.ComplexPointNonempty` (the checker imports that one module to print axioms, and it reaches all nine declarations); update the roadmap row and the `docs/gaps.md` row's module column (the General file) to match.
3. **Gaps row.** Add: "upstream's instance proves `nonempty_complexPoint` by `inferInstance` and is imported by the library root; at a pin bump, check its hypotheses, and if upstream weakens them to `Nonempty X.left`, replace the local copy."
4. **Ledger note.** Replace "Red team pending" with "Red team pass with changes (`docs/sketches/complex-point-nonempty.redteam.md`)".

Optional:

5. Add the empty-scheme counterexample to the Tests file as `HodgeLadder.Tests.not_nonempty_complexPoint_empty : ¬ Nonempty (ComplexPoint (Over.mk (Scheme.emptyTo (Spec ↧ℂ))))` (needs `Mathlib.AlgebraicGeometry.Limits`; proof `rintro ⟨z⟩; exact (z.left (IsLocalRing.closedPoint ℂ)).elim`, checked in scratch).
6. In the primed corollaries' docstrings, note that wherever `ProjectiveConnected` is imported the unprimed originals already apply through upstream's instance, so the primed forms record that the hypothesis is removable more than they add reach.
