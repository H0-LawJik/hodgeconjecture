# Red team: `cup-odd-degree-test` and its checked companions

Date: 2026-11-26. Branch `track/odd-degree-test` at `1d69994` (proof commit `6fe14fc`). Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same pin as the ledger toolchain block and as `cup-singular-comparison-absolute`. Targets: the checked rungs `torus-cycle-pairing`, `winding-torus-cup`, `singular-odd-cup-test`, `cup-odd-degree-transfer`, `gm2-witness`, `gm2-points`, `cup-odd-degree-gm2` (modules `HodgeLadder/Cup/{TorusPairing,TorusCycle,WindingTorus,OddDegree}.lean`, `HodgeLadder/Tests/{TorusSingular,AlgebraicTorus,AlgebraicTorusPoints,OddDegreeTorus}.lean`), the sketch `docs/sketches/cup-odd-degree-test.md`, the new conventions row "Torus cycle and winding classes", and the open rung `cup-odd-degree-test`. Scratch files were compiled with `lake env lean` in the worktree and deleted; each is described below by what it tests.

**Verdict: pass with changes.** The main claim `gm2_exists_cup_ne_zero : ∃ x y : H^1(gm2; ℚ), cup x y 2 rfl ≠ 0` is a statement about upstream's sheaf cohomology and the Yoneda `cup`, on an honest `Spec ℂ[x, y][(xy)⁻¹]` with honest instances. The values −1 and 1 are exact. The test separates (−1)^{pq} from +1 and from a square-zero product; a scratch lemma refutes the sign-free-and-unswapped comparison on 𝔾ₘ² outright. The changes (section 9) fix one wrong sentence about conventions (done in this pass in `docs/conventions.md`; the sketch still carries it), correct one overstatement in the sketch, sharpen the kill criterion, update the note of `cup-positive-degree-test`, and propose one added test lemma.

## 1. Is this the statement the literature makes?

The literature facts are: H¹(T²; ℚ) has basis α, β dual to the two circle factors and ⟨α ⌣ β, [T²]⟩ = 1 for the product orientation, with Hatcher's sign-free cup (φ ⌣ ψ)(σ) = φ(σ|[v₀,v₁]) ψ(σ|[v₁,v₂]) ([Hatcher2002] §3.2; the torus and surface computation is in that section, exact example number unverified); and the sheaf–singular isomorphism carries the sheaf product to the cup product up to conventions (recorded in `cup-singular-comparison-absolute.redteam.md`, sources unverified there).

| Literature | Lean | Check |
|---|---|---|
| 𝔾ₘ² = Spec ℂ[t₁^{±1}, t₂^{±1}] | `gm2 = Over.mk (ComplexPoint.affineSpecStructureMap gmRing)`, `gmRing = Localization.Away (X 0 * X 1)` in `MvPolynomial (Fin 2) ℂ` | scratch: `gm2.left = Spec (CommRingCat.of gmRing) := rfl` and `gm2.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ gmRing)) := rfl` both compile; `#print affineSpecStructureMap` shows upstream's reducible definition `Spec.map (ofHom (algebraMap ℂ R))`. ℂ[x, y][(xy)⁻¹] is ℂ[t₁^{±1}, t₂^{±1}] |
| H¹(X; ℚ), sheaf cohomology of the constant sheaf on X(ℂ) | `H^1(gm2; ℚ)`, upstream notation from `Definitions/AlgebraicGeometry/Hodge/Filtration.lean:301`, `Sheaf.H ((constantFunctor ↧(ComplexPoint X)).obj (AddCommGrpCat.of ℚ)) n` | the scheme-level notation is the one that elaborates (X is an `Over (Spec ↧ℂ)`); upstream's singular `H^` notation takes a `TopCat` |
| sheaf product | `HodgeLadder.Cup.cup` (rung `cup-product`, Yoneda), pinned exactly against Ψ and `cupSing` by `cup_singular_comparison` | not a new interface; decision 0003 holds |
| sheaf–singular isomorphism | upstream `rationalCohomologyAddEquivSingularCohomology` (`Other/.../GlobalSections.lean:310`), same four instance arguments as the local comparison theorem | read from source |
| x₁, x₂ | `sheafWindingClass gm2 gᵢ _ = Ψ⁻¹ (windingClass gᵢ _)` | genuine elements of upstream's H¹(gm2; ℚ); the local definitions only build the witnesses |
| α, β dual to the circles | `windingClass g` = `(cohIso Y 1).inv` of the class of the port's `rationalWindingCochain g` (σ ↦ (1/2πi)·(increment of log g along σ), read in ℚ) | `twoPiI = 2 * π * I` (port, `ChernWindingCochain.lean:125`); increment from vertex 0 to vertex 1 (`simplexIncrement`); `cohIso` is degreewise `ModuleCat.homLinearEquiv` with differentials equal by `rfl` (`dualIsoYoneda`), so no degree sign enters |
| [T²] | `σ₁ − σ₂`, σ₁ = T ∘ [(0,0),(1,0),(1,1)], σ₂ = T ∘ [(0,0),(0,1),(1,1)] (`lowerTriangle`, `upperTriangle`) | σ₁ is counterclockwise, σ₂ clockwise, so σ₁ − σ₂ carries ds ∧ dt; by hand ∂σ₁ − ∂σ₂ = (δ₀σ₁ − δ₂σ₂) + (δ₂σ₁ − δ₀σ₂) − (δ₁σ₁ − δ₁σ₂) = 0 under the three face identities `torus_h0/h1/h2` |
| Kronecker pairing on H² | `torusEval = torusPairing ∘ (cohIso Y 2).hom`, `torusPairing` the descent of φ ↦ φ(σ₁) − φ(σ₂) along `homologyIsCokernel` | well defined on cohomology by `torusEv_d` (coboundaries vanish) |
| ⟨α ⌣ β, [T²]⟩ = 1 | `torusEval_cupSing_winding` = 1, `_swap` = −1 | determinant formula checked by hand: (a ⌣ b)(σ₁) = a(δ₂σ₁) b(δ₀σ₁) = a(e) b(f); (a ⌣ b)(σ₂) = a(δ₂σ₂) b(δ₀σ₂) = a(f) b(e) by h0, h2. Edge values: e from (0,0) to (1,0), f from (1,0) to (1,1); g₁ = exp(2πi s) winds 1, 0; g₂ = exp(2πi t) winds 0, 1. Determinant 1·1 − 0·0 = 1. Matches the literature value and ∫ ds ∧ dt = 1 |
| 𝔾ₘ²(ℂ) ≅ ℂˣ × ℂˣ | `gmHomeomorph : ComplexPoint gm2 ≃ₜ puncturedSquare`, `puncturedSquare = {p : ℂ × ℂ // p.1 ≠ 0 ∧ p.2 ≠ 0}` with the subspace topology | through upstream's `affineSpecHomeomorph` (complex algebra maps with pointwise topology); scratch: `gmCoordOne z = (affineSpecHomeomorph gmRing z) gmX := rfl` compiles, so the first coordinate is evaluation of the point at the scheme coordinate x. The target is the subspace of ℂ × ℂ, which is homeomorphic to Mathlib's `ℂˣ × ℂˣ`; the Lean works with the subspace throughout |

Field by field, the Lean says what the literature says, with the orientation and order conventions written out.

## 2. Can the hypotheses be satisfied?

The general rungs (`torus-cycle-pairing`, `winding-torus-cup`, `cup-odd-degree-transfer`) take explicit data: faces, or (g₁, g₂, T) with periodicity and the two exponential identities. These are discharged twice by checked declarations: on `puncturedSquare` (`singular-odd-cup-test`, `standardTorus`, identities by `rfl`) and on `ComplexPoint gm2` (`gmTorus`, `gmCoordOne_gmTorus`, `gmCoordTwo_gmTorus`). The four instances for gm2:

- `IsIntegral gm2.left`: Spec of a domain (`IsLocalization.isDomain_localization` with x·y ≠ 0).
- `Smooth gm2.hom`: `HasRingHomProperty.Spec_iff` then `RingHom.smooth_algebraMap`, Mathlib's formal smoothness and finite presentation of a polynomial ring localized away from an element. Honest.
- `T2Space (ComplexPoint gm2)`: upstream `ComplexPoint.t2Space_of_isAffine`.
- `ParacompactSpace U` for every open U: metrizable as a subspace of ℂ × ℂ through `gmHomeomorph`, then Mathlib's paracompactness of (e)metric spaces.

Scratch `#synth` for each instance returns the local or upstream instance named above (`instT2SpaceComplexPointGm2`, `instParacompactSpaceSubtypeComplexPointGm2MemOpens`, `instIsIntegralLeftSchemeGm2`, `instSmoothHomSchemeGm2`); no unexpected instance path.

## 3. Trivially true?

Attempts, all in scratch:

- `⟨0, 0, _⟩` for the main claim: after `zero_cup'` (proved in five lines from `add_cup`) the goal is `0 ≠ 0`. It fails, as it should.
- No definition in the statement unfolds to `True`; the statement has no `ℕ∞`, no empty index type, no unused hypothesis (the instance arguments are used by Ψ inside `sheafWindingClass`, and the four are fixed instances, not hypotheses).
- Consistency probe: ⟨Ψ(x₁ ∪ x₁), T⟩ = 0, proved in four lines from `cup_singular_comparison_swap` and `torusEval_cupSing` (`ring` closes a − a). So `torusEval` is not a functional that is nonzero on every product.
- Corollary probe: `sheafWindingClass gm2 gmCoordOne _ ≠ 0` follows from `gm2_cup_ne_zero` and `zero_cup'` in two lines, so the witnesses are nonzero classes.

The nonvanishing is a consequence of the kernel-checked chain (comparison theorem, then a singular computation), and the singular computation is a determinant of four exactly computed edge values. No shortcut found.

## 4. Interface rung?

Not an interface rung. `cup-odd-degree-transfer` is a reduction whose hypotheses are a continuous map and two continuous functions on upstream's `ComplexPoint X` with stated identities; there is no structure and no axiom.

## 5. Checker

`python3 tools/check.py --no-build` in the worktree (build products dated with the sources): `ACCEPTED: all checks passed`, no sorry. Every declaration named by the seven new rungs is listed with axioms `[Classical.choice, Quot.sound, propext]`; scratch `#print axioms` on `gm2_exists_cup_ne_zero`, `gm2_torusEval_cup` and `gm2_cup_swap_ne` agrees. `#check @gm2_exists_cup_ne_zero` reads `∃ x y, cup x y 2 rfl ≠ 0` with `x y : H^1(gm2; ℚ)`. The declarations are the ones the ledger means: same names, same modules.

## 6. Conventions

| Convention | Used by | Row in `docs/conventions.md` | Truth depends on it? |
|---|---|---|---|
| Hatcher's sign-free cup, front face δ₂ times back face δ₀ | `torusPairing_tcCup` | "Singular cup product" | the values ±1 yes; nonvanishing no |
| face maps δᵢ skip vertex i (Mathlib `SimplexCategory.δ`) | `TorusCycle`, `torusPairing_tcCup` | covered by the cup row (front = δ₂ on a 2-simplex) | the identification of e, f; checked by `lowerFace_single` |
| orientation of the torus cycle, lower minus upper | `torusEval` | "Torus cycle and winding classes" | values flip with it; nonvanishing no |
| winding normalization (1/2πi)·d log g, increment from vertex 0 to vertex 1 | `windingClass` | same row | sign of the normalization: no (both classes negate, product unchanged); scale c: values scale by c² |
| ℚ-linear retraction ℂ → ℚ | `rationalWindingCochain` | same row | no: only the values 0 and 1 are read, and the class itself is independent of the retraction (values on 1-cycles are integers; not checked in Lean) |
| Ψ as defined upstream | `sheafWindingClass`, all `gm2_torusEval_*` | "Sheaf–singular comparison Ψ" | values yes |
| cohIso has no degree sign | `torusEval`, `windingClass`, `cupSing` | "Singular cup product" (cohIso, no sign) | if cohIso carried ε(n), torusEval would not be the Kronecker pairing; checked: degreewise `homLinearEquiv`, differentials by `rfl` |

Finding, fixed in this pass: the new row said that reversing either the cycle orientation or the winding normalization flips both values. Reversing the winding sign negates a₁ and a₂ together, so a₁ ⌣ a₂ and x₁ ∪ x₂ are unchanged; only the orientation (or exchanging s and t) flips the values. The row now says so, records the scale behaviour, states the convention-free content (the ratio −1 between the sheaf and singular values on the same cycle), and records the orientation check against ds ∧ dt. Sketch section 7, second bullet, repeats the wrong sentence and should be corrected the same way (change 1).

What can and cannot reproduce the computed pair (−1 for x₁ ∪ x₂, 1 for x₂ ∪ x₁), given `torusEval_cupSing_winding` = 1 on the same cycle:

- Comparison with sign +1, `Ψ(x ∪ y) = cupSing (Ψ x) (Ψ y)`: gives 1, not −1. Refuted in Lean, scratch (compiles): `¬ ∀ x y : H^1(gm2; ℚ), Ψ (cup x y 2 rfl) = cupSing (Ψ x) (Ψ y) 2 rfl`, by `gm2_torusEval_cup`, `torusEval_cupSing_winding` and `norm_num`.
- Square-zero product: gives 0. Refuted by `gm2_cup_ne_zero`.
- Degree twist Ψ' = ε(n)·Ψ: the value becomes ε(2)/ε(1)² times −1. For ε(n) = (−1)^{n(n−1)/2} that is +1, so the test detects that twist (and the refutation above covers it, since in degrees (1, 1) the twisted comparison is the +1 comparison). For ε(n) = cⁿ the value is unchanged; such twists satisfy the comparison theorem with the same sign, so no cup test can detect them, and the identity of record is insensitive to them.
- Back-face-first singular cup: would turn the sign into +1 against that cup. The sign is relative to Hatcher's convention, which is the recorded one.
- Orientation reversal: flips both singular and sheaf values together; the ratio stays −1.

So the test pins exactly what a cup computation can pin: Ψ(x ∪ y) = cupSing (Ψ y) (Ψ x), equivalently (−1)^{pq} against Hatcher's cup.

## 7. Equality first

`gm2_torusEval_cup` (= −1), `gm2_torusEval_cup_swap` (= 1), `torusEval_cupSing_winding` (= 1) and `_swap` (= −1) are exact rational equalities, not up to a scalar. The nonvanishing results are tests, not identity rungs. `torus-cycle-pairing` is an identity (the determinant formula), proved exactly.

### 7b. Non-vacuity

The smallest lemma that fails for a trivially true statement is `gm2_torusEval_cup` itself: a square-zero product gives 0, a sign-free comparison gives 1. It exists and is checked. For the singular side, `puncturedSquare_cupSing_swap_ne` is the non-vacuity test of `cupSing_gradedComm` in degrees (1, 1); it exists. Proposed addition (change 4): the refutation of the +1 comparison above, as a named test lemma, so that "the test distinguishes the sign" is a checked statement and not prose.

## 8. Pin drift

None. All seven rungs were built and checked at `2ead713`, the current pin in `lakefile.toml` and `lake-manifest.json`, which is also the pin at which `cup-singular-comparison-absolute` was checked. Mathlib's `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` at the pin has `PeriodPair.weierstrassP`, periodicity, pole order 2 and `derivWeierstrassP_sq`, as the sketch says.

## Weaker companion and the open rung

`cup-odd-degree-gm2` is a fair weaker companion. The comparison theorem has no projectivity hypothesis, so 𝔾ₘ² tests the sign and the non-square-zero property exactly as an elliptic curve would; it is affine, while the statements of record quantify over projective varieties (`IsProjective`). The original rung stays `open` with its statement unchanged; no weakening.

Sketch section 4 says 𝔾ₘ² is "the smallest variety with two independent H¹ classes and a nonzero product". An elliptic curve is a curve with that property, so the sentence is false as written; the true statement is that 𝔾ₘ² is the smallest affine example (an affine curve has H² = 0) and the simplest one available at the pin (change 2).

Relation to `cup-positive-degree-test` (ℙ¹ × ℙ¹, pr₁*[pt] ∪ pr₂*[pt] ≠ 0, depends on `cup-pullback`, `cycle-class-multiplicative`). Its ledger note gives its purpose as closing the vacuity gap of `cup-product` (the checked laws also hold for the square-zero product). That gap is now closed: `gm2_cup_ne_zero` is false for the square-zero product. Because the comparison pins `cup` against `cupSing` in every degree, a product that is square-zero only in even degrees would still have to match `cupSing` there; so even-degree non-vacuity of `cup` reduces to even-degree non-vacuity of `cupSing`, which no checked rung provides yet. `cup-positive-degree-test` keeps its own content: even degrees, a projective variety, and the cycle-class and pullback inputs it depends on. It is not discharged, in part or otherwise (change 3).

The elliptic-curve plan is sound in outline. The ℤ[i] choice is right: iΛ = Λ gives ℘(iz) = −℘(z) and g₃ = 0, and g₂ ≠ 0 follows from Δ ≠ 0. The g₁, g₂ of `elliptic-curve-torus-data` need the inverse of the uniformization, so the two-to-one counting of ℘ is on the critical path; there is no way around a continuous map E(ℂ) → S¹ × S¹ inside `cup-odd-degree-transfer` as stated. The kill criterion ("released twice without a stated sub-rung for the two-to-one counting") is hard to apply: the harness requires every release to name the missing lemma, so the condition is rarely met. Change 5 proposes a testable form.

## 9. Verdict: pass with changes

1. Sketch section 7, second bullet: replace "Reversing either flips both values" with the corrected statement now in the conventions row (orientation or exchanging s and t flips both values; the sign of the winding normalization does not change them; a scale c multiplies them by c²; the ratio −1 depends on none of it).
2. Sketch section 4: "the smallest variety with two independent H¹ classes and a nonzero product" becomes "the smallest affine variety ... (an affine curve has H² = 0); an elliptic curve is smaller but is not available at the pin".
3. Ledger note of `cup-positive-degree-test`: record that the square-zero vacuity of `cup` is closed in degrees (1, 1) by `cup-odd-degree-gm2`, and that the rung remains for even degrees, a projective variety and the cycle-class input. Reword the note of `cup-odd-degree-gm2` to match ("closes the square-zero vacuity of `cup` in degrees (1, 1); `cup-positive-degree-test` remains for even degrees").
4. Add a checked test lemma, for example `HodgeLadder.Tests.gm2_not_comparison_plus : ¬ ∀ x y : H^1(gm2; ℚ), Ψ (cup x y 2 rfl) = cupSing (Ψ x) (Ψ y) 2 rfl` (the scratch proof is five lines, given above), and name it in `cup-odd-degree-gm2`. Optional: `ledger` title of `gm2-points` could say "the subspace of ℂ × ℂ where both coordinates are nonzero", which is what the Lean proves.
5. Sketch section 6: replace the kill criterion with a testable one, for example: mark `cup-odd-degree-test` dead when `elliptic-curve-uniformization` reaches the harness's "needs split" state (three releases) and the counting sub-rung produced by the split is itself released; reopen as a new rung if Mathlib or upstream gains the analytic uniformization.

Done in this pass: the conventions row "Torus cycle and winding classes" (finding in section 6). No Lean file or ledger entry was edited.
