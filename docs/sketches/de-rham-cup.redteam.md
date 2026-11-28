# Red team: `de-rham-cup` and `de-rham-cup-test-p2` (statement and proof)

Date: 2026-11-27. Worktree `de-rham-cup`, branch `track/de-rham-cup`, base `3913fdf`, WIP commit `0d61890` holding `HodgeLadder/Hodge/DeRhamCupBilinear.lean` (rung `de-rham-cup`, 9 declarations of its own) and `HodgeLadder/Tests/DeRhamCupP2.lean` (rung `de-rham-cup-test-p2`, 1 declaration), both imported from `HodgeLadder.lean`, ledger entries set to `checked`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Issues #210 and #211.

Read: the ledger entries `de-rham-cup`, `de-rham-cup-test-p2`, `de-rham-cup-exact`, `cup-hodge-filtration`, `cup-hodge-classes`, `de-rham-cup-antisymm-h1`; both modules; `HodgeLadder/Hodge/{DeRhamCup,DeRhamScalarSheaf,DeRhamRationalSpan}.lean`, `HodgeLadder/Tests/{CupPositiveDegreeP2,CycleClassMultiplicativeP2,ProjectivePlaneLines}.lean`, `HodgeLadder/Cup/CupSingular.lean` (`cup_gradedComm`); `docs/sketches/de-rham-cup-exact.redteam.md` (RT1, RT4, RT5, finding 9), `docs/sketches/de-rham-scalar-sheaf.redteam.md`, `docs/sketches/cup-hodge-filtration.md` (statement (a), "What T1 needs"); `docs/conventions.md`, `docs/gaps.md` (branch and `main`), `docs/references.md`; upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (the `SMul ℂ H_dR^n(X)` instance at line 659, `deRham_complex_smul_eq` line 662, `deRhamHypercohomologyComplexModule` line 669, `deRhamHypercohomologyModule` line 678, `fieldToDeRhamCohomology` line 698, `hodgeFiltration` line 783, `hodgeFiltrationComplexSubmodule` line 803) and `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean` (`cycleComponentSheafClass`, line 88).

Scratch: `rt-scratch/*.lean` in the worktree, run with `lake env lean` against the current oleans (`lake build --no-build` on both modules: all targets up to date), deleted afterwards.

| Probe | Content | Result |
|---|---|---|
| RT0 | `python3 tools/check.py --no-build` | ACCEPTED; standard three axioms on all 11 names of `de-rham-cup` and on `Tests.planeLines_deRhamCup_ne_zero` |
| RT1a | `(inferInstance : Module ℂ H_dR^n(X)) = deRhamHypercohomologyComplexModule X n := rfl`, in a file with no local instances | compiles |
| RT1b | `deRhamCupBilinear X a b n h (c • x) y = hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c) n (deRhamCup x y n h)` by `rw [LinearMap.map_smul₂]; rfl`, and the same in the second factor by `rw [map_smul]; rfl` | compile |
| RT1c | `deRhamCup_smul_left c x y n h` closes the goal with both `c •` written as upstream's `hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c)` | compiles by term |
| RT1d | `deRhamCup (q • x) y n h = q • deRhamCup x y n h` for `q : ℚ` (upstream's `deRhamHypercohomologyModule`, restriction of scalars) by `algebraMap_smul` and `deRhamCup_smul_left` | compiles |
| RT1e | `H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X) := deRhamCupBilinear X a b n h` with no local instances | compiles |
| RT6 | uniqueness: on smooth projective `X`, a `ℂ`-bilinear `P` with `P (ι α) (ι β) = ι (α ∪ β)` equals `deRhamCupBilinear` | compiles, 7 tactic lines, standard axioms |
| RT7 | `deRhamCup y x 2 _ = −deRhamCup x y 2 _` for all `x y : H_dR^1(X)`, smooth projective `X` (the title of `de-rham-cup-antisymm-h1`) | compiles, standard axioms; RT6 and RT7 together 34 s |
| RT8a | finite sums in each factor through `LinearMap.map_sum₂` and `map_sum` | compiles |
| RT8b | `Submodule.map₂ (deRhamCupBilinear X a b n h) F^p F^q ≤ F^{p+q}` (upstream's `hodgeFiltrationComplexSubmodule`) reduces to the elementwise statement (a) of `cup-hodge-filtration` by `Submodule.map₂_le` | compiles |
| RT8c | `Submodule.map₂ (deRhamCupBilinear …) (span s) (span t) = span (image2 deRhamCup s t)` by `Submodule.map₂_span_span` | compiles |
| RT8d | `ℤ`-scalars in the first factor by `map_zsmul` | compiles |
| RT9a | `deRhamCup (ι [L₀]) (ι [L₁]) 4 _ = ι [pt]` on `projectivePlane`, exact | compiles, `rw [← planeLines_cup_eq_planeOrigin, fieldToDeRhamCohomology_cup]; rfl` |
| RT9b | `deRhamCup (ι [L₀]) (ι [L₁]) 4 _ ≠ −ι [pt]` | compiles |
| RT9c | `decide`, `trivial`, `simp` on the statement of `planeLines_deRhamCup_ne_zero` | all three fail to close it |
| Timing | `lake env lean` on each module | `DeRhamCupBilinear` 28.7 s, `DeRhamCupP2` 8.9 s |

**Verdict, `de-rham-cup`: pass with changes.** The `ℂ`-action is upstream's `deRhamHypercohomologyComplexModule` on every `H_dR^k(X)` in the type of `deRhamCupBilinear` and in both scalar laws, definitionally (RT1a to RT1c); no conjugation, restriction of scalars or second instance enters. Both laws are exact, with no sign and no scalar other than `c`. The bundled map has the shape the three consumers need (RT7, RT8). The changes are bookkeeping in `docs/conventions.md`, `docs/gaps.md` and the ledger, one new rung (`de-rham-cup-unique`, proved in scratch), and a rebase onto `main`.

**Verdict, `de-rham-cup-test-p2`: pass with changes.** The test is derived from three checked inputs with content (`fieldToDeRhamCohomology_cup`, `fieldToDeRhamCohomology_rat_injective`, `planeLines_cup_ne_zero`), the classes are upstream's `cycleComponentSheafClass` of the two distinct coordinate lines, and the degrees are right. The change: add the exact value `deRhamCup (ι [L₀]) (ι [L₁]) = ι [pt]` and its sign test to the module (RT9a, RT9b), the even-degree analogue of the `𝔾ₘ²` tests that the red team of `de-rham-cup-exact` required in degree (1, 1).

No sign other than Mathlib's Koszul `(−1)^p` (inside `deRhamWedge`) enters either rung, and none is forced. Nothing comes out `−1` unexpectedly: the scalar laws carry no sign, RT9b excludes `−ι [pt]` on ℙ², and the one `−1` found (RT7) is the expected `(−1)^{1·1}` of graded commutativity on `H¹`.

## 1. Is this the statement the literature makes?

Source: the de Rham cup product on `H^*_dR(X) = ℍ^*(X, Ω•)` is induced by the wedge of holomorphic forms, a `ℂ`-bilinear map of complexes, so it is `ℂ`-bilinear on hypercohomology, and the comparison `H^*(X; ℚ) → H^*_dR(X)` is a ring homomorphism ([`Voisin2002`] I, holomorphic de Rham complex and products; section unverified). Upstream states no product on `H_dR`; the ledger rung adds the bilinearity of the local `deRhamCup` of rung `de-rham-cup-exact`. Nothing upstream states is restated.

| Literature / upstream | Lean | Check |
|---|---|---|
| complex structure on `H^n_dR(X)`, `c` acting by multiplication on forms | upstream `SMul ℂ H_dR^n(X)`: `c • α = hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c) n α` (`deRham_complex_smul_eq`, `rfl`); `Module ℂ` is `deRhamHypercohomologyComplexModule`, built by `hypercohomologyModule` from the same `smul` | RT1a: the instance elaborated in a consumer with no local instances is `deRhamHypercohomologyComplexModule` by `rfl`. RT1b, RT1c: the `c •` in `deRhamCup_smul_left`, `deRhamCup_smul_right` and in the `map_smul` fields of `deRhamCupBilinear` is upstream's hypercohomology map of `scalarHolomorphicDeRhamComplexInt X c`, by `rfl` |
| `(c θ) ∧ η = c (θ ∧ η) = θ ∧ (c η)` | scalar laws `rationalDeRhamScalar_tensorHom_id_comp_deRhamWedge`, `rationalDeRhamScalar_id_tensorHom_comp_deRhamWedge` (rung `de-rham-scalar-sheaf`), `S_c` tied to upstream's scalar by `forget_rationalDeRhamScalar` | the hypotheses `hm` of `pairProductShQ_naturality`, used with no conversion; `S_c` is upstream's scalar exactly, and the forget square determines it (`eq_rationalDeRhamScalar_of_forget`) |
| `c •` on `H_dR` through the bridge | `deRhamShiftedHomEquiv_smul : e (c • z) = e z ≫ (Q.map S_c)⟦k⟧'` | the term `rationalHypercohomologyEquiv_smul X k c z`, which rewrites with `deRham_complex_smul_eq`; so the bridge reads upstream's action, with no second action |
| bilinear in the first factor | `deRhamCup_smul_left : deRhamCup (c • x) y n h = c • deRhamCup x y n h` | `pairProductShQ_naturality` with `f = 𝟙`, `g = k = S_c`, `hm` the second-factor law: `x` is the right tensor factor of `μ` (definition `pairProductShQ μ (e y) (e x)`), so the second-factor law is the right one |
| bilinear in the second factor | `deRhamCup_smul_right` | `f = k = S_c`, `g = 𝟙`, `hm` the first-factor law; consistent with `y` the left tensor factor |
| bundled bilinear map | `deRhamCupBilinear X a b n h := LinearMap.mk₂ ℂ (fun x y => deRhamCup x y n h) …`, `_apply` by `rfl` | the curried order is `x` outer, `y` inner; the four fields are the two additivity laws of `de-rham-cup-exact` and the two scalar laws |

`ℚ`-scalars (RT1d) follow from the `ℂ`-law through upstream's restriction of scalars and `IsScalarTower`; they also follow from additivity alone, so the content of the rung is the law for `c ∉ ℚ`.

Test rung. Source: on ℙ², two distinct lines meet transversally in one point, `[L₀] ∪ [L₁] = [pt] ≠ 0` in `H⁴(ℙ²; ℚ) ≅ ℚ`, and the comparison to `H⁴_dR(ℙ²) ≅ ℂ` is injective ([`Hatcher2002`] §3.2 for the cohomology ring of `ℂP²`; section unverified).

| Literature | Lean | Check |
|---|---|---|
| `[Lᵢ] ∈ H²(ℙ²; ℚ)`, class of the line `{xᵢ = 0}` | `cycleComponentSheafClass projectivePlane (planeLine i) (coheight_planeLine i)`, upstream's fundamental class (`FundamentalClass.lean:88`) of the generic point `planeLine i` of the line, in `H^(2 * 1)` | upstream's definition, the class `algebraicCycleClassSpan` is spanned by; `planeLine_zero_ne_one` (`Tests/ProjectivePlaneLines.lean:274`) gives distinct lines |
| `ι = H²(ℙ²; ℚ) → H²_dR(ℙ²)` | `fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)` | upstream's map, the one `hodgeClasses` uses |
| degree `2 + 2 = 4` | `deRhamCup (ι [L₀]) (ι [L₁]) 4 (by norm_num)`, `h : ((2 * 1 : ℕ) : ℤ) + ((2 * 1 : ℕ) : ℤ) = 4` | right; injectivity is applied at `2 * (1 + 1)`, the degree of `planeLines_cup_ne_zero`, and `↑(2 * (1 + 1))` and `4` agree definitionally (the final `exact h`) |
| `ι [L₀] ∧ ι [L₁] ≠ 0` | `planeLines_deRhamCup_ne_zero` | matches the ledger title |

## 2. Can the hypotheses be satisfied?

Yes. `de-rham-cup`: `[IsIntegral X.left] [Smooth X.hom]` and a degree equation, satisfied by `Spec ℂ`, `gm2`, `projectivePlane`; `deRhamCup_smul_one_one_ne` holds on every smooth integral `X` with no further hypothesis (through `deRhamCup_one_one_ne_zero`, which supplies a complex point). The test has no hypotheses.

## 3. Is the conclusion trivially true?

No. Attempts:

* **Subsingleton target or trivial action.** Excluded: `deRhamCup_smul_one_one_ne` gives `c • ι 1 ≠ c' • ι 1` for `c ≠ c'`, so `H_dR^0(X) ≠ 0` and upstream's action is faithful on `ι 1`. This test reads the instance more than the product: given that the law is a theorem, a conjugate-linear law could hold as well only if `(c − conj c) • deRhamCup x y = 0` for all `x, y`, which the test excludes at `x = y = ι 1`. The guarantee that no conjugation entered is RT1a to RT1c (the instance is upstream's, definitionally), and the kernel check.
* **Bilinearity from additivity.** Holds for `ℚ`-scalars only. For `c ∉ ℚ` the proof needs the sheaf-level scalar laws and `rationalHypercohomologyEquiv_smul`; nothing in the additivity lemmas implies it.
* **Circularity.** `deRhamCup_smul_left` and `_right` use only `deRhamShiftedHomEquiv_smul` (from `de-rham-scalar-sheaf`), `deRhamShiftedHomEquiv_deRhamCup` (`AddEquiv.apply_symm_apply`), `deRhamShiftedHomEquiv_comp_map_id` (functor `map_id`) and `pairProductShQ_naturality`. No step mentions `Cup.cup` or `fieldToDeRhamCohomology`.
* **Unused hypotheses.** None.
* **Test by computation.** RT9c: `decide`, `trivial`, `simp` fail on the statement. The proof needs `planeLines_cup_ne_zero` (which rests on `[L₀] ∪ [L₁] = [pt]` and `[pt] ≠ 0`, rungs `cycle-class-multiplicative-p2` and `p2-point-class-nonzero`), injectivity and the exact identity.
* **Square-zero product.** Excluded by the test, which is its purpose. The zero product also satisfies bilinearity; the test and `fieldToDeRhamCohomology_cup` pin the product.

## 4. Interface rung

Not applicable: no structure of axioms.

## 5. Checker and axioms

`python3 tools/check.py --no-build` in the worktree: ACCEPTED (no sorry, no import clash, ledger well-formed). Axioms `[propext, Classical.choice, Quot.sound]` for `deRhamCup`, `fieldToDeRhamCohomology_cup`, `deRhamShiftedHomEquiv_smul`, `deRhamShiftedHomEquiv_comp_map_id`, `deRhamShiftedHomEquiv_deRhamCup`, `deRhamCup_smul_left`, `deRhamCup_smul_right`, `deRhamCupBilinear`, `deRhamCupBilinear_apply`, `deRhamCup_smul_one_one`, `deRhamCup_smul_one_one_ne` (all with prefix `HodgeLadder.`) and `HodgeLadder.Tests.planeLines_deRhamCup_ne_zero`. `lake build --no-build` reported both modules up to date, so the oleans the checker read are those of the source. Each name is the declaration the ledger title means.

Ledger listing of `deRhamCup` and `fieldToDeRhamCohomology_cup` under `de-rham-cup` (attack 4): acceptable, keep them. The title of `de-rham-cup` names both, the checker resolves them through the module's import of `HodgeLadder.Hodge.DeRhamCup`, the note says where they are declared, and the ledger has six earlier names listed under two rungs (`Cup.step3_named_class`, `Cup.cupSing_singClass`, `Cup.supported_singular_class`, `Cup.homologyMap_rawMap_bijective`, `Cup.supported_relative_cup`, `Tests.capCross_complex_model`). Dropping them would leave the title naming declarations the entry does not list.

## 6. Conventions

| Convention | Used by | Truth depends on it | Register |
|---|---|---|---|
| Upstream's `ℂ`-action `deRhamHypercohomologyComplexModule`, `c • α = hypercohomologyMap (scalarHolomorphicDeRhamComplexInt X c) α` | `deRhamCup_smul_left`, `_right`, `deRhamCupBilinear` | yes: a conjugate action on one side would break the identity | row "Complex structure on H_dR and on complex constant cohomology"; reconfirm for this rung (change 1) |
| `S_c` on `Ω•_ℚ` and the bridge `rationalHypercohomologyEquiv_smul`, no conjugation | `deRhamShiftedHomEquiv_smul` | yes | row "ℂ-scalars on the rational de Rham complex", checked |
| Factor order of `deRhamCup` (`x` the right tensor factor of `μ`) and which scalar law serves which factor | `deRhamCup_smul_left` (second-factor law), `_right` (first-factor law) | only for the proof; both laws hold, so the statement is symmetric in this choice | row "de Rham cup order"; record the pairing of laws to factors (change 2) |
| Curried order of `deRhamCupBilinear` (`x` outer, `y` inner) | consumers that `flip` it (RT7) | yes for antisymmetry statements | row "de Rham cup order" (change 2) |
| Pairing naturality, no sign (`pairProductShQ_naturality`, shift in the first variable only) | both laws | yes: a sign would rescale the law | row "Pairing product (left action)", checked |
| Degrees: `ℤ` for `deRhamCup` and `deRhamCupBilinear`, `ℕ` for `ι` and `fieldToDeRhamCohomology_cup`, cast `((n : ℕ) : ℤ)` | test, RT7 | none (casts of literals agree definitionally) | row "de Rham cup order" (change 2: consumers ascribe the type when rewriting at a literal degree) |
| Upstream fundamental-class normalization and point class | test (through `planeLines_cup_ne_zero`), RT9a | the value `ι [pt]` and its sign: yes; the nonvanishing: no | row "Fundamental-class normalization", pinned |

Cited inputs: only checked rungs (`de-rham-cup-exact`, `de-rham-scalar-sheaf`, `pairing-product`, `de-rham-injective`, `cup-positive-degree-test-p2`, `cycle-class-multiplicative-p2`) and upstream definitions at the pin. No `Prop` hypothesis encodes a convention from a paper.

## 7. Equality first

`de-rham-cup`: both laws are identities, proved exactly; the final `exact pairProductShQ_naturality …` closes each goal with no scalar, `neg` or `zsmul`. They are steps toward the identities T1 needs: antisymmetry on `H¹` (`de-rham-cup-antisymm-h1`, open, proved in scratch as RT7) and the characterization `de-rham-cup-unique` (proposed, RT6).

`de-rham-cup-test-p2`: an inequality, by design of a test rung. Its equality form `deRhamCup (ι [L₀]) (ι [L₁]) = ι [pt]` holds exactly with sign `+` (RT9a) and is distinguished from `−ι [pt]` (RT9b); change 5 adds both.

## 7b. Non-vacuity

`de-rham-cup`: the smallest test that fails if the law were trivially true is `HodgeLadder.deRhamCup_smul_one_one_ne`, in the module, stated with upstream's `fieldToDeRhamCohomology ℚ X 0` and `HodgeLadder.Cup.one X`. It exists.

`de-rham-cup-test-p2`: the rung is itself the non-vacuity test of `cup-hodge-filtration` against the square-zero product, built from `HodgeLadder.Tests.planeLines_cup_ne_zero`, `HodgeLadder.fieldToDeRhamCohomology_rat_injective` and `HodgeLadder.fieldToDeRhamCohomology_cup`. RT9b is the test that would fail for the negated product in degree (2, 2); in that degree `(−1)^{ab}`, `(−1)^a` and `(−1)^b` are all `+1`, so only a global sign is at stake, already excluded by `deRhamCup_one_one_ne_neg`; RT9b adds it for positive degree.

## 8. Pin drift

None. `lakefile.toml` pins `2ead713179628a3c738197d5996f51c8a9c886ac` on the branch and on `main`; the upstream definitions in section 1 were read at that commit. `main` has moved to `16daf66` (`cac8f9a` pin walk, `16daf66` `p1p1-witness`) with no change to `lakefile.toml`, `lake-manifest.json` or `lean-toolchain`; it does change `HodgeLadder.lean`, `ledger/ladder.json`, `docs/roadmap.md`, `docs/conventions.md` and restructures `docs/gaps.md` into categories with a layer column. Rebase before merging (change 7); the gaps text below is written for `main`'s layout.

## Findings

1. **The `ℂ`-action is upstream's on every side.** The `Module ℂ H_dR^k(X)` in the type of `deRhamCupBilinear` is `deRhamHypercohomologyComplexModule` by `rfl`, elaborated in a consumer with none of the module's local instances (RT1a, RT1e); the `c •` in both laws and in the bundled `map_smul` fields is upstream's hypercohomology map of `scalarHolomorphicDeRhamComplexInt X c` by `rfl` (RT1b, RT1c); the bridge `deRhamShiftedHomEquiv_smul` is `rationalHypercohomologyEquiv_smul`, which starts from `deRham_complex_smul_eq`. No conjugate-linear step and no `restrictScalars` enter. `ℚ`-scalars come through upstream's restriction of scalars (RT1d).
2. **Signs.** None in either rung. Each law is exact with scalar `c` only (`S_c` has degree zero, the pairing naturality carries no sign). The test's exact value is `+ι [pt]` (RT9a, RT9b). The `−1` of RT7 is graded commutativity on `H¹`, `(−1)^{1·1}`, carried from `Cup.cup_gradedComm`.
3. **Factor bookkeeping is right.** `x` is the right tensor factor of `μ`, so its law uses the second-factor scalar law, and conversely; the docstring says so, and the module compiles only in that pairing.
4. **Shape for the consumers.** `deRhamCupBilinear X a b n h` with `ℤ` degrees and explicit `X` serves all three: `cup-hodge-filtration` in its submodule form through `Submodule.map₂_le` (RT8b), `cup-hodge-classes` through `cup-hodge-reduction` (membership, no bilinearity needed), and `de-rham-cup-antisymm-h1` through `LinearMap.flip` and `LinearMap.ext_on` (RT7). Finite sums (RT8a), spans of products (RT8c) and `ℤ`-scalars (RT8d) come from Mathlib's `LinearMap` API with no new lemma. Nothing is missing for them.
5. **Two spelling frictions, no change required.** (a) `X` is explicit in `deRhamCupBilinear` and in `deRhamCup_add_left` (rung `de-rham-cup-exact`) and implicit in `deRhamCupBilinear_apply`, `deRhamCup_smul_left`, `deRhamCup`; a `simp only [← deRhamCupBilinear_apply …]` needs `(X := X)`. (b) `fieldToDeRhamCohomology_cup` produces `deRhamCup … ((n : ℕ) : ℤ) _`; a `rw` at a literal `ℤ` degree fails syntactically, and a `have` with the ascribed type fixes it (RT7, as in `Tests.gm2_deRhamCup_twist_ne`).
6. **The uniqueness rung is ready (finding 9 of the `de-rham-cup-exact` red team).** RT6 proves it in 7 lines from `span_range_fieldToDeRhamCohomology_rat` and `LinearMap.ext_on`. It turns `fieldToDeRhamCohomology_cup` into a characterization on smooth projective `X`, and it discharges the known weakness "depends on the wedge only through its unit law" on cohomology. Post it (change 4).
7. **`de-rham-cup-antisymm-h1` is ready.** RT7 is its title, from `de-rham-cup`, `de-rham-rational-span` and `cup-graded-commutative`, the three rungs its ledger entry names. Record the proof in its note (change 4).
8. **The test is derived with content, and the classes are the right ones.** Upstream's `cycleComponentSheafClass` of the generic points of `{x₀ = 0}` and `{x₁ = 0}` (distinct by `planeLine_zero_ne_one`), degree `2 · 1` each, product in degree 4 = `2 · (1 + 1)`; the three inputs are checked rungs and trivial closers fail (RT9c).
9. **The test can state the value.** `deRhamCup (ι [L₀]) (ι [L₁]) = ι [pt]` holds exactly (RT9a) and the negated value fails (RT9b). Equality first (decision 0004) favours recording the identity next to the inequality; the cost is about 10 s (change 5).
10. **Kernel cost.** `DeRhamCupBilinear` 28.7 s, `DeRhamCupP2` 8.9 s with `lake env lean`; both are leaves (`pinwalk.py --hubs`: 0 downstream, layers 23 and 29). No action.
11. **Ledger listing.** Keep `deRhamCup` and `fieldToDeRhamCohomology_cup` under `de-rham-cup` (section 5).

## Required changes

1. `docs/conventions.md`, row "Complex structure on H_dR and on complex constant cohomology", last column: append "; reconfirmed for `de-rham-cup` (red team 2026-11-27, `docs/sketches/de-rham-cup.redteam.md`): the `Module ℂ` in the type of `deRhamCupBilinear` is `deRhamHypercohomologyComplexModule` by `rfl` in a file with no local instances, and the `c •` of `deRhamCup_smul_left` and `_right` is `hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c)` by `rfl`".
2. `docs/conventions.md`, row "de Rham cup order": in the column "Fixed where", after "rung `de-rham-cup-exact`)", insert "; `HodgeLadder.deRhamCup_smul_left`, `deRhamCup_smul_right`, `deRhamCupBilinear` (`HodgeLadder/Hodge/DeRhamCupBilinear.lean`, rung `de-rham-cup`)". In the column "Choice", append "`ℂ`-bilinear for upstream's action, exact, no sign: `deRhamCup (c • x) y = c • deRhamCup x y` from the second-factor scalar law of `deRhamWedge` (`x` is its right tensor factor) and `deRhamCup x (c • y) = c • deRhamCup x y` from the first-factor law; bundled as `deRhamCupBilinear X a b n h : H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X)`, `x` the outer argument, so `(deRhamCupBilinear X b a n h').flip y x = deRhamCup y x n h'`. Degrees are `ℤ` for `deRhamCup` and `ℕ` for `ι`; `fieldToDeRhamCohomology_cup` produces the degree `((n : ℕ) : ℤ)`, and a rewrite at a literal degree needs the type ascribed". In the column "Status", append "; bilinearity checked 2026-11-27 (rung `de-rham-cup`, red team `docs/sketches/de-rham-cup.redteam.md`); on ℙ² `deRhamCup (ι [L₀]) (ι [L₁]) = ι [pt]`, sign `+` (`Tests.planeLines_deRhamCup_eq_planeOrigin`)".
3. `docs/gaps.md` (on `main`'s layout, after the rebase of change 7):
   * Category "De Rham complex and holomorphic forms", new row after the `HodgeLadder.Hodge.DeRhamCup` row: "| `HodgeLadder.deRhamCupBilinear` with `deRhamCupBilinear_apply` (the de Rham cup product as a `ℂ`-bilinear map `H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X)` for upstream's `deRhamHypercohomologyComplexModule`), `deRhamCup_smul_left`, `deRhamCup_smul_right`, `deRhamShiftedHomEquiv_smul`, `deRhamShiftedHomEquiv_deRhamCup`, `deRhamShiftedHomEquiv_comp_map_id` | `HodgeLadder.Hodge.DeRhamCupBilinear` | 23 | upstream has no product on `H_dR`; a pin bump that adds one, or a `Module ℂ` structure on hypercohomology other than `deRhamHypercohomologyComplexModule`, must be compared with this row; rung `de-rham-cup` | 2026-11-27 |".
   * "Known weaknesses", the row beginning "`fieldToDeRhamCohomology_cup` depends on the wedge only through its unit law": replace the second cell "No effect on cohomology for smooth projective X once `de-rham-cup` (ℂ-bilinearity) lands, by `de-rham-rational-span`; a statement about forms representing a product class would need the missing map" by "No effect on cohomology for smooth projective X: with `de-rham-cup` (checked) and `de-rham-rational-span`, a `ℂ`-bilinear product satisfying the identity equals `deRhamCupBilinear` (rung `de-rham-cup-unique`; proof in `docs/sketches/de-rham-cup.redteam.md`, RT6); a statement about forms representing a product class would need the missing map".
4. `ledger/ladder.json`:
   * New rung (and a `docs/roadmap.md` row "| `de-rham-cup-unique` | foundation | open | `de-rham-cup`, `de-rham-rational-span` | on smooth projective X a ℂ-bilinear P with P (ι α) (ι β) = ι (α ∪ β) is `deRhamCupBilinear` |", and an issue from the gap template):

     ```json
     {
       "id": "de-rham-cup-unique",
       "title": "deRhamCup is characterized by the rational cup product: on smooth projective X, a ℂ-bilinear P : H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X) with P (ι α) (ι β) = ι (α ∪ β) equals deRhamCupBilinear X a b n _",
       "status": "open",
       "kind": "foundation",
       "module": null,
       "declarations": [],
       "depends_on": ["de-rham-cup", "de-rham-rational-span"],
       "contributors": [],
       "note": "Proposed by the red team of de-rham-cup (docs/sketches/de-rham-cup.redteam.md, finding 6, RT6), after finding 9 of docs/sketches/de-rham-cup-exact.redteam.md. Statement: theorem deRhamCupBilinear_unique (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {a b n : ℕ} (h : a + b = n) (P : H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X)) (hP : ∀ (α : H^a(X; ℚ)) (β : H^b(X; ℚ)), P (fieldToDeRhamCohomology ℚ X a α) (fieldToDeRhamCohomology ℚ X b β) = fieldToDeRhamCohomology ℚ X n (Cup.cup α β n h)) : P = deRhamCupBilinear X a b n (by lia). Proved in scratch in 7 lines (LinearMap.ext_on twice with span_range_fieldToDeRhamCohomology_rat, then hP, deRhamCupBilinear_apply, fieldToDeRhamCohomology_cup), standard axioms; text in the red team file. It makes fieldToDeRhamCohomology_cup a characterization: on smooth projective X the product, sign and factor order included, is fixed by the rational cup product, and the dependence of the identity on the wedge through its unit law only (docs/gaps.md, Known weaknesses) has no effect on cohomology. Non-vacuity: P = deRhamCupBilinear satisfies hP, P = 0 and P = −deRhamCupBilinear fail it at a = b = n = 0 (deRhamCup_one_one_ne_zero, deRhamCup_one_one_ne_neg). Module HodgeLadder.Hodge.DeRhamCupUnique."
     }
     ```

   * `de-rham-cup-antisymm-h1`, append to the note: "Update 2026-11-27 (red team of de-rham-cup, RT7): theorem deRhamCup_antisymm_one (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x y : H_dR^1(X)) : deRhamCup y x 2 (by norm_num) = -deRhamCup x y 2 (by norm_num) is proved in scratch, standard axioms, from (deRhamCupBilinear X 1 1 2 _).flip = -deRhamCupBilinear X 1 1 2 _ by LinearMap.ext_on twice with span_range_fieldToDeRhamCohomology_rat, fieldToDeRhamCohomology_cup at ascribed degrees, Cup.cup_gradedComm (local instance openParacompactSpace X) and map_zsmul; text in docs/sketches/de-rham-cup.redteam.md."
   * `de-rham-cup`, append to the note: "Red team: docs/sketches/de-rham-cup.redteam.md (pass with changes): the ℂ-action in the type of deRhamCupBilinear and in both laws is deRhamHypercohomologyComplexModule by rfl; no sign; the bundled map serves cup-hodge-filtration (Submodule.map₂_le), de-rham-cup-antisymm-h1 (flip, ext_on) and de-rham-cup-unique."
   * `de-rham-cup-test-p2`: add `"HodgeLadder.Tests.planeLines_deRhamCup_eq_planeOrigin"` and `"HodgeLadder.Tests.planeLines_deRhamCup_ne_neg"` to `declarations`, `"cycle-class-multiplicative-p2"` and `"p2-point-class-nonzero"` to `depends_on`, and append to the note: "Exact value (red team docs/sketches/de-rham-cup.redteam.md, change 5): planeLines_deRhamCup_eq_planeOrigin, deRhamCup (ι [L₀]) (ι [L₁]) = ι [pt], sign +, from planeLines_cup_eq_planeOrigin; planeLines_deRhamCup_ne_neg excludes −ι [pt]."
5. `HodgeLadder/Tests/DeRhamCupP2.lean`: add the two theorems below after `planeLines_deRhamCup_ne_zero` (compiled in scratch against the module, 19 s for the scratch file, standard axioms) and list them under "Main results" in the module docstring.

   ```lean
   /-- **The value, exact.** `deRhamCup (ι [L₀]) (ι [L₁]) = ι [pt]` in `H_dR⁴(ℙ²)`, sign `+`, with
   `[pt]` the class of `[0 : 0 : 1]`: `planeLines_cup_eq_planeOrigin` carried through
   `fieldToDeRhamCohomology_cup`. -/
   theorem planeLines_deRhamCup_eq_planeOrigin :
       deRhamCup
         (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
           (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)))
         (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
           (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1)))
         4 (by norm_num) =
         fieldToDeRhamCohomology ℚ projectivePlane (2 * (1 + 1))
           (cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin_add) := by
     rw [← planeLines_cup_eq_planeOrigin, fieldToDeRhamCohomology_cup]
     rfl

   /-- **The sign.** `deRhamCup (ι [L₀]) (ι [L₁]) ≠ −ι [pt]`: `ι` is injective and `[pt] ≠ 0`. -/
   theorem planeLines_deRhamCup_ne_neg :
       deRhamCup
         (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
           (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)))
         (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
           (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1)))
         4 (by norm_num) ≠
         -fieldToDeRhamCohomology ℚ projectivePlane (2 * (1 + 1))
           (cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin_add) := by
     rw [planeLines_deRhamCup_eq_planeOrigin, ← map_neg]
     intro h
     have h2 := fieldToDeRhamCohomology_rat_injective projectivePlane (2 * (1 + 1)) h
     have h3 : (2 : ℚ) • cycleComponentSheafClass projectivePlane planeOrigin
         coheight_planeOrigin_add = 0 := by
       rw [two_smul]; nth_rewrite 2 [h2]; exact add_neg_cancel _
     exact projectivePlane_point_class_ne_zero ((smul_eq_zero.mp h3).resolve_left two_ne_zero)
   ```

   The scratch file imported `HodgeLadder.Tests.DeRhamCupP2` and opened `CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder HodgeLadder.Tests`; inside the module's `namespace HodgeLadder.Tests` with its `open` line the names resolve the same way.
6. Ledger and roadmap rows of `de-rham-cup-test-p2`: change the summary to "deRhamCup (ι [L₀]) (ι [L₁]) ≠ 0 on ℙ², and = ι [pt] with sign + (`HodgeLadder.Tests.DeRhamCupP2`)".
7. Rebase `track/de-rham-cup` onto `main` (`16daf66`) before the pull request; resolve `HodgeLadder.lean`, `ledger/ladder.json`, `docs/roadmap.md` and `docs/gaps.md` against `main`; run the full `python3 tools/check.py`.

### RT6 and RT7 (for rungs `de-rham-cup-unique` and `de-rham-cup-antisymm-h1`)

Imports `HodgeLadder.Hodge.DeRhamCupBilinear`, `HodgeLadder.Hodge.DeRhamRationalSpan`, `HodgeLadder.Cup.CupSingular`; `open CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder TopologicalSpace`; no local instances besides the one in RT7; default heartbeats; 34 s for the file; standard axioms on both.

```lean
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

theorem rt_deRhamCupBilinear_unique {a b n : ℕ} (h : a + b = n)
    (P : H_dR^a(X) →ₗ[ℂ] H_dR^b(X) →ₗ[ℂ] H_dR^n(X))
    (hP : ∀ (α : H^a(X; ℚ)) (β : H^b(X; ℚ)),
      P (fieldToDeRhamCohomology ℚ X a α) (fieldToDeRhamCohomology ℚ X b β) =
        fieldToDeRhamCohomology ℚ X n (Cup.cup α β n h)) :
    P = deRhamCupBilinear X a b n (by lia) := by
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat X a) ?_
  rintro _ ⟨α, rfl⟩
  refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat X b) ?_
  rintro _ ⟨β, rfl⟩
  rw [hP, deRhamCupBilinear_apply, fieldToDeRhamCohomology_cup]

theorem rt_deRhamCup_antisymm_one (x y : H_dR^1(X)) :
    deRhamCup y x 2 (by norm_num) = -deRhamCup x y 2 (by norm_num) := by
  let : ∀ U : Opens (ComplexPoint X), ParacompactSpace U := openParacompactSpace X
  have key : (deRhamCupBilinear X 1 1 2 (by norm_num)).flip =
      -deRhamCupBilinear X 1 1 2 (by norm_num) := by
    refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat X 1) ?_
    rintro _ ⟨α, rfl⟩
    refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat X 1) ?_
    rintro _ ⟨β, rfl⟩
    have h1 : fieldToDeRhamCohomology ℚ X 2 (Cup.cup β α 2 rfl) =
        deRhamCup (fieldToDeRhamCohomology ℚ X 1 β) (fieldToDeRhamCohomology ℚ X 1 α) 2
          (by norm_num) := fieldToDeRhamCohomology_cup X (a := 1) (b := 1) (n := 2) rfl β α
    have h2 : fieldToDeRhamCohomology ℚ X 2 (Cup.cup α β 2 rfl) =
        deRhamCup (fieldToDeRhamCohomology ℚ X 1 α) (fieldToDeRhamCohomology ℚ X 1 β) 2
          (by norm_num) := fieldToDeRhamCohomology_cup X (a := 1) (b := 1) (n := 2) rfl α β
    simp only [LinearMap.flip_apply, LinearMap.neg_apply, deRhamCupBilinear_apply]
    rw [← h1, ← h2, Cup.cup_gradedComm X β α rfl, map_zsmul]
    norm_num
  have := congrArg (fun B => B x y) key
  simpa [deRhamCupBilinear_apply] using this
```

Attempt that failed on the way: in RT7, `have h1 := fieldToDeRhamCohomology_cup X (a := 1) (b := 1) (n := 2) rfl β α` produced the degree `↑2`, and `rw [← h1]` did not find it in a goal at the literal `2`; the ascribed `have` fixed it (finding 5b).

### RT8 (consumer shapes, for `cup-hodge-filtration`)

Imports `HodgeLadder.Hodge.DeRhamCupBilinear`; `open CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder`; no local instances; 5 s.

```lean
example {a b n : ℤ} (h : a + b = n) (p q : ℤ)
    (H : ∀ x ∈ hodgeFiltration X p a, ∀ y ∈ hodgeFiltration X q b,
      deRhamCup x y n h ∈ hodgeFiltration X (p + q) n) :
    Submodule.map₂ (deRhamCupBilinear X a b n h) (hodgeFiltrationComplexSubmodule X p a)
      (hodgeFiltrationComplexSubmodule X q b) ≤ hodgeFiltrationComplexSubmodule X (p + q) n :=
  Submodule.map₂_le.mpr fun x hx y hy => H x hx y hy

example {ι : Type} (s : Finset ι) {a b n : ℤ} (h : a + b = n) (x : ι → H_dR^a(X))
    (y : H_dR^b(X)) : deRhamCup (∑ i ∈ s, x i) y n h = ∑ i ∈ s, deRhamCup (x i) y n h := by
  simp only [← deRhamCupBilinear_apply (X := X) n h, LinearMap.map_sum₂]
```

Attempts that failed on the way: `deRhamCupBilinear_apply X n h` (X is implicit there); `LinearMap.map_zsmul₂`, `LinearMap.map_smul_of_tower₂` and `LinearMap.zsmul_apply` do not exist at the pin; `map_zsmul` with `LinearMap.smul_apply` works.

## Not done

* A test of the scalar law at a non-real `c` computed independently of the law (for example through `fieldToDeRhamCohomology ℂ X` and a complex cup product): the ladder has no cup product on `H^*(X; ℂ)`, so the law can only be checked against its own consequences and against the instance (section 3).
* The general graded commutativity `deRhamCup y x = (−1)^{ab} • deRhamCup x y` on smooth projective `X` for all `a, b`: the proof of RT7 generalizes with `Cup.cup_gradedComm` at `(a, b)`; T1 needs only `H¹`, so no rung is proposed.
* The full `python3 tools/check.py` (with build) on the rebased branch: owed by change 7.
