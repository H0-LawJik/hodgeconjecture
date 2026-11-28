# Red team: `de-rham-cup-unique` and `de-rham-cup-antisymm-h1` (statement and proof)

Date: 2026-11-27. Worktree `de-rham-cup-antisymm-h1`, branch `track/de-rham-cup-antisymm-h1`, base `e733367` (current `main`), WIP commit `660a4c0` holding `HodgeLadder/Hodge/DeRhamCupGradedComm.lean` (module `HodgeLadder.Hodge.DeRhamCupGradedComm`, 5 declarations), imported from `HodgeLadder.lean`; both ledger entries set to `checked`, roadmap rows updated, the `docs/gaps.md` "Known weaknesses" row on the unit law updated. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, unchanged by the commit. Issues #216 (`de-rham-cup-unique`) and #217 (`de-rham-cup-antisymm-h1`).

**Verdict, `de-rham-cup-unique`: pass with changes** (changes 2, 3, 4b).

**Verdict, `de-rham-cup-antisymm-h1`: pass with changes** (changes 1 to 4a; change 5 optional).

Both statements are the ones the red team of `de-rham-cup` proposed (RT6, RT7 of `docs/sketches/de-rham-cup.redteam.md`), unchanged; the general graded commutativity in all degrees is added. The sign `(−1)^{ab}` is the literature's, symmetric in `a` and `b`, so it does not depend on the diagrammatic factor order of `Cup.cup` or `deRhamCup`. No other sign enters. The changes are wording about non-vacuity (the affine `𝔾ₘ²` test is a separate theorem, and no projective `X` with `H¹ ≠ 0` exists at the pin), a conventions entry, a kept-local row, and ledger notes.

Read: the ledger entries `de-rham-cup-unique`, `de-rham-cup-antisymm-h1`, `cup-odd-degree-test`, `de-rham-cup`, `de-rham-cup-exact`; `python3 tools/next.py` for both rungs; the module; `HodgeLadder/Hodge/{DeRhamCup,DeRhamCupBilinear,DeRhamRationalSpan}.lean`, `HodgeLadder/Cup/CupSingular.lean` (`cup_singular_comparison'`, `cup_gradedComm`), `HodgeLadder/Tests/{DeRhamCupGm2,DeRhamCupP2}.lean`, the projective witnesses `HodgeLadder/Tests/{Witness,ProjectiveLine,ProjectivePlane,P1p1Witness}.lean`; `docs/sketches/de-rham-cup.redteam.md` (RT6, RT7, findings 5 to 7, "Not done"), `docs/sketches/de-rham-cup-exact.redteam.md` (finding 9), `docs/sketches/cup-hodge-filtration.md` ("What T1 needs from this rung"), `docs/notes/2026-11-25-markman-inventory.md` (§6, T1), `docs/strategy.md`; `docs/conventions.md` (rows "Cup product", "Singular cup product", "Wedge on complexes", "de Rham cup order"), `docs/gaps.md` (the #212 category layout), `docs/references.md`; upstream `HodgeConjecture/Statement.lean` (hypotheses of `HodgeConjecture`), `Lemmas/AlgebraicGeometry/ComplexPoint/{ProjectiveHausdorff,ProjectiveParacompact}.lean`.

Scratch: `rt-scratch/Probe.lean` and `rt-scratch/Odd.lean` (change 5) in the worktree, run with `lake env lean` against the current oleans, deleted afterwards. The final probe file compiles in 13 s wall time.

| Probe | Content | Result |
|---|---|---|
| RG0 | `python3 tools/check.py --no-build` | `ACCEPTED: all checks passed`; standard three axioms on all 5 names of the two rungs and on `Tests.gm2_deRhamCup_antisymm` |
| RG1 | `#print axioms` on the 5 declarations in a consumer file | `[propext, Classical.choice, Quot.sound]` on each |
| RG2 | `#synth T2Space (ComplexPoint X)` under `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]` | upstream's `IsProjective.complexPoint_t2Space`; the paracompactness instance is the proof-local `let` of `openParacompactSpace X` |
| RG3a | on `Tests.projectivePlane`, `(0 : bilinear) ≠ deRhamCupBilinear P2 0 0 0 _` and `-deRhamCupBilinear P2 0 0 0 _ ≠ deRhamCupBilinear P2 0 0 0 _` | compile, from `deRhamCup_one_one_ne_zero` and `deRhamCup_one_one_ne_neg` |
| RG3b | on `projectivePlane`, `P = -deRhamCupBilinear P2 2 2 4 _` fails the hypothesis `hP` of `deRhamCupBilinear_unique` (degree `(2, 2)`, positive degree on a projective `X`) | compiles: `deRhamCupBilinear_unique` turns `hP` into `-B = B`, and `B (ι [L₀]) (ι [L₁]) ≠ 0` (`Tests.planeLines_deRhamCup_ne_zero`) |
| RG4a | `rfl`, `simp; done`, `simp [deRhamCup]; done`, `simp [deRhamCup, deRhamShiftedHomEquiv]; done` on the statement of `deRhamCup_antisymm_one` | all four fail; `simp [deRhamCup]` stops at `e₂⁻¹ (pairProductShQ μ (e₁ x) (e₁ y)) = -e₂⁻¹ (pairProductShQ μ (e₁ y) (e₁ x))`, and the same at a smooth integral `Y` with no projectivity |
| RG4b | `rfl`, `simp; done`, `ext; simp [deRhamCup]; done` on `(deRhamCupBilinear X 1 1 2 _).flip = -deRhamCupBilinear X 1 1 2 _` | all fail; the statement follows from `deRhamCupBilinear_flip` by `simpa` |
| RG4c | `simp [deRhamCup]` on the wrong-sign statement `deRhamCup y x 2 _ = deRhamCup x y 2 _` at a smooth integral `Y` | stops at `pairProductShQ μ (e₁ x) (e₁ y) = pairProductShQ μ (e₁ y) (e₁ x)`; no closer |
| RG6a | `deRhamCup x x 2 _ = 0` for `x : H_dR^1(X)`, smooth projective `X` | compiles in 3 lines from `deRhamCup_antisymm_one` (`eq_neg_iff_add_eq_zero`, `two_smul`, `smul_eq_zero`) |
| RG6b | `deRhamCup x x n _ = 0` for `x : H_dR^a(X)`, `Odd a`, `a + a = n` | compiles in 3 lines from `deRhamCup_gradedComm` and `Odd.neg_one_pow` |
| RG6c | `(deRhamCupBilinear X 1 1 2 _).IsAlt` (Mathlib `LinearMap.IsAlt`) | compiles from RG6a |
| RG9 | `(deRhamCupBilinear P2 2 2 4 _).flip = deRhamCupBilinear P2 2 2 4 _` on `projectivePlane` | compiles from `deRhamCupBilinear_flip`; sign `+` in degree `(2, 2)`, as in the literature |

## 1. Is this the statement the literature makes?

Source. [Hatcher2002] §3.2 (Theorem 3.11, number recalled): for `α ∈ H^k(X; R)`, `β ∈ H^l(X; R)`, `R` commutative, `α ⌣ β = (−1)^{kl} β ⌣ α`. For de Rham cohomology, [Voisin2002] (volume I; section unverified): the wedge of forms satisfies `α ∧ β = (−1)^{kl} β ∧ α` and induces a graded-commutative product on `H^*_dR`. Both give, for `x` of degree `a` and `y` of degree `b`, `y ∪ x = (−1)^{ab} x ∪ y`.

Field by field against `deRhamCup_gradedComm X h x y : deRhamCup y x n _ = (−1 : ℤ)^(a * b) • deRhamCup x y n _`:

| Field | Literature | Lean | Agree |
|---|---|---|---|
| Space | smooth projective variety over ℂ, de Rham cohomology with ℂ-coefficients | `X : Over (Spec ↧ℂ)`, `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`, `H_dR^k(X)` = upstream's hypercohomology of the holomorphic de Rham complex | yes; the same hypotheses as upstream's `HodgeConjecture` (`Statement.lean`, line 44) |
| Degrees | `k, l ≥ 0`, product in degree `k + l` | `a b n : ℕ`, `h : a + b = n`, cast to `ℤ` for `H_dR` | yes; negative degrees are not covered, and the literature has none |
| Product | cup or wedge | `deRhamCup` (row "de Rham cup order": diagrammatic, `x` applied first) | yes up to factor order, which does not affect the sign (below) |
| Sign | `(−1)^{kl}` | `(−1 : ℤ)^(a * b)` as a `ℤ`-scalar | yes; `ℤ`-scalars agree with `ℂ`-scalars `(−1 : ℂ)^{ab}` on a `ℂ`-module, and `Module ℤ` on an additive group is unique |
| Side of the sign | either side, since the sign squares to 1 | the right side, the same form as `Cup.cup_gradedComm` | yes |

**Independence from the order convention.** Both `Cup.cup` and `deRhamCup` use the diagrammatic order (row "Cup product": `Ψ (x ∪ y) = cupSing (Ψ y) (Ψ x)`). Reversing the order replaces `(x, y, a, b)` by `(y, x, b, a)`, and `(−1)^{ab} = (−1)^{ba}`; so the identity reads the same for either convention. A convention mismatch of the withdrawal kind (arXiv:2610.30976) would need a sign that is asymmetric in `a` and `b`, such as `(−1)^a`; none occurs in the statement or proof.

**Independence from the comparison sign.** `Cup.cup_gradedComm` is derived through `cup_singular_comparison'` (sign `s(p, q) = (−1)^{pq}`) and Tau Ceti's `cupSing_gradedComm` (sign `g(p, q) = (−1)^{pq}`, Hatcher's front-back convention, row "Singular cup product"). The comparison sign enters on both sides and cancels whenever `s(p, q) = s(q, p)`, so the de Rham sign is `g`, the singular graded-commutativity sign. That one is a theorem of the vendored Tau Ceti stack, checked; no cited sign enters.

**Uniqueness.** `deRhamCupBilinear_unique` and `_eq_iff` have no literature counterpart to match field by field; they are the statement that a product on `H_dR` compatible with `ι` is determined, which holds whenever `ι` has `ℂ`-spanning image ([Voisin2002], comparison `H^k(X; ℂ) = H^k(X; ℚ) ⊗ ℂ`; rung `de-rham-rational-base-change`). The hypothesis `hP` uses the same `Cup.cup α β n h` and the same `ι = fieldToDeRhamCohomology ℚ X` as `fieldToDeRhamCohomology_cup`, with the factor order of the row "de Rham cup order". The theorem is the RT6 text unchanged.

**What is put first.** The proof's only sign is `(−1 : ℤ)^(b * a)` from `Cup.cup_gradedComm X β α`, turned into `(−1)^(a * b)` by `mul_comm`, and pushed through `ι` by `map_zsmul`. No `neg`, no `ℂ`-scalar, no `negOnePow` appears elsewhere in the module.

## 2. Can the hypotheses be satisfied?

Yes. `Tests.point`, `Tests.projectiveLine`, `Tests.projectiveSpace n` (with `projectivePlane`) and `Tests.p1p1` carry `IsIntegral`, `Smooth` and `IsProjective` instances (RG3 instantiates the theorems on `projectivePlane`). For `deRhamCupBilinear_unique`, `hP` is satisfiable by `deRhamCupBilinear_eq_iff` (forward direction, `P = deRhamCupBilinear`).

**Is integrality needed?** It is not needed mathematically; at the pin it is needed to state either result: `deRhamShiftedHomEquiv`, `deRhamCup` and `deRhamCupBilinear` are defined under `[IsIntegral X.left] [Smooth X.hom]` (`DeRhamCup.lean` line 132, `DeRhamCupBilinear.lean` line 76), and the span `span_range_fieldToDeRhamCohomology_rat` takes it too. It costs nothing against the target, whose statement of record carries the same three instances.

**Is projectivity needed?** Only through the span (and the `T2Space` and paracompactness instances that `Cup.cup_gradedComm` asks for, both supplied by projectivity, RG2). Mathematically graded commutativity holds on every smooth `X`; dropping projectivity would need either the span on that `X` or a derived-category proof through the braiding, which the ladder does not have (see "Not done").

## 3. Is the conclusion trivially true?

No.

* `H_dR` is not a subsingleton on projective `X` in the relevant degrees: degree 0 on every smooth integral `X` (`deRhamCup_one_one_ne_zero`), degree 4 on ℙ² (`Tests.planeLines_deRhamCup_ne_zero`). So the uniqueness conclusion `P = deRhamCupBilinear` is false for `P = 0` and `P = −deRhamCupBilinear` (RG3a at degree `(0, 0)`, RG3b at degree `(2, 2)`).
* `rfl` and `simp` (with and without unfolding `deRhamCup` and `deRhamShiftedHomEquiv`) fail on the antisymmetry and on the bundled flip (RG4a, RG4b); `simp [deRhamCup]` reduces each to an identity between `pairProductShQ` values with the factors swapped, with no closer. The wrong-sign statement reduces to the same kind of goal (RG4c), so nothing in the definitions decides the sign.
* Every hypothesis is used: `h` in the degree bookkeeping and in `Cup.cup α β n h`; `IsProjective` through the span and the `T2Space` instance; `IsIntegral` and `Smooth` in the definitions.
* No `ℕ∞` coercion, empty index type or definition unfolding to `True`.

The proofs are short (7 lines for uniqueness, 8 for the flip) because the content is in `span_range_fieldToDeRhamCohomology_rat` (rung `de-rham-rational-span`), `fieldToDeRhamCohomology_cup` (rung `de-rham-cup-exact`) and `Cup.cup_gradedComm` (rung `cup-graded-commutative`). That is the intended shape: these rungs transport known identities along a spanning map.

## 4. Interface rung

Not applicable: no structure, no `Prop` hypothesis encoding a cited result. The only hypotheses are instances that upstream's statement of record also carries.

## 5. Checker and axioms

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed` (placeholder scan clean, import clash none, ledger well-formed). Axioms line for each named declaration: `HodgeLadder.deRhamCupBilinear_unique`, `HodgeLadder.deRhamCupBilinear_eq_iff`, `HodgeLadder.deRhamCup_antisymm_one`, `HodgeLadder.deRhamCup_gradedComm`, `HodgeLadder.deRhamCupBilinear_flip`, each `[Classical.choice, Quot.sound, propext]`; also `HodgeLadder.Tests.gm2_deRhamCup_antisymm`. Each name is the declaration its ledger entry means: the `de-rham-cup-unique` note's statement is the type of `deRhamCupBilinear_unique` verbatim; the `de-rham-cup-antisymm-h1` title is the type of `deRhamCup_antisymm_one`.

Ledger declaration lists: `de-rham-cup-unique` lists `deRhamCupBilinear_unique` and `deRhamCupBilinear_eq_iff`; `de-rham-cup-antisymm-h1` lists `deRhamCup_antisymm_one`, `deRhamCup_gradedComm`, `deRhamCupBilinear_flip`. Correct: the general graded commutativity is stronger than the title and is the source of the `H¹` case, so it belongs with that rung. `depends_on` lists are right (the uniqueness file imports `CupSingular` only for the antisymmetry proofs).

## 6. Conventions

| Convention | Used by | Truth depends on it | Register |
|---|---|---|---|
| Graded-commutativity sign `(−1)^{ab}`, `ℤ`-scalar, on the right side | `deRhamCup_gradedComm`, `deRhamCupBilinear_flip`, `deRhamCup_antisymm_one` | yes (an identity); symmetric in `a`, `b`, so insensitive to the factor-order convention | missing from the row "de Rham cup order" (change 2) |
| Factor order of `deRhamCup` (diagrammatic) and the curried order of `deRhamCupBilinear` (`x` outer) | `flip` in `deRhamCupBilinear_flip`; `hP` in `deRhamCupBilinear_unique` | yes for `hP` (uniqueness fixes the product with this order); no for the sign | row "de Rham cup order", present |
| `Cup.cup` diagrammatic order and `cup_gradedComm` sign `(−1)^{pq}` | all three antisymmetry declarations | the sign only through `cupSing_gradedComm`; the comparison sign cancels (section 1) | rows "Cup product", "Singular cup product", present |
| `ℕ` degrees cast to `ℤ` for `H_dR`; `fieldToDeRhamCohomology_cup` rewritten at general `ℕ` degrees | all five | no (casts of literals agree definitionally; `simpa` handles `((1 : ℕ) : ℤ)`) | row "de Rham cup order", present |
| `ℂ`-action on `H_dR` (upstream's `deRhamHypercohomologyComplexModule`) | the types of `P` and `deRhamCupBilinear`; `LinearMap.ext_on` | uniqueness is for `ℂ`-bilinear `P` for this action | row "Complex structure on H_dR and on complex constant cohomology", present |
| Rational structure and `ι = fieldToDeRhamCohomology ℚ X` | the span, `hP` | yes for `hP` | row "Rational-to-de Rham map and the range of F^p", present |
| Mathlib's Koszul sign `(−1)^p` in the tensor differential | makes `deRhamWedge` a chain map; no step of these proofs | no (the identity on rational classes depends on the wedge through its unit law only) | row "Wedge on complexes", present |

No cited result enters: every input is a checked declaration of this repository or upstream, stated against the same definitions.

## 7. Equality first (decision 0004)

Both rungs are identities, proved exactly. `deRhamCup_gradedComm` has the sign `(−1)^{ab}` and no other scalar; `deRhamCup_antisymm_one` has `−1` and no other scalar; `deRhamCupBilinear_unique` is an equality of bilinear maps with no scalar. They are steps toward T1 (Weil classes on an abelian surface of Weil type, `docs/notes/2026-11-25-markman-inventory.md` §6), which also needs `cup-hodge-filtration` (open), `H¹_dR = F¹ ⊕ conj F¹` on an abelian surface, `b₁ = 4`, and pullback along endomorphisms on `H¹` with a definition of `W_K` (no rungs yet; `docs/sketches/cup-hodge-filtration.md`).

## 7b. Non-vacuity

* `de-rham-cup-unique`: the smallest separating tests exist: `HodgeLadder.deRhamCup_one_one_ne_zero` and `HodgeLadder.deRhamCup_one_one_ne_neg` (degree `(0, 0)`, every smooth integral `X`), and in positive degree on a projective `X`, `HodgeLadder.Tests.planeLines_deRhamCup_ne_zero` with `HodgeLadder.Tests.planeLines_deRhamCup_ne_neg` (degree `(2, 2)` on ℙ², RG3b). A sign twist `(−1)^{ab}` and the unsigned swap differ from `deRhamCup` only for `a`, `b` odd, so on a projective `X` they are separated only where `H^{odd} ≠ 0`; none such exists at the pin (next item). On `𝔾ₘ²` the twist and the swap fail the identity (`HodgeLadder.Tests.gm2_deRhamCup_twist_ne`, `gm2_deRhamCup_swap_ne`), but `𝔾ₘ²` is affine and outside the uniqueness theorem.
* `de-rham-cup-antisymm-h1`: every smooth projective integral `X` the ladder has at the pin is `Tests.point`, `Tests.projectiveLine`, `Tests.projectiveSpace n` or `Tests.p1p1` (the `IsProjective` instances in `HodgeLadder/` and upstream; the port's `IsProjectiveℂ` results build no new `X`). Each has first Betti number zero, so `H¹_dR(X) = 0` and `deRhamCup_antisymm_one` holds there with both sides zero; the ladder has no Lean statement of this vanishing. The test that would fail if the theorem were trivially true on projective `X` is a nonzero product of two `H¹` classes on a curve of positive genus or an abelian surface: rung `cup-odd-degree-test` (open, blocked on an elliptic-curve witness). `HodgeLadder.Tests.gm2_deRhamCup_antisymm` states the same identity on rational classes of the affine `𝔾ₘ²` with a nonzero product (`gm2_deRhamCup_ne_zero`) and with the sign `+1` refuted (`gm2_deRhamCup_swap_ne`). It is proved separately, from `Cup.cup_gradedComm` on `gm2` with no span, and is no instance of `deRhamCup_antisymm_one`; the current wording "the degree-(1, 1) witness is the affine test" in the module docstring, the ledger note and the roadmap row reads as if it were (change 1).
* For general `(a, b)`, `deRhamCup_gradedComm` has a nonzero instance with sign `+` on ℙ² in degree `(2, 2)` (RG9 together with `planeLines_deRhamCup_ne_zero`); every instance with sign `−` at the pin has both sides zero.

## 8. Pin drift

None. The commit is on `e733367` (current `main`) and leaves `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` unchanged: upstream `2ead713`, the pin of the `de-rham-cup` and `de-rham-cup-exact` red teams. Upstream definitions the results depend on: `fieldToDeRhamCohomology`, `deRhamHypercohomologyComplexModule`, `IsProjective.complexPoint_t2Space`, `openParacompactSpace`, `rationalCohomologyAddEquivSingularCohomology` (through `cup_gradedComm`), and the statement-of-record hypotheses. At a bump, a change to `fieldToDeRhamCohomology` or to the `ℂ`-module on `H_dR` would break `deRhamCupBilinear_unique` at the build or change what `hP` means; the kept-local row of change 3 names this.

## T1 fit

T1 works on an abelian surface `A` (smooth projective integral, `dim H¹_dR = 4`), with complex classes in `H^{1,0}` and `H^{0,1}`. `deRhamCup_antisymm_one` applies to all `x y : H_dR^1(A)` with no restriction to rational classes, and `deRhamCupBilinear X 1 1 2 _` is the bilinear map T1 would compose with. The shape fits. An exterior-square argument (`⋀² H¹ → H²`) consumes the alternating form `deRhamCup x x = 0`; over `ℂ` it follows from antisymmetry in 3 lines (RG6a), in every odd degree from the general form (RG6b), and as Mathlib's `LinearMap.IsAlt` (RG6c). Change 5 offers it. Nothing else in T1's list is supplied by these rungs, and no abelian surface exists at the pin.

## Findings

1. **The sign is the literature's and is convention-independent.** `(−1)^{ab}` agrees with [Hatcher2002] §3.2 and [Voisin2002]; it is symmetric in `a`, `b`, so the diagrammatic order of `Cup.cup` and `deRhamCup` does not affect it; the sheaf-singular comparison sign cancels; the sign that survives is Tau Ceti's checked `cupSing_gradedComm`. It agrees with `Tests.gm2_deRhamCup_antisymm` in degree `(1, 1)` and with the ℙ² value in degree `(2, 2)` (RG9). Nothing else comes out `−1`.
2. **Uniqueness has content on a projective `X`.** `0` and `−deRhamCupBilinear` fail `hP` at degree `(0, 0)` on every smooth integral `X` and at degree `(2, 2)` on ℙ² (RG3a, RG3b). A twisted or unsigned-swap product is separated only in odd degrees, where no projective `X` at the pin has cohomology; on `𝔾ₘ²` it fails, outside the theorem's hypotheses.
3. **No trivial proof.** `rfl` and `simp` with the definitions unfolded fail on both the correct-sign and the wrong-sign statements (RG4a to RG4c). The proofs rest on the span, the exact identity and the rational graded commutativity.
4. **Hypotheses.** Projectivity is used through the span and the `T2Space` instance; integrality is needed to state the definitions at the pin and matches upstream's statement of record.
5. **Non-vacuity wording overreaches (change 1).** The `𝔾ₘ²` test is a separate theorem on rational classes of an affine variety; the antisymmetry on projective `X` has only zero instances at the pin, and its first nonzero instance waits on `cup-odd-degree-test`.
6. **Conventions entry owed (change 2).** The row "de Rham cup order" does not yet record the graded-commutativity sign of `deRhamCup` or the uniqueness characterization.
7. **Kept-local row owed (change 3).** The module is layer 24 (`python3 tools/pinwalk.py --hubs`: 0 downstream) and belongs in the category "De Rham complex and holomorphic forms" after the `DeRhamCupBilinear` row (layer 23), like the two `deRhamCup` rows before it.
8. **Ledger notes (change 4).** The `de-rham-cup-unique` note keeps the planned module name `HodgeLadder.Hodge.DeRhamCupUnique` from the proposal; the appended "Checked" sentence names the real module, so no correction is needed, but both notes should cite this file.
9. **Placement.** One module for both rungs is reasonable (shared imports, 37 s); its name fits the antisymmetry rung, and the module docstring names both rung ids.
10. **Docstring precision (no change required).** "Mathlib's Koszul sign `(-1)^p` inside `deRhamWedge` enters only through `fieldToDeRhamCohomology_cup`" is accurate; on rational classes that identity uses the wedge only through its unit law (row "Wedge on complexes"), so the Koszul sign appears in no step of these proofs.

## Required changes

1. Non-vacuity wording.
   * `HodgeLadder/Hodge/DeRhamCupGradedComm.lean`, module docstring, section "Non-vacuity": replace the sentence beginning "For the antisymmetry, the ladder has" through "and antisymmetric." by: "For the antisymmetry, every smooth projective `X` the ladder has at the pin (`Tests.point`, `Tests.projectiveLine`, `Tests.projectiveSpace n`, `Tests.p1p1`) has first Betti number zero, so `deRhamCup_antisymm_one` has no instance with a nonzero product yet (no Lean statement of the vanishing); a projective instance waits on rung `cup-odd-degree-test`. The same identity on rational classes of the affine `𝔾ₘ²` is `HodgeLadder.Tests.gm2_deRhamCup_antisymm`, proved there from `Cup.cup_gradedComm` without the span: the product of the two generators is nonzero (`HodgeLadder.Tests.gm2_deRhamCup_ne_zero`) and the sign `+1` fails (`HodgeLadder.Tests.gm2_deRhamCup_swap_ne`). It is a separate theorem and no instance of `deRhamCup_antisymm_one`."
   * `ledger/ladder.json`, `de-rham-cup-antisymm-h1` note: replace "Non-vacuity: the ladder has no smooth projective X with H¹_dR(X) ≠ 0 at the pin; the degree-(1, 1) witness is the affine test HodgeLadder.Tests.gm2_deRhamCup_antisymm on 𝔾ₘ² (rung de-rham-cup-exact), with nonzero product gm2_deRhamCup_ne_zero." by "Non-vacuity: every smooth projective X at the pin (point, ℙ¹, ℙⁿ, ℙ¹ × ℙ¹) has b₁ = 0, so deRhamCup_antisymm_one has only zero instances there; a projective instance waits on cup-odd-degree-test. The same identity on rational classes of the affine 𝔾ₘ² is the separate theorem HodgeLadder.Tests.gm2_deRhamCup_antisymm (rung de-rham-cup-exact), with nonzero product gm2_deRhamCup_ne_zero and the sign +1 refuted by gm2_deRhamCup_swap_ne."
   * `docs/roadmap.md`, row `de-rham-cup-antisymm-h1`, last cell: replace "degree-(1, 1) witness on 𝔾ₘ² in `HodgeLadder.Tests.DeRhamCupGm2`" by "the same identity on rational classes of the affine 𝔾ₘ² is a separate test in `HodgeLadder.Tests.DeRhamCupGm2`; no projective X with H¹ ≠ 0 at the pin".
2. `docs/conventions.md`, row "de Rham cup order":
   * column "Fixed where": after "rung `de-rham-cup`)", insert "; `HodgeLadder.deRhamCup_gradedComm`, `deRhamCupBilinear_flip`, `deRhamCup_antisymm_one`, `deRhamCupBilinear_unique`, `deRhamCupBilinear_eq_iff` (`HodgeLadder/Hodge/DeRhamCupGradedComm.lean`, rungs `de-rham-cup-antisymm-h1`, `de-rham-cup-unique`)".
   * column "Choice": append "; graded commutativity on smooth projective integral X: `deRhamCup y x n _ = (−1 : ℤ)^(a * b) • deRhamCup x y n _` for `x : H_dR^a(X)`, `y : H_dR^b(X)`, `a b n : ℕ`, `a + b = n`, the sign as a `ℤ`-scalar on the right as in `Cup.cup_gradedComm`; bundled `(deRhamCupBilinear X b a n _).flip = (−1 : ℤ)^(a * b) • deRhamCupBilinear X a b n _`. The sign is symmetric in a and b, so it is the same for the diagrammatic and the Hatcher factor order; it comes from `cupSing_gradedComm`, the sheaf-singular comparison sign cancelling. On smooth projective integral X a `ℂ`-bilinear P with P (ι α) (ι β) = ι (α ∪ β) for all rational α, β equals `deRhamCupBilinear` (`deRhamCupBilinear_unique`), so the product, its sign and its factor order on cohomology are fixed by `Cup.cup`".
   * column "Results whose truth depends on it": append "; `deRhamCup_gradedComm` and `deRhamCup_antisymm_one` (the sign), `deRhamCupBilinear_unique` (the order in `hP`)".
   * column "Status": append "; graded commutativity and uniqueness checked 2026-11-27 (red team `docs/sketches/de-rham-cup-graded-comm.redteam.md`): sign `+` on ℙ² in degree (2, 2), sign `−` with a nonzero product only on the affine 𝔾ₘ² (`Tests.gm2_deRhamCup_antisymm`, a separate theorem); no projective X with H¹ ≠ 0 at the pin".
3. `docs/gaps.md`, "General lemmas kept local", category "De Rham complex and holomorphic forms": add after the row of `HodgeLadder.Hodge.DeRhamCupBilinear`:

   ```
   | `HodgeLadder.deRhamCupBilinear_unique`, `deRhamCupBilinear_eq_iff` (on smooth projective integral X a `ℂ`-bilinear `P` with `P (ι α) (ι β) = ι (α ∪ β)` is `deRhamCupBilinear`), `deRhamCupBilinear_flip`, `deRhamCup_gradedComm` (`deRhamCup y x n _ = (−1)^{ab} • deRhamCup x y n _`), `deRhamCup_antisymm_one` | `HodgeLadder.Hodge.DeRhamCupGradedComm` | 24 | upstream has no product on `H_dR`; a pin bump that adds one with a graded-commutativity or uniqueness lemma must be compared with this row (sign `(−1)^{ab}`, factor order of the row "de Rham cup order" in `docs/conventions.md`); rungs `de-rham-cup-unique`, `de-rham-cup-antisymm-h1` | 2026-11-27 |
   ```
4. `ledger/ladder.json`, notes:
   * (a) `de-rham-cup-antisymm-h1`, append: "Red team: docs/sketches/de-rham-cup-graded-comm.redteam.md (pass with changes): the sign (−1)^{ab} is Hatcher's and Voisin's graded commutativity, symmetric in a and b and so independent of the diagrammatic order of Cup.cup; it comes from cupSing_gradedComm with the comparison sign cancelling; rfl and simp fail on the correct-sign and the wrong-sign statements; deRhamCup x x 2 _ = 0 follows in 3 lines (for T1's exterior square)."
   * (b) `de-rham-cup-unique`, append: "Red team: docs/sketches/de-rham-cup-graded-comm.redteam.md (pass with changes): 0 and −deRhamCupBilinear fail hP at degree (0, 0) on every smooth integral X and at degree (2, 2) on ℙ² (from planeLines_deRhamCup_ne_zero); a (−1)^{ab}-twisted or unsigned-swap product is separated only in odd degree, where no projective X at the pin has cohomology (on 𝔾ₘ² gm2_deRhamCup_twist_ne and gm2_deRhamCup_swap_ne, outside the theorem). Integrality is needed to state deRhamCup at the pin and matches upstream's HodgeConjecture."
5. Optional, recommended for T1: add to `HodgeLadder/Hodge/DeRhamCupGradedComm.lean` (compiled in scratch against the module, standard axioms) and list under "Main results" and in the `de-rham-cup-antisymm-h1` declarations:

   ```lean
   /-- **Alternating in odd degree.** On a smooth projective integral `X` over `ℂ`, for `a` odd and
   `x : H_dR^a(X)`, `deRhamCup x x n _ = 0`: `deRhamCup_gradedComm` with `(-1 : ℤ) ^ (a * a) = -1`,
   and `2 • v = 0 → v = 0` in a `ℂ`-vector space. -/
   theorem deRhamCup_self_of_odd {a n : ℕ} (ha : Odd a) (h : a + a = n) (x : H_dR^a(X)) :
       deRhamCup x x n (by lia) = 0 := by
     have hg := deRhamCup_gradedComm X h x x
     rw [(ha.mul ha).neg_one_pow, neg_one_zsmul, eq_neg_iff_add_eq_zero, ← two_smul ℂ] at hg
     exact (smul_eq_zero.mp hg).resolve_left two_ne_zero
   ```

   With it, `(deRhamCupBilinear X 1 1 2 (by norm_num)).IsAlt` is the term `fun x => deRhamCup_self_of_odd X odd_one rfl x` (compiled in scratch, `rt-scratch/Odd.lean`, standard axioms).

## Attempts that failed or were reformulated

* RG4 first used `fail_if_success simp` and `fail_if_success ext`: both "succeeded" because the tactics made progress without closing the goal. Rewritten as `simp; done` and `ext; simp [deRhamCup]; done`, which fail as expected; an inspection run (`simp? [deRhamCup]`) showed the residual goals quoted in RG4a and RG4c.
* `fail_if_success exact?` on the antisymmetry: `exact?` finds `deRhamCup_antisymm_one` itself, which says nothing about triviality; dropped.
* RG3a first ended with `rw [← this, neg_neg]` after rewriting `deRhamCup_one_one` in the goal only; fixed by rewriting in both and closing with `neg_eq_iff_eq_neg.mp`.
* RG3b first wrote `(2 : ℂ) • deRhamCup _ _ ((4 : ℕ) : ℤ) _ = 0` with placeholders, which Lean could not elaborate; replaced by a lemma `∀ {k} (v : H_dR^k(P2)), -v = v → v = 0` applied to the hypothesis, which unifies the literal `4` with `((4 : ℕ) : ℤ)` definitionally.
* A projective `X` with `H¹ ≠ 0` was searched for among the `IsProjective` instances of `HodgeLadder/`, `port/` and upstream; none exists beyond point, ℙ¹, ℙⁿ, ℙ¹ × ℙ¹.

## Not done

* Graded commutativity on a smooth integral `X` without projectivity (it would make `Tests.gm2_deRhamCup_antisymm` an instance): it needs the span of rational classes on that `X` (the hook `span_range_fieldToDeRhamCohomology_rat_of_simplicialComplexSpan` asks for finitely generated singular homology) or a derived-category proof through the braiding with the twist `(−1)^{pq}` (row "Wedge on complexes"). T1 needs only projective `X`; no rung proposed.
* A Lean statement `H¹_dR(X) = 0` for the four projective witnesses: it would make the zero-instance claim of section 7b checked; it needs the cohomology of ℙⁿ in degree 1, which the ladder does not have.
