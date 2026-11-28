# Red team: `de-rham-cup-exact` (statement and proof)

Date: 2026-11-27. Worktree `de-rham-cup-exact`, branch `track/de-rham-cup-exact`, base `b231d98` (main), WIP commit `cb7d97b` holding `HodgeLadder/De/Rham/Cup/Exact.lean` (module `HodgeLadder.De.Rham.Cup.Exact`, 11 declarations, not imported from the root, not in the ledger). Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`.

Read: the ledger entries `de-rham-cup-exact`, `de-rham-cup`, `de-rham-cup-test-p2`, `de-rham-cup-antisymm-h1`, `cup-hodge-filtration`, `cup-hodge-classes`; the module; `HodgeLadder/Hodge/{PairingProduct,WedgeSheafMap,RationalHypercohomology,RationalDeRhamComplex,DeRhamScalarSheaf,DeRhamInjective}.lean`, `HodgeLadder/Cup/{Product,CupSingular}.lean`, `HodgeLadder/Tests/OddDegreeTorus.lean`; `docs/sketches/cup-hodge-filtration.md` and its red team (finding 5, change 5), `docs/sketches/wedge-sheaf-map.redteam.md` (findings 2 and 8), `docs/sketches/de-rham-scalar-sheaf.redteam.md`; `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`; upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (`fieldToDeRhamCohomology`, line 698; `hodgeClasses`, line 917).

Scratch (`rt-scratch/*.lean` in the worktree, run with `lake env lean` against the module's olean, deleted afterwards). The module olean was current (`lake build HodgeLadder.De.Rham.Cup.Exact` reported no work); `HodgeLadder.Hodge.DeRhamScalarSheaf` was built once in the worktree (42 s) for RT4 and RT5.

| Probe | Content | Result |
|---|---|---|
| RT0 | `#print axioms` for all 11 declarations | standard three on each, 5 s |
| RT1 | `deRhamCup (ι [L₀]) (ι [L₁]) 4 _ ≠ 0` on `projectivePlane` (the title of rung `de-rham-cup-test-p2`) | compiles, 24 s with RT2 |
| RT2 | generic: if `ι (α ∪ β) = (−1)^{ab} • deRhamCup (ι α) (ι β)` and `ab` is odd, then `α ∪ β = 0` | compiles |
| RT3a to RT3d | on `𝔾ₘ²` at degrees (1, 1): nonvanishing, factor order detected, the `(−1)^{ab}`-twisted product fails the identity, antisymmetry with sign `−1` | compile, 15 s; as the test module of change 2, 25 s with axioms printed |
| RT4 | `deRhamShiftedHomEquiv X n (c • α) = deRhamShiftedHomEquiv X n α ≫ (Q.map (rationalDeRhamScalar X c))⟦n⟧'` as `rationalHypercohomologyEquiv_smul X n c α`, term mode | compiles, 7 s, no conversion |
| RT5 | `deRhamCup (c • x) y n h = c • deRhamCup x y n h` and `deRhamCup x (c • y) n h = c • deRhamCup x y n h` from RT4, `pairProductShQ_naturality` and the two scalar laws of `de-rham-scalar-sheaf` | compile, standard axioms, 45 s for the file |
| Profile | one `lake env lean -D profiler=true` run of the module | 242 s wall, 230 s kernel type checking |

**Verdict: pass with changes.** No sign other than Mathlib's Koszul `(−1)^p` enters the construction, and none is forced. One value comes out `−1` and it is the expected one: on `𝔾ₘ²`, `deRhamCup (ι x₂) (ι x₁) = −deRhamCup (ι x₁) (ι x₂)` (RT3d), the `(−1)^{1·1}` of graded commutativity, and `deRhamCup (ι x₁) (ι x₂)` is the class whose torus pairing is `−1` (`gm2_torusEval_cup`), the order reversal of the diagrammatic convention registered in row "Cup product". The identity `fieldToDeRhamCohomology_cup` is proved exactly, with no scalar, against upstream's `fieldToDeRhamCohomology`; it is non-vacuous in degree 0, in degrees (1, 1) and in degrees (2, 2), and it separates `deRhamCup` from the zero product, from its negative, from the swapped product and from the `(−1)^{ab}`-twisted product. The changes: move the file under `HodgeLadder/Hodge/`, add the `𝔾ₘ²` tests as a module of this rung, bookkeeping in the ledger, `docs/conventions.md`, `docs/gaps.md` and two sketches.

## 1. Is this the statement the literature makes?

Source: the de Rham isomorphism `H^*(X; ℂ) ≅ H^*_dR(X)` is compatible with products, the cup product of singular or sheaf cohomology going to the class of the wedge product of forms ([`Voisin2002`] I, de Rham theorem and products; section unverified). The singular cup is front face times back face and is graded commutative with sign `(−1)^{kl}` ([`Hatcher2002`] §3.2). The wedge obeys `d(θ ∧ η) = dθ ∧ η + (−1)^p θ ∧ dη` and the tensor product of complexes carries the Koszul sign `(−1)^p` ([`Dold1972`], sections unverified). Upstream states no product on `H_dR`, so the rung adds a definition and pins it to the ladder's checked cup product; nothing upstream states is restated.

| Literature / upstream | Lean | Check |
|---|---|---|
| comparison map `H^n(X; ℚ) → H^n_dR(X)` | `fieldToDeRhamCohomology ℚ X n` (upstream, `Filtration.lean:698`), the map `hodgeClasses` is built from (through `fieldToDeRhamCohomologyLinear`, line 917) | used as is; `deRhamShiftedHomEquiv_fieldToDeRhamCohomology` rewrites it through `forget_rationalDeRhamUnit`, which lies over upstream's `fieldToHolomorphicDeRhamComplexInt ℚ X` through `forgetUnitComplexIso`, the comparison the conventions row "Rational hypercohomology bridge" requires |
| cup product on `H^*(X; ℚ)` | `HodgeLadder.Cup.cup α β n h = e⁻¹(e α ≫ e β)` (Yoneda, diagrammatic) | checked comparison `Ψ (x ∪ y) = (−1)^{pq} cupSing (Ψ x) (Ψ y)` (row "Cup product"); so `α ∪ β = (−1)^{ab} α ⌣ β` against the literature's classical cup |
| wedge `Ω^p ⊗ Ω^q → Ω^{p+q}`, Koszul sign `(−1)^p` | `deRhamWedge X`, left factor on the left, `ε₂(p, q) = (−1)^p`, unit law exact | row "Wedge on complexes" (red team of `wedge-sheaf-map`, finding 2) |
| product on `H_dR` induced by the wedge | `deRhamCup x y n h := e⁻¹ (pairProductShQ μ (e y) (e x))`, `e = deRhamShiftedHomEquiv X` | `pairProduct m x' y'` is the class of `m (x' ⊗ y')` on cocycles (row "Pairing product (left action)"), so `deRhamCup x y` is the class of `y ∧ x`: the diagrammatic order of `Cup.cup`, equal to `(−1)^{ab}` times the literature's `x ∧ y` (heuristic, no forms-to-`H_dR` map at the pin) |
| `ι(α ⌣ β) = ι α ∧ ι β` | `fieldToDeRhamCohomology_cup : ι (α ∪ β) = deRhamCup (ι α) (ι β)` | both sides carry the same reversal: `ι((−1)^{ab} α ⌣ β) = (−1)^{ab} [ι α ∧ ι β] = [ι β ∧ ι α]`. So the Lean identity is the literature's ring-homomorphism statement, read in the ladder's diagrammatic order on both sides, with no leftover sign |

Signature drift against the sketch: `cup-hodge-filtration.md` (lines 72, 78) and its red team (lines 192, 198) write `deRhamCup X x y n h` with `X` explicit; the module has `X` implicit (`variable {X} in`). Implicit is the better form, since `x : H_dR^a(X)` fixes `X`; the sketches should follow the module (change 7).

## 2. Can the hypotheses be satisfied?

Yes. The hypotheses are `[IsIntegral X.left] [Smooth X.hom]` and a degree equation. They hold for `Spec ℂ`, for `gm2` (RT3a to RT3d) and for `projectivePlane` (RT1), each with a nonzero instance of the conclusion. `deRhamCup_one_one_ne_zero` and `_ne_neg` hold on every smooth integral `X` with no extra hypothesis (they use `nonempty_complexPoint`).

## 3. Is the conclusion trivially true?

No. Attempts:

* **Definition unfolding to a tautology.** `deRhamCup` is built from `pairProductShQ`, `deRhamWedge` and `deRhamShiftedHomEquiv` only; it does not mention `Cup.cup`, `fieldToDeRhamCohomology` or `ι⁻¹`, so the identity is a theorem about two independent constructions. The proof needs the unit law `deRhamWedge_unit_unit`, the naturality and the unit clause of the pairing, and the agreement `rationalHypercohomologyEquiv_rationalUnitComplex`; each is a checked rung.
* **Zero product.** Excluded: `deRhamCup (ι 1) (ι 1) = ι 1 ≠ 0` (module), `deRhamCup (ι x₁) (ι x₂) ≠ 0` (RT3a), `deRhamCup (ι [L₀]) (ι [L₁]) ≠ 0` (RT1).
* **Negative product** `−deRhamCup`. Excluded by `deRhamCup_one_one_ne_neg`.
* **Degree-dependent sign** `(−1)^{ab} deRhamCup`. Agrees with the module on every pair with `ab` even, degree 0 included, so the module's own tests cannot tell them apart. RT2 shows that the twisted identity forces `α ∪ β = 0` whenever `ab` is odd; RT3c (`gm2_deRhamCup_twist_ne`) shows it fails on `𝔾ₘ²`. A sign `(−1)^a` or `(−1)^b` alone also has value `−1` at (1, 1) and is excluded by the same test. This is the reason the `𝔾ₘ²` tests belong in this rung (change 2).
* **Swapped product** `deRhamCup y x`. Excluded by RT3b (`gm2_deRhamCup_swap_ne`), from `gm2_cup_swap_ne`.
* **Unused hypothesis.** None: integrality and smoothness are needed to form `H_dR`, `h` fixes the target degree.

What the identity does not test: on rational classes `e (ι γ) = γ̂ ≫ (Q u)⟦n⟧` factors through the unit, so the identity depends on `μ` only through `(u ⊗ u) ≫ μ`, the unit law. Any chain map `μ'` with the same unit law gives a product satisfying the same identity. The positive-degree components of the wedge, the Leibniz sign among them, are invisible here. This costs nothing for cohomology: with ℂ-bilinearity (RT5) and the span of rational classes (`de-rham-rational-span`, smooth projective `X`), any two such products agree on `H_dR`, so the identity together with rung `de-rham-cup` determines `deRhamCup` on smooth projective `X`. A uniqueness lemma to that effect is a candidate new rung (finding 9). The form-level reading `deRhamCup [θ] [η] = [η ∧ θ]` stays without a Lean statement (change 5, Known weaknesses).

## 4. Interface rung

Not applicable: the rung is a definition with theorems, no structure of axioms.

## 5. Checker and axioms

`python3 tools/check.py --no-build` in the worktree: sorry scan, import clash and ledger checks accepted; the axioms step failed on a missing olean of an unrelated module (`HodgeLadder.Tests.ProjectivePlaneFundamentalEveryPoint`, merged in `6908d28` and not built in this worktree). The rung is not in the ledger yet, so the checker names none of its declarations. RT0 prints `[propext, Classical.choice, Quot.sound]` for all 11: `rationalUnitShiftedHom`, `rationalUnitShiftedHom_cup`, `deRhamShiftedHomEquiv`, `deRhamCup`, `deRhamCup_add_left`, `deRhamCup_add_right`, `deRhamShiftedHomEquiv_fieldToDeRhamCohomology`, `fieldToDeRhamCohomology_cup`, `deRhamCup_one_one`, `deRhamCup_one_one_ne_zero`, `deRhamCup_one_one_ne_neg`. Each is the declaration the ledger title means; the full `python3 tools/check.py` must pass after the move (change 1).

## 6. Conventions

| Convention | Used by | Truth depends on it | Register |
|---|---|---|---|
| Diagrammatic order of `Cup.cup` (Yoneda composition, `Ext.comp`) | `rationalUnitShiftedHom_cup`, `fieldToDeRhamCohomology_cup` | yes: the identity pairs `α ∪ β` with `deRhamCup (ι α) (ι β)`; the swapped product fails (RT3b) | row "Cup product", checked |
| Factor order of `deRhamCup`: `pairProduct μ (e y) (e x)` | definition | yes (RT3b) | row "de Rham cup order (proposed)": promote (change 4) |
| Koszul sign `(−1)^p` in Mathlib's tensor of complexes; wedge with no further sign | `deRhamWedge`, through `deRhamWedge_unit_unit` | only through the unit law on rational classes (section 3) | row "Wedge on complexes", checked |
| Pairing: left action, shift in the first variable only (`mapBifunctorShift₁Iso`, no sign); unit clause `pairProduct λ x y = y.comp x` | `pairProductShQ_naturality`, `pairProductShQ_unit` | yes: a `−1` in `λ` or a shift iso would rescale the identity | row "Pairing product (left action)", checked |
| Mathlib's `ShiftedHom.comp` through `shiftFunctorAdd'` (no sign), `Ext.comp_hom` | `rationalUnitShiftedHom_cup` | yes, exact | Mathlib, read from source; it is the composition `Cup.cup` is defined with, so no mismatch can enter |
| Bridge `rationalHypercohomologyEquiv` and its agreement with `rationalExtEquiv`, no scalar | `deRhamShiftedHomEquiv`, `deRhamShiftedHomEquiv_fieldToDeRhamCohomology` | yes: an automorphism of `ℚ_X` would rescale the identity | row "Rational hypercohomology bridge"; its status cell still reads "agreement stated, proof open" although rung `rational-hypercohomology-equiv` is checked (change 4) |
| `forgetRationalDeRhamIso` (inverse direction in `deRhamShiftedHomEquiv`) and `forget_rationalDeRhamUnit` through `forgetUnitComplexIso` | `deRhamShiftedHomEquiv_fieldToDeRhamCohomology` | yes: the unit must lie over upstream's `fieldToHolomorphicDeRhamComplexInt` | row "Rational de Rham complex and its comparison", checked |
| Same `deRhamShiftedHomEquiv` as the scalar bridge of `de-rham-scalar-sheaf` | consumers (`de-rham-cup`) | ℂ-bilinearity | RT4: `rationalHypercohomologyEquiv_smul` is the statement for `deRhamShiftedHomEquiv` by `exact`; RT5 assembles both scalar laws |
| Derived-category instances `rh*`, monoidal and additivity instances `wsm*` | module, RT4, RT5 | which `ShiftedHom` type the identity lives in | row "Derived-category instances in statements"; the tests on `gm2` and `projectivePlane` needed none |
| Degree bookkeeping: `h : a + b = n` for the user, `(add_comm b a).trans h` inside | `deRhamCup` | none (proofs of equalities in `ℤ` are irrelevant) | stated in the row (change 4) |

Cited inputs: the only external inputs are checked rungs (`pairing-product`, `wedge-sheaf-map`, `rational-hypercohomology-equiv`, `rational-de-rham-complex`, `de-rham-injective`, `cup-product`, `cup-graded-commutative`, `cup-odd-degree-gm2`) and upstream definitions at the pin. No `Prop` hypothesis encodes a convention from a paper.

## 7. Equality first

The rung is an identity, `ι (α ∪ β) = deRhamCup (ι α) (ι β)`, proved exactly: the final `rw [pairProductShQ_unit, rationalUnitShiftedHom_cup]` closes the goal with no scalar, no `zsmul` and no `neg`. The equality it serves is T1 of the Markman inventory through `cup-hodge-filtration` and `de-rham-cup-antisymm-h1`; neither exists as a checked rung yet, both are in the ledger.

## 7b. Non-vacuity

Smallest test that fails if the statement were trivially true: `deRhamCup_one_one_ne_zero`, in the module, stated with upstream's `fieldToDeRhamCohomology` and `Cup.one`, equal to upstream's `fieldCohomologyUnit` by `Cup.one_eq_fieldCohomologyUnit`. For the sign: `HodgeLadder.Tests.gm2_deRhamCup_twist_ne` (change 2), built from `HodgeLadder.Tests.gm2_cup_ne_zero` and `HodgeLadder.Cup.sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero`. For even positive degree: RT1, the title of rung `de-rham-cup-test-p2`, from `HodgeLadder.Tests.planeLines_cup_ne_zero`.

## 8. Pin drift

None. The branch is rebased on main `b231d98`; `git diff main..HEAD` touches only the new Lean file; `lakefile.toml` pins `2ead713179628a3c738197d5996f51c8a9c886ac`, the commit checked out under `.lake/packages/HodgeConjecture`. The upstream definitions the identity depends on (`fieldToDeRhamCohomology`, `fieldToHolomorphicDeRhamComplexInt`, `hypercohomologyAddEquivConstantCohomology`, `hypercohomologyMap`, `deRham_complex_smul_eq` for RT4) were read at that commit.

## Findings

1. **Signs.** Only Mathlib's Koszul `(−1)^p` enters, inside `deRhamWedge`, and on rational classes it enters only through the unit law. The single `−1` that comes out is the antisymmetry on `𝔾ₘ²` (RT3d), equal to the literature's `(−1)^{ab}` at `a = b = 1`; and `deRhamCup (ι x₁) (ι x₂)` is the class with torus value `−1`, the diagrammatic reversal of row "Cup product" (heuristically `[ω₂ ∧ ω₁]` with `ωᵢ = dzᵢ / (2πi zᵢ)`). Neither is a new convention.
2. **Degree-dependent sign excluded in odd degree.** The module's tests see degree 0 only, where every twist `ε(a, b)` with `ε(0, 0) = 1` is invisible. RT3c excludes `(−1)^{ab}`, `(−1)^a` and `(−1)^b` at (1, 1). Require it in the rung (change 2).
3. **Factor order.** `deRhamCup x y` applies `x` first and puts `y` on the left of `μ`; the identity holds in that order only (RT3b). Graded commutativity on rational classes has the literature sign (RT3d).
4. **`ι` is upstream's.** `fieldToDeRhamCohomology ℚ X` is the map upstream's `hodgeClasses` uses, and the proof reaches it through `forgetUnitComplexIso`, the comparison the bridge row requires.
5. **The consumer assembly goes through.** `deRhamShiftedHomEquiv` is literally the composite in `rationalHypercohomologyEquiv_smul` (RT4 by `exact`, after unfolding `hypercohomologyMapIso.symm` to `hypercohomologyMap (forgetRationalDeRhamIso X).inv`, as `h3` of the module also does). RT5 proves both ℂ-linearity laws of rung `de-rham-cup` from checked pieces, 45 s for the file. Exact text in the section "RT5" below, for that rung's prover.
6. **Kernel cost.** One profiled run: 242 s wall, 230 s kernel type checking. By order in the profiler output (attribution by position, not by name): `deRhamShiftedHomEquiv` 28.9 s, `deRhamCup` 63.5 s, two entries of 6.9 s and 10.4 s before the first `unfold` (equation lemmas of `deRhamCup`, presumably), `deRhamCup_add_left` 11.3 s, `deRhamCup_add_right` 10.5 s, `deRhamShiftedHomEquiv_fieldToDeRhamCohomology` 60.6 s, `fieldToDeRhamCohomology_cup` 17.7 s, the three unit tests about 5.5 s each. Acceptable: the module is a leaf, the cost is paid only when it or an import changes, precedents are 307 s (`WedgeSheafMap`) and about 758 s (`RationalHypercohomology`), and consumers are cheap (tests 25 s, RT5 45 s). Record it (change 5).
7. **Placement.** `HodgeLadder/De/Rham/Cup/Exact.lean` is the path `tools/next.py` derives from the id; every neighbour (`WedgeSheafMap`, `DeRhamScalarSheaf`, `DeRhamInjective`, `PairingProduct`) is under `HodgeLadder/Hodge/`, and a later `HodgeLadder/De/Rham/Cup.lean` for `de-rham-cup` would sit beside a directory of the same name. Move it (change 1).
8. **Stale status cell.** The row "Rational hypercohomology bridge" still ends "agreement stated, proof open" (change 4).
9. **Candidate new rung (proposal, no change to this one).** `de-rham-cup-unique`: on smooth projective `X`, any family of biadditive, ℂ-bilinear products `P` on `H_dR^*` with `ι (α ∪ β) = P (ι α) (ι β)` equals `deRhamCup`. From `de-rham-rational-span` and RT5. It turns the identity of this rung into a characterization, which is the strongest form of "the sign is fixed by the definition".
10. **Ready next.** `de-rham-cup-test-p2` is RT1 verbatim (below); `de-rham-cup` is RT5 plus bookkeeping; with them `de-rham-cup-antisymm-h1` needs only `de-rham-rational-span` (checked).

## Required changes

1. Move `HodgeLadder/De/Rham/Cup/Exact.lean` to `HodgeLadder/Hodge/DeRhamCup.lean`, module `HodgeLadder.Hodge.DeRhamCup`; add `public import HodgeLadder.Hodge.DeRhamCup` to `HodgeLadder.lean`; remove the empty `HodgeLadder/De/` directory; run the full `python3 tools/check.py`.
2. Add the test module `HodgeLadder/Tests/DeRhamCupGm2.lean` with the text below (compiled in scratch against the current module path; replace the first import by `HodgeLadder.Hodge.DeRhamCup` after change 1); import it from `HodgeLadder.lean`.
3. Ledger entry `de-rham-cup-exact`: `"status": "checked"`, `"module": "HodgeLadder.Hodge.DeRhamCup"`, `"declarations"`: the 11 names of section 5 with prefix `HodgeLadder.` and `HodgeLadder.Tests.gm2_deRhamCup_ne_zero`, `HodgeLadder.Tests.gm2_deRhamCup_swap_ne`, `HodgeLadder.Tests.gm2_deRhamCup_twist_ne`, `HodgeLadder.Tests.gm2_deRhamCup_antisymm`; add `"cup-odd-degree-gm2"`, `"cup-graded-commutative"`, `"de-rham-injective"` to `depends_on` (the tests and `_ne_zero` use them). Append to the note: "Checked 2026-11-27: exact, no sign, no scalar; on rational classes the identity depends on μ only through deRhamWedge_unit_unit. Tests: degree 0 (deRhamCup_one_one_ne_zero, _ne_neg, in the module) and degrees (1, 1) on 𝔾ₘ² (HodgeLadder.Tests.DeRhamCupGm2: nonzero, factor order, the (−1)^{ab} twist fails, antisymmetry). Red team: docs/sketches/de-rham-cup-exact.redteam.md." Append to the note of `de-rham-cup`: "Update 2026-11-27 (red team of de-rham-cup-exact, RT5): deRhamCup_smul_left and deRhamCup_smul_right are proved in scratch from rationalHypercohomologyEquiv_smul, pairProductShQ_naturality (f = 𝟙, g = k = S_c, resp. f = k = S_c, g = 𝟙, m = m' = μ) and the two scalar laws, 45 s; exact text in docs/sketches/de-rham-cup-exact.redteam.md." Update `docs/roadmap.md` line 138 to `checked`.
4. `docs/conventions.md`: replace the row "de Rham cup order (proposed)" by

   ```
   | de Rham cup order | this repository, `HodgeLadder.deRhamCup`, `deRhamShiftedHomEquiv`, `fieldToDeRhamCohomology_cup` (`HodgeLadder/Hodge/DeRhamCup.lean`, rung `de-rham-cup-exact`); primitive `HodgeLadder.pairProductShQ`, row "Pairing product (left action)" | `deRhamCup x y n h := e⁻¹ (pairProductShQ μ (e y) (e x))`, `e = deRhamShiftedHomEquiv X` (upstream's hypercohomology along `(forgetRationalDeRhamIso X).inv`, then `rationalHypercohomologyEquiv`), `μ = deRhamWedge X`: diagrammatic order as in the row "Cup product", `x` applied first, `y` the left tensor factor of `μ`; degree proof `h : a + b = n`, passed to `pairProductShQ` as `(add_comm b a).trans h`. `ι (α ∪ β) = deRhamCup (ι α) (ι β)` with `ι = fieldToDeRhamCohomology ℚ X`, exact, no sign, no scalar. On rational classes the identity depends on `μ` only through the unit law `deRhamWedge_unit_unit`. Heuristically (no forms-to-`H_dR` map at the pin) `deRhamCup [θ] [η] = [η ∧ θ] = (−1)^{ab} [θ ∧ η]`, the same reversal as `Ψ (x ∪ y) = cupSing (Ψ y) (Ψ x)`; on `𝔾ₘ²`, `deRhamCup (ι x₂) (ι x₁) = −deRhamCup (ι x₁) (ι x₂)` | identities between products of complex classes (T1); none of `deRhamCup_mem_hodgeFiltration`, `CupRespectsHodgeFiltrationRational`, `CupPreservesHodgeClasses`, which are membership statements in additive subgroups | checked 2026-11-27 (rung `de-rham-cup-exact`); red team `docs/sketches/de-rham-cup-exact.redteam.md`: zero, negative, swapped and `(−1)^{ab}`-twisted products fail the identity (`deRhamCup_one_one_ne_zero`, `_ne_neg`, `Tests.gm2_deRhamCup_swap_ne`, `Tests.gm2_deRhamCup_twist_ne`) |
   ```

   In the row "Rational hypercohomology bridge", replace the last cell "statement red team 2026-11-27 (`docs/sketches/rational-hypercohomology-equiv.redteam.md`); agreement stated, proof open" by "statement red team 2026-11-27 (`docs/sketches/rational-hypercohomology-equiv.redteam.md`); checked (`rationalHypercohomologyEquiv_rationalUnitComplex`); used exactly by `fieldToDeRhamCohomology_cup` (rung `de-rham-cup-exact`)". In the row "Pairing product (left action)", fourth cell, replace "`de-rham-cup` (`deRhamCup x y := pairProduct μ y x`;" by "`de-rham-cup-exact` (`deRhamCup x y := pairProduct μ y x`;".
5. `docs/gaps.md`:
   * "General lemmas kept local", new row: "| `HodgeLadder.deRhamShiftedHomEquiv` (`H_dR^n(X) ≃+ Hom(ℚ_X[0], Ω•_ℚ[n])`), `deRhamCup`, `deRhamCup_add_left`, `deRhamCup_add_right`, `rationalUnitShiftedHom`, `rationalUnitShiftedHom_cup` (the cup product as `ShiftedHom.comp` on `ℚ_X[0]`) | `HodgeLadder.Hodge.DeRhamCup` | upstream has no product on `H_dR` and Mathlib none on derived categories of sheaves; the pairing it uses is the row of `HodgeLadder.Hodge.PairingProduct`; rung `de-rham-cup-exact` | 2026-11-27 |".
   * "Known weaknesses", append to the `mapBifunctorMap` kernel-cost row, before "| State consumers": " `HodgeLadder.Hodge.DeRhamCup` (rung `de-rham-cup-exact`): module about 242 s, 230 s kernel; by position in the profiler output `deRhamCup` 63.5 s, `deRhamShiftedHomEquiv_fieldToDeRhamCohomology` 60.6 s, `deRhamShiftedHomEquiv` 28.9 s, `fieldToDeRhamCohomology_cup` 17.7 s; consumers cheap (tests on `𝔾ₘ²` 25 s, both ℂ-linearity laws 45 s)."
   * "Known weaknesses", new row: "| `fieldToDeRhamCohomology_cup` depends on the wedge only through its unit law: on rational classes `e (ι γ)` factors through the unit `u`, so any chain map with the same unit law gives a product satisfying the same identity. The form-level reading `deRhamCup [θ] [η] = [η ∧ θ]` has no Lean statement (no forms-to-`H_dR` map at the pin) | No effect on cohomology for smooth projective X once `de-rham-cup` (ℂ-bilinearity) lands, by `de-rham-rational-span`; a statement about forms representing a product class would need the missing map | 2026-11-27 |".
6. Module docstring: name the local instances a consumer activates for statements about `deRhamCup` at a variable `X` (`rh*` of `HodgeLadder.Hodge.RationalHypercohomology`; `Cup.sheafMonoidal`, `analyticShQMonoidal` and the `wsm*` of `HodgeLadder.Hodge.WedgeSheafMap` for scalar laws), as `WedgeSheafMap` does; say that statements at a concrete space (`gm2`, `projectivePlane`) needed none.
7. Sketch signatures: in `docs/sketches/cup-hodge-filtration.md` lines 72 and 78 and in `docs/sketches/cup-hodge-filtration.redteam.md` lines 192 and 198, replace `deRhamCup X ` by `deRhamCup ` (`X` is implicit in the module).

### Test module text (change 2)

```lean
module

public import HodgeLadder.Hodge.DeRhamCup
public import HodgeLadder.Tests.OddDegreeTorus
public import HodgeLadder.Cup.CupSingular

/-!
# The de Rham cup product in degree `(1, 1)` on `𝔾ₘ²`

Tests for rung `de-rham-cup-exact`. With `x₁ x₂ ∈ H¹(𝔾ₘ²; ℚ)` the winding classes of the two
coordinates (rung `cup-odd-degree-gm2`) and `ι = fieldToDeRhamCohomology ℚ gm2`, the identity
`fieldToDeRhamCohomology_cup` transports `x₁ ∪ x₂ ≠ 0` and `x₁ ∪ x₂ ≠ x₂ ∪ x₁` to `H_dR²(𝔾ₘ²)`.
So in odd degree `deRhamCup (ι x₁) (ι x₂)` is nonzero, the factor order is visible, the product
twisted by `(−1)^{ab}` does not satisfy the identity, and graded commutativity holds with the
sign `(−1)^{1·1} = −1` of `Cup.cup_gradedComm`.

## Main results

* `HodgeLadder.Tests.gm2_deRhamCup_ne_zero`, `HodgeLadder.Tests.gm2_deRhamCup_swap_ne`,
  `HodgeLadder.Tests.gm2_deRhamCup_twist_ne`, `HodgeLadder.Tests.gm2_deRhamCup_antisymm`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Tests

local notation "x₁" => HodgeLadder.Cup.sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero
local notation "x₂" => HodgeLadder.Cup.sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero

/-- **Odd-degree nonvacuity.** `deRhamCup (ι x₁) (ι x₂) ≠ 0` in `H_dR²(𝔾ₘ²)`: by
`fieldToDeRhamCohomology_cup` it is `ι (x₁ ∪ x₂)`, `ι` is injective and `x₁ ∪ x₂ ≠ 0`. -/
theorem gm2_deRhamCup_ne_zero :
    deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
      2 (by norm_num) ≠ 0 := by
  intro h
  apply gm2_cup_ne_zero
  apply fieldToDeRhamCohomology_rat_injective gm2 2
  rw [map_zero, fieldToDeRhamCohomology_cup]
  exact h

/-- **The factor order is visible.** `deRhamCup (ι x₂) (ι x₁) ≠ deRhamCup (ι x₁) (ι x₂)`, from
`gm2_cup_swap_ne`. So the product with its arguments exchanged does not satisfy
`fieldToDeRhamCohomology_cup`. -/
theorem gm2_deRhamCup_swap_ne :
    deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₂) (fieldToDeRhamCohomology ℚ gm2 1 x₁)
        2 (by norm_num) ≠
      deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
        2 (by norm_num) := by
  intro h
  apply gm2_cup_swap_ne
  apply fieldToDeRhamCohomology_rat_injective gm2 2
  rw [fieldToDeRhamCohomology_cup, fieldToDeRhamCohomology_cup]
  exact h

/-- **No degree-dependent sign.** `ι (x₁ ∪ x₂) ≠ −deRhamCup (ι x₁) (ι x₂)`: the product twisted
by `(−1)^{ab}` does not satisfy `fieldToDeRhamCohomology_cup` at `a = b = 1`. -/
theorem gm2_deRhamCup_twist_ne :
    fieldToDeRhamCohomology ℚ gm2 2 (HodgeLadder.Cup.cup x₁ x₂ 2 rfl) ≠
      -deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
        2 (by norm_num) := by
  intro htw
  have hc : fieldToDeRhamCohomology ℚ gm2 2 (HodgeLadder.Cup.cup x₁ x₂ 2 rfl) =
      deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
        2 (by norm_num) := fieldToDeRhamCohomology_cup gm2 (a := 1) (b := 1) (n := 2) rfl _ _
  rw [hc, eq_neg_iff_add_eq_zero, ← two_nsmul] at htw
  have h2 : (2 : ℂ) • deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁)
      (fieldToDeRhamCohomology ℚ gm2 1 x₂) 2 (by norm_num) = 0 := by
    rw [ofNat_smul_eq_nsmul (R := ℂ)]; exact htw
  have h3 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [← hc] at h3
  exact gm2_cup_ne_zero (fieldToDeRhamCohomology_rat_injective gm2 2 (h3.trans (map_zero _).symm))

/-- **Graded commutativity, literature sign.** `deRhamCup (ι x₂) (ι x₁) = −deRhamCup (ι x₁) (ι x₂)`,
the sign `(−1)^{1·1}` of `Cup.cup_gradedComm` carried through `fieldToDeRhamCohomology_cup`. -/
theorem gm2_deRhamCup_antisymm :
    deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₂) (fieldToDeRhamCohomology ℚ gm2 1 x₁)
        2 (by norm_num) =
      -deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
        2 (by norm_num) := by
  have h12 : fieldToDeRhamCohomology ℚ gm2 2 (HodgeLadder.Cup.cup x₁ x₂ 2 rfl) =
      deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
        2 (by norm_num) := fieldToDeRhamCohomology_cup gm2 (a := 1) (b := 1) (n := 2) rfl _ _
  have h21 : fieldToDeRhamCohomology ℚ gm2 2 (HodgeLadder.Cup.cup x₂ x₁ 2 rfl) =
      deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₂) (fieldToDeRhamCohomology ℚ gm2 1 x₁)
        2 (by norm_num) := fieldToDeRhamCohomology_cup gm2 (a := 1) (b := 1) (n := 2) rfl _ _
  rw [← h12, ← h21, HodgeLadder.Cup.cup_gradedComm gm2 x₂ x₁ rfl, map_zsmul]
  norm_num

end HodgeLadder.Tests
```

### RT1 (for rung `de-rham-cup-test-p2`)

Compiled with imports `HodgeLadder.De.Rham.Cup.Exact` and `HodgeLadder.Tests.CupPositiveDegreeP2`, `open CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder HodgeLadder.Tests`, no local instances:

```lean
set_option maxHeartbeats 400000 in
example :
    deRhamCup
      (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)))
      (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1)))
      4 (by norm_num) ≠ 0 := by
  intro h
  apply planeLines_cup_ne_zero
  apply fieldToDeRhamCohomology_rat_injective projectivePlane (2 * (1 + 1))
  rw [map_zero, fieldToDeRhamCohomology_cup]
  exact h
```

### RT5 (for rung `de-rham-cup`)

Imports `HodgeLadder.De.Rham.Cup.Exact` and `HodgeLadder.Hodge.DeRhamScalarSheaf`, with the two `attribute [local instance]` blocks of the module (the `rh*` list, then `Cup.sheafMonoidal`, `analyticShQMonoidal` and the three `wsm*`); `open CategoryTheory Limits AlgebraicGeometry ComplexPoint HodgeLadder DerivedCategory`. Standard axioms. The right-factor law is the same proof with `hx : e x = e x ≫ (Q.map (𝟙 Ω•_ℚ))⟦a⟧'`, `f = S_c`, `g = 𝟙`, and `rationalDeRhamScalar_tensorHom_id_comp_deRhamWedge`.

```lean
set_option maxHeartbeats 1000000 in
theorem rt_deRhamCup_smul_left (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (c : ℂ)
    {a b : ℤ} (x : H_dR^a(X)) (y : H_dR^b(X)) (n : ℤ) (h : a + b = n) :
    deRhamCup (c • x) y n h = c • deRhamCup x y n h := by
  have hs : ∀ (k : ℤ) (z : H_dR^k(X)), deRhamShiftedHomEquiv X k (c • z) =
      deRhamShiftedHomEquiv X k z ≫ (Q.map (rationalDeRhamScalar X c))⟦k⟧' :=
    fun k z => rationalHypercohomologyEquiv_smul X k c z
  apply (deRhamShiftedHomEquiv X n).injective
  rw [hs]
  unfold deRhamCup
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hs]
  have hy : deRhamShiftedHomEquiv X b y = deRhamShiftedHomEquiv X b y ≫
      (Q.map (𝟙 (rationalDeRhamComplex X)))⟦b⟧' := by
    rw [CategoryTheory.Functor.map_id (DerivedCategory.Q (C := HodgeLadder.Cup.ShQ
        (TopCat.of (ComplexPoint X)))) (rationalDeRhamComplex X),
      CategoryTheory.Functor.map_id (shiftFunctor _ b), Category.comp_id]
  conv_lhs => rw [hy]
  exact pairProductShQ_naturality (TopCat.of (ComplexPoint X)) 0 (TopologicalSpace.dim X.left) 0
    (TopologicalSpace.dim X.left) (𝟙 (rationalDeRhamComplex X)) (rationalDeRhamScalar X c)
    (rationalDeRhamScalar X c) (deRhamWedge X) (deRhamWedge X)
    (rationalDeRhamScalar_id_tensorHom_comp_deRhamWedge X c).symm ((add_comm b a).trans h) _ _
```

Attempts that failed on the way: `rw [Functor.map_id, Functor.map_id, Category.comp_id]` for `hy` timed out at 200000 heartbeats (`isDefEq`); naming the functors explicitly fixed it. A plain `rw [hy]` rewrote both occurrences of `e y` and broke the `exact`; `conv_lhs` fixed it. `dim` needs the `TopologicalSpace.` prefix outside the module's `open`.

## Not done

A form-level test of `deRhamCup [θ] [η] = [η ∧ θ]` (no forms-to-`H_dR` map at the pin; change 5). The uniqueness rung of finding 9. A per-declaration kernel profile by name (the attribution in finding 6 is by position). The full `python3 tools/check.py` in the worktree: the worktree build lacks oleans of unrelated modules merged on main, and the rung is not yet in the ledger.
