# Red team: `cup-hodge-filtration` (checked candidate) and the closure of `cup-hodge-classes`

Date: 2026-11-27. Worktree `cup-hodge-filtration`, branch `track/cup-hodge-filtration` at `22a24e5` (WIP on base `e733367`). `main` is one commit ahead (`a568e7b`, rungs `p1p1-fibres-transversal` and `cycle-class-multiplicative-p1p1`), which edits the ledger, roadmap, gaps and conventions and no Lean file this rung imports. Pin `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same as `main`. The statement-phase red team is `docs/sketches/cup-hodge-filtration.redteam.md`; this file reviews the proof and the ledger move.

Read: `HodgeLadder/Hodge/CupHodgeFiltration.lean`, `HodgeLadder/Tests/CupHodgeFiltrationP2.lean`, `HodgeLadder/Hodge/CupFiltration.lean`; `hodgeFiltration_eq_range_rational`, `rationalHodgeFilteredComplex`, `rationalHodgeFilteredInclusion` (`RationalDeRhamComplex.lean`); `deRhamWedgeFiltered`, `deRhamWedgeFiltered_comp_inclusion`, the bound instances (`WedgeSheafMap.lean`); `pairProductShQ_naturality` (`PairingProduct.lean`); upstream `hodgeFiltration`, `hodgeFiltrationComplexSubmodule`, `hodgePiece`, `hodgeClasses` (`Definitions/AlgebraicGeometry/Hodge/Filtration.lean:729-926`) and `Other/AlgebraicGeometry/Hodge/Filtration.lean`; Mathlib `DerivedCategory/TStructure.lean`, `Triangulated/TStructure/Basic.lean`; the ledger entries of the cup front; decisions 0008 to 0010; `docs/strategy.md`, `docs/roadmap.md`, `docs/conventions.md`, `docs/gaps.md`, `docs/statement.md`; the red teams of `de-rham-cup`, `de-rham-cup-exact`, `rational-de-rham-complex`, `wedge-sheaf-map`.

Scratch (`scratch_rt/` inside the worktree, deleted afterwards), after `lake build HodgeLadder.Hodge.CupHodgeFiltration HodgeLadder.Tests.CupHodgeFiltrationP2` (13 s incremental): RT1 axioms and types of the eight new declarations; RT2 trivial proof attempts; RT3 a local proof that `F^p = ⊥` above the dimension and two ℙ² tests on it; RT4 and RT7 `F^p H^n = ⊥` for `n < p`; RT5 the names the front closes on; RT6 the two ℙ² tests on upstream's `hodgeFiltration_eq_bot_of_lt`. Each file elaborated in 7 to 13 s.

**Verdict, `cup-hodge-filtration`: pass with changes.** The theorem is statement (a) as posted, with upstream's `hodgeFiltration` on both sides, for every integer degree and filtration index, on every smooth integral `X`. The proof is the planned naturality argument and uses each hypothesis; no sign or scalar enters, and the `q + p` to `p + q` swap is a rewrite of the goal's index alone. All declarations use the three standard axioms. The changes are a sharper non-vacuity test (checked in scratch), the ledger and root wiring, and bookkeeping.

**Verdict, `cup-hodge-classes`: pass with changes; move it from `stated` to `checked` in this PR.** `cupPreservesHodgeClasses_holds X : CupPreservesHodgeClasses X` and `cupRespectsHodgeFiltrationRational_holds X : CupRespectsHodgeFiltrationRational X` have the stated `Prop`s as their types, by name, so nothing is restated. The ledger entry must name the two theorems; a `Prop` definition alone passes `#print axioms` for any statement.

The cup front's rung list (decision 0009, items 1 to 8) is complete with this PR, and its win condition as amended by decision 0010 is met. Closing the front is due; decision text in change 9.

## 1. Is this the statement the literature makes?

Source: [`Voisin2002`] I: the wedge product maps `F^p Ω• ⊗ F^q Ω•` to `F^{p+q} Ω•`, so `F^p H^k ∪ F^q H^l ⊆ F^{p+q} H^{k+l}` on a compact Kähler manifold, and the Hodge classes form a graded subring of `⊕ H^{2k}(X; ℚ)` (section numbers unverified).

| Literature | Lean | Check |
|---|---|---|
| X smooth projective over ℂ | `X : Over (Spec ↧ℂ)`, `[IsIntegral X.left]`, `[Smooth X.hom]` | the same instance arguments upstream's `hodgeFiltration` and `hodgeClasses` take (`Filtration.lean:783`, `:917`), and nothing more. No `IsProjective`, no `T2Space`, no paracompactness. Stronger than the literature and true: the stupid filtration is multiplicative on any complex manifold |
| `F^p H^k(X; ℂ)` | `hodgeFiltration X p k`, `(filteredToDeRhamCohomology X p k).range`, `F^p Ω•` = `stupidTrunc (embeddingUpIntGE p)` | upstream's definition, read directly. `p, k : ℤ`, unrestricted |
| `∪` on `H^*(X; ℂ)` | `deRhamCup x y n h := e⁻¹ (pairProductShQ μ (e y) (e x))`, `μ = deRhamWedge X` | the local product of rungs `de-rham-cup-exact`, `de-rham-cup`: `ι (α ∪ β) = deRhamCup (ι α) (ι β)` exactly, ℂ-bilinear for upstream's action, nonzero with value `ι [pt]` on ℙ². Off the ℂ-span of `ι`, its only description is the construction; for projective X that span is everything (`deRhamRationalSpan`) |
| (a) `F^p ∪ F^q ⊆ F^{p+q}` | `deRhamCup_mem_hodgeFiltration {a b n} (h : a + b = n) {p q} hx hy` and `map₂_deRhamCupBilinear_le` for `hodgeFiltrationComplexSubmodule` | full strength: all `a b n p q : ℤ`. Both hypotheses carry content (section 3) |
| (a_ℚ) the same on `ι` of rational classes | `CupRespectsHodgeFiltrationRational X`: `∀ (a b n : ℕ) (h) (p q : ℤ) α β`, hypotheses and conclusion through upstream's `fieldToDeRhamCohomology ℚ X` and `hodgeFiltration` | `#print` (RT1) shows the definition unfolds to that quantifier, nothing trivial. Proof: `fieldToDeRhamCohomology_cup` then (a) |
| (b) `Hdg^p ∪ Hdg^q ⊆ Hdg^{p+q}` | `CupPreservesHodgeClasses X`: `∀ p q : ℕ`, `α ∈ Hdg^p(X; ℚ) → β ∈ Hdg^q(X; ℚ) → Cup.cup α β (2 * (p + q)) _ ∈ Hdg^(p + q)(X; ℚ)` | the literature's ring statement, upstream's `hodgeClasses` on both sides, the ladder's checked `Cup.cup` (pinned to the singular cup by `cup_singular_comparison'`). Proof: `cupPreservesHodgeClasses_of_rational` (rung `cup-hodge-reduction`, checked) of (a_ℚ) |

Degenerate readings of upstream's objects, checked at the pin:

- `hodgeFiltration X p n = ⊤` for `p ≤ 0` (`hodgeFiltration_eq_top_of_nonpos`; upstream `Other` has `hodgeFiltration_zero_eq_top`). So `Hdg^0 = ⊤`, as expected for `H^0`.
- `hodgeFiltration X p n = ⊥` for `dim X < p`: upstream's `AlgebraicGeometry.ComplexPoint.hodgeFiltration_eq_bot_of_lt` (`Other/AlgebraicGeometry/Hodge/Filtration.lean:262`; despite the name, the hypothesis is `(dim X.left : ℤ) < p`). It is in the import closure of the test module already (RT6). RT3 proved the same through `mem_hodgeFiltration_iff_exists_shiftedHom`; drop that local copy in favour of upstream's (decision 0011, use what upstream has).
- `hodgeFiltration X p n = ⊥` for `n < p` (RT4, RT7, new, 9 lines through Mathlib's t-structure on `D(ShQ)`). Upstream has no such lemma. This is the literature's `F^p H^n = 0` for `p > n`, which the conventions row "Rational-to-de Rham map and the range of F^p" lists as expected.
- `F^2 H^2_dR(ℙ²)` is a proper subgroup: `ι [L₀] ∉ hodgeFiltration projectivePlane 2 2` (RT6, finding 3). `F^3 H^4_dR(ℙ²) = ⊥` while `F^2 H^4_dR(ℙ²) ≠ ⊥`. So upstream's filtration on ℙ² is neither `⊤` nor `⊥` in degree 2 and in degree 4, which the statement-phase red team (its section 7b, last row) recorded as out of reach.
- `Hdg^1(ℙ²; ℚ)` contains `[L₀] ≠ 0`. A variety where `Hdg^p ≠ ⊤` with `p > 0` still needs a rational class outside `F^p`, for example on `E × E`; that is out of reach at the pin and stays a known weakness.

## 2. Can the hypotheses be satisfied?

Yes, with a nonzero product, on `projectivePlane` (integral, smooth, projective: `projectivePlane_witness`): `Tests.planeLines_deRhamCup_mem_hodgeFiltration` gives `ι [L₀], ι [L₁] ∈ F^1 H^2_dR` and `deRhamCup (ι [L₀]) (ι [L₁]) ∈ F^2 H^4_dR`, nonzero. For (b), `cup-hodge-classes-test-p2` gives Hodge classes with a nonzero product, and `Tests.planeOrigin_mem_hodgeClasses` gives `[pt] ∈ Hdg^(1 + 1)(ℙ²; ℚ)`, a codimension-two instance of the open rung `cycle-classes-are-hodge`.

## 3. Is the conclusion trivially true?

Attempts that failed (RT2):

- `simp_all [hodgeFiltration, filteredToDeRhamCohomology]` on (a) leaves `∃ x₁, hypercohomologyMap X (hodgeFilteredDeRhamInclusion X (p + q)) n x₁ = deRhamCup x y n h`.
- `exact ⟨0, by simp⟩` leaves `0 = deRhamCup x y n h`.
- `simp [hodgeFiltration, filteredToDeRhamCohomology]` on `hodgeFiltration X p n = ⊤` leaves the range goal; the statement is false (section 1).
- `simp_all [hodgeClasses, hodgePiece]` on (b) leaves the membership of `fieldToDeRhamCohomologyLinear ℚ X (2 * (p + q)) (Cup.cup α β _ _)`.

No definition unfolds to `True`, no index type is empty, no coercion collapses (`ℕ` to `ℤ` casts only, by `Nat.cast_add` in the reduction). Each hypothesis is needed, and the index `p + q` is sharp, by RT6 on ℙ²:

- without `hx`, take `y = ι [L₁] ∈ F^1`, `p = 2`: every `deRhamCup x y` would lie in `F^3 H^4 = ⊥`, against `planeLines_deRhamCup_ne_zero` at `x = ι [L₀]`;
- without `hy`, the same with the roles exchanged;
- with `F^{p+q+1}` in place of `F^{p+q}`, at `p = q = 1` the product would lie in `F^3 H^4 = ⊥`.

Circularity (attack item 5): the module imports `HodgeLadder.Hodge.DeRhamCupBilinear` and `HodgeLadder.Hodge.CupFiltration` only. The proof of (a) is: obtain the factorizations `x' ≫ (Q i_p)⟦a⟧'`, `y' ≫ (Q i_q)⟦b⟧'` (step 1), rewrite `e (deRhamCup x y)` by `deRhamShiftedHomEquiv_deRhamCup`, substitute, and apply `pairProductShQ_naturality` at `f = i_q`, `g = i_p`, `k = i_{q+p}`, `m = deRhamWedgeFiltered X q p`, `m' = deRhamWedge X`, `hm = deRhamWedgeFiltered_comp_inclusion X q p`. The `m'` is the `μ` of `deRhamCup` (`#print deRhamCup`, RT1: `pairProductShQ … 0 (dim X.left) (deRhamWedge X)`), with the same bounds `0, dim X.left`. Nothing in the chain uses (b), (a_ℚ) or a cycle-class statement. The filtered wedge is determined by its square, since `eq_truncMul_iff` (rung `wedge-sheaf-map`) makes it unique, so no choice of `m` can make the conclusion easier.

## 4. Interface rung?

No. The rung adds no structure, no axiom and no hypothesis of the shape "a product satisfying …". `CupPreservesHodgeClasses` and `CupRespectsHodgeFiltrationRational` are target `Prop`s, now proved.

## 5. Checker and declarations

`python3 tools/check.py --no-build` in the worktree: `ACCEPTED`. The two new modules are in neither the root nor the ledger, so this run did not judge them. RT1, `#print axioms`, each `[propext, Classical.choice, Quot.sound]`:

| Declaration | Rung (after change 1) |
|---|---|
| `HodgeLadder.deRhamShiftedHomEquiv_filtered` | `cup-hodge-filtration` |
| `HodgeLadder.mem_hodgeFiltration_iff_exists_shiftedHom` | `cup-hodge-filtration` |
| `HodgeLadder.deRhamCup_mem_hodgeFiltration` | `cup-hodge-filtration` |
| `HodgeLadder.map₂_deRhamCupBilinear_le` | `cup-hodge-filtration` |
| `HodgeLadder.cupRespectsHodgeFiltrationRational_holds` | `cup-hodge-classes` |
| `HodgeLadder.cupPreservesHodgeClasses_holds` | `cup-hodge-classes` |
| `HodgeLadder.Tests.planeLines_deRhamCup_mem_hodgeFiltration` | `cup-hodge-filtration-test-p2` (new) |
| `HodgeLadder.Tests.planeOrigin_mem_hodgeClasses` | `cup-hodge-filtration-test-p2` (new) |

RT6 and RT7 add `HodgeLadder.Tests.planeLine_not_mem_hodgeFiltration_two`, `HodgeLadder.Tests.plane_hodgeFiltration_three_four` and `HodgeLadder.hodgeFiltration_eq_bot_of_degree_lt`, same axioms. After changes 1 to 4 run the full `python3 tools/check.py`.

## 6. Conventions

| Convention | Used by | Truth depends on it? | Register |
|---|---|---|---|
| Cup product order (Yoneda, diagrammatic) | (a_ℚ), (b) | no: membership in an additive subgroup | row "Cup product", present |
| de Rham cup order: `x` applied first, `y` the left tensor factor of `μ` | (a): the filtered wedge is `deRhamWedgeFiltered X q p` with `y`'s index first, landing in `F^{q+p}`, then `add_comm p q` on the goal | no: the swap rewrites only the index of `hodgeFiltration X (p + q) n` (the degree proof `h` does not mention `p`, `q`) | row "de Rham cup order", present; it already lists `deRhamCup_mem_hodgeFiltration` as insensitive |
| Koszul sign `ε₂(p, q) = (−1)^p` of the tensor of complexes | `deRhamWedge` being a chain map, hence `deRhamWedgeFiltered` | only through the existence of `μ`; no sign appears in the theorem | rows "Tensor product of ℤ-indexed cochain complexes and its shifts", "Wedge on complexes", present |
| Hodge filtration as the image of the stupid truncation | every statement | yes: which classes count | row "Hodge filtration", present; status to update (change 6) |
| `F^p` through the rational bridge: `x ∈ F^p` iff `e x` factors through `(Q i_p)⟦n⟧'`, `e = deRhamShiftedHomEquiv X`, the same `e` that defines `deRhamCup` | (a) | the iff is exact; an automorphism of `e` that does not preserve the truncations would break it, and the proof excludes that through `hodgeFiltration_eq_range_rational` and `rationalHypercohomologyEquiv_map` | new row (change 6) |
| Vanishing ranges of `F^p`: `⊤` for `p ≤ 0`, `⊥` for `p > dim X` (upstream `Other`), `⊥` for `p > n` (new) | tests, the sharp ℙ² test | statements with `p + q ≤ 0` hold for the degenerate reason `F^{p+q} = ⊤`; the ℙ² test uses `F^3 = ⊥` | row "Rational-to-de Rham map and the range of F^p", to update (change 6) |
| `ι` normalization (no `(2πi)^p`) | (a_ℚ), (b) | no: membership | row present |

Attack item 3: no sign enters, none is forced, nothing evaluates to `−1`. Every identity in the proof is exact (`deRhamShiftedHomEquiv_deRhamCup`, `pairProductShQ_naturality`, `deRhamWedgeFiltered_comp_inclusion`, `fieldToDeRhamCohomology_cup`). The only non-trivial sign anywhere upstream of this rung is Mathlib's Koszul `(−1)^p` inside the chain-map property of `μ`.

No cited input with an outside convention. The one upstream lemma the sharper test uses (`hodgeFiltration_eq_bot_of_lt` in `Other`) is a lemma; its statement is checked by the build at every pin.

## 7. Equality first

(a), (a_ℚ) and (b) are closure statements. No identity is claimed here; the identities they rest on (`fieldToDeRhamCohomology_cup`, the unit and naturality laws) are checked exactly in earlier rungs. Equalities they serve: T1 of the Markman inventory (Weil classes are Hodge, then `W_K ⊆ algebraicCycleClassSpan` through `lefschetzOneOneEquality_holds`), which has no ledger rung yet, and the target equality `Hdg^p(X; ℚ) = algebraicCycleClassSpan X p` (rung `upstream-statement`), of which `planeOrigin_mem_hodgeClasses` gives the containment `[pt] ∈ Hdg^2(ℙ²)` in the known direction. An "equality form" `span (F^p ∪ F^q) = F^{p+q}` is false in general and is no target.

## 7b. Non-vacuity

| Statement | Smallest test | Exists? |
|---|---|---|
| (a), hypotheses with a nonzero product | `Tests.planeLines_deRhamCup_mem_hodgeFiltration` | yes, in the candidate |
| (a) is sharp in the index and uses both hypotheses; `F^2 H^2(ℙ²) ≠ ⊤` | `Tests.planeLine_not_mem_hodgeFiltration_two : ι [L₀] ∉ hodgeFiltration projectivePlane 2 2`, from `deRhamCup_mem_hodgeFiltration`, `AlgebraicGeometry.ComplexPoint.hodgeFiltration_eq_bot_of_lt`, `HodgeLadder.Tests.dim_projectiveSpace`, `mem_hodgeClasses_iff_mem_hodgeFiltration`, `cycleComponentSheafClass_mem_hodgeClasses_one`, `Tests.planeLines_deRhamCup_ne_zero`. It is false for the zero product's proof route: the contradiction needs the product nonzero | checked in scratch (RT6); add (change 2) |
| the conclusion's subgroup is proper in degree 4 | `Tests.plane_hodgeFiltration_three_four : F^3 H^4(ℙ²) = ⊥ ∧ F^2 H^4(ℙ²) ≠ ⊥` | checked in scratch (RT6); add (change 2) |
| (b) conclusion | `Tests.planeOrigin_mem_hodgeClasses` | yes, in the candidate |
| a nonzero product landing in a proper `F^{p+q}` | none on ℙ²: classically its proper pieces (`F^{≥2} H^2`, `F^{≥3} H^4`) are zero, so products landing there vanish. Needs `h^{p,0} ≠ 0`, for example an elliptic curve | no; known weakness, out of reach at the pin |
| `F^2 H^4(ℙ²) = ⊤` (the classical value) | from `ι [pt] ∈ F^2`, `deRhamRationalSpan` on ℙ² and `H^4(ℙ²; ℚ) ≅ ℚ` (`planeDegree_bijective`) | not attempted; optional, it would pin the value from the other side |

## 8. Pin drift

The worktree pin equals `main`'s (`lakefile.toml` rev `2ead713…`, `.lake/packages/HodgeConjecture` at `2ead7131…`). Nothing to diff. The branch must be rebased on `a568e7b` before the ledger edit (it touches the same files).

## Findings

1. **Faithful at full strength** (section 1). (a) is the literature's multiplicativity for every integer degree and index on every smooth integral X, against upstream's `hodgeFiltration`; (b) is the literature's ring statement against upstream's `hodgeClasses` and the checked `Cup.cup`. The theorems' types are the stated `Prop`s by name. The hypotheses are exactly those of upstream's definitions; the extra generality over projective X is true.

2. **The proof is honest and non-circular** (section 3, attack items 4 and 5). `mem_hodgeFiltration_iff_exists_shiftedHom` proves both directions from `hodgeFiltration_eq_range_rational` (rung `rational-de-rham-complex`, red team pass with changes, implemented; it pins `forgetRationalDeRhamIso` against upstream's truncation inclusion by `forget_rationalHodgeFilteredInclusion`) and `rationalHypercohomologyEquiv_map`. The bridge on the right of the iff is the same `deRhamShiftedHomEquiv` that defines `deRhamCup`, so no second identification enters. The main step is `pairProductShQ_naturality` with `m' = μ` of `deRhamCup` and the square `deRhamWedgeFiltered_comp_inclusion`.

3. **A sharper test exists and is cheap.** On ℙ², `ι [L₀] ∉ F^2 H^2_dR` and `F^3 H^4_dR = ⊥ ≠ F^2 H^4_dR`, each in under ten lines from the theorem, upstream's vanishing above the dimension, and the checked nonzero product. They show upstream's filtration is proper in positive degree on ℙ² (the statement-phase red team had this as out of reach), that the index `p + q` is sharp, and that both hypotheses carry content. The candidate's test only shows the hypotheses are met.

4. **Upstream already has the vanishing above the dimension.** `AlgebraicGeometry.ComplexPoint.hodgeFiltration_eq_bot_of_lt` in upstream's `Other`, in the closure already. Use it; do not add a local copy (decision 0011). The vanishing above the degree (`n < p`) is absent upstream and is a 9-line local lemma through Mathlib's t-structure; it settles the conventions row's "expected to vanish for p > n".

5. **Ledger: `cup-hodge-classes` is discharged.** Its declarations must become the two theorems (with the `Prop`s kept for the title): `check_axioms` on a `Prop` definition reports the axioms of the definition, which pass for any statement, so a `checked` entry naming only the `Prop`s would certify nothing.

6. **The cup front's list is complete.** Decision 0009's items 1 to 8 (`cup-pullback`, `sheaf-tensor-exact`, `supported-cup`, `cup-singular-comparison`, `local-class-product`, `cycle-class-multiplicative`, `cup-graded-commutative`, `cup-hodge-filtration`) are all `checked` after this PR, with `cup-positive-degree-test-p2` closing the vacuity gap that decision 0009 named. The win condition in `docs/strategy.md` ("a checked associative, unital, graded-commutative cup product, compatible with the cycle class map") holds with "compatible" read as decision 0010 fixes it: the transversal case with one integral component T, sign `+` (`cycleComponentSheafClass_cup_of_transversal_noReg`). Open items that stay open after closure, none of them on the front's list: `cup-positive-degree-test` (ℙ¹ × ℙ¹; its product identity `cycle-class-multiplicative-p1p1` is checked on `main`), and the T1 inputs `de-rham-cup-antisymm-h1`, `de-rham-cup-unique`. Non-transversal intersections lie outside the front's scope as decisions 0008 to 0010 define it.

7. **Docs drift.** `CupFiltration.lean`'s module docstring calls `cup-hodge-classes` stated and says the pin has no product on `H_dR`; the sketch's sub-rung table shows `de-rham-cup`, `de-rham-cup-test-p2`, `de-rham-scalar-sheaf`, `cup-hodge-filtration` as open and `cup-hodge-classes` as stated; the test module's docstring says the content is only that the hypotheses are met; `docs/strategy.md`, `docs/roadmap.md`, `docs/statement.md` and the `markman-statement` note call the front blocking.

8. **Placement.** `HodgeLadder/Hodge/CupHodgeFiltration.lean` sits beside `CupFiltration.lean` and `DeRhamCupBilinear.lean`; that is right. The default path `tools/next.py` prints (`HodgeLadder/Cup/Hodge/Filtration.lean`) comes from the null `module` field only. Layer 24 (`python3 tools/pinwalk.py --hubs`, 2026-11-27); the test module is layer 47.

## Required changes

1. **Ledger** (after rebasing on `main`). Replace the entries of `cup-hodge-filtration` and `cup-hodge-classes`, and add the test rung (open a gap issue for it, per the propagation map):

```json
{"id": "cup-hodge-filtration", "title": "The de Rham cup product respects the Hodge filtration: deRhamCup (F^p H_dR^a) (F^q H_dR^b) ⊆ F^{p+q} H_dR^{a+b}", "status": "checked", "kind": "foundation", "module": "HodgeLadder.Hodge.CupHodgeFiltration", "declarations": ["HodgeLadder.deRhamShiftedHomEquiv_filtered", "HodgeLadder.mem_hodgeFiltration_iff_exists_shiftedHom", "HodgeLadder.deRhamCup_mem_hodgeFiltration", "HodgeLadder.map₂_deRhamCupBilinear_le", "HodgeLadder.hodgeFiltration_eq_bot_of_degree_lt"], "depends_on": ["de-rham-cup", "wedge-sheaf-map", "rational-de-rham-complex", "pairing-product", "de-rham-cup-test-p2"], "contributors": ["claude-code"], "note": "Statement (a) of docs/sketches/cup-hodge-filtration.md, for complex classes, as needed by T1. Checked 2026-11-27: for all integer degrees a, b, n and indices p, q on every smooth integral X, deRhamCup x y n h ∈ hodgeFiltration X (p + q) n for x ∈ F^p, y ∈ F^q, with upstream's hodgeFiltration; the ℂ-submodule form map₂_deRhamCupBilinear_le. Proof: mem_hodgeFiltration_iff_exists_shiftedHom (x ∈ F^p iff deRhamShiftedHomEquiv X n x factors through (Q i_p)⟦n⟧', from hodgeFiltration_eq_range_rational and rationalHypercohomologyEquiv_map), then pairProductShQ_naturality along the truncation inclusions with the square deRhamWedgeFiltered_comp_inclusion X q p, and add_comm on the index. No sign, no scalar. F^p H^n = 0 for n < p (hodgeFiltration_eq_bot_of_degree_lt, Mathlib's t-structure); above the dimension upstream's Other has hodgeFiltration_eq_bot_of_lt. The zero product also satisfies (a); fieldToDeRhamCohomology_cup and the ℙ² tests (cup-hodge-filtration-test-p2: ι [L₀] ∉ F^2 H^2, F^3 H^4 = 0) tie it to the cup product and show the index p + q is sharp. Red team: docs/sketches/cup-hodge-filtration-checked.redteam.md."}
{"id": "cup-hodge-classes", "title": "Products of Hodge classes are Hodge classes: Hdg^p ∪ Hdg^q ⊆ Hdg^{p+q} for upstream's hodgeClasses and the checked cup", "status": "checked", "kind": "foundation", "module": "HodgeLadder.Hodge.CupHodgeFiltration", "declarations": ["HodgeLadder.cupPreservesHodgeClasses_holds", "HodgeLadder.cupRespectsHodgeFiltrationRational_holds", "HodgeLadder.CupPreservesHodgeClasses", "HodgeLadder.CupRespectsHodgeFiltrationRational"], "depends_on": ["cup-hodge-reduction", "cup-hodge-filtration", "de-rham-cup-exact"], "contributors": ["claude-code"], "note": "Statements (b) and (a_ℚ) of docs/sketches/cup-hodge-filtration.md, stated 2026-11-26 in HodgeLadder.Hodge.CupFiltration, checked 2026-11-27: cupRespectsHodgeFiltrationRational_holds X : CupRespectsHodgeFiltrationRational X from fieldToDeRhamCohomology_cup and deRhamCup_mem_hodgeFiltration; cupPreservesHodgeClasses_holds X : CupPreservesHodgeClasses X through cupPreservesHodgeClasses_of_rational (cup-hodge-reduction). Every smooth integral X, no projectivity, the same instance arguments as upstream's hodgeClasses. Membership statements: insensitive to the order of the factors and to nonzero scalars. Non-vacuity: cup-hodge-classes-test-p2 (Hodge line classes with nonzero product) and Tests.planeOrigin_mem_hodgeClasses ([pt] ∈ Hdg^2(ℙ²; ℚ), a codimension-two case of cycle-classes-are-hodge). Red team: docs/sketches/cup-hodge-filtration-checked.redteam.md."}
{"id": "cup-hodge-filtration-test-p2", "title": "Non-vacuity of cup-hodge-filtration and cup-hodge-classes on ℙ²: Hodge line classes with nonzero product in F^2 H_dR^4, ι [L₀] ∉ F^2 H_dR^2, F^3 H_dR^4 = 0 ≠ F^2 H_dR^4, [pt] ∈ Hdg^2", "status": "checked", "kind": "test", "module": "HodgeLadder.Tests.CupHodgeFiltrationP2", "declarations": ["HodgeLadder.Tests.planeLines_deRhamCup_mem_hodgeFiltration", "HodgeLadder.Tests.planeLine_not_mem_hodgeFiltration_two", "HodgeLadder.Tests.plane_hodgeFiltration_three_four", "HodgeLadder.Tests.planeOrigin_mem_hodgeClasses"], "depends_on": ["cup-hodge-filtration", "cup-hodge-classes", "de-rham-cup-test-p2", "cycle-class-multiplicative-p2", "cup-hodge-classes-test-p2"], "contributors": ["claude-code"], "note": "Checked 2026-11-27. The hypotheses of (a) hold with a nonzero product (ι [L₀], ι [L₁] ∈ F^1 H^2, product ≠ 0 in F^2 H^4). Sharp test: if ι [L₀] were in F^2 H^2, its product with ι [L₁] would lie in F^3 H^4 = 0 (upstream's hodgeFiltration_eq_bot_of_lt, dim ℙ² = 2), against planeLines_deRhamCup_ne_zero; so F^2 H^2(ℙ²) ≠ ⊤, the index p + q is sharp, and both hypotheses carry content. F^2 H^4(ℙ²) = ⊤ classically (unverified at the pin). (b) gives [pt] ∈ Hdg^2(ℙ²; ℚ) through planeLines_cup_eq_planeOrigin. Red team: docs/sketches/cup-hodge-filtration-checked.redteam.md."}
```

2. **Test module.** Append to `HodgeLadder/Tests/CupHodgeFiltrationP2.lean`, inside `namespace HodgeLadder.Tests` (checked in scratch as RT6, standard axioms, 10 s with the module's imports; no new import):

```lean
/-- **The filtration law is sharp on ℙ².** `ι [L₀] ∉ F^2 H_dR^2(ℙ²)`: otherwise
`deRhamCup (ι [L₀]) (ι [L₁])` would lie in `F^{2+1} H_dR^4(ℙ²)`, which is zero since
`dim ℙ² = 2` (upstream's `hodgeFiltration_eq_bot_of_lt`), against
`planeLines_deRhamCup_ne_zero`. -/
theorem planeLine_not_mem_hodgeFiltration_two :
    fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)) ∉
      hodgeFiltration projectivePlane 2 ((2 * 1 : ℕ) : ℤ) := by
  intro h
  have h1 := (mem_hodgeClasses_iff_mem_hodgeFiltration projectivePlane 1 _).mp
    (cycleComponentSheafClass_mem_hodgeClasses_one projectivePlane _ (coheight_planeLine 1))
  have hm := deRhamCup_mem_hodgeFiltration (n := 4) (by norm_num) h h1
  have hd : TopologicalSpace.dim projectivePlane.left = 2 := dim_projectiveSpace 2
  rw [AlgebraicGeometry.ComplexPoint.hodgeFiltration_eq_bot_of_lt projectivePlane
    (p := 2 + ((1 : ℕ) : ℤ)) (by rw [hd]; norm_num) 4] at hm
  exact planeLines_deRhamCup_ne_zero ((AddSubgroup.mem_bot).mp hm)

/-- On ℙ², `F^3 H_dR^4 = 0` while `F^2 H_dR^4` contains the nonzero class
`deRhamCup (ι [L₀]) (ι [L₁])`. -/
theorem plane_hodgeFiltration_three_four :
    hodgeFiltration projectivePlane 3 4 = ⊥ ∧ hodgeFiltration projectivePlane 2 4 ≠ ⊥ := by
  have hd : TopologicalSpace.dim projectivePlane.left = 2 := dim_projectiveSpace 2
  refine ⟨AlgebraicGeometry.ComplexPoint.hodgeFiltration_eq_bot_of_lt projectivePlane
    (p := 3) (by rw [hd]; norm_num) 4, ?_⟩
  intro hb
  have h := (planeLines_deRhamCup_mem_hodgeFiltration).2.2.1
  rw [show (1 + 1 : ℤ) = 2 from rfl, hb] at h
  exact (planeLines_deRhamCup_mem_hodgeFiltration).2.2.2 ((AddSubgroup.mem_bot).mp h)
```

   In the module docstring replace the paragraph "The conclusion `F^2 H_dR^4(ℙ²)` is the whole group in classical Hodge theory (unverified at the pin); the content of the test is that the hypotheses are met by classes with a nonzero product." by: "The conclusion `F^2 H_dR^4(ℙ²)` is the whole group in classical Hodge theory (unverified at the pin). The sharp test is `planeLine_not_mem_hodgeFiltration_two`: with `F^3 H_dR^4(ℙ²) = 0` (upstream's `hodgeFiltration_eq_bot_of_lt`), statement (a) and the nonzero product force `ι [L₀] ∉ F^2 H_dR^2`, so the index `p + q` is sharp, both hypotheses carry content, and upstream's filtration on ℙ² is proper in degrees 2 and 4 (`plane_hodgeFiltration_three_four`)." and add the two names to "Main results".

3. **Main module.** Add to `HodgeLadder/Hodge/CupHodgeFiltration.lean`, after `mem_hodgeFiltration_iff_exists_shiftedHom` (checked in scratch as RT7 with the module's opens and local instances, standard axioms):

```lean
/-- **The Hodge filtration vanishes above the degree.** For `n < p`, `hodgeFiltration X p n = ⊥`:
`ℚ_X[0]` is `≤ 0` and `(F^p Ω•_ℚ)[n]` is `≥ p − n ≥ 1` for Mathlib's t-structure on the derived
category, so every `x'` of `mem_hodgeFiltration_iff_exists_shiftedHom` is zero. Above the
dimension, upstream's `AlgebraicGeometry.ComplexPoint.hodgeFiltration_eq_bot_of_lt` applies. -/
theorem hodgeFiltration_eq_bot_of_degree_lt (p n : ℤ) (hn : n < p) :
    hodgeFiltration X p n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨x', hx'⟩ := (mem_hodgeFiltration_iff_exists_shiftedHom X p n x).mp hx
  have h1 : (Q.obj (unitComplex (TopCat.of (ComplexPoint X)))).IsLE 0 := inferInstance
  have h3 : ((Q.obj (rationalHodgeFilteredComplex X p))⟦n⟧).IsGE (p - n) :=
    TStructure.t.isGE_shift _ p n (p - n) (by lia)
  rw [TStructure.t.zero_of_isLE_of_isGE x' 0 (p - n) (by lia) h1 h3, Limits.zero_comp] at hx'
  exact (AddSubgroup.mem_bot).mpr ((deRhamShiftedHomEquiv X n).map_eq_zero_iff.mp hx')
```

   Add it to "Main results", and in "Non-vacuity" add: "`Tests.planeLine_not_mem_hodgeFiltration_two` shows the index `p + q` is sharp and both hypotheses carry content."

4. **Root.** Append to `HodgeLadder.lean`:

```lean
public import HodgeLadder.Hodge.CupHodgeFiltration
public import HodgeLadder.Tests.CupHodgeFiltrationP2
```

   then `python3 tools/check.py` (full).

5. **`docs/gaps.md`**, section "De Rham complex and holomorphic forms", after the `deRhamCupBilinear` row:

```
| `HodgeLadder.deRhamShiftedHomEquiv_filtered`, `mem_hodgeFiltration_iff_exists_shiftedHom` (upstream's `F^p H_dR^n(X)` as the classes whose image under `deRhamShiftedHomEquiv` factors through `(F^p Ω•_ℚ)[n]`), `hodgeFiltration_eq_bot_of_degree_lt` (`F^p H_dR^n = 0` for `n < p`), `deRhamCup_mem_hodgeFiltration`, `map₂_deRhamCupBilinear_le` (multiplicativity of the Hodge filtration for `deRhamCup`) | `HodgeLadder.Hodge.CupHodgeFiltration` | 24 | upstream has no product on `H_dR` and no vanishing of `hodgeFiltration` below the filtration index (its `Other` has the vanishing above the dimension, `hodgeFiltration_eq_bot_of_lt`, used here as is); a pin bump that adds either, or a `t`-structure lemma for `hypercohomology`, must be compared with this row; rungs `cup-hodge-filtration`, `cup-hodge-classes` | 2026-11-27 |
```

6. **`docs/conventions.md`.**
   - Row "Hodge filtration": status `recorded` becomes `recorded; multiplicative for deRhamCup (rung cup-hodge-filtration, checked 2026-11-27); proper on ℙ² in degrees 2 and 4 (Tests.planeLine_not_mem_hodgeFiltration_two, Tests.plane_hodgeFiltration_three_four)`.
   - Row "Rational-to-de Rham map and the range of F^p", choice column: replace "F^p H^n is expected to vanish for p > n" by "F^p H^n = 0 for p > n (`HodgeLadder.hodgeFiltration_eq_bot_of_degree_lt`, Mathlib's t-structure) and for p > dim X (upstream `Other`, `hodgeFiltration_eq_bot_of_lt`)".
   - New row after "de Rham cup order":

```
| Hodge filtration through the rational bridge | this repository, `HodgeLadder.mem_hodgeFiltration_iff_exists_shiftedHom`, `deRhamShiftedHomEquiv_filtered` (`HodgeLadder/Hodge/CupHodgeFiltration.lean`, rung `cup-hodge-filtration`); `hodgeFiltration_eq_range_rational`, `rationalHypercohomologyEquiv_map` | `x ∈ hodgeFiltration X p n` iff `deRhamShiftedHomEquiv X n x = x' ≫ (Q.map (rationalHodgeFilteredInclusion X p))⟦n⟧'` for some `x'`; the bridge is the one that defines `deRhamCup`; the filtered wedge is `deRhamWedgeFiltered X q p` (index of `y`, the left tensor factor, first), landing in `F^{q+p}`, rewritten to `F^{p+q}` by `add_comm` | the iff is exact; `deRhamCup_mem_hodgeFiltration`, `CupRespectsHodgeFiltrationRational`, `CupPreservesHodgeClasses` are membership statements, insensitive to sign, scalar and factor order | checked 2026-11-27; red team `docs/sketches/cup-hodge-filtration-checked.redteam.md`; no sign |
```

7. **`docs/roadmap.md`.** Replace rows 142 and 143 and add the test row:

```
| `cup-hodge-filtration` | foundation | checked | `de-rham-cup`, `wedge-sheaf-map`, `rational-de-rham-complex`, `pairing-product`, `de-rham-cup-test-p2` | deRhamCup (F^p) (F^q) ⊆ F^{p+q} for complex classes, statement (a), every smooth integral X; F^p H^n = 0 for n < p; `HodgeLadder.Hodge.CupHodgeFiltration` |
| `cup-hodge-classes` | foundation | checked | `cup-hodge-reduction`, `cup-hodge-filtration`, `de-rham-cup-exact` | Hdg^p ∪ Hdg^q ⊆ Hdg^{p+q} and its rational filtration form (`HodgeLadder.cupPreservesHodgeClasses_holds`, `HodgeLadder.cupRespectsHodgeFiltrationRational_holds`) |
| `cup-hodge-filtration-test-p2` | test | checked | `cup-hodge-filtration`, `cup-hodge-classes`, `de-rham-cup-test-p2`, `cycle-class-multiplicative-p2`, `cup-hodge-classes-test-p2` | on ℙ²: nonzero product in F^2 H^4, ι [L₀] ∉ F^2 H^2, F^3 H^4 = 0, [pt] ∈ Hdg^2; `HodgeLadder.Tests.CupHodgeFiltrationP2` |
```

   Row 39 becomes `| `cup-front` | front | checked | `upstream-statement` | ring structure on H^*(X; ℚ), decision 0008; won, decision 0012 |`. In "Order of attack", item 1, append: "`cup-hodge-filtration` and `cup-hodge-classes` are checked: the de Rham cup product respects the Hodge filtration, and products of Hodge classes are Hodge classes, on every smooth integral X. The front is closed as won (decision 0012)."

8. **`docs/sketches/cup-hodge-filtration.md`**, sub-rung table: set the status of `de-rham-scalar-sheaf`, `de-rham-cup`, `de-rham-cup-test-p2`, `cup-hodge-filtration` and `cup-hodge-classes` to `checked`, and add a row `| `cup-hodge-filtration-test-p2` | ι [L₀] ∉ F^2 H^2, F^3 H^4 = 0, [pt] ∈ Hdg^2 on ℙ² | checked |`.

9. **Close the front.** New file `docs/decisions/0012-close-cup-front.md`:

```markdown
# 0012. Close the cup-product front: won

Date: 2026-11-27. Status: accepted. Closes the front opened by decision 0008, as amended by decisions 0009 and 0010.

## Context

Decision 0009 ordered the front in eight rungs. With `cup-hodge-filtration` and `cup-hodge-classes` checked (red team `docs/sketches/cup-hodge-filtration-checked.redteam.md`), all eight are checked:

| Item | Rung | Checked result |
|---|---|---|
| 1 | `cup-pullback` | pullback along a morphism is multiplicative |
| 2 | `sheaf-tensor-exact` | the tensor of sheaves of ℚ-vector spaces is exact |
| 3 | `supported-cup` | supported times absolute, compatible with forgetting the support |
| 4 | `cup-singular-comparison` | the Yoneda cup goes to the singular cup, sign fixed exactly |
| 5 | `local-class-product` | product of normalized local classes of transversal components |
| 6 | `cycle-class-multiplicative` (with `cycle-class-multiplicative-no-reg`) | [Z] ∪ [W] = [T] for a transversal intersection with one integral component, sign + |
| 7 | `cup-graded-commutative` | α ∪ β = (−1)^{pq} β ∪ α |
| 8 | `cup-hodge-filtration`, `cup-hodge-classes` | F^p ∪ F^q ⊆ F^{p+q} for the de Rham cup; Hdg^p ∪ Hdg^q ⊆ Hdg^{p+q} |

The product itself (`cup-product`: associative, unital, biadditive) and the vacuity test of decision 0009 (`cup-positive-degree-test-p2`: [L₀] ∪ [L₁] = [pt] ≠ 0 on ℙ²) are checked. The win condition of `docs/strategy.md` asks for a checked associative, unital, graded-commutative cup product compatible with the cycle class map; compatibility is read as decision 0010 fixes it, the transversal case with one integral component.

## Decision

Close front `cup` as won. Its ledger rung `cup-front` becomes `checked`, with module `HodgeLadder` and the headline declarations `HodgeLadder.Cup.cup_assoc`, `HodgeLadder.Cup.one_cup`, `HodgeLadder.Cup.cup_one`, `HodgeLadder.Cup.cup_gradedComm`, `HodgeLadder.Cup.cup_singular_comparison'`, `HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal_noReg`, `HodgeLadder.Tests.planeLines_cup_eq_planeOrigin`, `HodgeLadder.cupPreservesHodgeClasses_holds`. The kill criteria of decisions 0009 and 0010 lapse.

## Consequences

- M2 and M3 are no longer blocked by the front. The next M2 rung is T1 of the Markman inventory (`docs/notes/2026-11-25-markman-inventory.md` §6); its open inputs `de-rham-cup-antisymm-h1` and `de-rham-cup-unique` are T1 prerequisites, outside the closed front.
- `cup-positive-degree-test` (ℙ¹ × ℙ¹) stays open as a test; its product identity `cycle-class-multiplicative-p1p1` is checked.
- Non-transversal products of cycle classes (excess intersection, multiplicities) were outside the front's scope and have no rung; a rung for them opens a new front or joins an existing one by its own decision.
- The rungs that depend on `cup-front` keep that dependency; the front rung keeps `depends_on: ["upstream-statement"]`, so the ledger has no cycle.
```

   Ledger entry for the front:

```json
{"id": "cup-front", "title": "Front cup: a ring structure on upstream's rational cohomology", "status": "checked", "kind": "front", "module": "HodgeLadder", "declarations": ["HodgeLadder.Cup.cup_assoc", "HodgeLadder.Cup.one_cup", "HodgeLadder.Cup.cup_one", "HodgeLadder.Cup.cup_gradedComm", "HodgeLadder.Cup.cup_singular_comparison'", "HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal_noReg", "HodgeLadder.Tests.planeLines_cup_eq_planeOrigin", "HodgeLadder.cupPreservesHodgeClasses_holds"], "depends_on": ["upstream-statement"], "contributors": ["claude-code"], "note": "Decision 0008. Yoneda route: H^n(X; ℚ) ≅ Ext^n(ℚ_X, ℚ_X) in sheaves of ℚ-vector spaces, product = Ext.comp. Amended by decision 0009 (comparison with the singular cup product, sign fixed exactly; rungs 1 to 8) and decision 0010 (two-support product on the singular side, ℙ² first). Closed as won 2026-11-27 (decision 0012): associative, unital, graded-commutative, compared with the singular cup, multiplicative on cycle classes for transversal intersections with one integral component (sign +), and products of Hodge classes are Hodge classes. Open after closure: cup-positive-degree-test (ℙ¹ × ℙ¹), and the T1 inputs de-rham-cup-antisymm-h1, de-rham-cup-unique."}
```

   `RT5` resolved all eight names with `import HodgeLadder` plus the new module; after change 4 the root alone suffices. In `docs/decisions/README.md` add `| 0012 | Close the cup-product front: won | 2026-11-27 |`. Status lines: 0008 "Status: accepted; amended by decision 0009; closed by decision 0012."; 0009 "Status: accepted; amended by decision 0010; closed by decision 0012. Amends decision 0008."; 0010 "Status: accepted; closed by decision 0012. Amends decision 0009 (rungs 5 and 6, the test rung, the kill criterion)."

10. **`docs/strategy.md`.**
    - Fronts table, row `cup`, last column becomes: "Won (decision 0012): `cup-product`, `cup-graded-commutative`, `cup-singular-comparison`, `cycle-class-multiplicative` and `cup-hodge-classes` checked, with the ℙ² tests; `cup-positive-degree-test` (ℙ¹ × ℙ¹) open as a test".
    - Row `abelian`, last column: replace "after front `cup`" by "front `cup` is closed (decision 0012)".
    - Milestone status, M2: replace "The blocking foundation is front `cup` (decision 0008): no ring structure exists on upstream's H^*(X; ℚ) at the pin. After it, the inventory's target sequence T1 to T5 (§6) starts with T1, Weil classes on abelian surfaces of Weil type" by "Front `cup` is closed as won (decision 0012): the cup product on upstream's H^*(X; ℚ) is checked, with graded commutativity, multiplicativity on transversal cycle classes and closure of Hodge classes. Next is the inventory's target sequence T1 to T5 (§6), starting with T1, Weil classes on abelian surfaces of Weil type".
    - M3: "open; front `cup` is closed (decision 0012); `hard-lefschetz` is the long pole (inventory §5)".

11. **Other notes.** `docs/statement.md` line 44: replace "with front `cup` as its blocking foundation" by "with front `cup` closed (decision 0012) and T1 of the Markman inventory next". Ledger `markman-statement`, note: replace "blocked on front cup (decision 0008)" by "front cup closed (decision 0012)". `HodgeLadder/Hodge/CupFiltration.lean` module docstring: "`cup-hodge-classes` (stated)" becomes "`cup-hodge-classes` (checked in `HodgeLadder.Hodge.CupHodgeFiltration`)", and the sentence "The complex form `F^p ∪ F^q ⊆ F^{p+q}` on `H_dR^*(X)` (rung `cup-hodge-filtration`) needs a product on de Rham hypercohomology, which neither upstream nor Mathlib has at the pin; its construction and the sub-rungs are in `docs/sketches/cup-hodge-filtration.md`." becomes "The complex form `F^p ∪ F^q ⊆ F^{p+q}` on `H_dR^*(X)` (rung `cup-hodge-filtration`) is checked in `HodgeLadder.Hodge.CupHodgeFiltration` for the local product `deRhamCup`; its construction and the sub-rungs are in `docs/sketches/cup-hodge-filtration.md`." The docstrings of the two target `Prop`s keep their text. A handoff under `docs/handoffs/`.

## Recommended, not required

- `F^2 H^4_dR(ℙ²) = ⊤` from `ι [pt] ∈ F^2`, `deRhamRationalSpan` and `planeDegree_bijective`: it would fix the classical value of the conclusion on ℙ² from the other side. Not attempted.
- A known-weakness row in `docs/gaps.md`: "No test exhibits a nonzero product landing in a proper `F^{p+q}`; on ℙ² every proper piece is zero. Needs a variety with `h^{p,0} ≠ 0`, for example an elliptic curve or an abelian surface, and a nonzero holomorphic form at the pin."
