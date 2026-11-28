# Red team: `de-rham-pullback`

Verdict: **pass with changes**

Candidate: commit `dde9f44` on `track/de-rham-pullback` (issue #257, plan node A5 of `docs/notes/2026-11-27-t1-plan.md`), `HodgeLadder/Hodge/DeRhamPullback.lean` (module `HodgeLadder.Hodge.DeRhamPullback`, namespace `HodgeLadder`) and `HodgeLadder/Tests/DeRhamPullbackP1p1.lean`, built against upstream `2ead713`, Lean `v4.35.0-rc4`, the pin on `main` at `19a4bda`. Red team 2026-11-28.

Read: the ledger entries `de-rham-pullback`, `pullback-functorial`, `weil-eigen-algebra`, `weil-surface-reduction`, `de-rham-hypercohomology-pullback`, `hodge-filtration-pullback`; `python3 tools/next.py` for the first three; plan nodes A5, B, D3; decision 0013; `HodgeLadder/Hodge/{DeRhamRationalBaseChange,DeRhamCupBilinear,Conjugation}.lean`, `HodgeLadder/Pullback/Functorial.lean`, `HodgeLadder/Cup/PullbackVariety.lean`, `HodgeLadder/General/EigenProducts.lean`; upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (`fieldToDeRhamCohomology`, `deRhamConj`, `deRhamConjSemilinear`) and `Lemmas/AlgebraicGeometry/Hodge/Filtration.lean` (`deRhamConjSemilinear_apply`); `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`. No thinker sketch exists for this rung.

Scratch: `rt-scratch-drp/` in the worktree, plain `lake env lean` runs against the built `.olean` files, deleted after the pass. Every Lean claim marked "scratch" below elaborated there.

## Findings

1. **Signs.** None found, none introduced. The ι law reads `1 ⊗ α ↦ 1 • ι α` through `deRhamBaseChangeEquiv_tmul` and closes by `one_smul`; the cup law is `Cup.pullbackCoh_cup` (no sign) read through `fieldToDeRhamCohomology_cup` (no sign, row "de Rham cup order"); the conjugation law reads `deRhamConj_fieldToDeRhamCohomology` twice. No scalar appears anywhere.

2. **Is this the literature's map (item 1).** The literature's pullback on de Rham cohomology of a holomorphic map f : X → Y is the map on ℍ^n(Ω•) induced by f⁻¹Ω•_Y → Ω•_X, and under the holomorphic Poincaré lemma it is the topological pullback on H^n(−; ℂ), which is ℂ ⊗ the pullback on H^n(−; ℚ) [Voisin2002] (locator unverified). Field by field against the Lean:

   | Field | Lean | Literature | Match |
   |---|---|---|---|
   | Spaces | upstream `H_dR^n(X)`, the hypercohomology of the holomorphic de Rham complex on X(ℂ) with the analytic topology | ℍ^n(X^an, Ω•) | yes |
   | Direction | `g : X ⟶ Y` gives `H_dR^n(Y) →ₗ[ℂ] H_dR^n(X)`; `(g ≫ h)^* = g^* ∘ₗ h^*` with Mathlib's diagrammatic `≫` | contravariant, (h ∘ g)^* = g^* ∘ h^* | yes |
   | Rational input | `Pullback.pullbackCohLinear g n`, the sheaf pullback along `pointMap g` (Mathlib `TopCat.Sheaf.pullback`, f⁻¹ℚ ≅ ℚ by `leftAdjointUniq`, `Ext.mapExactFunctor`) | f^* on H^n(X(ℂ); ℚ) as sheaf cohomology | yes, row "Pullback of cohomology and of cohomology with supports" |
   | Comparison | `deRhamBaseChangeEquiv X n`, `c ⊗ m ↦ c • ι m` with upstream's `ι = fieldToDeRhamCohomology ℚ`, "induced by including locally constant K-valued functions as holomorphic zero-forms" (upstream docstring) | ℂ ⊗_ℚ H^n(X; ℚ) ≅ H^n(X; ℂ) ≅ ℍ^n(Ω•) | yes, up to the swap of tensor factors (row "Base change ℂ ⊗_ℚ M"), no sign |
   | Morphisms | morphisms in `Over (Spec ↧ℂ)`, so ℂ-morphisms | holomorphic maps of the analytifications | yes for algebraic maps; a non-ℂ-linear scheme map is excluded by the type |

   The definition is canonical: a ℂ-linear map H_dR^n(Y) → H_dR^n(X) is determined by its values on `ι`-images (`span_range_fieldToDeRhamCohomology_rat`). Scratch: the uniqueness lemma of required change 1 compiles in three tactic lines (14 s of kernel time). So the rung provides exactly this: the unique ℂ-linear map with `g^* (ι α) = ι (pullbackCoh g n α)`, and its formal laws. It provides nothing about forms: no statement on `F^p`, no map of complexes, no comparison with `hypercohomologyMap`.

3. **Later agreement with the pullback of forms is provable and non-circular.** `de-rham-hypercohomology-pullback` (D3) must build φ from the filtered map g⁻¹Ω•_Y → Ω•_X, show φ is ℂ-linear for upstream's `deRhamHypercohomologyComplexModule`, and show φ (ι α) = ι (pullbackCoh g n α). The last step is naturality of ℚ_X → Ω•_X under g⁻¹ together with the agreement of the hypercohomology pullback with `conjExt`/`mapExactFunctor` (the route `cup-pullback` uses); nothing in it mentions `deRhamPullback`. Uniqueness (required change 1) then gives φ = `deRhamPullback g n`, and `hodge-filtration-pullback` follows from φ being filtered. The definition through rational classes presupposes nothing about forms, so the chain has no cycle. One caution for D3: its statement must name upstream's ℂ-action on both sides; with a conjugated action the ℂ-linear extension would be the same additive map (it sends c̄ • ι α to c̄ • ι (g^* α) in both readings), so the agreement is insensitive to that choice, while D3's ℂ-linearity proof is not.

4. **Hypotheses satisfiable (item 2).** Every hypothesis is a typeclass on X, Y: integral, smooth, projective over `Spec ℂ`. The test instantiates them at ℙ¹ and ℙ¹ × ℙ¹ with `prod.fst`. `IsProjective` is used (through `deRhamBaseChangeEquiv` and the span); `IsIntegral` and `Smooth` are required by upstream's `H_dR`. No hypothesis is idle.

5. **Trivial truth (item 3).** Tried and failed.
   - The laws other than the ι law are formal consequences of the ι law, the rational laws and the span; that is the design of a foundation rung. The mathematical content sits in the inputs (`Cup.pullbackCoh_cup`, `pullbackCoh_comp`, `span_range_fieldToDeRhamCohomology_rat`, `deRhamConj_fieldToDeRhamCohomology`), each checked and red-teamed in its own rung.
   - `deRhamPullback g n = 0`: refuted by `p1p1_deRhamPullback_fst_class_ne_zero`.
   - `Subsingleton H_dR^n(X)`: refuted by the same test (a nonzero element of H²_dR(ℙ¹ × ℙ¹)).
   - No `True`-valued definition, no `ℕ∞`, no empty index type. Degrees are `ℕ` cast to `ℤ`, as for `deRhamBaseChangeEquiv`; negative degrees are outside the statement, and H_dR vanishes there anyway.
   - The conjugation law would also hold for a family of conjugations differing by a uniform sign; it would fail for a conjugation that does not fix `ι`-images. It does not unfold to an identity: upstream's `deRhamConj` is `starRingEnd ℂ`-semilinear, so it differs from the identity on any nonzero `c • ι α` with c ∉ ℝ.

6. **Interface axioms (item 4).** Not an interface rung; no structure, no axiom.

7. **Checker (item 5).** `python3 tools/check.py --no-build` in the worktree: `ACCEPTED: all checks passed`; no sorry; ledger well formed; each of the eight named declarations reports `[Classical.choice, Quot.sound, propext]`. The names are the ones the ledger means: the seven in `HodgeLadder.Hodge.DeRhamPullback` and `HodgeLadder.Tests.p1p1_deRhamPullback_fst_class_ne_zero` in `HodgeLadder.Tests.DeRhamPullbackP1p1`. The module adds no instance, attribute or notation (grep). Scratch: `(inferInstance : Module ℂ H_dR^n(X)) = deRhamHypercohomologyComplexModule X n` closes by `with_reducible rfl` with this module imported, so the ℂ-structure in every statement is upstream's.

8. **Cup law against the reduction (attack 2).** The bundled form fits `weil-eigen-algebra` directly. Scratch, for `A` smooth projective integral and `f : A ⟶ A`:

   ```lean
   have hS : ∀ x y, deRhamPullback f 2 (deRhamCupBilinear A 1 1 2 (by norm_num) x y) =
       deRhamCupBilinear A 1 1 2 (by norm_num) (deRhamPullback f 1 x) (deRhamPullback f 1 y) :=
     fun x y => LinearMap.congr_fun₂ (deRhamPullback_cupBilinear f (a := 1) (b := 1) (n := 2) rfl) x y
   ```

   (3.3 s elaboration, 4.1 s kernel), and then

   ```lean
   ker_sub_smul_le_span_of_eigen (deRhamCupBilinear A 1 1 2 (by norm_num)) (deRhamPullback f 1)
     (deRhamPullback f 2) hS e μ he hspan c
   ```

   elaborates with `e : ι → H_dR^(1 : ℕ)(A)`, `he : ∀ i, deRhamPullback f 1 (e i) = μ i • e i` and the `hspan` of A2 (0.6 s elaboration, 0.4 s kernel). The type `H_dR^↑1(A)` of `deRhamPullback f 1` and the `H_dR^1(A)` of `deRhamCupBilinear A 1 1 2` unify by defeq.
   - Failed attempt, recorded for the consumer: the pointwise law through `simpa only [deRhamCupBilinear_apply] using deRhamPullback_cup f (n := 2) rfl x y` fails with a type mismatch between `deRhamCup x y ↑2 _` and `deRhamCup x y 2 _`. The degree sits in a dependent position (the type `H_dR^↑2(A)` and the proof argument), so `simp` cannot rewrite `↑2` to `2`. `rw [deRhamCupBilinear_apply, deRhamCupBilinear_apply]; exact deRhamPullback_cup f (a := 1) (b := 1) (n := 2) rfl x y` works (defeq). Consumers with literal ℤ degrees should use the bundled law or `exact`; required change 2 puts this in the docstring.

9. **Conjugation (attack 3).** Handled correctly. `key` is an equation of `starRingEnd ℂ`-semilinear maps `H_dR^n(Y) →ₛₗ[starRingEnd ℂ] H_dR^n(X)`: `deRhamConjSemilinear X n` after the ℂ-linear `deRhamPullback g n`, and `deRhamPullback g n` after `deRhamConjSemilinear Y n` (both compositions typecheck through `RingHomCompTriple` with the identity). `LinearMap.ext_on` needs agreement on a set whose span over the domain's scalars ℂ is ⊤, which `span_range_fieldToDeRhamCohomology_rat Y n` supplies. On `ι α` both sides reduce to `ι (pullbackCoh g n α)`. The step from `deRhamConjSemilinear` to `deRhamConj` is upstream's `deRhamConjSemilinear_apply`, `rfl`.

10. **Non-vacuity strength (item 7b, attack 4).** The smallest test that would fail if the statement were trivially true is `HodgeLadder.Tests.p1p1_deRhamPullback_fst_class_ne_zero`; it exists and is checked. It is honest (through `fieldToDeRhamCohomology_rat_injective` and `p1p1_pullbackCoh_fst_class_ne_zero`) and narrow: one class, one degree. A strictly stronger test costs nothing. Scratch:

    ```lean
    theorem deRhamPullback_injective_of_section (p : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
        (n : ℕ) : Function.Injective (deRhamPullback p n) := by
      have key : ∀ x, deRhamPullback s n (deRhamPullback p n x) = x := fun x => by
        rw [← LinearMap.comp_apply, ← deRhamPullback_comp, hs, deRhamPullback_id,
          LinearMap.id_apply]
      exact Function.LeftInverse.injective key
    theorem p1p1_deRhamPullback_fst_injective (n : ℕ) :
        Function.Injective (deRhamPullback (prod.fst : p1p1 ⟶ projectiveLine) n) :=
      deRhamPullback_injective_of_section _ fibreSectionSnd (prod.lift_fst _ _) n
    ```

    Both together take under 0.01 s of kernel time. They exercise `_comp` and `_id` on a non-identity morphism in every degree, which the current test does not. Optional change 1.

11. **Kernel cost (attack 5).** Serial, a scratch copy of the module under a fresh namespace, `set_option profiler true`: the definition 27.1 s, the ι law 36.6 s, `_comp` 10.4 s, `_id` 2.9 s, `_cupBilinear` 6.4 s, one of `_cup` and `_conj` 7.9 s and the other under 0.5 s; 92.4 s of type checking in total, 1 min 44 s wall. The ledger's figures (28 s, 31 s, 2 to 9 s) agree; the handoff's 2 min 40 s includes the test module and a parallel build. The shortcut `noncomputable instance (priority := high) shortQ (X : Over (Spec ↧ℂ)) (n : ℕ) : Module ℚ (H^n(X; ℚ)) := fieldCohomologyModule ℚ X n`, added at the top of the same copy: 99 s of type checking, 1 min 50 s wall, so no gain. The instance terms that the kernel compares sit inside the imported types of `deRhamBaseChangeEquiv` and `pullbackCohLinear`, elaborated before the shortcut exists; the shortcut could only help if it were declared before those modules. This is a new data point for the decision the `docs/gaps.md` Known-weaknesses row asks for: a local shortcut in a consumer does not help; it would have to live at the bottom of the import graph.

12. **Placement and layout (item 6).** `HodgeLadder/Hodge/` next to the other `DeRham*` modules, namespace `HodgeLadder` as `deRhamCup` and `deRhamBaseChangeEquiv`. `python3 tools/pinwalk.py --hubs`: `HodgeLadder.Hodge.DeRhamPullback` layer 25, `HodgeLadder.Tests.DeRhamPullbackP1p1` layer 49. Upstream at the pin has no pullback on `H_dR` (grep of every upstream file mentioning `DeRhamHypercohomology` for `pullback`, `comap`, `inverseImage`: only `comap` along `deRhamConjSemilinear` and along the coefficient maps into `H_dR` in `hodgeClasses_eq_comap_hodgeFiltrationComplexSubmodule`), so `deRhamPullback` is a local definition a pin bump must compare against; it needs a row in `docs/gaps.md` "De Rham complex and holomorphic forms" after the two layer-24 rows (required change 4). The ledger lists a `Tests` declaration under the module `HodgeLadder.Hodge.DeRhamPullback`; the only other rung that does so is the front `cup-front`. The checker accepts it and the note names the test module; a separate test rung (as `pullback-functorial-test`) is the usual layout. Optional change 2.

13. **Conventions (item 6).** Conventions the statement and proof use, against `docs/conventions.md`:

    | Convention | Row | Truth depends on it |
    |---|---|---|
    | Direction and composition order of pullback | "Pullback of cohomology and of cohomology with supports" | `_comp` as stated (diagrammatic `≫`) |
    | ℂ ⊗_ℚ M with ℂ on the left, `c ⊗ m ↦ c • ι m` | "Base change ℂ ⊗_ℚ M" | the definition as an additive map: no (determined by ι ∘ g^* and the span) |
    | upstream's ℂ-action on `H_dR` | "Complex structure on H_dR" | ℂ-linearity and the eigenvalue use downstream: yes; the additive map: no |
    | factor order of `deRhamCup` | "de Rham cup order" | no: a uniform sign or a reversed order on both X and Y leaves the cup law true |
    | conjugation `deRhamConj` | upstream, no row | no: any σ-semilinear conjugation fixing `ι`-images gives the same law |
    | ι = `fieldToDeRhamCohomology ℚ` | "Rational-to-de Rham map and the range of F^p" | the ι law is stated against it; a nonzero rational scalar on ι would cancel (it appears on both sides) |
    | ℕ degrees cast to ℤ | (no row; the convention of `fieldToDeRhamCohomology_cup`) | no |

    Missing: a row for the pullback on `H_dR` itself (required change 3). No cited input carries a convention from a paper; every input is a checked local lemma or an upstream definition.

14. **Equality first (item 7).** Every law is an identity, proved exactly: `_fieldToDeRhamCohomology`, `_comp`, `_id`, `_cupBilinear`, `_cup` and `_conj` are equations with no scalar. No inclusion is claimed.

15. **Pin drift (item 8).** None. The branch is `main` at `19a4bda` plus two commits; `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are unchanged (upstream `2ead713`), the pin every dependency was checked against.

## Required changes

1. `HodgeLadder/Hodge/DeRhamPullback.lean`, after `deRhamPullback_fieldToDeRhamCohomology`, add (scratch: compiles, 14 s of kernel time):

   ```lean
   /-- **Uniqueness.** A `ℂ`-linear map `H_dR^n(Y) →ₗ[ℂ] H_dR^n(X)` that sends `ι α` to
   `ι (g^* α)` for every `α ∈ H^n(Y; ℚ)` is `deRhamPullback g n`: the classes `ι α` span
   `H_dR^n(Y)` over `ℂ`. This is the step "hence everywhere" of `de-rham-hypercohomology-pullback`. -/
   theorem deRhamPullback_unique (g : X ⟶ Y) (n : ℕ) (φ : H_dR^n(Y) →ₗ[ℂ] H_dR^n(X))
       (hφ : ∀ α : H^n(Y; ℚ), φ (fieldToDeRhamCohomology ℚ Y n α) =
         fieldToDeRhamCohomology ℚ X n (Cup.pullbackCoh g n α)) :
       φ = deRhamPullback g n := by
     refine LinearMap.ext_on (span_range_fieldToDeRhamCohomology_rat Y n) ?_
     rintro _ ⟨α, rfl⟩
     rw [hφ, deRhamPullback_fieldToDeRhamCohomology]
   ```

   Add `* HodgeLadder.deRhamPullback_unique`: a `ℂ`-linear map agreeing with `ι ∘ g^*` on rational classes is `deRhamPullback g n` to "Main results", and `HodgeLadder.deRhamPullback_unique` to the ledger's `declarations` after `HodgeLadder.deRhamPullback_fieldToDeRhamCohomology`.

2. Same file, docstring of `deRhamPullback_cup`, append the sentence:

   ```
   With literal `ℤ` degrees (`deRhamCup x y 2 _`) `rw` and `simp` with this lemma fail on `↑2`
   against `2` in a dependent position; use `exact`, or `LinearMap.congr_fun₂` of
   `deRhamPullback_cupBilinear` (the form `weil-eigen-algebra`'s `hS` takes).
   ```

3. `docs/conventions.md`, add after the row "Base change ℂ ⊗_ℚ M and the rank of an infinite-dimensional space":

   ```
   | Pullback on de Rham cohomology | this repository, `HodgeLadder.deRhamPullback`, `deRhamPullback_fieldToDeRhamCohomology`, `deRhamPullback_unique`, `deRhamPullback_comp`, `deRhamPullback_id`, `deRhamPullback_cupBilinear`, `deRhamPullback_cup`, `deRhamPullback_conj` (`HodgeLadder/Hodge/DeRhamPullback.lean`, rung `de-rham-pullback`) | `g : X ⟶ Y` gives `H_dR^n(Y) →ₗ[ℂ] H_dR^n(X)`, defined through rational classes as `deRhamBaseChangeEquiv X n ∘ (pullbackCohLinear g n).baseChange ℂ ∘ (deRhamBaseChangeEquiv Y n)⁻¹`, equivalently the unique ℂ-linear map with `g^* (ι α) = ι (pullbackCoh g n α)`; composition in Mathlib's diagrammatic order, `(g ≫ h)^* = g^* ∘ₗ h^*`; no sign, no scalar; no information about forms | the additive map: none of the base-change factor order, a conjugated ℂ-action or a nonzero rational scalar on ι (each cancels). The cup law holds for any uniform cup convention on X and Y; the conjugation law for any semilinear conjugation fixing ι-images. ℂ-linearity, and so the eigenspace arguments of `weil-surface-reduction` and `elliptic-curve-h1-eigen`, depend on upstream's ℂ-action (row "Complex structure on H_dR"). Agreement with the pullback of forms, and so `hodge-filtration-pullback`, is `de-rham-hypercohomology-pullback` (open), which closes through `deRhamPullback_unique` | read from source; the ℂ-action in the statements is `deRhamHypercohomologyComplexModule` by `with_reducible rfl` in a scratch file importing the module (red team 2026-11-28, `docs/sketches/de-rham-pullback.redteam.md`) |
   ```

4. `docs/gaps.md`, "De Rham complex and holomorphic forms", add after the row for `HodgeLadder.Hodge.DeRhamCupGradedComm`:

   ```
   | `HodgeLadder.deRhamPullback`, `deRhamPullback_fieldToDeRhamCohomology`, `deRhamPullback_unique`, `deRhamPullback_comp`, `deRhamPullback_id`, `deRhamPullback_cupBilinear`, `deRhamPullback_cup`, `deRhamPullback_conj` (pullback on `H_dR` for smooth projective integral X, Y, through rational classes and the base change) | `HodgeLadder.Hodge.DeRhamPullback` | 25 | upstream has no pullback on `H_dR` at the pin; a pin bump that adds one (for example from a map of de Rham complexes) must be compared with this row through `deRhamPullback_unique` (direction, composition order, no sign; row "Pullback on de Rham cohomology" in `docs/conventions.md`); rung `de-rham-pullback` | 2026-11-28 |
   ```

5. `docs/gaps.md`, Known weaknesses, the row on the kernel cost of `fieldCohomologyModule`: append to its first cell:

   ```
    `HodgeLadder.Hodge.DeRhamPullback` (red team `de-rham-pullback`, serial scratch copy): `deRhamPullback` 27.1 s, `_fieldToDeRhamCohomology` 36.6 s, `_comp` 10.4 s, other laws under 8 s each, 92 s of type checking; with the shortcut instance declared in the consuming file 99 s, no gain, since the instance terms sit in the imported types of `deRhamBaseChangeEquiv` and `pullbackCohLinear`. A shortcut helps only if declared below `HodgeLadder.Pullback.Functorial` in the import graph.
   ```

6. `ledger/ladder.json`, `de-rham-pullback` note: replace the final sentence "Kernel cost: about 28 s for the definition, 31 s for the ι law, 2 to 9 s for each other law." with:

   ```
   Uniqueness: deRhamPullback_unique, a ℂ-linear map sending ι α to ι (pullbackCoh g n α) is deRhamPullback g n (the step de-rham-hypercohomology-pullback closes through). Kernel cost: about 27 s for the definition, 37 s for the ι law, 14 s for uniqueness, 3 to 10 s for each other law; a consumer-side Module ℚ shortcut instance does not reduce it (docs/gaps.md, Known weaknesses). Red team docs/sketches/de-rham-pullback.redteam.md, pass with changes.
   ```

   and update the roadmap row's last cell to end `; uniqueness `deRhamPullback_unique`; test `p1p1_deRhamPullback_fst_class_ne_zero`; `docs/sketches/de-rham-pullback.redteam.md``.

Then rerun `python3 tools/check.py`.

## Optional changes

1. Add `deRhamPullback_injective_of_section` to the main module and `p1p1_deRhamPullback_fst_injective` to the test module, with the text of finding 10, and list both in the ledger. Kernel cost under 0.01 s.
2. Split the test into its own rung `de-rham-pullback-test` (kind `test`, module `HodgeLadder.Tests.DeRhamPullbackP1p1`), as `pullback-functorial-test`, so each ledger entry names the module its declarations live in.

## What was tried

- The consumer's `hS`, bundled (works) and pointwise through `simpa` (fails on `↑2` against `2`; `exact` works). Finding 8.
- Feeding `hS` to `ker_sub_smul_le_span_of_eigen` with a generic family `e`, `μ`, `he`, `hspan` (works).
- The uniqueness lemma (works, 14 s kernel) and injectivity along a section, generic and at `prod.fst` on ℙ¹ × ℙ¹ (works, under 0.01 s).
- The instance check `(inferInstance : Module ℂ H_dR^n(X)) = deRhamHypercohomologyComplexModule X n` by `with_reducible rfl` (works).
- The `Module ℚ` shortcut instance in a copy of the module (no gain; finding 11).
- Trivial truth through a zero map, a subsingleton `H_dR`, an idle hypothesis, an identity conjugation: each refuted or excluded (finding 5).
- A search of upstream for an existing pullback on `H_dR` (none at `2ead713`).
