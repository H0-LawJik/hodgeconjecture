# Red team: `cup-singular-comparison-absolute` and `cup-graded-commutative`

Date: 2026-11-25. Main at `0eebcc1`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`; Tau Ceti files vendored in `port/LefschetzPort/TauCeti/` from Tau Ceti `7433fc3`. Targets: `HodgeLadder.Cup.cup_singular_comparison` (rung `cup-singular-comparison-absolute`), `HodgeLadder.Cup.cup_singular_comparison'` and `HodgeLadder.Cup.cup_gradedComm` (rung `cup-graded-commutative`), all in `HodgeLadder.Cup.CupSingular`. Inputs read: `cup-global-comparison` (`CupGlobal.lean`), `step3-named-class` (`Step3.lean`), `cup-top-open` (`TopOpenCup.lean`), `end-class-right-mult` (`EndClass.lean`), and the definitions `cup` (`Product.lean`, `Yoneda.lean`), `cupSing` (`SingularCup.lean`). Scratch files were compiled with `lake env lean` from the session scratchpad and are described by what they test; none is committed.

**Verdict: pass with changes.** The statement is about the objects of record (upstream's Ψ, the Yoneda product, Tau Ceti's Hatcher cup), the hypotheses are met by upstream's ℙ¹, nothing in the chain substitutes a local object for an upstream one in the statement, and the sign is the order reversal of Mathlib's diagrammatic `Ext.comp`. The changes (section 9) correct a ledger note that overstates an independent sign check, add the sign-free form of the identity, add a checked instantiation at ℙ¹, and update the conventions register (done in this pass).

## 1. Is this the statement of the literature?

The literature fact is that the sheaf-theoretic (Yoneda) product on H*(X; ℚ) = Ext*(ℚ_X, ℚ_X) and the singular cup product agree under the sheaf–singular isomorphism, up to an order or sign that depends on conventions. [Bredon, *Sheaf Theory*, ch. II], [Iversen, *Cohomology of Sheaves*, ch. II]: unverified, not opened, not in `docs/references.md`. The singular cup is [Hatcher, §3.2]: (φ ⌣ ψ)(σ) = φ(σ|[v₀..v_p]) · ψ(σ|[v_p..v_{p+q}]), no sign; not in `docs/references.md` either (Tau Ceti's vendored docstring cites it).

| Literature | Lean | Source |
|---|---|---|
| H^n(X; ℚ), sheaf cohomology of the constant sheaf on X(ℂ) | `H^n(X; ℚ)` (upstream notation) | upstream statement library |
| sheaf–singular isomorphism | `AlgebraicGeometry.ComplexPoint.rationalCohomologyAddEquivSingularCohomology X n` (fully qualified by `#check` with `pp.fullNames`; no local declaration of that name in `HodgeLadder/` or `port/`) | upstream `Other/AlgebraicGeometry/Cohomology/GlobalSections.lean:310` |
| singular cohomology | `AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint X)) n` (upstream, linear duals of `SingularChainComplex`) | upstream |
| Yoneda product | `HodgeLadder.Cup.cup x y n h = e⁻¹(e x ≫ e y)` with `Abelian.Ext.comp` (diagrammatic: x first) and e = `rationalExtEquiv` | local definition (rung `cup-product`) |
| singular cup, Hatcher's convention | `HodgeLadder.Cup.cupSing`: `TopCat.singularCup ℚ (λ_ _).inv (λ_ (𝟙_ _)).hom` transported along `cohIso` (degreewise `ModuleCat.homLinearEquiv`, differentials equal by `rfl`) | vendored Tau Ceti; the face formula is a checked lemma in the port, `cochainValuesEquiv_cupCochain_alexanderWhitneyDiagonal` (`port/.../Cohomology/Cup/Basic.lean`), with the same `u = (λ_ _).inv`, `μ = (λ_ _).hom` as `tcCup` |
| identity | `Ψ (cup x y (p+q) rfl) = ((p*q : ℤ).negOnePow : ℤ) • cupSing (Ψ x) (Ψ y) (p+q) rfl`, all X with the four instances, all p, q, x, y | `cup_singular_comparison` |
| graded commutativity | `cup x y n h = (-1)^(p*q) • cup y x n _`, all x, y, n | `cup_gradedComm`; topological input `cupSing_gradedComm` (Tau Ceti `singularCup_gradedComm_tensorUnit`) |

Is it what a mathematician expects? Yes, once the order convention is read correctly. Scratch check (compiles): from `cup_singular_comparison'` and `cupSing_gradedComm`,

```
Ψ (cup x y (p+q) rfl) = cupSing (Ψ y) (Ψ x) (p+q) _      -- no sign
```

So the identity says: the Yoneda composite "x, then y" (applicatively y ∘ x) goes to y ⌣ x. The (−1)^{pq} in the stated form is exactly the cost of writing the singular factors in diagrammatic order. This matches the heuristic recorded by the `cup-front` red team (left multiplication by b is a chain map S → S[q], suggesting α ≫ β ↦ ±(b ∪ a)), and it matches the sketch's prediction made before the proof. It is not a sign error; a wrong sign anywhere in the chain (for instance in `rightMulCochain`) would have broken a kernel-checked step (`end_class_right_mult` pins the cocycle R_b against upstream's step 1, so R_b cannot be replaced by −R_b).

A second equivalent reading: if Ψ_n were renormalized by ε(n) = (−1)^{n(n−1)/2}, then ε(p)ε(q)ε(p+q) = (−1)^{pq} and the renormalized map would be multiplicative with no sign and no swap. The theorem does not claim that upstream's Ψ agrees with any textbook isomorphism; it is a statement about upstream's Ψ as defined. This is the correct target (statements of record are upstream), and it is recorded as a convention row (section 6).

## 2. Are the hypotheses satisfiable?

Yes, on upstream's ℙ¹. Scratch file (compiles, no `sorry`):

```lean
example : IsIntegral HodgeLadder.Tests.projectiveLine.left := inferInstance
example : Smooth HodgeLadder.Tests.projectiveLine.hom := inferInstance
example : T2Space (ComplexPoint HodgeLadder.Tests.projectiveLine) := inferInstance
example {p q : ℕ} (x : H^p(HodgeLadder.Tests.projectiveLine; ℚ))
    (y : H^q(HodgeLadder.Tests.projectiveLine; ℚ)) : True := by
  haveI : ∀ U : Opens (ComplexPoint HodgeLadder.Tests.projectiveLine), ParacompactSpace U :=
    openParacompactSpace _
  have := HodgeLadder.Cup.cup_singular_comparison HodgeLadder.Tests.projectiveLine x y
  have := HodgeLadder.Cup.cup_gradedComm HodgeLadder.Tests.projectiveLine x y rfl
  trivial
```

| Instance | Where it comes from |
|---|---|
| `IsIntegral`, `Smooth` | `HodgeLadder.Tests.ProjectiveLine` (rung `projective-line-witness`, global instances) |
| `T2Space (ComplexPoint X)` | upstream global instance `IsProjective.complexPoint_t2Space` (`Lemmas/AlgebraicGeometry/ComplexPoint/ProjectiveHausdorff.lean:283`), from the `IsProjective` instance on ℙ¹ |
| `∀ U, ParacompactSpace U` | upstream **theorem** (not instance) `ComplexPoint.openParacompactSpace` (`Lemmas/.../ProjectiveParacompact.lean:48`), for any integral smooth projective X; it must be supplied with `haveI` |

So for every smooth projective integral X the four hypotheses hold, the last by an explicit `haveI`. The hypotheses are also all used: they are exactly the instance arguments of Ψ, which appears in the statement. The theorem does not need `IsProjective`, so it also applies to any smooth integral X whose analytification is Hausdorff and hereditarily paracompact.

## 3. Trivially true?

Attempts, all failed: `rfl`, `subsingleton`, `simp [cup, cupSing, cupY]` on the goal of `cup_singular_comparison` (simp unfolds to `rationalExtEquiv … .symm (… .comp …)` against `cohIso … .inv (tcCup …)` and stops). No definition unfolds to a constant: `cup` is `Ext.comp` through an additive equivalence, `cupSing` is the Alexander–Whitney cochain formula, neither is zero by definition. H^n(X; ℚ) is not a subsingleton in general (H²(ℙ¹; ℚ) has rank one, `projective-line-h2`). There is no `ℕ∞` coercion and no empty index type; the sign is `Int.negOnePow` on `(p : ℤ) * q`, and `cup_singular_comparison'` converts it to `(-1 : ℤ) ^ (p * q)` by `Int.coe_negOnePow_natCast`, so there is no cast trick.

Intermediate local definitions (`singClass`, `namedClass`, `cupGlobal`, `rightMulCocycle`, `iotaZ`) do not occur in the final statement, so a mistaken intermediate definition could not make the final identity false; it could only make an intermediate rung's statement mean something else. They were still read (section 4).

What section 3 cannot exclude by itself: if both products were square-zero in positive degrees, the identity would hold trivially there. That is not the case for these definitions (they are concrete formulas, not axiomatized laws), but no instance at the pin has a nonzero product of two positive-degree classes, so the positive-degree content has no computed witness. See 7b.

## 4. Definitions: nothing local stands in for an upstream object

| Object | Local or upstream | Finding |
|---|---|---|
| Ψ | upstream `rationalCohomologyAddEquivSingularCohomology` (namespace `AlgebraicGeometry.ComplexPoint`, library `Other`) | the object of record. The proof splits it as `rationalCohomologySingularCochainAddEquiv` followed by `rationalSingularCochainHypercohomologyAddEquivCohomology` by `rfl` (`hΨ` in the proof), which doubles as a pin: a change of Ψ's definition upstream breaks the build here |
| chosen K-injective resolution in step 2 | upstream, by `Classical.choice` (`GlobalSections.lean:211`) | `cup_global_comparison` is proved for **every** K-injective resolution with the flasque quasi-isomorphism; `cup_global_chosen` only specializes it. The comparison does not depend on the choice |
| `singClass c hc` | local, `(ordinarySingularCohomologyEquivGlobalRaw ℚ Y n).symm (cls … c …)` | defined through upstream's own identification of singular cohomology with the raw top-open complex (`GlobalSections.lean:251`); `singClass_eq` shows it equals the direct class via upstream's `singularCochainComplexIsoTopOpen`. It is the singular class of c under upstream's identification |
| `cupGlobal a b` | local, `rightMulApp b ⊤ p (p+q) rfl a` = Tau Ceti `cupCochain` on ⊤ with a in front, b at the back, no sign | `tcTop_cupGlobal` checks it is Tau Ceti's cup on ⊤; `singularCup_naturality` moves it to X |
| `cupSing` | local transport of vendored Tau Ceti | Hatcher's formula is a checked lemma at the pin (section 1) |
| `cup` | local (rung `cup-product`) | `rationalExtEquiv` uses two isomorphisms ℚ ⊗ ℤ_Y ≅ ℚ_Y and forget(ℚ_Y) ≅ ℚ_Y, chosen by universal properties. A non-unit scalar in either would rescale `cup` (and `one`). The comparison theorem rules this out: with Ψ and `cupSing` fixed upstream and in Tau Ceti, `cup` is now pinned exactly (`cup = Ψ⁻¹ ∘ (cupSing with factors swapped)`). This is the main value of the rung for the front |

## 5. Checker

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`. `cup_singular_comparison`, `cup_singular_comparison'`, `cup_gradedComm`, `exists_singClass`, `cup_global_chosen`, `cup_global_comparison`, `shiftedHom_cup_core`, `cocycleComp_precomp`, `end_class_right_mult` and its five siblings, `step3_named_class`, `singClass`, `cupSing_singClass`, `tcTop_cupGlobal` and the rest of the cup ledger report `[Classical.choice, Quot.sound, propext]`; `#print axioms` in the scratch file agrees for the two main theorems (this covers the vendored Tau Ceti closure transitively). Each ledger declaration is the one the title means.

Ledger nits: `cup-step3` lists module `HodgeLadder.Cup.TopOpenCup` while `step3_named_class` lives in `HodgeLadder.Cup.Step3` (harmless, TopOpenCup imports Step3). The module docstring of `CupSingular.lean` names the rung `cup-singular-comparison`; the ledger id is `cup-singular-comparison-absolute`.

## 6. Conventions

| Convention | Row in `docs/conventions.md` | Truth depends on it? |
|---|---|---|
| Yoneda order: `cup x y` = x followed by y (`Ext.comp`, diagrammatic) | "Cup product" (updated in this pass with the sign-free form) | Yes: swapping the order flips the sign for p, q odd. The statement as checked is consistent with it |
| Mathlib shift on complexes: differential (−1)^n d, maps unsigned; `Cocycle.equivHomShift` via `rightShift`; `Cochain.comp` unsigned | "Hom-complex composition and derived classes" | Yes, through `shiftedHom_cup_core` and `toSmallShiftedHom_cocycleComp`; all kernel-checked |
| R_b components (−1)^{pq}·(c ↦ c ∪ b), unsigned out of degree 0 | "Right multiplication as a Hom-complex cocycle" | Yes; it is the source of the (−1)^{pq}. Forced: the overall sign of R_b is pinned by `end_class_right_mult` |
| Singular cup: front p-face times back q-face, no sign | "Singular cup product" (updated: vendored, formula checked) | Yes |
| Singular coboundary δφ = φ ∘ ∂, no sign; `dualIsoYoneda` unsigned | "Singular coboundary" | Yes; the two cochain models agree by `rfl` on differentials |
| Upstream Ψ: no claimed agreement with a textbook isomorphism; a degree twist ε(n) = (−1)^{n(n−1)/2} would absorb the sign | **added**: "Sheaf–singular comparison Ψ" | Yes for how the sign is read; no for the truth of the checked identity, which is about Ψ as defined |
| `rationalExtEquiv` normalization (isos ℚ ⊗ ℤ_Y ≅ ℚ_Y, forget ℚ_Y ≅ ℚ_Y) | **added**: "Rational Ext normalization" | Yes for `cup`'s scale; now certified by this rung |
| Graded commutativity b ⌣ a = (−1)^{pq} a ⌣ b | Tau Ceti `singularCup_gradedComm_tensorUnit` | `cup_gradedComm`; insensitive to the order convention (the identity is symmetric under swapping factors and replacing the sign by its inverse) |

October 2026 failure mode (`LekiliSheridan2026`): every borrowed sign here enters a kernel-checked step, and the borrowed results (Tau Ceti's Hatcher formula and graded commutativity, upstream's Ψ) are used through their Lean statements, not through prose. The residual risk is interpretive: a later rung that reads "x ∪ y corresponds to Ψx ⌣ Ψy" without the sign would be wrong for p, q odd. The sign-free form (change 2) removes that trap.

## 7. Equality first

Both theorems are exact identities with an explicit sign, not "up to a nonzero scalar". The supported case is a separate open rung (`cup-singular-comparison`), whose sketch exists.

## 7b. Non-vacuity

What exists: `HodgeLadder.Tests.projectiveLine_one_cup_ne_zero` (degree (0, 2)); with this rung, scratch check: `cupSing (Ψ (one X)) z n _ = z` for all z, so on ℙ¹, `cupSing (Ψ one) (Ψ [pt]) ≠ 0` and `cupSing` is not zero in degree (0, 2). On ℙ¹ a product of two positive-degree classes lands in degree ≥ 4 (zero for a real surface) or is a product of H¹ classes, and H¹(ℙ¹; ℚ) = 0 mathematically (not computed at the pin), so ℙ¹ cannot test positive degrees.

Smallest lemma that would fail if the positive-degree content were trivial: for some X with the four instances, `∃ x y : H^1(X; ℚ), cup x y 2 rfl ≠ 0` (odd degrees, where the sign (−1)^{pq} = −1 is visible on an instance). It does not exist; it needs a curve of positive genus or an abelian surface at the pin. The even-degree test `cup-positive-degree-test` (ℙ¹ × ℙ¹, p = q = 2) is open, and it cannot see the sign: (−1)^{4} = 1. The ledger note on `cup-singular-comparison-absolute` says "cup-positive-degree-test checks it independently"; that is wrong on both counts (open, and blind to the sign). The kernel proof already determines the sign; what an odd test adds is a witness that the identity is not trivially satisfied there.

The same applies to `cup_gradedComm`: on ℙ¹ it reduces to the unit laws.

## 8. Pin drift

None: every rung in the chain was checked at the current pin `2ead713`, and the Tau Ceti files are a fixed vendored copy at `7433fc3`. Definitions to diff on the next bump (all upstream unless noted):

- `rationalCohomologyAddEquivSingularCohomology`, `rationalCohomologySingularCochainAddEquiv`, `hypercohomologyAddEquivConstantCohomology`, `rationalHypercohomologySingularCochainAddEquiv`, `rationalToSingularCochainComplexInt`
- `rationalSingularCochainHypercohomologyAddEquivCohomology`, `rationalSingularCochainHypercohomologyAddEquivGlobalSections`, `…OfResolution`, `globalSectionsSingularCochainComplexIntIsoExtend`
- `HereditarilyParacompact.ordinaryRationalSingularCohomologyEquivGlobalSections`, `ordinarySingularCohomologyEquivGlobalRaw`, `topOpenToGlobalSingularCochainSheafComplex`, `singularCochainComplexIsoTopOpen`, `globalRawSingularCochainComplexIso`, `topOpenForgottenSingularCochainHomologyIso`
- `singularCochainSheafComplexInt`, `singularCochainCoboundary`, `SingularChainComplex`, `linearDualCochainComplex`, `Cohomology`, the `H^n(X; ℚ)` notation
- `openParacompactSpace`, `IsProjective.complexPoint_t2Space` (for instantiation only)
- Mathlib: `Abelian.Ext.comp`, `Adjunction.extEquiv`, the `CochainComplex` shift, `HomComplex.Cocycle.equivHomShift`, `CohomologyClass.toSmallShiftedHom`
- vendored Tau Ceti: `cupCochain`, `tensorCochain`, `alexanderWhitneyDiagonal`, `singularCup`, `singularCup_gradedComm_tensorUnit`

Risk note: Ψ lives in upstream's `Other` library, which upstream describes as sanity checks and which its `CheckStatementImports` guard does not protect; it can change more freely than the statement library. The `rfl` split `hΨ` in the proof acts as a pin for the top-level composite only; the inner steps are pinned only by the proofs that unfold them (a changed inner definition breaks the build rather than silently changing the meaning, because the statement mentions only Ψ).

## 9. Verdict: pass with changes

1. **Ledger note** (`cup-singular-comparison-absolute`): replace "cup-positive-degree-test checks it independently" by: the sign is determined by the kernel proof; `cup-positive-degree-test` (open) is the even-degree non-vacuity test and cannot see the sign; an odd-degree test is the new rung below.
2. **Sign-free form**: add `cup_singular_comparison_swap : Ψ (cup x y n h) = cupSing (Ψ y) (Ψ x) n _` to `CupSingular.lean` (four lines, compiled in scratch: `rw [cup_singular_comparison' X x y h, cupSing_gradedComm …]` with `n := p + q`), list it under `cup-singular-comparison-absolute`, and cite it from downstream rungs that need multiplicativity.
3. **Instantiation test**: add the ℙ¹ instantiation of section 2 as a checked declaration in `HodgeLadder.Tests` (e.g. `projectiveLine_cup_singular_comparison`), so a change to the instance arguments of Ψ or to `openParacompactSpace` breaks the build. Optionally the unit corollary `cupSing (Ψ (one X)) z = z`.
4. **Docstrings**: in `CupSingular.lean`, name the rung `cup-singular-comparison-absolute` and cite the conventions rows "Cup product" and "Sheaf–singular comparison Ψ" in the docstrings of `cup_singular_comparison` and `cup_gradedComm` (rule in `docs/conventions.md`).
5. **Conventions register**: rows "Cup product" and "Singular cup product" updated, rows "Sheaf–singular comparison Ψ" and "Rational Ext normalization" added (done in this pass).
6. **New rung** `cup-odd-degree-test`: for some X satisfying the four instances, x, y ∈ H¹(X; ℚ) with `cup x y 2 rfl ≠ 0`. Depends on a positive-genus curve or abelian surface with H¹ computed; large, not urgent. Add citation keys for Hatcher and for a sheaf-theory source of the Yoneda–cup comparison to `docs/references.md` when one is opened.

## 10. Attempts that failed or were not completed

- `first | rfl | subsingleton | simp [cup, cupSing, cupY]` on the main goal: no closure (simp leaves the unfolded equation).
- `inferInstance` for `∀ U, ParacompactSpace U` on ℙ¹: not attempted as an instance search (upstream provides a theorem, not an instance); `haveI := openParacompactSpace _` works.
- Did not reopen Bredon, Iversen or Hatcher; the literature comparison above is unverified and rests on the Lean statements of Tau Ceti's formula and graded commutativity.
- Did not compute H¹ of any variety; no odd-degree instance exists at the pin.
