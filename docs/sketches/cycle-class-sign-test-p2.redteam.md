# Red team: `cycle-class-sign-test-p2` (statement and proof)

Date: 2026-11-27. Worktree `cycle-class-sign-test-p2` at `6084c3a`, plus the uncommitted `HodgeLadder/Tests/CycleClassSignTestP2.lean` (483 lines, built in the worktree) and the section "cycle-class-sign-test-p2: statement" of `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, the same as on `main`.

Read: the Lean file; the sketch section; the ledger entries of this rung, `cycle-class-multiplicative-p2`, `p2-point-class-nonzero`, `cycle-class-multiplicative-codim-zero`; `docs/conventions.md` (rows "Complex orientation of ℂ^p", "Fundamental-class normalization", "Point local coclass", "Transversal product of cycle classes", "Normalization iso against the singular transport", "Cohomology of an open, Mayer–Vietoris"); `docs/references.md`. Upstream at the pin: `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean` (`cycleComponentSupportedInjectiveClass`, `cycleComponentSheafClass`), `Definitions/.../Cycle/SmoothPair/CoclassSection.lean` (`smoothClosedSupportCoclassSection`), `Other/AlgebraicGeometry/Cycle/Component/PointClassNormalization.lean`, `Other/.../Component/PointCoclassNormalization.lean`, `Other/.../Component/PointPurity.lean`, `Other/.../Cycle/SmoothPair/PointPurity.lean`, `Other/.../Cycle/SmoothPair/PointCoclassSection.lean`, `Other/AlgebraicGeometry/ComplexPoint/LocalOrientation.lean`, `Other/.../ComplexPoint/CoclassOrientation.lean`.

Scratch files (in the worktree, `lake env lean`, deleted afterwards; the built module was imported, not recompiled):

| File | What | Result |
|---|---|---|
| RT1 | `#print axioms` of all 24 declarations; the "sign test" from the two earlier rungs only; trivial proofs of `deg [pt] = 1` | standard axioms everywhere; the sign test closes in 7 lines without the degree (finding 2); `rfl`, `simp`, `decide`, `norm_num [planeDegree]` fail |
| RT2 | a `module` file: are bodies of imported theorems visible to the guard? a transitive control | no imported theorem has a visible body (finding 4); the guard's walk from `planeLines_cup_eq_planeOrigin` does not reach `HodgeLadder.Local.ClassProduct`, which `HodgeLadder.Cycle.Multiplicative` imports and uses |
| RT3 | the closure of the degree roots, by module, in the guard's own view (`import all` of the tested module) | 12 753 constants over 942 modules; no reached module imports a forbidden module, directly or transitively |
| RT4, RT5 | a replacement guard by import closure (change A), with direct and transitive positive controls | degree roots and `planeDegree_eq_eval_of_restrict` clean; `planeDegree_planeLines_cup` caught through `CycleClassMultiplicativeP2`, also when only `HodgeLadder.Local.ClassProduct` is forbidden |
| RT6 | the exact text of change A, plus a `self` special case (in scratch the tested module is imported, so its constants carry a module index) | elaborates; the guard passes; `planeLines_cup_ne_neg_planeOrigin` as a root makes it fire |

`python3 tools/check.py --no-build` in the worktree after deleting the scratch files: `ACCEPTED: all checks passed`. The new module is not in the ledger yet, so the checker does not scan it; RT1 is the axiom evidence until phase 2 lists it.

**Verdict: pass with changes.** Every computation is correct and checked, with standard axioms. What the rung establishes is narrower than its title and note say:

- **It establishes** that upstream's point class has degree `+1` for a degree map that is an isomorphism `H⁴(ℙ²; ℚ) ≅ ℚ`, built without the multiplicativity proof: the class, lifted to `H⁴_{pt}`, carried by upstream's transport to `H⁴(ℙ²(ℂ), ℙ²(ℂ) ∖ pt; ℚ)` and evaluated on upstream's complex local orientation, gives `1`. New checked mathematics in the ladder: `H^{q+3}(ℙ²(ℂ) ∖ pt) = 0` for every `q`, `forgetSupport` bijective in degree 4, and `H⁴(ℙ²; ℚ)` one-dimensional.
- **It does not establish** anything about the sign of the multiplicativity theorem at `a = b = 1` beyond the checked identity. `deg ([L₀] ∪ [L₁]) = 1` is `planeLines_cup_eq_planeOrigin` followed by `deg [pt] = 1`, and `[L₀] ∪ [L₁] ≠ −[pt]` already follows from `cycle-class-multiplicative-p2` and `p2-point-class-nonzero` without the degree. No second computation of the product is made.
- **The value `1` is upstream's**, not the ladder's. The ladder's part of the proof cannot carry a sign (an equivalence's inverse applied to its own image; two identity pair maps). All the content sits in upstream's point-normalization chain, whose substantive step is `smoothClosedPointNormalModelPairMap_localClass` (the normal-chart class of a point is the `localChart` class, through complex-linear invariance of the standard class and a positive radial rescaling).
- **Its literature reading is conditional.** That `planeDegree` is ⟨−, [ℙ²]⟩ for the complex orientation is `planeDegree_eq_eval_of_restrict`, whose hypothesis (a class in `H₄(ℙ²(ℂ); ℚ)` restricting to the local orientation) is not met at the pin.

The changes: a sound independence guard (A), honest title, note and docstrings (B to D), a gaps entry for the kernel cost (E). Two strengthenings are proposed as optional or new rungs (F, G).

## 1. Is this the statement the literature makes?

Literature: for a compact connected complex manifold X of complex dimension n, the complex structure orients X, the fundamental class [X] ∈ H_{2n}(X; ℚ) is the unique class restricting at every (equivalently, at one) point x to the local orientation μ_x ∈ H_{2n}(X, X ∖ x; ℚ), and deg α = ⟨α, [X]⟩ on H^{2n}(X; ℚ) [`Hatcher2002` §3.3, Theorem 3.26 and the definition of the fundamental class; numbering unverified]. The class of a point has degree 1, and on ℙ² two distinct lines meet transversally in one point, so deg ([L₀] ∪ [L₁]) = 1 [`Hatcher2002` §3.2, the ring H*(ℂP²); `Fulton1998` ch. 8 and ch. 19, numbering unverified].

| Literature | Lean | Check |
|---|---|---|
| H^{2n}(X; ℚ) | upstream `H^(2 * 2)(projectivePlane; ℚ)` (sheaf cohomology of the constant sheaf) | the statement-of-record group; Ψ to singular cohomology only in `planeDegree_eq_eval_of_restrict` |
| μ_x, the complex local orientation at x = [0 : 0 : 1] | upstream `complexLocalOrientation projectivePlane 2 planeOriginPoint` = `localClassOfChart 2 (localChart …) …` of `standardComplexLocalClass ℚ 2` | `localChart` comes from algebraic étale coordinates, so it is holomorphic and carries the complex orientation; `standardComplexLocalClass` is the complex orientation of ℂ² by row "Complex orientation of ℂ^p" (pinned) |
| deg α = ⟨α, [X]⟩ | `planeDegree α` = ⟨T(a), μ_x⟩ with a the unique supported lift of α and T upstream's transport `complexSupportInjectiveSectionCohomologyEquiv … ⊤ 4 ∘ rationalSupportAddEquivSupportedInjectiveHomology`, pulled back along the identity of points | equals ⟨Ψ α, μ⟩ for every μ ∈ H₄(ℙ²(ℂ); ℚ) with μ ↦ μ_x (`planeDegree_eq_eval_of_restrict`). On a connected closed manifold that one-point condition determines μ and makes it the fundamental class of the orientation through μ_x, so the hypothesis is the literature's characterization; its discharge is missing (no μ at the pin) |
| deg [pt] = 1 | `planeDegree_planeOrigin` | exact, sign + |
| deg ([L₀] ∪ [L₁]) = 1 | `planeDegree_planeLines_cup` | by `rw [planeLines_cup_eq_planeOrigin]`; the ladder `cup` in degree `2 * (1 + 1)` |
| H⁴(ℙ²; ℚ) ≅ ℚ | `planeDegree_bijective`, `planeDegree_eq_one_iff` | exact |

The rung's title says the degree is "built from the complex orientation, independently of the multiplicativity proof", and concludes "so deg ([L₀] ∪ [L₁]) = 1 as in the literature". Both clauses are true. The title still overstates in two ways: the rung id and the ledger note present it as a test of the sign of `cycle-class-multiplicative` at a = b = 1, which it is not (finding 2), and "as in the literature" holds only through the conditional `planeDegree_eq_eval_of_restrict`. Change B gives the corrected title and note.

### What is definition, what is upstream mathematics, what is ladder mathematics

| Fact | Status | Where a sign could live |
|---|---|---|
| `[pt]` is `forgetSupport` of the supported class | upstream definition (`cycleComponentSheafClass_eq_forgetSupport`, `rfl`) | nowhere |
| the supported class is the unique class whose normalized section is the normal-chart coclass section | upstream definition (`cycleComponentSupportedInjectiveClass`) | nowhere |
| the normal-chart coclass section at a point equals the point coclass `analyticPointLocalCoclass` | upstream theorem chain: `cycleComponentSupportedInjectiveClass_point_normalization` ← `cycleComponentSmoothSupportCoclassSection_global_point_normalization` ← `smoothClosedSupportCoclassSection_eq_point_of_singleton` ← `smoothClosedPointNormalCoclass_eq_analyticPointLocalCoclass` ← `smoothClosedPointNormalModelPairMap_localClass` | here: the normal parametrization is the `localChart` composed with a complex-linear map and a radial compression; upstream proves both preserve `standardComplexLocalClass` (`centeredComplexLinear_preserves_standardComplexLocalClass`, `centeredComplexUnivBall_preserves_standardComplexLocalClass`). A non-complex-linear normal coordinate would show here |
| the point coclass pairs to 1 with `complexLocalOrientation` | upstream: `analyticPointLocalHomologyClass_eq_complexLocalOrientation` is `rfl`, then `normalizedRelativeCoclass_pairing_self` | nowhere: definitional normalization |
| the inverse of `forgetSupport` returns the supported class | ladder, `planeDegree_forgetSupport` (`AddEquiv.symm_apply_apply`) | nowhere: an equivalence's inverse on its own image |
| the two pair maps compose to the identity | ladder, `relativeCohomologyMap_pointToNeighborhood_toPoint` | nowhere: identities of points |
| `forgetSupport` is bijective in degree 4 | ladder mathematics: `subsingleton_H'_compl_planeOrigin`, `forget-support-exact` | no sign (vanishing statements); it makes the degree defined on all of H⁴ and bijective, and is not used in the value on `[pt]` beyond well-definedness |
| T agrees with Ψ under forgetting the support | ladder, `forgetRel_supportedEquivPair`, `supportedEquivPair_eq_transport` (rung `supported-pair-forget`) | checked, no sign; used only in `planeDegree_eq_eval_of_restrict` |

So `deg [pt] = 1` is a corollary of upstream's own normalization theorems read as a number. The sketch's sentence "A sign in any of them would give −1" (about the forget inverse, the point normalization, the transport and the pair maps) is right only for the upstream normalization: the ladder's steps cannot carry a sign, and a sign in T would cancel, because T sits inside both the normalization of `[pt]` (row "Normalization iso against the singular transport") and the degree. A sign in T against Ψ is visible only through `planeDegree_eq_eval_of_restrict`, and there `forgetRel_supportedEquivPair` excludes it. Change D corrects the sentence.

## 2. Can the hypotheses be satisfied?

The main statements have no hypotheses. `planeDegree_eq_eval_of_restrict` has one, `hμ`. It is satisfiable in mathematics: H₄(ℙ²(ℂ); ℚ) → H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ pt; ℚ) is onto because H₃(ℙ²(ℂ) ∖ pt; ℚ) = 0 (the complement retracts onto a line, S²). At the pin it is not discharged. A route exists from checked pieces and is new rung G: `subsingleton_H'_three_compl_planeOrigin` in sheaf form, Ψ on the open (upstream's `openParacompactSpace` already supplies the instance used in this file), duality over ℚ (a ℚ-vector space with zero dual is zero), and the homology sequence of the pair. The lemma is not vacuous for lack of a μ.

## 3. Trivially true?

`deg [pt] = 1`: `rfl`, `simp`, `decide` and `norm_num [planeDegree]` fail (RT1, also the prover's list). The proof is about 40 lines of upstream normalization and identity pair maps; it unfolds to nothing smaller.

`planeLines_cup_ne_neg_planeOrigin`: **trivially true from earlier rungs.** RT1 proves it without the degree map:

```lean
example :
    HodgeLadder.Cup.cup
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0))
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1))
        (2 * (1 + 1)) (by ring) ≠
      -cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin := by
  intro h
  rw [planeLines_cup_eq_planeOrigin] at h
  apply projectivePlane_point_class_ne_zero
  have h2 : (2 : ℚ) • cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin
      = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
```

In a ℚ-vector space, x = [pt] ≠ 0 forces x ≠ −x. The theorem is true and stays, but it is not evidence the degree adds; its docstring and the module docstring call it "the sign test" (change C).

`planeDegree_bijective` is not trivial: injectivity uses `span_complexLocalOrientation_eq_top` and needs H³ = 0, surjectivity needs H⁴ = 0 of the complement. `subsingleton_H'_compl_planeOrigin` is a real Mayer–Vietoris computation (section 6, row "Cohomology of an open").

No definition unfolds to `True`, no `ℕ∞` coercion is load-bearing (the degree index `2 * (1 + 1)` against `2 * 2` is closed by `Nat` reduction, and `coheight_planeOrigin` against `coheight_planeOrigin_add` by proof irrelevance), no index type is empty.

## 4. Interface axioms

None: a test rung over upstream definitions, no structure.

## 5. Axioms and names

RT1: all 24 declarations print `[propext, Classical.choice, Quot.sound]`: `subsingleton_H'_compl_planeOrigin`, `forgetSupport_planeOrigin_bijective`, `planeOriginForgetEquiv`, `pointToNeighborhoodSupportPairMap`, its two composition lemmas and two `relativeCohomologyMap` corollaries, `planeOriginPairMap`, `planeOriginLocalize`, `planeOriginEvaluation`, `planeDegree`, `planeDegree_forgetSupport`, `planeDegree_planeOrigin`, `planeDegree_planeLines_cup`, `planeDegree_bijective`, `planeDegree_eq_one_iff`, `planeDegree_neg_planeOrigin`, `planeLines_cup_ne_neg_planeOrigin`, `planeOriginSupportInclusion`, `planeOriginPairMap_eq_comp`, `relativeHomologyMap_planeOriginSupportInclusion_projection`, `relativeHomologyMap_planeOriginPairMap_orientation`, `planeDegree_eq_eval_of_restrict`. `python3 tools/check.py --no-build`: accepted (the module is not scanned until phase 2 names it in the ledger). The declarations are the ones the sketch lists; the ledger entry has none yet.

## 6. Conventions

| Convention | Used by | Truth depends on it? | Row |
|---|---|---|---|
| Complex orientation of ℂ² (consecutive Re, Im) | `complexLocalOrientation` and, through the normal charts, the normalization of `[pt]` | no: both sides share `standardComplexLocalClass`, so a real-parts-first ordering, sign (−1)^{d(d−1)/2} = −1 at d = 2, would cancel. The rung cannot detect it; the pinned row does | "Complex orientation of ℂ^p" |
| Complex conjugate orientation | same | no: (−1)^d = +1 at d = 2. A degree on ℙ² cannot tell the complex orientation from its conjugate | new row "Degree on H⁴(ℙ²)" |
| Fundamental-class normalization | `[pt]` | yes, it is what the rung reads | "Fundamental-class normalization", "Point local coclass" |
| Transport T and the normalization iso | `planeOriginLocalize`, and `[pt]` | no for `deg [pt] = 1` (T on both sides); yes for the literature reading, fixed by `forgetRel_supportedEquivPair` (no sign) | "Normalization iso against the singular transport", "Supported comparison Φ" |
| Ψ (sheaf to singular) | `planeDegree_eq_eval_of_restrict` | a sign of the form (−1)^n, (−1)^{n(n−1)/2} or (−1)^{n(n+1)/2} is +1 at n = 4 | "Sheaf–singular comparison Ψ" |
| Universal-coefficient evaluation | `planeOriginEvaluation`; the point coclass is normalized through the same `relativeCohomologyEquivDualHomology` | no: same equivalence on both sides; absolute and relative agree by upstream `cohomologyEquivDualHomology_forgetSupport` | new row |
| Mayer–Vietoris | `subsingleton_H'_compl_planeOrigin` | no: vanishing only | "Cohomology of an open" |
| Transversal product, sign at a = b = 1 | `planeDegree_planeLines_cup` through the checked identity | read through the identity; not tested | "Transversal product" (tail updated) |

The pair facts (`deg [pt] = 1`, `[L₀] ∪ [L₁] = [pt]`) constrain only a product. Write upstream's `[Lᵢ] = cᵢ · h` with h the literature's line class and the ladder `cup` as ε times the literature's cup in bidegree (2, 2). Then, reading the degree as the literature's (section 1, conditional), ε · c₀ · c₁ = 1. `cup-singular-comparison` gives ε = +1 against Hatcher's cup at p = q = 2 (sign (−1)^{pq} = +1), so c₀ · c₁ = 1. The test does not show c₀ = c₁ = 1, nor c₀ = c₁.

`docs/conventions.md`: added the row "Degree on H⁴(ℙ²)" and replaced the "Proposed test" tail of the row "Transversal product of cycle classes".

## 7. Equality first

The rung is an identity, `deg [pt] = 1`, proved exactly, with sign +, no scalar. `deg ([L₀] ∪ [L₁]) = 1` is exact. Nothing is up to a scalar.

## 7b. Non-vacuity

Smallest lemma that fails if the degree were degenerate: `planeDegree_neg_planeOrigin` (`planeDegree (−[pt]) = −1`), with `planeDegree_bijective`; both exist. If `planeDegree` were the zero map, `planeDegree_planeOrigin` would fail. The test that would fail if upstream's `[pt]` had the opposite normalization is `planeDegree_planeOrigin` itself; that is the rung.

## 8. Pin drift

Checked at `2ead713`, the current pin; no drift. For the next bump, diff: upstream `cycleComponentSupportedInjectiveClass`, `cycleComponentSheafClass_eq_forgetSupport` (`rfl`), `cycleComponentSupportedInjectiveClass_point_normalization`, `analyticComponentPointSupportedInjectiveCoclass_relative`, `analyticComponentPointRelativeCoclass` (unfolded by `change`), `smoothClosedPointNormalModelPairMap_localClass`, `analyticPointLocalCoclass`, `analyticPointLocalCoclass_apply_complexLocalOrientation`, `complexLocalOrientation`, `span_complexLocalOrientation_eq_top`, `neighborhoodSupportToPointPairMap`, `range_cycleComponentMap`, `supportInclusionPairMap`, `relativeChainProjection_supportInclusion`, `cohomologyEquivDualHomology_forgetSupport`, `relativeCohomologyEquivDualHomology_relativeCohomologyMap`, `openParacompactSpace`; the ladder's `forgetSupport_injective_of_subsingleton`, `forgetSupport_surjective_of_subsingleton`, the Mayer–Vietoris pieces of `ProjectivePlanePoint.lean`, `supportedEquivPair_eq_transport`, `forgetRel_supportedEquivPair`, `ofSubsetIsoNeighborhoodTop`. A change in the body of `analyticComponentPointRelativeCoclass` breaks the `change` step of `planeDegree_planeOrigin`, so that drift breaks the build.

## Findings

1. **What the test tests.** Upstream's `[pt]` evaluated, through upstream's transport, on upstream's complex local orientation. The value 1 comes from upstream's point-normalization chain; the ladder's steps cannot carry a sign. Sound as a `test` rung with the title and note of change B.
2. **The "sign test" is not new evidence.** `planeLines_cup_ne_neg_planeOrigin` follows from `cycle-class-multiplicative-p2` and `p2-point-class-nonzero` in 7 lines (section 3). `deg ([L₀] ∪ [L₁]) = 1` reads the product through the checked identity. The multiplicativity theorem's sign at a = b = 1 has no independent recomputation after this rung, as before; what is new is that `[pt]` is pinned, which turns the identity into ε · c₀ · c₁ = 1 (section 6).
3. **The computation is correct.** H^{q+3}(ℙ²(ℂ) ∖ pt) = 0 for all q: the three covers (two half-spaces, two slit pieces, two charts) and the step `H^q(A ⊓ B) = 0`, `H^{q+1}(A) = H^{q+1}(B) = 0` ⇒ `H^{q+1}(A ⊔ B) = 0` are right, as is the degree bookkeeping (q + 1, q + 2, q + 3). `forgetSupport` is bijective in degree 4 by `forget-support-exact` at n = 3 (injective) and n = 4 (surjective). H⁴ is one-dimensional. No sign in the definition of the degree: equivalences, pullbacks along identities of points, evaluation. `subsingleton_H'_three_compl_planeOrigin` is now the case q = 0 of the new lemma; keep it (it is named by a checked rung).
4. **The independence guard is unsound in general, correct here.** Under the module system, bodies of imported theorems are not in the environment (RT2: `planeLines_cup_eq_planeOrigin`, `cycleComponentSheafClass_cup_of_transversal`, upstream `cycleComponentSupportedInjectiveClass_point_normalization` all have `value? = none`). The walk therefore stops at the type of every imported theorem: from `planeLines_cup_eq_planeOrigin` it does not reach `HodgeLadder.Local.ClassProduct`, which the multiplicativity proof uses. The guard would miss a forbidden dependency inside the proof of any imported lemma. It visits about 12 700 constants in the build environment, against the sketch's "103 334 constants … private bodies included". Its positive control tests only a direct use. It also passes silently if its fuel runs out. RT3 confirms the conclusion soundly for this file: no module reached from the roots imports a forbidden module. Change A replaces it with a check by import closure, which is sound because a hidden proof can use only constants from its module's imports.
5. **Kernel cost.** 195 s of kernel time, about 4.5 min per elaboration. Recent CI runs on `main` take 3 to 4 minutes with cached builds, against a 240-minute limit; the module is a leaf (nothing imports it), so it is rebuilt only when it or one of its imports changes, and on pin bumps. Accept for merge. Reduction is not a merge condition; record it in `docs/gaps.md` (change E) with the hot spots the prover measured.
6. **`planeDegree_eq_eval_of_restrict` is the literature link, and conditional.** Its one-point hypothesis is the full literature characterization of [ℙ²] (section 1), so it is not weaker than a hypothesis at every point. It also carries the one input that ties T to Ψ. Its docstring is accurate.

## Changes

**A (required). Replace the guard.** Replace everything from the comment block before `open Lean in` to the end of the file with the following (RT6 ran this text with a `self` special case that the file itself does not need; RT5 is the transitive control):

```lean
-- Independence guard: the degree map and `deg [pt] = 1` do not use the multiplicativity proof.
-- The module imports it (for `planeDegree_planeLines_cup`, the positive control). Bodies of
-- imported theorems are not visible under the module system, so the guard walks the constants of
-- this file (types and values) and judges every imported constant by its module: it fails if that
-- module is forbidden or imports a forbidden module, directly or transitively. This is sound,
-- since a proof in a module uses only constants of the module and its imports. A docstring cannot
-- precede `run_cmd`.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let names := env.header.moduleNames
  let forbidden : List Name :=
    [`HodgeLadder.Cycle.Multiplicative, `HodgeLadder.Tests.CycleClassMultiplicativeP2,
     `HodgeLadder.Local.ClassProduct, `HodgeLadder.Normalization.Germ]
  for m in forbidden do
    unless (env.getModuleIdx? m).isSome do
      throwError "independence guard is stale: {m} is not imported"
  -- modules whose import closure meets a forbidden module (`moduleNames` is in import order)
  let mut tainted : NameSet := {}
  for i in [0:names.size] do
    let m := names[i]!
    if forbidden.contains m ||
        env.header.moduleData[i]!.imports.any (fun im => tainted.contains im.module) then
      tainted := tainted.insert m
  let check (roots : List Name) : CommandElabM (Option (Name × Name)) := do
    let mut todo := roots
    let mut visited : NameSet := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail
      if visited.contains n then continue
      visited := visited.insert n
      if let some i := env.getModuleIdxFor? n then
        let m := names[i.toNat]!
        if tainted.contains m then return some (n, m)
        continue
      match env.find? n with
      | some ci =>
        todo := (ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]).toList ++ todo
      | none => throwError "independence guard: {n} not found"
    return none
  -- positive control: the cup corollary goes through the multiplicativity proof
  if (← check [`HodgeLadder.Tests.planeDegree_planeLines_cup]).isNone then
    throwError "independence guard is blind: planeDegree_planeLines_cup shows no forbidden use"
  if let some (n, m) ← check [`HodgeLadder.Tests.planeDegree,
      `HodgeLadder.Tests.planeDegree_planeOrigin, `HodgeLadder.Tests.planeDegree_bijective,
      `HodgeLadder.Tests.planeDegree_forgetSupport] then
    throwError "the degree uses {n}, from {m}, which is or imports the multiplicativity proof"
```

The loop terminates without fuel: only constants of this file are expanded, and each is expanded once. Then, in the sketch section "Independence, guarded", replace "walks the constant closure (types and values, private bodies included) of `planeDegree`, `planeDegree_planeOrigin`, `planeDegree_bijective` and `planeDegree_forgetSupport` (103 334 constants in scratch) and fails the build if it meets a constant of" with: "walks the constants of this file reachable from `planeDegree`, `planeDegree_planeOrigin`, `planeDegree_bijective` and `planeDegree_forgetSupport` (types and values) and judges each imported constant by its module, since imported theorem bodies are not visible under the module system; it fails the build if that module is, or imports directly or transitively,". Replace "(blind guard, the positive control)" with "(blind guard, the positive control); the red team checked a transitive control with only `HodgeLadder.Local.ClassProduct` forbidden".

**B (required, phase 2). Ledger title and note.** Title: "On ℙ², the degree map H⁴(ℙ²; ℚ) → ℚ that lifts a class to H⁴_{pt} and evaluates it on the complex local orientation at [0 : 0 : 1] is an isomorphism with deg [pt] = 1, built without the multiplicativity proof; with cycle-class-multiplicative-p2, deg ([L₀] ∪ [L₁]) = 1". Replace the note's sentence "A degree map computed from upstream's point-class normalization, with no use of cycle-class-multiplicative, would make deg ([L₀] ∪ [L₁]) = 1 an independent check of that agreement; a wrong normalization or an odd sign convention at a = b = 1 would give −1." with: "deg [pt] = 1 is upstream's point normalization (cycleComponentSupportedInjectiveClass_point_normalization, through complex-linear invariance of the standard class) read as a number; the ladder's steps (the inverse of forgetSupport, identity pair maps) carry no sign. deg ([L₀] ∪ [L₁]) = 1 reads the product through planeLines_cup_eq_planeOrigin and recomputes nothing, and [L₀] ∪ [L₁] ≠ −[pt] already follows from cycle-class-multiplicative-p2 and p2-point-class-nonzero. With ε = +1 from cup-singular-comparison, the pair gives c₀ · c₁ = 1 for the scalars of [L₀], [L₁] against the literature's line class. The literature reading deg = ⟨Ψ −, [ℙ²]⟩ is planeDegree_eq_eval_of_restrict, conditional on a class in H₄(ℙ²(ℂ); ℚ) restricting to the local orientation (not at the pin). Insensitive to the ordering convention of ℂ² (shared by both sides) and to conjugation ((−1)² = 1)." In the note of `cycle-class-multiplicative-codim-zero`, replace "(cycle-class-sign-test-p2, open)" with "(cycle-class-sign-test-p2 pins deg [pt] = 1 and reads the product through the identity)".

**C (required). Docstrings of the sign test.** Docstring of `planeLines_cup_ne_neg_planeOrigin`: "`[L₀] ∪ [L₁] ≠ −[pt]`, read off the degree (`1` against `−1`). It also follows from `planeLines_cup_eq_planeOrigin` and `projectivePlane_point_class_ne_zero` alone, since `[pt] ≠ 0` in a ℚ-vector space; it adds nothing beyond `deg [pt] = 1`." Rename the section header `### Consequences: the sign test` to `### Consequences`. In the module docstring, after "`[L₀] ∪ [L₁] ≠ −[pt]` (`planeLines_cup_ne_neg_planeOrigin`)", add: "The value `1` is upstream's point normalization read as a number: the steps taken here (the inverse of `forgetSupport`, identity pair maps) carry no sign. The cup corollary reads the product through the checked identity and is not a second computation of it."

**D (required). Sketch, "What the test shows".** Replace "What the computation checks is the path from the global class to that coclass: the inverse of `forgetSupport`, upstream's point normalization of the supported class, upstream's transport, and the pair maps. A sign in any of them would give −1." with: "On that path only upstream's point normalization of the supported class could carry a sign (its substantive step is `smoothClosedPointNormalModelPairMap_localClass`): the inverse of `forgetSupport` is applied to its own image, the pair maps compose to the identity, and the transport T enters both the normalization of [pt] and the degree, so a sign in T would cancel. A sign in T against Ψ shows only through `planeDegree_eq_eval_of_restrict`, where `forgetRel_supportedEquivPair` excludes it."

**E (required, phase 2). `docs/gaps.md`, "Known weaknesses".** Add: "`HodgeLadder.Tests.CycleClassSignTestP2` takes about 4.5 minutes to elaborate, 195 s of it kernel type checking, mostly in declarations whose types restate upstream's `forgetSupport` (stated for a field K) with the `H^n(X; ℚ)` notation's instances: `planeOriginForgetEquiv` 43 s, `planeDegree_bijective` 37 s, `planeOriginLocalize` 30 s, `planeDegree_forgetSupport` 27 s. A leaf module; accepted. Reduce if a downstream file imports it." Phase 2 also lists `pointToNeighborhoodSupportPairMap` and its four lemmas under "General lemmas kept local", as the sketch plans.

**F (optional). Unconditional singular reading.** The proof of `planeDegree_eq_eval_of_restrict` contains, before it uses μ, a statement that needs no hypothesis: for every α there is c in singular `H⁴(ℙ²(ℂ), ℙ²(ℂ) ∖ pt; ℚ)` whose image in singular `H⁴(ℙ²(ℂ); ℚ)` is `Ψ α` and with `planeDegree α = ⟨c, complexLocalOrientation …⟩`. Stated in the spelling of that proof, it is the literature's "restrict Ψ α to the point and evaluate on the local orientation" without a fundamental class. Not elaborated by the red team; skip it if it adds kernel time.

**G (new rung, proposed). `p2-fundamental-class`:** some μ ∈ H₄(ℙ²(ℂ); ℚ) restricts to `complexLocalOrientation projectivePlane 2 planeOriginPoint`, from H₃(ℙ²(ℂ) ∖ pt; ℚ) = 0 (sheaf H³ = 0, Ψ on the open, duality over ℚ) and the homology sequence of the pair. It discharges the hypothesis of `planeDegree_eq_eval_of_restrict`. Depends on `cycle-class-sign-test-p2`, `p2-point-class-nonzero`. An independent recomputation of `[L₀] ∪ [L₁]` remains the only test of the multiplicativity sign at a = b = 1 that does not go through its proof; separating c₀ from c₁ needs the class of a line evaluated on a fundamental class of a line, or naturality of cycle classes under the coordinate swap of ℙ². Neither is proposed here.
