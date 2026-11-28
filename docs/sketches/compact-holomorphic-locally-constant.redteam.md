# Red team: `compact-holomorphic-locally-constant`

Date: 2026-11-28. Branch `track/compact-holomorphic-locally-constant` at `8b5915f`, one commit on `main` at `a509ee0`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4` (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain` identical to `main`). Target: `HodgeLadder/Compact/Holomorphic/Locally/Constant.lean`. Read: `python3 tools/next.py` for this rung and for `de-rham-functions-surjective-zero` (S2a); `docs/sketches/elliptic-curve-holomorphic-form.md` (S1, S2a rows, signs table); upstream `Definitions/AlgebraicGeometry/ComplexPoint/AnalyticSheaf.lean`, `Lemmas/AlgebraicGeometry/ComplexPoint/ProjectiveCompact.lean`, `Lemmas/AlgebraicGeometry/ComplexPoint/Manifold.lean` (`isManifold_omega`), `Other/AlgebraicGeometry/ComplexPoint/SmoothConnected.lean`, `Definitions/AlgebraicTopology/Sheaf/Constant.lean`; the port's `HolomorphicHodgeProjection.lean`, `HolomorphicZeroForms.lean`, `HolomorphicExponential.lean`; `HodgeLadder/Hodge/ZeroForms.lean`, `HodgeLadder/General/LocallyConstantSheaf.lean`; Mathlib `Geometry/Manifold/Complex.lean`; `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`, `ledger/ladder.json`. Probes P1 to P4 ran with `lake env lean` in a scratch directory of the worktree, since deleted.

**Verdict: pass with changes.** The statement is the literature's maximum principle on upstream's own sheaf, the defeq between a global section and a `C^ω` map on `⊤` is honest (P1), the ring map composes with the ladder's constant-sheaf isomorphism to give exactly the surjectivity S2a needs on global sections (P2), and no declaration is vacuous. The ℙ¹ test, however, cannot detect the one vacuity vector this rung has (an upstream 𝒪 with only locally constant sections); a nonconstant section on a chart of ℙ¹ closes that gap and compiles (P3). The other changes are placement (a general module and a separate test module, so that S2a does not import `Tests.ProjectiveLine`) and bookkeeping. No sign or scalar enters.

## Findings

1. **Statement against the literature (item 1).** `Voisin2002` (vol. I, the maximum principle for holomorphic functions on a compact complex manifold; locator unverified) and `GriffithsHarris1978` (ch. 0; locator unverified, outside the key's scope line): a holomorphic function on a compact complex manifold is locally constant, and constant on a connected one. Field by field:

   | Literature | Lean | Agrees |
   |---|---|---|
   | compact complex manifold M of dimension d | `ComplexPoint X` with upstream's charted space on `Fin d → ℂ` and `isManifold_omega` (`[SmoothOfRelativeDimension d X.hom]`), `[CompactSpace (ComplexPoint X)]`, or `[IsProjective X.hom]` through upstream's instance `complexPoint_compactSpace` (`ProjectiveCompact.lean:77`) | yes |
   | holomorphic function on M | a section over `⊤` of upstream's `holomorphicFunctionSheaf X d`, which is Mathlib's local-invariant-property sheaf for `contDiffWithinAt_localInvariantProp ω` in the model `𝓘(ℂ, Fin d → ℂ)`; complex `C^ω` is complex analytic | yes |
   | locally constant | `IsLocallyConstant` on `(⊤ : Opens (ComplexPoint X))`, the subtype of `univ` | yes |
   | constant when M is connected | `exists_eq_const_holomorphicFunctionSheaf_top` under `[PreconnectedSpace (ComplexPoint X)]` | yes; for an empty space the statement is the weaker literal one, harmless |

2. **The defeq claim (attack 1).** Honest. `(holomorphicFunctionSheafToTypes X d).presheaf.obj U` is Mathlib's subtype `{f : U → ℂ // ∀ x, LiftPropAt _ f x}`, and `C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯` is `{f // ContMDiff _ _ ω f}` with `ContMDiff` unfolding to the same pointwise `LiftPropAt`. Upstream's `CommRing` on `holomorphicFunctionSheafToTypes` is `inferInstanceAs` the `ContMDiffMap` ring, and `holomorphicFunctionPresheaf` restricts by `ContMDiffMap.restrictRingHom`, so ring operations and restriction agree by `rfl` (the candidate's `map_add' := rfl` relies on this). P1 checks by `rfl`: the value of `holomorphicTopSection X d s` at `z` is the underlying function of the Mathlib subtype; that underlying function satisfies `ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω` by `s.2`; restriction of `s` to any `V ≤ ⊤` evaluates as `s` at the same point. Nothing is coerced into a different object: `holomorphicTopSection` is the identity on terms.

3. **Fit with S2a (attack 2).** S2a's map is the port's `deRhamToHolomorphicFunctionCohomology X n` (`port/LefschetzPort/AlgebraicGeometry/HolomorphicHodgeProjection.lean:69`) under `[IsIntegral X.left] [Smooth X.hom]`; its 𝒪 is `holomorphicAdditiveSheaf X (dim X.left)` (`HolomorphicExponential.lean:51`), the `forget₂` image of `holomorphicFunctionSheaf X (dim X.left)`. Same sheaf, with `d := dim X.left`; the instance `SmoothOfRelativeDimension (dim X.left) X.hom` is found from `[IsIntegral X.left] [Smooth X.hom]`. The port's local topology instance `holomorphicExponentialTopology := Point.analyticTopology` unifies with the one in this file. P1 elaborates `Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0)` under `[CompactSpace (ComplexPoint X)]` and applies `isLocallyConstant_holomorphicFunctionSheaf_top X (dim X.left) s` to `s : (holomorphicAdditiveSheaf X (dim X.left)).obj.obj (op ⊤)` with no cast. P2 goes one step further: it defines the sheaf map `locallyConstantSheaf → holomorphicAdditiveSheaf X d` (a locally constant function is `C^ω`), proves `complexConstantsToHolomorphicSheaf X d = (constantSheafIsoLocallyConstantSheaf _ ℂ).hom ≫ that map` through `sheafifyLift_unique` and `toSheafify_constantSheafToLocallyConstantSheaf_hom`, and derives that `(complexConstantsToHolomorphicSheaf X d).hom.app (op ⊤)` is onto under compactness, with preimage `(constantSheafIsoLocallyConstantSheaf _ ℂ).inv.hom.app (op ⊤) (holomorphicTopToLocallyConstant X d s)`. That is the global-sections half of S2a; the remaining half (ℍ⁰ of a sheaf in degree 0 as its global sections, and the square `constantsToHolomorphicDeRhamComplex_comp_toFunctions`) is S2a's own work. Optional change O1 gives the text.

4. **Nonvacuity (attack 3, item 7b).** `projectiveLine_existsUnique_const` is genuine as far as it goes: existence of `c` comes from the maximum principle, and uniqueness uses a point of ℙ¹(ℂ) (from upstream's `ComplexPoint.connectedSpace`, since `ConnectedSpace` carries `Nonempty`), so `c ↦ const c` is a bijection `ℂ → Γ(ℙ¹(ℂ), 𝒪)`. It would pass unchanged if upstream's 𝒪 had only locally constant sections on every open (for instance a degenerate charted space), and then the whole rung would hold for a reason unrelated to compactness. The smallest test that fails in that case is a section of `holomorphicFunctionSheaf projectiveLine 1` on some open that takes two values. No such lemma exists in the ladder (S4 `elliptic-coordinate-functions` will give one on E, still open). P3 proves it for ℙ¹ on the chart domain of `chartAt (Fin 1 → ℂ) x₀`, with the section `z ↦ (chartAt _ x₀ z) 0` and two points whose chart values differ by ε/2; this also shows compactness is load-bearing, since the chart domain is a non-compact open. Required change 2 adds it.

5. **Trivial proofs fail (item 3).** Without `CompactSpace`, `simp` and `aesop` make no progress on `IsLocallyConstant (holomorphicTopSection X d s)` (P4), and finding 4 gives a nonconstant section on a non-compact open. Every hypothesis is used: `SmoothOfRelativeDimension` for the manifold, `CompactSpace` for the maximum principle, `PreconnectedSpace` for the constant form. No `ℕ∞` coercion (the order is `ω`, and `f.contMDiff.mdifferentiable (by simp)` discharges `ω ≠ 0`).

6. **Mathlib equivalents (attack 4).** Mathlib has `MDifferentiable.isLocallyConstant` and `MDifferentiable.exists_eq_const_of_compactSpace` (`Geometry/Manifold/Complex.lean:155,170`) for a manifold, nothing for upstream's sheaf, and no instance `CompactSpace (⊤ : Opens Y)` or `PreconnectedSpace (⊤ : Opens Y)`: `inferInstance` fails for both (P4), so `compactSpace_opens_top`, `preconnectedSpace_opens_top` are justified local helpers. `exists_eq_const_holomorphicFunctionSheaf_top` could call `exists_eq_const_of_compactSpace` directly (P4 compiles that form); cosmetic.

7. **Placement (attack 5).** `HodgeLadder/Compact/Holomorphic/Locally/Constant.lean` is `next.py`'s fallback path from the rung id and opens a new top-level directory `Compact/` for one file. The module also imports `HodgeLadder.Tests.ProjectiveLine` and upstream's `Other` library only for the test, so S2a (and every consumer of the general lemma) would pull in the port's projective-space stack and a `Tests` module. Precedent for the split: `elliptic-square-witness`, `elliptic-curve-points` name a `HodgeLadder.Tests.*` module in the ledger and list general declarations from `General/` modules it imports. The general half belongs next to `Hodge/ZeroForms.lean` (same sheaf, same consumer chain).

8. **Signs and conventions (item 6).** None. Local constancy and `∃! c` are insensitive to every sign and scalar. `holomorphicTopToLocallyConstant` is the identity on underlying functions, with no factor; the identification with `constantSheafIsoLocallyConstantSheaf` in P2 is `c ↦ const c` (`constantSheafIsoLocallyConstantSheaf_hom_app_toSheafify`), no sign. Relative dimension `d` against `dim X.left`: S1 is stated for any `d` and S2a instantiates `d := dim X.left` definitionally, so the `hX : dim X.left = 1` caution of the sketch's signs table applies to S3 and S6, not here. No row to add to `docs/conventions.md`.

9. **Equality first (item 7).** Not an identity or an inclusion between classes: a vanishing-of-variation statement and a bijection `ℂ → Γ(ℙ¹(ℂ), 𝒪)`, both exact. It is a step toward S2a (`de-rham-functions-surjective-zero`, open), then S6 and D5 (`F¹H¹_dR(E) ≠ ⊥`).

10. **Checker and axioms (item 5).** `python3 tools/check.py --no-build` exits with `ACCEPTED: all checks passed`; all twelve ledger declarations print `[Classical.choice, Quot.sound, propext]`, and each is the declaration the ledger note means.

11. **Pin drift (item 8).** Checked against the current pin; no drift.

12. **Ledger, roadmap, gaps text.** The note's "`Γ(ℙ¹(ℂ), 𝒪) ≅ ℂ`" is a bijection of sets in the Lean (`∃! c, s = projectiveLineConst c`); no ring isomorphism is stated. The gaps row's layer `6` matches `python3 tools/pinwalk.py` today and will change with the split. `depends_on: projective-line-witness` is right for the test and stays.

## Required changes

1. **Split the file.** Move every declaration outside `namespace Tests` to `HodgeLadder/Hodge/CompactHolomorphic.lean` (module `HodgeLadder.Hodge.CompactHolomorphic`), with imports `HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.AnalyticSheaf`, `HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact`, `Mathlib.Geometry.Manifold.Complex`, `Mathlib.Topology.LocallyConstant.Algebra` (drop `HodgeLadder.Tests.ProjectiveLine` and `Other.AlgebraicGeometry.ComplexPoint.SmoothConnected`). Move `Tests.projectiveLineConst`, `Tests.projectiveLine_existsUnique_const` and the lemma of change 2 to `HodgeLadder/Tests/CompactHolomorphicP1.lean` (module `HodgeLadder.Tests.CompactHolomorphicP1`), importing `HodgeLadder.Hodge.CompactHolomorphic`, `HodgeLadder.Tests.ProjectiveLine` and `Other.AlgebraicGeometry.ComplexPoint.SmoothConnected`. Root imports: both modules in `HodgeLadder.lean`, replacing `HodgeLadder.Compact.Holomorphic.Locally.Constant`; delete `HodgeLadder/Compact/`. Ledger `module`: `HodgeLadder.Tests.CompactHolomorphicP1` (it imports the general module, so the checker resolves every declaration). In S2a's brief and in the sketch, name `HodgeLadder.Hodge.CompactHolomorphic` as the import.

2. **Add the nonconstant-section test** to `HodgeLadder/Tests/CompactHolomorphicP1.lean` (inside `namespace HodgeLadder.Tests`), name `projectiveLine_exists_nonconstant_section`, add it to the ledger `declarations`. Text as compiled in P3, under `open CategoryTheory TopologicalSpace Topology AlgebraicGeometry ComplexPoint Opposite` and `open scoped ContDiff Manifold` (the candidate file opens all of these except `Opposite`; add it or write `Opposite.op`):

   ```lean
   /-- Upstream's 𝒪 on ℙ¹ has a nonconstant section on a chart domain: compactness is load-bearing. -/
   theorem projectiveLine_exists_nonconstant_section : ∃ (U : Opens (ComplexPoint projectiveLine))
       (s : (holomorphicFunctionSheaf projectiveLine 1).presheaf.obj (op U)) (a b : U),
       (show C^ω⟮𝓘(ℂ, Fin 1 → ℂ), U; ℂ⟯ from s) a ≠
         (show C^ω⟮𝓘(ℂ, Fin 1 → ℂ), U; ℂ⟯ from s) b := by
     have : QuasiSeparatedSpace projectiveLine.left :=
       quasiSeparatedSpace_of_quasiSeparated projectiveLine.hom
     have : ConnectedSpace (ComplexPoint projectiveLine) := ComplexPoint.connectedSpace _
     obtain ⟨x₀⟩ := (inferInstance : Nonempty (ComplexPoint projectiveLine))
     let e := chartAt (Fin 1 → ℂ) x₀
     let U : Opens (ComplexPoint projectiveLine) := ⟨e.source, e.open_source⟩
     have hf : ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω (fun z : U ↦ e z.1 0) := by
       have h1 : ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω (fun z : U ↦ e z.1) :=
         (contMDiffOn_chart (x := x₀)).comp_contMDiff contMDiff_subtype_val (fun z ↦ z.2)
       exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).contMDiff.comp h1
     let s : C^ω⟮𝓘(ℂ, Fin 1 → ℂ), U; ℂ⟯ := ⟨_, hf⟩
     have hy : e x₀ ∈ e.target := e.map_source (mem_chart_source _ x₀)
     obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target _ hy
     let y' : Fin 1 → ℂ := e x₀ + fun _ ↦ ((ε / 2 : ℝ) : ℂ)
     have hy' : y' ∈ e.target := hball (by
       rw [Metric.mem_ball, dist_eq_norm]
       simp only [y', add_sub_cancel_left, pi_norm_const, Complex.norm_real, Real.norm_eq_abs,
         abs_of_pos (half_pos hε)]
       linarith)
     refine ⟨U, s, ⟨x₀, mem_chart_source _ x₀⟩, ⟨e.symm y', e.map_target hy'⟩, ?_⟩
     change e x₀ 0 ≠ e (e.symm y') 0
     rw [e.right_inv hy']
     simp only [y', Pi.add_apply, ne_eq, left_eq_add, Complex.ofReal_eq_zero]
     exact (half_pos hε).ne'
   ```

   Docstring to use: "**Compactness is load-bearing.** Upstream's `holomorphicFunctionSheaf` on `ℙ¹` has a section taking two values on a chart domain, the first chart coordinate; so 𝒪 on ℙ¹ has sections that are not locally constant, and `projectiveLine_existsUnique_const` rests on the maximum principle."

3. **Ledger note**, replace the last two sentences with: "Nonvacuity: on ℙ¹, c ↦ the constant section c is a bijection ℂ → Γ(ℙ¹(ℂ), 𝒪) (projectiveLine_existsUnique_const; connectedness and a point from upstream's ComplexPoint.connectedSpace, library Other), and upstream's 𝒪 has a section with two values on a chart domain of ℙ¹ (projectiveLine_exists_nonconstant_section), so compactness is load-bearing. General lemmas in HodgeLadder.Hodge.CompactHolomorphic, the module S2a imports. No sign, no scalar. Red team pass with changes (docs/sketches/compact-holomorphic-locally-constant.redteam.md)." Make the same `≅` to bijection edit in the module docstring and in the docstring of `projectiveLine_existsUnique_const`.

4. **Roadmap row**: replace "`HodgeLadder.Compact.Holomorphic.Locally.Constant`" by "`HodgeLadder.Hodge.CompactHolomorphic`, test `HodgeLadder.Tests.CompactHolomorphicP1`", and "on ℙ¹ every global holomorphic function is exactly one constant" by "on ℙ¹ every global holomorphic function is exactly one constant, and a chart coordinate is a nonconstant section on a non-compact open".

5. **Gaps row** (category "Manifolds, charts and analytic functions"): module `HodgeLadder.Hodge.CompactHolomorphic`; layer the value `python3 tools/pinwalk.py` prints after the split (expect lower than 6, since the `Tests.ProjectiveLine` import goes); re-sort within the category by layer. Add to "Why local": "Mathlib has no `CompactSpace` or `PreconnectedSpace` instance for `⊤ : Opens Y` at the pin (red team probe)".

## Optional changes

O1. **Give S2a its first step here** (or leave it to S2a's prover): in `HodgeLadder/Hodge/CompactHolomorphic.lean`, importing `LefschetzPort.AlgebraicGeometry.HolomorphicZeroForms` and `HodgeLadder.General.LocallyConstantSheaf`, the text compiled in P2 under the same `open` lines as change 2, in a scratch namespace `RT` (names to adjust: `locallyConstantToHolomorphicSheaf`, `complexConstantsToHolomorphicSheaf_eq`, `exists_complexConstantsToHolomorphicSheaf_app_top_eq`):

   ```lean
   /-- locally constant functions as holomorphic functions -/
   noncomputable def lcToHol [SmoothOfRelativeDimension d X.hom] :
       HodgeLadder.locallyConstantSheaf (TopCat.of (ComplexPoint X)) ℂ ⟶ holomorphicAdditiveSheaf X d :=
     ⟨{ app U := AddCommGrpCat.ofHom
         { toFun f := show C^ω⟮𝓘(ℂ, Fin d → ℂ), U.unop; ℂ⟯ from
             ⟨(f : LocallyConstant U.unop ℂ), fun x ↦
               (contMDiffAt_const (c := (f : LocallyConstant U.unop ℂ) x)).congr_of_eventuallyEq
                 ((f : LocallyConstant U.unop ℂ).isLocallyConstant.eventually_eq x)⟩
           map_zero' := rfl
           map_add' _ _ := rfl }
        naturality _ _ _ := rfl }⟩
   
   set_option backward.isDefEq.respectTransparency false in
   theorem complexConstants_eq [SmoothOfRelativeDimension d X.hom] :
       complexConstantsToHolomorphicSheaf X d =
         (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).hom ≫ lcToHol X d := by
     apply Sheaf.hom_ext
     apply (sheafifyLift_unique _ _ _ _ _).symm
     rw [HodgeLadder.constantSheafIsoLocallyConstantSheaf_hom]
     change toSheafify _ _ ≫ (HodgeLadder.constantSheafToLocallyConstantSheaf _ ℂ).hom ≫
       (lcToHol X d).hom = _
     erw [← Category.assoc, HodgeLadder.toSheafify_constantSheafToLocallyConstantSheaf_hom]
     rfl

   theorem lift [SmoothOfRelativeDimension d X.hom] [CompactSpace (ComplexPoint X)]
       (s : (holomorphicAdditiveSheaf X d).obj.obj (op ⊤)) :
       ∃ t, (complexConstantsToHolomorphicSheaf X d).hom.app (op ⊤) t = s := by
     refine ⟨(HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).inv.hom.app (op ⊤)
       (HodgeLadder.holomorphicTopToLocallyConstant X d s), ?_⟩
     rw [complexConstants_eq]
     change ((HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).inv ≫
       (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).hom ≫ lcToHol X d).hom.app (op ⊤) _ = s
     rw [show (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).inv ≫
       (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).hom ≫ lcToHol X d = lcToHol X d from
         Iso.inv_hom_id_assoc _ _]
     rfl
   ```

   If O1 lands in this rung, the module's import layer rises to the port's; then keep it in a second file `HodgeLadder/Hodge/CompactHolomorphicConstants.lean` so the plain lemma stays light.

O2. `exists_eq_const_holomorphicFunctionSheaf_top` can call Mathlib's `MDifferentiable.exists_eq_const_of_compactSpace` directly (P4).

## Attempts recorded

- P1 (defeq, S2a types): all `rfl` checks and the S2a elaboration succeed.
- P2 (lift through the constant sheaf): first attempt failed on `Sheaf.comp_hom` (no such name at the pin) and on a `rw` blocked by `TopCat.Sheaf` against `Sheaf` spelling; `change` to the presheaf composite and `erw [← Category.assoc, toSheafify_constantSheafToLocallyConstantSheaf_hom]` closed it, then `Iso.inv_hom_id_assoc` through `rw [show …]`.
- P3 (nonconstant section): first attempt failed for want of `Nonempty (ComplexPoint projectiveLine)`; the candidate's test gets it from `ConnectedSpace`, and the same two `have`s fix the probe.
- P4: `inferInstance` for `CompactSpace (⊤ : Opens Y)`, `PreconnectedSpace (⊤ : Opens Y)` fails; `simp`, `aesop` fail on the conclusion without compactness; the Mathlib constant form compiles.
