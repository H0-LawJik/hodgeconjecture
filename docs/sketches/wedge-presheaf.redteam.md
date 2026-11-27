# Red team: `wedge-presheaf` (statement and proof)

Date: 2026-11-27. Worktree `wedge-presheaf` at base `146af90`, uncommitted `HodgeLadder/Hodge/WedgePresheaf.lean` and the section "wedge-presheaf: statement" of `docs/sketches/cup-hodge-filtration.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`, the same in `lakefile.toml`, `lake-manifest.json`, the package checkout and `main`.

Read: the ledger entries `wedge-descends`, `wedge-presheaf`, `wedge-sheafify`, `wedge-sheaf-map`, `cup-hodge-filtration`; the module; `HodgeLadder/Hodge/WedgeDescends.lean`, `CupFiltration.lean` (`formWedge`, `formWedge_differential`), `ZeroForms.lean`; the sketch and `docs/sketches/cup-hodge-filtration.redteam.md` (findings 8 and 9); upstream `Definitions/AlgebraicGeometry/Hodge/AnalyticDifferentialForms.lean` (`chartEvaluationKernel`, `formRestriction`, `HolomorphicForm`, `holomorphicFormOfConstant`, `holomorphicFormDifferential`, `holomorphicFormRestriction`), `Definitions/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean` (`holomorphicDeRhamPresheaf`, `holomorphicDeRhamPresheafComplex`), `Lemmas/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean` (`scalarHolomorphicDeRhamPresheaf`), `Definitions/Algebra/DeRham/Basic.lean` (`extDeriv_mul`, `differential_mk`, `extAlgMap`, `map`, `ofConstant`); Mathlib `Algebra/Module/Rat.lean`; `docs/conventions.md`.

Scratch (inside the worktree, deleted afterwards; about 7 s each with `lake env lean`): RT1 prints axioms, tries trivial proofs, derives the bilinear-map form of naturality, and proves five cast lemmas; RT2 proves nonvacuity in general and on ℙ¹; RT3 proves that the degree-zero wedge is multiplication of functions; RT4 probes the `ℚ`-module structure that `wedge-sheafify` needs.

**Verdict: pass with changes.** Every target is the literature's object with the literature's sign, every proof uses the three standard axioms, and nothing is vacuous: on a nonempty open the wedge `[1] ∧ [1]` is nonzero (RT2). Changes 1 to 4 below are required before the rung is posted; 5 to 7 are recommended for the consumers.

## 1. Is this the statement the literature makes?

Source: [`Voisin2002`] I, holomorphic forms on a complex manifold, the wedge product `Ω^p ⊗ Ω^q → Ω^{p+q}` and the Leibniz rule for `∂` on holomorphic forms (section numbers unverified); [`GriffithsHarris1978`] Ch. 0 carries the same rules for forms (page unverified). In both, the wedge is `𝒪`-bilinear, natural under restriction to smaller opens, associative and graded commutative, with unit the constant function 1, and `d(α ∧ β) = dα ∧ β + (−1)^{deg α} α ∧ dβ`.

| Literature | Lean | Check |
|---|---|---|
| holomorphic `p`-forms on `U` | upstream `HolomorphicForm X d U p = Form ℂ 𝒪(U) p ⧸ chartEvaluationKernel X d U p` | upstream's object of record; its sheafification is upstream's `Ω^p` |
| `α ∧ β` | `holomorphicWedge X d U p q`, `LinearMap.liftQ₂` of `mkQ ∘ formWedge` | on representatives the product `θ · η` in `⋀_{𝒪(U)} Ω_{𝒪(U)/ℂ}`, first factor on the left (`holomorphicWedge_mk`, `rfl`); well defined by both sides of the checked `wedgeDescends` |
| bilinear over `𝒪(U)` | bilinear over `ℂ` | weaker in type, the same function. `𝒪(U)`-linearity holds on representatives: `formWedge (f • θ) η = f • formWedge θ η` by `Subtype.ext (by simp)` (RT3). Upstream gives `HolomorphicForm` no `𝒪(U)`-module structure, and no consumer needs one (finding 2) |
| restriction `ρ_{UV}(α ∧ β) = ρ α ∧ ρ β` | `holomorphicFormRestriction_holomorphicWedge` | exact, no sign; from `map_formWedge`, which is `map_mul` of upstream's `extAlgMap` (the map `formRestriction` is `Algebra.DeRham.map` along `holomorphicRestrictionAlgHom`) |
| `d(α ∧ β) = dα ∧ β + (−1)^p α ∧ dβ` | `holomorphicFormDifferential_holomorphicWedge` | exact, sign `(−1 : ℤ)^p` with `p` the degree of the first factor, as in `formWedge_differential` and upstream's `extDeriv_mul` (`d(xy) = involute x · dy + dx · y`, with `d` placed on the left by `differential_mk`). The degree transport on `dα ∧ β` is the identity of the exterior algebra (finding 4) |
| unit: `1 ∧ ω = ω = ω ∧ 1` | `holomorphicWedge_ofConstant_left`, `_right` for any constant `c` | `[c] ∧ b = cast (c • b)`, `a ∧ [c] = c • a`; exact |
| associativity, graded commutativity | absent | not claimed by this rung; graded commutativity is not at the pin for `⋀^p · ⋀^q` (red team `cup-hodge-filtration`, finding 8). Associativity is `mul_assoc` on representatives if a consumer needs it |

Field by field, every argument of every statement is upstream's: `X : Over (Spec ↧ℂ)`, `d`, `[SmoothOfRelativeDimension d X.hom]`, opens as objects of `(Opens (TopCat.of (ComplexPoint X)))ᵒᵖ`, morphisms `i : U ⟶ V`, and upstream's restriction and differential at the same degrees `p`, `q`, `p + q`, `p + q + 1`. Nothing is restated.

## 2. Can the hypotheses be satisfied?

Yes. The only hypotheses are upstream's. Upstream's ℙⁿ carries `SmoothOfRelativeDimension n (projectiveSpace n).hom` (`HodgeLadder.Tests.smoothOfRelativeDimension_projectiveSpace`), and the chart `HodgeLadder.Normalization.projectiveChart` gives a complex point. RT2, standard axioms, importing `HodgeLadder.Hodge.WedgePresheaf` and `HodgeLadder.Tests.ProjectiveChart`:

```lean
open HodgeLadder.Tests HodgeLadder.Normalization in
example : ∃ (U : (Opens (TopCat.of (ComplexPoint (projectiveSpace 1))))ᵒᵖ),
    holomorphicWedge (projectiveSpace 1) 1 U 0 0 (holomorphicFormOfConstant _ 1 U 1)
      (holomorphicFormOfConstant _ 1 U 1) ≠ 0 := by
  refine ⟨Opposite.op ⊤, ?_⟩
  have : Nonempty (ComplexPoint (projectiveSpace 1)) := ⟨(projectiveChart 1 0).symm 0⟩
  have : Nonempty (Opposite.unop
      (Opposite.op (⊤ : Opens (TopCat.of (ComplexPoint (projectiveSpace 1)))))) :=
    ⟨⟨(projectiveChart 1 0).symm 0, trivial⟩⟩
  exact rt_wedge_ne_zero _
```

with `rt_wedge_ne_zero` the general lemma of change 3.

## 3. Is any conclusion trivially true?

No. If every `HolomorphicForm X d U p` were a subsingleton, all five identities would hold for no reason. They are not: change 3 proves `[1] ∧ [1] ≠ 0` on every nonempty open, through upstream's chart evaluation of the constant `1`, which is `1 ≠ 0` (the argument of upstream's private `holomorphicFormOfConstant_injective`). RT3 shows the degree-zero wedge is the product of functions:

```lean
example (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (f g : OpenHolomorphicFunctions X d U) :
    holomorphicWedge X d U 0 0
        (Submodule.Quotient.mk (Algebra.DeRham.ofFunction ℂ _ f))
        (Submodule.Quotient.mk (Algebra.DeRham.ofFunction ℂ _ g)) =
      Submodule.Quotient.mk (Algebra.DeRham.ofFunction ℂ _ (f * g)) := by
  rw [holomorphicWedge_mk]
  congr 1
  refine Subtype.ext ?_
  simp [Algebra.DeRham.ofFunction_apply, Algebra.DeRham.mk]
  rw [smul_smul, mul_comm]
```

so the wedge is pinned beyond the constants, against `HodgeLadder.holomorphicZeroFormToFunction_bijective` (`HodgeLadder/Hodge/ZeroForms.lean`, rung `chern-classes-are-hodge`).

Attempts at short proofs: `simp` on naturality makes no progress (RT1); the prover reports `rfl` rejected on naturality and `simp` rejected on the Leibniz rule. The hypotheses `i`, `a`, `b` are all used. No `ℕ∞` coercion and no empty index type enters. The definitional facts that are used (`holomorphicWedge_mk`, `holomorphicFormDifferential_mk`, `holomorphicFormCast_rfl` by `rfl`) are the intended computation rules of `liftQ₂`, `liftQ` and `▸`.

## 4. Interface rung?

No. This is a foundation rung with definitions and theorems; there is no structure and no assumed axiom.

## 5. Axioms and declarations

RT1, `#print axioms`: `formWedgeBilin`, `formWedgeBilin_apply`, `coe_formWedge`, `map_formWedge`, `holomorphicWedge`, `holomorphicWedge_mk`, `holomorphicFormRestriction_holomorphicWedge`, `holomorphicFormCast`, `holomorphicFormCast_rfl`, `holomorphicFormCast_mk`, `holomorphicFormDifferential_mk`, `holomorphicFormDifferential_formWedge_mk`, `holomorphicFormDifferential_holomorphicWedge`, `holomorphicWedge_ofConstant_left`, `holomorphicWedge_ofConstant_right` all depend on `[propext, Classical.choice, Quot.sound]`. `python3 tools/check.py --no-build` exits 0 on the worktree, but it does not see this module yet: the module is not imported from `HodgeLadder.lean` and the ledger entry has `module: null`, `declarations: []` (change 1). The declarations named in the brief are the ones in the file; there is no shadowing of upstream names (`holomorphicFormDifferential_mk` does not exist upstream at the pin; grep).

## 6. Conventions

| Convention | Where | Matches register? | Truth depends on it? |
|---|---|---|---|
| order of factors: first factor on the left in `⋀ Ω` | `formWedge`, `holomorphicWedge` | yes, row "Wedge product of algebraic forms" | yes, for every identity downstream (`deRhamCup` order); the row "de Rham cup order (proposed)" reverses the factors on the sheaf side with no sign |
| Leibniz sign `(−1)^p`, `p` the degree of the first factor | `holomorphicFormDifferential_holomorphicWedge` | yes, same row; and Mathlib's `ε₂(p, q) = (−1)^p` of row "Tensor product of ℤ-indexed cochain complexes" | yes: it is what makes `deRhamWedge` a chain map with no twist. Downstream the sign arrives as `(p : ℤ).negOnePow : ℤˣ` acting by `Units.smul`; converting needs `Int.coe_negOnePow_natCast` (or `Int.negOnePow_def`) and a `Nat.cast`. Same value, different spelling |
| degree transport `holomorphicFormCast` | this file | new row added | no sign: `holomorphicFormCast_mk` says the underlying element of the exterior algebra is unchanged |
| unit: constant `c` acts by `c •` on both sides, through `algebraMap ℂ 𝒪(U)` | `holomorphicWedge_ofConstant_left/right`, upstream `ofConstant` | new row added | yes, for `μ ∘ (u ⊗ 𝟙) = λ` in `wedge-sheaf-map`; no scalar, no Tate twist |
| scalars: `ℂ`-bilinear | this file | new row added | no for membership; T1 uses complex bilinearity, compatible with upstream's `scalarHolomorphicDeRhamPresheaf` (`c • LinearMap.id`) by `map_smul` in either argument |

The cited input `wedgeDescends` is a membership statement and is insensitive to sign. The cited input `formWedge_differential` is an identity, and its sign is the one used here; the Leibniz rule here is its image under `mkQ` plus a transport, with nothing added.

## 7. Equality first

Naturality, Leibniz and both unit laws are exact identities. None is up to a scalar; the Leibniz sign is in the docstring. Change 4 asks that the docstring also cite the register row by name, as `docs/conventions.md` "Rules" requires.

## 7b. Non-vacuity

Smallest test that fails if the rung were trivially true: `holomorphicWedge X d U 0 0 (holomorphicFormOfConstant X d U 1) (holomorphicFormOfConstant X d U 1) ≠ 0` for `[Nonempty U.unop]`, using upstream's `holomorphicFormOfConstant`, `chartEvaluationKernel`, `mem_chartEvaluationKernel_iff`, `chartSectionDomain`, `chartEvaluation_ofConstant` (upstream `Lemmas/AlgebraicGeometry/Hodge/HolomorphicPoincare.lean`). It does not exist in the module; RT2 proves it (change 3). The degree-zero multiplication of section 3 is the next test (change 7). A test of the Leibniz sign needs a nonzero 1-form, for example `dz` on an affine chart of ℙ¹; that is heavier and is recorded as a known weakness: the sign is pinned only through `formWedge_differential`, which is checked.

## 8. Pin drift

None. The rung was written and checked at `2ead713`, the current pin, and `main` pins the same commit. The upstream definitions this rung unfolds are `HolomorphicForm`, `chartEvaluationKernel`, `formRestriction`, `holomorphicFormRestriction`, `holomorphicFormDifferential`, `holomorphicFormOfConstant`, `Algebra.DeRham.map`, `extAlgMap`, `ofConstant`, `ofFunction`; on the next bump, diff these. A change of `HolomorphicForm` away from a quotient by a `ℂ`-submodule would break `liftQ₂` at build time, and a change of `holomorphicFormRestriction` or `holomorphicFormDifferential` away from `liftQ` would break the `rfl` lemmas `holomorphicWedge_mk` and `holomorphicFormDifferential_mk`. Both fail loudly.

## Findings

1. **Statement is right.** The wedge, its naturality, the Leibniz rule and the unit laws are the literature's, for upstream's holomorphic forms, exact and with the registered sign.

2. **`ℂ`-bilinearity is enough for every consumer.** `wedge-sheafify` works in `ShQ = Sheaf J (ModuleCat ℚ)`, whose tensor is over `ℚ`, and T1 needs `ℂ`-bilinearity of `deRhamCup`. An `𝒪(U)`-linear version would be needed only for a tensor over `𝒪_X`, which the route does not use. One gap for the consumer: `HolomorphicForm X d U p` has no `Module ℚ` instance at the pin (RT4: `#synth Module ℚ (HolomorphicForm X d U p)` fails). `rational-de-rham-complex` must supply one; Mathlib's `subsingleton_rat_module` makes any choice unique, and `map_rat_smul` (or `AddMonoidHom.toRatLinearMap`) makes the biadditive `holomorphicWedge` `ℚ`-bilinear for it. Record this in the brief of `wedge-sheafify`, not here.

3. **Prover's question 1 (pointwise or bilinear-map naturality).** The pointwise statement is the right primary form; the bilinear-map equation follows in one line (RT1):

   ```lean
   (holomorphicWedge X d U p q).compr₂ (holomorphicFormRestriction X d i (p + q)) =
     (holomorphicWedge X d V p q).compl₁₂ (holomorphicFormRestriction X d i p)
       (holomorphicFormRestriction X d i q) :=
     LinearMap.ext₂ fun a b => holomorphicFormRestriction_holomorphicWedge i a b
   ```

   The presheaf tensor in `wedge-sheafify` is checked on pure tensors (`TensorProduct.ext'`), which reduces to the pointwise form, so either works. Adding the line as a named lemma is change 5.

4. **Prover's question 2 (transport).** The cast is honest: `holomorphicFormCast_mk` shows the element of `⋀ Ω` is kept, with no reindexing sign. Keep `h ▸ LinearMap.id`. A `Submodule.mapQ` of `LinearEquiv.ofEq` would need the equality `⋀^m = ⋀^n` of submodules and a kernel comparison, both proved by `subst h` anyway, and it gives the same map. With `▸`, every lemma a consumer needs is `subst h; rfl` (RT1, all five elaborate), including agreement with `HomologicalComplex.XIsoOfEq` on upstream's presheaf complex, which is what the chain-map check of `wedge-sheaf-map` will meet. Change 6 lists them.

5. **Prover's question 3 (unit laws).** In scope. They are sectionwise statements about this file's wedge, they are the input to `μ ∘ (u ⊗ 𝟙) = λ` in `wedge-sheaf-map`, and the right unit law is what makes the nonvacuity test three lines.

6. **Sketch inaccuracy.** The sketch says "The ledger lists `HodgeLadder/Wedge/Presheaf.lean`". It does not: the ledger entry has `module: null`, and no file in the tree names that path. `HodgeLadder/Hodge/WedgePresheaf.lean` sits beside `WedgeDescends.lean` and `CupFiltration.lean` and is the right place.

## Changes

Required:

1. Import the module from `HodgeLadder.lean` (`public import HodgeLadder.Hodge.WedgePresheaf`) and fill the ledger entry: `status: checked`, `module: HodgeLadder.Hodge.WedgePresheaf`, `declarations` listing at least `HodgeLadder.holomorphicWedge`, `HodgeLadder.holomorphicWedge_mk`, `HodgeLadder.holomorphicFormRestriction_holomorphicWedge`, `HodgeLadder.holomorphicFormCast`, `HodgeLadder.holomorphicFormCast_mk`, `HodgeLadder.holomorphicFormDifferential_holomorphicWedge`, `HodgeLadder.holomorphicWedge_ofConstant_left`, `HodgeLadder.holomorphicWedge_ofConstant_right`, `HodgeLadder.map_formWedge`, `HodgeLadder.formWedgeBilin`, and the test of change 3; then rerun `python3 tools/check.py`.
2. Replace the sentence "The ledger lists `HodgeLadder/Wedge/Presheaf.lean`; the module path is to be settled at the red team." in the sketch with "The module path is `HodgeLadder/Hodge/WedgePresheaf.lean` (red team 2026-11-27)."
3. Add the nonvacuity test (RT2, standard axioms, no extra imports beyond the module's):

   ```lean
   /-- **Nonvacuity.** On a nonempty open, the wedge of the constant zero-form `1` with itself is
   not zero: through the right unit law it is `[1]`, whose chart evaluation at any point is `1`. -/
   theorem holomorphicWedge_ofConstant_one_ne_zero (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
       [Nonempty U.unop] :
       holomorphicWedge X d U 0 0 (holomorphicFormOfConstant X d U 1)
         (holomorphicFormOfConstant X d U 1) ≠ 0 := by
     rw [holomorphicWedge_ofConstant_right, one_smul]
     intro hzero
     let a : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) 0 :=
       Algebra.DeRham.ofConstant ℂ (OpenHolomorphicFunctions X d U) 1
     have ha : a ∈ chartEvaluationKernel X d U 0 := by
       change Submodule.Quotient.mk a = 0 at hzero
       rwa [Submodule.Quotient.mk_eq_zero] at hzero
     let x : U.unop := Classical.arbitrary U.unop
     let e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x.1
     have hxsource : x.1 ∈ e.source := mem_extChartAt_source x.1
     have hxe : e x.1 ∈ chartSectionDomain X d U x.1 := by
       refine ⟨mem_extChartAt_target x.1, ?_⟩
       change e.symm (e x.1) ∈ U.unop
       rw [e.left_inv hxsource]
       exact x.2
     have heval := (mem_chartEvaluationKernel_iff X d U 0 a).1 ha x.1 (e x.1) hxe
     rw [chartEvaluation_ofConstant X d U x.1 1 hxe] at heval
     have hcoeff := congrArg (fun f : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ ↦ f Fin.elim0) heval
     simp at hcoeff
   ```

4. In the docstring of `holomorphicFormDifferential_holomorphicWedge`, cite the register: append "Conventions row 'Wedge product of algebraic forms'; the degree transport is row 'Wedge product of holomorphic forms', with no sign."

Recommended:

5. Add the bilinear-map form of naturality from finding 3 as `holomorphicWedge_compr₂_restriction`.
6. Add the cast lemmas, each `by subst h; rfl` (and `subst h h'; rfl` for the first), all elaborated in RT1:

   ```lean
   lemma holomorphicFormCast_trans (U) {m n k : ℕ} (h : m = n) (h' : n = k)
       (a : HolomorphicForm X d U m) :
       holomorphicFormCast X d U h' (holomorphicFormCast X d U h a) =
         holomorphicFormCast X d U (h.trans h') a
   lemma holomorphicFormRestriction_holomorphicFormCast {U V} (i : U ⟶ V) {m n : ℕ} (h : m = n)
       (a : HolomorphicForm X d U m) :
       holomorphicFormRestriction X d i n (holomorphicFormCast X d U h a) =
         holomorphicFormCast X d V h (holomorphicFormRestriction X d i m a)
   lemma holomorphicFormDifferential_holomorphicFormCast (U) {m n : ℕ} (h : m = n)
       (a : HolomorphicForm X d U m) :
       holomorphicFormDifferential X d U n (holomorphicFormCast X d U h a) =
         holomorphicFormCast X d U (congrArg (· + 1) h) (holomorphicFormDifferential X d U m a)
   lemma XIsoOfEq_hom_app_eq_holomorphicFormCast (U) {m n : ℕ} (h : m = n)
       (a : HolomorphicForm X d U m) :
       ((holomorphicDeRhamPresheafComplex X d).XIsoOfEq h).hom.app U a =
         holomorphicFormCast X d U h a
   ```

   (`U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ` in each.) The fifth, agreement with `eqToHom (congrArg (fun k => (holomorphicDeRhamPresheaf X d k).obj U) h)`, also holds by `subst h; rfl`.
7. Add the degree-zero test of section 3 as `holomorphicWedge_ofFunction`, the pin of the wedge beyond constants.

## What was tried and failed

- `simp` on `holomorphicFormRestriction_holomorphicWedge`: no progress (RT1).
- `#synth Module ℚ (HolomorphicForm X d U p)`: fails at the pin (RT4), finding 2. `Module.compHom` cannot be a local instance (its ring map is explicit).
- A Lean test of the Leibniz sign: not attempted past the design stage; it needs a nonzero 1-form, and none is constructed at the pin outside the chart evaluations.
