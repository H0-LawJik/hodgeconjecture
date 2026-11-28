# Red team: `de-rham-scalar-sheaf` (statement and proof)

Date: 2026-11-27. Worktree `de-rham-scalar-sheaf`, base `9a9b9cb`; uncommitted `HodgeLadder/De/Rham/Scalar/Sheaf.lean` (module `HodgeLadder.De.Rham.Scalar.Sheaf`, 40 declarations; the count of 41 in the brief includes a docstring match). Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Module build: 33 s (`lake build HodgeLadder.De.Rham.Scalar.Sheaf`).

Read: the ledger entries `de-rham-scalar-sheaf`, `wedge-sheaf-map`, `de-rham-cup`, `de-rham-cup-exact`; the module; `HodgeLadder/Hodge/{WedgeSheafMap,WedgeSheafify,PairingProduct,RationalDeRhamComplex,RationalHypercohomology}.lean`, `HodgeLadder/Tests/ComplexPointNonempty.lean`; `docs/sketches/wedge-sheaf-map.redteam.md` (finding 8), `docs/sketches/cup-hodge-filtration.md` (construction steps 5 and 6); `docs/conventions.md`, `docs/gaps.md`, `docs/references.md`; upstream `Lemmas/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean` (`scalarHolomorphicDeRhamPresheaf`, `scalarHolomorphicDeRhamComplex`, `scalarHolomorphicDeRhamComplexInt`, `_zero`, `_one`, `_add`, `_mul`) and `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` (the `SMul ℂ H_dR^n(X)` instance, `deRham_complex_smul_eq`, `deRhamHypercohomologyComplexModule`).

Scratch (`HodgeLadder/RTProbe/*.lean` in the worktree, run with `lake env lean` against the fresh olean, deleted afterwards): RT_Ax prints axioms for all 40 declarations; RT2 proves that the forget square determines `S_c`; RT3 proves the bridge from `S_c` to upstream's `c •` on `H_dR^n(X)`; RT4 plugs both scalar laws into `pairProductShQ_naturality` as `hm`; RT5 proves that the first-factor scalar law holds for exactly one target scalar.

**Verdict: pass with changes.** No sign enters and none is forced: `S_c` has degree zero, the scalar laws carry no `(−1)^p`, and nothing comes out `−1` unexpectedly (`S_{−1} = −𝟙` is the expected value and is separated from `𝟙`). `S_c` is upstream's scalar exactly (forget square, `rfl` at presheaf level), the forget square determines it uniquely (RT2), and the scalar laws fit `pairProductShQ_naturality` with no conversion (RT4). The changes: the docstring's claim that `S_c` induces `c •` on `H_dR` has no Lean statement, and a 12-line proof exists (RT3); the uniqueness pin and a nonvacuity test for the scalar laws should enter the module (RT2, RT5); the file belongs under `HodgeLadder/Hodge/`; bookkeeping in the ledger, `docs/conventions.md` and `docs/gaps.md`.

## 1. Is this the statement the literature makes?

Source: the holomorphic de Rham complex is a complex of sheaves of `ℂ`-vector spaces whose differential and wedge product are `ℂ`-linear and `ℂ`-bilinear, and the complex structure on `H^n_dR(X) = ℍ^n(X, Ω•)` is induced by multiplication by `c` on forms ([`Voisin2002`] I, holomorphic de Rham complex; section unverified). At the pin the statement of record is upstream's: `c • α = hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c) n α` by `rfl` (`deRham_complex_smul_eq`), and `deRhamHypercohomologyComplexModule` is built from that action.

| Literature / upstream | Lean | Check |
|---|---|---|
| multiplication by `c` on `p`-forms, `θ ↦ c • θ` | `rationalScalarPresheaf X d p c`, app `U` = `(c • LinearMap.id).restrictScalars ℚ` on `HolomorphicForm X d U p` | forgetting `ℚ` gives upstream's `scalarHolomorphicDeRhamPresheaf X d p c` by `rfl` (`whiskerRight_rationalScalarPresheaf`); the same `Module ℂ` instance on `HolomorphicForm`, so no conjugation can enter on one side only |
| `c` commutes with `d` | `rationalScalarPresheaf_comp_differential`, `rationalScalarSheaf_comp_differential` | from `map_smul` of upstream's `holomorphicFormDifferential` |
| the sheafified scalar | `rationalScalarSheaf X d p c := (Cup.sheafifyQ _).map (rationalScalarPresheaf X d p c)` | matches the ledger title `sheafifyQ.map (c • ·)`; square `toSheafify_comp_rationalScalarSheaf` is Mathlib's `toSheafify_naturality` |
| `S_c` on `Ω•` | `rationalDeRhamScalar X c := extendMap (rationalScalarComplexNat X (dim X.left) c) embeddingUpNat` | the same shape as upstream's `scalarHolomorphicDeRhamComplexInt X c := extendMap (scalarHolomorphicDeRhamComplex X (dim X.left) c) embeddingUpNat` |
| `c` on `Ω•(X)` is upstream's | `forget_rationalDeRhamScalar : forget(S_c) ≫ e.hom = e.hom ≫ scalarHolomorphicDeRhamComplexInt X c`, `e = forgetRationalDeRhamIso X` | exact square, no scalar, no sign; matches the ledger title |
| `(c a) ∧ b = c (a ∧ b)` | `rationalDeRhamScalar_tensorHom_id_comp_deRhamWedge : tensorHomShQ S_c (𝟙 Ω) ≫ deRhamWedge X = deRhamWedge X ≫ S_c` | matches the ledger title; degreewise `LinearMap.map_smul₂` of `holomorphicWedge` |
| `a ∧ (c b) = c (a ∧ b)` | `rationalDeRhamScalar_id_tensorHom_comp_deRhamWedge : tensorHomShQ (𝟙 Ω) S_c ≫ deRhamWedge X = deRhamWedge X ≫ S_c` | matches the ledger title; degreewise `map_smul` of `holomorphicWedge X d U p q a` |
| `(ab) • x = a • (b • x)`, `1 • x = x`, `0 • x = 0`, `(a + b) • x = a • x + b • x` | `rationalDeRhamScalar_mul : S_{ab} = S_b ≫ S_a`, `_one`, `_zero`, `_add`, `_neg_one : S_{−1} = −𝟙` | `_mul` is in diagrammatic order, `S_b` first: the order of upstream's `scalarHolomorphicDeRhamComplexInt_mul`, and the left-action law `a • (b • x)` |

Every object is upstream's or a checked local one; nothing upstream states is restated. The rung adds structure (`S_c`) and identities about it, as the ledger asks.

## 2. Can the hypotheses be satisfied?

Yes. The hypotheses are `[IsIntegral X.left] [Smooth X.hom]` (complex level) and `[SmoothOfRelativeDimension d X.hom]` (degreewise); both hold for `HodgeLadder.Tests.point` (`Spec ℂ`). The tests `rationalDeRhamScalar_neg_one_ne_id`, `rationalDeRhamScalar_ne_zero`, `rationalDeRhamScalar_injective` hold on every smooth integral `X`, with no `Nonempty (ComplexPoint X)` hypothesis, through `Tests.rationalDeRhamUnit_ne_zero'` and `Tests.rationalDeRhamUnit_ne_neg'` (rung `complex-point-nonempty`). The generic lemmas take a chain endomorphism `s` with a hypothesis `hs`, discharged at `Ω•_ℚ` by the sheaf-level scalar laws, not assumed.

## 3. Is any conclusion trivially true?

No. What I tried:

- **Is the forget square satisfiable by any map, for example `0`?** No. RT2 proves in 5 s that the square determines `S_c`:

  ```lean
  theorem eq_rationalDeRhamScalar_of_forget (c : ℂ)
      (φ : rationalDeRhamComplex X ⟶ rationalDeRhamComplex X)
      (h : (forgetComplex X).map φ ≫ (forgetRationalDeRhamIso X).hom =
        (forgetRationalDeRhamIso X).hom ≫ scalarHolomorphicDeRhamComplexInt X c) :
      φ = rationalDeRhamScalar X c := by
    have h2 : (forgetComplex X).map φ = (forgetComplex X).map (rationalDeRhamScalar X c) := by
      rw [← cancel_mono (forgetRationalDeRhamIso X).hom, h, forget_rationalDeRhamScalar X c]
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    exact (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).map_injective
      (congrArg (fun f => HomologicalComplex.Hom.f f n) h2)
  ```

  (`Cup.forgetSheaf` is `Faithful` by instance search; `(forgetComplex X).Faithful` is not found by instance search, even with `rdrForgetAdditive` active, so the proof goes degreewise.) With `rationalDeRhamScalar_ne_zero`, `0` satisfies the square only at `c = 0`. The square therefore pins `S_c` completely, which is stronger than the presheaf-level sheafification square: that square also determines `rationalScalarSheaf` (Mathlib's `sheafify_hom_ext`), but says nothing by itself about upstream.
- **Could `S_c` be a rational scalar or trivial?** No: `rationalDeRhamScalar_injective` separates every two complex numbers, and `S_{−1} ≠ 𝟙`.
- **Are the scalar laws true for any target?** No. RT5 proves in 14 s that the first-factor law holds for exactly one target scalar:

  ```lean
  theorem eq_of_tensorHom_id_comp_deRhamWedge (c c' : ℂ)
      (h : tensorHomShQ (rationalDeRhamScalar X c) (𝟙 (rationalDeRhamComplex X)) ≫
          deRhamWedge X = deRhamWedge X ≫ rationalDeRhamScalar X c') : c = c' := by
    have e : shQLeftUnitor (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X) ≫
          rationalDeRhamScalar X c =
        shQLeftUnitor (TopCat.of (ComplexPoint X)) (rationalDeRhamComplex X) ≫
          rationalDeRhamScalar X c' := by
      rw [← deRhamWedge_unit X, Category.assoc, Category.assoc,
        ← rationalDeRhamScalar_tensorHom_id_comp_deRhamWedge X c, h]
    apply rationalDeRhamScalar_injective X
    rw [shQLeftUnitor_eq] at e
    exact (Iso.cancel_iso_hom_left _ _ _).1 e
  ```

  So the law with `S_{conj c}` or `S_{−c}` on the right is false for every `c` off the real line (respectively every `c ≠ 0`), on every smooth integral `X`. It would also fail if `deRhamWedge` or `S_c` were trivial. The proof uses the unit law and the candidate's law, so it is a consistency test of the pair, and it is the smallest test that makes the scalar law visible.
- **Unused hypotheses, empty index types, `True`-valued definitions.** None. `hs` is used in both generic proofs (`reassoc_of% (hs p q)`); the index types are `ℕ` and `ℤ`; no definition unfolds to `True`. The proofs of `forget_rationalScalarComplexNat` and `forget_rationalDeRhamScalar` are naturality of `forgetSheafifyNatIso` and of upstream's `mapExtendCanonicalIso`, the same mechanism as the checked `forget_rationalDeRhamUnit` and `forget_wedgeSheaf`; nothing is circular.
- **Second-factor law restricted to the unit.** Precomposed with `u ⊗ 𝟙`, the second-factor law reduces to naturality of the left unitor, which holds for any endomorphism. That restriction has no content; the law itself does (bidegrees `(p, q)` with `p > 0`), and it is proved from `map_smul` of `holomorphicWedge` in its second argument. The first-factor law has content already on the unit (constant `c` times a form), which is why RT5 tests that factor.

## 4. Interface rung

Not applicable: no structure, no `Prop` hypothesis, no axiom field.

## 5. Checker and axioms

RT_Ax: all 40 declarations (`extendTensor_hom_ext`, `embeddingUpNat_f_add`, `tensorHom_extendMap_id_comp_extendMul`, `tensorHom_id_extendMap_comp_extendMul`, `sheafify_whiskerRight_comp_μ_map`, `sheafify_whiskerLeft_comp_μ_map`, `rationalScalarPresheaf`, `whiskerRight_rationalScalarPresheaf`, `rationalScalarPresheaf_comp_differential`, `rationalScalarPresheaf_one`, `_mul`, `_zero`, `_add`, `rationalScalarPresheaf_whiskerRight_wedge`, `rationalScalarPresheaf_whiskerLeft_wedge`, `rationalScalarSheaf`, `toSheafify_comp_rationalScalarSheaf`, `rationalScalarSheaf_comp_differential`, `rationalScalarSheaf_whiskerRight_wedgeSheaf`, `rationalScalarSheaf_whiskerLeft_wedgeSheaf`, `rationalScalarComplexNat`, `rationalScalarComplexNat_f`, `_one`, `_zero`, `_mul`, `_add`, `forget_rationalScalarComplexNat`, `rationalDeRhamScalar`, `rationalDeRhamScalar_f`, `forget_rationalDeRhamScalar`, the two scalar laws, `rationalDeRhamScalar_one`, `_zero`, `_mul`, `_add`, `_neg_one`, `_neg_one_ne_id`, `_ne_zero`, `_injective`) depend on `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, `axiom` or `unsafe` in the file. No name clashes with `HodgeLadder/`, `port/`, upstream or Mathlib at the pin. `python3 tools/check.py --no-build` passes on the worktree; it does not yet see this module (no root import, ledger `module: null`), so the axioms line for this rung comes from RT_Ax until change 6 lands.

## 6. Conventions

| Convention | Used where | Register row | Truth depends on it? |
|---|---|---|---|
| ℂ-action on `H_dR^n(X)` | the bridge to upstream (`forget_rationalDeRhamScalar`, RT3) | "Complex structure on H_dR and on complex constant cohomology": `c` acts by multiplication on forms, no conjugation | yes for the downstream `ℂ`-bilinearity of `deRhamCup`; the rung matches it by `rfl` at presheaf level, so a conjugated or rescaled action upstream would change both sides together |
| ℚ-structure on `HolomorphicForm` | `restrictScalars ℚ` in `rationalScalarPresheaf` | "Rational de Rham complex and its comparison": `q • θ = (q : ℂ) • θ`, the only ℚ-structure | no; `S_c` is ℚ-linear for that structure, as the definition type-checks against `rationalHolomorphicFormPresheaf` |
| composition order of `S_{ab}` | `_mul` | none; upstream's `scalarHolomorphicDeRhamComplexInt_mul` | no, since ℂ is commutative (both orders hold); the stated order is upstream's |
| factor sides of the scalar laws | the two scalar laws | "Wedge on complexes": left factor on the left, `a ⊗ b ↦ a ∧ b` | the laws are true in both factors, so the side does not change truth; the side does fix which hypothesis of `pairProductShQ_naturality` each law feeds (RT4: first factor ↔ `f`, second ↔ `g`) |
| Koszul sign of `Ω•_ℚ ⊗ Ω•_ℚ` | only through `deRhamWedge` | "Tensor product of ℤ-indexed cochain complexes and its shifts", "Wedge on complexes" | no: `S_c` has degree zero, `tensorHom (S_c) (𝟙)` carries no sign, and no step of the proof reads `ε₂` |
| sheafification and the tensorator `μ` | `sheafify_whisker{Right,Left}_comp_μ_map` | "Sheafified wedge and the sheaf tensor" | no; naturality of Mathlib's `μ`, no scalar |

Missing row: the scalar endomorphism `S_c` itself (change 3). The two neighbouring rows need a pointer each (change 4).

## 7. Equality first

Every result is an identity, proved exactly: the forget square, both scalar laws, the algebra laws. No "up to a scalar" anywhere. The rung is a step toward the `ℂ`-bilinearity of `deRhamCup` (rung `de-rham-cup`, open, depending on `de-rham-cup-exact` and this rung). What de-rham-cup needs and where it comes from:

1. `deRhamCup x y` is the bridge `B = rationalHypercohomologyEquiv X Ω•_ℚ n ∘ hypercohomologyMap X e.inv n` applied to `pairProductShQ μ y x` (sketch `cup-hodge-filtration.md`, construction steps 5 and 6).
2. `B (c • α) = B α ≫ (Q.map S_c)⟦n⟧'` for upstream's action. **This is missing from the module**, though its docstring states it ("so `S_c` induces `c •` on de Rham cohomology"). RT3 proves it in 12 lines, 3 s, with `rationalHypercohomologyEquiv_map` and upstream's `hypercohomologyMap_comp_apply`:

   ```lean
   theorem forgetRationalDeRhamIso_inv_comp_forget_rationalDeRhamScalar (c : ℂ) :
       (forgetRationalDeRhamIso X).inv ≫ (forgetComplex X).map (rationalDeRhamScalar X c) =
         scalarHolomorphicDeRhamComplexInt X c ≫ (forgetRationalDeRhamIso X).inv := by
     rw [Iso.inv_comp_eq, ← Category.assoc, ← forget_rationalDeRhamScalar X c, Category.assoc,
       Iso.hom_inv_id, Category.comp_id]

   theorem rationalHypercohomologyEquiv_smul (n : ℤ) (c : ℂ) (α : H_dR^n(X)) :
       rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n
           (hypercohomologyMap X (forgetRationalDeRhamIso X).inv n (c • α)) =
         rationalHypercohomologyEquiv X (rationalDeRhamComplex X) n
             (hypercohomologyMap X (forgetRationalDeRhamIso X).inv n α) ≫
           (DerivedCategory.Q.map (rationalDeRhamScalar X c))⟦n⟧' := by
     have h1 : hypercohomologyMap X (forgetRationalDeRhamIso X).inv n (c • α) =
         hypercohomologyMap X ((forgetComplex X).map (rationalDeRhamScalar X c)) n
           (hypercohomologyMap X (forgetRationalDeRhamIso X).inv n α) := by
       rw [deRham_complex_smul_eq]
       exact ((hypercohomologyMap_comp_apply X _ _ n α).symm.trans
         (congrArg (fun f => hypercohomologyMap X f n α)
           (forgetRationalDeRhamIso_inv_comp_forget_rationalDeRhamScalar X c).symm)).trans
         (hypercohomologyMap_comp_apply X _ _ n α)
     rw [h1]
     exact rationalHypercohomologyEquiv_map X _ n _
   ```

   It needs the local instances listed in the docstring of `HodgeLadder.Hodge.RationalHypercohomology` (`rhHasDerivedCategory`, …, `rhForgetPFC`) and that file's `implicit_reducible` attributes; a direct `rw` chain through `hypercohomologyMap_comp_apply` times out at 200000 heartbeats, the `Eq.trans` form does not. The `c • α` in the statement elaborates against upstream's instance, and `deRham_complex_smul_eq` rewrites it, so the action is `deRhamHypercohomologyComplexModule`'s (change 1).
3. `pairProductShQ μ (x ≫ S_c) y = pairProductShQ μ x y ≫ S_c` and the same in `y`: `pairProductShQ_naturality` with `m = m' = deRhamWedge X`, `k = S_c`, and `(f, g) = (S_c, 𝟙)` or `(𝟙, S_c)`, bounds `0` and `dim X.left` on both sides. RT4 elaborates both with `hm := (rationalDeRhamScalar_tensorHom_id_comp_deRhamWedge X c).symm` and `(rationalDeRhamScalar_id_tensorHom_comp_deRhamWedge X c).symm`, no conversion, 5 to 6 s each. The `y ≫ (Q.map (𝟙 _))⟦b⟧'` factor still needs `Functor.map_id` and `ShiftedHom` simp in the consumer.
4. Biadditivity from `pairProductShQ_add_left/right` (rung `de-rham-cup-exact`).

So after change 1, `de-rham-cup`'s ℂ-bilinearity is assembly from checked pieces; no further gap.

## 7b. Non-vacuity

- For `S_c`: `rationalDeRhamScalar_injective` and `rationalDeRhamScalar_neg_one_ne_id` (both in the module) fail if `S_c` were constant in `c` or rational.
- For the forget square: `eq_rationalDeRhamScalar_of_forget` (RT2, change 2) fails if the square were satisfiable by other maps.
- For the scalar laws: `eq_of_tensorHom_id_comp_deRhamWedge` (RT5, change 2), in upstream's and Mathlib's API by the names `deRhamWedge_unit`, `shQLeftUnitor_eq`, `Iso.cancel_iso_hom_left`, fails if the law held for a wrong target scalar (for example `S_{conj c}`), or if `deRhamWedge` or `S_c` were trivial. Not in the module yet.
- For the bridge: `rationalHypercohomologyEquiv_smul` (RT3, change 1) is the identity the downstream rung uses; combined with `rationalDeRhamScalar_injective` and the injectivity of the bridge it would fail if upstream's action and `S_c` disagreed.

## 8. Pin drift

None. `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are identical on the base `9a9b9cb` and on `main` (`6908d28`). The one commit between them (`p2-fundamental-class-every-point`) touches `HodgeLadder/General/LocalOrientation.lean`, two test modules, and `HodgeLadder.lean`, `docs/conventions.md`, `docs/gaps.md`, `docs/roadmap.md`, the ledger; none is imported by this module. Rebase before posting: the ledger, `docs/conventions.md`, `docs/gaps.md` and `HodgeLadder.lean` all changed on `main`.

Risks at a future pin bump, for the drift check of `docs/conventions.md`:

- Upstream moves the `SMul ℂ H_dR^n(X)` instance off `scalarHolomorphicDeRhamComplexInt` (for example to a `Module` built another way): `deRham_complex_smul_eq` stops being `rfl`, and RT3 or its successor breaks loudly. A propositionally equal replacement would need a new proof; a different action (for example the conjugate one) would make RT3 false.
- Upstream changes `scalarHolomorphicDeRhamPresheaf` (it sits in the section "Constructions used only in proofs" of a `Lemmas` file, so it is less stable than a `Definitions` entry): `whiskerRight_rationalScalarPresheaf` and `forget_rationalScalarComplexNat` are definitional and break at build time.
- Mathlib changes `Sheaf.monoidalCategory` or `Functor.LaxMonoidal.μ_natural_left/right`: the sheaf-level laws break at build time; no silent change of value is possible, since they are equalities of maps proved by rewriting.

## 9. Placement and bookkeeping

- The path `HodgeLadder/De/Rham/Scalar/Sheaf.lean` is the fallback `tools/next.py` derives from the id when `module` is `null` (the same thing happened to `wedge-sheaf-map`, red team finding 9). The front's modules sit under `HodgeLadder/Hodge/` (`WedgeSheafify`, `WedgeSheafMap`, `RationalDeRhamComplex`). Move it (change 5).
- The import of `HodgeLadder.Tests.ComplexPointNonempty` in a foundation module has a precedent (`HodgeLadder.Hodge.WedgeSheafify` imports `HodgeLadder.Tests.DeRhamUnitNonzero`) and adds no heavy dependency (`ComplexPointNonempty` imports `WedgeSheafify`, already below `WedgeSheafMap`). Splitting the three tests into a `Tests` module is optional.
- The six generic lemmas need rows in `docs/gaps.md` "General lemmas kept local" (change 7). `extendTensor_hom_ext` is the ext step of the checked `eq_extendMul_of_components` (`WedgeSheafMap.lean`, line 253) factored out; the latter could be rederived from it in a later cleanup (optional, not required here). `embeddingUpNat_f_add` is `simp`; keep it as the named spelling the rewrites need.
- Kernel cost: the docstring's figure (about 11 s per scalar law) is consistent with the 33 s module build and with the row "Kernel cost of `HomologicalComplex.mapBifunctorMap`" in `docs/gaps.md`.

## Findings

1. No sign enters and none is forced. `S_c` has degree zero; the scalar laws have no `(−1)^p`; no step of the proof reads Mathlib's `ε₂`. `S_{−1} = −𝟙` is expected and separated from `𝟙`.
2. `S_c` is upstream's scalar exactly: `rfl` at presheaf level, an exact square at complex level, and the square determines `S_c` (RT2).
3. No hidden conjugation: both sides use the same `Module ℂ` instance on `HolomorphicForm`, and the first-factor law fails with `S_{conj c}` in place of `S_c` on the target for every non-real `c` (RT5).
4. `_mul` has upstream's order `S_{ab} = S_b ≫ S_a`; the order is immaterial since ℂ is commutative.
5. The scalar laws fit `pairProductShQ_naturality` as `hm` with no conversion (RT4).
6. The bridge from `S_c` to upstream's `c •` on `H_dR^n(X)` is claimed in the module docstring and has no Lean statement; RT3 proves it in 12 lines (change 1). With it, the `ℂ`-bilinearity of `deRhamCup` has no remaining gap beyond assembly.
7. Placement: the path is `next.py`'s fallback; move to `HodgeLadder/Hodge/DeRhamScalarSheaf.lean` (change 5). The test import is acceptable.
8. Declaration count: 40, not 41.

## Required changes

1. Add `forgetRationalDeRhamIso_inv_comp_forget_rationalDeRhamScalar` and `rationalHypercohomologyEquiv_smul` (section 7, item 2, verbatim from RT3) to the module, with the local instances and `implicit_reducible` attributes of `HodgeLadder.Hodge.RationalHypercohomology` activated in a section around them. Docstring of `rationalHypercohomologyEquiv_smul`: "**`S_c` induces upstream's `c •` on `H_dR^n(X)`.** Through `forgetRationalDeRhamIso` and `rationalHypercohomologyEquiv`, upstream's action `c • α` (`deRham_complex_smul_eq`) is postcomposition with `(Q.map S_c)⟦n⟧'`. Exact, no conjugation." Keep the sentence in the module docstring and point it at this theorem.
2. Add `eq_rationalDeRhamScalar_of_forget` (section 3, RT2) and `eq_of_tensorHom_id_comp_deRhamWedge` (section 3, RT5) to the module (or to a `Tests` module that imports it). Docstrings: "**The forget square pins `S_c`**: a chain endomorphism of `Ω•_ℚ` whose forgotten image is upstream's `scalarHolomorphicDeRhamComplexInt X c` through `forgetRationalDeRhamIso` is `S_c`." and "**The first-factor scalar law pins its target scalar**: `(S_c ⊗ 𝟙) ≫ deRhamWedge X = deRhamWedge X ≫ S_{c'}` only for `c' = c`; with `S_{conj c}` or `S_{−c}` on the right it fails on every smooth integral `X`."
3. `docs/conventions.md`, new row after "Rational de Rham complex and its comparison":

   `| ℂ-scalars on the rational de Rham complex | this repository, HodgeLadder.rationalScalarPresheaf, rationalScalarSheaf, rationalDeRhamScalar, forget_rationalDeRhamScalar, rationalHypercohomologyEquiv_smul (HodgeLadder/Hodge/DeRhamScalarSheaf.lean, rung de-rham-scalar-sheaf); upstream scalarHolomorphicDeRhamPresheaf, scalarHolomorphicDeRhamComplexInt, deRham_complex_smul_eq | S_c on Ω^p_ℚ is the sheafification of θ ↦ c • θ on HolomorphicForm X d U p, read ℚ-linearly; forgetting ℚ gives upstream's scalarHolomorphicDeRhamPresheaf X d p c by rfl; on Ω•_ℚ, S_c is the extension to ℤ, forget(S_c) ≫ e = e ≫ scalarHolomorphicDeRhamComplexInt X c with e = forgetRationalDeRhamIso X, exact, and this square determines S_c; S_{ab} = S_b ≫ S_a (upstream's order), S_1 = 𝟙, S_0 = 0, S_{a+b} = S_a + S_b, S_{−1} = −𝟙; degree zero, so no Koszul sign; scalar laws (S_c ⊗ 𝟙) ≫ deRhamWedge = deRhamWedge ≫ S_c and (𝟙 ⊗ S_c) ≫ deRhamWedge = deRhamWedge ≫ S_c, no sign, no conjugation | the ℂ-bilinearity of deRhamCup (de-rham-cup) and every ℂ-linear identity on H_dR read through Ω•_ℚ; spans and membership statements are insensitive | red team 2026-11-27 (docs/sketches/de-rham-scalar-sheaf.redteam.md): uniqueness from the square (RT2), bridge to upstream's c • (RT3), both laws plug into pairProductShQ_naturality (RT4), the first-factor law fails with S_{conj c} on the target for non-real c (RT5) |`

   (with the declaration and file names in backticks, as in the neighbouring rows).
4. `docs/conventions.md`, row "Complex structure on H_dR and on complex constant cohomology", column "Results whose truth depends on it": append "; on Ω•_ℚ the action is S_c (row 'ℂ-scalars on the rational de Rham complex'), tied to this instance by `rationalHypercohomologyEquiv_smul`". Row "Wedge on complexes", column "Choice": append "ℂ-scalar laws in both factors, no sign (`rationalDeRhamScalar_tensorHom_id_comp_deRhamWedge`, `rationalDeRhamScalar_id_tensorHom_comp_deRhamWedge`, rung `de-rham-scalar-sheaf`)".
5. Move the file to `HodgeLadder/Hodge/DeRhamScalarSheaf.lean`, module `HodgeLadder.Hodge.DeRhamScalarSheaf`; delete the empty `HodgeLadder/De/` tree; import it from `HodgeLadder.lean` next to `HodgeLadder.Hodge.WedgeSheafMap`.
6. Ledger `de-rham-scalar-sheaf`: `status: "checked"`, `module: "HodgeLadder.Hodge.DeRhamScalarSheaf"`, `declarations`: the 40 names of section 5 plus the four of changes 1 and 2, all with the `HodgeLadder.` prefix, `contributors: ["claude-code"]`. Note, replacing the current one: "Checked 2026-11-27. Red team docs/sketches/de-rham-scalar-sheaf.redteam.md: pass with changes, implemented. S_c := rationalDeRhamScalar X c, the extension to ℤ of the sheafified c • on HolomorphicForm (rationalScalarSheaf), forget(S_c) = upstream's scalarHolomorphicDeRhamComplexInt X c through forgetRationalDeRhamIso (forget_rationalDeRhamScalar, exact; rfl at presheaf level, whiskerRight_rationalScalarPresheaf), and that square determines S_c (eq_rationalDeRhamScalar_of_forget). Upstream's c • on H_dR^n(X) is postcomposition with (Q.map S_c)⟦n⟧' through the bridge (rationalHypercohomologyEquiv_smul). Scalar laws in both factors, tensorHomShQ S_c 𝟙 ≫ deRhamWedge X = deRhamWedge X ≫ S_c and tensorHomShQ 𝟙 S_c ≫ deRhamWedge X = deRhamWedge X ≫ S_c, no sign (S_c has degree zero); they are the hm of pairProductShQ_naturality with m = m' = deRhamWedge X, k = S_c, (f, g) = (S_c, 𝟙) or (𝟙, S_c), no conversion. S_{ab} = S_b ≫ S_a (upstream's order), S_1, S_0, S_{a+b}, S_{−1} = −𝟙; S_{−1} ≠ 𝟙, S_c ≠ 0 for c ≠ 0, c ↦ S_c injective on every smooth integral X; the first-factor law fails with S_{c'} on the target for c' ≠ c (eq_of_tensorHom_id_comp_deRhamWedge). Module build about 35 s. Consumers activate wsmCurriedTensorAdditive, wsmTensorLeftAdditive, wsmTensorRightPreservesEmpty, and for the bridge the local instances of HodgeLadder.Hodge.RationalHypercohomology."
7. `docs/gaps.md` "General lemmas kept local", one row: "| `HodgeLadder.extendTensor_hom_ext` (maps out of `K^ℤ ⊗ K^ℤ`, `K^ℤ = K.extend embeddingUpNat`, are determined on the summands `(p, q)`, `p q : ℕ`), `embeddingUpNat_f_add`, `tensorHom_extendMap_id_comp_extendMul`, `tensorHom_id_extendMap_comp_extendMul` (a chain endomorphism commuting with `μ` in one factor commutes with `extendMul`), `sheafify_whiskerRight_comp_μ_map`, `sheafify_whiskerLeft_comp_μ_map` (a presheaf whiskering law survives sheafification through Mathlib's `μ_natural_left/right`) | `HodgeLadder.Hodge.DeRhamScalarSheaf` | generic homological algebra and sheafification; Mathlib at the pin has no product on `HomologicalComplex.extend` (row of `extendMul`) | 2026-11-27 |".
8. `docs/roadmap.md` row and the status block, per the propagation map; rebase onto `main` first (section 8).

## Not done

- The second-factor analogue of RT5 (target-scalar uniqueness for `(𝟙 ⊗ S_c) ≫ deRhamWedge`): it needs the interchange of `tensorHomShQ u 𝟙` with `tensorHomShQ 𝟙 S_c` and the naturality of the left unitor at `ShQ`, at a kernel cost likely near the 14 s of RT5; not tried. On the unit summand the law reduces to naturality of the left unitor, so such a test would read the law in bidegrees `p > 0` only through the target scalar, which RT5 already pins.
- An instance `(forgetComplex X).Faithful`: Mathlib at the pin does not produce one by instance search; RT2 works degreewise instead.
- A form-level test of `S_c` on an explicit nonzero form (for example `c • 1` in degree zero against `holomorphicFormOfConstant c`): not needed for this rung, since the presheaf map is upstream's by `rfl`.
