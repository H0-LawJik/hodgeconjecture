# Sketch: `clifford-exterior-chevalley`

Date: 2026-11-26. Branch `track/clifford-exterior-chevalley` from `main` at `8b3a2fa`. Pin unchanged (Lean and Mathlib `v4.35.0-rc4`). Phase 1 fixed the statement; the statement red team passed it with changes (`docs/sketches/clifford-exterior-chevalley.redteam.md`). Phase 2, also on 2026-11-26: every declaration in `HodgeLadder/Markman/Chevalley.lean` is proved by the route below, the module is imported from `HodgeLadder.lean`, and the rung is checked. The red-team changes are implemented; see the section "Red-team changes".

Inputs read: the ledger entry, `HodgeLadder/Markman/CliffordSpin.lean` (`spinGen`, `spinAction`, `spinAction_unique`), `docs/sketches/clifford-exterior-spin.redteam.md` (finding 6, the two routes), the register row "Clifford relation of the split form and its action on ∧H" in `docs/conventions.md`, and the key `Chevalley1954` (not opened; the theorem is also [GolyshevLuntsOrlov2001, Prop. 3.2.1(e)], quoted in the spin red team, section 1).

## Statement

**Plain words.** Let `M` be a finite free module over a commutative ring `R`. The algebra map `spinAction R M` from the Clifford algebra of the split form `Q (f, x) = f x` on `Module.Dual R M × M` to `End_R(∧M)`, which sends `ι (f, x)` to contraction by `f` plus left wedge with `x`, is bijective. So it is an isomorphism of `R`-algebras.

**Lean** (namespace `HodgeLadder`, `variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]`):

```lean
theorem spinAction_bijective [Module.Free R M] [Module.Finite R M] :
    Function.Bijective (spinAction R M)

noncomputable def spinEquiv [Module.Free R M] [Module.Finite R M] :
    CliffordAlgebra (QuadraticForm.dualProd R M) ≃ₐ[R] Module.End R (ExteriorAlgebra R M) :=
  AlgEquiv.ofBijective (spinAction R M) (spinAction_bijective R M)

@[simp] theorem spinEquiv_apply [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra (QuadraticForm.dualProd R M)) : spinEquiv R M x = spinAction R M x := rfl

theorem spinEquiv_ι_apply [Module.Free R M] [Module.Finite R M] (v : Module.Dual R M × M)
    (y : ExteriorAlgebra R M) :
    spinEquiv R M (ι _ v) y = contractLeft v.1 y + ExteriorAlgebra.ι R v.2 * y

theorem spinEquiv_symm_spinGen [Module.Free R M] [Module.Finite R M] (v : Module.Dual R M × M) :
    (spinEquiv R M).symm (spinGen R M v) = ι _ v

theorem finrank_cliffordAlgebra_dualProd [Nontrivial R] [Module.Free R M] [Module.Finite R M] :
    Module.Free R (CliffordAlgebra (QuadraticForm.dualProd R M)) ∧
      Module.finrank R (CliffordAlgebra (QuadraticForm.dualProd R M)) =
        2 ^ (2 * Module.finrank R M)
```

`spinEquiv_apply`, `spinEquiv_ι_apply` and `spinEquiv_symm_spinGen` take one or two rewrites each, from `spinAction_ι_apply` and `AlgEquiv.symm_apply_eq`. The rank corollary is [GolyshevLuntsOrlov2001] Prop. 3.2.1(a), rank part, obtained as a consequence; with `finrank_cliffordAlgebra_dualProd_int` (rank 4 for `M = ℤ`) it checks the route end to end. The test that the hypotheses carry weight is `spinAction_int_zmod_two_not_surjective`.

**Hypotheses, one by one.**

| Hypothesis | Needed? | Why |
|---|---|---|
| `[CommRing R]` | yes | `spinAction` is built over a commutative ring; the Orzech property (`CommRing.orzechProperty`, `RingTheory/FiniteType.lean:625`) drives injectivity |
| `[Module.Finite R M]` | yes | an element of the Clifford algebra is a finite sum of products of at most `N` generators, and each generator shifts the exterior degree by at most one, so its image maps `⋀^k M` into the sum of the `⋀^j M` with `|j − k| ≤ N`. For `M = ℚ^(ℕ)` the endomorphism sending `e_{0,…,k−1}` to `e_{0,…,2k−1}` and the other basis monomials to `0` has unbounded shift, so it is not in the range (hand argument, not compiled). A dimension count does not separate the two sides: `Dual ℚ ℚ^(ℕ) ≅ ℚ^ℕ` has dimension 2^{ℵ₀}, and so do both sides |
| `[Module.Free R M]` | yes, as a hypothesis; finite projective would also work (`docs/gaps.md`) | for `R = ℤ`, `M = ℤ/2`: the dual is `0`, so every element acts by left multiplication by its value on `1`, and the projection onto `⋀¹` is not of this form. Checked: `spinAction_int_zmod_two_not_surjective` |
| `[Nontrivial R]` | no, for the bijection | over the zero ring both sides are subsingletons; scratch compile: `Function.Bijective (spinAction R M)` for `[Subsingleton R]` from `Module.subsingleton` |
| `[Nontrivial R]` | yes, for `finrank_cliffordAlgebra_dualProd` | Mathlib sets `finrank R M = 1` over the zero ring (`Module.finrank_subsingleton`), so the formula reads `1 = 4`; scratch compile of that inequality |

**File path.** `tools/next.py` prints the default path `HodgeLadder/Clifford/Exterior/Chevalley.lean`; this session used `HodgeLadder/Markman/Chevalley.lean`, next to `CliffordSpin.lean`, as instructed. The ledger `module` field is still `null`; set it to `HodgeLadder.Markman.Chevalley` when the rung is checked.

## Mathlib at the pin

| Declaration | File | Use here |
|---|---|---|
| `Module.Basis.ExteriorAlgebra : Basis (Finset I) R (ExteriorAlgebra R M)` for `[LinearOrder I]`, `basis_apply`, `basis_eq_coe_basis`, `basis_mul_of_disjoint` (sign `(permOfDisjoint h).sign`, a `ℤˣ`), `basis_mul_of_not_disjoint` | `LinearAlgebra/ExteriorAlgebra/Basis.lean` | the basis monomials `e_S` and their products |
| `Module.Basis.end`, `Basis.end_apply_apply : (b.end ij) (b k) = if ij.2 = k then b ij.1 else 0` | `LinearAlgebra/Matrix/ToLin.lean:1100` | matrix units of `End(∧M)` |
| `Module.finrank_linearMap` | `LinearAlgebra/FreeModule/Finite/Matrix.lean:60` | `finrank End(∧M) = (2 ^ n) ^ 2` |
| `OrzechProperty.bijective_of_surjective_of_finrank_le` | `LinearAlgebra/Dimension/Free.lean:374` | injectivity |
| `ExteriorAlgebra.ιMulti_apply : ιMulti R n v = (List.ofFn fun i => ι R (v i)).prod` | `LinearAlgebra/ExteriorAlgebra/Basic.lean:300` | basis monomials as list products |
| `List.mem_sublists`, `List.length_sublists : (sublists l).length = 2 ^ l.length` | `Data/List/Sublists.lean` | counting the spanning set |
| `CliffordAlgebra.prodEquiv : CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂)`, `QuadraticForm.dualProdProdIsometry`, `ExteriorAlgebra.prodEquivTensor` (graded tensor) | `CliffordAlgebra/Prod.lean:170`, `QuadraticForm/Dual.lean:111`, `ExteriorAlgebra/Product.lean:109` | route 2 only |
| basis, rank, `Module.Finite` or `Module.Free` for a general Clifford algebra | none | searched `LinearAlgebra/CliffordAlgebra/` for `Module.Finite`, `finrank`, `Module.Free`: no hits |

## Route

**Chosen: ordered monomials, counted by sublists, plus matrix units, plus Orzech.** The ledger's first route, with the spanning set indexed by `List.sublists` so that no order on the index set is needed and the count `2 ^ L.length` is `List.length_sublists`.

**Set aside: rank induction (route 2).** `CliffordAlgebra.prodEquiv` lands in the graded tensor product `evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂`, and `ExteriorAlgebra.prodEquivTensor` in the graded tensor of the exterior powers. The induction step needs `End(A ᵍ⊗ B) ≅ End A ⊗ End B` with the Koszul sign on the odd operators and a compatibility of `spinAction` with both isomorphisms. None of that is in Mathlib, and it is harder than the direct count. Kill criterion for route 1: if step 2 below needs more than about 300 lines because of the `powersetCard` reindexing in `Basis.ExteriorAlgebra`, reconsider.

### Step 1: spanning (general quadratic form)

`{R N} [CommRing R] [AddCommGroup N] [Module R N]`, `sublistSpan Q L := Submodule.span R {y | ∃ l ∈ L.sublists, y = (l.map (ι Q)).prod}`.

```lean
theorem ι_mul_mem_sublistSpan (Q : QuadraticForm R N) (L : List N) {v : N} (hv : v ∈ L)
    {y : CliffordAlgebra Q} (hy : y ∈ sublistSpan Q L) : ι Q v * y ∈ sublistSpan Q L
theorem span_sublists_prod_eq_top (Q : QuadraticForm R N) (L : List N)
    (hL : Submodule.span R {v | v ∈ L} = ⊤) : sublistSpan Q L = ⊤
theorem exists_surjective_fun_cliffordAlgebra (Q : QuadraticForm R N) (L : List N)
    (hL : Submodule.span R {v | v ∈ L} = ⊤) :
    ∃ φ : (Fin (2 ^ L.length) → R) →ₗ[R] CliffordAlgebra Q, Function.Surjective φ
```

Proof of the first, by induction on `L = a :: L'` (span induction on `y` reduces to `y = prod l`, `l <+ a :: L'`). If `l <+ L'`: for `v = a`, `a :: l <+ a :: L'`; for `v ∈ L'`, the induction hypothesis. If `l = a :: l'` with `l' <+ L'`: for `v = a`, `ι a * ι a = algebraMap (Q a)` (`ι_sq_scalar`); for `v ∈ L'`, `ι v * ι a = algebraMap (polar Q v a) - ι a * ι v` (`ι_mul_ι_add_swap`), so `ι v * prod (a :: l') = polar • prod l' - ι a * (ι v * prod l')`, the induction hypothesis puts `ι v * prod l'` in `sublistSpan Q L'`, and left multiplication by `ι a` maps `sublistSpan Q L'` into `sublistSpan Q (a :: L')`. The second: the set of `x` with `x * sublistSpan ⊆ sublistSpan` contains `ι v` for `v` in the span of `L` by linearity, hence everything by `CliffordAlgebra.induction`, and `1 = prod []` is in the span. The third: `Fintype.linearCombination` of `i ↦ prod (L.sublists.get i)`, reindexed by `List.length_sublists`.

For `V = Module.Dual R M × M` and a basis `b : Basis I R M`, take `L = (univ.toList.map fun i => (b.coord i, 0)) ++ (univ.toList.map fun i => (0, b i))`, length `2 * Fintype.card I`.

### Step 2: surjectivity (basis indexed by a finite linear order)

```lean
theorem contractLeft_list_prod_eq_zero (f : Module.Dual R M) (l : List M)
    (hl : ∀ x ∈ l, f x = 0) :
    contractLeft (Q := (0 : QuadraticForm R M)) f ((l.map (ExteriorAlgebra.ι R)).prod) = 0
theorem list_prod_contractLeft_eq_zero (fs : List (Module.Dual R M)) {j : ℕ}
    {y : ExteriorAlgebra R M} (hy : y ∈ ⋀[R]^j M) (hj : j < fs.length) :
    (fs.map fun f => contractLeft (Q := (0 : QuadraticForm R M)) f).prod y = 0
theorem list_prod_contractLeft_coord {I : Type*} (b : Module.Basis I R M) (l : List I)
    (hl : l.Nodup) :
    (l.reverse.map fun i => contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)).prod
      ((l.map fun i => ExteriorAlgebra.ι R (b i)).prod) = 1
theorem spinAction_list_prod_vec (l : List M) (y : ExteriorAlgebra R M) :
    spinAction R M ((l.map fun x => ι (QuadraticForm.dualProd R M) (0, x)).prod) y =
      (l.map (ExteriorAlgebra.ι R)).prod * y
theorem exists_mem_range_apply_basis {I : Type*} [Fintype I] [LinearOrder I]
    (b : Module.Basis I R M) (T : Finset I) :
    ∃ a ∈ (spinAction R M).range, ∃ u : ℤˣ, ∀ U : Finset I,
      a (b.ExteriorAlgebra U) = if U = T then u • (1 : ExteriorAlgebra R M) else 0
theorem basis_end_mem_range {I : Type*} [Fintype I] [LinearOrder I] (b : Module.Basis I R M)
    (S T : Finset I) : b.ExteriorAlgebra.end (S, T) ∈ (spinAction R M).range
theorem spinAction_surjective_of_basis {I : Type*} [Fintype I] [LinearOrder I]
    (b : Module.Basis I R M) : Function.Surjective (spinAction R M)
theorem spinAction_surjective [Module.Free R M] [Module.Finite R M] :
    Function.Surjective (spinAction R M)
```

The construction avoids most sign bookkeeping. Write `e_U = b.ExteriorAlgebra U` and `I` for `Finset.univ`. Let `c` be the contractions by all dual-basis vectors, applied in the sorted order of `I` (a `spinAction` of a product of `ι (b.coord i, 0)`, by `spinAction_ι_dual`).

- `c e_I = 1` exactly, by `list_prod_contractLeft_coord` on the sorted list of `I` (`contractLeft_ι_mul` peels one factor; `contractLeft_list_prod_eq_zero` kills the correction term since the list has no duplicates).
- `c y = 0` for `y ∈ ⋀^j M`, `j < n`, by `list_prod_contractLeft_eq_zero` (from the checked `contractLeft_mem_range_ι_pow` and `contractLeft_algebraMap`). Every `e_U` with `U ≠ I` has `|U| < n`.
- `a_T := c ∘ (e_{I \ T} * ·)`. If `U` meets `I \ T`, `e_{I \ T} * e_U = 0` (`basis_mul_of_not_disjoint`). Otherwise `U ⊆ T` and `e_{I \ T} * e_U = sign • e_{(I \ T) ∪ U}` (`basis_mul_of_disjoint`), of degree `< n` unless `U = T`. So `a_T e_U = if U = T then sign • 1 else 0`: this is `exists_mem_range_apply_basis`, with `e_{I \ T} * ·` in the range by `spinAction_list_prod_vec` and `ιMulti_apply`.
- `E_{S,T} = u • ((e_S * ·) ∘ a_T)`, since `u • u = 1` in `ℤˣ`. Check on `e_U` with `Basis.end_apply_apply` and `Basis.ext`. The range is a subalgebra, so `E_{S,T}` is in it, and the matrix units span `End(∧M)` (`Basis.span_eq`).
- `spinAction_surjective`: `Module.Free.chooseBasis`, a `LinearOrder` on its finite index type (for example `LinearOrder.lift'` along `Fintype.equivFin`), then the basis form.

### Step 3: injectivity

```lean
theorem finrank_end_exteriorAlgebra [Nontrivial R] {I : Type*} [Fintype I] [LinearOrder I]
    (b : Module.Basis I R M) :
    Module.finrank R (Module.End R (ExteriorAlgebra R M)) = 2 ^ (2 * Fintype.card I)
```

From `Module.finrank_linearMap`, `Module.finrank_eq_card_basis b.ExteriorAlgebra` and `Fintype.card_finset`. Then for `spinAction_bijective`: split on `subsingleton_or_nontrivial R` (the zero ring case is the scratch compile above). Otherwise take `φ` from step 1 with `L` of length `2 n`; `ψ := (spinAction R M).toLinearMap ∘ₗ φ` is surjective by step 2; `finrank (Fin (2 ^ (2 n)) → R) = 2 ^ (2 n) = finrank End(∧M)`; `OrzechProperty.bijective_of_surjective_of_finrank_le` makes `ψ` bijective; since `φ` is surjective, `spinAction` is injective. The rank corollary follows: `spinEquiv` gives `Cl ≃ₗ End(∧M)`, which is free of rank `2 ^ (2 n)`.

## Elaboration and trivial proofs

Phase 1: `lake env lean HodgeLadder/Markman/Chevalley.lean` took 4.0 to 4.4 s wall time, warnings `declaration uses 'sorry'` only (fourteen sorried declarations), no errors. Phase 2, the finished module: 6 to 7 s, no warnings. `lake build HodgeLadder.Markman.CliffordSpin` (warm): 10.9 s.

Trivial proofs of `Function.Bijective (spinAction R M)` under `[Module.Free R M] [Module.Finite R M]` all fail (scratch compile, 9.2 s): `rfl` (not definitional), `simp` (no progress), `constructor <;> simp` (no progress), `⟨fun _ _ h => by simpa using h, fun y => ⟨_, rfl⟩⟩` (type mismatch), `aesop` (no progress), `exact?` on surjectivity and on injectivity separately (no proof found); `constructor <;> aesop` without the finiteness hypotheses fails too.

## Red-team changes

| Change | Done |
|---|---|
| (a) the `Module.Finite` reason | bounded degree shift, in the hypotheses table above |
| (b) tests | `dual_int_zmod_two_eq_zero`, `spinAction_int_zmod_two_apply`, `spinAction_int_zmod_two_not_surjective`, `finrank_cliffordAlgebra_dualProd_int` in the module and the ledger |
| (c) non-vacuity wording | the rank corollary is GLO 3.2.1(a) as a consequence; the hypothesis test is the `ZMod 2` theorem |
| (d) full-strength basis | `linearIndependent_sublistProd_dualProd` and `cliffordDualProdBasis` (with `cliffordDualProdBasis_apply`): for a basis `b` of `M` indexed by a finite type, the products of the sublists of `dualProdList b` are a basis of the Clifford algebra. It costs one step: the Orzech count already makes `R ^ (2 ^ (2 n)) → Cl → End(∧M)` injective (`injective_spinAction_comp_sublistProd`) |
| (e) graded form | new open rung `clifford-exterior-half-spin`; statements below |
| (f) name | `spinEquiv` kept |
| finding 2, bridge | `basis_exteriorAlgebra_eq_list_prod`; `powersetCard` appears only in `exists_mem_range_apply_basis`, through `basis_mul_of_disjoint` and `basis_mul_of_not_disjoint` |

Step 2 (contraction lemmas through `spinAction_surjective`) is about 230 lines with docstrings, under the kill criterion of 300.

## Half-spin form (rung `clifford-exterior-half-spin`, open)

From the red team, finding 7. They elaborate at the pin with `sorry` bodies (red team scratch); the third needs `public import Mathlib.LinearAlgebra.CliffordAlgebra.Even`. They are not in the checked module.

```lean
theorem spinAction_mem_evenOdd_zero_iff [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra (QuadraticForm.dualProd R M)) :
    x ∈ evenOdd (QuadraticForm.dualProd R M) 0 ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        spinAction R M x y ∈ exteriorParity R M j

theorem spinAction_mem_evenOdd_one_iff [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra (QuadraticForm.dualProd R M)) :
    x ∈ evenOdd (QuadraticForm.dualProd R M) 1 ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        spinAction R M x y ∈ exteriorParity R M (j + 1)

noncomputable def spinEquivEven [Module.Free R M] [Module.Finite R M] :
    CliffordAlgebra.even (QuadraticForm.dualProd R M) ≃ₐ[R]
      Module.End R (exteriorParity R M 0) × Module.End R (exteriorParity R M 1)
```

The forward directions follow from the checked `spinAction_mem_evenOdd`. For the reverse direction of the first, write `x = x₀ + x₁` (`evenOdd_isCompl`); the action of `x₁` maps each parity part into both parities, hence to `0`, so `spinAction x₁ = 0` and `x₁ = 0` by `spinAction_bijective`. Equality form first, the product decomposition second. Irreducibility and inequivalence of S⁺ and S⁻ over ℚ ([GolyshevLuntsOrlov2001] §3.5.1) is a further step.

## Future rung: Chevalley's S ⊗ S ≅ ∧*V

Recorded here only, with no ledger entry yet (red team, finding 9). The Markman inventory cites "Chevalley S ⊗ S ≅ ∧*V" [Chevalley1954]. It needs this rung, the Mukai (Chevalley) pairing on S, and the normal-ordering identification `Cl(V) ≅ ∧V` of modules; this rung does not imply it. Open it when the Markman track reaches it.

## Questions for the red team (phase 1, answered)

1. Is `spinEquiv` the right name, given finding 7 of the spin red team (keep "spin" for the Chevalley isomorphism)? Alternative: `cliffordDualProdEquivEnd`.
2. Should the rung also state the half-spin form `even (dualProd R M) ≅ End(∧^ev) × End(∧^odd)` now, or as a separate rung (finding in section 7 of the spin red team: no rung yet)?
3. Is `Module.Free` the intended generality, or should the statement be for finite projective `M` (true by localization, not needed for `H¹` of a torus over `ℤ` or `ℚ`)?
4. The sign of `exists_mem_range_apply_basis` is left existential (`u : ℤˣ`). It is used only to show membership in the range, and the matrix-unit statement `basis_end_mem_range` carries no sign; confirm that no downstream rung needs the exact sign.
