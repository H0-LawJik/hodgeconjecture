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

## Half-spin form (rung `clifford-exterior-half-spin`, checked)

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

## clifford-exterior-half-spin: statement

Date: 2026-11-26, branch `track/clifford-exterior-half-spin` from `main` at `62a6c1d`. Phase 1: the statements elaborate in `HodgeLadder/Markman/HalfSpin.lean` (next to `Chevalley.lean`, as instructed; `tools/next.py` prints the default path `HodgeLadder/Clifford/Exterior/Half/Spin.lean`). Phase 1 left two bodies as `sorry`: `spinAction_mem_evenOdd_iff` and `spinActionEven_bijective`. The statement red team passed it with changes (`docs/sketches/clifford-exterior-half-spin.redteam.md`). Phase 2 (2026-11-26, after a rebase onto `main` at `61b74dc`): both proofs are done by the route below, the red-team changes are implemented (section "clifford-exterior-half-spin: phase 2"), the module is imported from `HodgeLadder.lean`, and the rung is checked. The Lean block below is the phase 1 statement; phase 2 added declarations and changed no statement in it.

**Plain words.** Let `M` be finite free over a commutative ring `R`. (1) An element `x` of the Clifford algebra of `dualProd R M` has parity `i` exactly when `spinAction x` shifts the parity of `∧M` by `i`. (2) The image of `evenOdd i` under `spinAction` is the submodule of parity-`i` endomorphisms (the equality form). (3) Restricting the action of an even element to `∧^ev M` and to `∧^odd M` is an algebra isomorphism from `Cl^+` onto `End(∧^ev M) × End(∧^odd M)`.

**Lean** (namespace `HodgeLadder`, same `variable` line as `Chevalley.lean`; `Q` abbreviates `QuadraticForm.dualProd R M` here only, the file spells it out):

```lean
def parityShift (i : ZMod 2) : Submodule R (Module.End R (ExteriorAlgebra R M)) :=
  ⨅ j : ZMod 2, Submodule.compatibleMaps (exteriorParity R M j) (exteriorParity R M (j + i))

theorem mem_parityShift {i : ZMod 2} {f : Module.End R (ExteriorAlgebra R M)} :
    f ∈ parityShift R M i ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        f y ∈ exteriorParity R M (j + i)                                   -- proved

theorem spinAction_mem_evenOdd_iff [Module.Free R M] [Module.Finite R M] (i : ZMod 2)
    (x : CliffordAlgebra Q) :
    x ∈ evenOdd Q i ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        spinAction R M x y ∈ exteriorParity R M (j + i)                    -- sorry

theorem spinAction_mem_evenOdd_zero_iff [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra Q) :
    x ∈ evenOdd Q 0 ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        spinAction R M x y ∈ exteriorParity R M j                          -- from the iff

theorem spinAction_mem_evenOdd_one_iff [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra Q) :
    x ∈ evenOdd Q 1 ↔
      ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
        spinAction R M x y ∈ exteriorParity R M (j + 1)                    -- from the iff

theorem map_evenOdd_dualProd_eq_parityShift [Module.Free R M] [Module.Finite R M]
    (i : ZMod 2) :
    (evenOdd Q i).map (spinAction R M).toLinearMap = parityShift R M i
                                                -- from the iff and spinAction_bijective

def spinActionParity (j : ZMod 2) :
    CliffordAlgebra.even Q →ₐ[R] Module.End R (exteriorParity R M j)   -- restriction, built

def spinActionEven :
    CliffordAlgebra.even Q →ₐ[R]
      Module.End R (exteriorParity R M 0) × Module.End R (exteriorParity R M 1) :=
  (spinActionParity R M 0).prod (spinActionParity R M 1)

theorem spinActionEven_bijective [Module.Free R M] [Module.Finite R M] :
    Function.Bijective (spinActionEven R M)                                -- sorry

noncomputable def spinEquivEven [Module.Free R M] [Module.Finite R M] :
    CliffordAlgebra.even Q ≃ₐ[R]
      Module.End R (exteriorParity R M 0) × Module.End R (exteriorParity R M 1) :=
  AlgEquiv.ofBijective (spinActionEven R M) (spinActionEven_bijective R M)

@[simp] theorem spinEquivEven_apply ... (x : CliffordAlgebra.even Q) :
    spinEquivEven R M x = (spinActionParity R M 0 x, spinActionParity R M 1 x) := rfl
theorem spinEquivEven_apply_fst ... (y : exteriorParity R M 0) :
    ((spinEquivEven R M x).1 y : ExteriorAlgebra R M) = spinAction R M x y := rfl
theorem spinEquivEven_apply_snd ... (y : exteriorParity R M 1) :
    ((spinEquivEven R M x).2 y : ExteriorAlgebra R M) = spinAction R M x y := rfl
theorem spinEquivEven_ι_mul_ι_fst ... (v w : Module.Dual R M × M) (y : exteriorParity R M 0) :
    ((spinEquivEven R M ((even.ι _).bilin v w)).1 y : ExteriorAlgebra R M) =
      spinGen R M v (spinGen R M w y)                                      -- proved

theorem spinActionEven_int_zmod_two_not_surjective :
    ¬ Function.Surjective (spinActionEven ℤ (ZMod 2))                      -- proved
```

Also proved: `spinAction_mem_exteriorParity_of_mem_even` (an even element preserves each parity part, no hypothesis on `M`; it is what makes `spinActionParity` a definition), `spinActionParity_apply`. The data `spinActionParity` and `spinActionEven` carry no `sorry`; only the bijectivity proof that `spinEquivEven` takes is open.

**Refinements against the earlier "Half-spin form" section.** The two posted iff statements are kept verbatim. They are corollaries of one statement for all `i : ZMod 2`, written with `j + i` (the order of the posted `_one_iff`; the checked `spinAction_mem_exteriorParity` writes `i + j`). The equality form is added as an equality of submodules of `End(∧M)`: the image of `evenOdd i` is all of `parityShift i`, which also uses surjectivity, so it is stronger than the iff. `spinEquivEven` is `AlgEquiv.ofBijective` of an explicit restriction map, so its value is `rfl`. Nothing is weakened.

**Hypotheses.**

| Hypothesis | Needed? | Why |
|---|---|---|
| `[CommRing R]` | yes | `spinAction` is defined over a commutative ring |
| `[Module.Free R M] [Module.Finite R M]` on the iff | needed through injectivity of `spinAction`; the forward direction needs neither | the general form is `spinAction_mem_evenOdd_iff_of_injective`, and `injective_spinAction_iff` makes the criterion for all `i` equivalent to injectivity. `Module.Free` cannot be dropped: `evenOdd_one_iff_zmod_four_fails` is a finite non-free counterexample (the ideal `(2)` of `ZMod 4`, where the nonzero even element `ι (0, 2) * ι (incl, 0)` acts by `0`). Over a field `Module.Finite` is not needed (red team, hand argument). For `ZMod 2` over `ℤ` the action is faithful, so the iff holds there |
| `[Module.Free R M]` on `spinEquivEven` | yes | checked for both halves. Injectivity: `spinActionEven_zmod_four_not_injective` (the ideal `(2)` of `ZMod 4`). Surjectivity: `spinActionEven_int_zmod_two_not_surjective`. For `M = ZMod 2` over `ℤ`, `(0, 1)` is not in the range: an element acting by `0` on `1 ∈ ∧^ev` acts by `0` on `ι 1 ∈ ∧^odd`, and `ι 1 ≠ 0` |
| `[Module.Finite R M]` on `spinEquivEven` | yes | the bounded-shift argument of `Chevalley.lean`, restricted to `∧^ev M`: an even element shifts exterior degree by a bounded amount, and for `M = ℚ^(ℕ)` some endomorphism of `∧^ev M` does not (hand argument, not compiled) |
| `[Nontrivial R]` | no | over the zero ring both sides of every statement are subsingletons; no rank appears |

**Route (phase 2).** Iff, reverse direction: write `x = a + b` with `a ∈ evenOdd i`, `b ∈ evenOdd (i + 1)` (`evenOdd_isCompl`, `Submodule.mem_sup`). For `y ∈ exteriorParity j`, `spinAction b y = spinAction x y − spinAction a y` lies in parity `j + i` and, by `spinAction_mem_exteriorParity`, in parity `j + i + 1`, so it is `0` by `evenOdd_isCompl (0 : QuadraticForm R M)` and `exteriorParity_eq_evenOdd`. The two parity parts span `∧M`, so `spinAction b = 0`, and `b = 0` by `spinAction_bijective`. Bijectivity: injective because `spinAction (x − x')` vanishes on both parity parts, hence on `∧M`; surjective because for `(f₀, f₁)` the endomorphism `ι₀ ∘ f₀ ∘ π₀ + ι₁ ∘ f₁ ∘ π₁` (`Submodule.projectionOnto` for the two projections; `linearProjOfIsCompl` is a deprecated alias at the pin) lies in `parityShift 0`, so its preimage under `spinAction` is even by the iff, and its restrictions are `f₀` and `f₁`.

**Elaboration and trivial proofs.** Phase 1: `lake env lean HodgeLadder/Markman/HalfSpin.lean`: 5.0 to 5.2 s wall time, two `declaration uses 'sorry'` warnings, no errors. Phase 2, the finished module: 5.7 to 6.8 s, no warnings. On the general iff, these fail (scratch copy, 5 to 23 s each): `rfl` (not definitional), `simp` (no progress), `aesop` (exhaustive search fails), `exact?` (no proof found), `constructor <;> simp` (no progress), `constructor <;> aesop` (heartbeat timeout), and the forward direction from `spinAction_mem_exteriorParity` with `simp_all` for the reverse (no progress). On `spinActionEven_bijective`: `rfl` (type mismatch), `simp [spinActionEven]` (unsolved goals), `aesop` (no progress), `exact?` and `constructor <;> exact?` (no proof found), and `⟨fun a b h => by simpa using h, fun p => ⟨0, by simp⟩⟩` (type mismatch).

**Non-vacuity.** The hypotheses hold for `M = ℤ^n` and `M = ℚ^n` (red team of `clifford-exterior-chevalley`, section 2). The iff separates the two parities nontrivially: with the checked `ι_not_mem_exteriorParity_zero`, `ι (0, m)` for `ι m ≠ 0` is odd and fails the even condition. Irreducibility and inequivalence of `∧^ev` and `∧^odd` over `ℚ` ([GolyshevLuntsOrlov2001] §3.5.1) remain a further step.

**Questions for the red team (answered in the verdict).**

1. Is `parityShift` (an `iInf` of `Submodule.compatibleMaps`) the right shape for the equality form, or should the equality be stated as `evenOdd Q i = (parityShift R M i).comap (spinAction R M).toLinearMap`? The `map` form is stated because it also records surjectivity onto the parity-`i` endomorphisms.
2. `j + i` against `i + j` in `spinAction_mem_exteriorParity`: keep `j + i` as posted, or align with the checked lemma?
3. Should the module also state that the two components of `spinEquivEven` are surjective `AlgHom`s separately, the form in which [Markman2025] reads a unit of `Cl^+` as a pair in `GL(∧^ev) × GL(∧^odd)` (unverified at page level)?

## clifford-exterior-half-spin: phase 2

| Red-team change | Done |
|---|---|
| route (finding 1) | as written above; `evenOdd_isCompl_add_one` (`fin_cases k` on `evenOdd_isCompl`), `exteriorParity_isCompl_add_one`, `exteriorParity_isCompl`, `ext_exteriorParity` (two endomorphisms that agree on both parity parts are equal) are the helpers |
| `ZMod 4` tests (finding 2) | `zmodFourIdeal`, `zmodFourGen`, `zmodFourCovector`, `zmodFourCovector_smul_gen`, `spinAction_zmodFour_kernel`, `zmodFourPairing`, `zmodFourPairing_toQuadraticMap`, `zmodFourAlt`, `zmodFourAlts`, `zmodFour_kernel_ne_zero`, `spinAction_zmodFour_not_injective`, `not_free_zmodFourIdeal`, `evenOdd_one_iff_zmod_four_fails`, `spinActionEven_zmod_four_not_injective`; the red team's code, wrapped to 100 columns; the module imports `Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating` for it |
| injectivity form (finding 3) | `spinAction_mem_evenOdd_iff_of_injective`, with `spinAction_mem_evenOdd_iff` in one line from it; `injective_spinAction_iff` also, since it costs six lines (an element acting by `0` meets the criterion in both parities, so it lies in `evenOdd 0 ⊓ evenOdd 1 = ⊥`) |
| `comap` form (finding 4) | `evenOdd_dualProd_eq_comap_parityShift`; the `map` form stays the headline |
| `j + i` (finding 5) | kept |
| separate components (finding 6) | `spinActionParity_surjective`; `spinUnitsEquivEven` deferred to the rung that defines Spin(V) |
| non-vacuity of the even condition (finding 7) | `ι_vec_not_mem_evenOdd_zero_int` |
| hypothesis table (finding 8) | corrected above |
| GLO 3.5.1 (finding 9) | future rung below, sketch only |

## Future rung: irreducibility of the half-spin modules (GLO 3.5.1)

Recorded here only, with no ledger entry yet (red team of `clifford-exterior-half-spin`, finding 9). Over a field, `exteriorParity R M 0` and `exteriorParity R M 1` are irreducible `Cl⁰`-modules and are not isomorphic. Both follow in a few lines from `spinActionParity_surjective` (a module whose endomorphism algebra is the image of `Cl⁰` has no proper nonzero invariant subspace) and from the central idempotent `(spinEquivEven R M).symm (1, 0)`, which acts by `1` on one part and by `0` on the other. [GolyshevLuntsOrlov2001] §3.5.1 states it for the group `Spin_ℚ`, which needs in addition that `Spin_ℚ` spans `Cl⁰_ℚ`. Open it when the Markman track needs irreducibility.

## Future rung: Chevalley's S ⊗ S ≅ ∧*V

Recorded here only, with no ledger entry yet (red team, finding 9). The Markman inventory cites "Chevalley S ⊗ S ≅ ∧*V" [Chevalley1954]. It needs this rung, the Mukai (Chevalley) pairing on S, and the normal-ordering identification `Cl(V) ≅ ∧V` of modules; this rung does not imply it. Open it when the Markman track reaches it.

## Questions for the red team (phase 1, answered)

1. Is `spinEquiv` the right name, given finding 7 of the spin red team (keep "spin" for the Chevalley isomorphism)? Alternative: `cliffordDualProdEquivEnd`.
2. Should the rung also state the half-spin form `even (dualProd R M) ≅ End(∧^ev) × End(∧^odd)` now, or as a separate rung (finding in section 7 of the spin red team: no rung yet)?
3. Is `Module.Free` the intended generality, or should the statement be for finite projective `M` (true by localization, not needed for `H¹` of a torus over `ℤ` or `ℚ`)?
4. The sign of `exists_mem_range_apply_basis` is left existential (`u : ℤˣ`). It is used only to show membership in the range, and the matrix-unit statement `basis_end_mem_range` carries no sign; confirm that no downstream rung needs the exact sign.
