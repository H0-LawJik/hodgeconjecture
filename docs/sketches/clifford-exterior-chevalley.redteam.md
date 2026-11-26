# Red team: `clifford-exterior-chevalley` (statement pass)

Date: 2026-11-26. Branch `track/clifford-exterior-chevalley` from `main` at `8b3a2fa`; `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` have no diff against `main` (pin `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`). Target: the fourteen sorried declarations and the three proved wrappers in `HodgeLadder/Markman/Chevalley.lean`, before any proof work. Inputs read: the ledger entries `clifford-exterior-chevalley`, `clifford-exterior-spin` and `markman-statement`, the sketch, `HodgeLadder/Markman/CliffordSpin.lean`, `docs/sketches/clifford-exterior-spin.redteam.md`, the register row "Clifford relation of the split form and its action on ∧H", `docs/references.md`, the research note 2026-11-24 §1, the Markman inventory 2026-11-25, and the Mathlib sources at the pin for `OrzechProperty.bijective_of_surjective_of_finrank_le`, `CommRing.orzechProperty`, `Module.Basis.ExteriorAlgebra` and its product lemmas, `Basis.end_apply_apply`, `List.length_sublists`, `Module.finrank_subsingleton`, `Module.Free.ChooseBasisIndex.fintype`. Literature opened this pass: the arXiv source of [GolyshevLuntsOrlov2001] (math/9812003), §3.1, §3.2, Prop. 3.2.1 with its proof, §3.5.1 and §4.3.6. Not opened: [Chevalley1954]. Scratch files were compiled with `lake env lean` inside the worktree and deleted afterwards.

**Verdict: pass with changes.** The targets state [GolyshevLuntsOrlov2001] Prop. 3.2.1(e) in the model [Markman2025] uses, at the generality the Markman track needs (ℤ and ℚ coefficients). The hypotheses are right, and one of the two counterexamples now has a sorry-free Lean proof. The route is the proof GLO give, down to the unspecified sign. The changes are a wrong argument in the sketch, two short test theorems to add, and a follow-up rung for the graded form. No change alters a target statement.

## 1. Is this the statement the literature makes?

[GolyshevLuntsOrlov2001] §3.1 (source, quoted): "Put Λ = Γ ⊕ Γ^* with the canonical symmetric bilinear form Q((a_1,b_1),(a_2,b_2)) = b_1(a_2) + b_2(a_1)", and "Cl(Λ,Q) := T(Λ)/<x⊗x = ½Q(x,x)>". Prop. 3.2.1: "(a) Cl(Λ,Q) is a free abelian group of rank 2^{4n} with the basis consisting of monomials x_{j_1}⋯x_{j_s} l_{i_1}⋯l_{i_k} ... (e) The homomorphism σ: Cl(Λ,Q) → End_ℤ(I) is an isomorphism, hence Cl(Λ,Q) ≅ M_{2^{2n}}(ℤ)." Here Γ ≅ ℤ^{2n} and I ≅ ∧Γ^* (3.2.1(d)). §4.3.6 transports (e) to the model this rung uses: "cor_A((l, x))(·) = l(·) + x ∪ (·) ... l(α) := Σ(−1)^{i−1} l(x_i)·x_1∪…∪x_{i−1}∪x_{i+1}∪…∪x_k. By Proposition 3.2.1e) the homomorphism cor_A is an isomorphism." [Markman2025] (quoted in the spin red team, section 1): "m extends an algebra homomorphism m : C(V) → End(S), which is in fact an isomorphism, by [GLO, Prop. 3.2.1(e)]", with m_{(w,θ)} = L_w + D_θ and S = ∧*H¹(X, ℤ).

| Literature | Lean | Agreement |
|---|---|---|
| Γ ≅ ℤ^{2n} free of finite rank; Markman's H¹(X, ℤ) | `[CommRing R] [Module.Free R M] [Module.Finite R M]` | more general (any commutative ring, any finite rank); ℤ and ℚ are instances |
| Λ = Γ ⊕ Γ^*, Q as above, x² = ½Q(x, x) = b(a) | `CliffordAlgebra (QuadraticForm.dualProd R M)` on `Module.Dual R M × M`, `Q (f, x) = f x` | equal; factor order swapped (`Prod.swap`, an isometry, no sign); register row |
| cor_A(l, x) = l(·) + x ∪ (·), l(·) the left interior product with sign (−1)^{i−1}; Markman's L_w + D_θ | `spinAction`, with `spinEquiv_ι_apply : spinEquiv R M (ι _ v) y = contractLeft v.1 y + ExteriorAlgebra.ι R v.2 * y` | equal; Mathlib's `contractLeft_ι_mul` is the same sign rule (`d⌋(ι a * b) = d a • b − ι a * (d⌋b)`) |
| (e): σ, equivalently cor_A or m, is an isomorphism of algebras | `spinAction_bijective`, `spinEquiv : CliffordAlgebra (dualProd R M) ≃ₐ[R] Module.End R (ExteriorAlgebra R M)` | equal |
| (a), rank part: free of rank 2^{4n} = 2^{2·rank Γ} | `finrank_cliffordAlgebra_dualProd : Module.Free R Cl ∧ finrank R Cl = 2 ^ (2 * finrank R M)` | equal, with `Nontrivial R` |
| (a), basis part: the ordered monomials are a basis | spanning only (`span_sublists_prod_eq_top`) | weaker; see finding 6 |
| 4.3.6: "it sends Cl^+ onto H^ev(A×A)"; 3.5.1: I_ℚ = I^ev ⊕ I^odd, the two semispinorial representations | not in this rung; the forward inclusion is checked (`spinAction_mem_evenOdd`) | finding 7 |

GLO identify I with ∧Γ^* through a left ideal of Cl; the Lean statement uses the action on ∧M directly, which is the form of §4.3.6 and of [Markman2025]. The isomorphism is the one the Markman track consumes. An `AlgEquiv` also transports units, which is the form needed to read an element of GL(S) as an element of C(V); which exact consequence [Markman2025] draws from the isomorphism is unverified at page level in this pass.

## 2. Can the hypotheses be satisfied?

Yes. Compiled: `Module.Free ℤ (Fin 2 → ℤ) ∧ Module.Finite ℤ (Fin 2 → ℤ)` and `Module.Free ℚ ℚ ∧ Module.Finite ℚ ℚ ∧ Nontrivial ℚ` by `inferInstance`. `Module.Free.ChooseBasisIndex.fintype` needs only `[Module.Free R M] [Module.Finite R M]` over a semiring, so `spinAction_surjective` can take `Module.Free.chooseBasis` without a `Nontrivial R` split.

**Is each hypothesis needed?**

- `Module.Free`: needed, given `Module.Finite`. Checked in scratch, sorry-free, axioms `[propext, Classical.choice, Quot.sound]`: `¬ Function.Surjective (spinAction ℤ (ZMod 2))`. The dual of `ZMod 2` over ℤ is zero, so every element of the Clifford algebra acts by left multiplication by its value on `1`; the projection onto `⋀¹` sends `1` to `0` and `ι 1` to `ι 1 ≠ 0`. The prover's hand argument is right. Finite projective modules would also do (localize), and that generality is not needed: H¹ of a complex torus is free over ℤ and ℚ. Record it in `docs/gaps.md` as a known weakness.
- `Module.Finite`: needed, but **the sketch's reason is wrong** (finding 1). For `M = ℚ^(ℕ)` the dual is `ℚ^ℕ`, which has dimension 2^{ℵ₀} (Erdős–Kaplansky). So `Cl(Dual × M)` has dimension 2^{ℵ₀}, and `End(∧M) ≅ ∏_{ℕ} ∧M` also has dimension 2^{ℵ₀}; a dimension count separates nothing. A correct argument: an element of the Clifford algebra is a finite sum of products of at most N generators, each generator shifts exterior degree by at most one, so its image maps `⋀^k M` into `⊕_{|j−k| ≤ N} ⋀^j M`. The endomorphism that sends the basis monomial `e_{{0,…,k−1}}` to `e_{{0,…,2k−1}}` and the other basis monomials to `0` has unbounded shift, so it is not in the range. Not compiled.
- `Nontrivial R`: correctly placed. Over the zero ring both sides of the bijection are subsingletons (the prover's scratch); the rank formula reads `1 = 4` there because Mathlib's `Module.finrank_subsingleton` gives `finrank = 1` (compiled: `¬ (finrank (ZMod 1) (ZMod 1) = 2 ^ (2 * finrank (ZMod 1) (ZMod 1)))`).

## 3. Is the conclusion trivially true?

No. Compiled attempts, all failing: on `Function.Bijective (spinAction R M)`, `first | rfl | decide | simp | aesop | (constructor <;> simp) | infer_instance | trivial`; on injectivity, `AlgHom.injective`, `(spinAction R M).toRingHom.injective`, `simp`, `aesop`; on surjectivity, `simp`, `aesop`, `fun y => ⟨_, rfl⟩`; on the rank statement, `simp`, `aesop`, `constructor <;> infer_instance` (no `Module.Free` instance on a Clifford algebra exists at the pin), `omega`, `norm_num`. No `ℕ∞` coercion, no empty index type: `Fin (2 ^ L.length)` is nonempty. The `ZMod 2` counterexample of section 2 shows the conclusion is false once a hypothesis is dropped, so the hypotheses carry weight.

Sub-lemmas checked by hand for truth as stated:

| Declaration | True? | Note |
|---|---|---|
| `ι_mul_mem_sublistSpan` | yes, every Q | four cases on `L = a :: L'`, `l <+ L'` or `l = a :: l'`; the mixed case uses `ι v * ι a = polar Q v a − ι a * ι v` and that `ι a *` maps `sublistSpan Q L'` into `sublistSpan Q (a :: L')` |
| `span_sublists_prod_eq_top`, `exists_surjective_fun_cliffordAlgebra` | yes | the stabilizer of the span is a subalgebra containing `ι v` for `v` in the span of `L`; `1 = prod []` |
| `contractLeft_list_prod_eq_zero` | yes | induction with `contractLeft_ι_mul` |
| `list_prod_contractLeft_coord` | yes, and only with `l.reverse` | a list product in `Module.End` applies its last factor first (`Module.End.mul_apply`), so `l.reverse` applies `coord i₁` first; `Nodup` kills the correction term. Without the reverse, `l = [i₁, i₂]` gives `−1` (hand computation), which differs from `1` when `2 ≠ 0` in `R`; new register row |
| `list_prod_contractLeft_eq_zero` | yes | `j` contractions land in `⋀⁰`, one more gives `contractLeft_algebraMap = 0` |
| `spinAction_list_prod_vec` | yes | `map_list_prod` and `spinAction_ι_vec` |
| `exists_mem_range_apply_basis` | yes | `a_T = c ∘ (e_{I∖T} * ·)`; `u` is the sign of `basis_mul_of_disjoint` for `(I ∖ T, T)` and depends on `T` only, as the quantifier order requires |
| `basis_end_mem_range`, `spinAction_surjective_of_basis`, `spinAction_surjective` | yes | `u • u = 1`; the matrix units are a basis of `End(∧M)` |
| `finrank_end_exteriorAlgebra` | yes | `(2 ^ n) ^ 2 = 2 ^ (2 n)` |
| `finrank_cliffordAlgebra_dualProd` | yes | equals GLO 3.2.1(a), rank part, with `n_GLO = rank M / 2` |

## 4. Interface rung

Not applicable: no structure and no `Prop` hypothesis.

## 5. Checker and axioms

Statement pass: the module is not imported from `HodgeLadder.lean` and has sorried bodies, so there are no axioms to read yet. `lake env lean HodgeLadder/Markman/Chevalley.lean` elaborates in 4.6 s with fourteen `declaration uses 'sorry'` warnings and no errors. `python3 tools/check.py --no-build` in the worktree rejects for a reason unrelated to this rung: the worktree has no build of `HodgeLadder.Normalization.ChartStep` (missing `.olean`). The prover runs the full `python3 tools/check.py` before the rung is posted; the ledger should then name the declarations of the module, including those added under finding 3.

## 6. Conventions

| Convention | Used by | Register | Truth depends on it? |
|---|---|---|---|
| split form `Q (f, x) = f x`, Clifford relation sign +, no factor 2 | the type of `spinAction` and `spinEquiv` | existing row "Clifford relation of the split form"; GLO §3.1 confirms; this pass adds the GLO 4.3.6 confirmation of the contraction sign to that row | well-definedness only; bijectivity is invariant under a unit rescaling of Q (isometric) |
| left contraction sign (−1)^{i−1} | `spinEquiv_ι_apply` | same row | the formula is an equality and depends on it; it is `spinAction_ι_apply` verbatim, with no new sign |
| composition order in `Module.End` | `list_prod_contractLeft_coord` | **new row** (this pass) | the sub-lemma is true only with `l.reverse` |
| sign of a product of exterior basis monomials, `(permOfDisjoint h).sign : ℤˣ` | `exists_mem_range_apply_basis` | **new row** | no: existential, used for range membership only, matching GLO's own "±" (finding 5) |
| `finrank R M = 1` over the zero ring | `finrank_cliffordAlgebra_dualProd` | **new row** | yes: the formula needs `Nontrivial R` |
| factor order `Dual × M` against `Γ ⊕ Γ^*` | everything | existing row | no |

No cited result enters as a hypothesis; the rung uses Mathlib alone.

## 7. Equality first

`spinEquiv` is an identity of algebras, stated exactly (an `AlgEquiv`, with its value on generators `spinEquiv_ι_apply` and the inverse on `spinGen` `spinEquiv_symm_spinGen`). The rank statement is an exact equality. The one existential sign (`u : ℤˣ`) is inside a membership lemma and does not reach a stated identity.

## 7b. Non-vacuity

Smallest test that fails if the conclusion were vacuous or the hypotheses idle: `spinAction_int_zmod_two_not_surjective` (below, compiled sorry-free), which shows the conclusion fails for a finite non-free module, together with the concrete rank `Module.finrank ℤ (CliffordAlgebra (QuadraticForm.dualProd ℤ ℤ)) = 4` (compiled from the sorried `finrank_cliffordAlgebra_dualProd`). Neither exists in the module yet (finding 3). The sketch's sentence "the rank corollary is the non-vacuity test of injectivity: it fails if `spinAction` had a kernel" overstates: the rank of the Clifford algebra is an independent classical fact (GLO 3.2.1(a)), so the corollary checks the route end to end and does not by itself detect a kernel of a different map. Reword (finding 4).

## 8. Pin drift

None: the branch has the pin of `main`. Nothing from `Paul-Lez/HodgeConjecture` is used. On a Mathlib bump, recheck `contractLeft_ι_mul`'s sign, `QuadraticForm.dualProd`'s `toFun`, `basis_mul_of_disjoint`'s statement (it is recent Mathlib code, 2026, indexed by `powersetCard`), and `Module.finrank_subsingleton`.

## 9. Verdict: pass with changes

1. **Sketch, `Module.Finite` row: wrong reason.** Replace "the Clifford algebra has countable dimension and `End(∧M)` uncountable dimension" by the bounded-degree-shift argument of section 2: `Dual ℚ ℚ^(ℕ) ≅ ℚ^ℕ` has dimension 2^{ℵ₀}, so both sides have dimension 2^{ℵ₀}. The hypothesis stays.
2. **Route: sound, and it is GLO's proof.** GLO prove 3.2.1(e) by rank plus surjectivity, with "x_h l x_{p'} (x_m l) = ± x_h l if p = m, 0 otherwise", which is the sketch's `E_{S,T} = u • ((e_S * ·) ∘ c ∘ (e_{I∖T} * ·))` with the same unspecified sign. GLO take the rank from 3.2.1(a) ("standard"); the route replaces (a) by spanning plus the Orzech property and gets the rank back as a corollary, which avoids a basis theorem Mathlib lacks. Keep it. The kill criterion (about 300 lines in step 2 because of `powersetCard`) is sensible; add the mitigation to try first: one bridging lemma that writes `b.ExteriorAlgebra U` as `((U.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι R (b i)).prod`, so the rest of step 2 works with lists and `basis_mul_of_disjoint` is the only place a `powersetCard` coercion appears.
3. **Add two tests to the module and name them in the ledger.** Compiled in module form against the file's imports; the first has axioms `[propext, Classical.choice, Quot.sound]`.

   ```lean
   /-- Over `ℤ`, the dual of `ZMod 2` is zero. -/
   theorem dual_int_zmod_two_eq_zero (φ : Module.Dual ℤ (ZMod 2)) : φ = 0 := by
     ext x
     have h2 : (2 : ℤ) • x = 0 := by revert x; decide
     have : (2 : ℤ) * φ x = 0 := by rw [← smul_eq_mul, ← map_smul, h2, map_zero]
     simp only [LinearMap.zero_apply]
     omega

   /-- For `M = ZMod 2` over `ℤ` every element of the Clifford algebra acts by left
   multiplication by its value on `1`. -/
   theorem spinAction_int_zmod_two_apply
       (x : CliffordAlgebra (QuadraticForm.dualProd ℤ (ZMod 2))) (y : ExteriorAlgebra ℤ (ZMod 2)) :
       spinAction ℤ (ZMod 2) x y = spinAction ℤ (ZMod 2) x 1 * y := by
     induction x using CliffordAlgebra.induction generalizing y with
     | algebraMap r =>
       rw [AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
         smul_mul_assoc, one_mul]
     | ι v =>
       obtain ⟨f, m⟩ := v
       rw [dual_int_zmod_two_eq_zero f, spinAction_ι_apply, spinAction_ι_apply]
       simp
     | mul a b ha hb =>
       rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha, ha (spinAction _ _ b 1),
         mul_assoc]
     | add a b ha hb =>
       rw [map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb, add_mul]

   /-- **`Module.Free` cannot be dropped.** For the finite, non-free `ℤ`-module `ZMod 2` the
   action is not surjective: the projection onto `⋀¹` is not left multiplication by an element. -/
   theorem spinAction_int_zmod_two_not_surjective :
       ¬ Function.Surjective (spinAction ℤ (ZMod 2)) := by
     intro hs
     let T := GradedAlgebra.proj (fun i : ℕ => ⋀[ℤ]^i (ZMod 2)) 1
     obtain ⟨x, hx⟩ := hs T
     have h1 : T 1 = 0 := by
       simp only [T, GradedAlgebra.proj_apply]
       rw [DirectSum.decompose_of_mem_ne _ SetLike.GradedOne.one_mem (by decide : (0 : ℕ) ≠ 1)]
     have hι : (ExteriorAlgebra.ι ℤ (1 : ZMod 2)) ∈ ⋀[ℤ]^1 (ZMod 2) := by
       simp only [ExteriorAlgebra.exteriorPower, pow_one]; exact LinearMap.mem_range_self _ _
     have h2 : T (ExteriorAlgebra.ι ℤ 1) = ExteriorAlgebra.ι ℤ 1 := by
       simp only [T, GradedAlgebra.proj_apply]
       exact DirectSum.decompose_of_mem_same _ hι
     have h3 := spinAction_int_zmod_two_apply x (ExteriorAlgebra.ι ℤ 1)
     rw [hx, h1, zero_mul, h2, ExteriorAlgebra.ι_eq_zero_iff] at h3
     exact absurd h3 (by decide)

   /-- Concrete rank: the Clifford algebra of the split form on `ℤ^∨ × ℤ` has rank `4`. -/
   theorem finrank_cliffordAlgebra_dualProd_int :
       Module.finrank ℤ (CliffordAlgebra (QuadraticForm.dualProd ℤ ℤ)) = 4 := by
     rw [(finrank_cliffordAlgebra_dualProd ℤ ℤ).2, Module.finrank_self]; norm_num
   ```

   Keep `dual_int_zmod_two_eq_zero` a theorem; a global `Subsingleton` instance on a Mathlib type is not needed.
4. **Reword the non-vacuity sentence** in the sketch and the ledger note: the rank corollary is GLO 3.2.1(a) (rank part) as a consequence; the hypothesis-necessity test is `spinAction_int_zmod_two_not_surjective`.
5. **Sign `u : ℤˣ`: keep it existential.** It matches GLO's "±", it is consumed only by `basis_end_mem_range`, whose statement carries no sign, and no planned rung uses an explicit Clifford preimage of a matrix unit. A later rung that needs explicit preimages (for example the Mukai pairing as a Clifford element) states its own sign and adds a register row.
6. **Optional strengthening, same rung or a new one:** GLO 3.2.1(a) at full strength, that the sublist products of the list `L` built from a basis form a basis of the Clifford algebra. It falls out of the injectivity step (the surjection `φ` from `Fin (2 ^ (2 n)) → R` is bijective by the Orzech property applied to `φ` itself, once the rank is known), so it costs a few lines. Name it, for example, `linearIndependent_sublists_prod_dualProd`.
7. **Graded form: a new rung, not this one.** GLO 4.3.6 ("it sends Cl^+ onto H^ev") and 3.5.1 (the two semispinorial representations) use the graded statement, and the Markman track's Spin(V) acts through the even part on S⁺ and S⁻. The inclusion is checked (`spinAction_mem_evenOdd`). Open `clifford-exterior-half-spin`, depending on this rung, with the equality form first and the product decomposition second. These elaborate at the pin (scratch, `sorry` bodies; the third needs `public import Mathlib.LinearAlgebra.CliffordAlgebra.Even`):

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

   The reverse direction of the first is short given this rung: write `x = x₀ + x₁`; the action of `x₁` maps each parity part into both parities, hence to `0` (`evenOdd_isCompl` on `∧M`), so `spinAction x₁ = 0` and `x₁ = 0` by injectivity. Irreducibility and inequivalence of S⁺ and S⁻ over ℚ (GLO 3.5.1) is a further step.
8. **Naming: keep `spinEquiv`.** With this rung checked, "spin" is earned (spin red team, finding 7), and `spinEquiv` reads as the equivalence built from `spinAction`. No collision in the repository or in Mathlib's `CliffordAlgebra` directory. `cliffordDualProdEquivEnd` is the name to use if the declaration goes to Mathlib.
9. **Chevalley's second isomorphism is a separate target.** The Markman inventory row cites "Chevalley S ⊗ S ≅ ∧*V"; that statement needs this rung plus the Mukai (Chevalley) pairing on S and a normal-ordering identification `Cl(V) ≅ ∧V` of modules. It is not implied by this rung's title; record it as a future rung when the Markman track reaches it.

Attempts that failed: trivializing bijectivity, injectivity, surjectivity or the rank statement (section 3); finding an idle hypothesis (each is needed, with a compiled counterexample for `Module.Free` and for `Nontrivial R` in the rank formula); finding a sign in `spinEquiv_ι_apply` beyond the registered one (it is `spinAction_ι_apply` verbatim).
