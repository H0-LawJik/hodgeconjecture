# Red team: `clifford-exterior-half-spin` (statement pass)

Date: 2026-11-26. Branch `track/clifford-exterior-half-spin` from `main` at `62a6c1d`; `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` have no diff against `main` (pin `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`). Target: `HodgeLadder/Markman/HalfSpin.lean` (uncommitted, two `sorry` bodies) and the section "clifford-exterior-half-spin: statement" of `docs/sketches/clifford-exterior-chevalley.md`, before the two remaining proofs. Inputs read: the ledger entries `clifford-exterior-spin`, `clifford-exterior-chevalley`, `clifford-exterior-half-spin` and `markman-statement`; `HodgeLadder/Markman/CliffordSpin.lean` and `Chevalley.lean`; `docs/sketches/clifford-exterior-chevalley.redteam.md` (finding 7); the register rows "Clifford relation of the split form" and "Chevalley isomorphism"; `docs/references.md`; the Markman inventory 2026-11-25; Mathlib at the pin for `evenOdd_isCompl`, `even.ι`, `changeForm`, `changeForm_ι_mul_ι`, `left_induction`, `liftAlternating`. Literature opened this pass: the arXiv source of [GolyshevLuntsOrlov2001] (math/9812003), §3.2.1(c), §3.4.1, §3.5.1, §4.3.6; [Markman2025] (arXiv:2502.03415 v2), §2.1 and §2.2. Scratch files were compiled with `lake env lean` inside the worktree and deleted afterwards; the only build product left is the worktree's own `HalfSpin.olean`.

**Verdict: pass with changes.** The targets state the literature's half-spin theorem at full strength over any commutative ring, in the form [Markman2025] consumes, and the map form is [GolyshevLuntsOrlov2001] 4.3.6 verbatim. The route is sound. The prover's open question on `Module.Free` has an answer: it is needed for the iff, with a compiled counterexample over `ZMod 4`; the same module shows `spinActionEven` is not injective without it. The changes add that test, generalize the iff to an injectivity hypothesis (a strengthening with the same proof), add three short corollaries, and correct one row of the sketch. No target statement is weakened.

## 1. Is this the statement the literature makes?

[GolyshevLuntsOrlov2001] §3.2.1(c), source: "`Cl(Λ,Q)` is a `ℤ_2`-graded algebra, `Cl(Λ,Q)=Cl^{+}(Λ,Q)⊕Cl^{-}(Λ,Q)`, where `Cl^{+}(Λ,Q)` (resp. `Cl^{-}(Λ,Q)`) is the span of monomials with even (resp. odd) number of elements." §4.3.6: "`cor_A: Cl(Λ, Q) → End(H^*(A, ℤ)) ≅ H^{*}(A×A, ℤ)` ... By Proposition 3.2.1e) the homomorphism `cor_A` is an isomorphism. [...] it sends `Cl^{+}(Λ, Q)` onto `H^{ev}(A×A, ℤ)`." §3.5.1: "`Spin_ℚ(Λ_ℚ,Q_ℚ)` is a subgroup of the multiplicative group `Cl^+(Λ_ℚ, Q_ℚ)^*` ... It is a direct sum of two (nonequivalent) irreducible semispinorial representations `I_ℚ=I_ℚ^{ev} ⊕ I_ℚ^{odd}`."

[Markman2025] §2.1: "S := H^∗(X, Z) is the Spin representation and S^+ := H^ev(X, Z) and S^− := H^odd(X, Z) are its two half-spin subrepresentations"; "m : C(V) → End(S), which is in fact an isomorphism, by [GLO, Prop. 3.2.1(e)]"; "Spin(V) := {x ∈ C(V)^even : x · x^∗ = 1 and x · V · x^∗ ⊂ V}"; "An element x ∈ C(V)^odd is mapped via (2.1.3) to an endomorphism m_x of S, which maps S^+ to S^− and S^− to S^+." §2.2 uses `m_w : V → S^−` for `w ∈ S^+` and the stabilizer in Spin(V) of a plane `P ⊂ S^+_ℚ`.

| Literature | Lean | Agreement |
|---|---|---|
| `Cl^+`, `Cl^-` = span of monomials with an even, odd number of vectors (GLO 3.2.1(c)); Markman's `C(V)^even`, `C(V)^odd` | `evenOdd (dualProd R M) i`; `CliffordAlgebra.even` with `even_toSubmodule : (even Q).toSubmodule = evenOdd Q 0` | equal |
| `H^ev`, `H^odd` of `H^*(X) = ∧^*H^1(X)`; GLO's `I^{ev}`, `I^{odd}` (monomials `x_{j_1}⋯x_{j_s} l_1⋯l_{2n}` with `s` even, odd) | `exteriorParity R M j = ⨆ (k ≡ j), ⋀[R]^k M` | equal; new register row for the labels |
| `End(H^*(A)) ≅ H^*(A×A)`, `H^{ev}(A×A)` the parity-preserving endomorphisms (Poincaré duality on `H^*(A)` shifts degree by the even number `2g`) | `parityShift R M i := ⨅ j, compatibleMaps (exteriorParity j) (exteriorParity (j + i))` | equal for `i = 0`; `i = 1` is the odd half, which GLO leave implicit |
| "`cor_A` sends `Cl^+` onto `H^{ev}(A×A)`" | `map_evenOdd_dualProd_eq_parityShift : (evenOdd Q i).map spinAction = parityShift R M i` | equal (GLO's "onto" is the `map` form), and for both parities |
| odd elements swap `S^+` and `S^-` (Markman) | forward half of `spinAction_mem_evenOdd_one_iff` (checked as `spinAction_mem_exteriorParity`) | equal |
| `Cl^+ ≅ End(S^+) × End(S^-)` (standard structure of the even Clifford algebra of a split form; not written in GLO or Markman, equivalent there to "onto `H^{ev}`" plus injectivity) | `spinEquivEven : even (dualProd R M) ≃ₐ[R] End(exteriorParity 0) × End(exteriorParity 1)`, `AlgEquiv.ofBijective` of the restriction map | equal |
| Γ free of finite rank over ℤ (GLO), `H^1(X, ℤ)` (Markman) | `[CommRing R] [Module.Free R M] [Module.Finite R M]` | more general; ℤ and ℚ are instances |
| GLO 3.5.1: `I^{ev}`, `I^{odd}` irreducible and nonequivalent under `Spin_ℚ` | not in this rung | a further step (finding 9) |

Full strength: yes. The iff for each `i`, the `map` equality for each `i` and the algebra isomorphism together are the whole graded form of Chevalley's theorem. One piece is left implicit: the odd analog `Cl^- ≅ Hom(S^+, S^-) × Hom(S^-, S^+)` as a product of modules. It is the `i = 1` map equality plus injectivity, and the Markman track needs it only through its forward half; no change.

Markman at page level (the sketch's question 3 left it unverified): §2.1 reads Spin(V) inside `GL(S)` (`m : Spin(V) → GL(S)`, (5.2.1)) and uses the two half-spin subrepresentations separately. It states no product `GL(S^+) × GL(S^-)`. The restriction maps `spinActionParity R M j` are the form it uses.

## 2. Can the hypotheses be satisfied?

Yes: `M = ℤ^n` and `M = ℚ^n` (red team of `clifford-exterior-chevalley`, section 2, compiled). The tests compile against the file's imports.

**Is each hypothesis needed?**

- **`Module.Free` for the iff: needed, given `Module.Finite`.** The sketch says no counterexample is known. Here is one, compiled sorry-free, axioms `[propext, Classical.choice, Quot.sound]` (Lean in finding 2). Let `R = ZMod 4` and `M = (2) ⊆ ZMod 4`, the ideal as an `R`-module (finite, cyclic of order two). Take `m₀ = 2 ∈ M` and `f₀ = M.subtype ∈ Module.Dual R M`, so `f₀ m₀ = 2` and `f₀ m • m₀ = 0` for every `m`. The element `x = ι (0, m₀) * ι (f₀, 0)` is even and acts on `∧M` by `y ↦ ι m₀ * (f₀ ⌋ y)`, which is `0` (induction on `y`, using `f₀ m • ι m₀ = 0` and anticommutation). It is nonzero: `changeForm` to the zero form with `B (v, w) = −w.1 v.2` sends it to `ι u * ι e − algebraMap (B u e)`, and the alternating map `ω v = (v 0).1 (v 1).2 − (v 1).1 (v 0).2` in degree two, through `ExteriorAlgebra.liftAlternating`, evaluates it to `−f₀ m₀ = 2 ≠ 0`. So `x` acts by `0`, which shifts parity by `1`, and `x ∉ evenOdd 1` because `x ∈ evenOdd 0` and `x ≠ 0`. The reverse direction of `spinAction_mem_evenOdd_one_iff` fails. The same `x` shows `spinAction` and `spinActionEven` are not injective, and, through the checked `spinAction_bijective`, that `M` is not free.

  The `ZMod 2` over `ℤ` example in the sketch is right that the action is faithful there; it fails only surjectivity.

  More precisely, the iff for both `i` is equivalent to injectivity of `spinAction`, for every `R` and `M`. One direction is the route. For the other, the kernel is graded (if `spinAction (a + b) = 0` with `a` even and `b` odd, then on each parity part `spinAction a y` and `spinAction b y` lie in complementary parity parts and sum to `0`), and a nonzero kernel element of parity `i + 1` violates the iff at `i`. Hand argument, statement compiled (finding 3).

- **`Module.Finite` for the iff: used by the route only through injectivity.** Over a field, `spinAction` is injective for every vector space (hand argument, not compiled): an element of the Clifford algebra involves finitely many generators `(f_k, m_k)`; split `M = F ⊕ G` with `F` finite-dimensional containing the `m_k` and `G ⊆ ⋂ ker f_k`; then the element comes from `Cl(F^∨ × F)` and acts on `∧F ⊆ ∧M` through the finite Chevalley isomorphism. So over a field the iff holds without `Module.Finite`. For free modules of infinite rank over a general ring this pass did not settle it (a functional need not vanish on a free complement of a finite free summand). Finding 3 makes the question moot by stating the iff under `Function.Injective (spinAction R M)`.

- **`Module.Free` for `spinEquivEven`: needed.** Surjectivity: the checked `spinActionEven_int_zmod_two_not_surjective`. Injectivity: `spinActionEven_zmod_four_not_injective` above.

- **`Module.Finite` for `spinEquivEven`: needed; the sketch's reason is right.** Every Clifford element is a finite sum of products of at most `N` generators, each shifting exterior degree by at most one, so `spinActionParity 0 x` maps `⋀^k M` into `⊕_{|j − k| ≤ N} ⋀^j M`. For `M = ℚ^(ℕ)` the endomorphism of `∧^{ev} M` that sends `e_{{0, …, 2k−1}}` to `e_{{0, …, 4k−1}}` and the other basis monomials to `0` has unbounded shift, so `(φ, 0)` is not in the range. Injectivity holds there (field case above), so only surjectivity fails. Not compiled.

- **`Nontrivial R`: correctly omitted.** Over the zero ring every type in sight is a subsingleton; no rank appears in any target.

## 3. Is the conclusion trivially true?

No. No definition unfolds to `True`: `parityShift` is a genuine infimum of `compatibleMaps`, `mem_parityShift` is its `rfl` unfolding. `exteriorParity 0 ≠ exteriorParity 1` for `M ≠ 0` free (`ι_not_mem_exteriorParity_zero`), and `ZMod 2` has two elements, so no index type is empty and no parity condition is vacuous. The iff fails for a finite module (section 2), so it carries content beyond the checked forward inclusion.

Compiled attempts, all failing: on the general iff, `simp [exteriorParity_eq_evenOdd]`, `constructor <;> intro h <;> simp_all [exteriorParity_eq_evenOdd]`, and the forward direction from `spinAction_mem_exteriorParity` with `simpa` for the reverse. On `spinActionEven_bijective`, `constructor <;> aesop` and `⟨fun a b h => Subtype.ext (by simpa [spinActionEven] using h), fun p => ⟨1, by simp⟩⟩`. These add to the prover's list in the sketch.

Docstrings checked against statements: all match. `spinActionParity` and `spinActionEven` carry no `sorry` (the `ZMod 4` test about `spinActionEven` has standard axioms only), so the data `spinEquivEven` wraps is honest; only its bijectivity is open.

## 4. Interface rung

Not applicable: no structure and no `Prop` hypothesis.

## 5. Checker and axioms

Statement pass. `lake env lean HodgeLadder/Markman/HalfSpin.lean`: 5.3 s, two `declaration uses 'sorry'` warnings (lines 69 and 148), no errors. `python3 tools/check.py --no-build` in the worktree: every ledger declaration accepted with the three standard axioms; one rejection, the sorry scan at `HalfSpin.lean:74` and `:150`, as expected before the proofs. When the rung is posted, the ledger should name every declaration of the module including the tests of finding 2, and the prover runs the full `python3 tools/check.py`.

## 6. Conventions

| Convention | Used by | Register | Truth depends on it? |
|---|---|---|---|
| split form `Q (f, x) = f x`, relation sign +, left contraction sign `(−1)^{i−1}` | `spinAction` and everything built on it; `spinEquivEven_ι_mul_ι_fst` | existing row "Clifford relation of the split form" | the sign is forced by well-definedness (a minus sign gives no Clifford action of `dualProd`); the parity statements and the isomorphism are insensitive to it |
| composition order in `Module.End` | `spinEquivEven_ι_mul_ι_fst`: `ι v * ι w` acts as `spinGen v ∘ spinGen w`, `w` first | existing row "Chevalley isomorphism: composition order" | yes for that sanity lemma, and it is stated in the right order |
| Clifford parity = number of generators mod 2; `S^+ = exteriorParity 0` (exterior degree counted in `M`); `parityShift i` maps parity `j` into `j + i`; `spinEquivEven` lists the `S^+` component first | every target | **new row** (this pass) | no for `j + i` against `i + j`; yes for which component `spinEquivEven_apply_fst` names |
| `End(H^*(A)) ≅ H^*(A×A)` (GLO 4.3.6) | the literature comparison only | recorded in the new row | the parity match uses that Poincaré duality shifts degree by `2g`, an even number |

No cited result enters as a hypothesis; the rung uses Mathlib and two checked modules. The literature's normalizations were confirmed against the definitions they are compared with: GLO's `Cl^+` (monomial count) is `evenOdd Q 0`, Markman's `S^+ = H^ev` is `exteriorParity 0`, Markman's `C(V)^even` is `CliffordAlgebra.even`.

## 7. Equality first

`map_evenOdd_dualProd_eq_parityShift` is an equality of submodules, stated exactly for both parities, and `spinEquivEven` is an `AlgEquiv` whose value is `rfl` (`spinEquivEven_apply`). No scalar and no sign appear. The iff is the membership form of the `comap` equality (finding 4). Nothing here is an inclusion standing in for an identity; the checked `spinAction_mem_evenOdd` was the inclusion and this rung is the equality it was a step toward.

## 7b. Non-vacuity

Smallest tests that fail if the statements were trivially true:

| Test | What it detects | Status |
|---|---|---|
| `spinActionEven_int_zmod_two_not_surjective` | surjectivity half needs `Module.Free` | in the module, proved |
| `evenOdd_one_iff_zmod_four_fails` (finding 2) | the reverse direction of the iff is not automatic; `Module.Free` is needed for it | compiled in scratch, to add |
| `spinActionEven_zmod_four_not_injective` (finding 2) | injectivity half needs `Module.Free` | compiled in scratch, to add |
| `ι_vec_not_mem_evenOdd_zero_int` (finding 6) | the even condition rejects a generator: `ι (0, 1)` over `ℤ` is not even, through its action | compiled in scratch, to add |

## 8. Pin drift

None: the branch has the pin of `main`, and nothing from `Paul-Lez/HodgeConjecture` is used. On a Mathlib bump, recheck `CliffordAlgebra.evenOdd_isCompl`, `even_toSubmodule`, `Submodule.compatibleMaps`, `Submodule.linearProjOfIsCompl`, and the items listed in the Chevalley red team, section 8.

## 9. Verdict: pass with changes

1. **Route: sound.** Iff, reverse direction: write `x = a + b` with `a ∈ evenOdd i`, `b ∈ evenOdd (i + 1)` (`evenOdd_isCompl` gives only the pair `0, 1`, so `fin_cases i` and use `.symm` for `i = 1`). For `y ∈ exteriorParity j`, `spinAction b y = spinAction x y − spinAction a y` lies in parity `j + i` and, by `spinAction_mem_exteriorParity`, in parity `(i + 1) + j`; these are complementary (`evenOdd_isCompl (0 : QuadraticForm R M)` through `exteriorParity_eq_evenOdd`), so it is `0`. The two parity parts span `∧M` (`sup_eq_top`, `Submodule.mem_sup`), so `spinAction b = 0` and `b = 0` by injectivity. Bijectivity: injective because `spinAction (x − x')` vanishes on both parity parts; surjective because for `(f₀, f₁)` the operator `p₀.subtype ∘ f₀ ∘ π₀ + p₁.subtype ∘ f₁ ∘ π₁` (`Submodule.linearProjOfIsCompl` and `linearProjOfIsCompl_apply_left`, `_right`) lies in `parityShift 0`, so its `spinAction_surjective` preimage is even by `spinAction_mem_evenOdd_zero_iff`, giving an element of `even Q` through `even_toSubmodule`, and its restrictions are `f₀`, `f₁`.

2. **Add the `Module.Free` test for the iff and for injectivity.** Compiled against the module (with `public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating` added), sorry-free, axioms `[propext, Classical.choice, Quot.sound]` for every declaration. Rename freely; put it in the `Tests` section.

   ```lean
   /-- The ideal `(2)` of `ZMod 4`, a finite `ZMod 4`-module that is not free. -/
   abbrev zmodFourIdeal : Submodule (ZMod 4) (ZMod 4) := Submodule.span (ZMod 4) {2}

   /-- The generator `2` of `zmodFourIdeal`. -/
   abbrev zmodFourGen : zmodFourIdeal := ⟨2, Submodule.mem_span_singleton_self 2⟩

   /-- The inclusion of `zmodFourIdeal`, a covector with value `2` on the generator. -/
   abbrev zmodFourCovector : Module.Dual (ZMod 4) zmodFourIdeal := zmodFourIdeal.subtype

   /-- `zmodFourCovector m • zmodFourGen = 0` for every `m`: the covector takes values in `(2)`. -/
   theorem zmodFourCovector_smul_gen (m : zmodFourIdeal) : zmodFourCovector m • zmodFourGen = 0 := by
     obtain ⟨m, hm⟩ := m
     obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
     ext
     simp only [Submodule.subtype_apply, SetLike.mk_smul_mk, smul_eq_mul, Submodule.coe_zero]
     clear hm; revert c; decide

   /-- The even element `ι (0, 2) * ι (incl, 0)` acts by zero on `∧ zmodFourIdeal`. -/
   theorem spinAction_zmodFour_kernel :
       spinAction (ZMod 4) zmodFourIdeal
         (ι _ (0, zmodFourGen) * ι _ (zmodFourCovector, 0)) = 0 := by
     refine LinearMap.ext fun y => ?_
     rw [map_mul, Module.End.mul_apply, spinAction_ι_dual, spinAction_ι_vec, LinearMap.zero_apply]
     induction y using CliffordAlgebra.left_induction with
     | algebraMap r => rw [contractLeft_algebraMap, mul_zero]
     | add a b ha hb => rw [map_add, mul_add, ha, hb, add_zero]
     | ι_mul y m hy =>
       rw [contractLeft_ι_mul, mul_sub, mul_smul_comm, ← smul_mul_assoc, ← map_smul,
         zmodFourCovector_smul_gen, map_zero, zero_mul, zero_sub, ← mul_assoc,
         eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ZMod 4) zmodFourGen m),
         neg_mul, mul_assoc]
       change -(-(ExteriorAlgebra.ι (ZMod 4) m *
         (ExteriorAlgebra.ι (ZMod 4) zmodFourGen * contractLeft zmodFourCovector y))) = 0
       rw [hy, mul_zero, neg_zero, neg_zero]

   /-- The bilinear form `(v, w) ↦ w.1 v.2`, whose diagonal is `dualProd`. -/
   def zmodFourPairing : LinearMap.BilinForm (ZMod 4) (Module.Dual (ZMod 4) zmodFourIdeal × zmodFourIdeal) :=
     ((LinearMap.applyₗ).comp (LinearMap.snd (ZMod 4) _ _)).compl₂ (LinearMap.fst (ZMod 4) _ _)

   theorem zmodFourPairing_toQuadraticMap :
       (-zmodFourPairing).toQuadraticMap = 0 - QuadraticForm.dualProd (ZMod 4) zmodFourIdeal := by
     ext v
     simp [zmodFourPairing]

   /-- The alternating pairing `(v 0).1 (v 1).2 − (v 1).1 (v 0).2` on `Dual × M`. -/
   def zmodFourAlt : (Module.Dual (ZMod 4) zmodFourIdeal × zmodFourIdeal) [⋀^Fin 2]→ₗ[ZMod 4] ZMod 4 where
     toFun v := (v 0).1 (v 1).2 - (v 1).1 (v 0).2
     map_update_add' v i x y := by fin_cases i <;> simp <;> ring
     map_update_smul' v i c x := by fin_cases i <;> simp <;> ring
     map_eq_zero_of_eq' v i j h hij := by fin_cases i <;> fin_cases j <;> simp_all

   /-- `zmodFourAlt` in degree two, zero in the other degrees. -/
   def zmodFourAlts : ∀ i, (Module.Dual (ZMod 4) zmodFourIdeal × zmodFourIdeal) [⋀^Fin i]→ₗ[ZMod 4] ZMod 4
     | 2 => zmodFourAlt
     | _ => 0

   /-- The kernel element is nonzero: change the form to `0` and evaluate the degree-two part. -/
   theorem zmodFour_kernel_ne_zero :
       (ι _ (0, zmodFourGen) * ι _ (zmodFourCovector, 0) :
         CliffordAlgebra (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)) ≠ 0 := by
     intro h
     have h1 := congrArg
       (fun z => ExteriorAlgebra.liftAlternating zmodFourAlts (changeForm zmodFourPairing_toQuadraticMap z)) h
     simp only [changeForm_ι_mul_ι, map_zero, map_sub] at h1
     rw [ExteriorAlgebra.liftAlternating_algebraMap, ExteriorAlgebra.liftAlternating_ι_mul,
       ExteriorAlgebra.liftAlternating_ι] at h1
     change zmodFourAlt ![(0, zmodFourGen), (zmodFourCovector, 0)] - _ • (0 : ZMod 4) = 0 at h1
     simp [zmodFourAlt] at h1
     revert h1; decide

   /-- **`Module.Free` cannot be dropped from injectivity.** -/
   theorem spinAction_zmodFour_not_injective :
       ¬ Function.Injective (spinAction (ZMod 4) zmodFourIdeal) :=
     fun hinj => zmodFour_kernel_ne_zero (hinj (by rw [spinAction_zmodFour_kernel, map_zero]))

   /-- **`Module.Free` cannot be dropped from the parity iff.** For the finite module
   `zmodFourIdeal` a nonzero even element acts by zero, so it shifts parity by one without
   being odd. -/
   theorem evenOdd_one_iff_zmod_four_fails :
       ¬ ∀ x : CliffordAlgebra (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal),
         x ∈ evenOdd (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal) 1 ↔
           ∀ (j : ZMod 2) (y : ExteriorAlgebra (ZMod 4) zmodFourIdeal),
             y ∈ exteriorParity (ZMod 4) zmodFourIdeal j →
               spinAction (ZMod 4) zmodFourIdeal x y ∈ exteriorParity (ZMod 4) zmodFourIdeal (j + 1) := by
     intro h
     have h1 := (h (ι _ (0, zmodFourGen) * ι _ (zmodFourCovector, 0))).mpr (fun j y _ => by
       rw [spinAction_zmodFour_kernel, LinearMap.zero_apply]; exact Submodule.zero_mem _)
     have h0 := ι_mul_ι_mem_evenOdd_zero (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)
       (0, zmodFourGen) (zmodFourCovector, 0)
     exact zmodFour_kernel_ne_zero ((Submodule.disjoint_def.mp (evenOdd_isCompl _).disjoint) _ h0 h1)

   /-- **`Module.Free` cannot be dropped from the injectivity of `spinActionEven`.** -/
   theorem spinActionEven_zmod_four_not_injective :
       ¬ Function.Injective (spinActionEven (ZMod 4) zmodFourIdeal) := by
     intro hinj
     have h : spinActionEven (ZMod 4) zmodFourIdeal
         ((even.ι (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)).bilin
           (0, zmodFourGen) (zmodFourCovector, 0)) = 0 := by
       have hk : (((even.ι (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)).bilin
           (0, zmodFourGen) (zmodFourCovector, 0) :
             even (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)) :
               CliffordAlgebra (QuadraticForm.dualProd (ZMod 4) zmodFourIdeal)) =
             ι _ (0, zmodFourGen) * ι _ (zmodFourCovector, 0) := rfl
       ext y <;> simp [spinActionEven, hk, spinAction_zmodFour_kernel]
     exact zmodFour_kernel_ne_zero (congrArg Subtype.val (hinj (h.trans (map_zero _).symm)))
   ```

   This block was recompiled verbatim in namespace `HodgeLadder` with `open CliffordAlgebra` (4.4 s); five lines exceed 100 characters and need wrapping. A corollary costs two lines and is worth stating (compiled, standard axioms):

   ```lean
   /-- So `zmodFourIdeal` is not free. -/
   theorem not_free_zmodFourIdeal : ¬ Module.Free (ZMod 4) zmodFourIdeal := fun _ =>
     spinAction_zmodFour_not_injective (spinAction_bijective (ZMod 4) zmodFourIdeal).1
   ``` Record in `docs/gaps.md` next to the Chevalley row: the finite non-projective module `(2) ⊆ ZMod 4` breaks injectivity, which is consistent with "finite projective would also work".

3. **Strengthen the iff to an injectivity hypothesis (same proof).** The route uses `Module.Free` and `Module.Finite` only through `(spinAction_bijective R M).1`. State the general form and derive the posted one; this is a stronger statement, and it applies to every vector space over a field (section 2) and to `ZMod 2` over `ℤ`. Both statements compiled (sorry body for the first):

   ```lean
   theorem spinAction_mem_evenOdd_iff_of_injective (hinj : Function.Injective (spinAction R M))
       (i : ZMod 2) (x : CliffordAlgebra (QuadraticForm.dualProd R M)) :
       x ∈ evenOdd (QuadraticForm.dualProd R M) i ↔
         ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
           spinAction R M x y ∈ exteriorParity R M (j + i)

   theorem spinAction_mem_evenOdd_iff [Module.Free R M] [Module.Finite R M] (i : ZMod 2)
       (x : CliffordAlgebra (QuadraticForm.dualProd R M)) : ... :=
     spinAction_mem_evenOdd_iff_of_injective R M (spinAction_bijective R M).1 i x
   ```

   Optional, same rung or later: the converse, which makes the iff exactly the injectivity of the action (hand argument in section 2; statement compiled):

   ```lean
   theorem injective_spinAction_iff :
       Function.Injective (spinAction R M) ↔
         ∀ (i : ZMod 2) (x : CliffordAlgebra (QuadraticForm.dualProd R M)),
           (x ∈ evenOdd (QuadraticForm.dualProd R M) i ↔
             ∀ (j : ZMod 2) (y : ExteriorAlgebra R M), y ∈ exteriorParity R M j →
               spinAction R M x y ∈ exteriorParity R M (j + i))
   ```

4. **Question 1, `map` or `comap`: keep `map` as the headline and add `comap` as a corollary.** The `map` form is GLO 4.3.6's "sends `Cl^+` onto `H^{ev}`" and records surjectivity onto `parityShift i`; the `comap` form is the iff as an equality and holds under injectivity alone. Compiled from the sorried iff:

   ```lean
   /-- **The grading, preimage form.** -/
   theorem evenOdd_dualProd_eq_comap_parityShift [Module.Free R M] [Module.Finite R M]
       (i : ZMod 2) :
       evenOdd (QuadraticForm.dualProd R M) i =
         (parityShift R M i).comap (spinAction R M).toLinearMap := by
     ext x
     rw [Submodule.mem_comap, mem_parityShift]
     exact spinAction_mem_evenOdd_iff R M i x
   ```

5. **Question 2, `j + i` or `i + j`: keep `j + i`.** It matches the posted `_one_iff` (`j + 1`) and the reading of `parityShift` ("shift `j` by `i`"), and `_zero_iff` closes by `simpa` (`add_zero`). The forward direction costs one `add_comm` against the checked `spinAction_mem_exteriorParity` (`i + j`). Truth does not depend on it; recorded in the new register row.

6. **Question 3, separate surjective components: add them; the units form is optional.** Markman uses `S^+` and `S^-` separately (Spin(V) acting on `S^+`, stabilizers of planes in `S^+_ℚ`), so the restriction maps should be stated surjective on their own. Compiled from the sorried bijectivity:

   ```lean
   /-- Each half-spin component is surjective. -/
   theorem spinActionParity_surjective [Module.Free R M] [Module.Finite R M] (j : ZMod 2) :
       Function.Surjective (spinActionParity R M j) := by
     intro f
     fin_cases j
     · obtain ⟨x, hx⟩ := (spinActionEven_bijective R M).2 (f, 1)
       exact ⟨x, congrArg Prod.fst hx⟩
     · obtain ⟨x, hx⟩ := (spinActionEven_bijective R M).2 (1, f)
       exact ⟨x, congrArg Prod.snd hx⟩

   /-- Optional: units of the even Clifford algebra are pairs of automorphisms of `S^+`, `S^-`. -/
   noncomputable def spinUnitsEquivEven [Module.Free R M] [Module.Finite R M] :
       (CliffordAlgebra.even (QuadraticForm.dualProd R M))ˣ ≃*
         (Module.End R (exteriorParity R M 0))ˣ × (Module.End R (exteriorParity R M 1))ˣ :=
     (Units.mapEquiv (spinEquivEven R M).toMulEquiv).trans MulEquiv.prodUnits
   ```

   Defer `spinUnitsEquivEven` to the rung that defines Spin(V) unless it is free to add: Markman's Spin(V) (`x x^* = 1`, `x V x^* ⊂ V`, `^*` = reverse composed with the main involution) needs its own conventions row against Mathlib's `spinGroup` when that rung opens.

7. **Add the non-vacuity test for the even condition.** Compiled, standard axioms, uses only checked lemmas and the proved `spinAction_mem_exteriorParity_of_mem_even`:

   ```lean
   /-- Sanity check: the generator `ι (0, 1)` over `ℤ` is not even; it sends `1` to `ι 1`. -/
   theorem ι_vec_not_mem_evenOdd_zero_int :
       ι (QuadraticForm.dualProd ℤ ℤ) (0, 1) ∉ evenOdd (QuadraticForm.dualProd ℤ ℤ) 0 := by
     intro h
     have h1 : (1 : ExteriorAlgebra ℤ ℤ) ∈ exteriorParity ℤ ℤ 0 := by
       rw [exteriorParity_eq_evenOdd]
       exact Submodule.one_le.mp (one_le_evenOdd_zero _)
     have := spinAction_mem_exteriorParity_of_mem_even ℤ ℤ
       (by rw [← even_toSubmodule] at h; exact h) h1
     rw [spinAction_ι_one] at this
     exact ι_not_mem_exteriorParity_zero ℤ ℤ (by simp) this
   ```

8. **Correct the sketch's hypothesis table.** Replace the row "`[Module.Free R M] [Module.Finite R M]` on the iff ... A counterexample to the reverse direction without `Module.Free` is not known" by: needed through injectivity; `evenOdd_one_iff_zmod_four_fails` is a finite non-free counterexample; over a field `Module.Finite` is not needed (hand argument); the general form is `spinAction_mem_evenOdd_iff_of_injective`. Add `spinActionEven_zmod_four_not_injective` to the `Module.Free` row for `spinEquivEven`.

9. **Future rung, not this one: GLO 3.5.1.** Over a field, irreducibility of `S^+` and `S^-` as `Cl^+`-modules and their nonequivalence follow in a few lines from `spinActionParity_surjective` and the central idempotent `spinEquivEven.symm (1, 0)`; GLO's statement is for the group `Spin_ℚ`, which needs in addition that `Spin_ℚ` spans `Cl^+_ℚ`. Open it when the Markman track needs irreducibility; record the cheap `Cl^+` form in the sketch.

Attempts that failed: trivializing the iff and the bijectivity (section 3); finding a sign or a scalar in any target (there is none; the one sign in play is the registered contraction sign, which the parity statements do not see); finding an idle hypothesis (`Module.Free` is needed for both the iff and the equivalence, with compiled counterexamples, and `Module.Finite` is needed for the equivalence by the bounded-shift argument). One question stays open: whether `Module.Finite` is needed for the iff over a general ring for free `M` of infinite rank. Finding 3 makes it irrelevant to the statements.
