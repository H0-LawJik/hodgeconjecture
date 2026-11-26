module

public import HodgeLadder.Markman.CliffordSpin
public import Mathlib.Data.List.Sublists
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.FiniteType

/-!
# Chevalley's theorem: the exterior algebra is the spin module of the split form

Let `M` be a finite free module over a commutative ring `R`. The algebra homomorphism
`HodgeLadder.spinAction R M : CliffordAlgebra (QuadraticForm.dualProd R M) →ₐ[R]
Module.End R (ExteriorAlgebra R M)` of rung `clifford-exterior-spin` is bijective, so the
Clifford algebra of the split form on `Module.Dual R M × M` is isomorphic to the endomorphism
algebra of `∧M` [Chevalley1954], [GolyshevLuntsOrlov2001, Prop. 3.2.1(e)]. This is what makes
`∧*H¹(A) = H*(A)` the spin module in Markman's construction (rung
`clifford-exterior-chevalley`).

The proof runs in three steps; it is the proof of [GolyshevLuntsOrlov2001, Prop. 3.2.1(e)],
with the rank of the Clifford algebra obtained from the count instead of assumed.

1. **Spanning.** For any quadratic form `Q` on a module spanned by a list `L`, the products
   `(l.map (ι Q)).prod` over the sublists `l` of `L` span `CliffordAlgebra Q`. There are
   `2 ^ L.length` of them. Mathlib at the pin has no basis, rank bound or finiteness result for
   a general Clifford algebra.
2. **Surjectivity.** In a basis `b` of `M`, every matrix unit `b.ExteriorAlgebra.end (S, T)`
   of `End(∧M)` lies in the range of `spinAction`: up to a sign it is
   `(e_S * ·) ∘ c ∘ (e_{I \ T} * ·)`, with `e_S` a basis monomial and `c` the product of all
   the dual-basis contractions, which sends `e_I` to `1` and kills every lower degree.
3. **Injectivity.** `End(∧M)` is free of rank `(2 ^ n) ^ 2 = 2 ^ (2 n)`, the Clifford algebra
   is spanned by `2 ^ (2 n)` elements, and a surjection `R ^ k → R ^ k` is bijective for every
   commutative ring (Orzech property, `OrzechProperty.bijective_of_surjective_of_finrank_le`).
   The same count shows the sublist products form a basis.

## Main definitions

* `HodgeLadder.sublistSpan`, `HodgeLadder.sublistProd`: the sublist products of a list.
* `HodgeLadder.dualProdList`: the spanning list `(b.coord i, 0)`, `(0, b i)` of `Dual × M`.
* `HodgeLadder.cliffordDualProdBasis`: the basis of sublist products of the Clifford algebra of
  the split form.
* `HodgeLadder.spinEquiv`: the algebra isomorphism
  `CliffordAlgebra (QuadraticForm.dualProd R M) ≃ₐ[R] Module.End R (ExteriorAlgebra R M)`.

## Main results

* `HodgeLadder.span_sublists_prod_eq_top`: ordered monomials span a Clifford algebra, for any
  quadratic form.
* `HodgeLadder.basis_exteriorAlgebra_eq_list_prod`: an exterior basis monomial as a list product.
* `HodgeLadder.basis_end_mem_range`: the matrix units of `End(∧M)` are in the range.
* `HodgeLadder.spinAction_surjective`, `HodgeLadder.spinAction_injective_of_basis`,
  `HodgeLadder.spinAction_bijective`: Chevalley's theorem.
* `HodgeLadder.spinEquiv_apply`, `HodgeLadder.spinEquiv_ι_apply`,
  `HodgeLadder.spinEquiv_symm_spinGen`: values of the isomorphism.
* `HodgeLadder.linearIndependent_sublistProd_dualProd`,
  `HodgeLadder.finrank_cliffordAlgebra_dualProd`:
  the Clifford algebra of the split form is free of rank `2 ^ (2 * finrank R M)`
  ([GolyshevLuntsOrlov2001, Prop. 3.2.1(a)]).
* `HodgeLadder.spinAction_int_zmod_two_not_surjective`: `Module.Free` cannot be dropped;
  `HodgeLadder.finrank_cliffordAlgebra_dualProd_int`: the rank is `4` for `M = ℤ`.
-/

@[expose] public section

namespace HodgeLadder

open CliffordAlgebra

section Spanning

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]

/-- The span of the products of the sublists of `L` in `CliffordAlgebra Q`. -/
def sublistSpan (Q : QuadraticForm R N) (L : List N) : Submodule R (CliffordAlgebra Q) :=
  Submodule.span R {y | ∃ l ∈ L.sublists, y = (l.map (ι Q)).prod}

/-- The sublist span of `L` sits inside the sublist span of `a :: L`. -/
theorem sublistSpan_le_cons (Q : QuadraticForm R N) (a : N) (L : List N) :
    sublistSpan Q L ≤ sublistSpan Q (a :: L) := by
  refine Submodule.span_mono ?_
  rintro y ⟨l, hl, rfl⟩
  exact ⟨l, List.mem_sublists.mpr ((List.mem_sublists.mp hl).cons a), rfl⟩

/-- Left multiplication by `ι Q a` maps the sublist span of `L` into that of `a :: L`. -/
theorem ι_mul_mem_sublistSpan_cons (Q : QuadraticForm R N) (a : N) (L : List N)
    {y : CliffordAlgebra Q} (hy : y ∈ sublistSpan Q L) : ι Q a * y ∈ sublistSpan Q (a :: L) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    refine Submodule.subset_span ⟨a :: l, List.mem_sublists.mpr
      ((List.mem_sublists.mp hl).cons_cons a),
      ?_⟩
    rw [List.map_cons, List.prod_cons]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

/-- **Reordering step.** Left multiplication by `ι Q v` for `v ∈ L` preserves the span of the
sublist products of `L`. -/
theorem ι_mul_mem_sublistSpan (Q : QuadraticForm R N) (L : List N) {v : N} (hv : v ∈ L)
    {y : CliffordAlgebra Q} (hy : y ∈ sublistSpan Q L) : ι Q v * y ∈ sublistSpan Q L := by
  induction L generalizing v y with
  | nil => simp at hv
  | cons a L' ih =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      rw [List.mem_sublists] at hl
      have hgen : ∀ l' : List N, List.Sublist l' L' → (l'.map (ι Q)).prod ∈ sublistSpan Q L' :=
        fun l' hl' => Submodule.subset_span ⟨l', List.mem_sublists.mpr hl', rfl⟩
      rcases List.mem_cons.mp hv with rfl | hv'
      · cases hl with
        | cons _ hl' =>
          exact ι_mul_mem_sublistSpan_cons Q _ L' (hgen l hl')
        | cons_cons _ hl' =>
          rw [List.map_cons, List.prod_cons, ← mul_assoc, ι_sq_scalar,
            Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
          exact Submodule.smul_mem _ _ (sublistSpan_le_cons Q _ L' (hgen _ hl'))
      · cases hl with
        | cons _ hl' =>
          exact sublistSpan_le_cons Q a L' (ih hv' (hgen l hl'))
        | cons_cons _ hl' =>
          rename_i l'
          have hswap := ι_mul_ι_add_swap (Q := Q) v a
          have h1 : ι Q v * ι Q a = algebraMap R _ (QuadraticMap.polar Q v a) - ι Q a * ι Q v :=
            eq_sub_of_add_eq hswap
          rw [List.map_cons, List.prod_cons, ← mul_assoc, h1, sub_mul, mul_assoc,
            Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
          refine Submodule.sub_mem _ ?_ ?_
          · exact Submodule.smul_mem _ _ (sublistSpan_le_cons Q _ L' (hgen _ hl'))
          · exact ι_mul_mem_sublistSpan_cons Q a L' (ih hv' (hgen _ hl'))
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

/-- **Ordered monomials span a Clifford algebra.** If the entries of `L` span `N`, the products
of the sublists of `L` span `CliffordAlgebra Q`, for any quadratic form `Q`. -/
theorem span_sublists_prod_eq_top (Q : QuadraticForm R N) (L : List N)
    (hL : Submodule.span R {v | v ∈ L} = ⊤) : sublistSpan Q L = ⊤ := by
  have key : ∀ x : CliffordAlgebra Q, ∀ y ∈ sublistSpan Q L, x * y ∈ sublistSpan Q L := by
    intro x
    induction x using CliffordAlgebra.induction with
    | algebraMap r =>
      intro y hy
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact Submodule.smul_mem _ _ hy
    | ι v =>
      have hv : v ∈ Submodule.span R {v | v ∈ L} := hL ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem w hw => exact fun y hy => ι_mul_mem_sublistSpan Q L hw hy
      | zero => intro y _; rw [map_zero, zero_mul]; exact Submodule.zero_mem _
      | add w w' _ _ h h' =>
        intro y hy; rw [map_add, add_mul]; exact Submodule.add_mem _ (h y hy) (h' y hy)
      | smul r w _ h =>
        intro y hy; rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ _ (h y hy)
    | mul a b ha hb => intro y hy; rw [mul_assoc]; exact ha _ (hb y hy)
    | add a b ha hb => intro y hy; rw [add_mul]; exact Submodule.add_mem _ (ha y hy) (hb y hy)
  have h1 : (1 : CliffordAlgebra Q) ∈ sublistSpan Q L :=
    Submodule.subset_span ⟨[], List.mem_sublists.mpr (List.nil_sublist _), by simp⟩
  rw [eq_top_iff]
  intro x _
  simpa using key x 1 h1

/-- The sublist products of `L`, indexed by `Fin (2 ^ L.length)` through `List.sublists`. -/
def sublistProd (Q : QuadraticForm R N) (L : List N) : Fin (2 ^ L.length) → CliffordAlgebra Q :=
  fun i => ((L.sublists.get (Fin.cast (List.length_sublists L).symm i)).map (ι Q)).prod

/-- The family `sublistProd Q L` spans `CliffordAlgebra Q` when the entries of `L` span `N`. -/
theorem span_range_sublistProd (Q : QuadraticForm R N) (L : List N)
    (hL : Submodule.span R {v | v ∈ L} = ⊤) :
    Submodule.span R (Set.range (sublistProd Q L)) = ⊤ := by
  rw [eq_top_iff, ← span_sublists_prod_eq_top Q L hL]
  refine Submodule.span_mono ?_
  rintro y ⟨l, hl, rfl⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hl
  exact ⟨Fin.cast (List.length_sublists L) i, rfl⟩

/-- A Clifford algebra on a module spanned by a list `L` is a quotient of `R ^ (2 ^ L.length)`. -/
theorem exists_surjective_fun_cliffordAlgebra (Q : QuadraticForm R N) (L : List N)
    (hL : Submodule.span R {v | v ∈ L} = ⊤) :
    ∃ φ : (Fin (2 ^ L.length) → R) →ₗ[R] CliffordAlgebra Q, Function.Surjective φ :=
  ⟨Fintype.linearCombination R (sublistProd Q L), by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, span_range_sublistProd Q L hL]⟩

end Spanning

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

section Contraction

/-- Contraction by `f` kills a product of vectors on which `f` vanishes. -/
theorem contractLeft_list_prod_eq_zero (f : Module.Dual R M) (l : List M)
    (hl : ∀ x ∈ l, f x = 0) :
    contractLeft (Q := (0 : QuadraticForm R M)) f ((l.map (ExteriorAlgebra.ι R)).prod) = 0 := by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, contractLeft_one]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ExteriorAlgebra.ι, contractLeft_ι_mul,
      hl a List.mem_cons_self, zero_smul, zero_sub,
      ih (fun x hx => hl x (List.mem_cons_of_mem a hx)),
      mul_zero, neg_zero]

/-- `k` contractions map `⋀[R]^(j + k) M` into `⋀[R]^j M`. -/
theorem list_prod_contractLeft_mem (fs : List (Module.Dual R M)) {j : ℕ}
    {y : ExteriorAlgebra R M} (hy : y ∈ ⋀[R]^(j + fs.length) M) :
    (fs.map fun f => contractLeft (Q := (0 : QuadraticForm R M)) f).prod y ∈ ⋀[R]^j M := by
  induction fs generalizing j with
  | nil => simpa using hy
  | cons f fs ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    have h := ih (j := j + 1) (by rw [List.length_cons] at hy; rwa [add_right_comm, add_assoc])
    exact contractLeft_mem_range_ι_pow R M f j h

/-- More contractions than the degree give zero: `k` contractions kill `⋀[R]^j M` for `j < k`. -/
theorem list_prod_contractLeft_eq_zero (fs : List (Module.Dual R M)) {j : ℕ}
    {y : ExteriorAlgebra R M} (hy : y ∈ ⋀[R]^j M) (hj : j < fs.length) :
    (fs.map fun f => contractLeft (Q := (0 : QuadraticForm R M)) f).prod y = 0 := by
  induction fs with
  | nil => simp at hj
  | cons f fs ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [List.length_cons] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [ih hj, map_zero]
    · have h := list_prod_contractLeft_mem R M fs (j := 0) (by rwa [zero_add])
      rw [ExteriorAlgebra.exteriorPower, pow_zero] at h
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp h
      rw [← hr, contractLeft_algebraMap]

/-- The dual-basis contractions, applied in the order of a duplicate-free list `l` of indices,
send the product `ι (b i₁) * ⋯ * ι (b iₖ)` to `1`, with no sign. -/
theorem list_prod_contractLeft_coord {I : Type*} (b : Module.Basis I R M) (l : List I)
    (hl : l.Nodup) :
    (l.reverse.map fun i => contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)).prod
      ((l.map fun i => ExteriorAlgebra.ι R (b i)).prod) = 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    rw [List.reverse_cons, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, List.map_cons, List.prod_cons, Module.End.mul_apply,
      ExteriorAlgebra.ι, contractLeft_ι_mul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, one_smul]
    have h0 : contractLeft (Q := (0 : QuadraticForm R M)) (b.coord a)
        ((t.map fun i => ExteriorAlgebra.ι R (b i)).prod) = 0 := by
      have := contractLeft_list_prod_eq_zero R M (b.coord a) (t.map b) (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        rw [Module.Basis.coord_apply, Module.Basis.repr_self]
        exact Finsupp.single_eq_of_ne (fun h => hl.1 (by rw [h]; exact hi)))
      rwa [List.map_map] at this
    rw [h0, mul_zero, sub_zero]
    exact ih hl.2

end Contraction

section Surjective

/-- `spinAction` of a product of vectors `(0, x)` is left multiplication by the product of the
`ι x` in the exterior algebra. -/
theorem spinAction_list_prod_vec (l : List M) (y : ExteriorAlgebra R M) :
    spinAction R M ((l.map fun x => ι (QuadraticForm.dualProd R M) (0, x)).prod) y =
      (l.map (ExteriorAlgebra.ι R)).prod * y := by
  induction l generalizing y with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih, spinAction_ι_vec,
      List.map_cons, List.prod_cons, mul_assoc]

/-- **Bridge to lists.** The basis monomial `b.ExteriorAlgebra U` is the product of the
`ι (b i)` over the elements of `U` in increasing order. -/
theorem basis_exteriorAlgebra_eq_list_prod {I : Type*} [LinearOrder I] (b : Module.Basis I R M)
    (U : Finset I) :
    b.ExteriorAlgebra U = ((U.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι R (b i)).prod := by
  rw [ExteriorAlgebra.basis_apply]
  unfold ExteriorAlgebra.ιMulti_family
  rw [ExteriorAlgebra.ιMulti_apply]
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp [Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.orderEmbOfFin_apply]

/-- **The coordinate functionals are in the range.** For a basis `b` of `M` indexed by a finite
linear order and a finset `T` of indices, some element of the range of `spinAction` sends the
basis monomial `b.ExteriorAlgebra U` to `u • 1` for `U = T`, for a sign `u`, and to `0`
otherwise. -/
theorem exists_mem_range_apply_basis {I : Type*} [Fintype I] [LinearOrder I]
    (b : Module.Basis I R M) (T : Finset I) :
    ∃ a ∈ (spinAction R M).range, ∃ u : ℤˣ, ∀ U : Finset I,
      a (b.ExteriorAlgebra U) = if U = T then u • (1 : ExteriorAlgebra R M) else 0 := by
  classical
  -- the contractions by all dual-basis vectors, in increasing order
  set lI := (Finset.univ : Finset I).sort (· ≤ ·) with hlI
  set c : CliffordAlgebra (QuadraticForm.dualProd R M) :=
    (lI.reverse.map fun i => ι (QuadraticForm.dualProd R M) (b.coord i, 0)).prod with hc
  have hcact : spinAction R M c =
      (lI.reverse.map fun i => contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)).prod := by
    rw [hc, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    exact LinearMap.ext (spinAction_ι_dual R M (b.coord i))
  -- left multiplication by the basis monomial of the complement of `T`
  set w : CliffordAlgebra (QuadraticForm.dualProd R M) :=
    (((Finset.univ \ T).sort (· ≤ ·)).map fun i =>
      ι (QuadraticForm.dualProd R M) (0, b i)).prod with hw
  have hwact : ∀ y, spinAction R M w y = b.ExteriorAlgebra (Finset.univ \ T) * y := by
    intro y
    have h := spinAction_list_prod_vec R M (((Finset.univ \ T).sort (· ≤ ·)).map b) y
    rw [List.map_map, List.map_map] at h
    rw [hw, basis_exteriorAlgebra_eq_list_prod]
    exact h
  have hcuniv : spinAction R M c (b.ExteriorAlgebra Finset.univ) = 1 := by
    rw [hcact, basis_exteriorAlgebra_eq_list_prod]
    exact list_prod_contractLeft_coord R M b lI (Finset.sort_nodup _ _)
  have hclow : ∀ {k : ℕ} {y : ExteriorAlgebra R M}, y ∈ ⋀[R]^k M → k < Fintype.card I →
      spinAction R M c y = 0 := by
    intro k y hy hk
    rw [hcact]
    have h := list_prod_contractLeft_eq_zero R M (lI.reverse.map b.coord) hy (by
      rw [List.length_map, List.length_reverse, hlI, Finset.length_sort, Finset.card_univ]
      exact hk)
    rwa [List.map_map] at h
  have hT : Disjoint (Set.powersetCard.ofCard (s := Finset.univ \ T) rfl).val
      (Set.powersetCard.ofCard (s := T) rfl).val := Finset.sdiff_disjoint
  refine ⟨spinAction R M (c * w), AlgHom.mem_range_self _ _,
    (Set.powersetCard.permOfDisjoint hT).sign,
    fun U => ?_⟩
  rw [map_mul, Module.End.mul_apply, hwact]
  by_cases hU : U = T
  · subst hU
    rw [ite_eq_left rfl]
    have hm := ExteriorAlgebra.basis_mul_of_disjoint b
      (Set.powersetCard.ofCard (s := Finset.univ \ U) rfl)
      (Set.powersetCard.ofCard (s := U) rfl) hT
    have hunion : ((Set.powersetCard.disjUnion hT : Set.powersetCard I _) : Finset I) =
        Finset.univ := by
      rw [Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union]
      exact Finset.sdiff_union_of_subset (Finset.subset_univ _)
    erw [hm]
    rw [hunion, map_zsmul_unit, hcuniv]
  · rw [ite_eq_right hU]
    by_cases hd : Disjoint (Finset.univ \ T) U
    · have hd' : Disjoint (Set.powersetCard.ofCard (s := Finset.univ \ T) rfl).val
          (Set.powersetCard.ofCard (s := U) rfl).val := hd
      have hm := ExteriorAlgebra.basis_mul_of_disjoint b
        (Set.powersetCard.ofCard (s := Finset.univ \ T) rfl)
        (Set.powersetCard.ofCard (s := U) rfl) hd'
      erw [hm]
      rw [map_zsmul_unit]
      have hsub : U ⊂ T := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨fun x hx => ?_, hU⟩
        by_contra hxT
        exact Finset.disjoint_left.mp hd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxT⟩) hx
      have hcard : (Finset.univ \ T).card + U.card < Fintype.card I := by
        have h1 := Finset.card_lt_card hsub
        have h2 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
        rw [Finset.card_univ] at h2
        omega
      rw [hclow (ExteriorAlgebra.basis_eq_coe_basis b _ ▸ Submodule.coe_mem _) hcard, smul_zero]
    · have hd' : ¬ Disjoint (Set.powersetCard.ofCard (s := Finset.univ \ T) rfl).val
          (Set.powersetCard.ofCard (s := U) rfl).val := hd
      have hm := ExteriorAlgebra.basis_mul_of_not_disjoint b
        (Set.powersetCard.ofCard (s := Finset.univ \ T) rfl)
        (Set.powersetCard.ofCard (s := U) rfl) hd'
      erw [hm]
      rw [map_zero]

/-- **Matrix units are in the range.** Every element `b.ExteriorAlgebra.end (S, T)` of the
standard basis of `End(∧M)` (send `e_T` to `e_S`, the other basis monomials to `0`) lies in the
range of `spinAction`. -/
theorem basis_end_mem_range {I : Type*} [Fintype I] [LinearOrder I] (b : Module.Basis I R M)
    (S T : Finset I) : b.ExteriorAlgebra.end (S, T) ∈ (spinAction R M).range := by
  classical
  obtain ⟨a, ha, u, hau⟩ := exists_mem_range_apply_basis R M b T
  set w : CliffordAlgebra (QuadraticForm.dualProd R M) :=
    ((S.sort (· ≤ ·)).map fun i => ι (QuadraticForm.dualProd R M) (0, b i)).prod with hw
  have hwact : ∀ y, spinAction R M w y = b.ExteriorAlgebra S * y := by
    intro y
    have h := spinAction_list_prod_vec R M ((S.sort (· ≤ ·)).map b) y
    rw [List.map_map, List.map_map] at h
    rw [hw, basis_exteriorAlgebra_eq_list_prod]
    exact h
  set r : R := ((u : ℤ) : R) with hr
  have hrr : r * r = 1 := by
    rw [hr, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hE : b.ExteriorAlgebra.end (S, T) = r • (spinAction R M w * a) := by
    refine b.ExteriorAlgebra.ext fun U => ?_
    rw [Module.Basis.end_apply_apply, LinearMap.smul_apply, Module.End.mul_apply, hau, hwact]
    by_cases hU : U = T
    · subst hU
      rw [ite_eq_left rfl, ite_eq_left rfl, Units.smul_def, ← Int.cast_smul_eq_zsmul R, ← hr,
        mul_smul_comm, mul_one, smul_smul, hrr, one_smul]
    · rw [ite_eq_right hU, ite_eq_right (Ne.symm hU), mul_zero, smul_zero]
  rw [hE]
  exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (AlgHom.mem_range_self _ _) ha) r

/-- **Surjectivity** for a module with a basis indexed by a finite linear order. -/
theorem spinAction_surjective_of_basis {I : Type*} [Fintype I] [LinearOrder I]
    (b : Module.Basis I R M) : Function.Surjective (spinAction R M) := by
  classical
  have h : Subalgebra.toSubmodule (spinAction R M).range = ⊤ := by
    rw [eq_top_iff, ← b.ExteriorAlgebra.end.span_eq, Submodule.span_le]
    rintro _ ⟨⟨S, T⟩, rfl⟩
    exact basis_end_mem_range R M b S T
  intro y
  have hy : y ∈ Subalgebra.toSubmodule (spinAction R M).range := h ▸ Submodule.mem_top
  exact (AlgHom.mem_range _).mp hy

/-- **Surjectivity.** For `M` finite free, every endomorphism of `∧M` is the action of an
element of the Clifford algebra of the split form. -/
theorem spinAction_surjective [Module.Free R M] [Module.Finite R M] :
    Function.Surjective (spinAction R M) := by
  let b := Module.Free.chooseBasis R M
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R M) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  exact spinAction_surjective_of_basis R M b

end Surjective

/-- The rank of `End(∧M)` for a basis indexed by a finite type: `2 ^ (2 * #I)`. -/
theorem finrank_end_exteriorAlgebra [Nontrivial R] {I : Type*} [Fintype I] [LinearOrder I]
    (b : Module.Basis I R M) :
    Module.finrank R (Module.End R (ExteriorAlgebra R M)) = 2 ^ (2 * Fintype.card I) := by
  have := Module.Free.of_basis b.ExteriorAlgebra
  have := Module.Finite.of_basis b.ExteriorAlgebra
  rw [Module.finrank_linearMap, Module.finrank_eq_card_basis b.ExteriorAlgebra, Fintype.card_finset,
    ← pow_add, two_mul]

section Injective

variable {R M}

/-- The spanning list of `Module.Dual R M × M` attached to a basis `b` of `M`: the vectors
`(b.coord i, 0)`, then the vectors `(0, b i)`. -/
noncomputable def dualProdList {I : Type*} [Fintype I] (b : Module.Basis I R M) :
    List (Module.Dual R M × M) :=
  ((Finset.univ : Finset I).toList.map fun i => (b.coord i, 0)) ++
    ((Finset.univ : Finset I).toList.map fun i => (0, b i))

/-- `dualProdList b` has `2 * #I` entries. -/
theorem length_dualProdList {I : Type*} [Fintype I] (b : Module.Basis I R M) :
    (dualProdList b).length = 2 * Fintype.card I := by
  rw [dualProdList, List.length_append, List.length_map, List.length_map, Finset.length_toList,
    Finset.card_univ, two_mul]

/-- The entries of `dualProdList b` span `Module.Dual R M × M`. -/
theorem span_dualProdList {I : Type*} [Fintype I] (b : Module.Basis I R M) :
    Submodule.span R {v | v ∈ dualProdList b} = ⊤ := by
  classical
  rw [eq_top_iff, ← (b.dualBasis.prod b).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  simp only [Set.mem_ofPred_eq, dualProdList, List.mem_append, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  rcases i with i | i
  · refine Or.inl ⟨i, Prod.ext ?_ ?_⟩
    · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.coe_dualBasis]
    · rw [Module.Basis.prod_apply_inl_snd]
  · refine Or.inr ⟨i, Prod.ext ?_ ?_⟩
    · rw [Module.Basis.prod_apply_inr_fst]
    · rw [Module.Basis.prod_apply_inr_snd]

/-- **The rank count.** For a basis of `M` indexed by a finite type, the composite of the
sublist-product combination `R ^ (2 ^ (2 n)) → CliffordAlgebra (dualProd R M)` with
`spinAction` is injective: it is a surjection between free modules of the same finite rank, and
a commutative ring has the Orzech property. -/
theorem injective_spinAction_comp_sublistProd {I : Type*} [Fintype I] (b : Module.Basis I R M) :
    Function.Injective ((spinAction R M).toLinearMap ∘ₗ
      Fintype.linearCombination R (sublistProd (QuadraticForm.dualProd R M) (dualProdList b))) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := Module.subsingleton R (Fin (2 ^ (dualProdList b).length) → R)
    exact fun _ _ _ => Subsingleton.elim _ _
  let _ : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hsurj : Function.Surjective ((spinAction R M).toLinearMap ∘ₗ
      Fintype.linearCombination R (sublistProd (QuadraticForm.dualProd R M) (dualProdList b))) := by
    refine (spinAction_surjective_of_basis R M b).comp ?_
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact span_range_sublistProd _ _ (span_dualProdList b)
  have := Module.Free.of_basis b.ExteriorAlgebra
  have := Module.Finite.of_basis b.ExteriorAlgebra
  refine (OrzechProperty.bijective_of_surjective_of_finrank_le _ hsurj ?_).1
  rw [Module.finrank_fin_fun, finrank_end_exteriorAlgebra R M b, length_dualProdList]

/-- **Ordered monomials are a basis** ([GolyshevLuntsOrlov2001, Prop. 3.2.1(a)]). For a basis
`b` of `M` indexed by a finite type, the products of the sublists of `dualProdList b` are
linearly independent in the Clifford algebra of the split form. -/
theorem linearIndependent_sublistProd_dualProd {I : Type*} [Fintype I] (b : Module.Basis I R M) :
    LinearIndependent R (sublistProd (QuadraticForm.dualProd R M) (dualProdList b)) := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  have h := injective_spinAction_comp_sublistProd b
  rw [LinearMap.coe_comp] at h
  exact h.of_comp

/-- The basis of the Clifford algebra of the split form given by the products of the sublists of
`dualProdList b`, indexed by `Fin (2 ^ (dualProdList b).length)`, that is `2 ^ (2 * #I)`
elements. -/
noncomputable def cliffordDualProdBasis {I : Type*} [Fintype I] (b : Module.Basis I R M) :
    Module.Basis (Fin (2 ^ (dualProdList b).length)) R
      (CliffordAlgebra (QuadraticForm.dualProd R M)) :=
  Module.Basis.mk (linearIndependent_sublistProd_dualProd b)
    (span_range_sublistProd _ _ (span_dualProdList b)).ge

/-- The basis vectors of `cliffordDualProdBasis b` are the sublist products. -/
theorem cliffordDualProdBasis_apply {I : Type*} [Fintype I] (b : Module.Basis I R M)
    (i : Fin (2 ^ (dualProdList b).length)) :
    cliffordDualProdBasis b i = sublistProd (QuadraticForm.dualProd R M) (dualProdList b) i :=
  Module.Basis.mk_apply _ _ i

/-- **Injectivity** for a module with a basis indexed by a finite type. -/
theorem spinAction_injective_of_basis {I : Type*} [Fintype I] (b : Module.Basis I R M) :
    Function.Injective (spinAction R M) := by
  have hφ : Function.Surjective (Fintype.linearCombination R
      (sublistProd (QuadraticForm.dualProd R M) (dualProdList b))) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact span_range_sublistProd _ _ (span_dualProdList b)
  intro x x' h
  obtain ⟨a, rfl⟩ := hφ x
  obtain ⟨a', rfl⟩ := hφ x'
  exact congrArg _ (injective_spinAction_comp_sublistProd b h)

end Injective

/-- **Chevalley's theorem.** For `M` finite free over a commutative ring `R`, the action of the
Clifford algebra of the split form `QuadraticForm.dualProd R M` on the exterior algebra by
contraction plus wedge is bijective. No nontriviality of `R` is needed: over the zero ring both
sides are zero. -/
theorem spinAction_bijective [Module.Free R M] [Module.Finite R M] :
    Function.Bijective (spinAction R M) :=
  ⟨spinAction_injective_of_basis (Module.Free.chooseBasis R M), spinAction_surjective R M⟩

/-- **The spin module isomorphism.** For `M` finite free, `spinAction` is an isomorphism of
`R`-algebras `CliffordAlgebra (QuadraticForm.dualProd R M) ≃ₐ[R] Module.End R (ExteriorAlgebra R M)`
(Chevalley). -/
noncomputable def spinEquiv [Module.Free R M] [Module.Finite R M] :
    CliffordAlgebra (QuadraticForm.dualProd R M) ≃ₐ[R] Module.End R (ExteriorAlgebra R M) :=
  AlgEquiv.ofBijective (spinAction R M) (spinAction_bijective R M)

/-- `spinEquiv` is `spinAction`. -/
@[simp]
theorem spinEquiv_apply [Module.Free R M] [Module.Finite R M]
    (x : CliffordAlgebra (QuadraticForm.dualProd R M)) : spinEquiv R M x = spinAction R M x :=
  rfl

/-- `spinEquiv (ι (f, x))` is contraction by `f` plus left wedge with `x`. -/
theorem spinEquiv_ι_apply [Module.Free R M] [Module.Finite R M] (v : Module.Dual R M × M)
    (y : ExteriorAlgebra R M) :
    spinEquiv R M (ι _ v) y = contractLeft v.1 y + ExteriorAlgebra.ι R v.2 * y := by
  rw [spinEquiv_apply]
  exact spinAction_ι_apply R M v y

/-- The inverse of `spinEquiv` sends the operator `spinGen v` back to the generator `ι v`. -/
theorem spinEquiv_symm_spinGen [Module.Free R M] [Module.Finite R M] (v : Module.Dual R M × M) :
    (spinEquiv R M).symm (spinGen R M v) = ι _ v := by
  rw [AlgEquiv.symm_apply_eq, spinEquiv_apply, spinAction_ι]

/-- **Rank of the Clifford algebra of the split form.** For `M` finite free over a nontrivial
`R`, the Clifford algebra of `QuadraticForm.dualProd R M` is free of rank
`2 ^ (2 * finrank R M)`. `Nontrivial R` is needed here only because Mathlib sets
`finrank R M = 1` over the zero ring (`Module.finrank_subsingleton`). -/
theorem finrank_cliffordAlgebra_dualProd [Nontrivial R] [Module.Free R M] [Module.Finite R M] :
    Module.Free R (CliffordAlgebra (QuadraticForm.dualProd R M)) ∧
      Module.finrank R (CliffordAlgebra (QuadraticForm.dualProd R M)) =
        2 ^ (2 * Module.finrank R M) := by
  let b := Module.Free.chooseBasis R M
  refine ⟨Module.Free.of_basis (cliffordDualProdBasis b), ?_⟩
  rw [Module.finrank_eq_card_basis (cliffordDualProdBasis b), Fintype.card_fin, length_dualProdList,
    Module.finrank_eq_card_chooseBasisIndex]

section Tests

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

end Tests

end HodgeLadder
