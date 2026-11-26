module

public import HodgeLadder.Cup.TopOpenCup

/-!
# The Yoneda cup product against the singular cup product

Rung `cup-singular-comparison` (front `cup`, absolute case). Upstream's equivalence
`rationalCohomologyAddEquivSingularCohomology` from rational sheaf cohomology to rational singular
cohomology carries the Yoneda cup product `cup` (decision 0009) to `(−1)^{pq}` times the singular
cup product `cupSing`, in the same order:
`Ψ (x ∪ y) = (−1)^{pq} · cupSing (Ψ x) (Ψ y)`.

## Main results

* `HodgeLadder.Cup.exists_singClass`, `HodgeLadder.Cup.cup_global_chosen`,
  `HodgeLadder.Cup.cup_singular_comparison`, `HodgeLadder.Cup.cup_gradedComm`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}}

/-- **Every singular class is the singular class of a global cocycle.** -/
lemma exists_singClass {n : ℕ} (z : Cohomology ℚ Y n) :
    ∃ (c : OpenCochains ℚ Y (op ⊤) n) (hc : (singularCochainCoboundary ℚ Y n).app (op ⊤) c = 0),
      singClass c hc = z := by
  obtain ⟨u, hu⟩ := (AddCommGrpCat.epi_iff_surjective
    ((globalRawSingularCochainComplex ℚ Y).homologyπ n)).mp inferInstance
    (ordinarySingularCohomologyEquivGlobalRaw ℚ Y n z)
  set c : OpenCochains ℚ Y (op ⊤) n := (globalRawSingularCochainComplex ℚ Y).iCycles n u
  have hd : (globalRawSingularCochainComplex ℚ Y).d n (n + 1) c = 0 := by
    change ((globalRawSingularCochainComplex ℚ Y).iCycles n ≫
      (globalRawSingularCochainComplex ℚ Y).d n (n + 1)) u = 0
    rw [HomologicalComplex.iCycles_d]
    rfl
  have hc : (singularCochainCoboundary ℚ Y n).app (op ⊤) c = 0 := by
    have := hd
    change ((singularCochainPresheafComplex ℚ Y).d n (n + 1)).app (op ⊤) c = 0 at this
    rwa [singularCochainPresheafComplex_d] at this
  refine ⟨c, hc, ?_⟩
  rw [singClass, AddEquiv.symm_apply_eq, ← hu]
  unfold cls
  congr 1
  apply cycles_ext
  exact iCycles_cyc _ _ _ _ _ _

section Variety

open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ))

set_option maxHeartbeats 1000000 in
/-- `cup-global-comparison` for upstream's chosen resolution. -/
lemma cup_global_chosen [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    {p q : ℕ} (x : H^p(X; ℚ)) (y : H^q(X; ℚ))
    (a : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) p)
    (b : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) q)
    (ha : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) p).app (op ⊤) a = 0)
    (hb : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) q).app (op ⊤) b = 0)
    (hx : rationalSingularCochainHypercohomologyAddEquivGlobalSections X p
        (rationalCohomologySingularCochainAddEquiv X p x) =
      namedClass X ((rightMulCocycle a ha).precomp (iotaZ (TopCat.of (ComplexPoint X)))))
    (hy : rationalSingularCochainHypercohomologyAddEquivGlobalSections X q
        (rationalCohomologySingularCochainAddEquiv X q y) =
      namedClass X ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X))))) :
    rationalSingularCochainHypercohomologyAddEquivGlobalSections X (p + q : ℕ)
        (rationalCohomologySingularCochainAddEquiv X (p + q) (cup x y (p + q) rfl)) =
      (((p : ℤ) * q).negOnePow : ℤ) • namedClass X ((rightMulCocycle (cupGlobal a b)
        (cupGlobal_coboundary ha hb)).precomp (iotaZ (TopCat.of (ComplexPoint X)))) := by
  unfold rationalSingularCochainHypercohomologyAddEquivGlobalSections at hx hy ⊢
  dsimp only at hx hy ⊢
  refine @cup_global_comparison X _ _ _ ?_ _ ?_ ?_ p q x y a b ha hb hx hy

set_option maxHeartbeats 1000000 in
/-- **The Yoneda cup product against the singular cup product**: upstream's equivalence `Ψ` from
rational sheaf cohomology to rational singular cohomology satisfies
`Ψ (x ∪ y) = (−1)^{pq} · cupSing (Ψ x) (Ψ y)`. -/
theorem cup_singular_comparison [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    {p q : ℕ} (x : H^p(X; ℚ)) (y : H^q(X; ℚ)) :
    rationalCohomologyAddEquivSingularCohomology X (p + q) (cup x y (p + q) rfl) =
      (((p : ℤ) * q).negOnePow : ℤ) • cupSing (TopCat.of (ComplexPoint X))
        (rationalCohomologyAddEquivSingularCohomology X p x)
        (rationalCohomologyAddEquivSingularCohomology X q y) (p + q) rfl := by
  obtain ⟨a, ha, hxa⟩ := exists_singClass (rationalCohomologyAddEquivSingularCohomology X p x)
  obtain ⟨b, hb, hyb⟩ := exists_singClass (rationalCohomologyAddEquivSingularCohomology X q y)
  rw [← hxa, ← hyb, cupSing_singClass]
  -- `Ψ` is step 1 followed by steps 2 and 3
  have hΨ : ∀ (n : ℕ) (z : H^n(X; ℚ)), rationalCohomologyAddEquivSingularCohomology X n z =
      rationalSingularCochainHypercohomologyAddEquivCohomology X n
        (rationalCohomologySingularCochainAddEquiv X n z) := fun _ _ => rfl
  -- step 1 of `x` and `y` are the classes of the named cocycles
  have hstep : ∀ {n : ℕ} (z : H^n(X; ℚ)) (c : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) n)
      (hc : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) n).app (op ⊤) c = 0),
      rationalCohomologyAddEquivSingularCohomology X n z = singClass c hc →
      rationalSingularCochainHypercohomologyAddEquivGlobalSections X n
        (rationalCohomologySingularCochainAddEquiv X n z) =
      namedClass X ((rightMulCocycle c hc).precomp (iotaZ (TopCat.of (ComplexPoint X)))) := by
    intro n z c hc h
    rw [hΨ, ← step3_named_class X c hc] at h
    rw [(rationalSingularCochainHypercohomologyAddEquivCohomology X n).injective h]
    exact globalSections_mk X n _
  have hcup := cup_global_chosen X x y a b ha hb (hstep x a ha hxa.symm) (hstep y b hb hyb.symm)
  -- steps 2 and 3 through the global sections
  set R := (rationalSingularCochainHypercohomologyAddEquivGlobalSections X ((p + q : ℕ) : ℤ)).symm.trans
    (rationalSingularCochainHypercohomologyAddEquivCohomology X (p + q))
  have key : ∀ w, rationalSingularCochainHypercohomologyAddEquivCohomology X (p + q) w =
      R (rationalSingularCochainHypercohomologyAddEquivGlobalSections X ((p + q : ℕ) : ℤ) w) := by
    intro w
    simp [R]
  rw [hΨ, key, hcup, map_zsmul]
  erw [← globalSections_mk X _ ((rightMulCocycle (cupGlobal a b) (cupGlobal_coboundary ha hb)).precomp
    (iotaZ (TopCat.of (ComplexPoint X))))]
  rw [← key]
  congr 1
  exact step3_named_class X (cupGlobal a b) (cupGlobal_coboundary ha hb)

/-- The comparison in any target degree. -/
theorem cup_singular_comparison' [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    {p q n : ℕ} (x : H^p(X; ℚ)) (y : H^q(X; ℚ)) (h : p + q = n) :
    rationalCohomologyAddEquivSingularCohomology X n (cup x y n h) =
      ((-1 : ℤ) ^ (p * q)) • cupSing (TopCat.of (ComplexPoint X))
        (rationalCohomologyAddEquivSingularCohomology X p x)
        (rationalCohomologyAddEquivSingularCohomology X q y) n h := by
  subst h
  rw [cup_singular_comparison X x y, ← Nat.cast_mul, Int.coe_negOnePow_natCast]

/-- **Graded commutativity of the cup product**: `x ∪ y = (−1)^{pq} · y ∪ x`. -/
theorem cup_gradedComm [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    {p q n : ℕ} (x : H^p(X; ℚ)) (y : H^q(X; ℚ)) (h : p + q = n) :
    cup x y n h = ((-1 : ℤ) ^ (p * q)) • cup y x n (by omega) := by
  apply (rationalCohomologyAddEquivSingularCohomology X n).injective
  rw [map_zsmul, cup_singular_comparison' X x y h, cup_singular_comparison' X y x (by omega)]
  generalize rationalCohomologyAddEquivSingularCohomology X p x = A
  generalize rationalCohomologyAddEquivSingularCohomology X q y = B
  rw [cupSing_gradedComm (TopCat.of (ComplexPoint X)) A B n h, smul_smul, smul_smul]
  have hk : ((-1 : ℤ) ^ (p * q)) * (-1 : ℤ) ^ (q * p) * (-1 : ℤ) ^ (p * q) =
      (-1 : ℤ) ^ (p * q) := by
    rw [mul_comm q p, ← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [hk]

end Variety

end HodgeLadder.Cup
