module

public import HodgeLadder.Cup.SupportedConeCompat
public import HodgeLadder.Cup.RelCupCocycle
public import HodgeLadder.Cup.RightMultCocycle
public import HodgeLadder.Cup.Step3
public import HodgeLadder.Cup.TopOpenCup

/-!
# Right multiplication on supported sections against the relative cup product

Rung `supported-relative-cup` (front `cup`, supported comparison). For a relative cocycle `x` of
`(V, V ⊓ U)` and a global cocycle `b`, `Θ` carries the relative cup `x ∪ b` to right
multiplication by `b` on sections of the singular cochain sheaves (`rawMap_relCupInt`): the
sheafification unit commutes with right multiplication, and forgetting `V ⊓ U` sends the relative
cup to the Alexander–Whitney cup. With `supported-singular-class`, upstream's supported singular
equivalence sends the class of a supported cocycle whose section is `b` acting on the section of
`Θ₁ x` to `relCupSing` of the class of `Θ₁ x` and the class of `b` on `V`. No sign enters.

## Main results

* `HodgeLadder.Cup.rawMapMid_apply`, `HodgeLadder.Cup.relProj_relCupDual`,
  `HodgeLadder.Cup.toSheafify_rightMul`, `HodgeLadder.Cup.rawMap_relCupInt`,
  `HodgeLadder.Cup.relDualEquiv_cls`, `HodgeLadder.Cup.supported_relative_cup`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory TopologicalSpace Opposite AlgebraicTopology.Singular
  TopCat.Sheaf

namespace HodgeLadder.Cup

section Ext

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]
  {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J} (K : HomologicalComplex C c)
  (e : c.Embedding c') [e.IsRelIff]

/-- The inverse of `mapExtendCanonicalIso` in a degree coming from the original complex. -/
lemma mapExtendCanonicalIso_inv_f {i : I} {j : J} (h : e.f i = j) :
    (HomologicalComplex.mapExtendCanonicalIso F K e).inv.f j =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫ F.map (K.extendXIso e h).inv := by
  rw [← cancel_epi ((HomologicalComplex.mapExtendCanonicalIso F K e).hom.f j),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    HomologicalComplex.mapExtendCanonicalIso_hom_f F K e h]
  simp [← F.map_comp]

end Ext

variable (X : TopCat.{0}) (U V : Opens X)

set_option backward.isDefEq.respectTransparency false in
/-- **The middle component of `Θ` on a cochain**: the sheafification of the raw cochain. -/
lemma rawMapMid_apply (k : ℕ) (y : (relSeq X U V).X₂.X (k : ℤ)) :
    (sInt_XIso (X := X) (rfl : (k : ℤ) = k)).hom.hom.app (op V) ((rawMapMid X U V).f k y) =
      (toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf ℚ X k)).app (op V)
        ((((relativeDualCochainShortComplexNat ℚ (openInclusionPair X (Opens.infLELeft V U))).X₂).extendXIso
          ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f k = k)).hom y) := by
  simp only [rawMapMid, openRawSingularCochainComplexIntIsoDual, HomologicalComplex.comp_f,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl,
    HomologicalComplex.mapExtendCanonicalIso_hom_f _ _ ComplexShape.embeddingUpNat (i := k) (j := (k : ℤ)) rfl,
    mapExtendCanonicalIso_inv_f _ _ ComplexShape.embeddingUpNat (i := k) (j := (k : ℤ)) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [← ConcreteCategory.comp_apply]
  erw [Iso.inv_hom_id_assoc]
  have hS : (supportEvaluation X V).map
      (HomologicalComplex.extendXIso (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f k = k)).inv ≫
      (sInt_XIso (X := X) (rfl : (k : ℤ) = k)).hom.hom.app (op V) = 𝟙 _ := by
    exact ((supportEvaluation X V).mapIso (sInt_XIso (X := X) (rfl : (k : ℤ) = k))).inv_hom_id
  simp only [Category.assoc, hS]
  rfl

/-- The pair `(V, V ⊓ U)`. -/
abbrev pairVU : TopPair.{0} := openInclusionPair X (Opens.infLELeft V U)

/-- The relative cup product of a relative cochain and an absolute cochain of `V`, as linear
functionals. -/
def relCupDual {p q : ℕ} (c : (RelativeCochainComplex ℚ (pairVU X U V)).X p)
    (b : (SingularChainComplex ℚ (pairVU X U V).fst).linearDualCochainComplex.X q) (n : ℕ)
    (h : p + q = n) : (RelativeCochainComplex ℚ (pairVU X U V)).X n :=
  ModuleCat.homLinearEquiv (R := ℚ) (S := ℚ) (TauCeti.ChainComplex.cupCochain ℚ (relDiagonal (pairVU X U V))
    (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h ((ModuleCat.homLinearEquiv (R := ℚ) (S := ℚ)).symm c)
    ((ModuleCat.homLinearEquiv (R := ℚ) (S := ℚ)).symm b))

set_option backward.isDefEq.respectTransparency false in
/-- **Forgetting `V ⊓ U` sends the relative cup to right multiplication on cochains of `V`.** -/
lemma relProj_relCupDual {p q : ℕ} (c : (RelativeCochainComplex ℚ (pairVU X U V)).X p)
    (b : OpenCochains ℚ X (op ⊤) q) (n : ℕ) (h : p + q = n) :
    (HomologicalComplex.linearDualMap (relativeChainProjection ℚ (pairVU X U V))).f n
        (relCupDual X U V c (resQ b (op V)) n h) =
      rightMulApp b (op V) p n h
        ((HomologicalComplex.linearDualMap (relativeChainProjection ℚ (pairVU X U V))).f p c) := by
  apply (toHomQ X (U := op V) (n := n)).injective
  simp only [rightMulApp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.apply_symm_apply]
  have h1 := relProj_cupCochain (pairVU X U V) ((ModuleCat.homLinearEquiv (R := ℚ) (S := ℚ)).symm c)
    ((ModuleCat.homLinearEquiv (R := ℚ) (S := ℚ)).symm (resQ b (op V))) n h
  exact h1.symm

/-- **The sheafification unit commutes with right multiplication.** -/
lemma toSheafify_rightMul {p q : ℕ} (b : OpenCochains ℚ X (op ⊤) q) (n : ℕ) (h : p + q = n)
    (y : OpenCochains ℚ X (op V) p) :
    (rightMulSheaf b p n h).hom.app (op V)
        ((toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf ℚ X p)).app (op V) y) =
      (toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf ℚ X n)).app (op V)
        (rightMulApp b (op V) p n h y) := by
  have e := congrArg (fun f => f.app (op V))
    (toSheafify_naturality (Opens.grothendieckTopology X) (rightMul b p n h))
  have e' := ConcreteCategory.congr_hom e y
  simp only [NatTrans.comp_app] at e'
  exact e'.symm

/-- The relative cup product in integer degrees. -/
def relCupInt {p q : ℕ} (x : (relSeq X U V).X₁.X (p : ℤ)) (b : OpenCochains ℚ X (op ⊤) q) (n : ℕ)
    (h : p + q = n) : (relSeq X U V).X₁.X (n : ℤ) :=
  ((RelativeCochainComplex ℚ (pairVU X U V)).extendXIso ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f n = n)).inv
    (relCupDual X U V (((RelativeCochainComplex ℚ (pairVU X U V)).extendXIso
      ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f p = p)).hom x)
      (resQ b (op V)) n h)

set_option backward.isDefEq.respectTransparency false in
/-- The forgetful map of the relative sequence on an element, in nonnegative degrees. -/
lemma relSeq_f_apply (k : ℕ) (w : (relSeq X U V).X₁.X (k : ℤ)) :
    (((relativeDualCochainShortComplexNat ℚ (pairVU X U V)).X₂).extendXIso
        ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f k = k)).hom
        ((relSeq X U V).f.f k w) =
      (HomologicalComplex.linearDualMap (relativeChainProjection ℚ (pairVU X U V))).f k
        (((RelativeCochainComplex ℚ (pairVU X U V)).extendXIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f k = k)).hom w) := by
  change (((relativeDualCochainShortComplexNat ℚ (pairVU X U V)).X₂).extendXIso
      ComplexShape.embeddingUpNat rfl).hom ((HomologicalComplex.extendMap
        (relativeDualCochainShortComplexNat ℚ (pairVU X U V)).f ComplexShape.embeddingUpNat).f k w) = _
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl]
  simp only [ConcreteCategory.comp_apply]
  erw [Iso.inv_hom_id_apply]
  rfl

section ExtD

variable (K : CochainComplex (ModuleCat.{0} ℚ) ℕ)

/-- A cocycle of the extended complex, in a nonnegative degree, has a cocycle as component. -/
lemma extend_d_zero_iff (k : ℕ) (w : (K.extend ComplexShape.embeddingUpNat).X (k : ℤ)) :
    (K.extend ComplexShape.embeddingUpNat).d (k : ℤ) ((k : ℤ) + 1) w = 0 ↔
      K.d k (k + 1) ((K.extendXIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f k = k)).hom w) = 0 := by
  rw [HomologicalComplex.extend_d_eq K _ (show ComplexShape.embeddingUpNat.f k = (k : ℤ) from rfl)
    (show ComplexShape.embeddingUpNat.f (k + 1) = (k : ℤ) + 1 by simp)]
  simp only [ConcreteCategory.comp_apply]
  constructor
  · intro h
    have := congrArg ((K.extendXIso ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f (k + 1) = (k : ℤ) + 1 by simp)).hom) h
    rw [Iso.inv_hom_id_apply, map_zero] at this
    convert this using 3
    rfl
  · intro h
    erw [h, map_zero]

end ExtD

set_option backward.isDefEq.respectTransparency false in
/-- **(F′) The relative class of a cocycle in integer degrees.** Upstream's
`relativeDualCochainCohomologyEquiv`, after forgetting to abelian groups, sends the class of `w`
to the relative class of its component in degree `k`. -/
lemma relDualEquiv_cls (k : ℕ) (w : (relSeq X U V).X₁.X (k : ℤ))
    (hw : (relSeq X U V).X₁.d (k : ℤ) ((k : ℤ) + 1) w = 0)
    (hw' : (RelativeCochainComplex ℚ (pairVU X U V)).d k (k + 1)
      (((RelativeCochainComplex ℚ (pairVU X U V)).extendXIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f k = k)).hom w) = 0) :
    relativeDualCochainCohomologyEquiv ℚ (pairVU X U V) k
        ((ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ (pairVU X U V)).X₁.sc k)
          (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
          (cls (relSeq X U V).X₁ (k : ℤ) ((k : ℤ) + 1) (by simp) w hw)) =
      (RelativeCochainComplex ℚ (pairVU X U V)).homologyπ k
        ((RelativeCochainComplex ℚ (pairVU X U V)).cyclesMk
          (((RelativeCochainComplex ℚ (pairVU X U V)).extendXIso ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f k = k)).hom w) (k + 1) (by simp) hw') := by
  set K := RelativeCochainComplex ℚ (pairVU X U V)
  set F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  set S := (K.extend ComplexShape.embeddingUpNat).sc (k : ℤ)
  have e1 := ConcreteCategory.congr_hom (homologyπ_mapHomologyIso_hom F S)
    (cyc (relSeq X U V).X₁ (k : ℤ) ((k : ℤ) + 1) (by simp) w hw)
  simp only [ConcreteCategory.comp_apply] at e1
  unfold cls
  erw [e1]
  set u := (S.mapCyclesIso F).hom (cyc (relSeq X U V).X₁ (k : ℤ) ((k : ℤ) + 1) (by simp) w hw)
  change (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
    ((K.extend ComplexShape.embeddingUpNat).homologyπ (k : ℤ) u) = _
  have e2 := ConcreteCategory.congr_hom (K.homologyπ_extendHomologyIso_hom ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f k = k)) u
  simp only [ConcreteCategory.comp_apply] at e2
  erw [e2]
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles k)).mp inferInstance
  have e3 := ConcreteCategory.congr_hom (K.extendCyclesIso_hom_iCycles ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f k = k)) u
  simp only [ConcreteCategory.comp_apply] at e3
  erw [e3]
  have e5 := HomologicalComplex.i_cyclesMk K
    ((K.extendXIso ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f k = k)).hom w)
    (k + 1) (by simp) hw'
  erw [e5]
  congr 1
  have e4 := ConcreteCategory.congr_hom (ShortComplex.mapCyclesIso_hom_iCycles S F)
    (cyc (relSeq X U V).X₁ (k : ℤ) ((k : ℤ) + 1) (by simp) w hw)
  simp only [ConcreteCategory.comp_apply] at e4
  refine e4.trans ?_
  exact iCycles_cyc (relSeq X U V).X₁ (k : ℤ) ((k : ℤ) + 1) (by simp) w hw

set_option backward.isDefEq.respectTransparency false in
/-- On cocycles, `relCupDual` is the cochain of `relCupCycles`. -/
lemma relCupDual_iCycles {p q : ℕ} (c : (RelativeCochainComplex ℚ (pairVU X U V)).cycles p)
    (b : (SingularChainComplex ℚ (pairVU X U V).fst).linearDualCochainComplex.cycles q) (n : ℕ)
    (h : p + q = n) :
    relCupDual X U V ((RelativeCochainComplex ℚ (pairVU X U V)).iCycles p c)
        ((SingularChainComplex ℚ (pairVU X U V).fst).linearDualCochainComplex.iCycles q b) n h =
      (RelativeCochainComplex ℚ (pairVU X U V)).iCycles n (relCupCycles (pairVU X U V) c b n h) := by
  unfold relCupCycles
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  erw [TauCeti.ChainComplex.iCycles_cupCycles]
  have hi : ∀ {K L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (m : ℕ) (x : K.cycles m),
      L.iCycles m (HomologicalComplex.cyclesMap φ m x) = φ.f m (K.iCycles m x) := by
    intro K L φ m x
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  erw [hi, hi]
  rfl

section Paracompact

variable [T2Space X] [∀ W : Opens X, ParacompactSpace W]

set_option backward.isDefEq.respectTransparency false in
/-- `Θ₁` followed by the inclusion of supported sections is `Θ₂` after forgetting `V ⊓ U`. -/
lemma rawMap_comm₁₂_apply (k : ℤ) (w : (relSeq X U V).X₁.X k) :
    (supSeq X U V).f.f k ((rawMap X U V).τ₁.f k w) =
      (rawMap X U V).τ₂.f k ((relSeq X U V).f.f k w) := by
  have e := congrArg (fun φ => HomologicalComplex.Hom.f φ k) (rawMap X U V).comm₁₂
  simp only [HomologicalComplex.comp_f] at e
  exact ConcreteCategory.congr_hom e w

set_option backward.isDefEq.respectTransparency false in
/-- **(E) `Θ` carries the relative cup by `b` to right multiplication by `b` on sections.** -/
theorem rawMap_relCupInt {p q : ℕ} (x : (relSeq X U V).X₁.X (p : ℤ))
    (b : OpenCochains ℚ X (op ⊤) q) (n : ℕ) (h : p + q = n) :
    (sInt_XIso (X := X) (rfl : (n : ℤ) = n)).hom.hom.app (op V)
        ((supSeq X U V).f.f n ((rawMap X U V).τ₁.f n (relCupInt X U V x b n h))) =
      (rightMulSheaf b p n h).hom.app (op V)
        ((sInt_XIso (X := X) (rfl : (p : ℤ) = p)).hom.hom.app (op V)
          ((supSeq X U V).f.f p ((rawMap X U V).τ₁.f p x))) := by
  rw [rawMap_comm₁₂_apply, rawMap_comm₁₂_apply]
  erw [rawMapMid_apply, rawMapMid_apply]
  rw [relSeq_f_apply, relSeq_f_apply, toSheafify_rightMul]
  congr 1
  rw [relCupInt]
  erw [Iso.inv_hom_id_apply]
  exact relProj_relCupDual X U V _ b n h

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Right multiplication on supported sections against the relative cup product.** Let `x` be a
relative cocycle of `(V, V ⊓ U)` and `b` a global cocycle of degree `q`. If a supported cocycle
`s'` has, as a section of `S` over `V`, right multiplication by `b` applied to the section of
`Θ₁ x`, then upstream's supported singular equivalence sends the class of `s'` to `relCupSing`
of the class of `Θ₁ x` and the class of `b` on `V`. -/
theorem supported_relative_cup {p q : ℕ} (x : (relSeq X U V).X₁.X (p : ℤ))
    (hx : (relSeq X U V).X₁.d (p : ℤ) ((p : ℤ) + 1) x = 0) (b : OpenCochains ℚ X (op ⊤) q)
    (hb : (SingularChainComplex ℚ (pairVU X U V).fst).linearDualCochainComplex.d q (q + 1)
      (resQ b (op V)) = 0)
    (n : ℕ) (h : p + q = n) (s' : (supSeq X U V).X₁.X (n : ℤ))
    (hs'd : (supSeq X U V).X₁.d (n : ℤ) ((n : ℤ) + 1) s' = 0)
    (hs' : (sInt_XIso (X := X) (rfl : (n : ℤ) = n)).hom.hom.app (op V) ((supSeq X U V).f.f n s') =
      (rightMulSheaf b p n h).hom.app (op V)
        ((sInt_XIso (X := X) (rfl : (p : ℤ) = p)).hom.hom.app (op V)
          ((supSeq X U V).f.f p ((rawMap X U V).τ₁.f p x)))) :
    supportedRationalSingularSectionCohomologyEquivRelative X U V n
        (cls (supSeq X U V).X₁ (n : ℤ) ((n : ℤ) + 1) (by simp) s' hs'd) =
      relCupSing (pairVU X U V)
        (supportedRationalSingularSectionCohomologyEquivRelative X U V p
          (cls (supSeq X U V).X₁ (p : ℤ) ((p : ℤ) + 1) (by simp) ((rawMap X U V).τ₁.f p x)
            (map_d_eq_zero _ x hx)))
        ((SingularChainComplex ℚ (pairVU X U V).fst).linearDualCochainComplex.homologyπ q
          ((SingularChainComplex ℚ (pairVU X U V).fst).linearDualCochainComplex.cyclesMk
            (resQ b (op V)) (q + 1) (by simp) hb)) n h := by
  set K := RelativeCochainComplex ℚ (pairVU X U V)
  set LD := (SingularChainComplex ℚ (pairVU X U V).fst).linearDualCochainComplex
  set eK : ∀ k : ℕ, (K.extend ComplexShape.embeddingUpNat).X (k : ℤ) ≅ K.X k := fun k =>
    K.extendXIso ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f k = k)
  have hx₀ : K.d p (p + 1) ((eK p).hom x) = 0 := (extend_d_zero_iff K p x).mp hx
  set cx := K.cyclesMk ((eK p).hom x) (p + 1) (by simp) hx₀
  set cb := LD.cyclesMk (resQ b (op V)) (q + 1) (by simp) hb
  set w := relCupInt X U V x b n h
  have hw₀ : (eK n).hom w = K.iCycles n (relCupCycles (pairVU X U V) cx cb n h) := by
    rw [← relCupDual_iCycles]
    simp only [w, relCupInt, eK]
    erw [Iso.inv_hom_id_apply]
    congr 1
    · exact (HomologicalComplex.i_cyclesMk K _ (p + 1) (by simp) hx₀).symm
    · exact (HomologicalComplex.i_cyclesMk LD _ (q + 1) (by simp) hb).symm
  have hw₀d : K.d n (n + 1) ((eK n).hom w) = 0 := by
    rw [hw₀, ← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
    rfl
  have hw : (relSeq X U V).X₁.d (n : ℤ) ((n : ℤ) + 1) w = 0 := (extend_d_zero_iff K n w).mpr hw₀d
  -- `s'` is `Θ₁ w`
  have hs'eq : s' = (rawMap X U V).τ₁.f n w := by
    have hinj : Function.Injective ((supSeq X U V).f.f (n : ℤ)) := by
      haveI := (supSeq_shortExact X U V).mono_f
      exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    apply hinj
    apply (AddCommGrpCat.mono_iff_injective
      ((sInt_XIso (X := X) (rfl : (n : ℤ) = n)).hom.hom.app (op V))).mp inferInstance
    rw [hs', rawMap_relCupInt]
  -- the two classes through `Θ₁`
  have hcls : ∀ (k : ℕ) (v : (relSeq X U V).X₁.X (k : ℤ))
      (hv : (relSeq X U V).X₁.d (k : ℤ) ((k : ℤ) + 1) v = 0)
      (hv₀ : K.d k (k + 1) ((eK k).hom v) = 0),
      supportedRationalSingularSectionCohomologyEquivRelative X U V k
        (cls (supSeq X U V).X₁ (k : ℤ) ((k : ℤ) + 1) (by simp) ((rawMap X U V).τ₁.f k v)
          (map_d_eq_zero _ v hv)) =
      K.homologyπ k (K.cyclesMk ((eK k).hom v) (k + 1) (by simp) hv₀) := by
    intro k v hv hv₀
    rw [← homologyMap_cls, supported_singular_class]
    exact relDualEquiv_cls X U V k v hv hv₀
  rw [cls_congr (supSeq X U V).X₁ (by simp) hs'd hs'eq, hcls n w hw hw₀d, hcls p x hx hx₀, relCupSing_homologyπ]
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  have e := HomologicalComplex.i_cyclesMk K ((eK n).hom w) (n + 1) (by simp) hw₀d
  erw [e, hw₀]

end Paracompact

end HodgeLadder.Cup
