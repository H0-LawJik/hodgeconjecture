module

public import HodgeLadder.Cup.NamedCocycle
public import HodgeLadder.Cup.SupportedStep2

/-!
# Composing a supported cocycle with right multiplication

Rung `supported-named-cocycle-comp` (front `cup`, supported comparison; the supported analogue of
`named-cocycle-comp`). A Hom-complex cocycle `z : ℤ[V, W][0] → S` of degree `p` out of the pair
sheaf names a section of `S^p` over `V`: its evaluation at the generator
(`pairSheafHomEvaluation`), which vanishes on `W`. Composing with right multiplication `R_b` by a
global cocycle `b` of degree `q` multiplies that section by `b`, with the sign `(−1)^{pq}` of
`rightMulCochain`:
`ev (z · R_b) = (−1)^{pq} · (ev z) ∪ b`.
Supported sections inject into all sections over `V`, and upstream's
`pairSheafHomIsoSupportedSections_hom_inclusion` identifies the inclusion of the supported section
of `z` with `ev z`, so this determines the supported section of `z · R_b`.

## Main results

* `HodgeLadder.Cup.pairEval`, `HodgeLadder.Cup.xIso_smul_apply`,
  `HodgeLadder.Cup.pairSheafEvaluation_cocycleComp_rightMul`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TopCat.Sheaf AlgebraicTopology.Singular
  CochainComplex.HomComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}} (U V W : Opens Y) (hW : V ⊓ U = W)

/-- The section over `V` named by a cochain out of the pair sheaf, in degree `k`. -/
def pairEval {k : ℕ} {n : ℤ} (hk : (k : ℤ) = n)
    (c : Cochain ((CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat Y) 0).obj
      (pairSheaf' Y U V W hW)) (sInt Y) n) :
    (singularCochainSheaf ℚ Y k).obj.obj (op V) :=
  ((sInt_XIso hk).hom.hom.app (op V))
    (pairSheafHomEvaluation Y U V W hW ((sInt Y).X n) (Cochain.fromSingleEquiv (zero_add n) c))

/-- Sections of a sheaf map conjugated by isomorphisms and scaled by an integer. -/
lemma xIso_smul_apply {A B A' B' : TopCat.Sheaf AddCommGrpCat Y} (e : A' ≅ A) (e' : B' ≅ B)
    (c : ℤ) (f : A ⟶ B) (x : A'.obj.obj (op V)) :
    e'.hom.hom.app (op V) ((e.hom ≫ (c • f) ≫ e'.inv).hom.app (op V) x) =
      c • f.hom.app (op V) (e.hom.hom.app (op V) x) := by
  have h1 : (e.hom ≫ (c • f) ≫ e'.inv) ≫ e'.hom = e.hom ≫ (c • f) := by simp
  have h2 := ConcreteCategory.congr_hom (congrArg (fun g : A' ⟶ B => g.hom.app (op V)) h1) x
  have h3 := ConcreteCategory.congr_hom (congrArg (fun g => NatTrans.app g (op V))
    ((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map_zsmul (f := f) (r := c)))
    (e.hom.hom.app (op V) x)
  refine h2.trans (h3.trans ?_)
  simp [NatTrans.app_zsmul]

set_option backward.isDefEq.respectTransparency false in
/-- **Composing with right multiplication multiplies the named section by `b`**, with the sign
`(−1)^{pq}`. -/
theorem pairSheafEvaluation_cocycleComp_rightMul {p q : ℕ}
    (z : Cocycle ((CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat Y) 0).obj
      (pairSheaf' Y U V W hW)) (sInt Y) p)
    (b : OpenCochains ℚ Y (op ⊤) q) (hb : (singularCochainCoboundary ℚ Y q).app (op ⊤) b = 0) :
    pairEval U V W hW (k := p + q) (by push_cast; rfl)
        (cocycleComp z (rightMulCocycle b hb) (show (p : ℤ) + q = ((p + q : ℕ) : ℤ) by push_cast; rfl)).1 =
      (((p : ℤ) * q).negOnePow : ℤ) •
        (rightMulSheaf b p (p + q) rfl).hom.app (op V) (pairEval U V W hW rfl z.1) := by
  unfold pairEval
  have h1 : (cocycleComp z (rightMulCocycle b hb)
      (show (p : ℤ) + q = ((p + q : ℕ) : ℤ) by push_cast; rfl)).1 =
      z.1.comp (rightMulCochain b) (show (p : ℤ) + q = ((p + q : ℕ) : ℤ) by push_cast; rfl) := rfl
  rw [h1, fromSingleEquiv_comp,
    rightMulCochain_v b p (p + q) (p : ℤ) ((p + q : ℕ) : ℤ) rfl rfl rfl]
  -- evaluation at the generator is natural in the target
  have hev : ∀ {G G' : TopCat.Sheaf AddCommGrpCat Y} (f : pairSheaf' Y U V W hW ⟶ G) (g : G ⟶ G'),
      pairSheafHomEvaluation Y U V W hW G' (f ≫ g) =
        g.hom.app (op V) (pairSheafHomEvaluation Y U V W hW G f) := fun _ _ => rfl
  erw [hev, hev]
  exact xIso_smul_apply V _ _ _ _ _

end HodgeLadder.Cup
