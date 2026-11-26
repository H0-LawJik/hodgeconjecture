module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections
public import HodgeConjecture.Mathlib.CategoryTheory.Sites.SheafCohomology.Pair

/-!
# The section `1` of the constant sheaf and the generator of `ℤ[⊤]`

Part of rung `supported-forget-compat` (front `cup`). Upstream evaluates maps out of the constant
sheaf `ℤ_Y` at the section `1` through the constant-sheaf adjunction
(`integerConstantHomAddEquivGlobalSections`), and maps out of `ℤ[⊤]` at its generator through
sheafification (`freeAbelianSheafHomAddEquiv`). Under upstream's `freeAbelianSheafTerminalIso` and
`ULift`, the generator goes to `1`.

## Main results

* `HodgeLadder.Cup.integerConstantHomAddEquivGlobalSections_apply`,
  `HodgeLadder.Cup.terminalIso_generator`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}}

set_option backward.isDefEq.respectTransparency false in
/-- **Upstream's evaluation at `1` of a map out of `ℤ_Y`.** -/
lemma integerConstantHomAddEquivGlobalSections_apply (F : TopCat.Sheaf AddCommGrpCat Y)
    (φ : (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) :
    TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F φ =
      φ.hom.app (op ⊤) ((toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op ⊤) (1 : ℤ)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Upstream's terminal isomorphism sends the generator of `ℤ[⊤]` to the section `1`**, read in
`ULift ℤ`. -/
lemma terminalIso_generator :
    (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso (J := Opens.grothendieckTopology Y)
        isTerminalTop).hom.hom.app (op ⊤)
        (CategoryTheory.Sheaf.freeAbelianSheafGenerator (J := Opens.grothendieckTopology Y) ⊤) =
      ((TopCat.Sheaf.constantFunctor Y).map (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso.inv).hom.app
        (op ⊤) ((toSheafify (Opens.grothendieckTopology Y)
          ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op ⊤) (1 : ℤ)) := by
  have hn : ∀ {P Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}} (N : P ⟶ Q) (x : P.obj (op ⊤)),
      (sheafifyMap (Opens.grothendieckTopology Y) N).app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology Y) P).app (op ⊤) x) =
      (toSheafify (Opens.grothendieckTopology Y) Q).app (op ⊤) (N.app (op ⊤) x) := by
    intro P Q N x
    have h := congrArg (fun f => f.app (op ⊤)) (toSheafify_naturality (Opens.grothendieckTopology Y) N)
    simp only [NatTrans.comp_app] at h
    exact (ConcreteCategory.congr_hom h x).symm
  unfold CategoryTheory.Sheaf.freeAbelianSheafTerminalIso CategoryTheory.Sheaf.freeAbelianSheafGenerator
  erw [hn, hn]
  rfl

end HodgeLadder.Cup
