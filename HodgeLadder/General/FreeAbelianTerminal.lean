module

public import HodgeConjecture.Mathlib.CategoryTheory.Sites.SheafCohomology.Pair

/-!
# The generator of `ℤ[T]` for a terminal object `T`

Upstream's `CategoryTheory.Sheaf.freeAbelianSheafTerminalIso` identifies the free abelian sheaf
`ℤ[T]` on a terminal object `T` of a site with the constant sheaf `ULift ℤ`. This file computes it
on the generator `[𝟙 T]` (upstream's `freeAbelianSheafGenerator`): the image is the section `1`
of the constant sheaf over `T`, that is, the image of `ULift.up 1` under sheafification. The
statement holds on any site with a terminal object; `HodgeLadder.Cup.terminalIso_generator` is the
case of the open `⊤` of a topological space, with the value read in `ℤ`.

## Main results

* `HodgeLadder.toSheafify_app_sheafifyMap_app`: `sheafifyMap` on the image of a section
* `HodgeLadder.freeAbelianSheafTerminalIso_hom_generator`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace HodgeLadder

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

/-- **`sheafifyMap` on sections coming from the presheaf**: for `N : P ⟶ Q` and a section `x` of
`P` over `U`, the image of `x` in `sheafify P` goes to the image of `N x` in `sheafify Q`. -/
lemma toSheafify_app_sheafifyMap_app {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (N : P ⟶ Q) (U : Cᵒᵖ)
    (x : P.obj U) :
    (sheafifyMap J N).app U ((toSheafify J P).app U x) =
      (toSheafify J Q).app U (N.app U x) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality J N) U) x).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Upstream's terminal isomorphism sends the generator `[𝟙 T]` of `ℤ[T]` to the section `1`**
of the constant sheaf `ULift ℤ` over `T`. -/
lemma freeAbelianSheafTerminalIso_hom_generator {T : C} (hT : IsTerminal T) :
    (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso (J := J) hT).hom.hom.app (op T)
        (CategoryTheory.Sheaf.freeAbelianSheafGenerator (J := J) T) =
      (toSheafify J ((Functor.const _).obj (AddCommGrpCat.of (ULift ℤ)))).app (op T)
        (ULift.up 1) := by
  unfold CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
    CategoryTheory.Sheaf.freeAbelianSheafGenerator
  erw [toSheafify_app_sheafifyMap_app]
  rfl

end HodgeLadder
