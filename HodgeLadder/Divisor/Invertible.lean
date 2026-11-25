module

public import LefschetzPort.AlgebraicGeometry.InvertibleSheafRationalSection
public import LefschetzPort.TauCeti.SheafOfModules.JacobsonLocalTriviality
public import LefschetzPort.TauCeti.SheafOfModules.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# A generating section is a trivialization

For a sheaf of modules `L` on a scheme and a section `g ∈ Γ(L, U)` that generates (every section
over every `V ⊆ U` is a unique multiple of `g`), multiplication by `g` is an isomorphism
`𝒪|_U ≅ L|_U`. This is the converse of the stack's `unitIsoSection`. With Tau Ceti's
`LocalTrivializations.ofClosedPoints`, generating sections near all closed points of a Jacobson
scheme make `L` invertible. Part of rung `prime-divisor-ideal-sheaf`.

## Main results

* `HodgeLadder.isoOfGenerates`
* `HodgeLadder.isInvertible_of_generates_closedPoints`
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Scheme.Modules

universe u

namespace HodgeLadder

variable {S : Scheme.{u}} (L : S.Modules)

/-- The restrictions of a section `g ∈ Γ(L, U)` to the opens below `U`, as a section of `L|_U`. -/
def sectionOfRestrictions {U : S.Opens} (g : Γ(L, U)) : (L.over U).val.sections :=
  PresheafOfModules.sectionsMk (fun Y => L.val.map Y.unop.hom.op g) (by
    intro X Y f
    change (L.presheaf.map X.unop.hom.op ≫ L.presheaf.map f.unop.left.op) g =
      L.presheaf.map Y.unop.hom.op g
    rw [← Functor.map_comp]
    rfl)

/-- Multiplication by `g`, as a morphism `𝒪|_U ⟶ L|_U`. -/
def homOfSection {U : S.Opens} (g : Γ(L, U)) :
    SheafOfModules.unit (S.ringCatSheaf.over U) ⟶ L.over U :=
  (L.over U).unitHomEquiv.symm (sectionOfRestrictions L g)

/-- **A generating section is a trivialization.** -/
theorem isIso_homOfSection {U : S.Opens} {g : Γ(L, U)} (hg : Generates g) :
    IsIso (homOfSection L g) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have hY : Y.unop.left ≤ U := Y.unop.hom.le
  change Function.Bijective (fun r : Γ(S, Y.unop.left) => r • resSection L hY g)
  exact hg Y.unop.left hY

/-- `L|_U ≅ 𝒪|_U` from a generating section. -/
def isoOfGenerates {U : S.Opens} {g : Γ(L, U)} (hg : Generates g) :
    SheafOfModules.unit (S.ringCatSheaf.over U) ≅ L.over U :=
  have := isIso_homOfSection L hg
  asIso (homOfSection L g)

/-- **Generating sections near all closed points make a sheaf invertible** (on a scheme whose
underlying space is Jacobson). -/
theorem isInvertible_of_generates_closedPoints [JacobsonSpace S]
    (U : closedPoints S → S.Opens) (hU : ∀ x, x.1 ∈ U x) (g : ∀ x, Γ(L, U x))
    (hg : ∀ x, Generates (g x)) : TauCeti.SheafOfModules.IsInvertible.{u} L :=
  (TauCeti.SheafOfModules.LocalTrivializations.ofClosedPoints U hU (fun x =>
    TauCeti.SheafOfModules.freePUnitIsoUnit _ ≪≫ isoOfGenerates L (hg x))).isInvertible

end HodgeLadder
