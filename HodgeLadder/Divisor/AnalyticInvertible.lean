module

public import LefschetzPort.AlgebraicGeometry.AnalytificationStalk
public import LefschetzPort.AlgebraicGeometry.InvertibleSheafStalk
public import LefschetzPort.AlgebraicGeometry.InvertibleSheafCoherent
public import LefschetzPort.AlgebraicGeometry.HolomorphicAnalyticSpace
public import LefschetzPort.AlgebraicGeometry.HolomorphicSheafGenerators
public import LefschetzPort.AlgebraicGeometry.ComplexPointClosedPointEquiv
public import LefschetzPort.Oka.AnalyticSpace.PullbackCoherent
public import LefschetzPort.Oka.AlgebraicGeometry.Modules.Coherent
public import LefschetzPort.TauCeti.SheafOfModules.JacobsonLocalTriviality
public import LefschetzPort.RingTheory.FaithfullyFlatRankOne

/-!
# The analytification of an invertible sheaf is invertible

For an invertible sheaf `L` on a smooth projective integral complex scheme, the analytification
`L^an` is invertible, so it has a holomorphic trivializing cover. `L` is coherent (invertible over
the coherent structure sheaf of a Noetherian scheme); `L^an` is coherent (Oka:
pullbacks of coherent sheaves to analytic spaces are coherent); the stalk of `L^an` at `z` is the
stalk of `L` with scalars extended (`moduleAnalytificationStalkIso`), so it is free of rank one;
and `X(ℂ)` is T1, hence Jacobson, so Tau Ceti's closed-point criterion applies. This replaces the
stack's unproved `AnalytificationGenerates` for the purpose of rung `unit-extension-of-invertible`.

## Main results

* `HodgeLadder.isInvertible_moduleAnalytification`
* `HodgeLadder.nonempty_holomorphicTrivializingCover_moduleAnalytification`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint

namespace HodgeLadder

/-- Extension of scalars of a free module of rank one is free of rank one. -/
theorem nonempty_extendScalars_linearEquiv_self {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{0} R) (e : M ≃ₗ[R] R) :
    Nonempty ((ModuleCat.extendScalars f).obj M ≃ₗ[S] S) := by
  algebraize [f]
  exact ⟨(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) e).trans
    (TensorProduct.AlgebraTensorModule.rid R S S)⟩

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

/-- The analytic topology on the complex points of a scheme locally of finite type is T1: each
complex point maps to a closed point, injectively and continuously. -/
instance t1Space_complexPoint : T1Space (ComplexPoint X) := by
  refine ⟨fun z => ?_⟩
  have hz : IsClosed ({(complexPointEquivClosedPoint X z).1} : Set X.left) :=
    (complexPointEquivClosedPoint X z).2
  have hpre : (underlyingContinuousMap X) ⁻¹' {(complexPointEquivClosedPoint X z).1} = {z} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact (complexPointEquivClosedPoint X).injective (Subtype.ext h)
    · rintro rfl; rfl
  rw [← hpre]
  exact hz.preimage (underlyingContinuousMap X).hom.continuous

/-- **The analytification of an invertible sheaf is invertible.** -/
theorem isInvertible_moduleAnalytification (L : X.left.Modules)
    [hL : TauCeti.SheafOfModules.IsInvertible.{0} L] :
    TauCeti.SheafOfModules.IsInvertible.{0}
      ((moduleAnalytification X (TopologicalSpace.dim X.left)).obj L) := by
  set d := TopologicalSpace.dim X.left
  have hcohX : (SheafOfModules.unit X.left.toLocallyRingedSpace.ringSheaf).IsCoherent :=
    X.left.isCoherentStructureSheaf
  have hLcoh : (show SheafOfModules.{0} X.left.toLocallyRingedSpace.ringSheaf from L).IsCoherent :=
    @LocallyRingedSpace.isCoherent_of_isInvertible X.left.toLocallyRingedSpace L hcohX hL
  have hLan : ((analytificationToAlgebraic X d).pullbackModules.obj
      (show SheafOfModules.{0} X.left.toLocallyRingedSpace.ringSheaf from L)).IsCoherent :=
    @ComplexAnalytic.isCoherent_pullbackModules_of_isCoherent (holomorphicAnalyticSpace X d) _
      (analytificationToAlgebraic X d) L hLcoh
  have hBasis (z : closedPoints (holomorphicLocallyRingedSpace X d)) :
      Nonempty (Module.Basis PUnit.{1}
        ((holomorphicLocallyRingedSpace X d).presheaf.stalk z.1)
        (((holomorphicLocallyRingedSpace X d).stalkFunctor z.1).obj
          ((analytificationToAlgebraic X d).pullbackModules.obj
            (show SheafOfModules.{0} X.left.toLocallyRingedSpace.ringSheaf from L)))) := by
    obtain ⟨e⟩ := @LocallyRingedSpace.nonempty_stalkLinearEquiv_of_isInvertible
      X.left.toLocallyRingedSpace L hL (z.1 : ComplexPoint X).underlying
    let f : X.left.presheaf.stalk (z.1 : ComplexPoint X).underlying →+*
        (holomorphicFunctionSheaf X d).presheaf.stalk z.1 :=
      ((analytificationToPresheafedSpace X d).stalkMap z.1).hom
    obtain ⟨e'⟩ := nonempty_extendScalars_linearEquiv_self f _ e
    change Nonempty (Module.Basis PUnit.{1} ((holomorphicFunctionSheaf X d).presheaf.stalk z.1)
      ((SheafOfModules.stalkFunctor (R := (holomorphicFunctionSheaf X d).presheaf)
          (hR := (holomorphicRingSheaf X d).property) z.1).obj
            ((moduleAnalytification X d).obj L)))
    exact ⟨Module.basisPUnitOfLinearEquivSelf _ _
      (((moduleAnalytificationStalkIso X d z.1).app L).toLinearEquiv.trans e')⟩
  have hT1 : T1Space (holomorphicLocallyRingedSpace X d).toTopCat := t1Space_complexPoint X
  exact @LocallyRingedSpace.isInvertible_of_isCoherent_of_basis_closedPoints
    (holomorphicLocallyRingedSpace X d) inferInstance _ hLan hBasis

/-- The analytification of an invertible sheaf has a holomorphic trivializing cover. -/
theorem nonempty_holomorphicTrivializingCover_moduleAnalytification (L : X.left.Modules)
    [TauCeti.SheafOfModules.IsInvertible.{0} L] :
    Nonempty (HolomorphicTrivializingCover
      ((moduleAnalytification X (TopologicalSpace.dim X.left)).obj L)) :=
  nonempty_holomorphicTrivializingCover_of_isInvertible _
    (isInvertible_moduleAnalytification X L)

end HodgeLadder
