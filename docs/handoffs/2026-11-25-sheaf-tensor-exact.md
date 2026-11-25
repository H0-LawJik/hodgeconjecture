# Handoff 2026-11-25: `sheaf-tensor-exact`

- Moved: rung checked (standard axioms), module `HodgeLadder.Cup.SheafTensor`.
- Monoidal structure: Mathlib `Sheaf.monoidalCategory (J Y) (ModuleCat ℚ)` as the local instance `HodgeLadder.Cup.sheafMonoidal`; braiding `Sheaf.braidedCategory` as `sheafBraided`. Downstream files must activate the same local instances (`attribute [local instance] sheafMonoidal sheafBraided`).
- `tensor_exact`: for every sheaf `F`, `tensorLeft F` and `tensorRight F` preserve finite limits and finite colimits and are additive; they also preserve small colimits (`tensorLeft_preservesColimits`, `tensorRight_preservesColimits`). All are instances.
- Route: `tensorLeftIso : tensorLeft F ≅ presheafQ ⋙ tensorLeft F.obj ⋙ sheafifyQ`, from `Functor.Monoidal.commTensorLeft` for sheafification and the counit isomorphism. Pointwise tensor over ℚ is left exact (every ℚ-module is flat, `Module.Flat` and `ModuleCat` tensor exactness); colimits by `preservesColimitsOfShape_of_sheafify`; `tensorRight` by `BraidedCategory.tensorLeftIsoTensorRight`.
- The stalk route (`Sites/Point/*`) was not needed.
- Unit: `unitIsoQX : 𝟙_ ≅ QX Y` is `Iso.refl`; the unit of the localized structure is the sheafified constant presheaf, which is how `constantSheaf` is defined.
- Upstream candidate logged in `docs/gaps.md`.
- Next: `supported-cup` (α ↦ (α ⊗ ℚ_W) ≫ β) can use these instances to map `Ext` classes along `tensorRight`.
