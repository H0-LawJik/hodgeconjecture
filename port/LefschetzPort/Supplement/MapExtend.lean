/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend

/-!
# Port supplement to `HodgeConjecture.Mathlib.Algebra.Homology.MapExtend`

Upstream stack part 6/11 (PR #222) adds this lemma to an existing upstream file. The port stages
it here, unchanged, so that upstream's file at the pin is not edited.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]
  {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}
  (K : HomologicalComplex C c) (e : c.Embedding c')

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In a retained degree, the inverse comparison is the inverse grading transport. -/
lemma mapExtendCanonicalIso_inv_f {i : I} {j : J} (h : e.f i = j) :
    (mapExtendCanonicalIso F K e).inv.f j =
    (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
      F.map (K.extendXIso e h).inv := by
  apply (cancel_mono ((mapExtendCanonicalIso F K e).hom.f j)).mp
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [mapExtendCanonicalIso_hom_f F K e h]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]

end HomologicalComplex
