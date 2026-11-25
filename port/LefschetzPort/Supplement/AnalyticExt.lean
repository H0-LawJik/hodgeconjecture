/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration

/-!
# Port supplement: universe-0 `Ext` for analytic sheaves

Upstream main computes the cohomology of constant sheaves on `X(ℂ)` with a universe-0 `HasExt`
instance that is local to `Hodge/Filtration.lean`, so the statement of record (`H^n(X; K)`,
`Hdg^p(X; K)`) lives in universe 0. The upstream stack (part 2/11, PR #218) makes that instance
global, and the rest of the stack elaborates `Ext` and `H^n` against it. The port declares the
same global instance here and imports it into every staged geometry and topology file, so that
staged statements land in the same universe as main's definitions.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

/-- `Ext`-groups of sheaves of abelian groups on `X(ℂ)`, in universe zero, as in upstream main's
`Hodge/Filtration.lean` (where the instance is local). -/
instance analyticHasExt (X : Over (Spec ↧ℂ)) :
    HasExt.{0} (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  inferInstance

end AlgebraicGeometry.ComplexPoint
