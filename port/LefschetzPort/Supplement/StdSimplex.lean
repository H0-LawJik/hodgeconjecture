/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Port supplement: the topological standard simplex

The upstream stack was written when Mathlib's topological standard simplex was the subset
`stdSimplex ℝ (Fin (n + 1))` of `Fin (n + 1) → ℝ`. At the current pin, singular simplices are
maps from the type `Convexity.StdSimplex ℝ (Fin (n + 1))`. This file identifies the two by a
homeomorphism (the weights map) and transfers the contractibility and local path-connectedness
the stack uses.

## Main definitions

* `LefschetzPort.stdSimplexHomeomorph n`: `Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ
  stdSimplex ℝ (Fin (n + 1))`, sending a point to its weights.
-/

set_option linter.deprecated false

@[expose] public section

open Topology

namespace LefschetzPort

/-- The weights of points of `Convexity.StdSimplex ℝ (Fin (n + 1))` fill out exactly the subset
`stdSimplex ℝ (Fin (n + 1))`. -/
lemma range_weights_eq_stdSimplex (n : ℕ) :
    Set.range (fun t ↦ t.weights : Convexity.StdSimplex ℝ (Fin (n + 1)) → Fin (n + 1) → ℝ) =
      stdSimplex ℝ (Fin (n + 1)) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  ext s
  simp [stdSimplex, Set.mem_iInter]

/-- The standard `n`-simplex as a type is homeomorphic to the standard `n`-simplex as a subset of
`Fin (n + 1) → ℝ`, by taking weights. -/
noncomputable def stdSimplexHomeomorph (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ stdSimplex ℝ (Fin (n + 1)) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).toHomeomorph.trans
    (Homeomorph.setCongr (range_weights_eq_stdSimplex n))

lemma stdSimplex_nonempty (n : ℕ) : (stdSimplex ℝ (Fin (n + 1))).Nonempty :=
  ⟨_, (stdSimplexHomeomorph n (Classical.arbitrary _)).2⟩

instance stdSimplex_contractibleSpace (n : ℕ) :
    ContractibleSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  haveI : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace (stdSimplex_nonempty n)
  (stdSimplexHomeomorph n).contractibleSpace

instance stdSimplex_locallyPathConnectedSpace (n : ℕ) :
    LocallyPathConnectedSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  haveI := (convex_stdSimplex ℝ (Fin (n + 1))).locallyPathConnectedSpace
  (stdSimplexHomeomorph n).symm.locallyPathConnectedSpace

end LefschetzPort
