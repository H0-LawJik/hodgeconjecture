module

public import HodgeLadder.Hodge.CompactHolomorphic
public import HodgeLadder.Tests.ProjectiveLine
public import Other.AlgebraicGeometry.ComplexPoint.SmoothConnected

/-!
# Global holomorphic functions on ℙ¹: constants, and a nonconstant local section

Tests of rung `compact-holomorphic-locally-constant`, whose general lemmas are in
`HodgeLadder.Hodge.CompactHolomorphic`. On `ℙ¹`, `c ↦` the constant section `c` is a bijection
`ℂ → Γ(ℙ¹(ℂ), 𝒪)` (`projectiveLine_existsUnique_const`): `ℙ¹(ℂ)` is compact (projective),
connected and nonempty (upstream's `ComplexPoint.connectedSpace`). Upstream's 𝒪 on `ℙ¹` has a
section with two values on a chart domain, the first chart coordinate
(`projectiveLine_exists_nonconstant_section`), so compactness is load-bearing. No sign or scalar
enters.

## Main definitions

* `HodgeLadder.Tests.projectiveLineConst`

## Main results

* `HodgeLadder.Tests.projectiveLine_existsUnique_const`
* `HodgeLadder.Tests.projectiveLine_exists_nonconstant_section`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry ComplexPoint Opposite
open scoped ContDiff Manifold

namespace HodgeLadder.Tests

/-- The constant global section `c` of upstream's `holomorphicFunctionSheaf` on `ℙ¹`. -/
def projectiveLineConst (c : ℂ) :
    (holomorphicFunctionSheaf projectiveLine 1).presheaf.obj (Opposite.op ⊤) :=
  show C^ω⟮𝓘(ℂ, Fin 1 → ℂ), (⊤ : Opens (ComplexPoint projectiveLine)); ℂ⟯ from
    ContMDiffMap.const c

/-- **Nonvacuity on `ℙ¹`.** Every global holomorphic function on `ℙ¹(ℂ)` is exactly one constant
section: `c ↦ projectiveLineConst c` is a bijection `ℂ → Γ(ℙ¹(ℂ), 𝒪)`. `ℙ¹(ℂ)` is compact
(projective), connected and nonempty (upstream's `ComplexPoint.connectedSpace`). -/
theorem projectiveLine_existsUnique_const
    (s : (holomorphicFunctionSheaf projectiveLine 1).presheaf.obj (Opposite.op ⊤)) :
    ∃! c : ℂ, s = projectiveLineConst c := by
  have : QuasiSeparatedSpace projectiveLine.left :=
    quasiSeparatedSpace_of_quasiSeparated projectiveLine.hom
  have : ConnectedSpace (ComplexPoint projectiveLine) := ComplexPoint.connectedSpace _
  obtain ⟨c, hc⟩ := exists_eq_const_holomorphicFunctionSheaf_top projectiveLine 1 s
  obtain ⟨z⟩ := (inferInstance : Nonempty (ComplexPoint projectiveLine))
  refine ⟨c, ContMDiffMap.ext fun w ↦ hc w, fun c' hc' ↦ ?_⟩
  have := hc ⟨z, trivial⟩
  rw [hc'] at this
  exact this

/-- **Compactness is load-bearing.** Upstream's `holomorphicFunctionSheaf` on `ℙ¹` has a section
taking two values on a chart domain, the first chart coordinate; so 𝒪 on ℙ¹ has sections that are
not locally constant, and `projectiveLine_existsUnique_const` rests on the maximum principle. -/
theorem projectiveLine_exists_nonconstant_section : ∃ (U : Opens (ComplexPoint projectiveLine))
    (s : (holomorphicFunctionSheaf projectiveLine 1).presheaf.obj (op U)) (a b : U),
    (show C^ω⟮𝓘(ℂ, Fin 1 → ℂ), U; ℂ⟯ from s) a ≠
      (show C^ω⟮𝓘(ℂ, Fin 1 → ℂ), U; ℂ⟯ from s) b := by
  have : QuasiSeparatedSpace projectiveLine.left :=
    quasiSeparatedSpace_of_quasiSeparated projectiveLine.hom
  have : ConnectedSpace (ComplexPoint projectiveLine) := ComplexPoint.connectedSpace _
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (ComplexPoint projectiveLine))
  let e := chartAt (Fin 1 → ℂ) x₀
  let U : Opens (ComplexPoint projectiveLine) := ⟨e.source, e.open_source⟩
  have hf : ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω (fun z : U ↦ e z.1 0) := by
    have h1 : ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω (fun z : U ↦ e z.1) :=
      (contMDiffOn_chart (x := x₀)).comp_contMDiff contMDiff_subtype_val (fun z ↦ z.2)
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).contMDiff.comp h1
  let s : C^ω⟮𝓘(ℂ, Fin 1 → ℂ), U; ℂ⟯ := ⟨_, hf⟩
  have hy : e x₀ ∈ e.target := e.map_source (mem_chart_source _ x₀)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target _ hy
  let y' : Fin 1 → ℂ := e x₀ + fun _ ↦ ((ε / 2 : ℝ) : ℂ)
  have hy' : y' ∈ e.target := hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [y', add_sub_cancel_left, pi_norm_const, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith)
  refine ⟨U, s, ⟨x₀, mem_chart_source _ x₀⟩, ⟨e.symm y', e.map_target hy'⟩, ?_⟩
  change e x₀ 0 ≠ e (e.symm y') 0
  rw [e.right_inv hy']
  simp only [y', Pi.add_apply, ne_eq, left_eq_add, Complex.ofReal_eq_zero]
  exact (half_pos hε).ne'

end HodgeLadder.Tests
