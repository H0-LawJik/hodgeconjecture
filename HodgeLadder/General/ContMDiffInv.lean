module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The inverse of a nowhere-vanishing smooth function

For a `C^n` map `f : M → 𝕜` into a nontrivially normed field that vanishes nowhere, the pointwise
inverse `x ↦ (f x)⁻¹` is again `C^n` (Mathlib's `ContMDiff.inv₀`), and it is a two-sided inverse
of `f` in the ring `C^n⟮I, M; 𝕜⟯`. Mathlib states the `C^n` property of the inverse; the bundled
map and its ring identities are kept here (decision 0011). Rung `elliptic-omega` uses it for the
coefficients `(3x² − 1)⁻¹` and `(1 + 2uw)⁻¹` of the holomorphic form `dx / y` on the plane cubic.

## Main definitions

* `HodgeLadder.contMDiffMapInv₀`: the inverse of a nowhere-vanishing `C^n` function

## Main results

* `HodgeLadder.contMDiffMapInv₀_apply`, `HodgeLadder.contMDiffMapInv₀_mul`,
  `HodgeLadder.mul_contMDiffMapInv₀`
-/

@[expose] public section

open scoped Manifold ContDiff

namespace HodgeLadder

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- The pointwise inverse `x ↦ (f x)⁻¹` of a nowhere-vanishing `C^n` function, as a `C^n`
function (Mathlib's `ContMDiff.inv₀`). -/
def contMDiffMapInv₀ (f : C^n⟮I, M; 𝕜⟯) (hf : ∀ x, f x ≠ 0) : C^n⟮I, M; 𝕜⟯ :=
  ⟨fun x => (f x)⁻¹, f.contMDiff.inv₀ hf⟩

/-- The value of the inverse is the inverse of the value. -/
@[simp] theorem contMDiffMapInv₀_apply (f : C^n⟮I, M; 𝕜⟯) (hf : ∀ x, f x ≠ 0) (x : M) :
    contMDiffMapInv₀ f hf x = (f x)⁻¹ := rfl

/-- `f⁻¹ · f = 1` in the ring of `C^n` functions. -/
theorem contMDiffMapInv₀_mul (f : C^n⟮I, M; 𝕜⟯) (hf : ∀ x, f x ≠ 0) :
    contMDiffMapInv₀ f hf * f = 1 := by
  ext x
  exact inv_mul_cancel₀ (hf x)

/-- `f · f⁻¹ = 1` in the ring of `C^n` functions. -/
theorem mul_contMDiffMapInv₀ (f : C^n⟮I, M; 𝕜⟯) (hf : ∀ x, f x ≠ 0) :
    f * contMDiffMapInv₀ f hf = 1 := by
  ext x
  exact mul_inv_cancel₀ (hf x)

end HodgeLadder
