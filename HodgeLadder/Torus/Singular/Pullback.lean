module

public import HodgeLadder.Torus.Singular.Cohomology
public import HodgeLadder.Cup.WindingPullback

/-!
# The rotation of `T²`, `H¹(T¹; ℚ)`, and transport of the torus bases along `Y ≃ₜ Tⁿ`

Rung `winding-class-pullback` (issue #267, sketch `docs/sketches/torus-singular-cohomology.md`,
order 5). Everything here is singular: upstream's `AlgebraicTopology.Singular.Cohomology ℚ`, its
pullback `cohomologyMap`, and the ladder's cup `HodgeLadder.Cup.cupSing`. The sheaf-singular
comparison `Ψ` does not enter. The any-space input is `HodgeLadder.Cup.WindingPullback`:
`f^* [g] = [g ∘ f]`, `[g g'] = [g] + [g']`, and `h^*` as a linear equivalence.

On `T² = UnitAddTorus (Fin 2)` let `rot x = ![-x 1, x 0]`, the rotation `(s, t) ↦ (−t, s)`
(multiplication by `i` in the basis `(ω₁, ω₂) = (c, ic)` of the sketch). Since
`coordChar 0 ∘ rot = (coordChar 1)⁻¹` and `coordChar 1 ∘ rot = coordChar 0` pointwise,

  `rot^* a₀ = −a₁` and `rot^* a₁ = a₀`.

The sign is computed by the definition: `exp (2πi (−x₁)) = exp (2πi x₁)⁻¹`. The opposite
orientation `ω₂ = −iω₁` would give the inverse rotation and swap both signs; the square
`(rot^*)² = −1` on `H¹(T²; ℚ)` holds for either, and `rot^*` is the identity on
`H²(T²; ℚ)` (`rot^* (a₀ ⌣ a₁) = (−a₁) ⌣ a₀ = a₀ ⌣ a₁`, the sign `(−1)^{1·1}` of
`cupSing_gradedComm` cancelling the `−1` of `rot^* a₀`). For a map `e` with `h ∘ e = rot ∘ h`
the same signs hold for `e^*` on the transported classes (`homeoWinding_pullback_of_comm_rot`).

The `n = 1` case of the `H¹` basis of rung `torus-singular-cohomology`, left open there, closes
here: the projection `T² → T¹` to coordinate `0` pulls `a₀` back to `a₀ ≠ 0` on `T²`.

For `h : Y ≃ₜ Tⁿ`, `h^*` carries `aᵢ` to the winding class of `coordChar i ∘ h` and `aᵢ ⌣ aⱼ`
to the cup of those (naturality `cupSing_cohomologyMap`). So the winding classes of
`coordChar i ∘ h` form a basis of `H¹(Y; ℚ)` and their cups with `i < j` a basis of
`H²(Y; ℚ)`, for every `n`. On a product `Y₁ × Y₂` with `prodTorusHomeo h₁ h₂` (through
`Fin.appendHomeomorph`, first factor first) the first `m` transported classes are pulled back
from `Y₁` and the last `n` from `Y₂`.

## Main definitions

* `HodgeLadder.Torus.rot`: the rotation `x ↦ ![-x 1, x 0]` of `T²`.
* `HodgeLadder.Torus.projFirst`: the projection `T² → T¹` to coordinate `0`.
* `HodgeLadder.Torus.homeoWinding`, `HodgeLadder.Torus.homeoCup`,
  `HodgeLadder.Torus.homeoWindingBasis`, `HodgeLadder.Torus.homeoCupBasis`: the transported
  classes and bases.
* `HodgeLadder.Torus.prodTorusHomeo`: `Y₁ × Y₂ ≃ₜ T^{m+n}` from `h₁ : Y₁ ≃ₜ Tᵐ`,
  `h₂ : Y₂ ≃ₜ Tⁿ`.

## Main results

* `HodgeLadder.Torus.rot_pullback_coordWinding`: `rot^* a₀ = −a₁ ∧ rot^* a₁ = a₀`;
  `HodgeLadder.Torus.rot_pullback_coordWinding_zero_ne`: `rot^* a₀ ≠ a₁`;
  `HodgeLadder.Torus.rot_pullback_sq`: `(rot^*)² = −1` on `H¹(T²; ℚ)`;
  `HodgeLadder.Torus.rot_pullback_coordCup`: `rot^* (a₀ ⌣ a₁) = a₀ ⌣ a₁`;
  `HodgeLadder.Torus.homeoWinding_pullback_of_comm_rot`.
* `HodgeLadder.Torus.coordWinding_torus_one_ne_zero`,
  `HodgeLadder.Torus.linearIndependent_coordWinding_all`, `HodgeLadder.Torus.span_coordWinding_all`,
  `HodgeLadder.Torus.finrank_cohomology_one_torus_all`: `H¹(Tⁿ; ℚ)` has basis
  `a₀, …, a_{n−1}` for every `n`.
* `HodgeLadder.Torus.linearIndependent_windingClass_of_homeomorph`,
  `HodgeLadder.Torus.span_windingClass_of_homeomorph`,
  `HodgeLadder.Torus.linearIndependent_cupWinding_of_homeomorph`,
  `HodgeLadder.Torus.span_cupWinding_of_homeomorph`,
  `HodgeLadder.Torus.finrank_cohomology_one_of_homeomorph`,
  `HodgeLadder.Torus.finrank_cohomology_two_of_homeomorph`.
* `HodgeLadder.Torus.homeoWinding_prodTorusHomeo_castAdd`,
  `HodgeLadder.Torus.homeoWinding_prodTorusHomeo_natAdd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology.Singular

namespace HodgeLadder.Torus

open HodgeLadder.Cup

/-! ### The rotation of `T²` -/

/-- **The rotation `rot x = ![-x 1, x 0]` of `T²`**, `(s, t) ↦ (−t, s)`: multiplication by `i`
in the basis `(ω₁, ω₂) = (c, ic)`. -/
def rot : torus 2 ⟶ torus 2 :=
  TopCat.ofHom ⟨fun x => ![-(x : UnitAddTorus (Fin 2)) 1, (x : UnitAddTorus (Fin 2)) 0], by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact (continuous_apply 1).neg
    · exact continuous_apply 0⟩

/-- **`rot^* a₀ = −a₁`**: `coordChar 0 ∘ rot = exp (2πi (−x₁)) = (coordChar 1)⁻¹`. -/
theorem rot_pullback_coordWinding_zero :
    cohomologyMap ℚ 1 rot (coordWinding 0) = -coordWinding 1 := by
  rw [coordWinding, windingClass_comp, coordWinding]
  refine windingClass_eq_neg_of_mul_eq_one _ _ _ _ fun x => ?_
  change ((AddCircle.toCircle (-(x : UnitAddTorus (Fin 2)) 1) : Circle) : ℂ) *
    ((AddCircle.toCircle ((x : UnitAddTorus (Fin 2)) 1) : Circle) : ℂ) = 1
  rw [AddCircle.toCircle_neg, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

/-- **`rot^* a₁ = a₀`**: `coordChar 1 ∘ rot = coordChar 0`. -/
theorem rot_pullback_coordWinding_one :
    cohomologyMap ℚ 1 rot (coordWinding 1) = coordWinding 0 := by
  rw [coordWinding, windingClass_comp, coordWinding]
  exact windingClass_ext _ _ fun _ => rfl

/-- **The action of `rot` on `H¹(T²; ℚ)`**: `rot^* a₀ = −a₁` and `rot^* a₁ = a₀`, exact. -/
theorem rot_pullback_coordWinding :
    cohomologyMap ℚ 1 rot (coordWinding 0) = -coordWinding 1 ∧
      cohomologyMap ℚ 1 rot (coordWinding 1) = coordWinding 0 :=
  ⟨rot_pullback_coordWinding_zero, rot_pullback_coordWinding_one⟩

/-- **The sign is visible**: `rot^* a₀ ≠ a₁`, since `a₁ ≠ 0` and `−a₁ ≠ a₁` over `ℚ`. -/
theorem rot_pullback_coordWinding_zero_ne :
    cohomologyMap ℚ 1 rot (coordWinding 0) ≠ coordWinding 1 := by
  rw [rot_pullback_coordWinding_zero]
  intro h
  have h2 : (2 : ℚ) • coordWinding (n := 2) 1 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  have hne := (linearIndependent_coordWinding (n := 2) le_rfl).ne_zero 1
  exact hne ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-- **`(rot^*)² = −1` on `H¹(T²; ℚ)`**, checked on the basis `a₀, a₁`. -/
theorem rot_pullback_sq (a : Cohomology ℚ (torus 2) 1) :
    cohomologyMap ℚ 1 rot (cohomologyMap ℚ 1 rot a) = -a := by
  have key : ((cohomologyMap ℚ 1 rot).comp (cohomologyMap ℚ 1 rot)) = -LinearMap.id := by
    refine (coordWindingBasis (n := 2) le_rfl).ext fun i => ?_
    simp only [coordWindingBasis, Module.Basis.mk_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.neg_apply, LinearMap.id_apply]
    fin_cases i
    · simp [rot_pullback_coordWinding_zero, rot_pullback_coordWinding_one]
    · simp [rot_pullback_coordWinding_zero, rot_pullback_coordWinding_one]
  exact LinearMap.congr_fun key a

/-- **`rot^*` fixes `a₀ ⌣ a₁`**: `rot^* (a₀ ⌣ a₁) = (−a₁) ⌣ a₀ = a₀ ⌣ a₁`, the sign
`(−1)^{1·1}` of `cupSing_gradedComm` cancelling the `−1` of `rot^* a₀`. -/
theorem rot_pullback_coordCup :
    cohomologyMap ℚ 2 rot (cupSing (torus 2) (coordWinding 0) (coordWinding 1) 2 rfl) =
      cupSing (torus 2) (coordWinding 0) (coordWinding 1) 2 rfl := by
  rw [cupSing_cohomologyMap, rot_pullback_coordWinding_zero, rot_pullback_coordWinding_one,
    ← cupSingBilin_apply, map_neg, LinearMap.neg_apply, cupSingBilin_apply,
    cupSing_gradedComm (torus 2) (coordWinding 0) (coordWinding 1) 2 rfl]
  simp

/-! ### `H¹(T¹; ℚ)` -/

/-- The projection `T² → T¹` to coordinate `0`. -/
def projFirst : torus 2 ⟶ torus 1 :=
  TopCat.ofHom ⟨fun x _ => (x : UnitAddTorus (Fin 2)) 0, continuous_pi fun _ => continuous_apply 0⟩

/-- The projection pulls `a₀` on `T¹` back to `a₀` on `T²`. -/
theorem projFirst_pullback_coordWinding :
    cohomologyMap ℚ 1 projFirst (coordWinding (n := 1) 0) = coordWinding (n := 2) 0 := by
  rw [coordWinding, windingClass_comp, coordWinding]
  exact windingClass_ext _ _ fun _ => rfl

/-- **`a₀ ≠ 0` in `H¹(T¹; ℚ)`** (the circle, `n = 1`). -/
theorem coordWinding_torus_one_ne_zero : coordWinding (n := 1) 0 ≠ 0 := by
  intro h
  have := projFirst_pullback_coordWinding
  rw [h, map_zero] at this
  exact (linearIndependent_coordWinding (n := 2) le_rfl).ne_zero 0 this.symm

/-- **The winding classes `aᵢ` are linearly independent in `H¹(Tⁿ; ℚ)` for every `n`.** -/
theorem linearIndependent_coordWinding_all (n : ℕ) :
    LinearIndependent ℚ (coordWinding (n := n)) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · exact linearIndependent_empty_type
    · exact linearIndependent_unique_iff.mpr coordWinding_torus_one_ne_zero
  · exact linearIndependent_coordWinding h

/-- **The winding classes `aᵢ` span `H¹(Tⁿ; ℚ)` for every `n`.** -/
theorem span_coordWinding_all (n : ℕ) :
    Submodule.span ℚ (Set.range (coordWinding (n := n))) = ⊤ := by
  have hli := linearIndependent_coordWinding_all n
  refine hli.span_eq_top_of_card_eq_finrank' (le_antisymm ?_ ?_)
  · simpa using hli.fintype_card_le_finrank
  · simpa using finrank_cohomology_torus_le n 1

/-- **`dim H¹(Tⁿ; ℚ) = n` for every `n`.** -/
theorem finrank_cohomology_one_torus_all (n : ℕ) :
    Module.finrank ℚ (Cohomology ℚ (torus n) 1) = n := by
  have hli := linearIndependent_coordWinding_all n
  refine le_antisymm (by simpa using finrank_cohomology_torus_le n 1) ?_
  simpa using hli.fintype_card_le_finrank

/-! ### Transport along `Y ≃ₜ Tⁿ` -/

variable {Y : TopCat.{0}} {n : ℕ}

/-- The winding class in `H¹(Y; ℚ)` of the `i`-th coordinate character read through
`h : Y ≃ₜ Tⁿ`, `y ↦ exp (2πi h(y)ᵢ)`. -/
def homeoWinding (h : Y ≃ₜ torus n) (i : Fin n) : Cohomology ℚ Y 1 :=
  windingClass ((coordChar i).comp (h : C(Y, torus n))) fun _ => coordChar_ne_zero i _

/-- `h^* aᵢ` is the winding class of `coordChar i ∘ h`. -/
theorem cohomologyEquivOfHomeomorph_coordWinding (h : Y ≃ₜ torus n) (i : Fin n) :
    cohomologyEquivOfHomeomorph h 1 (coordWinding i) = homeoWinding h i := by
  rw [cohomologyEquivOfHomeomorph_apply, coordWinding, windingClass_comp]
  rfl

/-- **The winding classes of `coordChar i ∘ h` are linearly independent** in `H¹(Y; ℚ)`. -/
theorem linearIndependent_windingClass_of_homeomorph (h : Y ≃ₜ torus n) :
    LinearIndependent ℚ (homeoWinding h) := by
  have := (linearIndependent_coordWinding_all n).map' _
    (cohomologyEquivOfHomeomorph h 1).ker
  convert this using 1
  ext i
  exact (cohomologyEquivOfHomeomorph_coordWinding h i).symm

/-- **The winding classes of `coordChar i ∘ h` span `H¹(Y; ℚ)`.** -/
theorem span_windingClass_of_homeomorph (h : Y ≃ₜ torus n) :
    Submodule.span ℚ (Set.range (homeoWinding h)) = ⊤ := by
  have := congrArg (Submodule.map (cohomologyEquivOfHomeomorph h 1).toLinearMap)
    (span_coordWinding_all n)
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at this
  convert this using 3
  ext i
  exact (cohomologyEquivOfHomeomorph_coordWinding h i).symm

/-- The cup `xᵢ ⌣ xⱼ ∈ H²(Y; ℚ)` of two transported winding classes, for `i < j`. -/
def homeoCup (h : Y ≃ₜ torus n) (p : {p : Fin n × Fin n // p.1 < p.2}) : Cohomology ℚ Y 2 :=
  cupSing Y (homeoWinding h p.1.1) (homeoWinding h p.1.2) 2 rfl

/-- `h^* (aᵢ ⌣ aⱼ) = h^* aᵢ ⌣ h^* aⱼ`, by naturality of the cup. -/
theorem cohomologyEquivOfHomeomorph_coordCup (h : Y ≃ₜ torus n)
    (p : {p : Fin n × Fin n // p.1 < p.2}) :
    cohomologyEquivOfHomeomorph h 2 (coordCup p) = homeoCup h p := by
  rw [cohomologyEquivOfHomeomorph_apply, coordCup, cupSing_cohomologyMap, homeoCup,
    ← cohomologyEquivOfHomeomorph_apply, ← cohomologyEquivOfHomeomorph_apply,
    cohomologyEquivOfHomeomorph_coordWinding, cohomologyEquivOfHomeomorph_coordWinding]

/-- **The cups `xᵢ ⌣ xⱼ`, `i < j`, are linearly independent** in `H²(Y; ℚ)`. -/
theorem linearIndependent_cupWinding_of_homeomorph (h : Y ≃ₜ torus n) :
    LinearIndependent ℚ (homeoCup h) := by
  have := (linearIndependent_coordCup n).map' _ (cohomologyEquivOfHomeomorph h 2).ker
  convert this using 1
  ext p
  exact (cohomologyEquivOfHomeomorph_coordCup h p).symm

/-- **The cups `xᵢ ⌣ xⱼ`, `i < j`, span `H²(Y; ℚ)`.** -/
theorem span_cupWinding_of_homeomorph (h : Y ≃ₜ torus n) :
    Submodule.span ℚ (Set.range (homeoCup h)) = ⊤ := by
  have := congrArg (Submodule.map (cohomologyEquivOfHomeomorph h 2).toLinearMap)
    (span_coordCup n)
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at this
  convert this using 3
  ext p
  exact (cohomologyEquivOfHomeomorph_coordCup h p).symm

/-- **The basis `x₀, …, x_{n−1}` of `H¹(Y; ℚ)`** for `h : Y ≃ₜ Tⁿ`. -/
def homeoWindingBasis (h : Y ≃ₜ torus n) : Module.Basis (Fin n) ℚ (Cohomology ℚ Y 1) :=
  Module.Basis.mk (linearIndependent_windingClass_of_homeomorph h)
    (span_windingClass_of_homeomorph h).ge

/-- **The basis `xᵢ ⌣ xⱼ`, `i < j`, of `H²(Y; ℚ)`** for `h : Y ≃ₜ Tⁿ`. -/
def homeoCupBasis (h : Y ≃ₜ torus n) :
    Module.Basis {p : Fin n × Fin n // p.1 < p.2} ℚ (Cohomology ℚ Y 2) :=
  Module.Basis.mk (linearIndependent_cupWinding_of_homeomorph h)
    (span_cupWinding_of_homeomorph h).ge

/-- **`dim H¹(Y; ℚ) = n`** for `Y ≃ₜ Tⁿ`. -/
theorem finrank_cohomology_one_of_homeomorph (h : Y ≃ₜ torus n) :
    Module.finrank ℚ (Cohomology ℚ Y 1) = n := by
  rw [← (cohomologyEquivOfHomeomorph h 1).finrank_eq, finrank_cohomology_one_torus_all]

/-- **`dim H²(Y; ℚ) = n.choose 2`** for `Y ≃ₜ Tⁿ`. -/
theorem finrank_cohomology_two_of_homeomorph (h : Y ≃ₜ torus n) :
    Module.finrank ℚ (Cohomology ℚ Y 2) = n.choose 2 := by
  rw [← (cohomologyEquivOfHomeomorph h 2).finrank_eq, finrank_cohomology_two_torus]


/-- **The conjugation bridge**: if `h ∘ e = rot ∘ h`, then `e^* x₀ = −x₁` and `e^* x₁ = x₀`
for `xᵢ = h^* aᵢ = homeoWinding h i`. -/
theorem homeoWinding_pullback_of_comm_rot (h : Y ≃ₜ torus 2) (e : Y ⟶ Y)
    (he : ∀ y, h (e y) = rot (h y)) :
    cohomologyMap ℚ 1 e (homeoWinding h 0) = -homeoWinding h 1 ∧
      cohomologyMap ℚ 1 e (homeoWinding h 1) = homeoWinding h 0 := by
  have hc : e ≫ TopCat.ofHom (h : C(Y, torus 2)) = TopCat.ofHom (h : C(Y, torus 2)) ≫ rot := by
    apply ConcreteCategory.hom_ext; intro y; exact he y
  have key : ∀ a, cohomologyMap ℚ 1 e (cohomologyEquivOfHomeomorph h 1 a) =
      cohomologyEquivOfHomeomorph h 1 (cohomologyMap ℚ 1 rot a) := by
    intro a
    rw [cohomologyEquivOfHomeomorph_apply, cohomologyEquivOfHomeomorph_apply,
      ← LinearMap.comp_apply, ← cohomologyMap_comp, hc, cohomologyMap_comp, LinearMap.comp_apply]
  refine ⟨?_, ?_⟩
  · rw [← cohomologyEquivOfHomeomorph_coordWinding, key, rot_pullback_coordWinding_zero, map_neg,
      cohomologyEquivOfHomeomorph_coordWinding]
  · rw [← cohomologyEquivOfHomeomorph_coordWinding, key, rot_pullback_coordWinding_one,
      cohomologyEquivOfHomeomorph_coordWinding]

/-! ### Product tori -/

/-- **The product chart** `Y₁ × Y₂ ≃ₜ T^{m+n}`, `(y₁, y₂) ↦ Fin.append (h₁ y₁) (h₂ y₂)`: the
first `m` coordinates come from the first factor. -/
def prodTorusHomeo {Y₁ Y₂ : TopCat.{0}} {m n : ℕ} (h₁ : Y₁ ≃ₜ torus m) (h₂ : Y₂ ≃ₜ torus n) :
    TopCat.of (Y₁ × Y₂) ≃ₜ torus (m + n) :=
  (h₁.prodCongr h₂).trans (Fin.appendHomeomorph m n)

/-- The coordinate `Fin.castAdd n i` of the product chart is `pr₁^* (homeoWinding h₁ i)`. -/
theorem homeoWinding_prodTorusHomeo_castAdd {Y₁ Y₂ : TopCat.{0}} {m n : ℕ}
    (h₁ : Y₁ ≃ₜ torus m) (h₂ : Y₂ ≃ₜ torus n) (i : Fin m) :
    homeoWinding (prodTorusHomeo h₁ h₂) (Fin.castAdd n i) =
      cohomologyMap ℚ 1 (TopCat.ofHom (ContinuousMap.fst : C(Y₁ × Y₂, Y₁)))
        (homeoWinding h₁ i) := by
  rw [homeoWinding, homeoWinding, windingClass_comp]
  refine windingClass_ext _ _ fun y => ?_
  simp [prodTorusHomeo, coordChar, Fin.appendHomeomorph, Fin.appendEquiv]

/-- The coordinate `Fin.natAdd m j` of the product chart is `pr₂^* (homeoWinding h₂ j)`. -/
theorem homeoWinding_prodTorusHomeo_natAdd {Y₁ Y₂ : TopCat.{0}} {m n : ℕ}
    (h₁ : Y₁ ≃ₜ torus m) (h₂ : Y₂ ≃ₜ torus n) (j : Fin n) :
    homeoWinding (prodTorusHomeo h₁ h₂) (Fin.natAdd m j) =
      cohomologyMap ℚ 1 (TopCat.ofHom (ContinuousMap.snd : C(Y₁ × Y₂, Y₂)))
        (homeoWinding h₂ j) := by
  rw [homeoWinding, homeoWinding, windingClass_comp]
  refine windingClass_ext _ _ fun y => ?_
  simp [prodTorusHomeo, coordChar, Fin.appendHomeomorph, Fin.appendEquiv]

end HodgeLadder.Torus
