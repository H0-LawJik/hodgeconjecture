# Sketch: `cup-odd-degree-test`

Rung: a nonzero product of two classes in H¹(X; ℚ), on a curve of positive genus or an abelian surface. Purpose (red team on `cup-singular-comparison-absolute`, section 7b): the only planned test in which the sign (−1)^{pq} of `Ψ (x ∪ y) = (−1)^{pq} · cupSing (Ψ x) (Ψ y)` takes the value −1 on a computed instance, and a witness that the Yoneda product is not square-zero in positive degree.

Inventory taken 2026-11-26 at the upstream pin `2ead713` (Lean and Mathlib `v4.35.0-rc4`, Tau Ceti vendored at `7433fc3`). Verdict: the rung stays open. A weaker companion, `cup-odd-degree-gm2`, carries the same content on the algebraic torus 𝔾ₘ² and is checked in this session, with four supporting rungs. The original rung needs an elliptic curve with its complex uniformization; the missing pieces are listed below as proposed sub-rungs.

## 1. What the test has to show

The comparison theorem holds for every X with `IsIntegral X.left`, `Smooth X.hom`, `T2Space (ComplexPoint X)` and paracompact opens. Projectivity is not among them. So any such X with two classes a₁, a₂ ∈ H¹(X(ℂ); ℚ) and a 2-cycle c with ⟨a₁ ⌣ a₂, c⟩ ≠ 0 gives the test: pull a₁, a₂ back along Ψ to x₁, x₂ ∈ H¹(X; ℚ), then

⟨Ψ(x₁ ∪ x₂), c⟩ = (−1)^{1·1} ⟨a₁ ⌣ a₂, c⟩ = −⟨a₁ ⌣ a₂, c⟩ ≠ 0.

Three pieces are needed: a pairing of H²(Y; ℚ) with a 2-cycle that computes cup products, explicit degree-one classes with computable values, and an X at the pin whose complex points carry both.

## 2. The singular side, for any space

**Torus cycle** (rung `torus-cycle-pairing`). Two singular 2-simplices σ₁, σ₂ with δ₀σ₁ = δ₂σ₂, δ₁σ₁ = δ₁σ₂, δ₂σ₁ = δ₀σ₂ form a cycle σ₁ − σ₂, and evaluation on it kills coboundaries (three faces cancel in pairs). With Tau Ceti's face formula (φ ⌣ ψ)(σ) = φ(δ₂σ) ψ(δ₀σ) (`cochainValuesEquiv_cupCochain_one_one`, [Hatcher2002] §3.2),

⟨a ⌣ b, σ₁ − σ₂⟩ = a(e) b(f) − a(f) b(e), e = δ₂σ₁, f = δ₀σ₁,

a determinant, antisymmetric in (a, b). A map T : ℝ × ℝ → Y of period 1 in each variable gives such a pair: σ₁ = T ∘ [(0,0),(1,0),(1,1)], σ₂ = T ∘ [(0,0),(0,1),(1,1)] (the square model of the torus; its cup ring is computed in [Hatcher2002] §3.2, exact locator unverified).

**Winding classes** (rung `winding-torus-cup`). The port already has the winding cocycle σ ↦ (1/2πi)·(logarithmic increment of g along σ) of a nowhere vanishing continuous g, and a ℚ-valued version through a ℚ-linear retraction ℂ → ℚ (`ChernWinding.rationalWindingCochain`). If g₁(T(s,t)) = exp(2πi s) and g₂(T(s,t)) = exp(2πi t), the increments along e and f are computed exactly by `logIncrement_of_exp`: g₁ winds once along e and zero times along f, g₂ the reverse. So ⟨a₁ ⌣ a₂, T⟩ = 1 and ⟨a₂ ⌣ a₁, T⟩ = −1.

**Concrete instance** (rung `singular-odd-cup-test`): Y = ℂˣ × ℂˣ, g₁, g₂ the coordinates, T(s,t) = (exp 2πi s, exp 2πi t). This makes `cupSing_gradedComm` non-vacuous in degrees (1, 1).

## 3. Transfer to sheaf cohomology

Rung `cup-odd-degree-transfer`: for X with the four instances and the data (g₁, g₂, T) on X(ℂ), the classes xᵢ = Ψ⁻¹(aᵢ) satisfy ⟨Ψ(x₁ ∪ x₂), T⟩ = −1 and ⟨Ψ(x₂ ∪ x₁), T⟩ = 1, hence x₁ ∪ x₂ ≠ 0 and x₁ ∪ x₂ ≠ x₂ ∪ x₁. The proof is `cup_singular_comparison_swap` and section 2. The hypotheses are statements on upstream and Mathlib definitions (continuous functions and maps into upstream's `ComplexPoint X`); there is no interface structure.

What the value −1 pins: upstream's Ψ as defined. A degree twist Ψ' = ε(n)·Ψ with ε(n) = (−1)^{n(n−1)/2} (conventions row "Sheaf–singular comparison Ψ") fixes H¹ and negates H², so it would give +1. A square-zero product would give 0.

## 4. Candidate spaces

| Space | H¹ classes and torus at the pin | Instances at the pin | Status |
|---|---|---|---|
| 𝔾ₘ² = Spec ℂ[x, y][(xy)⁻¹] | coordinates x, y; T(s,t) = (exp 2πi s, exp 2πi t) through 𝔾ₘ²(ℂ) ≅ ℂˣ × ℂˣ | integral, smooth (localization of a polynomial ring), Hausdorff (upstream `t2Space_of_isAffine`), opens metrizable | checked: `gm2-witness`, `gm2-points`, `cup-odd-degree-gm2` |
| elliptic curve E ⊂ ℙ² | needs E(ℂ) ≅ ℂ/Λ ([Silverman2009] ch. VI, [Mumford1970] §1; locators unverified) | nothing: Mathlib's Weierstrass curves have points over rings but no scheme over Spec ℂ; upstream has ℙⁿ and closed immersions | open, see section 5 |
| abelian surface E × E | as for E, plus complex points of a fibre product | as for E, plus products in `Over (Spec ℂ)` | open, after E |
| curve of genus ≥ 2 | no explicit model of X(ℂ) at the pin | nothing | not proposed |
| smooth projective rational surfaces, ℙⁿ | H¹ = 0 ([Hatcher2002] for ℙⁿ(ℂ)) | ℙ¹ checked | cannot test degree 1 |

𝔾ₘ² is the smallest affine variety with two independent H¹ classes and a nonzero product: 𝔾ₘ has H² = 0 (a noncompact curve). It is affine, so it does not meet the upstream statements of record (which ask for `IsProjective`); it meets every hypothesis of the cup comparison.

## 5. Proposed sub-rungs for the original statement (elliptic curve route)

| Id | Statement | Route | Depends on |
|---|---|---|---|
| `elliptic-curve-witness` | E = V(y²z − x³ + xz²) ⊂ ℙ² (or any Weierstrass cubic with Δ ≠ 0) as `Over (Spec ↧ℂ)` with `IsIntegral`, `Smooth`, `IsProjective` | closed subscheme of upstream's ℙ²; smoothness by the Jacobian criterion on the three standard charts, each a localization of ℂ[u, v]/(f) with a unit partial derivative (Mathlib `Algebra.IsStandardSmooth` presentations); integrality from one irreducible chart meeting the others | `projective-line-witness` (pattern) |
| `elliptic-curve-points` | E(ℂ) (upstream `ComplexPoint`) is homeomorphic to {[x : y : z] ∈ ℙ²(ℂ) : y²z = x³ − xz²} with the quotient topology from ℂ³ ∖ 0 | upstream `ClosedImmersion` for complex points, `ProjectiveCoordinates`, the affine-chart homeomorphisms used for 𝔾ₘ² | `elliptic-curve-witness` |
| `elliptic-curve-uniformization` | for a lattice Λ with g₂(Λ), g₃(Λ) matching the chosen cubic, z ↦ [℘(z) : ℘'(z) : 1] is a homeomorphism ℂ/Λ → E(ℂ) | Mathlib has ℘, its periodicity, its pole orders and ℘'² = 4℘³ − g₂℘ − g₃; missing: Δ(Λ) ≠ 0 for the chosen Λ, that ℘ takes each value twice on a period parallelogram (argument principle), and matching the coefficients of the chosen cubic (choose Λ = ℤ[i], where g₃ = 0 by ℘(iz) = −℘(z), and the cubic y² = 4x³ − g₂x, after proving g₂(ℤ[i]) ≠ 0, known by [Silverman2009] ch. VI, unverified here). Compact to Hausdorff gives continuity of the inverse | `elliptic-curve-points` |
| `elliptic-curve-torus-data` | continuous nowhere vanishing g₁, g₂ on E(ℂ) and T : ℝ × ℝ → E(ℂ) of period 1 with gᵢ ∘ T the two angle characters | g₁, g₂ = exp(2πi·(coordinate of the inverse uniformization in the basis ω₁, ω₂)); T(s, t) = uniformization of sω₁ + tω₂ | `elliptic-curve-uniformization` |
| `cup-odd-degree-test` | this rung | `cup-odd-degree-transfer` with the data above | `elliptic-curve-torus-data`, `cup-odd-degree-transfer` |

The abelian-surface case adds products: `Over (Spec ℂ)` fibre products and the homeomorphism (E × E)(ℂ) ≅ E(ℂ) × E(ℂ). It is longer and gives nothing the curve case lacks.

Estimate: `elliptic-curve-witness` two sessions, `elliptic-curve-points` one to two, `elliptic-curve-uniformization` several (the counting of ℘-values is the largest missing piece, and none of it is at the pin), `elliptic-curve-torus-data` one.

## 6. Kill criterion

The rung's purpose (a sign-visible, non-square-zero product of two H¹ classes for the cup product of record) is met by `cup-odd-degree-gm2`. Mark `cup-odd-degree-test` dead, with this sketch kept, if `elliptic-curve-uniformization` is released twice without a stated sub-rung for the two-to-one counting of ℘ on a period parallelogram. Reopen it as a new rung if Mathlib or upstream gains the analytic uniformization of elliptic curves over ℂ.

## 7. Red-team notes for the checked companions

- The nonvanishing results (`gm2_cup_ne_zero`, `gm2_exists_cup_ne_zero`, `gm2_cup_swap_ne`) are statements about upstream's H¹(X; ℚ) and the Yoneda `cup`; the local definitions `windingClass`, `sheafWindingClass` and `torusEval` only produce the witnesses.
- The values ±1 depend on two conventions: the orientation of the torus cycle (lower triangle minus upper triangle) and the exchange of the two circle coordinates; reversing either flips both values. Reversing the winding normalization (1/2πi)·d log g negates both classes and leaves every product value unchanged; rescaling it by c multiplies the values by c². nonvanishing and x₁ ∪ x₂ ≠ x₂ ∪ x₁ do not depend on them. Recorded as the conventions row "Torus cycle and winding classes".
- The rational retraction ℂ → ℚ behind `rationalWindingCochain` is not continuous; it only matters on the values of the two edges e, f, which are the rationals 0 and 1.
- 𝔾ₘ² instances: T2 from upstream; paracompactness of opens from the homeomorphism with a subspace of ℂ × ℂ (`gm2-points`), a Mathlib fact about metric spaces. The upstream structure map is `ComplexPoint.affineSpecStructureMap`, so `affineSpecHomeomorph` applies without transport.

### Kill criterion, revised (red team 2026-11-26)

Mark `cup-odd-degree-test` dead, keeping this sketch, when `elliptic-curve-uniformization` reaches needs-split (three releases) and the counting sub-rung that comes out of the split is itself released.
