# Markman inventory (milestone M2)

Date: 2026-11-25. Pin: upstream `2ead713`, Mathlib `v4.35.0-rc4`. Sources: [Markman2025] §§1, 7, 9.3; [Markman2023] §§1.3–1.4, 13; [Markman2026ICM]; [vanGeemen2022] §4; [MoonenZarhin1999] introduction; [FloccariFu2025] §§1–3. Schoen's addendum, [MoonenZarhin1995] and Ramón-Marí 2008 were not read directly; claims from them are marked "cited". A survey of formal libraries (Mathlib at the pin and master, upstream, this repository's port, other Lean projects, other provers) supplies the "exists" column. Claims about libraries outside Mathlib and this repository are unverified until `#print axioms` runs locally.

## 1. Shape of the proof

| Step | Content | Source |
|---|---|---|
| R1 | Simple abelian fourfold: H^{2,2}(A, ℚ) is spanned by quadratic polynomials in divisor classes and by Weil classes | [Markman2025] §1.6, citing [MoonenZarhin1995] Thm 2.11 (cited) |
| R2 | Non-simple fourfolds reduce to surfaces or to B × E up to isogeny | [Markman2025] Cor 1.6.1 (cited sources) |
| R3 | Weil classes on abelian sixfolds of Weil type with discriminant −1 are algebraic, for every K = ℚ(√−d) | [Markman2025] Thm 1.5.1, §9.3 |
| R4 | Fourfolds of every discriminant, from R3, by specializing sixfolds to products A₄ × A₂ | [Markman2025] §1.6, citing Schoen (cited); the extraction step is unverified |
| R5 | Discriminant 1 independently: ℚh² ⊕ W_K is algebraic on every polarized Weil fourfold of discriminant 1 | [Markman2023] Thm 1.5 = Thm 13.4 (refereed) |

Correction to the plan: the all-discriminant proof passes through degree six (the Weil class κ₃ ∈ H^{3,3} on sixfolds X × X̂). Only the refereed discriminant-1 route [Markman2023] stays in degree four.

## 2. Tools by degree

| Tool | Degree | Used in | Status in the literature | Formal status |
|---|---|---|---|---|
| Lefschetz (1,1) | 2 | R1, R2, R4 | classical [GriffithsHarris1978] | **checked here** (`HodgeLadder.lefschetzOneOneEquality_holds`) |
| H*(A; ℚ) = ∧*H¹, H^{p,q} = ∧^pH^{1,0} ⊗ ∧^qH^{0,1} | all | throughout | classical | absent for upstream's cohomology; linear-algebra model in Mathlib (`ExteriorAlgebra.prodEquivTensor`) |
| Cup product, graded commutativity | all | every product of classes | classical | **absent** for `Sheaf.H` (Mathlib has Yoneda composition of `Ext` only) |
| Cycle class is multiplicative | 2·2 → 4, 2·4 → 6 | R1, R2 | classical [Fulton1998] Ch. 19 | absent on the Betti side; partial in unreviewed external Lean projects (Chow-side intersection products) |
| Weil-type data: K-action, balanced eigenspaces on H^{1,0}, W_K = ∧^{2n}_K H¹, Hermitian form, discriminant | 1, 2, 2n | definitions | classical (Weil 1977; [vanGeemen2022] §§4.2–4.4) | absent; linear-algebra core buildable now |
| Mumford–Tate groups of generic Weil type | 2, 2n | R1, R5 | classical (cited) | absent |
| Chern classes of coherent sheaves are algebraic; GAGA | 4, 6 | end of R3, R5 | classical [Fulton1998] | c₁ only (port); higher Chern classes absent on the Betti side |
| Clifford algebra of H¹(X) ⊕ H¹(X̂), spin module, Chevalley S ⊗ S ≅ ∧*V | all | R3 (§§2, 6) | classical [Chevalley1954] | Clifford algebra, contraction, spin group in Mathlib; the action on ∧*H and Chevalley's isomorphism absent, buildable |
| Fourier–Mukai, Orlov's equivalence, Spin-equivariance of its cohomological action | all | R3 (§§5–6) | [Orlov2002] classical; equivariance new | Fourier–Mukai calculus partial in external projects; Poincaré bundle and Orlov absent |
| Secant sheaves on Jacobians, κ(E) = ch(E)·exp(−c₁/r) | 2, 4, 2n | R3 (§8) | new | absent |
| Semiregularity (Buchweitz–Flenner), twisted version | all | R3 (§§7–9) | Buchweitz–Flenner classical; twisted reduction new | absent |
| "Algebraic in the family": countable union of closed algebraic loci | 2n | R3 | classical (Voisin) | absent |
| Hyperkähler route: generalized Kummer monodromy, Verbitsky deformation, Torelli | 2, 4 | R5 | Verbitsky classical, rest new | absent |
| Hard Lefschetz | 2 → 6 | not used by Markman | classical | absent (open rung `hard-lefschetz`) |
| Absolute Hodge classes, Cattani–Deligne–Kaplan | none | not used | | |

## 3. Stating versus proving

| Target | Needs |
|---|---|
| `HodgeConjectureForAbelianVarietiesInDimensionLE 4` (upstream `Variants.lean`) | nothing new to state. Its docstring calls the case n ≤ 5 a theorem; for discriminants other than 1 that rests on a preprint [Markman2025]. Red-team item |
| "Weil classes are algebraic" on upstream definitions | degree 2: pullback of an endomorphism on H¹, the Hodge piece H^{1,0}; degree 4: a cup product H¹^{⊗4} → H⁴ to define W_K; for the discriminant-1 form, a polarization and its alternating form (H² ≅ ∧²H¹ or a trace map) |
| The proof, discriminant 1 [Markman2023] | the degree-4 list above plus multiplicativity of the cycle class map, Chern classes in `algebraicCycleClassSpan`, the hyperkähler machinery |
| The proof, all discriminants [Markman2025] | additionally degree 6, Fourier–Mukai with Grothendieck–Riemann–Roch, semiregularity, the Weil-type moduli argument, Schoen's specialization |

The discriminant convention (split means discriminant 1 for fourfolds and −1 for sixfolds under van Geemen's normalization of H) goes into `docs/conventions.md` before any Weil-class statement is posted.

## 4. Blocking gaps, in order

1. A ring structure on upstream's H*(X; ℚ): cup product on `Sheaf.H` of the constant sheaf, graded commutativity, naturality, multiplicative cycle class map.
2. An analytic model of abelian varieties: A(ℂ) ≅ ℂ^g/Λ, complex points of products, Künneth for constant-sheaf cohomology, H*(A; ℚ) ≅ ∧*H¹.
3. Hodge theory of tori: H^{p,q} of a torus, polarizations, Weil-type data.
4. The Poincaré-bundle side: Pic⁰, dual abelian variety, Mukai and Orlov equivalences, Chern characters landing in Betti cohomology.
5. Families: Weil-type families, Hodge loci, deformation of sheaves.

## 5. Consequences for the ladder

- Gap 1 is also the main missing input for M3 (`hard-lefschetz`, `dimension-le-three`). A cup-product rung serves both milestones.
- `elliptic-product-test` needs gaps 1 and 2 (H²(E₁ × E₂) through Künneth). It is a strong degree-two test once they exist; it cannot be the first rung.
- Rungs that can start at the pin, all pure linear algebra: the Clifford action of the split form on ∧*H (`clifford-exterior-spin`, a Mathlib candidate); exterior powers of a weight-one Hodge structure; the linear-algebra core of Weil classes (∧^n_K of a K-vector space with balanced Hodge eigenspaces is a 2-dimensional space of Hodge classes, an equality of subspaces). The last is easier after a pin bump that brings in Mathlib's exterior-power base change.
