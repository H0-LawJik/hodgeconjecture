# Research note: spinors, character sieves, and torus test cases

**Date:** 2026-11-24. **Source:** the maintainer's research notes on hypercube topology, Hodge diamonds, exceptional lattices and the zeta function, reviewed against the literature. This note keeps the parts usable on this ladder, in corrected form, and records why the rest is set aside. Citation keys are in `docs/references.md`.

## 1. Spinors on the cohomology of a torus (for the Markman inventory)

**Corrected statement.** Let A be a complex torus of dimension g and H = H¹(A, ℚ), of dimension 2g, so that H*(A, ℚ) = ∧*H. Put V = H ⊕ H^∨ with the split quadratic form q(x, ξ) = ξ(x). The Clifford algebra Cl(V, q) acts on ∧*H, with x ∈ H acting by wedge product and ξ ∈ H^∨ by contraction; this makes ∧*H the spin module S of Spin(V), of dimension 2^{2g}, with S⁺ and S⁻ the even and odd degrees [Chevalley1954]. So Spin(V) acts on the whole cohomology of A [Mukai1981] [GolyshevLuntsOrlov2001].

**Correction to the source notes.** The notes identified the cohomology of a torus of real dimension 2g with the spin module of Spin(2g) for a Euclidean form. The dimensions disagree (2^{2g} against 2^g; 256 against 16 for real dimension 8). The working version doubles the space to H ⊕ H^∨ and uses the split form that pairs cohomology with its dual.

**Why it matters here.** Markman's construction of cycles representing Weil classes uses Orlov's derived equivalence D^b(A × A) ≅ D^b(A × Â) [Orlov2002], which categorifies an isomorphism of Spin(V)-representations, the tensor square of the spin representation, via Chevalley's isomorphism S ⊗ S ≅ ∧*V [Markman2025]. Van Geemen's account of Weil-type fourfolds goes through the spinor map [vanGeemen2022]. The spin action is part of the machinery behind the frontier result this project targets after the Lefschetz checkpoint.

**What Mathlib has at the pin.** Clifford algebras (`Mathlib/LinearAlgebra/CliffordAlgebra/`), including the contraction action on the exterior algebra (`Contraction.lean`), the even subalgebra and its grading, and the spin group (`SpinGroup.lean`); exterior algebras with their grading. Künneth formulas for sheaf cohomology are not in Mathlib.

**Rung.** `clifford-exterior-spin`: for a finite-dimensional ℚ-vector space H, the split form on H ⊕ H^∨ and the action of its Clifford algebra on ∧*H (wedge plus contraction, squaring to the form), compatible with the parity grading. Pure linear algebra and a Mathlib upstream candidate; the librarian checks first whether Mathlib already has it under another name. Sequenced after the Lefschetz checkpoint (decision 0003).

## 2. Character sieves (for a future Fermat front)

**Corrected statement.** The notes' sieve keeps the forms on a torus whose phase weights sum to 0 mod N, as the cohomology of the quotient by a cyclic group. Rationally, the cohomology of X/G is the G-invariant part of the cohomology of X. That is the untwisted part only: a resolution of X/G, or orbifold cohomology, adds twisted sectors from the fixed loci, which the sieve does not see.

**Where it applies exactly.** On a Fermat hypersurface X = X^n_m, the group μ_m^{n+2} acts, and the primitive middle cohomology splits into one-dimensional character spaces V(a) indexed by tuples a = (a₀, …, a_{n+1}) with 1 ≤ aᵢ ≤ m − 1 and Σaᵢ ≡ 0 mod m. The Hodge type of V(a) is read off from ⟨a⟩ = Σaᵢ/m, and for n = 2p the character a gives Hodge classes exactly when ⟨ta⟩ = p + 1 for every unit t mod m. The Hodge conjecture for X^n_m then reduces to showing that algebraic cycles span the Hodge characters [Shioda1979]; the 2026 work on lengths of Hodge characters refines this reduction [MMRV2026]. This is the sieve of the notes, applied to the cohomology of X itself, with no quotient and so no twisted sectors. The thinker checks these statements against [Shioda1979] before any rung is posted.

**Status.** Candidate front `fermat`. Per `docs/strategy.md`, opening it needs a decision record and a first rung. Fermat varieties are attractive for Lean because the character computations are finite and explicit.

## 3. Torus test cases (non-vacuity, after the checkpoint)

**Hodge numbers.** For a complex torus of dimension g, h^{p,q} = C(g, p)·C(g, q). For a product E₁ × … × E_g of elliptic curves, counting how many factors contribute dz ∧ dz̄, dz only, or dz̄ only refines this to
h^{p,q} = Σ_k C(g, k)·C(g − k, p − k)·C(g − p, q − k),
which sums to C(g, p)·C(g, q); checked numerically for every g ≤ 8.

**What the diamond cannot see.** Every abelian variety of dimension g has the same Hodge diamond, while the Hodge classes depend on the periods. The smallest example: for a product of two elliptic curves, h^{1,1} = 4 always, but by Lefschetz (1,1) the rational Hodge classes in degree two have dimension equal to the Picard number, 2 + rank Hom(E₁, E₂): that is 2 for non-isogenous curves, 3 for isogenous curves without complex multiplication, 4 for isogenous curves with complex multiplication. For products of elliptic curves the Hodge conjecture is a theorem (Murasaki; Imai; see [Gordon1999]), so these varieties are a known case, not a frontier.

**Rung.** `elliptic-product-test`: on upstream definitions, compute the dimension of Hdg^1 of a product of two elliptic curves as 2 + rank Hom(E₁, E₂), and check the Hodge numbers of products of elliptic curves against the formula above. Needs the cohomology of tori on upstream definitions; sequenced after the Lefschetz checkpoint.

## 4. Process: certifying a large agent-assisted Lean proof

On 2026-11-20 Levent Alpöge announced a Lean proof, found with Claude, of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet L-functions [AlpogeRH2026]. Reports describe a joint statement by the Lean FRO and the Mathlib Initiative certifying the statement and proof of the classical hypothesis, independent full statement-comparison runs, and human review still in progress. This project is attempting smaller versions of the same thing: agent-built Lean proofs whose statements must match a statement of record. How that certification was done (which tool compares a proof's theorem against a reference statement, and what it checks) is worth adopting for `lefschetz-1-1` and the port. Recorded in `docs/gaps.md` as an open item; the tooling details are unverified here.

## 5. Set aside, with reasons

| Part of the source notes | Why it is not used |
|---|---|
| Prime factors of central Hodge numbers ("anchors", "vacuums", "resonances") | Fully explained by Kummer's theorem: p divides C(2m, m) exactly when adding m + m in base p carries. No Hodge-theoretic content. In dimension 24, 23 divides no C(12, k). |
| Hypercube volume concentration | No connection to Hodge classes. |
| Definite even unimodular lattices, lattice vertex algebras, extremal norms | Lattice and modular-form theory. The lattice that enters Hodge theory is the indefinite K3 lattice U³ ⊕ E₈(−1)², through Kuga–Satake: a possible later front, not this material. |
| Theta functions, the zeta function, the critical line | A different problem. The functional equation's symmetry about Re(s) = 1/2 does not place zeros on the line: Davenport–Heilbronn functions satisfy a functional equation of the same shape and have zeros off it. |

Corrections to the source notes found during review, for the record: the Construction A weight condition is "doubly even" (weights ≡ 0 mod 4 with the standard scaling), not ≡ 0 mod 8; inscribed-ball volume fractions are 1.15 × 10⁻⁸ % in dimension 24 and 1.0 × 10⁻¹³ % in dimension 32; among the Niemeier lattices only the Leech lattice has minimum norm 4; four extremal even unimodular lattices are known in dimension 48; Q₃₂, with 261,120 minimal vectors, is not an extremal even unimodular lattice (those share one theta series, with 146,880); the bound on cusp-form coefficients is Deligne's theorem and needs no GRH.
