# Red team: decision 0008, front `cup`

Date: 2026-11-25. Main at `127ffa1`. Pin: upstream `2ead713`, Lean and Mathlib v4.35.0-rc4 (Mathlib `1f41440`). Tau Ceti clone `7433fc3` (Lean v4.37.0-rc1, Mathlib `31ce06e`), read only; nothing there was built. `python3 tools/check.py --no-build`: all checks passed; every `HodgeLadder.Cup.*` declaration in the ledger reports `[Classical.choice, Quot.sound, propext]`. Scratch files were compiled with `lake env lean` and are described by what they test.

**Verdict: amend.** The Yoneda definition stands. The decision's rung list leaves out the rung its own kill criterion needs: a multiplicative comparison between sheaf and singular cohomology. The amended order is below.

## 1. What the new evidence shows

| Item | Finding | Evidence |
|---|---|---|
| (a) `rationalCohomologyLinearEquivSingularCohomology` | additive equivalence promoted to ℚ-linear by `map_rat_smul`; needs `IsIntegral`, `Smooth`, `T2Space`, paracompact opens | `Other/AlgebraicGeometry/Cohomology/SingularComparison.lean:48-57` |
| how it is built | Ext(ℤ, ℚ) is mapped to hypercohomology of sheafified singular cochains, then to a **chosen** K-injective resolution (`exists_quasiIso_injective`), flasque global sections, raw top-open cochains, singular cohomology | `HodgeConjecture/Lemmas/.../SingularSheafComparison.lean:81`; `GlobalSections.lean:198-235` (choice at `:211`), `:286`, `:310` |
| natural in X? | no statement of naturality anywhere; the only consumer is the guide | grep: used in `HodgeGuide/Overview.lean:177` only |
| multiplicative? | nothing upstream is. Upstream has **cap** products in Hatcher's convention, φ ∩ x = φ(front) · back, absolute, relative and support-valued, with naturality | `Other/AlgebraicTopology/Singular/Cap/Simplicial.lean:34-36,54,62`; `Cap/Support.lean`; `Cap/Naturality.lean:179` |
| (b) Tau Ceti cup | (φ⌣ψ)(σ) = μ(φ(σ\|[0..p]) ⊗ ψ(σ\|[p..n])), no sign; natural in X; graded commutative b⌣a = (−1)^{pq} a⌣b | `Cup/Basic.lean:259,279`; `GradedCommutativity.lean:70,86` |
| relative cups | yes. Absolute × relative (`TopPair.singularCup`, `Cup/Relative.lean:200`, graded commutative `:325`); relative × relative `singularRelativeCup : Hᵖ(X,U) × H^q(X,V) → Hⁿ(X,U∪V)` for U, V open in U∪V (`:352-354`); relative cross product (`:612`). Complements of closed supports satisfy the openness hypothesis |
| torus | T² only (`Torus.lean`); Künneth needs finiteness of homology (`Kunneth.lean:320`) |
| cochain models | absolute: an iso of complexes with components `ModuleCat.homLinearEquiv`, differentials agree by `rfl` (scratch `dualIsoYoneda`, 10 lines, compiles). `𝟙_ (ModuleCat ℚ) = ModuleCat.of ℚ ℚ` and `SingularChainComplex ℚ X = (toSSet.obj X).chainComplex _` hold by `rfl`; the degree-n cochain modules are not defeq (`Module.Dual` vs `ModuleCat` hom). Relative: upstream uses `Limits.coker` (`Singular/Cohomology.lean:92`), Tau Ceti its own relative complex (`Singular/Relative.lean:195`); a cokernel comparison, small |
| backport closure | computed by import walk: `Cup.Basic` 27 modules / 8.9k lines; `GradedCommutativity` 41 / 13.3k (matches the harvest estimate); `Cup.Relative` 130 / 39.9k; `Cup.Pullback` 153 / 44.8k; `Kunneth` 140 / 39.5k; `Torus` 365 / 106k. Two toolchain steps down |
| (c) cycle classes | the class of record is Ext-side: `supportH = relH = Ext(ℤ[X, X∖Z], ℚ_X)` (`Definitions/AlgebraicTopology/Support/Cohomology.lean:53`), forgotten to `H^{2p}` (`FundamentalClass.lean:88`). Its normalization is singular-side: `normalizedRelativeCoclass` is the UCT dual of the oriented generator (`Cycle/Local/Purity.lean:58`), carried over by `complexSupportInjectiveSectionCohomologyEquiv` (`Lemmas/.../Transport/CohomologySheaf.lean:37`, relative singular H^n(V, V∖S)) and `rationalSupportAddEquivSupportedInjectiveHomology` (`SupportedInjectiveModel.lean:57`). Both are checked and additive only. `singularComponentCycleClassLine` (`Other/.../Cycle/SingularClass.lean:69`) is a separate singular span, not the statement of record |

## 2. Rung by rung

| Rung | Yoneda route: missing | Singular route: missing | Less work |
|---|---|---|---|
| `cup-graded-commutative` | Y1 ⊗ on `Sheaf (Opens) (ModuleCat ℚ)` exact in each variable (structure elaborates: scratch `Sheaf.monoidalCategory _ _` compiles; exactness via `Opens.pointGrothendieckTopology`, `Sites/Point/Monoidal.lean`, `Point/Conservative`); Y2 unitor transport for `Ext.mapExactFunctor` (from `id_mapExactFunctor`, `mapExactFunctor_comp_mk₀_natTransApp`, `Ext/Map.lean:239,265`); **Y3 interchange** (α⊗C) ≫ (B⊗β) = (−1)^{pq} (A⊗β) ≫ (α⊗D) on Ext. Y3 is absent at the pin; Mathlib has the complex-level sign only (`BifunctorShift.lean:196`) and no derived bifunctor | backport 41 modules; model iso (done in scratch); **C4** below | Y1+Y3 when C4 is not otherwise needed. C4 is needed (next row), so transfer through C4 costs only the backport |
| `cycle-class-multiplicative` | supported product α ↦ (α ⊗ ℚ_W) ≫ β, Ext(ℚ_Z) × Ext(ℚ_W) → Ext(ℚ_{Z∩W}); compatibility with `forgetSupport` and `cup` uses only degree-0 naturality (no sign); needs Y1, `extEquivQ` for general A (`SheafExact.lean:137`), `Adjunction.extEquiv_naturality_left`. Then the local value: the product of normalized classes must pair to 1 with the oriented generator of ℂ^{p+q}. Normalization lives in singular cohomology, so this needs **C4 on supported groups** | relative cup exists in Tau Ceti (130-module closure); still needs C4 to reach the Ext class of record | neither avoids C4. The local orientation computation (cross product of oriented generators; upstream's reference simplex, standard basis followed by (−1,…,−1), is not a product simplex) is needed on both |
| pullback (T1) | port `TopCat.Sheaf.H.pullback` via `H.mapOfExact` (`port/.../Cohomology/Pullback.lean:44,112`); multiplicativity is `Ext.mapExactFunctor_comp` (`Ext/Map.lean:223`) plus conjugation by Φ(ℚ) ≅ ℚ; missing: the ℚ-sheaf version or compatibility of `extEquivQ` with pullback | `singularCup_naturality` exists, but transporting it needs naturality in X of upstream's comparison, which is unproved and built on a chosen resolution | Yoneda |
| Hodge side | `hodgeClasses` (`Hodge/Filtration.lean:917`) is postcomposition into ℍ(F^pΩ•) in sheaves of abelian groups. "Product of Hodge classes is Hodge" needs F^p · F^q ⊆ F^{p+q}: a tensor product of complexes of sheaves descending to D (over a field, ⊗ preserves quasi-isomorphisms stalkwise; `Algebra/Homology/Monoidal.lean`, `Localization.Monoidal`), the wedge map, conjugation multiplicative | a multiplicative de Rham theorem with smooth forms and integration; upstream has no smooth forms | Yoneda/tensor is the only route at the pin; large on any route |

**C4 (Option C).** Statement: under `rationalCohomologyLinearEquivSingularCohomology`, `cup α β` maps to ε · (singular cup in a stated order) with ε determined exactly; the same for the supported equivalences against `singularRelativeCup`. Feasible. Missing pieces: a presheaf cup on U ↦ C*(U) compatible with restriction and sheafification; the unit ℚ → S⁰ multiplicative; the key lemma that for a flasque sheaf of dg algebras S with quasi-iso ℚ → S, Yoneda composition becomes multiplication on H(ΓS), proved through upstream's six-step chain including the chosen injective resolution and the top-open to global-sections quasi-iso (`GlobalSections.lean:263-282`). Heuristic (not checked): with Mathlib's shift differential (−1)^n d, left multiplication s ↦ b∪s is a chain map S → S[q], which suggests α ≫ β ↦ ±(b ∪ a). Size estimate: 2k to 5k lines, plus the backport if Tau Ceti's cup is reused. Upstream's own front/back faces (`Cap/Simplicial.lean:54,62`) allow a cup on upstream's cochain model without the backport for definition and Leibniz rule; graded commutativity on that model still needs the Alexander–Whitney braiding homotopy.

## 3. Graded commutativity on the Yoneda side

Feasible in principle: the Hilton–Eckmann argument gives α ≫ β = (−1)^{pq} β ≫ α on Ext*(𝟙, 𝟙) in an abelian monoidal category with exact tensor [Suárez-Álvarez, *The Hilton–Heckmann argument for the anti-commutativity of cup products*, Proc. AMS 132 (2004) 2241–2246; unverified, not opened]. Missing at the pin: Y1 and Y3; Y3 is the content. Estimate 1.5k to 4k lines, Mathlib-level. Yoneda product equals cup product up to sign: [Bredon, *Sheaf Theory*, 2nd ed., GTM 170, ch. II], [Iversen, *Cohomology of Sheaves*, ch. II], [Kashiwara–Schapira, *Sheaves on Manifolds*, ch. II]; all unverified, no section numbers or signs confirmed. None of these keys is in `docs/references.md`.

## 4. Conventions

| Convention | Where | Truth depends on it? |
|---|---|---|
| Yoneda factor order: `cup α β = e⁻¹(e α ≫ e β)`, `Ext.comp α β = α ≫ β⟦p⟧` with shift differential (−1)^n d | `Cup/Product.lean`; conventions row "Cup product" | identities between products; **not** graded commutativity (the identity is invariant under swapping factors) and not even-degree identities |
| Singular coboundary δφ = φ ∘ ∂, no sign | upstream `LinearDual.lean:173`; Mathlib `linearYonedaObj` (`Abelian/Ext.lean:56`); Tau Ceti uses the latter | every comparison; Dold and Spanier style signed δ (unverified) would change ε |
| Singular cup: front p-face times back q-face, no sign [Hatcher §3.2] | Tau Ceti `Cup/Basic.lean:259` | C4's ε |
| Upstream cap φ ∩ x = φ(front) · back | `Cap/Simplicial.lean:34-36` | ⟨ψ, φ∩σ⟩ = (φ⌣ψ)(σ) at cochain level with Tau Ceti's cup (derived here, unchecked) |
| Graded commutativity b⌣a = (−1)^{pq} a⌣b | Tau Ceti `GradedCommutativity.lean:86` | `cup-graded-commutative` |
| Comparison degree twist ε(n) | upstream comparisons; mapping-cone connecting map is −1 (existing row) | a twist gives ε(p)ε(q)ε(p+q) on products; for ε(n) = (−1)^n or (−1)^{n(n−1)/2} this is 1 in even degrees, so cycle-class identities survive, odd-degree ones (T1's H¹ ⊗ H¹) do not |
| Cross product of complex orientations | `complexRealHomeomorph` ordering; concatenation ℂ^p × ℂ^q = ℂ^{p+q} | the sign of [Z]∪[W] = [Z·W]; expected + (even real blocks), unproved |
| Relative cup hypothesis U, V open in U ∪ V | Tau Ceti `Cup/Relative.lean:352-354` | none for closed supports |

The existing "Cup product" row should be corrected: "which factor comes first" and "(−1)^{pq}" are one ambiguity; add the degree twist ε(n) as a separate one.

## 5. Vacuity and equality first

- The checked API (associative, unital, biadditive) is also satisfied by the square-zero product (zero in bidegrees p, q > 0). The non-vacuity test `projectiveLine_one_cup_ne_zero` uses only the unit law, so it would pass for that product too. **Missing test:** a product of two positive-degree classes that is nonzero. Cheapest candidates: on ℙ¹ × ℙ¹, pr₁*[pt] ∪ pr₂*[pt] = [pt] ≠ 0 (first transversal case of the kill criterion), or on the topological torus, cupY of the two H¹ classes ≠ 0 (needs C4 and Tau Ceti `Torus.lean`). Neither exists.
- `cycle-class-multiplicative` is an identity: it must be stated exactly with sign +, not up to scalar.
- Pin drift: none. All cup rungs were checked at the current pin; Tau Ceti is a different toolchain and enters only through a backport.

## 6. Amended route

1. `cup-pullback`: pullback on H*(X; ℚ) along morphisms, multiplicative (Yoneda, `mapExactFunctor_comp`). Small.
2. `sheaf-tensor-exact` (Y1). Mathlib candidate.
3. `supported-cup`: supported Yoneda product; compatibility with `forgetSupport` and `cup`. Medium, no sign.
4. `cup-singular-comparison` (C4), absolute and supported, ε recorded exactly. Large. **Go/no-go:** if ε cannot be determined exactly, close the front; both routes to the kill criterion pass through it.
5. `local-class-product`: cross product of normalized local classes on ℂ^p × ℂ^q, sign +.
6. `cycle-class-multiplicative`, first case transversal (ℙ¹ × ℙ¹ fibres), with the non-vacuity test above. Kill criterion unchanged.
7. `cup-graded-commutative`: transfer through 4 from a Tau Ceti backport (41 modules) or Hilton–Eckmann (Y1 + Y3), whichever lands first. Required by T1 (a ∪ a = 0 in odd degree).
8. `cup-hodge-filtration`: F^p ∪ F^q ⊆ F^{p+q} and conjugation multiplicative; tensor-on-D route only. Required by T1.

Decision 0008's sentence "nothing at the pin provides a multiplicative comparison" remains true. The survey missed upstream's cap products and relative-pair machinery, which shrink the cochain side of rung 4.

## 7. Attempts that failed or were not completed

- `rfl` between upstream's degree-n dual cochains and `linearYonedaObj`: fails (type mismatch); the iso needed `homLinearEquiv` with explicit arguments on the second try.
- `Sheaf.monoidalCategory` with only `Sites.Monoidal` imported: fails on `HasWeakSheafify`; succeeds with `HodgeLadder.Cup.SheafExact` imported.
- Searched upstream, Mathlib and the port for any cup, Yoneda/cup comparison, naturality in X of the singular comparison, or derived tensor bifunctor: none found.
- Did not build Tau Ceti or check its axioms; the harvest agent's claim is not re-verified. Did not attempt a Lean proof of the square-zero counter-model; the argument is the standard square-zero extension.
- Could not open Bredon, Iversen, Kashiwara–Schapira or Suárez-Álvarez; all four citations are unverified.
