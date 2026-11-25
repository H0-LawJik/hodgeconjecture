# Sketch: `prime-divisors-cartier`

Date: 2026-11-25. Target: close `lefschetz-1-1-equality` (decision 0004) by proving `HodgeLadder.CycleClassesAreHodgeOne`, the known half in codimension one.

## Where the rung sits

`chern-classes-are-hodge` (checked) gives `HodgeLadder.sheafCycleClassOnCycles_divisor_mem_hodgeClasses`: for Cartier data `c` representing an invertible sheaf `L`, and a unit extension `E` with `L^an ≅ E.sectionSheafOfModules`, the class of `c.divisor` is a Hodge class. `algebraicCycleClassSpan X 1` is spanned by the classes `cycleComponentSheafClass X x hx` of prime divisors (`docs/cycle-class.md`), and `sheafCycleClassOnCycles_single` gives each component its multiplicity. So the known half in codimension one follows once every prime divisor `D` is, up to a nonzero rational factor, the divisor of such Cartier data, with such a unit extension.

## Sub-rungs

| Id | Statement (informal) | Kind | Route | Depends on |
|---|---|---|---|---|
| `ufd-descent` | If `A → B` is a faithfully flat local homomorphism of Noetherian local domains and `B` is a UFD, then `A` is a UFD | foundation (Mathlib) | Mathlib's `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`. For a height-one prime `P` of `A`: `P` is divisorial; flat base change commutes with `(A : I)` for finitely generated `I`, so `PB` is divisorial, hence principal in the UFD `B`; a finitely generated ideal that becomes principal after faithfully flat base change is invertible (rank-one descent, `port/LefschetzPort/RingTheory/FaithfullyFlatRankOne.lean`), hence principal since `A` is local. Normality of `A` (for "height-one primes are divisorial") descends from `B` along the faithfully flat map | none |
| `analytic-stalk-ufd` | The stalk of holomorphic functions on `X(ℂ)` at every point is a UFD | foundation | the chart identifies the stalk with germs on `ℂ^d`, which `okaStalkEquiv` identifies with `LocalOkaRing (Fin d)`; `LocalOkaRing.instUniqueFactorizationMonoid` (`Oka/UFD.lean`) | none |
| `local-factoriality` | The local rings of a smooth projective complex variety are UFDs | foundation | `ufd-descent` along `faithfullyFlat_stalkMap_holomorphicAnalytificationπ` and `analytic-stalk-ufd` | `ufd-descent`, `analytic-stalk-ufd` |
| `prime-divisor-ideal-sheaf` | The ideal sheaf `𝓘_D` of a prime divisor is invertible and is represented by Cartier data whose divisor is `−D` | foundation | Mathlib has `IdealSheafData` but no sheaf-of-modules form, so `𝓘_D` is built as a `Scheme.Modules`. Near each closed point `q ∈ D` the ideal of `D` in the UFD `𝒪_{X,q}` is a height-one prime, hence `(π)`; shrink the neighbourhood until `V(π) = D` there; away from `D` the generator is `1`. Opens around closed points cover `X` (every point specializes to a closed point). `Generates` gives invertibility; `Represents` holds with `fnᵢ = πᵢ⁻¹` (from `u πᵢ = πⱼ`), and `ord πᵢ = 1` along `D`, `0` at other codimension-one points, so the divisor is `−D`. Then `−[D]` is a Hodge class, so `[D]` is | `local-factoriality` |
| `unit-extension-of-invertible` | For every invertible sheaf `L`, a unit extension `E` with `L^an ≅ E.sectionSheafOfModules` | foundation | the transition cocycle of `L` on a trivializing cover gives a class in `H¹(𝒪ˣ)`; `exists_cohomologyClass` realizes it as `E`; compare `E`'s section sheaf (built from local lifts of `1`) with `L^an` frame by frame | none |

`prime-divisors-cartier` is then the assembly: `CycleClassesAreHodgeOne`, and with `lefschetzOneOneEquality_iff` and `lefschetzOneOne_holds`, the checkpoint `LefschetzOneOneEquality`.

## What could go wrong

- The faithful flatness theorem carries the instance `IsLocalIso (comparisonToCanonical X d)`; check it is discharged unconditionally, as in the proof of `lefschetzOneOne`.
- `unit-extension-of-invertible` compares two constructions of a line bundle; a sign or inverse in the transition convention (`g_ij` against `g_ij⁻¹`) changes `E` into its dual and `c₁` into `-c₁`. The divisor–Chern identity is stated for the `E` the hypothesis names, so the comparison has to produce `L^an ≅ E.section`, and the convention goes into `docs/conventions.md`.
- Normality: `ufd-descent` needs it for `A`; if descent of normality is long, use that the local rings of a smooth variety are regular, if Mathlib proves regular local rings are normal at the pin.

## Progress (2026-11-25)

All sub-rungs and the assembly are checked (standard axioms): `ufd-descent`, `analytic-stalk-ufd`, `local-factoriality`, `prime-divisor-ideal-sheaf`, `unit-extension-of-invertible`, and `prime-divisors-cartier` with `lefschetz-1-1-equality` (`HodgeLadder.lefschetzOneOneEquality_holds`). `unit-extension-of-invertible` did not need the stack's `AnalytificationGenerates`: invertibility of L^an comes from coherence and rank-one stalks, and E is built from the frames of L^an directly (middle sheaf of pairs (n, v)), not from `exists_cohomologyClass`.

## Order

`ufd-descent` first (self-contained, upstreamable), then `analytic-stalk-ufd`, `local-factoriality`, `prime-divisor-cartier-data`; `unit-extension-of-invertible` is independent and can run in parallel.
