module

public import LefschetzPort.TauCeti.AlgebraicTopology.Singular.Shuffle
public import Other.AlgebraicTopology.Singular.Cap.Triad
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
public import HodgeConjecture.Mathlib.Topology.Category.TopPair
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
public import LefschetzPort.TauCeti.Algebra.Homology.ModuleCat.Basic
public import LefschetzPort.TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
import all LefschetzPort.TauCeti.AlgebraicTopology.SimplicialSet.Shuffle

/-!
# The shuffle cross product of relative cycles

Rung `relative-cross-chain` (front `cup`, sub-rung of `local-class-product`). Tau Ceti's shuffle
map `C(P) ⊗ C(Q) → C(P × Q)` sends `C(A) ⊗ C(Q)` into `C(A × Q)` and `C(P) ⊗ C(B)` into
`C(P × B)`, so the shuffle product of a relative cycle of `(P, A)` and a relative cycle of
`(Q, B)` is a cycle of upstream's sum-relative triad complex `C(P × Q) / (C(A × Q) + C(P × B))`.
This gives the homology cross product

`H_m(P, A) × H_n(Q, B) → TriadRelativeHomology(P × Q; A × Q, P × B)`
`  → H_{m+n}(P × Q, A × Q ∪ P × B)`,

the second map being upstream's comparison `triadToUnionRelativeHomologyMap`. No excision is
needed to define it; upstream's `triadToUnionRelativeChainMap_quasiIso_of_isOpen` makes it an
isomorphism when `leftProdSet A Q` and `rightProdSet P B` are open in `P × Q`, in particular
when `A` and `B` are open.

Signs. The shuffle chain is Tau Ceti's `SSet.shuffleChain`: the sum over the `(m, n)`-shuffles,
a lattice path with sign `(-1)^N`, `N` the number of pairs (vertical step, later horizontal
step). The identity shuffle (all first-factor steps first) has coefficient `+1`
(`HodgeLadder.Relative.shuffleChain_idShuffle_coeff`, register row "Shuffle map"). The
coefficient change is the left unitor `ℚ ⊗ ℚ ≅ ℚ`, which carries `1 ⊗ 1` to `1`, so no further
sign enters; the tensor differential is Mathlib's `d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y`. Register
rows "Shuffle map", "Tensor product of chain complexes" and "Relative homology cross product".

## Main definitions

* `HodgeLadder.Relative.simplexCoeff`: the coefficient of a simplex in a simplicial chain.
* `HodgeLadder.Relative.idShuffle`: the identity `(p, q)`-shuffle simplex of `Δ[p] ⊗ Δ[q]`.
* `HodgeLadder.Relative.crossChainMap`, `HodgeLadder.Relative.shuffleBilin`: the singular shuffle
  map with rational coefficients, as a chain map and as a bilinear map on chains.
* `HodgeLadder.Relative.relCross`: the cross product into upstream's triad relative homology.
* `HodgeLadder.Relative.relCrossUnion`: the cross product into `H_{m+n}(P × Q, A × Q ∪ P × B)`.
* `HodgeLadder.Relative.homologyBilin`: the bilinear map on homology of a chain-level product that
  sends cycles to cycles and boundaries to boundaries (any complex shape, modules over a
  commutative ring); `HodgeLadder.Relative.descendLinear`, `HodgeLadder.Relative.descendBilin`.

## Main results

* `HodgeLadder.Relative.shuffleChain_idShuffle_coeff`: the identity shuffle has coefficient `+1`.
* `HodgeLadder.Relative.exists_triadCycle_shuffle`: the shuffle product of relative cycles is a
  triad cycle.
* `HodgeLadder.Relative.existsUnique_relCross`, `HodgeLadder.Relative.relCross_homologyπ`: the
  cross product exists, is unique, and is the class of the shuffle product on cycles.
* `HodgeLadder.Relative.relCrossUnion_homologyπ`, `HodgeLadder.Relative.relCrossUnion_naturality`.
* `HodgeLadder.Relative.shuffleBilin_ι`: the shuffle product of two singular simplices;
  `HodgeLadder.Relative.shuffleBilin_vertex`: two vertices give the vertex of the product.
* `HodgeLadder.Relative.shB_d_succ_succ`, `HodgeLadder.Relative.shB_d_zero_succ`,
  `HodgeLadder.Relative.shB_d_succ_zero`: the Leibniz rule of the shuffle product on chains.

## Implementation notes

Tau Ceti's cone `SSet.stdSimplex.prodCone` is a plain `def` of a `module` file, so its body is
not exposed; the vertex computations of `shuffleChain_idShuffle_coeff` read it through the
private `import all` of `LefschetzPort.TauCeti.AlgebraicTopology.SimplicialSet.Shuffle`. This
changes no statement and adds no axiom.

`relCross` is the bilinear map characterized by `existsUnique_relCross`; every later use goes
through `relCross_homologyπ` and the uniqueness, never through the choice. The witness of the
existence is `relCrossAux`: the chain-level product `relMu` on relative chains (the shuffle
product descended through both cokernel projections, `descendBilin`) fed to `homologyBilin`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial
  HomologicalComplex AlgebraicTopology.Singular

universe w v u

namespace HodgeLadder.Relative

/-! ## The identity shuffle -/

section IdShuffle

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

open Classical in
/-- The coefficient of the simplex `x` in a simplicial chain of `K` with coefficients in `T`: the
map out of the coproduct `(K.chainComplex T).X n = ∐_{K_n} T` that is the identity on the summand
of `x` and zero on every other summand. -/
def simplexCoeff (K : SSet.{w}) (T : C) {n : ℕ} (x : K _⦋n⦌) :
    (K.chainComplex T).X n ⟶ T :=
  Cofan.IsColimit.desc (K.isColimitChainComplexXCofan T n) fun y => if y = x then 𝟙 T else 0

/-- The identity `(p, q)`-shuffle: the `n`-simplex of `Δ[p] ⊗ Δ[q]`, `n = p + q`, whose lattice
path takes all `p` horizontal (first-factor) steps first. Its vertices are
`(min i p, i - p)` for `i = 0, …, n` (truncated subtraction). -/
def idShuffle (p q n : ℕ) (h : p + q = n) : ((Δ[p] : SSet.{w}) ⊗ Δ[q]) _⦋n⦌ :=
  (SSet.stdSimplex.objMk (n := ⦋p⦌) (m := Opposite.op ⦋n⦌)
      ⟨fun i : Fin (n + 1) => (⟨min i.val p, by omega⟩ : Fin (p + 1)), fun i j hij => by
        change min i.val p ≤ min j.val p; exact min_le_min_right p hij⟩,
    SSet.stdSimplex.objMk (n := ⦋q⦌) (m := Opposite.op ⦋n⦌)
      ⟨fun i : Fin (n + 1) => (⟨i.val - p, by omega⟩ : Fin (q + 1)), fun i j hij => by
        change i.val - p ≤ j.val - p; exact Nat.sub_le_sub_right hij p⟩)

/-- The coefficient of `x` on the summand of `x` is the identity. -/
@[reassoc (attr := simp)]
lemma ι_simplexCoeff_self (K : SSet.{w}) (T : C) {n : ℕ} (x : K _⦋n⦌) :
    K.ιChainComplex x ≫ simplexCoeff K T x = 𝟙 T :=
  (Cofan.IsColimit.fac (K.isColimitChainComplexXCofan T n) _ x).trans (by simp)

/-- The coefficient of `x` on the summand of a simplex `y ≠ x` is zero. -/
lemma ι_simplexCoeff_of_ne (K : SSet.{w}) (T : C) {n : ℕ} {x y : K _⦋n⦌} (h : y ≠ x) :
    K.ιChainComplex y ≫ simplexCoeff K T x = 0 :=
  (Cofan.IsColimit.fac (K.isColimitChainComplexXCofan T n) _ y).trans (by simp [h])

/-- A simplex of `Δ[p] ⊗ Δ[q]` is the identity shuffle exactly when its `i`-th vertex is
`(min i p, i - p)` for every `i`. -/
lemma eq_idShuffle_iff {p q n : ℕ} (h : p + q = n) (x : ((Δ[p] : SSet.{w}) ⊗ Δ[q]) _⦋n⦌) :
    x = idShuffle p q n h ↔
      ∀ i : Fin (n + 1), (x.1 i).val = min i.val p ∧ (x.2 i).val = i.val - p := by
  constructor
  · rintro rfl i
    exact ⟨rfl, rfl⟩
  · intro hx
    exact Prod.ext (SSet.stdSimplex.ext _ _ fun i => Fin.ext (hx i).1)
      (SSet.stdSimplex.ext _ _ fun i => Fin.ext (hx i).2)

/-- Vertex `i + 1` of the cone on `y` pushed along the zeroth face of the first factor. -/
lemma prodCone_whiskerRight_succ {p q n : ℕ} (y : ((Δ[p] : SSet.{w}) ⊗ Δ[q]) _⦋n⦌)
    (i : Fin (n + 1)) :
    ((SSet.stdSimplex.prodCone ((SSet.stdSimplex.δ 0 ▷ (Δ[q] : SSet.{w})).app _ y)).1
        i.succ).val = (y.1 i).val + 1 ∧
      ((SSet.stdSimplex.prodCone ((SSet.stdSimplex.δ 0 ▷ (Δ[q] : SSet.{w})).app _ y)).2
        i.succ).val = (y.2 i).val := by
  constructor
  · change ((SimplexCategory.δ (0 : Fin (p + 2))).toOrderHom (y.1 i)).val = _
    simp [SimplexCategory.δ]
  · rfl

/-- Vertex `1` of the cone on `y` pushed along the zeroth face of the second factor has second
coordinate at least `1`. -/
lemma prodCone_whiskerLeft_one {p q n : ℕ} (y : ((Δ[p] : SSet.{w}) ⊗ Δ[q]) _⦋n⦌) :
    1 ≤ ((SSet.stdSimplex.prodCone (((Δ[p] : SSet.{w}) ◁ SSet.stdSimplex.δ 0).app _ y)).2
        (0 : Fin (n + 1)).succ).val := by
  change 1 ≤ ((SimplexCategory.δ (0 : Fin (q + 2))).toOrderHom (y.2 0)).val
  simp [SimplexCategory.δ]

/-- **The identity shuffle has coefficient `+1` in Tau Ceti's shuffle chain**, exactly (register
row "Shuffle map"). Every other term of `SSet.shuffleChain` carries a sign `(-1)^N` with `N` the
number of (vertical step, later horizontal step) pairs; the identity shuffle has `N = 0`. -/
theorem shuffleChain_idShuffle_coeff (T : C) (p q n : ℕ) (h : p + q = n) :
    SSet.shuffleChain T p q n h ≫
        simplexCoeff ((Δ[p] : SSet.{w}) ⊗ Δ[q]) T (idShuffle p q n h) = 𝟙 T := by
  induction p generalizing q n with
  | zero =>
    obtain rfl : n = q := by omega
    rw [SSet.shuffleChain_zero_left T n h (SSet.stdSimplex.map (SimplexCategory.const _ _ 0))]
    convert ι_simplexCoeff_self _ T _
    refine ((eq_idShuffle_iff h _).2 fun i => ⟨?_, ?_⟩).symm
    · rw [Fin.val_eq_zero, Nat.min_zero]
    · rfl
  | succ p ih =>
    cases q with
    | zero =>
      obtain rfl : n = p + 1 := by omega
      rw [SSet.shuffleChain_zero_right T (p + 1) h
        (SSet.stdSimplex.map (SimplexCategory.const _ _ 0))]
      convert ι_simplexCoeff_self _ T _
      refine ((eq_idShuffle_iff h _).2 fun i => ⟨?_, ?_⟩).symm
      · change i.val = min i.val (p + 1)
        omega
      · rw [Fin.val_eq_zero]
        omega
    | succ q =>
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [SSet.shuffleChain_succ_succ]
      simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]
      have h1 : (SSet.chainComplexMap (SSet.stdSimplex.δ 0 ▷ (Δ[q + 1] : SSet.{w})) T).f n ≫
          SSet.stdSimplex.prodConeChain (p + 1) (q + 1) T n ≫
            simplexCoeff ((Δ[p + 1] : SSet.{w}) ⊗ Δ[q + 1]) T
              (idShuffle (p + 1) (q + 1) (n + 1) h) =
          simplexCoeff ((Δ[p] : SSet.{w}) ⊗ Δ[q + 1]) T (idShuffle p (q + 1) n (by omega)) := by
        ext y
        rw [SSet.ι_chainComplexMap_f_assoc, SSet.stdSimplex.ιChainComplex_prodConeChain_assoc]
        by_cases hy : y = idShuffle p (q + 1) n (by omega)
        · have hc : SSet.stdSimplex.prodCone
              ((SSet.stdSimplex.δ 0 ▷ (Δ[q + 1] : SSet.{w})).app _ y) =
                idShuffle (p + 1) (q + 1) (n + 1) h := by
            refine (eq_idShuffle_iff h _).2 fun i => ?_
            cases i using Fin.cases with
            | zero => exact ⟨rfl, (Nat.zero_sub (p + 1)).symm⟩
            | succ i =>
              obtain ⟨h₁, h₂⟩ := prodCone_whiskerRight_succ y i
              obtain ⟨k₁, k₂⟩ := (eq_idShuffle_iff (by omega) y).1 hy i
              rw [h₁, h₂, k₁, k₂, Fin.val_succ]
              omega
          rw [hc, ι_simplexCoeff_self, hy, ι_simplexCoeff_self]
        · have hc : SSet.stdSimplex.prodCone
              ((SSet.stdSimplex.δ 0 ▷ (Δ[q + 1] : SSet.{w})).app _ y) ≠
                idShuffle (p + 1) (q + 1) (n + 1) h := by
            intro hc
            refine hy ((eq_idShuffle_iff (by omega) y).2 fun i => ?_)
            obtain ⟨h₁, h₂⟩ := prodCone_whiskerRight_succ y i
            obtain ⟨k₁, k₂⟩ := (eq_idShuffle_iff h _).1 hc i.succ
            rw [h₁, Fin.val_succ] at k₁
            rw [h₂, Fin.val_succ] at k₂
            omega
          rw [ι_simplexCoeff_of_ne _ _ hc, ι_simplexCoeff_of_ne _ _ hy]
      have h2 : (SSet.chainComplexMap ((Δ[p + 1] : SSet.{w}) ◁ SSet.stdSimplex.δ 0) T).f n ≫
          SSet.stdSimplex.prodConeChain (p + 1) (q + 1) T n ≫
            simplexCoeff ((Δ[p + 1] : SSet.{w}) ⊗ Δ[q + 1]) T
              (idShuffle (p + 1) (q + 1) (n + 1) h) = 0 := by
        ext y
        rw [SSet.ι_chainComplexMap_f_assoc, SSet.stdSimplex.ιChainComplex_prodConeChain_assoc,
          comp_zero]
        refine ι_simplexCoeff_of_ne _ _ fun hc => ?_
        have k := ((eq_idShuffle_iff h _).1 hc (0 : Fin (n + 1)).succ).2
        have l := prodCone_whiskerLeft_one y
        rw [k, Fin.val_succ, Fin.val_zero] at l
        omega
      rw [h1, h2, comp_zero, smul_zero, add_zero, ih]

end IdShuffle

/-! ## Bilinear maps on homology -/

section Bilinear

variable {R : Type u} [CommRing R]

/-- A linear map that kills the kernel of a surjection `π` descends along `π`. -/
def descendLinear {M N L : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup L] [Module R L] (π : M →ₗ[R] N) (hπ : Function.Surjective π) (f : M →ₗ[R] L)
    (hf : ∀ x, π x = 0 → f x = 0) : N →ₗ[R] L :=
  (LinearMap.ker π).liftQ f (fun x hx => hf x hx) ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

/-- The descended map on the image of an element. -/
@[simp]
lemma descendLinear_apply {M N L : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup L] [Module R L] (π : M →ₗ[R] N) (hπ : Function.Surjective π)
    (f : M →ₗ[R] L) (hf : ∀ x, π x = 0 → f x = 0) (x : M) :
    descendLinear π hπ f hf (π x) = f x := by
  have : (π.quotKerEquivOfSurjective hπ).symm (π x) = Submodule.Quotient.mk x :=
    (LinearEquiv.symm_apply_eq _).2 (by simp)
  simp only [descendLinear, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, this]
  rfl

/-- A bilinear map that vanishes when either argument is in the kernel of a surjection descends
along the two surjections. -/
def descendBilin {M₁ M₂ N₁ N₂ L : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup L] [Module R L] (π₁ : M₁ →ₗ[R] N₁) (hπ₁ : Function.Surjective π₁)
    (π₂ : M₂ →ₗ[R] N₂) (hπ₂ : Function.Surjective π₂) (Φ : M₁ →ₗ[R] M₂ →ₗ[R] L)
    (h₁ : ∀ x y, π₁ x = 0 → Φ x y = 0) (h₂ : ∀ x y, π₂ y = 0 → Φ x y = 0) :
    N₁ →ₗ[R] N₂ →ₗ[R] L :=
  descendLinear π₁ hπ₁ (descendLinear π₂ hπ₂ Φ.flip
      (fun y hy => LinearMap.ext fun x => h₂ x y hy)).flip
    (fun x hx => LinearMap.ext fun z => by
      obtain ⟨y, rfl⟩ := hπ₂ z
      simp [h₁ x y hx])

/-- The descended bilinear map on images of elements. -/
@[simp]
lemma descendBilin_apply {M₁ M₂ N₁ N₂ L : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂]
    [Module R N₂] [AddCommGroup L] [Module R L] (π₁ : M₁ →ₗ[R] N₁)
    (hπ₁ : Function.Surjective π₁) (π₂ : M₂ →ₗ[R] N₂) (hπ₂ : Function.Surjective π₂)
    (Φ : M₁ →ₗ[R] M₂ →ₗ[R] L) (h₁ : ∀ x y, π₁ x = 0 → Φ x y = 0)
    (h₂ : ∀ x y, π₂ y = 0 → Φ x y = 0) (x : M₁) (y : M₂) :
    descendBilin π₁ hπ₁ π₂ hπ₂ Φ h₁ h₂ (π₁ x) (π₂ y) = Φ x y := by
  simp [descendBilin]

variable {ι : Type*} {c : ComplexShape ι} {K₁ K₂ K₀ : HomologicalComplex (ModuleCat.{v} R) c}
  {p q n p' q' n' n'' : ι}

/-- The product of cycles, for a bilinear map of chains that sends two cycles to a cycle. -/
def cyclesBilin (hn'' : c.next n = n'') (μ : K₁.X p →ₗ[R] K₂.X q →ₗ[R] K₀.X n)
    (hcyc : ∀ a b, K₀.d n n'' (μ (K₁.iCycles p a) (K₂.iCycles q b)) = 0) :
    K₁.cycles p →ₗ[R] K₂.cycles q →ₗ[R] K₀.cycles n :=
  LinearMap.mk₂ R
    (fun a b => K₀.moduleCatCyclesMk (μ (K₁.iCycles p a) (K₂.iCycles q b)) n'' hn'' (hcyc a b))
    (fun a a' b => K₀.moduleCat_iCycles_injective n (by simp))
    (fun r a b => K₀.moduleCat_iCycles_injective n (by simp))
    (fun a b b' => K₀.moduleCat_iCycles_injective n (by simp))
    (fun r a b => K₀.moduleCat_iCycles_injective n (by simp))

/-- The underlying chain of the product of cycles is the product of the chains. -/
@[simp]
lemma iCycles_cyclesBilin (hn'' : c.next n = n'') (μ : K₁.X p →ₗ[R] K₂.X q →ₗ[R] K₀.X n)
    (hcyc : ∀ a b, K₀.d n n'' (μ (K₁.iCycles p a) (K₂.iCycles q b)) = 0) (a : K₁.cycles p)
    (b : K₂.cycles q) :
    K₀.iCycles n (cyclesBilin hn'' μ hcyc a b) = μ (K₁.iCycles p a) (K₂.iCycles q b) := by
  simp [cyclesBilin]

/-- **The product on homology** of a bilinear map of chains that sends two cycles to a cycle, and
a boundary and a cycle, in either order, to a boundary: the class of the product of
representatives (`homologyBilin_homologyπ`). This is the homology map
`H_p(K₁) × H_q(K₂) → H_n(K₀)` of a chain-level product, for any complex shape. -/
def homologyBilin (hp : c.prev p = p') (hq : c.prev q = q') (hn : c.prev n = n')
    (hn'' : c.next n = n'') (μ : K₁.X p →ₗ[R] K₂.X q →ₗ[R] K₀.X n)
    (hcyc : ∀ a b, K₀.d n n'' (μ (K₁.iCycles p a) (K₂.iCycles q b)) = 0)
    (hleft : ∀ (w : K₁.X p') (b : K₂.cycles q), ∃ v : K₀.X n',
      μ (K₁.d p' p w) (K₂.iCycles q b) = K₀.d n' n v)
    (hright : ∀ (a : K₁.cycles p) (w : K₂.X q'), ∃ v : K₀.X n',
      μ (K₁.iCycles p a) (K₂.d q' q w) = K₀.d n' n v) :
    K₁.homology p →ₗ[R] K₂.homology q →ₗ[R] K₀.homology n :=
  descendBilin (K₁.homologyπ p).hom (K₁.moduleCat_homologyπ_surjective p)
    (K₂.homologyπ q).hom (K₂.moduleCat_homologyπ_surjective q)
    ((cyclesBilin hn'' μ hcyc).compr₂ (K₀.homologyπ n).hom)
    (fun a b ha => by
      obtain ⟨w, rfl⟩ := (K₁.moduleCat_homologyπ_eq_zero_iff hp a).1 ha
      obtain ⟨v, hv⟩ := hleft w b
      have : cyclesBilin hn'' μ hcyc (K₁.toCycles p' p w) b = K₀.toCycles n' n v :=
        K₀.moduleCat_iCycles_injective n (by simp [hv])
      simp only [LinearMap.compr₂_apply, this]
      exact (K₀.moduleCat_homologyπ_eq_zero_iff hn _).2 ⟨v, rfl⟩)
    (fun a b hb => by
      obtain ⟨w, rfl⟩ := (K₂.moduleCat_homologyπ_eq_zero_iff hq b).1 hb
      obtain ⟨v, hv⟩ := hright a w
      have : cyclesBilin hn'' μ hcyc a (K₂.toCycles q' q w) = K₀.toCycles n' n v :=
        K₀.moduleCat_iCycles_injective n (by simp [hv])
      simp only [LinearMap.compr₂_apply, this]
      exact (K₀.moduleCat_homologyπ_eq_zero_iff hn _).2 ⟨v, rfl⟩)

/-- The product on homology is the class of the product of representing cycles. -/
lemma homologyBilin_homologyπ (hp : c.prev p = p') (hq : c.prev q = q') (hn : c.prev n = n')
    (hn'' : c.next n = n'') (μ : K₁.X p →ₗ[R] K₂.X q →ₗ[R] K₀.X n)
    (hcyc : ∀ a b, K₀.d n n'' (μ (K₁.iCycles p a) (K₂.iCycles q b)) = 0)
    (hleft : ∀ (w : K₁.X p') (b : K₂.cycles q), ∃ v : K₀.X n',
      μ (K₁.d p' p w) (K₂.iCycles q b) = K₀.d n' n v)
    (hright : ∀ (a : K₁.cycles p) (w : K₂.X q'), ∃ v : K₀.X n',
      μ (K₁.iCycles p a) (K₂.d q' q w) = K₀.d n' n v) (a : K₁.cycles p) (b : K₂.cycles q) :
    homologyBilin hp hq hn hn'' μ hcyc hleft hright (K₁.homologyπ p a) (K₂.homologyπ q b) =
      K₀.homologyπ n (cyclesBilin hn'' μ hcyc a b) :=
  descendBilin_apply _ _ _ _ _ _ _ a b

end Bilinear

/-! ## The singular shuffle product with rational coefficients -/

/-- The singular shuffle map with rational coefficients,
`C(P; ℚ) ⊗ C(Q; ℚ) ⟶ C(P × Q; ℚ)`: Tau Ceti's `TopCat.shuffle` with unit coefficients, followed
by the coefficient change along the left unitor `ℚ ⊗ ℚ ≅ ℚ`. -/
def crossChainMap (P Q : TopCat.{0}) :
    SingularChainComplex ℚ P ⊗ SingularChainComplex ℚ Q ⟶ SingularChainComplex ℚ (P ⊗ Q) :=
  TopCat.shuffle P Q (𝟙_ (ModuleCat.{0} ℚ)) (𝟙_ (ModuleCat.{0} ℚ)) ≫
    ((SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).map (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom).app _

/-- The shuffle product of an `m`-chain of `P` and an `n`-chain of `Q`, an `(m + n)`-chain of
`P × Q`, as a bilinear map. -/
def shuffleBilin (P Q : TopCat.{0}) (m n : ℕ) :
    (SingularChainComplex ℚ P).X m →ₗ[ℚ] (SingularChainComplex ℚ Q).X n →ₗ[ℚ]
      (SingularChainComplex ℚ (P ⊗ Q)).X (m + n) :=
  (TensorProduct.mk ℚ _ _).compr₂
    (ιTensorObj (SingularChainComplex ℚ P) (SingularChainComplex ℚ Q) m n (m + n) rfl ≫
      (crossChainMap P Q).f (m + n)).hom

/-- The shuffle product with the total degree given by an equation `h : p + q = k`;
`shuffleBilin P Q m n` is the case `k = m + n`. -/
def shB (P Q : TopCat.{0}) (p q k : ℕ) (h : p + q = k) :
    (SingularChainComplex ℚ P).X p →ₗ[ℚ] (SingularChainComplex ℚ Q).X q →ₗ[ℚ]
      (SingularChainComplex ℚ (P ⊗ Q)).X k :=
  (TensorProduct.mk ℚ _ _).compr₂
    (ιTensorObj (SingularChainComplex ℚ P) (SingularChainComplex ℚ Q) p q k h ≫
      (crossChainMap P Q).f k).hom

/-- `shuffleBilin` is `shB` in total degree `m + n`. -/
lemma shuffleBilin_eq_shB (P Q : TopCat.{0}) (m n : ℕ) :
    shuffleBilin P Q m n = shB P Q m n (m + n) rfl := rfl

/-- `shB` on a pair of chains is the shuffle map on their tensor. -/
lemma shB_apply (P Q : TopCat.{0}) (p q k : ℕ) (h : p + q = k)
    (x : (SingularChainComplex ℚ P).X p) (y : (SingularChainComplex ℚ Q).X q) :
    shB P Q p q k h x y =
      (ιTensorObj (SingularChainComplex ℚ P) (SingularChainComplex ℚ Q) p q k h ≫
        (crossChainMap P Q).f k).hom (x ⊗ₜ[ℚ] y) := rfl

/-- The singular chain functor with rational coefficients. -/
abbrev singChainFunctor : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)

set_option backward.isDefEq.respectTransparency false in
/-- The shuffle map with rational coefficients is natural in both spaces. -/
lemma crossChainMap_naturality {P P' Q Q' : TopCat.{0}} (f : P ⟶ P') (g : Q ⟶ Q') :
    (singChainFunctor.map f ⊗ₘ singChainFunctor.map g) ≫ crossChainMap P' Q' =
      crossChainMap P Q ≫ singChainFunctor.map (f ⊗ₘ g) := by
  unfold crossChainMap
  have hn := ((SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).map
    (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom).naturality (TopCat.toSSet.map (f ⊗ₘ g))
  erw [← Category.assoc, TopCat.shuffle_naturality f g, Category.assoc, Category.assoc, hn]
  rfl

/-- The shuffle product is natural in both spaces, on chains. -/
lemma shB_naturality {P P' Q Q' : TopCat.{0}} (f : P ⟶ P') (g : Q ⟶ Q') (p q k : ℕ)
    (h : p + q = k) (x : (SingularChainComplex ℚ P).X p) (y : (SingularChainComplex ℚ Q).X q) :
    shB P' Q' p q k h ((singChainFunctor.map f).f p x) ((singChainFunctor.map g).f q y) =
      (singChainFunctor.map (f ⊗ₘ g)).f k (shB P Q p q k h x y) := by
  have e := congrArg (fun φ => φ.hom (x ⊗ₜ[ℚ] y))
    (congrArg (fun φ => ιTensorObj (SingularChainComplex ℚ P) (SingularChainComplex ℚ Q)
      p q k h ≫ HomologicalComplex.Hom.f φ k) (crossChainMap_naturality f g))
  simp only [HomologicalComplex.comp_f] at e
  rw [HomologicalComplex.ι_tensorHom_f_assoc] at e
  exact e

set_option backward.isDefEq.respectTransparency false in
/-- The boundary of the shuffle product of chains, before the differential is evaluated. -/
lemma shB_d_aux (P Q : TopCat.{0}) (p q k k' : ℕ) (h : p + q = k)
    (x : (SingularChainComplex ℚ P).X p) (y : (SingularChainComplex ℚ Q).X q) :
    (SingularChainComplex ℚ (P ⊗ Q)).d k k' (shB P Q p q k h x y) =
      ((ιTensorObj (SingularChainComplex ℚ P) (SingularChainComplex ℚ Q) p q k h ≫
        (HomologicalComplex.tensorObj (SingularChainComplex ℚ P)
          (SingularChainComplex ℚ Q)).d k k') ≫
          (crossChainMap P Q).f k').hom (x ⊗ₜ[ℚ] y) := by
  rw [shB_apply, Category.assoc]
  erw [← (crossChainMap P Q).comm k k']
  rfl

/-- **Leibniz rule** for the shuffle product, both degrees positive:
`d (x × y) = d x × y + (-1)^p x × d y` (register row "Tensor product of chain complexes"). -/
lemma shB_d_succ_succ {P Q : TopCat.{0}} {p q k : ℕ} (p' q' k' : ℕ) (hp : p = p' + 1)
    (hq : q = q' + 1) (hk : k = k' + 1) (h : p + q = k)
    (x : (SingularChainComplex ℚ P).X p) (y : (SingularChainComplex ℚ Q).X q) :
    (SingularChainComplex ℚ (P ⊗ Q)).d k k' (shB P Q p q k h x y) =
      shB P Q p' q k' (by omega) ((SingularChainComplex ℚ P).d p p' x) y +
        (-1 : ℤ) ^ p • shB P Q p q' k' (by omega) x ((SingularChainComplex ℚ Q).d q q' y) := by
  subst hp hq hk
  rw [shB_d_aux, HomologicalComplex.ιTensorObj_d_of_rel _ _ h (p' := p') (q' := q') (j' := k')
    (by simp) (by simp) (by omega)]
  simp [shB_apply, Units.smul_def]

/-- **Leibniz rule** for the shuffle product with a vertex chain on the left:
`d (x × y) = x × d y`. -/
lemma shB_d_zero_succ {P Q : TopCat.{0}} {q k : ℕ} (q' k' : ℕ) (hq : q = q' + 1)
    (hk : k = k' + 1) (h : 0 + q = k)
    (x : (SingularChainComplex ℚ P).X 0) (y : (SingularChainComplex ℚ Q).X q) :
    (SingularChainComplex ℚ (P ⊗ Q)).d k k' (shB P Q 0 q k h x y) =
      shB P Q 0 q' k' (by omega) x ((SingularChainComplex ℚ Q).d q q' y) := by
  subst hq hk
  rw [shB_d_aux, HomologicalComplex.ιTensorObj_d_of_not_rel_left _ _ h (q' := q') (j' := k')
    (by simp) (by simp) (by omega)]
  simp [shB_apply]

/-- **Leibniz rule** for the shuffle product with a vertex chain on the right:
`d (x × y) = d x × y`. -/
lemma shB_d_succ_zero {P Q : TopCat.{0}} {p k : ℕ} (p' k' : ℕ) (hp : p = p' + 1)
    (hk : k = k' + 1) (h : p + 0 = k)
    (x : (SingularChainComplex ℚ P).X p) (y : (SingularChainComplex ℚ Q).X 0) :
    (SingularChainComplex ℚ (P ⊗ Q)).d k k' (shB P Q p 0 k h x y) =
      shB P Q p' 0 k' (by omega) ((SingularChainComplex ℚ P).d p p' x) y := by
  subst hp hk
  rw [shB_d_aux, HomologicalComplex.ιTensorObj_d_of_not_rel_right _ _ h (p' := p') (j' := k')
    (by simp) (by simp) (by omega)]
  simp [shB_apply]

/-- **The shuffle product of two singular simplices** `σ : Δ^p → P`, `τ : Δ^q → Q` is the image of
Tau Ceti's shuffle chain of `Δ[p] ⊗ Δ[q]` under the map classified by `(σ, τ)`. -/
theorem shuffleBilin_ι {P Q : TopCat.{0}} {p q : ℕ} (σ : (TopCat.toSSet.obj P) _⦋p⦌)
    (τ : (TopCat.toSSet.obj Q) _⦋q⦌) :
    shuffleBilin P Q p q
        (((TopCat.toSSet.obj P).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom (1 : ℚ))
        (((TopCat.toSSet.obj Q).ιChainComplex (R := ModuleCat.of ℚ ℚ) τ).hom (1 : ℚ)) =
      (SSet.shuffleChain (ModuleCat.of ℚ ℚ) p q (p + q) rfl ≫
        (SSet.chainComplexMap
          ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
            Functor.LaxMonoidal.μ TopCat.toSSet P Q) (ModuleCat.of ℚ ℚ)).f (p + q)).hom
        (1 : ℚ) := by
  have key : ((TopCat.toSSet.obj P).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ ⊗ₘ
        (TopCat.toSSet.obj Q).ιChainComplex (R := ModuleCat.of ℚ ℚ) τ) ≫
        ιTensorObj (SingularChainComplex ℚ P) (SingularChainComplex ℚ Q) p q (p + q) rfl ≫
          (crossChainMap P Q).f (p + q) =
      (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom ≫ SSet.shuffleChain (ModuleCat.of ℚ ℚ) p q (p + q) rfl ≫
        (SSet.chainComplexMap
          ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
            Functor.LaxMonoidal.μ TopCat.toSSet P Q) (ModuleCat.of ℚ ℚ)).f (p + q) := by
    unfold crossChainMap
    erw [HomologicalComplex.comp_f,
      TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_assoc (C := ModuleCat.{0} ℚ)]
    have hn := ((SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).map
      (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom).naturality
        ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
          Functor.LaxMonoidal.μ TopCat.toSSet P Q)
    erw [← HomologicalComplex.comp_f, hn, HomologicalComplex.comp_f,
      SSet.shuffleChain_chainComplexFunctor_map_app_f_assoc]
    rfl
  have h1 := congrArg (fun f => f.hom ((1 : ℚ) ⊗ₜ[ℚ] (1 : ℚ))) key
  have h2 : ((λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom).hom ((1 : ℚ) ⊗ₜ[ℚ] (1 : ℚ)) = (1 : ℚ) := by
    erw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
    exact one_smul ℚ (1 : ℚ)
  refine h1.trans ?_
  change (SSet.shuffleChain (ModuleCat.of ℚ ℚ) p q (p + q) rfl ≫
        (SSet.chainComplexMap
          ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
            Functor.LaxMonoidal.μ TopCat.toSSet P Q) (ModuleCat.of ℚ ℚ)).f (p + q)).hom
      (((λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom).hom ((1 : ℚ) ⊗ₜ[ℚ] (1 : ℚ))) = _
  rw [h2]

/-- **Vertex normalization**: the shuffle product of two singular vertices is the vertex of the
product, with coefficient `1` (register row "Relative homology cross product"). -/
theorem shuffleBilin_vertex {P Q : TopCat.{0}} (σ : (TopCat.toSSet.obj P) _⦋0⦌)
    (τ : (TopCat.toSSet.obj Q) _⦋0⦌) :
    shuffleBilin P Q 0 0
        (((TopCat.toSSet.obj P).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom (1 : ℚ))
        (((TopCat.toSSet.obj Q).ιChainComplex (R := ModuleCat.of ℚ ℚ) τ).hom (1 : ℚ)) =
      ((TopCat.toSSet.obj (P ⊗ Q)).ιChainComplex (R := ModuleCat.of ℚ ℚ)
        ((Functor.LaxMonoidal.μ TopCat.toSSet P Q).app _
          ((σ, τ) : (TopCat.toSSet.obj P ⊗ TopCat.toSSet.obj Q) _⦋0⦌))).hom (1 : ℚ) := by
  rw [shuffleBilin_ι]
  erw [SSet.shuffleChain_zero_zero (ModuleCat.of ℚ ℚ) rfl
      (SSet.yonedaEquiv (𝟙 _), SSet.yonedaEquiv (𝟙 _)), SSet.ι_chainComplexMap_f]
  change (((TopCat.toSSet.obj (P ⊗ Q)).ιChainComplex (R := ModuleCat.of ℚ ℚ)
    ((Functor.LaxMonoidal.μ TopCat.toSSet P Q).app _
      (((SSet.yonedaEquiv.symm σ).app _ (SSet.yonedaEquiv (𝟙 _)),
        (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (𝟙 _))) :
          (TopCat.toSSet.obj P ⊗ TopCat.toSSet.obj Q) _⦋0⦌))).hom (1 : ℚ)) = _
  rw [SSet.yonedaEquiv_symm_app_id, SSet.yonedaEquiv_symm_app_id]

/-! ## The cross product on relative homology -/

/-- `A × Q`, as a subset of `P × Q`. -/
abbrev leftProdSet {P : TopCat.{0}} (A : Set P) (Q : TopCat.{0}) :
    Set ((P ⊗ Q : TopCat.{0}) : Type) :=
  {z | fst P Q z ∈ A}

/-- `P × B`, as a subset of `P × Q`. -/
abbrev rightProdSet (P : TopCat.{0}) {Q : TopCat.{0}} (B : Set Q) :
    Set ((P ⊗ Q : TopCat.{0}) : Type) :=
  {z | snd P Q z ∈ B}

/-- The pair `(P × Q, A × Q ∪ P × B)`. -/
abbrev crossUnionPair {P Q : TopCat.{0}} (A : Set P) (B : Set Q) : TopPair.{0} :=
  TopPair.ofSubset (X := P ⊗ Q) (leftProdSet A Q ∪ rightProdSet P B)

/-! ### Chain-level facts for the relative cross product -/

/-- `A × Q ⟶ P × Q` lands in `leftProdSet A Q`. -/
def leftProdLift {P : TopCat.{0}} (A : Set P) (Q : TopCat.{0}) :
    (TopPair.ofSubset A).snd ⊗ Q ⟶ (TopPair.ofSubset (X := P ⊗ Q) (leftProdSet A Q)).snd :=
  TopCat.ofHom ⟨fun z => ⟨(z.1.1, z.2), z.1.2⟩, Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) _⟩

/-- `P × B ⟶ P × Q` lands in `rightProdSet P B`. -/
def rightProdLift (P : TopCat.{0}) {Q : TopCat.{0}} (B : Set Q) :
    P ⊗ (TopPair.ofSubset B).snd ⟶ (TopPair.ofSubset (X := P ⊗ Q) (rightProdSet P B)).snd :=
  TopCat.ofHom ⟨fun z => ⟨(z.1, z.2.1), z.2.2⟩, Continuous.subtype_mk
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) _⟩

/-- `leftProdLift` followed by the inclusion of `A × Q` is the inclusion of `A` times `Q`. -/
lemma leftProdLift_comp {P : TopCat.{0}} (A : Set P) (Q : TopCat.{0}) :
    leftProdLift A Q ≫ (TopPair.ofSubset (X := P ⊗ Q) (leftProdSet A Q)).map =
      (TopPair.ofSubset A).map ⊗ₘ 𝟙 Q := by
  ext; rfl

/-- `rightProdLift` followed by the inclusion of `P × B` is `P` times the inclusion of `B`. -/
lemma rightProdLift_comp (P : TopCat.{0}) {Q : TopCat.{0}} (B : Set Q) :
    rightProdLift P B ≫ (TopPair.ofSubset (X := P ⊗ Q) (rightProdSet P B)).map =
      𝟙 P ⊗ₘ (TopPair.ofSubset B).map := by
  ext; rfl

/-- Chains of `A × Q` vanish in the triad complex. -/
lemma left_comp_triadRelativeChainProjection {P Q : TopCat.{0}} (A : Set P) (B : Set Q) :
    singChainFunctor.map (TopPair.ofSubset (X := P ⊗ Q) (leftProdSet A Q)).map ≫
      triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) = 0 := by
  have h := triadSubspaceChainMap_triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q)
    (rightProdSet P B)
  rw [triadSubspaceChainMap] at h
  have h' := biprod.inl ≫= h
  erw [biprod.inl_desc_assoc, comp_zero] at h'
  exact h'

/-- Chains of `P × B` vanish in the triad complex. -/
lemma right_comp_triadRelativeChainProjection {P Q : TopCat.{0}} (A : Set P) (B : Set Q) :
    singChainFunctor.map (TopPair.ofSubset (X := P ⊗ Q) (rightProdSet P B)).map ≫
      triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) = 0 := by
  have h := triadSubspaceChainMap_triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q)
    (rightProdSet P B)
  rw [triadSubspaceChainMap] at h
  have h' := biprod.inr ≫= h
  erw [biprod.inr_desc_assoc, comp_zero] at h'
  exact h'

/-- The shuffle product of a chain of `A` and a chain of `Q` vanishes in the triad complex. -/
lemma triadProj_shB_left {P Q : TopCat.{0}} (A : Set P) (B : Set Q) {p q k : ℕ}
    (h : p + q = k) (a : (SingularChainComplex ℚ (TopPair.ofSubset A).snd).X p)
    (y : (SingularChainComplex ℚ Q).X q) :
    ((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f k).hom
      (shB P Q p q k h ((singChainFunctor.map (TopPair.ofSubset A).map).f p a) y) = 0 := by
  have e := shB_naturality (TopPair.ofSubset A).map (𝟙 Q) p q k h a y
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply] at e
  erw [e]
  have e1 : singChainFunctor.map ((TopPair.ofSubset A).map ⊗ₘ 𝟙 Q) =
      singChainFunctor.map (leftProdLift A Q) ≫
        singChainFunctor.map (TopPair.ofSubset (X := P ⊗ Q) (leftProdSet A Q)).map :=
    (congrArg singChainFunctor.map (leftProdLift_comp A Q).symm).trans
      (singChainFunctor.map_comp _ _)
  have e2 : singChainFunctor.map ((TopPair.ofSubset A).map ⊗ₘ 𝟙 Q) ≫
      triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) = 0 := by
    rw [e1]
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (left_comp_triadRelativeChainProjection A B)).trans comp_zero)
  have e3 : ((singChainFunctor.map ((TopPair.ofSubset A).map ⊗ₘ 𝟙 Q) ≫
      triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f k).hom
        (shB _ Q p q k h a y) = 0 := by
    rw [e2]; rfl
  exact e3

/-- The shuffle product of a chain of `P` and a chain of `B` vanishes in the triad complex. -/
lemma triadProj_shB_right {P Q : TopCat.{0}} (A : Set P) (B : Set Q) {p q k : ℕ}
    (h : p + q = k) (x : (SingularChainComplex ℚ P).X p)
    (b : (SingularChainComplex ℚ (TopPair.ofSubset B).snd).X q) :
    ((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f k).hom
      (shB P Q p q k h x ((singChainFunctor.map (TopPair.ofSubset B).map).f q b)) = 0 := by
  have e := shB_naturality (𝟙 P) (TopPair.ofSubset B).map p q k h x b
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply] at e
  erw [e]
  have e1 : singChainFunctor.map (𝟙 P ⊗ₘ (TopPair.ofSubset B).map) =
      singChainFunctor.map (rightProdLift P B) ≫
        singChainFunctor.map (TopPair.ofSubset (X := P ⊗ Q) (rightProdSet P B)).map :=
    (congrArg singChainFunctor.map (rightProdLift_comp P B).symm).trans
      (singChainFunctor.map_comp _ _)
  have e2 : singChainFunctor.map (𝟙 P ⊗ₘ (TopPair.ofSubset B).map) ≫
      triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) = 0 := by
    rw [e1]
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (right_comp_triadRelativeChainProjection A B)).trans comp_zero)
  have e3 : ((singChainFunctor.map (𝟙 P ⊗ₘ (TopPair.ofSubset B).map) ≫
      triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f k).hom
        (shB P _ p q k h x b) = 0 := by
    rw [e2]; rfl
  exact e3

/-- Components of upstream's relative chain projection are surjective. -/
lemma relProj_surjective (X : TopPair.{0}) (i : ℕ) :
    Function.Surjective ((relativeChainProjection ℚ X).f i).hom :=
  (ModuleCat.epi_iff_surjective _).1
    (epi_of_isColimit_cofork (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
      (R := ℚ) X i))

/-- The kernel of a component of the relative chain projection consists of subspace chains. -/
lemma exists_of_relProj_eq_zero (X : TopPair.{0}) (i : ℕ) (x : (SingularChainComplex ℚ X.fst).X i)
    (hx : ((relativeChainProjection ℚ X).f i).hom x = 0) :
    ∃ a, ((singChainFunctor.map X.map).f i).hom a = x := by
  have w : ((chainPairFunctor ℚ).obj X).hom.f i ≫ (relativeChainProjection ℚ X).f i = 0 := by
    have h := congrArg (fun q => q.f i) (subspaceChainMap_relativeChainProjection ℚ X)
    exact h
  exact (ShortComplex.moduleCat_exact_iff _).1 (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk (((chainPairFunctor ℚ).obj X).hom.f i) ((relativeChainProjection ℚ X).f i) w)
    (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) X i)) x hx

/-- The relative chain projection commutes with the boundary, on elements. -/
lemma relProj_d (X : TopPair.{0}) (i j : ℕ) (x : (SingularChainComplex ℚ X.fst).X i) :
    ((relativeChainFunctor ℚ).obj X).d i j (((relativeChainProjection ℚ X).f i).hom x) =
      ((relativeChainProjection ℚ X).f j).hom ((SingularChainComplex ℚ X.fst).d i j x) := by
  have := congrArg (fun φ => φ.hom x) ((relativeChainProjection ℚ X).comm i j)
  exact this

/-- The triad projection commutes with the boundary, on elements. -/
lemma triadProj_d (X : TopCat.{0}) (A B : Set X) (i j : ℕ) (x : (SingularChainComplex ℚ X).X i) :
    (triadRelativeChainComplex ℚ X A B).d i j (((triadRelativeChainProjection ℚ X A B).f i).hom x) =
      ((triadRelativeChainProjection ℚ X A B).f j).hom ((SingularChainComplex ℚ X).d i j x) := by
  have := congrArg (fun φ => φ.hom x) ((triadRelativeChainProjection ℚ X A B).comm i j)
  exact this

/-- The boundary of a chain whose class is a relative cycle is a chain of the subspace. -/
lemma exists_d_eq_of_cycle (X : TopPair.{0}) {i : ℕ} (j : ℕ)
    (x : (SingularChainComplex ℚ X.fst).X i) (z : ((relativeChainFunctor ℚ).obj X).cycles i)
    (hz : (((relativeChainFunctor ℚ).obj X).iCycles i).hom z =
      ((relativeChainProjection ℚ X).f i).hom x) :
    ∃ a, ((singChainFunctor.map X.map).f j).hom a = (SingularChainComplex ℚ X.fst).d i j x := by
  refine exists_of_relProj_eq_zero X j _ ?_
  rw [← relProj_d, ← hz]
  exact HomologicalComplex.moduleCat_d_iCycles_apply _ _ _ _

/-- The shuffle product on relative chains, with values in the triad complex. -/
def relMu {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (p q k : ℕ) (h : p + q = k) :
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).X p →ₗ[ℚ]
      ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).X q →ₗ[ℚ]
        (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).X k :=
  descendBilin ((relativeChainProjection ℚ (TopPair.ofSubset A)).f p).hom
    (relProj_surjective _ p) ((relativeChainProjection ℚ (TopPair.ofSubset B)).f q).hom
    (relProj_surjective _ q)
    ((shB P Q p q k h).compr₂
      ((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f k).hom)
    (fun x y hx => by
      obtain ⟨a, rfl⟩ := exists_of_relProj_eq_zero _ p x hx
      exact triadProj_shB_left A B h a y)
    (fun x y hy => by
      obtain ⟨b, rfl⟩ := exists_of_relProj_eq_zero _ q y hy
      exact triadProj_shB_right A B h x b)

/-- `relMu` on projected ambient chains is the projected shuffle product. -/
lemma relMu_apply {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (p q k : ℕ) (h : p + q = k)
    (x : (SingularChainComplex ℚ P).X p) (y : (SingularChainComplex ℚ Q).X q) :
    relMu A B p q k h (((relativeChainProjection ℚ (TopPair.ofSubset A)).f p).hom x)
        (((relativeChainProjection ℚ (TopPair.ofSubset B)).f q).hom y) =
      ((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f k).hom
        (shB P Q p q k h x y) :=
  descendBilin_apply _ _ _ _ _ _ _ x y

/-- The product of two relative cycles is a triad cycle. -/
lemma relMu_cycle {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n n'' : ℕ)
    (a : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).cycles m)
    (b : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles n) :
    (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).d (m + n) n''
      (relMu A B m n (m + n) rfl (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m a)
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n b)) = 0 := by
  by_cases hr : (ComplexShape.down ℕ).Rel (m + n) n''
  swap
  · rw [HomologicalComplex.shape _ _ _ hr]
    rfl
  change n'' + 1 = m + n at hr
  obtain ⟨x, hx⟩ := relProj_surjective (TopPair.ofSubset A) m
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m a)
  obtain ⟨y, hy⟩ := relProj_surjective (TopPair.ofSubset B) n
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n b)
  erw [← hx, ← hy]
  erw [relMu_apply]
  rw [triadProj_d]
  rcases m with _ | m' <;> rcases n with _ | n'
  · omega
  · obtain ⟨b', hb'⟩ := exists_d_eq_of_cycle (TopPair.ofSubset B) n' y b hy.symm
    erw [shB_d_zero_succ n' n'' rfl (by omega), ← hb']
    exact triadProj_shB_right A B _ x b'
  · obtain ⟨a', ha'⟩ := exists_d_eq_of_cycle (TopPair.ofSubset A) m' x a hx.symm
    erw [shB_d_succ_zero m' n'' rfl (by omega), ← ha']
    exact triadProj_shB_left A B _ a' y
  · obtain ⟨a', ha'⟩ := exists_d_eq_of_cycle (TopPair.ofSubset A) m' x a hx.symm
    obtain ⟨b', hb'⟩ := exists_d_eq_of_cycle (TopPair.ofSubset B) n' y b hy.symm
    erw [shB_d_succ_succ m' n' n'' rfl rfl (by omega), ← ha', ← hb']
    rw [map_add, map_zsmul, triadProj_shB_left A B _ a' y, triadProj_shB_right A B _ x b',
      smul_zero, add_zero]

/-- A relative boundary times a relative cycle is a triad boundary. -/
lemma relMu_boundary_left {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ)
    (w : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).X (m + 1))
    (b : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles n) :
    ∃ v : (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).X
        (m + n + 1),
      relMu A B m n (m + n) rfl (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).d (m + 1) m w)
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n b) =
      (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).d
        (m + n + 1) (m + n) v := by
  obtain ⟨w', rfl⟩ : ∃ w' : (SingularChainComplex ℚ P).X (m + 1),
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f (m + 1)).hom w' = w :=
    relProj_surjective (TopPair.ofSubset A) (m + 1) w
  obtain ⟨y, hy⟩ : ∃ y : (SingularChainComplex ℚ Q).X n,
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y =
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom b :=
    relProj_surjective (TopPair.ofSubset B) n _
  refine ⟨((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f
    (m + n + 1)).hom (shB P Q (m + 1) n (m + n + 1) (by omega) w' y), ?_⟩
  erw [relProj_d, ← hy]
  erw [relMu_apply]
  rw [triadProj_d]
  rcases n with _ | n'
  · rw [shB_d_succ_zero m (m + 0) rfl rfl]
    rfl
  · obtain ⟨b', hb'⟩ := exists_d_eq_of_cycle (TopPair.ofSubset B) n' y b hy.symm
    rw [shB_d_succ_succ m n' (m + (n' + 1)) rfl rfl rfl]
    erw [← hb']
    rw [map_add, map_zsmul, triadProj_shB_right A B _ w' b', smul_zero, add_zero]
    rfl

/-- A relative cycle times a relative boundary is a triad boundary. -/
lemma relMu_boundary_right {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ)
    (a : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).cycles m)
    (w : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).X (n + 1)) :
    ∃ v : (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).X
        (m + n + 1),
      relMu A B m n (m + n) rfl (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m a)
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).d (n + 1) n w) =
      (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).d
        (m + n + 1) (m + n) v := by
  obtain ⟨w', rfl⟩ : ∃ w' : (SingularChainComplex ℚ Q).X (n + 1),
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f (n + 1)).hom w' = w :=
    relProj_surjective (TopPair.ofSubset B) (n + 1) w
  obtain ⟨x, hx⟩ : ∃ x : (SingularChainComplex ℚ P).X m,
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x =
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom a :=
    relProj_surjective (TopPair.ofSubset A) m _
  refine ⟨(-1 : ℤ) ^ m • ((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q)
    (rightProdSet P B)).f (m + n + 1)).hom (shB P Q m (n + 1) (m + n + 1) (by omega) x w'), ?_⟩
  erw [relProj_d, ← hx]
  erw [relMu_apply]
  rw [map_zsmul, triadProj_d]
  rcases m with _ | m'
  · rw [shB_d_zero_succ n (0 + n) rfl rfl]
    simp
    rfl
  · obtain ⟨a', ha'⟩ := exists_d_eq_of_cycle (TopPair.ofSubset A) m' x a hx.symm
    rw [shB_d_succ_succ m' n (m' + 1 + n) rfl rfl rfl]
    erw [← ha']
    rw [map_add, map_zsmul, triadProj_shB_left A B _ a' w', zero_add, smul_smul, ← mul_pow,
      neg_one_mul, neg_neg, one_pow, one_smul]
    rfl

/-- Upstream's comparison map on a projected ambient chain, on elements. -/
lemma triadToUnion_apply {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (k : ℕ)
    (c : (SingularChainComplex ℚ (P ⊗ Q)).X k) :
    ((triadToUnionRelativeChainMap ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f k).hom
        (((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f k).hom
          c) =
      ((relativeChainProjection ℚ (crossUnionPair A B)).f k).hom c := by
  have h := triadRelativeChainProjection_triadToUnionRelativeChainMap ℚ (P ⊗ Q) (leftProdSet A Q)
    (rightProdSet P B)
  have h' := congrArg (fun φ : SingularChainComplex ℚ (P ⊗ Q) ⟶ _ => (φ.f k).hom c) h
  exact h'

/-- The triad cycle represented by the shuffle product of two relative cycles. -/
def triadCycleMk {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ)
    (x : (SingularChainComplex ℚ P).X m) (y : (SingularChainComplex ℚ Q).X n)
    (zx : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).cycles m)
    (zy : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles n)
    (e : ((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f
      (m + n)).hom (shuffleBilin P Q m n x y) =
        relMu A B m n (m + n) rfl
          ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx)
          ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy)) :
    (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).cycles (m + n) :=
  (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).moduleCatCyclesMk
    (((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f
      (m + n)).hom (shuffleBilin P Q m n x y)) _ rfl
    (by rw [e]; exact relMu_cycle A B m n _ zx zy)

/-- **The shuffle product of relative cycles is a triad cycle.** If `x` is an `m`-chain of `P`
whose class in `C(P, A)` is a cycle and `y` an `n`-chain of `Q` whose class in `C(Q, B)` is a
cycle, the class of their shuffle product in upstream's sum-relative complex
`C(P × Q) / (C(A × Q) + C(P × B))` is a cycle. -/
theorem exists_triadCycle_shuffle {P Q : TopCat.{0}} (A : Set P) (B : Set Q) {m n : ℕ}
    (x : (SingularChainComplex ℚ P).X m) (y : (SingularChainComplex ℚ Q).X n)
    (zx : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).cycles m)
    (hx : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx =
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x)
    (zy : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles n)
    (hy : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy =
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y) :
    ∃ z : (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).cycles
        (m + n),
      ((triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).iCycles
          (m + n)).hom z =
        ((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f
          (m + n)).hom (shuffleBilin P Q m n x y) := by
  have e : ((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f
      (m + n)).hom (shuffleBilin P Q m n x y) =
        relMu A B m n (m + n) rfl
          ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx)
          ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy) := by
    rw [hx, hy]
    exact (relMu_apply A B m n (m + n) rfl x y).symm
  exact ⟨HodgeLadder.Relative.triadCycleMk A B m n x y zx zy e, by
    simp [triadCycleMk]⟩

/-- The shuffle product of relative cycles is a cycle of `C(P × Q, A × Q ∪ P × B)`: the image of
the triad cycle of `exists_triadCycle_shuffle` under upstream's comparison chain map. -/
theorem exists_unionCycle_shuffle {P Q : TopCat.{0}} (A : Set P) (B : Set Q) {m n : ℕ}
    (x : (SingularChainComplex ℚ P).X m) (y : (SingularChainComplex ℚ Q).X n)
    (zx : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).cycles m)
    (hx : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx =
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x)
    (zy : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles n)
    (hy : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy =
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y) :
    ∃ z : ((relativeChainFunctor ℚ).obj (crossUnionPair A B)).cycles (m + n),
      (((relativeChainFunctor ℚ).obj (crossUnionPair A B)).iCycles (m + n)).hom z =
        ((relativeChainProjection ℚ (crossUnionPair A B)).f (m + n)).hom
          (shuffleBilin P Q m n x y) := by
  obtain ⟨z₀, hz₀⟩ := exists_triadCycle_shuffle A B x y zx hx zy hy
  refine ⟨HomologicalComplex.cyclesMap
    (triadToUnionRelativeChainMap ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)) (m + n) z₀, ?_⟩
  erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply]
  erw [hz₀]
  exact triadToUnion_apply A B _ _

/-- The defining property of the cross product into triad relative homology: on the classes of
relative cycles represented by chains `x` and `y`, it is the class of the triad cycle represented
by their shuffle product. -/
def IsRelCross {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ)
    (f : RelativeHomology ℚ (TopPair.ofSubset A) m →ₗ[ℚ]
      RelativeHomology ℚ (TopPair.ofSubset B) n →ₗ[ℚ]
        TriadRelativeHomology ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) (m + n)) : Prop :=
  ∀ (x : (SingularChainComplex ℚ P).X m) (y : (SingularChainComplex ℚ Q).X n)
    (zx : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).cycles m)
    (zy : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles n)
    (z : (triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).cycles
      (m + n)),
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx =
        ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x →
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy =
        ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y →
    ((triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).iCycles
        (m + n)).hom z =
      ((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f
        (m + n)).hom (shuffleBilin P Q m n x y) →
    f ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).homologyπ m).hom zx)
        ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).homologyπ n).hom zy) =
      ((triadRelativeChainComplex ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).homologyπ
        (m + n)).hom z

/-- The cross product on relative homology, built from `relMu` by `homologyBilin`. -/
def relCrossAux {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset A) m →ₗ[ℚ]
      RelativeHomology ℚ (TopPair.ofSubset B) n →ₗ[ℚ]
        TriadRelativeHomology ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) (m + n) :=
  homologyBilin (ChainComplex.prev ℕ m) (ChainComplex.prev ℕ n) (ChainComplex.prev ℕ (m + n)) rfl
    (relMu A B m n (m + n) rfl) (relMu_cycle A B m n _) (relMu_boundary_left A B m n)
    (relMu_boundary_right A B m n)

/-- `relCrossAux` has the defining property of the cross product. -/
lemma isRelCross_relCrossAux {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ) :
    IsRelCross A B m n (relCrossAux A B m n) := by
  intro x y zx zy z hx hy hz
  refine (homologyBilin_homologyπ _ _ _ _ _ _ _ _ zx zy).trans (congrArg _ ?_)
  apply HomologicalComplex.moduleCat_iCycles_injective
  erw [iCycles_cyclesBilin, hx, hy, relMu_apply]
  exact hz.symm

/-- **The shuffle cross product on relative homology exists and is unique**:
there is exactly one bilinear map `H_m(P, A) × H_n(Q, B) → TriadRelativeHomology(P × Q; A × Q,
P × B)` sending the classes of relative cycles to the class of their shuffle product. -/
theorem existsUnique_relCross {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ) :
    ∃! f, IsRelCross A B m n f := by
  refine ⟨relCrossAux A B m n, isRelCross_relCrossAux A B m n, fun g hg => ?_⟩
  refine LinearMap.ext fun α => LinearMap.ext fun β => ?_
  obtain ⟨zx, rfl⟩ :=
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).moduleCat_homologyπ_surjective m α
  obtain ⟨zy, rfl⟩ :=
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).moduleCat_homologyπ_surjective n β
  obtain ⟨x, hx⟩ : ∃ x : (SingularChainComplex ℚ P).X m,
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x =
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx :=
    relProj_surjective (TopPair.ofSubset A) m _
  obtain ⟨y, hy⟩ : ∃ y : (SingularChainComplex ℚ Q).X n,
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y =
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy :=
    relProj_surjective (TopPair.ofSubset B) n _
  obtain ⟨z, hz⟩ := exists_triadCycle_shuffle A B x y zx hx.symm zy hy.symm
  exact (hg x y zx zy z hx.symm hy.symm hz).trans
    (isRelCross_relCrossAux A B m n x y zx zy z hx.symm hy.symm hz).symm

/-- **The relative cross product** `H_m(P, A) × H_n(Q, B) → TriadRelativeHomology(P × Q; A × Q,
P × B)`, the bilinear map characterized by `existsUnique_relCross`. -/
def relCross {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset A) m →ₗ[ℚ]
      RelativeHomology ℚ (TopPair.ofSubset B) n →ₗ[ℚ]
        TriadRelativeHomology ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) (m + n) :=
  (existsUnique_relCross A B m n).exists.choose

/-- **The relative cross product on classes of cycles is the class of the shuffle product**, with
no sign (register row "Relative homology cross product"). -/
theorem relCross_homologyπ {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ) :
    IsRelCross A B m n (relCross A B m n) :=
  (existsUnique_relCross A B m n).exists.choose_spec

/-- **The relative cross product into `H_{m+n}(P × Q, A × Q ∪ P × B)`**: `relCross` followed by
upstream's comparison from the triad complex to the union-relative complex. -/
def relCrossUnion {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset A) m →ₗ[ℚ]
      RelativeHomology ℚ (TopPair.ofSubset B) n →ₗ[ℚ]
        RelativeHomology ℚ (crossUnionPair A B) (m + n) :=
  (relCross A B m n).compr₂
    (triadToUnionRelativeHomologyMap ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) (m + n))

/-- On classes of relative cycles, `relCrossUnion` is the class of the shuffle product in
`C(P × Q, A × Q ∪ P × B)`, with no sign (register row "Relative homology cross product"). -/
theorem relCrossUnion_homologyπ {P Q : TopCat.{0}} (A : Set P) (B : Set Q) {m n : ℕ}
    (x : (SingularChainComplex ℚ P).X m) (y : (SingularChainComplex ℚ Q).X n)
    (zx : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).cycles m)
    (zy : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles n)
    (z : ((relativeChainFunctor ℚ).obj (crossUnionPair A B)).cycles (m + n))
    (hx : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx =
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x)
    (hy : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy =
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y)
    (hz : (((relativeChainFunctor ℚ).obj (crossUnionPair A B)).iCycles (m + n)).hom z =
      ((relativeChainProjection ℚ (crossUnionPair A B)).f (m + n)).hom
        (shuffleBilin P Q m n x y)) :
    relCrossUnion A B m n
        ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).homologyπ m).hom zx)
        ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).homologyπ n).hom zy) =
      (((relativeChainFunctor ℚ).obj (crossUnionPair A B)).homologyπ (m + n)).hom z := by
  obtain ⟨z₀, hz₀⟩ := exists_triadCycle_shuffle A B x y zx hx zy hy
  refine (congrArg (triadToUnionRelativeHomologyMap ℚ (P ⊗ Q) (leftProdSet A Q)
    (rightProdSet P B) (m + n)) (relCross_homologyπ A B m n x y zx zy z₀ hx hy hz₀)).trans ?_
  refine (HomologicalComplex.moduleCat_homologyMap_homologyπ _ _ _).trans (congrArg _ ?_)
  apply HomologicalComplex.moduleCat_iCycles_injective
  erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, hz₀, hz]
  exact triadToUnion_apply A B _ _

/-- A product of maps of pairs `(P, A) → (P', A')`, `(Q, B) → (Q', B')` is a map of pairs
`(P × Q, A × Q ∪ P × B) → (P' × Q', A' × Q' ∪ P' × B')`. -/
lemma tensorHom_mem_union {P P' Q Q' : TopCat.{0}} (f : P ⟶ P') (g : Q ⟶ Q')
    {A : Set P} {A' : Set P'} {B : Set Q} {B' : Set Q'}
    (hf : ∀ a ∈ A, f a ∈ A') (hg : ∀ b ∈ B, g b ∈ B') :
    ∀ z ∈ leftProdSet A Q ∪ rightProdSet P B,
      (f ⊗ₘ g) z ∈ leftProdSet A' Q' ∪ rightProdSet P' B' := by
  rintro z (hz | hz)
  · exact Or.inl (hf _ hz)
  · exact Or.inr (hg _ hz)

/-- **Naturality of the relative cross product** in both pairs, an exact equality with no sign
(register row "Relative homology cross product"). -/
theorem relCrossUnion_naturality {P P' Q Q' : TopCat.{0}} (f : P ⟶ P') (g : Q ⟶ Q')
    {A : Set P} {A' : Set P'} {B : Set Q} {B' : Set Q'}
    (hf : ∀ a ∈ A, f a ∈ A') (hg : ∀ b ∈ B, g b ∈ B') {m n : ℕ}
    (x : RelativeHomology ℚ (TopPair.ofSubset A) m)
    (y : RelativeHomology ℚ (TopPair.ofSubset B) n) :
    relCrossUnion A' B' m n (relativeHomologyMap ℚ m (TopPair.ofSubsetHom f hf) x)
        (relativeHomologyMap ℚ n (TopPair.ofSubsetHom g hg) y) =
      relativeHomologyMap ℚ (m + n)
        (TopPair.ofSubsetHom (f ⊗ₘ g) (tensorHom_mem_union f g hf hg))
        (relCrossUnion A B m n x y) := by
  obtain ⟨zx, rfl⟩ :=
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).moduleCat_homologyπ_surjective m x
  obtain ⟨zy, rfl⟩ :=
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).moduleCat_homologyπ_surjective n y
  obtain ⟨x, hx⟩ : ∃ x : (SingularChainComplex ℚ P).X m,
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x =
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx :=
    relProj_surjective (TopPair.ofSubset A) m _
  obtain ⟨y, hy⟩ : ∃ y : (SingularChainComplex ℚ Q).X n,
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y =
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy :=
    relProj_surjective (TopPair.ofSubset B) n _
  -- the images of the two cycles
  have hx' : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A')).iCycles m).hom
      (HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hf)) m
        zx) =
        ((relativeChainProjection ℚ (TopPair.ofSubset A')).f m).hom
          ((singChainFunctor.map f).f m x) := by
    erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, ← hx]
    exact congrArg (fun φ : SingularChainComplex ℚ P ⟶ _ => (φ.f m).hom x)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) (TopPair.ofSubsetHom f hf))
  have hy' : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B')).iCycles n).hom
      (HomologicalComplex.cyclesMap ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom g hg)) n
        zy) =
        ((relativeChainProjection ℚ (TopPair.ofSubset B')).f n).hom
          ((singChainFunctor.map g).f n y) := by
    erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, ← hy]
    exact congrArg (fun φ : SingularChainComplex ℚ Q ⟶ _ => (φ.f n).hom y)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) (TopPair.ofSubsetHom g hg))
  obtain ⟨z, hz⟩ := exists_unionCycle_shuffle A B x y zx hx.symm zy hy.symm
  obtain ⟨z', hz'⟩ := exists_unionCycle_shuffle A' B' _ _ _ hx' _ hy'
  have lhs := relCrossUnion_homologyπ A' B' _ _ _ _ z' hx' hy' hz'
  have rhs := relCrossUnion_homologyπ A B x y zx zy z hx.symm hy.symm hz
  refine (congrArg₂ (fun a b => relCrossUnion A' B' m n a b)
    (HomologicalComplex.moduleCat_homologyMap_homologyπ _ _ _)
    (HomologicalComplex.moduleCat_homologyMap_homologyπ _ _ _)).trans (lhs.trans ?_)
  refine Eq.trans ?_ (congrArg _ rhs).symm
  refine Eq.trans ?_ (HomologicalComplex.moduleCat_homologyMap_homologyπ _ _ _).symm
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  erw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, hz', hz]
  rw [shuffleBilin_eq_shB, shuffleBilin_eq_shB, shB_naturality]
  exact (congrArg (fun φ : SingularChainComplex ℚ (P ⊗ Q) ⟶ _ =>
    (φ.f (m + n)).hom (shB P Q m n (m + n) rfl x y))
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
        (TopPair.ofSubsetHom (f ⊗ₘ g) (tensorHom_mem_union f g hf hg)))).symm

end HodgeLadder.Relative
