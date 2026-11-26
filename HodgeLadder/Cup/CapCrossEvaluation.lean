module

public import HodgeLadder.Relative.CrossChain
public import Other.AlgebraicTopology.Singular.Excision.Triad
public import LefschetzPort.TauCeti.AlgebraicTopology.SimplicialSet.EilenbergZilber
public import LefschetzPort.TauCeti.Algebra.Homology.Monoidal.Tensor.Cochain

/-!
# Evaluation of upstream's triad cap product on a relative cross product

Rung `cap-cross-evaluation` (front `cup`, sub-rung of `local-class-product`). For pairs `(P, A)`,
`(Q, B)`, classes `φ ∈ H^m(P, A)`, `ψ ∈ H^n(Q, B)`, `x ∈ H_m(P, A)`, `y ∈ H_n(Q, B)` over `ℚ`:

`⟨pr₂^* ψ, pr₁^* φ ⌢ (x × y)⟩ = ⟨φ, x⟩ · ⟨ψ, y⟩`,

exactly, with no sign. Here `x × y` is `HodgeLadder.Relative.relCross` (triad form) or
`HodgeLadder.Relative.relCrossUnion` (union form), the cap is upstream's sum-relative
`triadCapCohomologyLinear` or its excision transport `unionRelativeTriadCapCohomologyLinear`
(library `Other`), the pairing is upstream's `relativeCohomologyEquivDualHomology`, and
`pr₁ : (P × Q, A × Q) ⟶ (P, A)`, `pr₂ : (P × Q, P × B) ⟶ (Q, B)` are the projections.

Signs. The cap is upstream's unsigned chain formula `φ ⌢ σ = φ(front p-face) · back q-face`
(register row "Triad cap product"; the factors `(-1)^p` on the outer terms of
`triadCapShortComplexHomSucc` do not reach homology, since homology is read off the middle term
`triadCapHom`). The evaluation is `⟨[φ], [x]⟩ = φ(x)` (row "Universal-coefficient evaluation").
The cross product is `[x] × [y] = [shuffle(x ⊗ y)]` with the identity shuffle of coefficient `+1`
(rows "Shuffle map", "Relative homology cross product"). Koszul conventions for evaluating a
tensor of cochains on a tensor of chains would insert `(-1)^{|ψ||x|} = (-1)^{nm}`; upstream's
cap and pairing insert nothing, and the identity holds with no sign in every degree.

Unnormalized chains. Upstream's and Tau Ceti's singular chains are unnormalized, so
Alexander–Whitney after shuffle is the identity only up to the natural chain homotopy
`SSet.shuffleAlexanderWhitneyHomotopy`, and a non-identity shuffle simplex contributes
`φ(degenerate) · ψ(degenerate)`, which need not vanish for an arbitrary cocycle. The chain-level
identity is stated for cocycles and relative cycles (`cap_cross_evaluation_cocycle`); for
arbitrary cochains single shuffle terms survive. By naturality in each factor the homotopy
preserves `C(A) ⊗ C(Q) + C(P) ⊗ C(B)`, and this is what makes the relative statement hold.

## Main definitions

* `HodgeLadder.CapCross.prFstPair`, `HodgeLadder.CapCross.prSndPair`: the two projections as maps
  of pairs.
* `HodgeLadder.CapCross.capEval`: `c ↦ β(pr₂_*(pr₁^*α ⌢ c))` on chains of `P × Q`.
* `HodgeLadder.CapCross.tensorEval`: `α ⊗ β` on `C(P) ⊗ C(Q)` (Tau Ceti's `tensorCochain`).

## Main results

* `HodgeLadder.CapCross.cap_cross_evaluation_cocycle`: the identity on cocycle and cycle
  representatives.
* `HodgeLadder.CapCross.alexanderWhitney_tensorEval`: the cap evaluation is `α ⊗ β` after
  Alexander–Whitney.
* `HodgeLadder.CapCross.tensorEval_shuffle`: `(α ⊗ β)(AW(EZ(x ⊗ y))) = α(x) β(y)` for cocycles and
  relative cycles, through Tau Ceti's homotopy `AW ∘ EZ ≃ id` and its naturality.
* `HodgeLadder.CapCross.cap_cross_evaluation_triad`: the identity for the sum-relative triad cap
  and `relCross`, from the cocycle form.
* `HodgeLadder.CapCross.cap_cross_evaluation`: the identity for upstream's union-relative triad
  cap and `relCrossUnion`, for any proof of the excision quasi-isomorphism.
* `HodgeLadder.CapCross.quasiIso_triadToUnion_prod_of_isOpen`: that proof, for open `A`, `B`.
* `HodgeLadder.CapCross.relEval_class`, `HodgeLadder.CapCross.relativeCohomologyMap_class`,
  `HodgeLadder.CapCross.triadCap_class_homologyπ`: evaluation, pullback and the triad cap on
  explicit representatives.

## Implementation notes

Route of `cap_cross_evaluation_cocycle`: the left side is `capEval α β (EZ(x ⊗ y))`, with
`α = φ ∘ relProj_A` and `β = ψ ∘ relProj_B`; `alexanderWhitney_tensorEval` turns it into
`(α ⊗ β)(AW(EZ(x ⊗ y)))`; Tau Ceti's `TopCat.shuffle_alexanderWhitney` and
`SSet.shuffleAlexanderWhitneyHomotopy` give `AW ∘ EZ = d h + h d + id`; `tensorEval_d_eq_zero`
kills `d h` (cocycles), `d_ιTensorObj_mem` with `tensorEval_homotopy_left`, `_right` kill `h d`
(relative cycles, naturality of `h` along the inclusions `A → P`, `B → Q`). Upstream's subspace
chain map is `SSet.chainComplexMap` of the inclusion by `rfl` (`subspaceChainMap_pin`).

The private `rfl` pins below fix the formulas of upstream's `capHom`, `relativeCapLift`,
`triadCapLiftHom` and `unionRelativeTriadCapCohomologyLinear` (through
`triadCapCochainCohomologyLinear`, `relativeCochainCohomologyEquiv` and the inverse of
`isoOfQuasiIsoAt` of the excision comparison) at the pin. Replace them by the shared pins of
`HodgeLadder.Cup.TriadCapPins` (rung `triad-relative-cup-cap`) once that module lands.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomologicalComplex
  AlgebraicTopology AlgebraicTopology.Singular HodgeLadder.Relative
open scoped Simplicial

namespace HodgeLadder.CapCross

/-- The first projection as a map of pairs `(P × Q, A × Q) ⟶ (P, A)`. -/
def prFstPair {P : TopCat.{0}} (A : Set P) (Q : TopCat.{0}) :
    TopPair.ofSubset (X := P ⊗ Q) (leftProdSet A Q) ⟶ TopPair.ofSubset A :=
  TopPair.ofSubsetHom (fst P Q) fun _ h => h

/-- The second projection as a map of pairs `(P × Q, P × B) ⟶ (Q, B)`. -/
def prSndPair (P : TopCat.{0}) {Q : TopCat.{0}} (B : Set Q) :
    TopPair.ofSubset (X := P ⊗ Q) (rightProdSet P B) ⟶ TopPair.ofSubset B :=
  TopPair.ofSubsetHom (snd P Q) fun _ h => h

/-- For open `A ⊆ P` and `B ⊆ Q`, upstream's comparison from the sum-relative triad complex of
`(P × Q; A × Q, P × B)` to the union-relative complex is a quasi-isomorphism (upstream excision,
`triadToUnionRelativeChainMap_quasiIso_of_isOpen`). -/
theorem quasiIso_triadToUnion_prod_of_isOpen {P Q : TopCat.{0}} {A : Set P} {B : Set Q}
    (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (triadToUnionRelativeChainMap ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)) :=
  triadToUnionRelativeChainMap_quasiIso_of_isOpen (P ⊗ Q) _ _
    (hA.preimage (fst P Q).hom.continuous) (hB.preimage (snd P Q).hom.continuous)

/-! ### Pins (replace by `HodgeLadder.Cup.TriadCapPins` once it lands) -/

/-- Pin: upstream's simplicial cap sends a simplex `x` to `φ(front p-face) • back q-face`. -/
private theorem capHom_pin {X : SSet.{0}} (p q : ℕ) (φ : Simplicial.Cochain ℚ X p) :
    Simplicial.capHom ℚ p q φ =
      (X.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) (p + q)).desc
        (Cofan.mk _ fun x ↦ ModuleCat.ofHom <|
          LinearMap.toSpanSingleton ℚ _ <|
            φ (Simplicial.chainOfSimplex ℚ (Simplicial.frontFace X x)) •
              Simplicial.chainOfSimplex ℚ (Simplicial.backFace X x)) :=
  rfl

/-- Pin: the front face is the face on the vertices `0, …, p`. -/
private theorem frontFace_pin {X : SSet.{0}} {p q : ℕ} (x : X _⦋p + q⦌) (i : Fin (p + 1)) :
    Simplicial.frontFace X x = X.map (Simplicial.frontInclusion p q).op x ∧
      ((Simplicial.frontInclusion p q).toOrderHom i).val = i.val :=
  ⟨rfl, rfl⟩

/-- Pin: the back face is the face on the vertices `p, …, p + q`. -/
private theorem backFace_pin {X : SSet.{0}} {p q : ℕ} (x : X _⦋p + q⦌) (i : Fin (q + 1)) :
    Simplicial.backFace X x = X.map (Simplicial.backInclusion p q).op x ∧
      ((Simplicial.backInclusion p q).toOrderHom i).val = p + i.val :=
  ⟨rfl, rfl⟩

/-- Pin: the relative cap lift caps with the cochain pulled back along the projection. -/
private theorem relativeCapLift_pin (X : TopPair.{0}) (p q : ℕ) (φ : RelativeCochain ℚ X p) :
    relativeCapLift ℚ X p q φ =
      Simplicial.cap ℚ p q (((relativeChainProjection ℚ X).f p).hom.dualMap φ) :=
  rfl

/-- Pin: the triad cap lift is the relative cap lift followed by the projection to `C(X, B)`. -/
private theorem triadCapLiftHom_pin (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (φ : RelativeCochain ℚ (TopPair.ofSubset A) p) :
    triadCapLiftHom ℚ X A B p q φ =
      ModuleCat.ofHom (relativeCapLift ℚ (TopPair.ofSubset A) p q φ) ≫
        (relativeChainProjection ℚ (TopPair.ofSubset B)).f q :=
  rfl

/-- Pin: the union-relative triad cap is the sum-relative cap on the cochain-cohomology model,
precomposed with the inverse of the homology isomorphism of the excision comparison. -/
private theorem unionRelativeTriadCap_pin (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (hExc : QuasiIso (triadToUnionRelativeChainMap ℚ X A B))
    (α : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (z : RelativeHomology ℚ (TopPair.ofSubset (A ∪ B)) (p + q)) :
    unionRelativeTriadCapCohomologyLinear ℚ X A B p q hExc α z =
      triadCapCochainCohomologyLinear ℚ X A B p q
        ((relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset A) p).symm α)
        ((haveI := hExc; isoOfQuasiIsoAt (triadToUnionRelativeChainMap ℚ X A B)
          (p + q)).toLinearEquiv.symm z) :=
  rfl

/-! ### Representatives -/

set_option backward.isDefEq.respectTransparency false in
/-- In a short complex of modules, the abstract class `homologyπ z` of a cycle is the explicit
class of its underlying element. -/
theorem homologyπ_eq_class {R : Type} [CommRing R] (S : ShortComplex (ModuleCat.{0} R))
    (z : S.cycles) :
    S.homologyπ z = S.moduleCatHomologyClass
      ⟨S.iCycles z, by
        change S.g.hom (S.iCycles.hom z) = 0
        rw [← ConcreteCategory.comp_apply, S.iCycles_g]; rfl⟩ := by
  have h := S.moduleCatCyclesIso_inv_π_apply (S.moduleCatCyclesIso.hom z)
  rw [Iso.hom_inv_id_apply] at h
  rw [h]
  change S.moduleCatHomologyIso.inv.hom (Submodule.mkQ _ (S.moduleCatCyclesIso.hom z)) =
    S.moduleCatHomologyIso.inv.hom (Submodule.mkQ _ _)
  congr 2

set_option backward.isDefEq.respectTransparency false in
/-- Upstream's evaluation pairing on explicit representatives: the class of a relative dual
cycle `φc` paired with the class of a relative cycle `z` is `φc z`, no sign (register row
"Universal-coefficient evaluation"). -/
theorem relEval_class (X : TopPair.{0}) (n : ℕ)
    (φc : LinearMap.ker ((((relativeChainFunctor ℚ).obj X).sc n).linearDual.g.hom))
    (z : ((relativeChainFunctor ℚ).obj X).cycles n) :
    relativeCohomologyEquivDualHomology ℚ X n
        (relativeCochainCohomologyEquiv ℚ X n
          ((((relativeChainFunctor ℚ).obj X).sc n).linearDual.moduleCatHomologyClass φc))
        ((((relativeChainFunctor ℚ).obj X).homologyπ n).hom z) =
      (show Module.Dual ℚ (((relativeChainFunctor ℚ).obj X).sc n).X₂ from φc.1)
        ((((relativeChainFunctor ℚ).obj X).iCycles n).hom z) := by
  have he : relativeCohomologyEquivDualHomology ℚ X n (relativeCochainCohomologyEquiv ℚ X n
      ((((relativeChainFunctor ℚ).obj X).sc n).linearDual.moduleCatHomologyClass φc)) =
      (((relativeChainFunctor ℚ).obj X).sc n).linearDualHomologyEquiv
        ((((relativeChainFunctor ℚ).obj X).sc n).linearDual.moduleCatHomologyClass φc) := by
    change ((ShortComplex.homologyMapIso (linearDualCochainComplexScIso
        ((relativeChainFunctor ℚ).obj X) n)).toLinearEquiv.trans
      (((relativeChainFunctor ℚ).obj X).sc n).linearDualHomologyEquiv)
        ((ShortComplex.homologyMapIso (linearDualCochainComplexScIso
          ((relativeChainFunctor ℚ).obj X) n)).toLinearEquiv.symm _) = _
    rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [he]
  exact (homologyπ_eq_class (((relativeChainFunctor ℚ).obj X).sc n) z ▸
    ShortComplex.linearDualHomologyEquiv_class_apply_class
      (((relativeChainFunctor ℚ).obj X).sc n) φc _ :)

set_option backward.isDefEq.respectTransparency false in
/-- Upstream's pullback `relativeCohomologyMap` on explicit representatives: the class of `φc`
goes to the class of `φc` composed with the chain map of `f`. -/
theorem relativeCohomologyMap_class {X Y : TopPair.{0}} (f : X ⟶ Y) (n : ℕ)
    (φc : LinearMap.ker ((((relativeChainFunctor ℚ).obj Y).sc n).linearDual.g.hom)) :
    relativeCohomologyMap ℚ n f (relativeCochainCohomologyEquiv ℚ Y n
        ((((relativeChainFunctor ℚ).obj Y).sc n).linearDual.moduleCatHomologyClass φc)) =
      relativeCochainCohomologyEquiv ℚ X n
        ((((relativeChainFunctor ℚ).obj X).sc n).linearDual.moduleCatHomologyClass
          (ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap
            ((shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map
              ((relativeChainFunctor ℚ).map f))) φc)) := by
  rw [← ShortComplex.moduleCatHomologyClass_naturality]
  have hnat := congrArg (ShortComplex.homologyFunctor (ModuleCat ℚ)).map
    (linearDualCochainComplexScIso_naturality ((relativeChainFunctor ℚ).map f) n)
  rw [Functor.map_comp, Functor.map_comp] at hnat
  set eX := (ShortComplex.homologyMapIso
    (linearDualCochainComplexScIso ((relativeChainFunctor ℚ).obj X) n)).toLinearEquiv
  set eY := (ShortComplex.homologyMapIso
    (linearDualCochainComplexScIso ((relativeChainFunctor ℚ).obj Y) n)).toLinearEquiv
  set c := (((relativeChainFunctor ℚ).obj Y).sc n).linearDual.moduleCatHomologyClass φc
  have ha : eX (relativeCohomologyMap ℚ n f (eY.symm c)) =
      (ShortComplex.homologyMap (ShortComplex.linearDualMap
            ((shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map
              ((relativeChainFunctor ℚ).map f)))).hom (eY (eY.symm c)) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hnat) (eY.symm c)
  rw [eY.apply_symm_apply] at ha
  exact (eX.symm_apply_eq.2 ha.symm).symm

set_option backward.isDefEq.respectTransparency false in
/-- Upstream's sum-relative triad cap on explicit representatives: capping the class of a
relative dual cycle `φc` with the class of a triad cycle `z` gives the class of the cycle
`triadCap φc z`, with no sign. -/
theorem triadCap_class_homologyπ (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (φc : LinearMap.ker
      ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).sc p).linearDual.g.hom))
    (z : (triadRelativeChainComplex ℚ X A B).cycles (p + q)) :
    ∃ w : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles q,
      (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles q).hom w =
          triadCap ℚ X A B p q φc.1
            (((triadRelativeChainComplex ℚ X A B).iCycles (p + q)).hom z) ∧
        triadCapCohomologyLinear ℚ X A B p q
            (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset A) p
              (ShortComplex.moduleCatHomologyClass
                (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).sc p).linearDual φc))
            (((triadRelativeChainComplex ℚ X A B).homologyπ (p + q)).hom z) =
          (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).homologyπ q).hom w := by
  have hφ := (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset A) p φc).2
  let F := triadCapShortComplexHom ℚ X A B p q φc.1 hφ
  refine ⟨ShortComplex.cyclesMap F z, ?_, ?_⟩
  · have h := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i F) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      triadCapShortComplexHom_τ₂] at h
    exact h
  · have h := triadCapCohomologyLinear_on_cycle ℚ X A B p q φc
    dsimp only at h
    erw [h]
    exact ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality F) z

/-! ### The chain-level computation -/

/-- Pin: upstream's subspace chain map of `(X, A)` is the chain map of the inclusion `A → X`. -/
private theorem subspaceChainMap_pin (P : TopCat.{0}) (A : Set P) :
    ((chainPairFunctor ℚ).obj (TopPair.ofSubset A)).hom =
      SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset A).map) (ModuleCat.of ℚ ℚ) :=
  rfl

/-- The functional `c ↦ β(pr₂_*(pr₁^*α ⌢ c))` on chains of `P × Q` in degree `m + n`, for an
`m`-cochain `α` of `P` and an `n`-cochain `β` of `Q`, with upstream's simplicial cap. -/
def capEval (P Q : TopCat.{0}) (m n : ℕ) (α : (SingularChainComplex ℚ P).X m →ₗ[ℚ] ℚ)
    (β : (SingularChainComplex ℚ Q).X n →ₗ[ℚ] ℚ) :
    (SingularChainComplex ℚ (P ⊗ Q)).X (m + n) →ₗ[ℚ] ℚ :=
  β ∘ₗ ((SSet.chainComplexMap (TopCat.toSSet.map (snd P Q)) (ModuleCat.of ℚ ℚ)).f n).hom ∘ₗ
    Simplicial.cap ℚ m n (Simplicial.cochainMap ℚ (TopCat.toSSet.map (fst P Q)) m α)

/-- The functional `α ⊗ β` on the tensor product of the chain complexes of `P` and `Q` in degree
`m + n`: Tau Ceti's `tensorCochain`, which is `α ⊗ β` on the summand of bidegree `(m, n)` and zero
on the others, with the coefficient pairing `ℚ ⊗ ℚ → ℚ` the left unitor. -/
abbrev tensorEval (P Q : TopCat.{0}) (m n : ℕ) (α : (SingularChainComplex ℚ P).X m →ₗ[ℚ] ℚ)
    (β : (SingularChainComplex ℚ Q).X n →ₗ[ℚ] ℚ) :
    ((TopCat.toSSet.obj P).chainComplex (𝟙_ (ModuleCat.{0} ℚ)) ⊗
      (TopCat.toSSet.obj Q).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X (m + n) ⟶
      𝟙_ (ModuleCat.{0} ℚ) :=
  TauCeti.ChainComplex.tensorCochain (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
    (M := 𝟙_ (ModuleCat.{0} ℚ)) (N := 𝟙_ (ModuleCat.{0} ℚ))
    (ModuleCat.ofHom α) (ModuleCat.ofHom β) (m + n)

/-- Upstream's front inclusion `[p] → [p + q]` is Mathlib's `subinterval 0 p`. -/
theorem frontInclusion_eq_subinterval (m n : ℕ) (h : 0 + m ≤ m + n) :
    Simplicial.frontInclusion m n = SimplexCategory.subinterval 0 m h := by
  ext i
  simp [Simplicial.frontInclusion, SimplexCategory.subinterval]

/-- Upstream's back inclusion `[q] → [p + q]` is Mathlib's `subinterval p q`. -/
theorem backInclusion_eq_subinterval (m n : ℕ) (h : m + n ≤ m + n) :
    Simplicial.backInclusion m n = SimplexCategory.subinterval m n h := by
  ext i
  simp only [Simplicial.backInclusion_apply]
  change m + i.val = i.val + m
  omega

/-- The summand inclusion of a simplex sends `r` to `r` times the simplex. -/
theorem ιChainComplex_apply {X : SSet.{0}} {k : ℕ} (x : X _⦋k⦌) (r : ℚ) :
    (X.ιChainComplex (R := 𝟙_ (ModuleCat.{0} ℚ)) x).hom r = r • Simplicial.chainOfSimplex ℚ x := by
  rw [Simplicial.chainOfSimplex, ← map_smul]
  congr 1
  exact (mul_one r).symm

/-- **Cap to Alexander–Whitney.** On chains of `P × Q` with coefficients `ℚ ⊗ ℚ`, the
Alexander–Whitney map followed by `α ⊗ β` is the coefficient change followed by
`c ↦ β(pr₂_*(pr₁^*α ⌢ c))`: both send a simplex `s` to `α(front m-face of pr₁ s) · β(back n-face of
pr₂ s)`, with no sign. -/
theorem alexanderWhitney_tensorEval (P Q : TopCat.{0}) (m n : ℕ)
    (α : (SingularChainComplex ℚ P).X m →ₗ[ℚ] ℚ) (β : (SingularChainComplex ℚ Q).X n →ₗ[ℚ] ℚ) :
    (TopCat.alexanderWhitney P Q (𝟙_ (ModuleCat.{0} ℚ)) (𝟙_ (ModuleCat.{0} ℚ))).f (m + n) ≫
        tensorEval P Q m n α β =
      (((SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).map (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom).app
        (TopCat.toSSet.obj (P ⊗ Q))).f (m + n) ≫ ModuleCat.ofHom (capEval P Q m n α β) := by
  refine SSet.chainComplex_hom_ext (fun s => ?_)
  rw [TopCat.ιChainComplex_alexanderWhitney_f_assoc]
  erw [SSet.ιChainComplex_alexanderWhitney_f_assoc]
  rw [SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc, Preadditive.sum_comp,
    Finset.sum_eq_single ⟨m, by omega⟩]
  · set s1 := (TopCat.toSSet.map (fst P Q)).app _ s
    set s2 := (TopCat.toSSet.map (snd P Q)).app _ s
    have key : ∀ (j : ℕ) (hj : j = n) (hj' : m + j ≤ m + n) (hj'' : m + j = m + n),
        ((TopCat.toSSet.obj P).ιChainComplex (R := 𝟙_ (ModuleCat.{0} ℚ))
            ((TopCat.toSSet.obj P).map (SimplexCategory.subinterval 0 m (by omega)).op s1) ⊗ₘ
          (TopCat.toSSet.obj Q).ιChainComplex (R := 𝟙_ (ModuleCat.{0} ℚ))
            ((TopCat.toSSet.obj Q).map (SimplexCategory.subinterval m j hj').op s2)) ≫
          ιTensorObj _ _ m j (m + n) hj'' ≫ tensorEval P Q m n α β =
        (((TopCat.toSSet.obj P).ιChainComplex
              ((TopCat.toSSet.obj P).map (SimplexCategory.subinterval 0 m (by omega)).op s1) ≫
              ModuleCat.ofHom α) ⊗ₘ
            ((TopCat.toSSet.obj Q).ιChainComplex
              ((TopCat.toSSet.obj Q).map (SimplexCategory.subinterval m n (by omega)).op s2) ≫
              ModuleCat.ofHom β)) ≫ (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom := by
      rintro _ rfl _ _
      rw [TauCeti.ChainComplex.ιTensorObj_tensorCochain, tensorHom_comp_tensorHom_assoc]
    simp only [Category.assoc]
    refine (key (m + n - m) (by omega) _ _).trans ?_
    refine ModuleCat.MonoidalCategory.tensor_ext (fun r t => ?_)
    have hL : ∀ (f g : 𝟙_ (ModuleCat.{0} ℚ) ⟶ 𝟙_ (ModuleCat.{0} ℚ)) (r t : ℚ),
        ((f ⊗ₘ g) ≫ (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom).hom (r ⊗ₜ t) = f.hom r * g.hom t := by
      intro f g r t
      rfl
    have hR : ∀ {Y : ModuleCat.{0} ℚ} (f : 𝟙_ (ModuleCat.{0} ℚ) ⟶ Y) (r t : ℚ),
        ((λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom ≫ f).hom (r ⊗ₜ t) = f.hom (r * t) := by
      intro Y f r t
      rfl
    rw [hL, hR]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    change (α _ * β _ : ℚ) = capEval P Q m n α β _
    rw [ιChainComplex_apply, ιChainComplex_apply, ιChainComplex_apply]
    erw [α.map_smul, β.map_smul, (capEval P Q m n α β).map_smul]
    change _ = r * t * β (((SSet.chainComplexMap (TopCat.toSSet.map (snd P Q))
      (ModuleCat.of ℚ ℚ)).f n).hom (Simplicial.cap ℚ m n
        (Simplicial.cochainMap ℚ (TopCat.toSSet.map (fst P Q)) m α)
        (Simplicial.chainOfSimplex ℚ s)))
    rw [Simplicial.cap_chainOfSimplex, map_smul, Simplicial.chainOfSimplex_map]
    erw [β.map_smul]
    erw [Simplicial.cochainMap_apply, Simplicial.chainOfSimplex_map]
    rw [← Simplicial.frontFace_naturality, ← Simplicial.backFace_naturality, Simplicial.frontFace,
      Simplicial.backFace, frontInclusion_eq_subinterval _ _ (by omega),
      backInclusion_eq_subinterval _ _ (by omega), smul_eq_mul, smul_eq_mul, smul_eq_mul]
    simp only [s1, s2]
    ac_rfl
  · rintro i - hi
    rw [Category.assoc, TauCeti.ChainComplex.ιTensorObj_tensorCochain_of_ne_left _ _ _ _
      (fun h ↦ hi (Fin.ext h)), comp_zero]
  · simp


/-- The singular chains of `X`, as simplicial chains of `Sing X` with unit coefficients. -/
abbrev unitChains (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  (TopCat.toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))

/-- Tau Ceti's homotopy `AW ∘ EZ ≃ id` on `Sing P × Sing Q`. -/
abbrev ezHomotopy (P Q : TopCat.{0}) :=
  SSet.shuffleAlexanderWhitneyHomotopy (TopCat.toSSet.obj P) (TopCat.toSSet.obj Q)
    (𝟙_ (ModuleCat.{0} ℚ)) (𝟙_ (ModuleCat.{0} ℚ))

/-- The tensor product of cochains with a zero first factor is zero. -/
theorem tensorCochain_zero_left {A B : ChainComplex (ModuleCat.{0} ℚ) ℕ} [A.HasTensor B]
    {p q : ℕ} (ψ : B.X q ⟶ 𝟙_ (ModuleCat.{0} ℚ)) (k : ℕ) :
    TauCeti.ChainComplex.tensorCochain (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
      (0 : A.X p ⟶ 𝟙_ (ModuleCat.{0} ℚ)) ψ k = 0 := by
  have h := TauCeti.ChainComplex.tensorCochain_smul_left (k := ℚ) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
    (0 : ℚ) (0 : A.X p ⟶ 𝟙_ (ModuleCat.{0} ℚ)) ψ k
  rwa [zero_smul, zero_smul] at h

/-- The tensor product of cochains with a zero second factor is zero. -/
theorem tensorCochain_zero_right {A B : ChainComplex (ModuleCat.{0} ℚ) ℕ} [A.HasTensor B]
    {p q : ℕ} (φ : A.X p ⟶ 𝟙_ (ModuleCat.{0} ℚ)) (k : ℕ) :
    TauCeti.ChainComplex.tensorCochain (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
      φ (0 : B.X q ⟶ 𝟙_ (ModuleCat.{0} ℚ)) k = 0 := by
  have h := TauCeti.ChainComplex.tensorCochain_smul_right (k := ℚ) (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
    (0 : ℚ) φ (0 : B.X q ⟶ 𝟙_ (ModuleCat.{0} ℚ)) k
  rwa [zero_smul, zero_smul] at h

/-- The homotopy `AW ∘ EZ ≃ id` followed by `α ⊗ β` vanishes on the image of `C(A) ⊗ C(Q)` when `α`
vanishes on `C(A)`: Tau Ceti's naturality of the homotopy along `A → P`. -/
theorem tensorEval_homotopy_left (P Q : TopCat.{0}) {A' : TopCat.{0}} (iA : A' ⟶ P) (m n : ℕ)
    (α : (SingularChainComplex ℚ P).X m →ₗ[ℚ] ℚ) (β : (SingularChainComplex ℚ Q).X n →ₗ[ℚ] ℚ)
    (hαA : ∀ a, α ((SSet.chainComplexMap (TopCat.toSSet.map iA) (𝟙_ (ModuleCat.{0} ℚ))).f m a) = 0)
    (i : ℕ) (w : (unitChains A' ⊗ unitChains Q).X i) :
    (tensorEval P Q m n α β).hom (((ezHomotopy P Q).hom i (m + n)).hom
      ((SSet.chainComplexMap (TopCat.toSSet.map iA) (𝟙_ (ModuleCat.{0} ℚ)) ⊗ₘ
        SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj Q)) (𝟙_ (ModuleCat.{0} ℚ))).f i w)) = 0 := by
  have h1 := SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality (R := 𝟙_ (ModuleCat.{0} ℚ))
    (S := 𝟙_ (ModuleCat.{0} ℚ)) (TopCat.toSSet.map iA) (𝟙 (TopCat.toSSet.obj Q)) i (m + n)
  have h0 : (SSet.chainComplexMap (TopCat.toSSet.map iA) (𝟙_ (ModuleCat.{0} ℚ))).f m ≫
      ModuleCat.ofHom α = 0 := by
    ext a
    exact hαA a
  have h2 : (SSet.chainComplexMap (TopCat.toSSet.map iA) (𝟙_ (ModuleCat.{0} ℚ)) ⊗ₘ
        SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj Q)) (𝟙_ (ModuleCat.{0} ℚ))).f (m + n) ≫
      tensorEval P Q m n α β = 0 := by
    rw [tensorEval]
    erw [TauCeti.ChainComplex.tensorHom_f_comp_tensorCochain]
    rw [h0]
    exact tensorCochain_zero_left _ _
  have h3 := congrArg (fun f => f.hom w) (congrArg (· ≫ tensorEval P Q m n α β) h1)
  simp only [Category.assoc, h2, comp_zero] at h3
  exact h3


/-- The homotopy `AW ∘ EZ ≃ id` followed by `α ⊗ β` vanishes on the image of `C(P) ⊗ C(B)` when `β`
vanishes on `C(B)`. -/
theorem tensorEval_homotopy_right (P Q : TopCat.{0}) {B' : TopCat.{0}} (iB : B' ⟶ Q) (m n : ℕ)
    (α : (SingularChainComplex ℚ P).X m →ₗ[ℚ] ℚ) (β : (SingularChainComplex ℚ Q).X n →ₗ[ℚ] ℚ)
    (hβB : ∀ b, β ((SSet.chainComplexMap (TopCat.toSSet.map iB) (𝟙_ (ModuleCat.{0} ℚ))).f n b) = 0)
    (i : ℕ) (w : (unitChains P ⊗ unitChains B').X i) :
    (tensorEval P Q m n α β).hom (((ezHomotopy P Q).hom i (m + n)).hom
      ((SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj P)) (𝟙_ (ModuleCat.{0} ℚ)) ⊗ₘ
        SSet.chainComplexMap (TopCat.toSSet.map iB) (𝟙_ (ModuleCat.{0} ℚ))).f i w)) = 0 := by
  have h1 := SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality (R := 𝟙_ (ModuleCat.{0} ℚ))
    (S := 𝟙_ (ModuleCat.{0} ℚ)) (𝟙 (TopCat.toSSet.obj P)) (TopCat.toSSet.map iB) i (m + n)
  have h0 : (SSet.chainComplexMap (TopCat.toSSet.map iB) (𝟙_ (ModuleCat.{0} ℚ))).f n ≫
      ModuleCat.ofHom β = 0 := by
    ext b
    exact hβB b
  have h2 : (SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj P)) (𝟙_ (ModuleCat.{0} ℚ)) ⊗ₘ
        SSet.chainComplexMap (TopCat.toSSet.map iB) (𝟙_ (ModuleCat.{0} ℚ))).f (m + n) ≫
      tensorEval P Q m n α β = 0 := by
    rw [tensorEval]
    erw [TauCeti.ChainComplex.tensorHom_f_comp_tensorCochain]
    rw [h0]
    exact tensorCochain_zero_right _ _
  have h3 := congrArg (fun f => f.hom w) (congrArg (· ≫ tensorEval P Q m n α β) h1)
  simp only [Category.assoc, h2, comp_zero] at h3
  exact h3

/-- `α ⊗ β` vanishes on boundaries when `α` and `β` are cocycles (Tau Ceti's Leibniz rule for
`tensorCochain`). -/
theorem tensorEval_d_eq_zero (P Q : TopCat.{0}) (m n : ℕ)
    (α : (SingularChainComplex ℚ P).X m →ₗ[ℚ] ℚ) (β : (SingularChainComplex ℚ Q).X n →ₗ[ℚ] ℚ)
    (hα : ∀ c, α ((SingularChainComplex ℚ P).d (m + 1) m c) = 0)
    (hβ : ∀ c, β ((SingularChainComplex ℚ Q).d (n + 1) n c) = 0) :
    (unitChains P ⊗ unitChains Q).d (m + n + 1) (m + n) ≫ tensorEval P Q m n α β = 0 := by
  rw [tensorEval]
  erw [TauCeti.ChainComplex.d_comp_tensorCochain]
  have h0 : (unitChains P).d (m + 1) m ≫ ModuleCat.ofHom α = 0 := by
    ext c
    exact hα c
  have h0' : (unitChains Q).d (n + 1) n ≫ ModuleCat.ofHom β = 0 := by
    ext c
    exact hβ c
  rw [h0, h0', tensorCochain_zero_left, tensorCochain_zero_right, smul_zero, add_zero]


/-- A tensor product of chain maps on a homogeneous tensor `u ⊗ v`. -/
theorem tensorHom_ι_apply {K₁ K₂ L₁ L₂ : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f₁ : K₁ ⟶ L₁)
    (f₂ : K₂ ⟶ L₂) (i₁ i₂ j : ℕ) (h : i₁ + i₂ = j) (u : K₁.X i₁) (v : K₂.X i₂) :
    (f₁ ⊗ₘ f₂).f j ((ιTensorObj K₁ K₂ i₁ i₂ j h).hom (u ⊗ₜ v)) =
      (ιTensorObj L₁ L₂ i₁ i₂ j h).hom (f₁.f i₁ u ⊗ₜ f₂.f i₂ v) := by
  have := congrArg (fun f => f.hom (u ⊗ₜ v)) (HomologicalComplex.ι_tensorHom_f f₁ f₂ i₁ i₂ j h)
  exact this

/-- The identity of a simplicial set induces the identity on chains. -/
theorem chainComplexMap_id_apply (X : SSet.{0}) (k : ℕ)
    (u : (X.chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X k) :
    (SSet.chainComplexMap (𝟙 X) (𝟙_ (ModuleCat.{0} ℚ))).f k u = u := by
  rw [SSet.chainComplexMap_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- If `d x` comes from `C(A)` and `d y` from `C(B)`, the boundary of `x ⊗ y` lies in the image of
`C(A) ⊗ C(Q)` plus the image of `C(P) ⊗ C(B)` (Leibniz rule, all four degree cases). -/
theorem d_ιTensorObj_mem (P Q : TopCat.{0}) {A' B' : TopCat.{0}} (iA : A' ⟶ P) (iB : B' ⟶ Q)
    {m n k' : ℕ} (hk : m + n = k' + 1) (x : (unitChains P).X m) (y : (unitChains Q).X n)
    (hx : ∀ j, ∃ a, (SSet.chainComplexMap (TopCat.toSSet.map iA) (𝟙_ (ModuleCat.{0} ℚ))).f j a =
      (unitChains P).d m j x)
    (hy : ∀ j, ∃ b, (SSet.chainComplexMap (TopCat.toSSet.map iB) (𝟙_ (ModuleCat.{0} ℚ))).f j b =
      (unitChains Q).d n j y) :
    ∃ w₁ w₂, (unitChains P ⊗ unitChains Q).d (m + n) k'
        ((ιTensorObj (unitChains P) (unitChains Q) m n (m + n) rfl).hom (x ⊗ₜ y)) =
      (SSet.chainComplexMap (TopCat.toSSet.map iA) (𝟙_ (ModuleCat.{0} ℚ)) ⊗ₘ
        SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj Q)) (𝟙_ (ModuleCat.{0} ℚ))).f k' w₁ +
      (SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj P)) (𝟙_ (ModuleCat.{0} ℚ)) ⊗ₘ
        SSet.chainComplexMap (TopCat.toSSet.map iB) (𝟙_ (ModuleCat.{0} ℚ))).f k' w₂ := by
  rcases m with _ | m' <;> rcases n with _ | n'
  · omega
  · obtain ⟨b, hb⟩ := hy n'
    refine ⟨0, (ComplexShape.down ℕ).ε 0 •
      (ιTensorObj (unitChains P) (unitChains B') 0 n' k' (by omega)).hom
      (x ⊗ₜ b), ?_⟩
    have e := congrArg (fun f => f.hom (x ⊗ₜ y))
      (HomologicalComplex.ιTensorObj_d_of_not_rel_left (unitChains P) (unitChains Q)
        (rfl : 0 + (n' + 1) = _)
        (q' := n') (j' := k') (by simp) (by simp) (by omega))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    erw [e]
    rw [map_zero]
    refine Eq.trans ?_ (zero_add _).symm
    rw [Units.smul_def, Units.smul_def, map_zsmul, tensorHom_ι_apply,
      chainComplexMap_id_apply, hb]
    rfl
  · obtain ⟨a, ha⟩ := hx m'
    refine ⟨(ιTensorObj (unitChains A') (unitChains Q) m' 0 k' (by omega)).hom (a ⊗ₜ y), 0, ?_⟩
    have e := congrArg (fun f => f.hom (x ⊗ₜ y))
      (HomologicalComplex.ιTensorObj_d_of_not_rel_right (unitChains P) (unitChains Q)
        (rfl : (m' + 1) + 0 = _)
        (p' := m') (j' := k') (by simp) (by simp) (by omega))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    erw [e]
    rw [map_zero]
    refine Eq.trans ?_ (add_zero _).symm
    rw [tensorHom_ι_apply, chainComplexMap_id_apply, ha]
    rfl
  · obtain ⟨a, ha⟩ := hx m'
    obtain ⟨b, hb⟩ := hy n'
    refine ⟨(ιTensorObj (unitChains A') (unitChains Q) m' (n' + 1) k' (by omega)).hom (a ⊗ₜ y),
      (ComplexShape.down ℕ).ε (m' + 1) •
        (ιTensorObj (unitChains P) (unitChains B') (m' + 1) n' k' (by omega)).hom
        (x ⊗ₜ b), ?_⟩
    have e := congrArg (fun f => f.hom (x ⊗ₜ y))
      (HomologicalComplex.ιTensorObj_d_of_rel (unitChains P) (unitChains Q)
        (rfl : (m' + 1) + (n' + 1) = _)
        (p' := m') (q' := n') (j' := k') (by simp) (by simp) (by omega))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    erw [e]
    rw [Units.smul_def, Units.smul_def, map_zsmul, tensorHom_ι_apply, tensorHom_ι_apply,
      chainComplexMap_id_apply, chainComplexMap_id_apply, ha, hb]
    rfl


set_option backward.isDefEq.respectTransparency false in
/-- **The homotopy step.** For cocycles `α` vanishing on `C(A)`, `β` vanishing on `C(B)`, and chains
`x`, `y` whose boundaries come from `C(A)`, `C(B)`: `(α ⊗ β)(AW(EZ(x ⊗ y))) = α(x) · β(y)`. Tau
Ceti's `SSet.shuffleAlexanderWhitneyHomotopy` gives `AW ∘ EZ = id + d h + h d`; the `d h` term dies because
`α ⊗ β` kills boundaries, the `h d` term by naturality of `h` along `A → P` and `B → Q`. -/
theorem tensorEval_shuffle (P Q : TopCat.{0}) {A' B' : TopCat.{0}} (iA : A' ⟶ P) (iB : B' ⟶ Q)
    (m n : ℕ) (α : (SingularChainComplex ℚ P).X m →ₗ[ℚ] ℚ)
    (β : (SingularChainComplex ℚ Q).X n →ₗ[ℚ] ℚ)
    (hα : ∀ c, α ((SingularChainComplex ℚ P).d (m + 1) m c) = 0)
    (hβ : ∀ c, β ((SingularChainComplex ℚ Q).d (n + 1) n c) = 0)
    (hαA : ∀ a, α ((SSet.chainComplexMap (TopCat.toSSet.map iA) (𝟙_ (ModuleCat.{0} ℚ))).f m a) = 0)
    (hβB : ∀ b, β ((SSet.chainComplexMap (TopCat.toSSet.map iB) (𝟙_ (ModuleCat.{0} ℚ))).f n b) = 0)
    (x : (unitChains P).X m) (y : (unitChains Q).X n)
    (hx : ∀ j, ∃ a, (SSet.chainComplexMap (TopCat.toSSet.map iA) (𝟙_ (ModuleCat.{0} ℚ))).f j a =
      (unitChains P).d m j x)
    (hy : ∀ j, ∃ b, (SSet.chainComplexMap (TopCat.toSSet.map iB) (𝟙_ (ModuleCat.{0} ℚ))).f j b =
      (unitChains Q).d n j y) :
    (tensorEval P Q m n α β).hom
        (((TopCat.shuffle P Q (𝟙_ (ModuleCat.{0} ℚ)) (𝟙_ (ModuleCat.{0} ℚ)) ≫
          TopCat.alexanderWhitney P Q (𝟙_ (ModuleCat.{0} ℚ)) (𝟙_ (ModuleCat.{0} ℚ))).f
            (m + n)).hom
              ((ιTensorObj (unitChains P) (unitChains Q) m n (m + n) rfl).hom (x ⊗ₜ y))) =
      α x * β y := by
  rw [TopCat.shuffle_alexanderWhitney, (ezHomotopy P Q).comm (m + n)]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, map_add]
  have hprev : (tensorEval P Q m n α β).hom ((prevD (m + n) (ezHomotopy P Q).hom).hom
      ((ιTensorObj (unitChains P) (unitChains Q) m n (m + n) rfl).hom (x ⊗ₜ y))) = 0 := by
    rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel (m + n + 1) (m + n) by simp)]
    have h := congrArg (fun f => f.hom (((ezHomotopy P Q).hom (m + n) (m + n + 1)).hom
      ((ιTensorObj (unitChains P) (unitChains Q) m n (m + n) rfl).hom (x ⊗ₜ y))))
      (tensorEval_d_eq_zero P Q m n α β hα hβ)
    exact h
  have hnext : (tensorEval P Q m n α β).hom ((dNext (m + n) (ezHomotopy P Q).hom).hom
      ((ιTensorObj (unitChains P) (unitChains Q) m n (m + n) rfl).hom (x ⊗ₜ y))) = 0 := by
    rcases Nat.eq_zero_or_eq_succ_pred (m + n) with h0 | hk
    · rw [dNext_eq_zero _ _ (by rw [h0]; simp), ModuleCat.hom_zero, LinearMap.zero_apply,
        map_zero]
    · rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (m + n) (m + n).pred by simp; omega)]
      obtain ⟨w₁, w₂, hw⟩ := d_ιTensorObj_mem P Q iA iB hk x y hx hy
      change (tensorEval P Q m n α β).hom (((ezHomotopy P Q).hom _ (m + n)).hom
        ((unitChains P ⊗ unitChains Q).d (m + n) (m + n).pred
          ((ιTensorObj (unitChains P) (unitChains Q) m n (m + n) rfl).hom (x ⊗ₜ y)))) = 0
      rw [hw, map_add, map_add, tensorEval_homotopy_left P Q iA m n α β hαA,
        tensorEval_homotopy_right P Q iB m n α β hβB, add_zero]
  rw [hprev, hnext, zero_add, zero_add]
  have h := congrArg (fun f => f.hom (x ⊗ₜ y))
    (TauCeti.ChainComplex.ιTensorObj_tensorCochain (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom
      (ModuleCat.ofHom α) (ModuleCat.ofHom β) (m + n) rfl)
  exact h


/-- Upstream's relative chain projection is natural, on elements. -/
theorem relProj_map_apply {X Y : TopPair.{0}} (f : X ⟶ Y) (k : ℕ)
    (c : (SingularChainComplex ℚ X.fst).X k) :
    (((relativeChainFunctor ℚ).map f).f k).hom (((relativeChainProjection ℚ X).f k).hom c) =
      ((relativeChainProjection ℚ Y).f k).hom ((singChainFunctor.map (TopPair.Hom.fst f)).f k c) :=
  congrArg (fun g => g.hom c)
    (congrArg (fun g => HomologicalComplex.Hom.f g k)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f))

/-! ### The evaluation identity -/

set_option backward.isDefEq.respectTransparency false in
/-- **Cap–cross evaluation on representatives.** For a relative cocycle `φ` of `(P, A)` in
degree `m`, a relative cocycle `ψ` of `(Q, B)` in degree `n`, and chains `x`, `y` whose
projections are relative cycles,

`(pr₂^* ψ)(triadCap (pr₁^* φ) [shuffle(x ⊗ y)]) = φ(x) · ψ(y)`,

with no sign. The cocycle and cycle hypotheses are needed: singular chains are unnormalized, so
Alexander–Whitney after shuffle is the identity only up to the natural homotopy
`SSet.shuffleAlexanderWhitneyHomotopy`, and the non-identity shuffle simplices contribute
`φ(degenerate) · ψ(degenerate)`; those terms cancel on cocycles and relative cycles because the
homotopy, natural in each factor, preserves `C(A) ⊗ C(Q) + C(P) ⊗ C(B)`. Register rows "Triad cap
product", "Shuffle map", "Universal-coefficient evaluation". -/
theorem cap_cross_evaluation_cocycle {P Q : TopCat.{0}} (A : Set P) (B : Set Q) {m n : ℕ}
    (φ : RelativeCochain ℚ (TopPair.ofSubset A) m)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset A) m φ = 0)
    (ψ : RelativeCochain ℚ (TopPair.ofSubset B) n)
    (hψ : relativeCoboundary ℚ (TopPair.ofSubset B) n ψ = 0)
    (x : (SingularChainComplex ℚ P).X m) (y : (SingularChainComplex ℚ Q).X n)
    (zx : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).cycles m)
    (hx : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx =
      ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x)
    (zy : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).cycles n)
    (hy : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy =
      ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y) :
    (((relativeChainFunctor ℚ).map (prSndPair P B)).f n).hom.dualMap ψ
        (triadCap ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) m n
          ((((relativeChainFunctor ℚ).map (prFstPair A Q)).f m).hom.dualMap φ)
          (((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f
            (m + n)).hom (shuffleBilin P Q m n x y))) =
      φ (((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom x) *
        ψ (((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom y) := by
  set α : (SingularChainComplex ℚ P).X m →ₗ[ℚ] ℚ :=
    φ ∘ₗ ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom with hαdef
  set β : (SingularChainComplex ℚ Q).X n →ₗ[ℚ] ℚ :=
    ψ ∘ₗ ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom with hβdef
  have hL : (((relativeChainFunctor ℚ).map (prSndPair P B)).f n).hom.dualMap ψ
        (triadCap ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) m n
          ((((relativeChainFunctor ℚ).map (prFstPair A Q)).f m).hom.dualMap φ)
          (((triadRelativeChainProjection ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)).f
            (m + n)).hom (shuffleBilin P Q m n x y))) =
      capEval P Q m n α β (shuffleBilin P Q m n x y) := by
    rw [triadCap_projection_apply]
    have hcoch : relativeCochainToAbsolute ℚ _ m
        ((((relativeChainFunctor ℚ).map (prFstPair A Q)).f m).hom.dualMap φ) =
        Simplicial.cochainMap ℚ (TopCat.toSSet.map (fst P Q)) m α := by
      ext c
      exact congrArg φ (relProj_map_apply (prFstPair A Q) m c)
    change ψ ((((relativeChainFunctor ℚ).map (prSndPair P B)).f n).hom
      (((relativeChainProjection ℚ _).f n).hom (Simplicial.cap ℚ m n
        (relativeCochainToAbsolute ℚ _ m
          ((((relativeChainFunctor ℚ).map (prFstPair A Q)).f m).hom.dualMap φ))
        (shuffleBilin P Q m n x y)))) = _
    rw [relProj_map_apply, hcoch]
    rfl
  rw [hL]
  have e1 := congrArg (fun f => f.hom (((TopCat.shuffle P Q (𝟙_ (ModuleCat.{0} ℚ))
      (𝟙_ (ModuleCat.{0} ℚ))).f (m + n)).hom
        ((ιTensorObj (unitChains P) (unitChains Q) m n (m + n) rfl).hom (x ⊗ₜ y))))
    (alexanderWhitney_tensorEval P Q m n α β)
  change (((((SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).map (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom).app
        (TopCat.toSSet.obj (P ⊗ Q))).f (m + n) ≫ ModuleCat.ofHom (capEval P Q m n α β)).hom
      (((TopCat.shuffle P Q (𝟙_ (ModuleCat.{0} ℚ)) (𝟙_ (ModuleCat.{0} ℚ))).f (m + n)).hom
        ((ιTensorObj (unitChains P) (unitChains Q) m n (m + n) rfl).hom (x ⊗ₜ y)))) = _
  have hα : ∀ c, α ((SingularChainComplex ℚ P).d (m + 1) m c) = 0 := by
    intro c
    change φ (((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom
      ((SingularChainComplex ℚ P).d (m + 1) m c)) = 0
    exact (congrArg φ (relProj_d (TopPair.ofSubset A) (m + 1) m c)).symm.trans
      (LinearMap.congr_fun hφ (((relativeChainProjection ℚ (TopPair.ofSubset A)).f (m + 1)).hom c))
  have hβ : ∀ c, β ((SingularChainComplex ℚ Q).d (n + 1) n c) = 0 := by
    intro c
    change ψ (((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom
      ((SingularChainComplex ℚ Q).d (n + 1) n c)) = 0
    exact (congrArg ψ (relProj_d (TopPair.ofSubset B) (n + 1) n c)).symm.trans
      (LinearMap.congr_fun hψ (((relativeChainProjection ℚ (TopPair.ofSubset B)).f (n + 1)).hom c))
  have hαA : ∀ a, α ((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset A).map)
      (𝟙_ (ModuleCat.{0} ℚ))).f m a) = 0 := by
    intro a
    have w : ((chainPairFunctor ℚ).obj (TopPair.ofSubset A)).hom.f m ≫
        (relativeChainProjection ℚ (TopPair.ofSubset A)).f m = 0 :=
      congrArg (fun q => q.f m) (subspaceChainMap_relativeChainProjection ℚ (TopPair.ofSubset A))
    have h2 : ((relativeChainProjection ℚ (TopPair.ofSubset A)).f m).hom
        ((((chainPairFunctor ℚ).obj (TopPair.ofSubset A)).hom.f m).hom a) = 0 :=
      ConcreteCategory.congr_hom w a
    exact (congrArg φ h2).trans (map_zero φ)
  have hβB : ∀ b, β ((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset B).map)
      (𝟙_ (ModuleCat.{0} ℚ))).f n b) = 0 := by
    intro b
    have w : ((chainPairFunctor ℚ).obj (TopPair.ofSubset B)).hom.f n ≫
        (relativeChainProjection ℚ (TopPair.ofSubset B)).f n = 0 :=
      congrArg (fun q => q.f n) (subspaceChainMap_relativeChainProjection ℚ (TopPair.ofSubset B))
    have h2 : ((relativeChainProjection ℚ (TopPair.ofSubset B)).f n).hom
        ((((chainPairFunctor ℚ).obj (TopPair.ofSubset B)).hom.f n).hom b) = 0 :=
      ConcreteCategory.congr_hom w b
    exact (congrArg ψ h2).trans (map_zero ψ)
  refine e1.symm.trans ?_
  exact tensorEval_shuffle P Q (TopPair.ofSubset A).map (TopPair.ofSubset B).map m n α β hα hβ
    hαA hβB x y (fun j => exists_d_eq_of_cycle (TopPair.ofSubset A) j x zx hx)
    (fun j => exists_d_eq_of_cycle (TopPair.ofSubset B) j y zy hy)

set_option backward.isDefEq.respectTransparency false in
/-- **Cap–cross evaluation, triad form.** For `φ ∈ H^m(P, A)`, `ψ ∈ H^n(Q, B)`,
`x ∈ H_m(P, A)`, `y ∈ H_n(Q, B)` over `ℚ` and any subsets `A`, `B`:

`⟨pr₂^* ψ, pr₁^* φ ⌢ (x × y)⟩ = ⟨φ, x⟩ · ⟨ψ, y⟩`,

with upstream's sum-relative triad cap `triadCapCohomologyLinear` on
`TriadRelativeHomology(P × Q; A × Q, P × B)` and `x × y = relCross A B m n x y`. Exact, no sign
in any degree (a Koszul convention would give `(-1)^{nm}`). Register rows "Triad cap product",
"Relative homology cross product", "Universal-coefficient evaluation". -/
theorem cap_cross_evaluation_triad {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ)
    (φ : RelativeCohomology ℚ (TopPair.ofSubset A) m)
    (ψ : RelativeCohomology ℚ (TopPair.ofSubset B) n)
    (x : RelativeHomology ℚ (TopPair.ofSubset A) m)
    (y : RelativeHomology ℚ (TopPair.ofSubset B) n) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (X := P ⊗ Q) (rightProdSet P B)) n
        (relativeCohomologyMap ℚ n (prSndPair P B) ψ)
        (triadCapCohomologyLinear ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B) m n
          (relativeCohomologyMap ℚ m (prFstPair A Q) φ) (relCross A B m n x y)) =
      relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset A) m φ x *
        relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) n ψ y := by
  obtain ⟨φc, rfl⟩ : ∃ φc, relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset A) m
      ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).sc m).linearDual.moduleCatHomologyClass
        φc) = φ :=
    ((relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset A) m).surjective.comp
      (ShortComplex.moduleCatHomologyClass_surjective _)) φ
  obtain ⟨ψc, rfl⟩ : ∃ ψc, relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset B) n
      ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).sc n).linearDual.moduleCatHomologyClass
        ψc) = ψ :=
    ((relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset B) n).surjective.comp
      (ShortComplex.moduleCatHomologyClass_surjective _)) ψ
  obtain ⟨zx, rfl⟩ :=
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).moduleCat_homologyπ_surjective m x
  obtain ⟨zy, rfl⟩ :=
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).moduleCat_homologyπ_surjective n y
  obtain ⟨x, hx⟩ := relProj_surjective (TopPair.ofSubset A) m
    ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset A)).iCycles m).hom zx)
  obtain ⟨y, hy⟩ := relProj_surjective (TopPair.ofSubset B) n
    ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).iCycles n).hom zy)
  obtain ⟨z, hz⟩ := exists_triadCycle_shuffle A B x y zx hx.symm zy hy.symm
  rw [relCross_homologyπ A B m n x y zx zy z hx.symm hy.symm hz,
    relativeCohomologyMap_class, relativeCohomologyMap_class]
  obtain ⟨w, hw, hcap⟩ := triadCap_class_homologyπ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)
    m n _ z
  rw [hcap, relEval_class, relEval_class, relEval_class, hw, hz, ← hx, ← hy]
  exact cap_cross_evaluation_cocycle A B _
    (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset A) m φc).2 _
    (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset B) n ψc).2 x y zx hx.symm zy hy.symm

/-- **Cap–cross evaluation, union form** (rung `cap-cross-evaluation`). For `φ ∈ H^m(P, A)`,
`ψ ∈ H^n(Q, B)`, `x ∈ H_m(P, A)`, `y ∈ H_n(Q, B)` over `ℚ`, whenever upstream's excision
comparison for `(P × Q; A × Q, P × B)` is a quasi-isomorphism (for open `A`, `B`:
`quasiIso_triadToUnion_prod_of_isOpen`):

`⟨pr₂^* ψ, pr₁^* φ ⌢ (x × y)⟩ = ⟨φ, x⟩ · ⟨ψ, y⟩`,

with upstream's customary triad cap `unionRelativeTriadCapCohomologyLinear`
`H^m(P × Q, A × Q) × H_{m+n}(P × Q, A × Q ∪ P × B) → H_n(P × Q, P × B)` and
`x × y = relCrossUnion A B m n x y`. Exact, no sign in any degree; the excision proof `hExc` is a
proposition, so the statement does not depend on it. Register rows "Triad cap product",
"Relative homology cross product", "Universal-coefficient evaluation". -/
theorem cap_cross_evaluation {P Q : TopCat.{0}} (A : Set P) (B : Set Q) (m n : ℕ)
    (hExc : QuasiIso
      (triadToUnionRelativeChainMap ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)))
    (φ : RelativeCohomology ℚ (TopPair.ofSubset A) m)
    (ψ : RelativeCohomology ℚ (TopPair.ofSubset B) n)
    (x : RelativeHomology ℚ (TopPair.ofSubset A) m)
    (y : RelativeHomology ℚ (TopPair.ofSubset B) n) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (X := P ⊗ Q) (rightProdSet P B)) n
        (relativeCohomologyMap ℚ n (prSndPair P B) ψ)
        (unionRelativeTriadCapCohomologyLinear ℚ (P ⊗ Q) (leftProdSet A Q) (rightProdSet P B)
          m n hExc (relativeCohomologyMap ℚ m (prFstPair A Q) φ) (relCrossUnion A B m n x y)) =
      relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset A) m φ x *
        relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) n ψ y := by
  rw [show relCrossUnion A B m n x y = triadToUnionRelativeHomologyMap ℚ (P ⊗ Q)
      (leftProdSet A Q) (rightProdSet P B) (m + n) (relCross A B m n x y) from rfl,
    unionRelativeTriadCapCohomologyLinear_on_comparison]
  exact cap_cross_evaluation_triad A B m n φ ψ x y

end HodgeLadder.CapCross
