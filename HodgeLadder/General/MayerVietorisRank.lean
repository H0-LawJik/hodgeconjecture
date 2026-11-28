module

public import Other.AlgebraicTopology.Singular.MayerVietoris
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Dimension counts from the singular Mayer–Vietoris sequence

Rank consequences of upstream's singular Mayer–Vietoris sequence
(`Other.AlgebraicTopology.Singular.MayerVietoris`) for rational singular homology of a
topological space `X` with an open cover `X = U ∪ V`. Finite-dimensionality enters as explicit
instance hypotheses. `Module.finrank` is `0` on an infinite-dimensional space, so each upper
bound on a `finrank` of `H_k(X)` has a companion finite-dimensionality theorem for the same
space: `finiteDimensional_homology_succ` for `finrank_homology_succ_add_le`, and
`finiteDimensional_homology_of_disjoint` for `finrank_homology_le_of_disjoint` and
`finrank_homology_eq_of_disjoint`. The exact count carries finite-dimensionality in its
conclusion.

Upstream's overlap map is `(i, -j)`; under `sumHomologyEquiv` it is the pair
`(i_*, -j_*)` exactly (`sumHomologyEquiv_comp_overlap`), and its sum map is
`(ι_U)_* + (ι_V)_*` with no sign (`sum_comp_sumHomologyEquiv_symm`). Only ranks of these maps
enter the counts below.

## Main definitions

* `HodgeLadder.MayerVietoris.sumHomologyEquiv`: the middle term as `H_n(U) × H_n(V)`.
* `HodgeLadder.MayerVietoris.homologyEquivOfDisjoint`: `H_k(U) × H_k(V) ≃ H_k(X)` for a disjoint
  open cover.

## Main results

* `HodgeLadder.MayerVietoris.finiteDimensional_homology_succ_and_finrank_eq`: the exact count
  `dim H_{k+1}(X) + rank φ_{k+1} + rank φ_k = dim H_{k+1}(U) + dim H_{k+1}(V) + dim H_k(U ∩ V)`.
* `HodgeLadder.MayerVietoris.finiteDimensional_homology_succ`,
  `HodgeLadder.MayerVietoris.finrank_homology_succ_add_le`: the bound with the ranks of
  `i_* : H(U ∩ V) → H(U)`.
* `HodgeLadder.MayerVietoris.bijective_coprod_homologyMap_of_disjoint`,
  `HodgeLadder.MayerVietoris.finrank_homology_eq_of_disjoint`,
  `HodgeLadder.MayerVietoris.finrank_homology_le_of_disjoint`: a disjoint open cover, in every
  degree including `0`.
* `HodgeLadder.MayerVietoris.finrank_le_finrank_range_of_comp_eq_id`: rank from a section.
* `HodgeLadder.MayerVietoris.subsingleton_homology_of_isEmpty`,
  `HodgeLadder.MayerVietoris.subsingleton_homology_succ_of_totallyDisconnected`,
  `HodgeLadder.MayerVietoris.finrank_homology_zero_of_pathConnected`: small spaces.
* `HodgeLadder.MayerVietoris.finrank_homology_zero_bool`,
  `HodgeLadder.MayerVietoris.finrank_range_overlap_zero_punit`: nonvacuity tests of the disjoint
  equality and of the exact count.
* `HodgeLadder.MayerVietoris.subsetIntersectionToLeft_apply`,
  `HodgeLadder.MayerVietoris.subsetIntersectionToRight_apply`: `rfl` pins of the two upstream
  inclusions named in the statements.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular Module Convexity

namespace HodgeLadder.MayerVietoris

/-- **Rank count along four exact terms.** For linear maps `A → B → C → D → E` over a field,
exact at `B`, `C` and `D`, with `B` and `D` finite-dimensional, the middle term `C` is
finite-dimensional and `dim C + rank f + rank f' = dim B + dim D`. -/
theorem finrank_add_finrank_range_of_exact {K A B C D E : Type*} [Field K] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C] [AddCommGroup D]
    [Module K D] [AddCommGroup E] [Module K E] (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (δ : C →ₗ[K] D) (f' : D →ₗ[K] E)
    (hfg : LinearMap.range f = LinearMap.ker g) (hgδ : LinearMap.range g = LinearMap.ker δ)
    (hδf : LinearMap.range δ = LinearMap.ker f') [FiniteDimensional K B]
    [FiniteDimensional K D] :
    FiniteDimensional K C ∧
      finrank K C + finrank K (LinearMap.range f) + finrank K (LinearMap.range f') =
        finrank K B + finrank K D := by
  have hC : FiniteDimensional K C := by
    refine ⟨(⊤ : Submodule K C).fg_of_fg_map_of_fg_inf_ker δ ?_ ?_⟩
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq, ← hgδ, LinearMap.range_eq_map]
      exact (Module.Finite.fg_top).map g
  refine ⟨hC, ?_⟩
  have e1 := LinearMap.finrank_range_add_finrank_ker δ
  have e2 := LinearMap.finrank_range_add_finrank_ker g
  have e3 := LinearMap.finrank_range_add_finrank_ker f'
  rw [hδf, ← hgδ] at e1
  rw [← hfg] at e2
  omega

variable (X : TopCat.{0}) (U V : Set X)

/-- The middle term of the Mayer–Vietoris sequence in degree `n` as the product
`H_n(U; ℚ) × H_n(V; ℚ)`: upstream's `singularMayerVietorisHomologySumIso` followed by
`ModuleCat.biprodIsoProd`. -/
noncomputable def sumHomologyEquiv (n : ℕ) :
    (singularMayerVietorisShortComplex X U V).X₂.homology n ≃ₗ[ℚ]
      (Homology ℚ (TopCat.of U) n × Homology ℚ (TopCat.of V) n) :=
  (singularMayerVietorisHomologySumIso X U V n ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv

/-- Pin: upstream's `subsetIntersectionToLeft` is the inclusion `U ∩ V → U`. -/
theorem subsetIntersectionToLeft_apply (x : ↥(U ∩ V)) :
    ((subsetIntersectionToLeft X U V x : ↥U) : X) = x := rfl

/-- Pin: upstream's `subsetIntersectionToRight` is the inclusion `U ∩ V → V`. -/
theorem subsetIntersectionToRight_apply (x : ↥(U ∩ V)) :
    ((subsetIntersectionToRight X U V x : ↥V) : X) = x := rfl

/-- **The overlap map as a pair.** Under `sumHomologyEquiv`, the Mayer–Vietoris map
`H_n(U ∩ V; ℚ) → H_n(U; ℚ) × H_n(V; ℚ)` is `x ↦ (i_* x, -j_* x)`, with `i`, `j` the inclusions
of `U ∩ V` into `U` and `V`. The sign sits on the second component, as upstream fixes it. -/
theorem sumHomologyEquiv_comp_overlap (n : ℕ) :
    (sumHomologyEquiv X U V n).toLinearMap ∘ₗ
        (HomologicalComplex.homologyMap (singularMayerVietorisShortComplex X U V).f n).hom =
      LinearMap.prod (homologyMap ℚ n (subsetIntersectionToLeft X U V))
        (-homologyMap ℚ n (subsetIntersectionToRight X U V)) := by
  have h := singularMayerVietoris_overlap_map_eq X U V n
  have hfst : (ModuleCat.biprodIsoProd (Homology ℚ (TopCat.of U) n)
      (Homology ℚ (TopCat.of V) n)).hom ≫ ModuleCat.ofHom (LinearMap.fst ℚ _ _) = biprod.fst := by
    rw [← ModuleCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc]
  have hsnd : (ModuleCat.biprodIsoProd (Homology ℚ (TopCat.of U) n)
      (Homology ℚ (TopCat.of V) n)).hom ≫ ModuleCat.ofHom (LinearMap.snd ℚ _ _) = biprod.snd := by
    rw [← ModuleCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc]
  refine LinearMap.ext fun x => Prod.ext ?_ ?_
  · have := congrArg (fun φ => ModuleCat.Hom.hom (φ ≫ biprod.fst) x) h
    rw [← hfst] at this
    exact this.trans (congrArg (fun φ => ModuleCat.Hom.hom φ x) (biprod.lift_fst _ _))
  · have := congrArg (fun φ => ModuleCat.Hom.hom (φ ≫ biprod.snd) x) h
    rw [← hsnd] at this
    exact this.trans (congrArg (fun φ => ModuleCat.Hom.hom φ x) (biprod.lift_snd _ _))

variable {X U V}

/-- **Exact Mayer–Vietoris count.** For an open cover `X = U ∪ V` with `H_{k+1}(U)`,
`H_{k+1}(V)` and `H_k(U ∩ V)` finite-dimensional over `ℚ`, the space `H_{k+1}(X)` is
finite-dimensional and
`dim H_{k+1}(X) + rank φ_{k+1} + rank φ_k = dim H_{k+1}(U) + dim H_{k+1}(V) + dim H_k(U ∩ V)`,
where `φ_n = (i_*, -j_*) : H_n(U ∩ V) → H_n(U) × H_n(V)` is the overlap map. -/
theorem finiteDimensional_homology_succ_and_finrank_eq (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (k : ℕ)
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of U) (k + 1))]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of V) (k + 1))]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of ↥(U ∩ V)) k)] :
    FiniteDimensional ℚ (Homology ℚ X (k + 1)) ∧
      finrank ℚ (Homology ℚ X (k + 1)) +
          finrank ℚ (LinearMap.range
            (LinearMap.prod (homologyMap ℚ (k + 1) (subsetIntersectionToLeft X U V))
              (-homologyMap ℚ (k + 1) (subsetIntersectionToRight X U V)))) +
          finrank ℚ (LinearMap.range
            (LinearMap.prod (homologyMap ℚ k (subsetIntersectionToLeft X U V))
              (-homologyMap ℚ k (subsetIntersectionToRight X U V)))) =
        finrank ℚ (Homology ℚ (TopCat.of U) (k + 1)) +
          finrank ℚ (Homology ℚ (TopCat.of V) (k + 1)) +
          finrank ℚ (Homology ℚ (TopCat.of ↥(U ∩ V)) k) := by
  have h1 := (singularMayerVietoris_exact_sum X U V hU hV hUV (k + 1)).moduleCat_range_eq_ker
  have h2 := (singularMayerVietoris_exact_ambient X U V hU hV hUV k).moduleCat_range_eq_ker
  have h3 := (singularMayerVietoris_exact_overlap X U V hU hV hUV k).moduleCat_range_eq_ker
  let e := sumHomologyEquiv X U V (k + 1)
  have : FiniteDimensional ℚ ((singularMayerVietorisShortComplex X U V).X₂.homology (k + 1)) :=
    LinearEquiv.finiteDimensional e.symm
  obtain ⟨hC, hcount⟩ := finrank_add_finrank_range_of_exact _ _ _ _ h1 h2 h3
  refine ⟨hC, ?_⟩
  dsimp only at hcount
  have r1 := sumHomologyEquiv_comp_overlap X U V (k + 1)
  have r0 := sumHomologyEquiv_comp_overlap X U V k
  have q1 := LinearEquiv.finrank_map_eq e (LinearMap.range
    (HomologicalComplex.homologyMap (singularMayerVietorisShortComplex X U V).f (k + 1)).hom)
  have q0 := LinearEquiv.finrank_map_eq (sumHomologyEquiv X U V k) (LinearMap.range
    (HomologicalComplex.homologyMap (singularMayerVietorisShortComplex X U V).f k).hom)
  rw [← LinearMap.range_comp] at q1 q0
  rw [r1] at q1
  rw [r0] at q0
  have qB := e.finrank_eq
  rw [Module.finrank_prod] at qB
  convert hcount using 2
  · exact congrArg (_ + ·) q1
  · exact q0
  · exact qB.symm

/-- The rank of a component is at most the rank of the pair, when the range of the pair is
finite-dimensional. -/
theorem finrank_range_le_finrank_range_prod {K A B C : Type*} [Field K] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (i : A →ₗ[K] B) (j : A →ₗ[K] C)
    [FiniteDimensional K (LinearMap.range (LinearMap.prod i j))] :
    finrank K (LinearMap.range i) ≤ finrank K (LinearMap.range (LinearMap.prod i j)) := by
  have h : LinearMap.range i = (LinearMap.range (LinearMap.prod i j)).map (LinearMap.fst K B C) := by
    rw [← LinearMap.range_comp, LinearMap.fst_prod]
  rw [h]
  exact Submodule.finrank_map_le _ _

/-- **Rank from a section.** If `p ∘ f ∘ s = id`, then `dim C ≤ rank f`. -/
theorem finrank_le_finrank_range_of_comp_eq_id {K A B C : Type*} [Field K] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (s : C →ₗ[K] A) (f : A →ₗ[K] B) (p : B →ₗ[K] C) (h : p ∘ₗ f ∘ₗ s = LinearMap.id)
    [FiniteDimensional K B] :
    finrank K C ≤ finrank K (LinearMap.range f) := by
  have hle : LinearMap.range (p ∘ₗ f ∘ₗ s) ≤ (LinearMap.range f).map p := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f (s x), ⟨s x, rfl⟩, rfl⟩
  rw [h, LinearMap.range_id] at hle
  have := Submodule.finrank_mono hle
  rw [finrank_top] at this
  exact this.trans (Submodule.finrank_map_le _ _)

/-- **Finite dimension from Mayer–Vietoris.** For an open cover `X = U ∪ V`, if `H_{k+1}(U)`,
`H_{k+1}(V)` and `H_k(U ∩ V)` are finite-dimensional over `ℚ`, so is `H_{k+1}(X)`. -/
theorem finiteDimensional_homology_succ (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (k : ℕ)
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of U) (k + 1))]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of V) (k + 1))]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of ↥(U ∩ V)) k)] :
    FiniteDimensional ℚ (Homology ℚ X (k + 1)) :=
  (finiteDimensional_homology_succ_and_finrank_eq hU hV hUV k).1

/-- **Mayer–Vietoris dimension bound.** For an open cover `X = U ∪ V` and the inclusion
`i : U ∩ V → U`, with `H_{k+1}(U)`, `H_{k+1}(V)` and `H_k(U ∩ V)` finite-dimensional over `ℚ`,
`dim H_{k+1}(X) + rank i_{*,k+1} + rank i_{*,k} ≤ dim H_{k+1}(U) + dim H_{k+1}(V) + dim H_k(U ∩ V)`.
The sign `(i, -j)` of upstream's overlap map enters only through ranks. Read it with
`finiteDimensional_homology_succ`: for an infinite-dimensional `H_{k+1}(X)` the `finrank` is `0`
and the bound is empty. -/
theorem finrank_homology_succ_add_le (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (k : ℕ)
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of U) (k + 1))]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of V) (k + 1))]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of ↥(U ∩ V)) k)] :
    finrank ℚ (Homology ℚ X (k + 1)) +
        finrank ℚ (LinearMap.range (homologyMap ℚ (k + 1) (subsetIntersectionToLeft X U V))) +
        finrank ℚ (LinearMap.range (homologyMap ℚ k (subsetIntersectionToLeft X U V))) ≤
      finrank ℚ (Homology ℚ (TopCat.of U) (k + 1)) +
        finrank ℚ (Homology ℚ (TopCat.of V) (k + 1)) +
        finrank ℚ (Homology ℚ (TopCat.of ↥(U ∩ V)) k) := by
  have h := (finiteDimensional_homology_succ_and_finrank_eq hU hV hUV k).2
  have a1 := finrank_range_le_finrank_range_prod
    (homologyMap ℚ (k + 1) (subsetIntersectionToLeft X U V))
    (-homologyMap ℚ (k + 1) (subsetIntersectionToRight X U V))
  have a0 := finrank_range_le_finrank_range_prod
    (homologyMap ℚ k (subsetIntersectionToLeft X U V))
    (-homologyMap ℚ k (subsetIntersectionToRight X U V))
  omega

/-- Rational singular homology of an empty space is zero in every degree: there are no
singular simplices. -/
theorem subsingleton_homology_of_isEmpty (Y : TopCat.{0}) [IsEmpty Y] (n : ℕ) :
    Subsingleton (Homology ℚ Y n) := by
  have hK : IsZero ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)) := by
    rw [IsZero.iff_id_eq_zero]
    ext m : 1
    apply SSet.chainComplex_hom_ext
    intro σ
    exact (IsEmpty.false (Y.toSSetObjEquiv _ σ (StdSimplex.barycenter))).elim
  exact ModuleCat.isZero_iff_subsingleton.mp
    ((HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map_isZero hK)

/-- For an open cover `X = U ∪ V` with `U` and `V` disjoint, upstream's Mayer–Vietoris sum map
`H_k(C(U) ⊞ C(V)) → H_k(X)` is bijective in every degree `k`. Degree `0` uses
`HomologicalComplex.epi_homologyMap_of_epi_of_not_rel`; higher degrees use exactness at
`H_k(X)`, the boundary landing in `H_{k-1}(∅) = 0`. -/
theorem bijective_sumChainMap_homology_of_disjoint (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (hd : Disjoint U V) (k : ℕ) :
    Function.Bijective
      (HomologicalComplex.homologyMap (singularMayerVietorisSumChainMap X U V) k).hom := by
  have : IsEmpty (TopCat.of ↥(U ∩ V)) :=
    Set.isEmpty_coe_sort.mpr (Set.disjoint_iff_inter_eq_empty.mp hd)
  have hsub : ∀ n, Subsingleton (Homology ℚ (TopCat.of ↥(U ∩ V)) n) :=
    subsingleton_homology_of_isEmpty _
  constructor
  · rw [← LinearMap.ker_eq_bot,
      ← (singularMayerVietoris_exact_sum X U V hU hV hUV k).moduleCat_range_eq_ker, eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_bot, (hsub k).elim x 0]
    exact map_zero _
  · cases k with
    | zero =>
      have := (singularMayerVietorisShortComplex_shortExact X U V).epi_g
      have := HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
        (singularMayerVietorisShortComplex X U V).g 0 (by simp)
      have := twoSubsetSmallChainInclusion_homology_isIso X U V hU hV hUV 0
      rw [← ModuleCat.epi_iff_surjective, singularMayerVietorisSumChainMap,
        HomologicalComplex.homologyMap_comp]
      infer_instance
    | succ n =>
      rw [← LinearMap.range_eq_top]
      have h := (singularMayerVietoris_exact_ambient X U V hU hV hUV n).moduleCat_range_eq_ker
      dsimp only at h
      rw [h, eq_top_iff]
      intro x _
      have := hsub n
      exact Subsingleton.elim _ _

/-- The first biproduct inclusion in `ModuleCat ℚ`, read in the product model, is
`LinearMap.inl`. -/
theorem biprod_inl_biprodIsoProd_hom (M N : ModuleCat.{0} ℚ) :
    biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom = ModuleCat.ofHom (LinearMap.inl ℚ M N) := by
  rw [← Iso.eq_comp_inv]
  apply biprod.hom_ext
  · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst, biprod.inl_fst]
    ext x
    rfl
  · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inl_snd]
    ext x
    rfl

/-- The second biproduct inclusion in `ModuleCat ℚ`, read in the product model, is
`LinearMap.inr`. -/
theorem biprod_inr_biprodIsoProd_hom (M N : ModuleCat.{0} ℚ) :
    biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom = ModuleCat.ofHom (LinearMap.inr ℚ M N) := by
  rw [← Iso.eq_comp_inv]
  apply biprod.hom_ext
  · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst, biprod.inr_fst]
    ext x
    rfl
  · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inr_snd]
    ext x
    rfl

variable (X U V) in
/-- **The sum map as a coproduct.** Under `sumHomologyEquiv`, upstream's Mayer–Vietoris sum
map is `(x, y) ↦ (ι_U)_* x + (ι_V)_* y`, with no sign. -/
theorem sum_comp_sumHomologyEquiv_symm (n : ℕ) :
    (HomologicalComplex.homologyMap (singularMayerVietorisSumChainMap X U V) n).hom ∘ₗ
        (sumHomologyEquiv X U V n).symm.toLinearMap =
      LinearMap.coprod (homologyMap ℚ n (topologicalSubsetInclusion X U))
        (homologyMap ℚ n (topologicalSubsetInclusion X V)) := by
  have h := singularMayerVietoris_sum_map_eq X U V n
  apply LinearMap.prod_ext
  · refine LinearMap.ext fun x => ?_
    have := congrArg (fun φ => ModuleCat.Hom.hom (biprod.inl ≫ φ) x) h
    erw [biprod.inl_desc] at this
    have hx : LinearMap.inl ℚ _ _ x = (biprod.inl ≫ (ModuleCat.biprodIsoProd
        (Homology ℚ (TopCat.of U) n) (Homology ℚ (TopCat.of V) n)).hom).hom x := by
      rw [biprod_inl_biprodIsoProd_hom]
      rfl
    refine (Eq.trans ?_ this).trans ?_
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hx]
      simp only [sumHomologyEquiv, ModuleCat.hom_comp, LinearMap.comp_apply]
      congr 1
      change ModuleCat.Hom.hom (_ ≫ (singularMayerVietorisHomologySumIso X U V n ≪≫
        ModuleCat.biprodIsoProd _ _).inv) _ = _
      rw [Iso.trans_inv, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    · erw [LinearMap.comp_apply, LinearMap.coprod_apply, map_zero, add_zero]
      rfl
  · refine LinearMap.ext fun x => ?_
    have := congrArg (fun φ => ModuleCat.Hom.hom (biprod.inr ≫ φ) x) h
    erw [biprod.inr_desc] at this
    have hx : LinearMap.inr ℚ _ _ x = (biprod.inr ≫ (ModuleCat.biprodIsoProd
        (Homology ℚ (TopCat.of U) n) (Homology ℚ (TopCat.of V) n)).hom).hom x := by
      rw [biprod_inr_biprodIsoProd_hom]
      rfl
    refine (Eq.trans ?_ this).trans ?_
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hx]
      simp only [sumHomologyEquiv, ModuleCat.hom_comp, LinearMap.comp_apply]
      congr 1
      change ModuleCat.Hom.hom (_ ≫ (singularMayerVietorisHomologySumIso X U V n ≪≫
        ModuleCat.biprodIsoProd _ _).inv) _ = _
      rw [Iso.trans_inv, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    · erw [LinearMap.comp_apply, LinearMap.coprod_apply, map_zero, zero_add]
      rfl

/-- **Homology of a disjoint open cover.** For an open cover `X = U ∪ V` with `U` and `V`
disjoint, `(x, y) ↦ (ι_U)_* x + (ι_V)_* y` is a bijection
`H_k(U; ℚ) × H_k(V; ℚ) → H_k(X; ℚ)` in every degree. -/
theorem bijective_coprod_homologyMap_of_disjoint (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (hd : Disjoint U V) (k : ℕ) :
    Function.Bijective (LinearMap.coprod (homologyMap ℚ k (topologicalSubsetInclusion X U))
      (homologyMap ℚ k (topologicalSubsetInclusion X V))) := by
  have h := (bijective_sumChainMap_homology_of_disjoint hU hV hUV hd k).comp
    (sumHomologyEquiv X U V k).symm.bijective
  have e := sum_comp_sumHomologyEquiv_symm X U V k
  rw [← e]
  exact h

/-- The linear equivalence `H_k(U; ℚ) × H_k(V; ℚ) ≃ H_k(X; ℚ)` for a disjoint open cover
`X = U ∪ V`, given by the sum of the two inclusion maps. -/
noncomputable def homologyEquivOfDisjoint (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (hd : Disjoint U V) (k : ℕ) :
    (Homology ℚ (TopCat.of U) k × Homology ℚ (TopCat.of V) k) ≃ₗ[ℚ] Homology ℚ X k :=
  LinearEquiv.ofBijective _ (bijective_coprod_homologyMap_of_disjoint hU hV hUV hd k)

/-- `homologyEquivOfDisjoint` sends `(x, y)` to `(ι_U)_* x + (ι_V)_* y`. -/
theorem homologyEquivOfDisjoint_apply (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (hd : Disjoint U V) (k : ℕ)
    (x : Homology ℚ (TopCat.of U) k × Homology ℚ (TopCat.of V) k) :
    homologyEquivOfDisjoint hU hV hUV hd k x =
      homologyMap ℚ k (topologicalSubsetInclusion X U) x.1 +
        homologyMap ℚ k (topologicalSubsetInclusion X V) x.2 :=
  rfl

/-- For a disjoint open cover `X = U ∪ V` with `H_k(U)` and `H_k(V)` finite-dimensional over
`ℚ`, the space `H_k(X)` is finite-dimensional. -/
theorem finiteDimensional_homology_of_disjoint (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (hd : Disjoint U V) (k : ℕ)
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of U) k)]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of V) k)] :
    FiniteDimensional ℚ (Homology ℚ X k) :=
  LinearEquiv.finiteDimensional (homologyEquivOfDisjoint hU hV hUV hd k)

/-- **Dimension of a disjoint open cover.** For a disjoint open cover `X = U ∪ V` with `H_k(U)`
and `H_k(V)` finite-dimensional over `ℚ`, `dim H_k(X) = dim H_k(U) + dim H_k(V)`. -/
theorem finrank_homology_eq_of_disjoint (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (hd : Disjoint U V) (k : ℕ)
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of U) k)]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of V) k)] :
    finrank ℚ (Homology ℚ X k) =
      finrank ℚ (Homology ℚ (TopCat.of U) k) + finrank ℚ (Homology ℚ (TopCat.of V) k) := by
  rw [← (homologyEquivOfDisjoint hU hV hUV hd k).finrank_eq, Module.finrank_prod]

/-- **Disjoint-cover dimension bound.** For a disjoint open cover `X = U ∪ V` with `H_k(U)` and
`H_k(V)` finite-dimensional over `ℚ`, `dim H_k(X) ≤ dim H_k(U) + dim H_k(V)`; the equality is
`finrank_homology_eq_of_disjoint`. -/
theorem finrank_homology_le_of_disjoint (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (hd : Disjoint U V) (k : ℕ)
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of U) k)]
    [FiniteDimensional ℚ (Homology ℚ (TopCat.of V) k)] :
    finrank ℚ (Homology ℚ X k) ≤
      finrank ℚ (Homology ℚ (TopCat.of U) k) + finrank ℚ (Homology ℚ (TopCat.of V) k) :=
  (finrank_homology_eq_of_disjoint hU hV hUV hd k).le

/-- For a path-connected space, `H_0(Y; ℚ)` is finite-dimensional. -/
theorem finiteDimensional_homology_zero_of_pathConnected (Y : TopCat.{0})
    [PathConnectedSpace Y] : FiniteDimensional ℚ (Homology ℚ Y 0) :=
  LinearEquiv.finiteDimensional
    (asIso (Y.singularHomology₀ε (ModuleCat.of ℚ ℚ))).toLinearEquiv.symm

/-- For a path-connected space, `H_0(Y; ℚ)` has dimension one, through the augmentation
`TopCat.singularHomology₀ε`. -/
theorem finrank_homology_zero_of_pathConnected (Y : TopCat.{0}) [PathConnectedSpace Y] :
    finrank ℚ (Homology ℚ Y 0) = 1 := by
  have e := (asIso (Y.singularHomology₀ε (ModuleCat.of ℚ ℚ))).toLinearEquiv
  rw [e.finrank_eq]
  exact Module.finrank_self ℚ

/-- Rational singular homology of a totally disconnected space vanishes in positive degree. -/
theorem subsingleton_homology_succ_of_totallyDisconnected (Y : TopCat.{0})
    [TotallyDisconnectedSpace Y] (n : ℕ) : Subsingleton (Homology ℚ Y (n + 1)) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℚ) (n + 1) (ModuleCat.of ℚ ℚ) Y (by omega))

/-- **Nonvacuity test of the exact count.** For the point covered by `univ` twice, the count at
`k = 0` reads `0 + 0 + rank φ₀ = 0 + 0 + 1`, so the overlap map `(i_*, -j_*)` on `H_0` has rank
one. -/
theorem finrank_range_overlap_zero_punit :
    finrank ℚ (LinearMap.range
      (LinearMap.prod (homologyMap ℚ 0 (subsetIntersectionToLeft (TopCat.of PUnit.{1})
          Set.univ Set.univ))
        (-homologyMap ℚ 0 (subsetIntersectionToRight (TopCat.of PUnit.{1})
          Set.univ Set.univ)))) = 1 := by
  have hU : IsOpen (Set.univ : Set (TopCat.of PUnit.{1})) := isOpen_univ
  have hp : PathConnectedSpace
      (TopCat.of ↥((Set.univ : Set (TopCat.of PUnit.{1})) ∩ Set.univ)) :=
    { nonempty := ⟨⟨PUnit.unit, trivial, trivial⟩⟩
      joined := fun x y => by rw [Subsingleton.elim x y] }
  have := finiteDimensional_homology_zero_of_pathConnected
    (TopCat.of ↥((Set.univ : Set (TopCat.of PUnit.{1})) ∩ Set.univ))
  have := subsingleton_homology_succ_of_totallyDisconnected
    (TopCat.of ↥(Set.univ : Set (TopCat.of PUnit.{1}))) 0
  have := subsingleton_homology_succ_of_totallyDisconnected (TopCat.of PUnit.{1}) 0
  obtain ⟨-, h⟩ := finiteDimensional_homology_succ_and_finrank_eq hU hU (Set.union_self _) 0
  have h1 := Submodule.finrank_le (LinearMap.range
    (LinearMap.prod (homologyMap ℚ (0 + 1) (subsetIntersectionToLeft (TopCat.of PUnit.{1})
        Set.univ Set.univ))
      (-homologyMap ℚ (0 + 1) (subsetIntersectionToRight (TopCat.of PUnit.{1})
        Set.univ Set.univ))))
  have e0 : finrank ℚ (Homology ℚ (TopCat.of PUnit.{1}) (0 + 1)) = 0 :=
    finrank_zero_of_subsingleton
  have e1 : finrank ℚ (Homology ℚ (TopCat.of ↥(Set.univ : Set (TopCat.of PUnit.{1}))) (0 + 1)) =
    0 := finrank_zero_of_subsingleton
  have e2 := finrank_homology_zero_of_pathConnected
    (TopCat.of ↥((Set.univ : Set (TopCat.of PUnit.{1})) ∩ Set.univ))
  rw [Module.finrank_prod] at h1
  omega

/-- **Nonvacuity test.** The discrete space `Bool`, covered by the disjoint opens `{true}` and
`{false}`, has `dim H_0(Bool; ℚ) = 2`, read off `finrank_homology_eq_of_disjoint`: the disjoint
bound is attained with a nonzero value. -/
theorem finrank_homology_zero_bool : finrank ℚ (Homology ℚ (TopCat.of Bool) 0) = 2 := by
  have hU : IsOpen ({true} : Set (TopCat.of Bool)) := isOpen_discrete _
  have hV : IsOpen ({false} : Set (TopCat.of Bool)) := isOpen_discrete _
  have hUV : ({true} : Set (TopCat.of Bool)) ∪ {false} = Set.univ := by
    ext b; cases b <;> simp
  have hd : Disjoint ({true} : Set (TopCat.of Bool)) {false} := by simp
  have hp : ∀ b : Bool, PathConnectedSpace (TopCat.of ↥({b} : Set (TopCat.of Bool))) := fun b =>
    { nonempty := ⟨⟨b, rfl⟩⟩
      joined := fun x y => by
        rw [Subsingleton.elim x y] }
  have := finiteDimensional_homology_zero_of_pathConnected
    (TopCat.of ↥({true} : Set (TopCat.of Bool)))
  have := finiteDimensional_homology_zero_of_pathConnected
    (TopCat.of ↥({false} : Set (TopCat.of Bool)))
  rw [finrank_homology_eq_of_disjoint hU hV hUV hd 0,
    finrank_homology_zero_of_pathConnected, finrank_homology_zero_of_pathConnected]

end HodgeLadder.MayerVietoris
