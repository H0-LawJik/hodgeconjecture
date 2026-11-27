module

public import HodgeLadder.Cup.TriadCupCap
public import HodgeLadder.Cup.TriadCupNaturality
public import HodgeLadder.Cup.CapCrossEvaluation
public import HodgeLadder.Local.CrossOrientation
public import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.NormalProjectionCoclass
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-!
# The product of normalized local classes of transversal components

Rung `local-class-product` (front `cup`, decisions 0009 and 0010). Write `u_k` for upstream's
normalized local class of `ℂ^k`, the class of `H^{2k}(ℂ^k, ℂ^k ∖ 0; ℚ)` that pairs to `1` with
upstream's complex orientation class `standardComplexLocalClass ℚ k`. Split
`ℂ^{a+b} = ℂ^a × ℂ^b` by `Fin.append` (first `a` coordinates `z'`, then `b` coordinates `z''`),
put `A = {z' ≠ 0}` and `B = {z'' ≠ 0}`, so that `A ∪ B = ℂ^{a+b} ∖ 0`.

* Model form: the triad relative cup `relCup2` of the pullbacks of `u_a` along `z ↦ z'` and of
  `u_b` along `z ↦ z''` is `u_{a+b}`, read on `(ℂ^{a+b}, A ∪ B)` through the identity of
  `ℂ^{a+b}`. Sign `+`, exact.
* Chart form: for charts adapted to `Z`, `W` and `T` whose normal coordinates on `V` are `z'`,
  `z''` and `(z', z'')`, `relCup2` of the normal-projection coclasses of `Z` and `W` on `V` is
  the normal-projection coclass of `T`, read through the identity of `V`. Sign `+`, exact.

Signs (register rows "Product of local classes (model and chart)", "Cross product of complex
orientations", "Cap–cross evaluation", "Triad relative cup product", "Cup–cap adjunction
(triad)"): every step below carries `+`. The cross
product of the complex orientation classes is the orientation class (`cross_orientation_orient`,
sign `+` from the block compatibility of upstream's real coordinates with `Fin.append`); the
cap–cross evaluation has no sign (`cap_cross_evaluation`); the cup–cap adjunction has no sign
(`relCup2_eval_eq_eval_triadCap`); naturality of `relCup2` has no sign
(`relCup2_naturality`). The degree identity `2a + 2b = 2(a + b)` enters only as the proof argument
of `relCup2`, which is a proposition.

## Main definitions

* `HodgeLadder.LocalClassProduct.projA`, `projB`: the block projections as maps of pairs.
* `HodgeLadder.LocalClassProduct.u`: upstream's normalized local class of `ℂ^k`.
* `HodgeLadder.LocalClassProduct.unionIso`: `(ℂ^{a+b}, ℂ^{a+b} ∖ 0) ≅ (ℂ^{a+b}, A ∪ B)`, the
  identity of `ℂ^{a+b}`.
* `HodgeLadder.LocalClassProduct.chartUnionIso`: `(V, (V ∖ Z) ∪ (V ∖ W)) ≅ (V, V ∖ T)`, the
  identity of `V`, when `T ∩ V = Z ∩ W ∩ V`.

## Main results

* `HodgeLadder.LocalClassProduct.relCup2_model_eval_orient`: the pairing of the model product with
  `orient a b` is `1` (the sign check).
* `HodgeLadder.LocalClassProduct.relCup2_model`: the model form.
* `HodgeLadder.LocalClassProduct.relCup2_chartNormalProjectionCoclass`: the chart form;
  `chartNormalProjectionCoclass_eq_relCup2`: the same identity read on `(V, V ∖ T)`.
* Helpers: `isOpen_setA`, `isOpen_setB`, `isOpen_chart_notMem` (openness of the relative
  subspaces), `chart_mem_iff` (`T ∩ V = Z ∩ W ∩ V` from the charts), `eval_relCup2_degree`
  (degree transport of the pairing, no scalar), `relativeCohomologyMap_normalizedRelativeCoclass`
  (the pullback of a normalized coclass along a map of pairs, the lemma asked for by the red team
  of `cap-cross-evaluation`, question (i)).

## Route

The model's pairing with `orient a b` is computed on `ℂ^a × ℂ^b`: `cross_orientation_orient`
writes `orient a b` as the push along `complexAppendMap` of the cross product of the two
orientation classes; the pairing moves along that map (upstream's
`relativeCohomologyEquivDualHomology_relativeCohomologyMap`); `relCup2_naturality` moves the cup
to the product triad, where the two pullbacks become `prFstPair^* u_a` and `prSndPair^* u_b`;
`relCup2_eval_eq_eval_triadCap` and `cap_cross_evaluation` give `⟨u_a, s_a⟩ ⟨u_b, s_b⟩ = 1`. These
last two steps are the content of `HodgeLadder.Tests.capCross_complex_model`, used here through
the rung lemma so that this module imports no test module. Uniqueness of normalized coclasses
(`normalizedRelativeCoclass_unique`, with `span_standardComplexLocalClass_eq_top_for_chart`
moved along `unionIso`) gives the model form. The chart form is `relCup2_naturality` along the
normal projection `w ↦ (eT w).2` of `V` to `ℂ^{a+b}`; the three pair-map identities are checked on
points.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology.Singular
open HodgeLadder.Cup HodgeLadder.Relative HodgeLadder.CrossOrientation HodgeLadder.CapCross

namespace HodgeLadder.LocalClassProduct

/-! ## The model on `ℂ^{a+b}` -/

/-- `ℂ^{a+b}` as an object of `TopCat`. -/
abbrev cx (a b : ℕ) : TopCat.{0} := TopCat.of (Fin (a + b) → ℂ)

/-- `setA a b = {z' ≠ 0}` is open. -/
theorem isOpen_setA (a b : ℕ) : IsOpen (setA a b) :=
  isOpen_compl_singleton.preimage (by fun_prop : Continuous fun z : Fin (a + b) → ℂ =>
    fun i : Fin a => z (Fin.castAdd b i))

/-- `setB a b = {z'' ≠ 0}` is open. -/
theorem isOpen_setB (a b : ℕ) : IsOpen (setB a b) :=
  isOpen_compl_singleton.preimage (by fun_prop : Continuous fun z : Fin (a + b) → ℂ =>
    fun j : Fin b => z (Fin.natAdd a j))

/-- The first block projection `z ↦ z'`, a map of pairs `(ℂ^{a+b}, {z' ≠ 0}) ⟶ (ℂ^a, ℂ^a ∖ 0)`. -/
def projA (a b : ℕ) : TopPair.ofSubset (X := cx a b) (setA a b) ⟶ puncturedPair ℂ a :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun z i => z (Fin.castAdd b i), by fun_prop⟩)
    fun _ h => h

/-- The second block projection `z ↦ z''`, a map of pairs
`(ℂ^{a+b}, {z'' ≠ 0}) ⟶ (ℂ^b, ℂ^b ∖ 0)`. -/
def projB (a b : ℕ) : TopPair.ofSubset (X := cx a b) (setB a b) ⟶ puncturedPair ℂ b :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun z j => z (Fin.natAdd a j), by fun_prop⟩)
    fun _ h => h

/-- Upstream's normalized local class `u_k ∈ H^{2k}(ℂ^k, ℂ^k ∖ 0; ℚ)`: it pairs to `1` with
upstream's complex orientation class `standardComplexLocalClass ℚ k`. -/
def u (k : ℕ) : RelativeCohomology ℚ (puncturedPair ℂ k) (2 * k) :=
  normalizedRelativeCoclass (standardComplexLocalClass ℚ k) (standardComplexLocalClass_ne_zero k)

/-- `(ℂ^{a+b}, ℂ^{a+b} ∖ 0) ≅ (ℂ^{a+b}, setA ∪ setB)`, the identity of `ℂ^{a+b}`; `orient a b` is
upstream's orientation class pushed along its `hom`. -/
def unionIso (a b : ℕ) :
    puncturedPair ℂ (a + b) ≅ TopPair.ofSubset (X := cx a b) (setA a b ∪ setB a b) :=
  TopPair.isoOfSubset (Homeomorph.refl _) (fun z => union_eq a b z)

/-- **Sign check of the model, `+`.** The pairing of the model product, in degree `2a + 2b`, with
`orient a b` (upstream's complex orientation class of `ℂ^{a+b}` on `(ℂ^{a+b}, setA ∪ setB)`) is
`1`. Route: `relCup2_eval_eq_eval_triadCap` turns it into a triad cap; `relCup2_naturality` and
the naturality of the cap pairing move it along `complexAppendMap` to `ℂ^a × ℂ^b`, where
`cross_orientation_orient` writes `orient a b` as the cross product of the two orientation
classes and `cap_cross_evaluation` gives `1 · 1`. -/
theorem relCup2_model_eval_orient (a b : ℕ) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (X := cx a b) (setA a b ∪ setB a b))
        (2 * a + 2 * b)
      (relCup2 (cx a b) (setA a b) (setB a b) (isOpen_setA a b) (isOpen_setB a b)
        (relativeCohomologyMap ℚ (2 * a) (projA a b) (u a))
        (relativeCohomologyMap ℚ (2 * b) (projB a b) (u b)) (2 * a + 2 * b) rfl)
      (orient a b) = 1 := by
  have hfA : ∀ z ∈ leftProdSet (P := TopCat.of (Fin a → ℂ)) ({0}ᶜ : Set (Fin a → ℂ))
      (TopCat.of (Fin b → ℂ)), complexAppendMap a b z ∈ setA a b := by
    intro z hz h
    exact hz (funext fun i => (Fin.append_left z.1 z.2 i).symm.trans (congrFun h i))
  have hfB : ∀ z ∈ rightProdSet (TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
      ({0}ᶜ : Set (Fin b → ℂ)), complexAppendMap a b z ∈ setB a b := by
    intro z hz h
    exact hz (funext fun j => (Fin.append_right z.1 z.2 j).symm.trans (congrFun h j))
  have hA' : IsOpen (leftProdSet (P := TopCat.of (Fin a → ℂ)) ({0}ᶜ : Set (Fin a → ℂ))
      (TopCat.of (Fin b → ℂ))) :=
    isOpen_compl_singleton.preimage (fst (TopCat.of (Fin a → ℂ)) (TopCat.of (Fin b → ℂ))).hom.continuous
  have hB' : IsOpen (rightProdSet (TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ))
      ({0}ᶜ : Set (Fin b → ℂ))) :=
    isOpen_compl_singleton.preimage (snd (TopCat.of (Fin a → ℂ)) (TopCat.of (Fin b → ℂ))).hom.continuous
  have hpA : TopPair.ofSubsetHom (complexAppendMap a b) hfA ≫ projA a b =
      prFstPair (P := TopCat.of (Fin a → ℂ)) ({0}ᶜ : Set (Fin a → ℂ)) (TopCat.of (Fin b → ℂ)) := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      exact Subtype.ext (funext fun i => Fin.append_left z.1.1 z.1.2 i)
    · ext z
      exact funext fun i => Fin.append_left z.1 z.2 i
  have hpB : TopPair.ofSubsetHom (complexAppendMap a b) hfB ≫ projB a b =
      prSndPair (TopCat.of (Fin a → ℂ)) (Q := TopCat.of (Fin b → ℂ)) ({0}ᶜ : Set (Fin b → ℂ)) := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      exact Subtype.ext (funext fun j => Fin.append_right z.1.1 z.1.2 j)
    · ext z
      exact funext fun j => Fin.append_right z.1 z.2 j
  rw [← cross_orientation_orient, ← relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  rw [show TopPair.ofSubsetHom (complexAppendMap a b) (complexAppendMap_mem_union a b) =
      TopPair.ofSubsetHom (complexAppendMap a b) (triadMap_mem_union _ hfA hfB) from rfl,
    relCup2_naturality (complexAppendMap a b) (isOpen_setA a b) (isOpen_setB a b) hA' hB' hfA hfB]
  have eA := congrArg (fun g => relativeCohomologyMap ℚ (2 * a) g (u a)) hpA
  have eB := congrArg (fun g => relativeCohomologyMap ℚ (2 * b) g (u b)) hpB
  simp only [relativeCohomologyMap_comp, LinearMap.comp_apply] at eA eB
  rw [eA, eB, relCup2_eval_eq_eval_triadCap, cap_cross_evaluation]
  simp only [u, normalizedRelativeCoclass_pairing_self, mul_one]

/-- The pairing with `relCup2` in degree `n` is the pairing with `relCup2` in degree `m`, for
`e : n = m`, moving the homology class along `e`. A degree transport: no scalar. -/
theorem eval_relCup2_degree (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    {p q : ℕ} (φ : RelativeCohomology ℚ (TopPair.ofSubset A) p)
    (ψ : RelativeCohomology ℚ (TopPair.ofSubset B) q) {n m : ℕ} (h : p + q = n) (e : n = m)
    (z : RelativeHomology ℚ (TopPair.ofSubset (A ∪ B)) n) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (A ∪ B)) n
        (relCup2 X A B hA hB φ ψ n h) z =
      relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (A ∪ B)) m
        (relCup2 X A B hA hB φ ψ m (h.trans e)) (e ▸ z) := by
  subst e
  rfl

/-- Pulling back a normalized coclass: if `f_* z ≠ 0` and `z` spans `H_n(X; ℚ)`, then the pullback
along `f` of the normalized coclass of `f_* z` is the normalized coclass of `z`. -/
theorem relativeCohomologyMap_normalizedRelativeCoclass {X Y : TopPair.{0}} (f : X ⟶ Y) {n : ℕ}
    {z : RelativeHomology ℚ X n} (hz : z ≠ 0) (hspan : Submodule.span ℚ {z} = ⊤)
    (hfz : relativeHomologyMap ℚ n f z ≠ 0) :
    relativeCohomologyMap ℚ n f (normalizedRelativeCoclass (relativeHomologyMap ℚ n f z) hfz) =
      normalizedRelativeCoclass z hz :=
  normalizedRelativeCoclass_unique hz hspan _ (by
    rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
      normalizedRelativeCoclass_pairing_self])

/-- **Model form, sign `+`, exact.** On `ℂ^{a+b}`, the triad relative cup of the pullback of
`u_a` along `z ↦ z'` (relative to `{z' ≠ 0}`, first factor) and the pullback of `u_b` along
`z ↦ z''` (relative to `{z'' ≠ 0}`, second factor) is `u_{a+b}` pulled back along the identity of
`ℂ^{a+b}` to `(ℂ^{a+b}, {z' ≠ 0} ∪ {z'' ≠ 0})`. The degree is `2(a + b)`, with `2a + 2b = 2(a + b)`
as the proof argument of `relCup2`. -/
theorem relCup2_model (a b : ℕ) :
    relCup2 (cx a b) (setA a b) (setB a b) (isOpen_setA a b) (isOpen_setB a b)
        (relativeCohomologyMap ℚ (2 * a) (projA a b) (u a))
        (relativeCohomologyMap ℚ (2 * b) (projB a b) (u b)) (2 * (a + b))
        (Nat.mul_add 2 a b).symm =
      relativeCohomologyMap ℚ (2 * (a + b)) (unionIso a b).inv (u (a + b)) := by
  set s := standardComplexLocalClass ℚ (a + b)
  set z := relativeHomologyMap ℚ (2 * (a + b)) (unionIso a b).hom s
  have hinv : relativeHomologyMap ℚ (2 * (a + b)) (unionIso a b).inv z = s := by
    simp only [z, ← LinearMap.comp_apply, ← relativeHomologyMap_comp, Iso.hom_inv_id,
      relativeHomologyMap_id, LinearMap.id_apply]
  have hs : s ≠ 0 := standardComplexLocalClass_ne_zero (a + b)
  have hz : z ≠ 0 := by
    intro h
    exact hs (by rw [← hinv, h, map_zero])
  have hspan : Submodule.span ℚ {z} = ⊤ := by
    rw [Submodule.span_singleton_eq_top_iff]
    intro v
    obtain ⟨r, hr⟩ := (Submodule.span_singleton_eq_top_iff ℚ s).mp
      (span_standardComplexLocalClass_eq_top_for_chart (a + b))
      (relativeHomologyMap ℚ (2 * (a + b)) (unionIso a b).inv v)
    refine ⟨r, ?_⟩
    simp only [z, ← map_smul, hr, ← LinearMap.comp_apply, ← relativeHomologyMap_comp,
      Iso.inv_hom_id, relativeHomologyMap_id, LinearMap.id_apply]
  have hR : relativeCohomologyMap ℚ (2 * (a + b)) (unionIso a b).inv (u (a + b)) =
      normalizedRelativeCoclass z hz := by
    have := relativeCohomologyMap_normalizedRelativeCoclass (unionIso a b).inv hz hspan
      (by rw [hinv]; exact hs)
    simp only [hinv] at this
    exact this
  rw [hR]
  refine normalizedRelativeCoclass_unique hz hspan _ ?_
  rw [eval_relCup2_degree _ _ _ _ _ _ _ _ (Nat.mul_add 2 a b)]
  exact relCup2_model_eval_orient a b

/-! ## The chart form -/

variable {M : Type} [TopologicalSpace M]

/-- `(V, (V ∖ Z) ∪ (V ∖ W)) ≅ (V, V ∖ T)`, the identity of `V`, when `T`, `Z ∩ W` agree on `V`. -/
def chartUnionIso (V : Set M) {Z W T : Set M} (h : ∀ y ∈ V, y ∈ T ↔ y ∈ Z ∧ y ∈ W) :
    TopPair.ofSubset (X := TopCat.of V) ({w : V | w.1 ∉ Z} ∪ {w : V | w.1 ∉ W}) ≅
      neighborhoodSupportComplementPair V T :=
  TopPair.isoOfSubset (Homeomorph.refl V) (fun w => by
    simp only [Homeomorph.refl_apply, id_eq, Set.mem_ofPred_eq, Set.mem_union, h w.1 w.2]
    tauto)

section Charts

variable {EZ EW ET : Type} [NormedAddCommGroup EZ] [NormedAddCommGroup EW] [NormedAddCommGroup ET]
  {a b : ℕ}

/-- On `V`, membership in `T` is membership in `Z` and in `W`, when the normal coordinates of the
three charts are `z'`, `z''` and `(z', z'')`. -/
theorem chart_mem_iff
    (eZ : OpenPartialHomeomorph M (EZ × (Fin a → ℂ)))
    (eW : OpenPartialHomeomorph M (EW × (Fin b → ℂ)))
    (eT : OpenPartialHomeomorph M (ET × (Fin (a + b) → ℂ)))
    {Z W T : Set M}
    (hZ : ∀ y ∈ eZ.source, y ∈ Z ↔ (eZ y).2 = 0)
    (hW : ∀ y ∈ eW.source, y ∈ W ↔ (eW y).2 = 0)
    (hT : ∀ y ∈ eT.source, y ∈ T ↔ (eT y).2 = 0)
    {V : Set M} (hVZ : V ⊆ eZ.source) (hVW : V ⊆ eW.source) (hVT : V ⊆ eT.source)
    (hnZ : ∀ y ∈ V, (eZ y).2 = fun i => (eT y).2 (Fin.castAdd b i))
    (hnW : ∀ y ∈ V, (eW y).2 = fun j => (eT y).2 (Fin.natAdd a j)) :
    ∀ y ∈ V, y ∈ T ↔ y ∈ Z ∧ y ∈ W := by
  intro y hy
  rw [hT y (hVT hy), hZ y (hVZ hy), hW y (hVW hy), hnZ y hy, hnW y hy]
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h _, funext fun j => congrFun h _⟩
  · rintro ⟨h1, h2⟩
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · exact congrFun h1 i
    · exact congrFun h2 j

/-- In a chart adapted to `Z`, the complement `{w ∈ V | w ∉ Z}` is open in `V`. -/
theorem isOpen_chart_notMem {E : Type} [NormedAddCommGroup E] {c : ℕ}
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) {Z : Set M}
    (hZ : ∀ y ∈ e.source, y ∈ Z ↔ (e y).2 = 0) {V : Set M} (hV : V ⊆ e.source) :
    IsOpen {w : V | w.1 ∉ Z} := by
  have hc : Continuous fun w : V => (e w.1).2 :=
    ((e.continuousOn.mono hV).domRestrict).snd
  convert (isOpen_compl_singleton (x := (0 : Fin c → ℂ))).preimage hc using 1
  ext w
  simp [hZ w.1 (hV w.2)]

/-- **Chart form, sign `+`, exact.** Let `eZ`, `eW`, `eT` be charts of `M` into
`EZ × ℂ^a`, `EW × ℂ^b`, `ET × ℂ^{a+b}`, adapted to `Z`, `W`, `T` (on its source each set is the zero
set of the normal coordinate), and let `V` lie in the three sources, with the normal coordinate of
`eZ` the first `a` and that of `eW` the last `b` normal coordinates of `eT` on `V`. Then the triad
relative cup of the normal-projection coclasses of `Z` (first factor) and of `W` (second factor) on
`V` is the normal-projection coclass of `T` on `V`, read on `(V, (V ∖ Z) ∪ (V ∖ W))` through the
identity of `V` (`chartUnionIso`; `T ∩ V = Z ∩ W ∩ V` by `chart_mem_iff`). The degree is
`2(a + b)`, with `2a + 2b = 2(a + b)` as the proof argument of `relCup2`. The openness proofs
`hA`, `hB` are arguments so that any proof matches; `isOpen_chart_notMem` supplies them. -/
theorem relCup2_chartNormalProjectionCoclass
    (eZ : OpenPartialHomeomorph M (EZ × (Fin a → ℂ)))
    (eW : OpenPartialHomeomorph M (EW × (Fin b → ℂ)))
    (eT : OpenPartialHomeomorph M (ET × (Fin (a + b) → ℂ)))
    (Z W T : Set M)
    (hZ : ∀ y ∈ eZ.source, y ∈ Z ↔ (eZ y).2 = 0)
    (hW : ∀ y ∈ eW.source, y ∈ W ↔ (eW y).2 = 0)
    (hT : ∀ y ∈ eT.source, y ∈ T ↔ (eT y).2 = 0)
    (V : Set M) (hVZ : V ⊆ eZ.source) (hVW : V ⊆ eW.source) (hVT : V ⊆ eT.source)
    (hnZ : ∀ y ∈ V, (eZ y).2 = fun i => (eT y).2 (Fin.castAdd b i))
    (hnW : ∀ y ∈ V, (eW y).2 = fun j => (eT y).2 (Fin.natAdd a j))
    (hA : IsOpen {w : V | w.1 ∉ Z}) (hB : IsOpen {w : V | w.1 ∉ W}) :
    relCup2 (TopCat.of V) {w : V | w.1 ∉ Z} {w : V | w.1 ∉ W} hA hB
        (chartNormalProjectionCoclass EZ a eZ Z hZ V hVZ)
        (chartNormalProjectionCoclass EW b eW W hW V hVW) (2 * (a + b))
        (Nat.mul_add 2 a b).symm =
      relativeCohomologyMap ℚ (2 * (a + b))
        (chartUnionIso V (chart_mem_iff eZ eW eT hZ hW hT hVZ hVW hVT hnZ hnW)).hom
        (chartNormalProjectionCoclass ET (a + b) eT T hT V hVT) := by
  let f : TopCat.of V ⟶ cx a b :=
    TopCat.ofHom ⟨fun w => (eT w.1).2, ((eT.continuousOn.mono hVT).domRestrict).snd⟩
  have hfA : ∀ w ∈ {w : V | w.1 ∉ Z}, f w ∈ setA a b := by
    intro w hw h
    exact hw ((hZ w.1 (hVZ w.2)).mpr ((hnZ w.1 w.2).trans h))
  have hfB : ∀ w ∈ {w : V | w.1 ∉ W}, f w ∈ setB a b := by
    intro w hw h
    exact hw ((hW w.1 (hVW w.2)).mpr ((hnW w.1 w.2).trans h))
  have hpA : TopPair.ofSubsetHom f hfA ≫ projA a b =
      chartNormalProjectionPair EZ a eZ Z hZ V hVZ := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      exact Subtype.ext (hnZ w.1.1 w.1.2).symm
    · ext w
      exact (hnZ w.1 w.2).symm
  have hpB : TopPair.ofSubsetHom f hfB ≫ projB a b =
      chartNormalProjectionPair EW b eW W hW V hVW := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      exact Subtype.ext (hnW w.1.1 w.1.2).symm
    · ext w
      exact (hnW w.1 w.2).symm
  have hpT : TopPair.ofSubsetHom f (triadMap_mem_union f hfA hfB) ≫ (unionIso a b).inv =
      (chartUnionIso V (chart_mem_iff eZ eW eT hZ hW hT hVZ hVW hVT hnZ hnW)).hom ≫
        chartNormalProjectionPair ET (a + b) eT T hT V hVT := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      rfl
    · ext w
      rfl
  have eA := congrArg (fun g => relativeCohomologyMap ℚ (2 * a) g (u a)) hpA
  have eB := congrArg (fun g => relativeCohomologyMap ℚ (2 * b) g (u b)) hpB
  have eT' := congrArg (fun g => relativeCohomologyMap ℚ (2 * (a + b)) g (u (a + b))) hpT
  simp only [relativeCohomologyMap_comp, LinearMap.comp_apply] at eA eB eT'
  have key := relCup2_naturality f (isOpen_setA a b) (isOpen_setB a b) hA hB hfA hfB
    (relativeCohomologyMap ℚ (2 * a) (projA a b) (u a))
    (relativeCohomologyMap ℚ (2 * b) (projB a b) (u b)) (2 * (a + b)) (Nat.mul_add 2 a b).symm
  rw [eA, eB, relCup2_model, eT'] at key
  exact key.symm

/-- The chart form read on `(V, V ∖ T)`: the pullback along `chartUnionIso.inv` of the triad
relative cup of the chart coclasses of `Z` and `W` is the chart coclass of `T`. Sign `+`. -/
theorem chartNormalProjectionCoclass_eq_relCup2
    (eZ : OpenPartialHomeomorph M (EZ × (Fin a → ℂ)))
    (eW : OpenPartialHomeomorph M (EW × (Fin b → ℂ)))
    (eT : OpenPartialHomeomorph M (ET × (Fin (a + b) → ℂ)))
    (Z W T : Set M)
    (hZ : ∀ y ∈ eZ.source, y ∈ Z ↔ (eZ y).2 = 0)
    (hW : ∀ y ∈ eW.source, y ∈ W ↔ (eW y).2 = 0)
    (hT : ∀ y ∈ eT.source, y ∈ T ↔ (eT y).2 = 0)
    (V : Set M) (hVZ : V ⊆ eZ.source) (hVW : V ⊆ eW.source) (hVT : V ⊆ eT.source)
    (hnZ : ∀ y ∈ V, (eZ y).2 = fun i => (eT y).2 (Fin.castAdd b i))
    (hnW : ∀ y ∈ V, (eW y).2 = fun j => (eT y).2 (Fin.natAdd a j))
    (hA : IsOpen {w : V | w.1 ∉ Z}) (hB : IsOpen {w : V | w.1 ∉ W})
    (h : ∀ y ∈ V, y ∈ T ↔ y ∈ Z ∧ y ∈ W) :
    relativeCohomologyMap ℚ (2 * (a + b)) (chartUnionIso V h).inv
        (relCup2 (TopCat.of V) {w : V | w.1 ∉ Z} {w : V | w.1 ∉ W} hA hB
          (chartNormalProjectionCoclass EZ a eZ Z hZ V hVZ)
          (chartNormalProjectionCoclass EW b eW W hW V hVW) (2 * (a + b))
          (Nat.mul_add 2 a b).symm) =
      chartNormalProjectionCoclass ET (a + b) eT T hT V hVT := by
  rw [relCup2_chartNormalProjectionCoclass eZ eW eT Z W T hZ hW hT V hVZ hVW hVT hnZ hnW,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp, Iso.inv_hom_id,
    relativeCohomologyMap_id, LinearMap.id_apply]

end Charts

end HodgeLadder.LocalClassProduct
