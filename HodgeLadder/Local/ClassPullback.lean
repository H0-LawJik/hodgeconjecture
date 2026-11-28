module

public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-!
# Pulling back the normal-projection coclass along a chart projection

Rung `local-class-pullback-submersion` (sub-rung of `fibre-class-pullback`).

Let `f : M' → M` be continuous, `e : M ⇀ E × ℂ^c` a chart in which `S ⊆ M` is the zero set of the
normal coordinate `(e ·).2`, and `e' : M' ⇀ E' × ℂ^c` a chart of `M'` with the same normal
coordinate after `f`: `(e (f y)).2 = (e' y).2` on an open `W' ⊆ e'.source` mapped by `f` into
`W ⊆ e.source`. In local coordinates `f` is then a map `(t', n) ↦ (g (t', n), n)`; a holomorphic
submersion written in charts as a coordinate projection `(t'', t, n) ↦ (t, n)` is the case the
ladder uses (the first projection of `ℙ¹ × ℙ¹`). The main theorem: the pullback of upstream's
`chartNormalProjectionCoclass` of `e`, `S`, `W` along the map of pairs induced by `f` is the
`chartNormalProjectionCoclass` of `e'`, `f⁻¹ S`, `W'`. Exact, sign `+`, no scalar.

Signs. No sign enters: the two normal projections agree as maps of pairs, so both coclasses are
pullbacks of the same normalized class of `(ℂ^c, ℂ^c ∖ 0)`. Upstream's charts put the tangent block
first and the normal block second (`E × ℂ^c`), on both sides, so the statement contains no
reordering of coordinates. A reordering appears only when a chart in the maximal atlas, with values
in `ℂ^d`, is split into tangent and normal blocks to produce `e` or `e'`. The split enters through
the holomorphy hypothesis `he` of `cycle-class-germ` alone, as its `ℂ`-linear witness `L`; the chart
coclass reads only the normal coordinate `(e ·).2`, so `L` does not occur in it, and this theorem
assumes no holomorphy (row "Pullback of local classes along a chart projection" of
`docs/conventions.md`).

## Main definitions

* `HodgeLadder.LocalClassPullback.neighborhoodSupportPullbackPairMap`: the map of pairs
  `(W', W' ∖ S') → (W, W ∖ S)` induced by `f`, when `f` maps `W'` into `W` and `S'` contains
  the points of `W'` that `f` sends into `S`.

## Main results

* `HodgeLadder.LocalClassPullback.pullbackPairMap_comp_chartNormalProjectionPair`: the normal
  projections agree as maps of pairs.
* `HodgeLadder.LocalClassPullback.chartNormalProjectionCoclass_pullback`: the rung, for any `S'`
  adapted to `e'` that contains `f⁻¹ S ∩ W'`.
* `HodgeLadder.LocalClassPullback.chartNormalProjectionCoclass_pullback_preimage`: the rung with
  `S' = f⁻¹ S`.
* `HodgeLadder.LocalClassPullback.inclusion_comp_pullbackPairMap`: the pullback commutes with
  restriction to smaller neighborhoods.
* `HodgeLadder.LocalClassPullback.restrict_pullback_eq_chartNormalProjectionCoclass`: the form
  `fibre-class-pullback` consumes: if a class on `(V, V ∖ S)` restricts on `W` to the chart
  coclass of `e`, its pullback to `(V', V' ∖ S')` restricts on `W'` to the chart coclass of `e'`.
* `HodgeLadder.LocalClassPullback.chartNormalProjectionCoclass_flattened_ne_zero`: non-vacuity,
  the chart coclass on upstream's flattened neighborhood of a support point is nonzero.
-/

@[expose] public noncomputable section

open CategoryTheory Topology AlgebraicTopology.Singular

namespace HodgeLadder.LocalClassPullback

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M']

/-- The map of pairs `(W', W' ∖ S') → (W, W ∖ S)` given by a continuous `f : M' → M` on both
subspaces, when `f` maps `W'` into `W` and every point of `W'` that `f` sends into `S` lies in
`S'`. -/
def neighborhoodSupportPullbackPairMap (f : M' → M) (hf : Continuous f) {W' : Set M'}
    {W : Set M} (hWW : Set.MapsTo f W' W) {S' : Set M'} {S : Set M}
    (hSS : ∀ y ∈ W', f y ∈ S → y ∈ S') :
    neighborhoodSupportComplementPair W' S' ⟶ neighborhoodSupportComplementPair W S :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w => ⟨f w.1, hWW w.2⟩,
      (hf.comp continuous_subtype_val).subtype_mk _⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨f w.1.1, hWW w.1.2⟩, fun h => w.2 (hSS _ w.1.2 h)⟩,
      ((hf.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _⟩)
    (by ext w; rfl)

/-- Restriction to smaller neighborhoods commutes with the pullback map of pairs. -/
theorem inclusion_comp_pullbackPairMap (f : M' → M) (hf : Continuous f) {W' V' : Set M'}
    {W V : Set M} (hWV' : W' ⊆ V') (hWV : W ⊆ V) (hWW : Set.MapsTo f W' W)
    (hVV : Set.MapsTo f V' V) {S' : Set M'} {S : Set M}
    (hSS : ∀ y ∈ V', f y ∈ S → y ∈ S') :
    neighborhoodSupportInclusionPairMap hWV' S' ≫
        neighborhoodSupportPullbackPairMap f hf hVV hSS =
      neighborhoodSupportPullbackPairMap f hf hWW (fun y hy => hSS y (hWV' hy)) ≫
        neighborhoodSupportInclusionPairMap hWV S := rfl

variable {E E' : Type} [NormedAddCommGroup E] [NormedAddCommGroup E'] {c : ℕ}

/-- The pullback map of pairs followed by the normal projection of `e` is the normal projection
of `e'`, when the two normal coordinates agree on `W'`. -/
theorem pullbackPairMap_comp_chartNormalProjectionPair (f : M' → M) (hf : Continuous f)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (e' : OpenPartialHomeomorph M' (E' × (Fin c → ℂ))) (S' : Set M')
    (hS' : ∀ y ∈ e'.source, y ∈ S' ↔ (e' y).2 = 0)
    (W : Set M) (hW : W ⊆ e.source) (W' : Set M') (hW' : W' ⊆ e'.source)
    (hWW : Set.MapsTo f W' W) (hSS : ∀ y ∈ W', f y ∈ S → y ∈ S')
    (hn : ∀ y ∈ W', (e (f y)).2 = (e' y).2) :
    neighborhoodSupportPullbackPairMap f hf hWW hSS ≫ chartNormalProjectionPair E c e S hS W hW =
      chartNormalProjectionPair E' c e' S' hS' W' hW' := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    exact Subtype.ext (hn w.1.1 w.1.2)
  · ext w
    exact hn w.1 w.2

/-- **Local classes pull back along a chart projection, sign `+`, exact.** Let `f : M' → M` be
continuous, `e` a chart of `M` adapted to `S` and `e'` a chart of `M'` adapted to `S'`, both with
normal block `ℂ^c` second, and let `f` map `W' ⊆ e'.source` into `W ⊆ e.source` with
`(e (f y)).2 = (e' y).2` on `W'` and `f⁻¹ S ∩ W' ⊆ S'`. Then the pullback along `f` of the
normal-projection coclass of `e` on `W` is the normal-projection coclass of `e'` on `W'`, in
`H^{2c}(W', W' ∖ S'; ℚ)`. -/
theorem chartNormalProjectionCoclass_pullback (f : M' → M) (hf : Continuous f)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (e' : OpenPartialHomeomorph M' (E' × (Fin c → ℂ))) (S' : Set M')
    (hS' : ∀ y ∈ e'.source, y ∈ S' ↔ (e' y).2 = 0)
    (W : Set M) (hW : W ⊆ e.source) (W' : Set M') (hW' : W' ⊆ e'.source)
    (hWW : Set.MapsTo f W' W) (hSS : ∀ y ∈ W', f y ∈ S → y ∈ S')
    (hn : ∀ y ∈ W', (e (f y)).2 = (e' y).2) :
    relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportPullbackPairMap f hf hWW hSS)
        (chartNormalProjectionCoclass E c e S hS W hW) =
      chartNormalProjectionCoclass E' c e' S' hS' W' hW' := by
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    pullbackPairMap_comp_chartNormalProjectionPair f hf e S hS e' S' hS' W hW W' hW' hWW hSS hn]

/-- The rung with `S' = f⁻¹ S`: when `f⁻¹ S` is the zero set of the normal coordinate of `e'`,
the pullback along `f` of the chart coclass of `S` is the chart coclass of `f⁻¹ S`. Sign `+`. -/
theorem chartNormalProjectionCoclass_pullback_preimage (f : M' → M) (hf : Continuous f)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (e' : OpenPartialHomeomorph M' (E' × (Fin c → ℂ)))
    (hS' : ∀ y ∈ e'.source, y ∈ f ⁻¹' S ↔ (e' y).2 = 0)
    (W : Set M) (hW : W ⊆ e.source) (W' : Set M') (hW' : W' ⊆ e'.source)
    (hWW : Set.MapsTo f W' W) (hn : ∀ y ∈ W', (e (f y)).2 = (e' y).2) :
    relativeCohomologyMap ℚ (2 * c)
        (neighborhoodSupportPullbackPairMap f hf hWW (S' := f ⁻¹' S) (fun _ _ h => h))
        (chartNormalProjectionCoclass E c e S hS W hW) =
      chartNormalProjectionCoclass E' c e' (f ⁻¹' S) hS' W' hW' :=
  chartNormalProjectionCoclass_pullback f hf e S hS e' _ hS' W hW W' hW' hWW _ hn

/-- **Restricted form.** Let `α` be a class on `(V, V ∖ S)` whose restriction to `W ⊆ V` is the
chart coclass of `e`, and let `f` map `V'` into `V` and `W' ⊆ V'` into `W`, with the hypotheses of
`chartNormalProjectionCoclass_pullback` on `W'`. Then the restriction to `W'` of the pullback of
`α` to `(V', V' ∖ S')` is the chart coclass of `e'` on `W'`. Sign `+`, exact. -/
theorem restrict_pullback_eq_chartNormalProjectionCoclass (f : M' → M) (hf : Continuous f)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (e' : OpenPartialHomeomorph M' (E' × (Fin c → ℂ))) (S' : Set M')
    (hS' : ∀ y ∈ e'.source, y ∈ S' ↔ (e' y).2 = 0)
    {V : Set M} {V' : Set M'} (hVV : Set.MapsTo f V' V)
    (hSS : ∀ y ∈ V', f y ∈ S → y ∈ S')
    (W : Set M) (hW : W ⊆ e.source) (hWV : W ⊆ V)
    (W' : Set M') (hW' : W' ⊆ e'.source) (hWV' : W' ⊆ V')
    (hWW : Set.MapsTo f W' W) (hn : ∀ y ∈ W', (e (f y)).2 = (e' y).2)
    (α : RelativeCohomology ℚ (neighborhoodSupportComplementPair V S) (2 * c))
    (hα : relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap hWV S) α =
      chartNormalProjectionCoclass E c e S hS W hW) :
    relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap hWV' S')
        (relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportPullbackPairMap f hf hVV hSS) α) =
      chartNormalProjectionCoclass E' c e' S' hS' W' hW' := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    inclusion_comp_pullbackPairMap f hf hWV' hWV hWW hVV hSS, relativeCohomologyMap_comp,
    LinearMap.comp_apply, hα]
  exact chartNormalProjectionCoclass_pullback f hf e S hS e' S' hS' W hW W' hW' hWW _ hn

/-- Non-vacuity of both sides: on upstream's flattened neighborhood of a point `x` of `S` in the
chart source, the chart coclass pairs to `1` with upstream's normal class
(`chartNormalProjectionCoclass_apply_normalClass`), so it is nonzero; a sign `-1` in
`chartNormalProjectionCoclass_pullback` would contradict that pairing. -/
theorem chartNormalProjectionCoclass_flattened_ne_zero [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0) :
    chartNormalProjectionCoclass E c e S hS (flattenedSupportNeighborhood E c e x hx)
        (flattenedSupportNeighborhood_subset_source E c e x hx) ≠ 0 := by
  intro h
  have h1 := chartNormalProjectionCoclass_apply_normalClass E c e S hS x hx h0
  rw [h, map_zero] at h1
  exact zero_ne_one ((LinearMap.zero_apply _).symm.trans h1)

end HodgeLadder.LocalClassPullback
