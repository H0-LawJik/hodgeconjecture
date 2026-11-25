# Handoff 2026-11-25: the ℙ¹ test case

- Moved: `projective-line-witness`, `projective-line-point`, `contractible-open-acyclic` (PR #36, parallel agent), `projective-line-class-nonzero`, `projective-line-h2`, `projective-line-test`, all checked with the standard axioms.
- Witness: smoothness from Oka's standard charts and base change; integrality on Oka's ℙ¹ over ℂ, carried to upstream's object by `okaIso`.
- Point: [1 : 0] is the complement of the chart X₁ ≠ 0, which is affine space over Spec ℂ; its complex points are ℂ.
- General results: `cycleComponentSheafClass_ne_zero_of_subsingleton` (codimension one, any X) and `finrank_H2_of_subsingleton` (curves).
- H² count: forget support is bijective in degree two. Upstream's supported group is relative singular cohomology, which the point coclass spans.
- Next: the Markman inventory. `projective-space-test` (ℙⁿ, n ≥ 2) stays open.
