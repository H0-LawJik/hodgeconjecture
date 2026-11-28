module

public import HodgeLadder.Tests.P1p1Fibres
public import HodgeLadder.Cycle.Multiplicative

/-!
# `[{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)]` on ℙ¹ × ℙ¹

Rung `cycle-class-multiplicative-p1p1` (decision 0010, the second transversal case). On `p1p1`,
the fibres `{∞} × ℙ¹` and `ℙ¹ × {∞}` of the two projections over `∞ = [1 : 0]` (`p1p1FibreFst`,
`p1p1FibreSnd`) meet transversally in `(∞, ∞)` (`p1p1Corner`), and the cycle classes satisfy
`[{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)]` in `H⁴(ℙ¹ × ℙ¹; ℚ)`, exact, sign `+`. The proof applies
`HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal` with `d = 2`, `a = b = 1`; every
hypothesis is supplied by rung `p1p1-fibres-transversal`.

The identity constrains the sign only where `[(∞, ∞)] ≠ 0`; rung `p1p1-point-class-nonzero`
checks that.

## Main results

* `HodgeLadder.Tests.p1p1Fibres_cup_eq_p1p1Corner`
-/

@[expose] public section

namespace HodgeLadder.Tests

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

/-- **`[{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)]` on ℙ¹ × ℙ¹**, exact, sign `+`: the Yoneda cup product
of the cycle classes of the fibres of the first and second projections over `∞ = [1 : 0]` is the
cycle class of their intersection point. Conventions rows "Transversal product of cycle classes"
and "Point ∞ of ℙ¹ and the fibres of ℙ¹ × ℙ¹". -/
theorem p1p1Fibres_cup_eq_p1p1Corner :
    HodgeLadder.Cup.cup
        (cycleComponentSheafClass p1p1 p1p1FibreFst coheight_p1p1FibreFst)
        (cycleComponentSheafClass p1p1 p1p1FibreSnd coheight_p1p1FibreSnd)
        (2 * (1 + 1)) (by ring) =
      cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner_add :=
  HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal p1p1 (d := 2)
    p1p1FibreFst p1p1FibreSnd p1p1Corner coheight_p1p1FibreFst coheight_p1p1FibreSnd
    coheight_p1p1Corner_add (by norm_num) p1p1Corner_support_eq_inter
    p1p1Corner_support_subset_smoothSupportAmbientOpen_fst
    p1p1Corner_support_subset_smoothSupportAmbientOpen_snd p1p1Fibres_transversal

end HodgeLadder.Tests
