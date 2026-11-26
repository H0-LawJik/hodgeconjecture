# Handoff 2026-11-26: `cross-orientation`

- Checked: `HodgeLadder/Local/CrossOrientation.lean` (namespace `HodgeLadder.CrossOrientation`) and the test module `HodgeLadder/Tests/CrossOrientation.lean` (new rung `cross-orientation-test`), both imported from the root, standard axioms only. `python3 tools/check.py` exits 0. The statements the red team passed are unchanged.
- Sign: + for every m, n and every a, b, kernel-checked.
  - `cross_orientation_real`: s_m × s_n = s_{m+n} under `Fin.append`.
  - `cross_orientation_complex`: the cross product of upstream's complex orientation classes of ℂ^a and ℂ^b is `(Nat.mul_add 2 a b) ▸ standardComplexLocalClass ℚ (a + b)`.
  - `cross_orientation_orient` (red-team change C2): the same identity on (ℂ^{a+b}, setA ∪ setB), equal to `orient a b`.
- Where the sign comes from:
  - The identity shuffle has coefficient +1.
  - Its simplex is the affine simplex on (v_{min(k,m)}, w_{k−m}), with det E = det E(s_m) · det E(s_n), so the class scalar is 1.
  - No other simplex of Δ[m] ⊗ Δ[n] reaches the barycenter (`eq_idShuffle_of_shuffleBarycenter`, degenerate simplices included).
  - The (Re, Im) block identification is the identity.
  - The degree casts go through `HEq` and carry no scalar.
- Red-team changes C1 to C3: implemented. The tests sit in a separate rung because the checker reads a rung's declarations from its own module. `Complex.piBasisOneI` is on the drift list. The ledger note cites the verdict.
- What took time:
  - `rw` along `supportInclusionPairMap` and backwards along `relativeHomologyMap_comp` on `crossUnionPair`. Apply specialized lemmas with `congrArg` or `.trans` instead.
  - Membership proofs inside rewrite motives. Pass them in as hypotheses.
- Not done: the GitHub issue for the new rung `cross-orientation-test` (no push from this session); the CLAUDE.md status block.
- Next: `local-class-cross-model` can read `cross_orientation_orient`, or `cross_orientation_complex` if it is restated on ℂ^a ⊗ ℂ^b. It should import `setA`, `setB`, `orient` from this module and not redefine them.
