# Handoff 2026-11-26: `supported-forget-compat`

- Goal: `forgetRel (Φ α) = Ψ (forgetSupport α)` on `⊤`, no sign (red team finding 4 on the supported comparison).
- Checked so far: `step1-of-hom` (`step1_of_hom`), `forget-support-cocycle` (`forgetSupport_eq_comp`, `forgetSupport_named`), `constant-generator` (`integerConstantHomAddEquivGlobalSections_apply`, `terminalIso_generator`).
- On branch `rung/supported-forget-compat-wip`, `HodgeLadder/Cup/SupportedForgetFinal.lean`: the main theorem `supported_forget_compat` is assembled from these and compiles except for one `sorry` inside the lemma `forget_named_cocycle`.
- That lemma says the representative's cocycle, after `forgetMap`, has `fromSingleEquiv` equal to `globalMap c`, with `c` the relative cocycle read as a global cochain. Its steps `hgen`, `hes`, `h1` and `h2` compile.
- Blocker: stating `pairEval … z.1` for the variety's `supCocycle` times out (over 4,000,000 heartbeats), even with the proof replaced by `sorry`. The cost is the comparison of the site and `TopCat.Sheaf` spellings of the single complex on the pair sheaf, which is cheap for a general space (`supportedSection_eq_pairEval'`).
- Next move: restate `forget_named_cocycle` for a general `Y` with `U : Opens Y`, using `sInt Y` and a general `forgetMap`, prove it there, then specialize with `exact`.
- `SupportedForget.lean` already takes about 5 minutes to elaborate; keep new statements out of it.
- Resolved 2026-11-26: `gen_forget_named_cocycle` (general space, `HodgeLadder/Cup/SupportedForgetGen.lean`) checks in about 40 seconds, and the variety statement follows by `exact`. `supported-forget-compat` is checked.
