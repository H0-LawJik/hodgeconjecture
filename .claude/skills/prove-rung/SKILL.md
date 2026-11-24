---
name: prove-rung
description: Prove one rung of the Hodge conjecture ladder in this session. Use with a rung id, for example /prove-rung rational-equivalence. Follows the prover protocol in docs/harness.md.
---

Run `python3 tools/next.py $ARGUMENTS` and follow the brief exactly. Then apply the protocol in `.claude/agents/hodge-prover.md` in this session (do not spawn a subagent unless the user asks). Finish with the checker green, the ledger updated, a pull request, and a handoff in `docs/handoffs/`. If you release the rung, say which lemma you needed as a Lean statement, and stop.
