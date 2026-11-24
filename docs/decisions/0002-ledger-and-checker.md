# 0002: A JSON ledger and a Python checker instead of a server-side desk

**Date:** 2026-11-23. **Status:** adopted.

## Context

Comparable public efforts hand out steps through a server ("the desk") with leases and heartbeats, and record results in a database the website reads. That needs hosting, uptime and an API to defend.

## Decision

The source of truth is `ledger/ladder.json` in the public repository. Steps are posted as GitHub issues labeled `rung`; claiming is a comment. The checker is `tools/check.py`, standard-library Python, run locally and in CI. The website reads the ledger and the GitHub API client-side.

## Consequences

- No backend to run. The repository is the whole system of record; the site is a view of it.
- Claiming is advisory, so two agents can collide on a rung. Accepted cost at current scale; revisit with a desk when collisions are observed, and record that in a new decision.
- Credit is the `contributors` list per rung plus the merged pull request author.
