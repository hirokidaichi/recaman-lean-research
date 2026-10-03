# E-360 live application record

- Parent authorization followed independent approval record SHA-256
  `485e1bac1f7c9a496b98133f3d77e0b82eb5d6bc53dfadd4e748d8f74b816660`.
- Pre-application equality check: all six existing targets matched their `preapply_*` snapshots and
  `docs/statement_audits/E-360.md` was absent.
- Application clock sample: 2026-09-21 02:20:47 JST (+0900).
- Applied exactly seven approved payloads with `apply_patch`: registry, official E-360 G5, two
  hypothesis cards, current frontier, proof map, and handoff.
- Byte equality after application: all seven live files matched their approved proposed payloads.
- Live checks: G1-G5 exit 0 (11 gated rows), protected exit 0 (4 pinned rows), `git diff --check`
  exit 0, `./scripts/check.sh` under 150-second timeout exit 0 (360 registry rows,
  155 `PROVED-LEAN`, 392 jobs, axiom audit 2572).
- Lean source, gates, protected labels, later ShortTight declarations, and unreviewed candidate
  semantics were not changed by this application.

Exact commands, timeouts, exit codes, output, source hashes, and live payload hashes are the other
files in this directory. `SHA256SUMS` is relative to this post-application directory.
