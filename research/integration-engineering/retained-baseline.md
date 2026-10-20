# Retained baseline

Verified against `HEAD` **4e3f01c307d67ae2c0b1b1ce9723afda39376f4d** on 2026-10-20.

Ran `python -X utf8 tools/query.py __NO_MATCH__ --deep` from each project directory. Both commands exited 0 with no matching-node output, confirming each checked tree's graph/freshness checks and deep runtime rehash passed.

| Project | Checked inputs | HEAD/working mismatches | Runtime artifacts | Checked targets | Fact nodes | Pending | Edges |
|---|---:|---:|---:|---:|---:|---:|---:|
| Root | 16 | 0 | 7,076 | 38 | 38 | 0 | 14 |
| local-field | 15 | 0 | 13,008 | 24 | 24 | 0 | 31 |

For every `input_sha256` entry in each project's `verification/checked-inputs.json`, the recorded hash equals both `git show HEAD:<repo-relative-path>` bytes and current working-tree bytes. There are no missing paths or mismatches, so the previously observed 14-byte drift is cleared from both checked input sets. Detailed counts and per-path mismatch lists are in [retained-baseline.json](retained-baseline.json).
