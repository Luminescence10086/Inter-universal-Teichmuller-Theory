# T4 — frozen replay of three existing entries

status: `CLI_CHECKED_EDITOR_PENDING` · three commands, each run **once**, real exit codes.

## Step 1 — prior records checked before replaying

`research/core-log-extraction-2026-10-22.json` (3 sources + 3 logs) and
`research/core-transport-checks-2026-10-22.json` (3 logs) were re-hashed against disk:
**9/9 recorded hashes match, 0 mismatches, 0 missing**. Two sources compiled below had **no
record** in those files — `CoreTransport/Completion.lean` and `CoreTransport/AxiomExports.lean`
were never listed as *sources* (only their logs were) — so their hashes are recorded here for
the first time rather than assumed.

## Step 2 — the replay

| # | cwd | argv (after `lake`) | exit | stdout | stderr | axioms | errors | warnings |
|---|---|---|---|---|---|---|---|---|
| 1 | `candidates/core-log` | `env lean -DwarningAsError=true CoreLog/QpThree.lean` | 0 | 635 B | 0 B | 7 | 0 | 0 |
| 2 | `candidates/core-transport` | `env lean -DwarningAsError=true CoreTransport/Completion.lean` | 0 | 0 B | 0 B | 0 | 0 | 0 |
| 3 | `candidates/core-transport` | `env lean -DwarningAsError=true CoreTransport/AxiomExports.lean` | 0 | 935 B | 0 B | 10 | 0 | 0 |

Executable: `C:\Users\18746\.elan\bin\lake.exe`. Each process had a 300 s ceiling; none came
close, none timed out. No `-o`, no upstream rebuild, no `lake build`, no `lake update`, and
`DelegatedLogBridge.lean` (T3) was **not** compiled here, per the handoff.

Sources hashed before and after: `CoreLog/QpThree.lean`, `CoreTransport/Completion.lean`,
`CoreTransport/AxiomExports.lean`, `CoreTransport/Basic.lean`,
`PadicLogVolume/PadicLog.lean` — **0 drift**.

## A process defect worth recording

The first attempt used PowerShell `Start-Process -PassThru` + `WaitForExit()`; the returned
object gave **no usable `ExitCode`** (and its `StartTime` was null, raising an error). The
handoff forbids filling in a fabricated `0`, so that attempt produced `exit_code: null` and was
discarded in favour of `replay.py`, which drives `subprocess.run` and reports `returncode`
directly. The exit codes above come from that second, measured run; the logs on disk are from
it, and the discarded attempt's logs were overwritten.

## What this does and does not establish

Three specific command-line invocations exit 0 with zero diagnostics on the hashes recorded.
That is a **replay**, not a proof: no `#print axioms` claim is added beyond what the entries
themselves export, the editor was never opened, and **no IUT GAP is closed by this task**.
