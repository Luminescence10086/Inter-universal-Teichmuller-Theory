# Editor check for T3: `EDITOR_CHECKED` (zero errors, zero warnings)

The handoff left `editor_status: NOT_CHECKED`. This document records what an actual VS Code
attempt produced — including the attempts that failed, since two of them looked like results and
were not.

## Final observation

VS Code 1.143.0, extension `leanprover.lean4-0.0.240`, workspace folder
`candidates/core-transport` opened in a **trusted** window (trust granted through the Restricted
Mode banner itself; no user settings were edited). Problems panel:

| severity | count |
|---|---|
| errors | **0** |
| warnings | **0** |
| information | 4 |

The four information entries are the file's own `#print axioms` output, each reading
`depends on axioms: [propext, Classical.choice, Quot.sound]` (lines 69–72). The status bar shows
`信息: 4 条` and carries no error or warning counter.

## The path there, including the failures

| attempt | outcome |
|---|---|
| 1 | **invalid** — the folder path was passed unquoted to `code.cmd`, so VS Code split it on the space and opened `D:\Inter-universal` plus `…\Teichmüller`; the window was also in Restricted Mode, which disables the Lean extension. Its "没有问题" status line therefore says nothing about Lean. Kept as `vscode-observation-attempt1-INVALID.txt`. |
| 2 | trusted window, Lean 4 active, file open — and **1 error**: `Imports are out of date and must be rebuilt; use the "Restart File" command in your editor.` at line 1, character 1. |
| 2b | driving the extension's own "Restart File" command did not clear it. |
| 2c | `CoreLog/QpThree.lean` in `core-log` showed the **same** single guard message, even after `lake build` there succeeded (3047 jobs, exit 0) and the editor was restarted. |
| 3 | root cause found and fixed; re-captured: **0 errors, 0 warnings, 4 information**. |

## Root cause and the fix, and how the fix is labelled

`lakefile.lean` declares `lean_lib CoreTransport`, and Lake resolves the library root to the
module `CoreTransport`, i.e. the file `CoreTransport.lean`. That file did not exist, so

    lake build CoreTransport  ->  exit 1
    error: no such file or directory: .../candidates/core-transport/CoreTransport.lean

and the extension, unable to obtain a build plan for imports, reported its stale-imports guard
instead of elaborating the file.

`candidates/core-transport/CoreTransport.lean` was therefore added: two `import` lines and a
header that says, in the file itself, that **it is a structural fix, declares nothing, contains no
mathematics, and sits outside T3's permitted-source rule** (T3 allowed only
`DelegatedLogBridge.lean`); it records that the user authorised it on 2026-10-23 with the explicit
instruction to label it. After the addition:

- `lake build CoreTransport` → exit 0, 2672 jobs;
- the T3 entry `lake env lean -DwarningAsError=true DelegatedLogBridge.lean` → exit 0, stderr 0
  bytes, the same four whitelisted axiom lines;
- the editor observation above.

## The InfoView reading (this was the last missing piece)

Plain UI Automation cannot see the Infoview: it is an embedded webview, and the same limitation is
already recorded in round 5 of this repository. The lever that worked is Chromium's own
accessibility tree — VS Code relaunched with `--force-renderer-accessibility` exposes the webview
content, and the cursor is then parked on the line after the last tactic step (or at the end of
it) so the Tactic state section reports the goal list.

One single pass, all four declarations:

| declaration | cursor line | Tactic state |
|---|---|---|
| `localLog_eq_padicLog` | 36 | `No goals` |
| `summable_logTerm` | 41 | `Goals accomplished!` |
| `hasSum_logTerm_localLog` | 50 | `No goals` |
| `logImage_Q3_eq_closedBall` | 64 | `No goals` / `Goals accomplished!` |

Both strings are the Lean 4 extension's ways of saying the goal list is empty. In the captured
tree the text sits under the `Tactic state` heading, and the sibling section
`All Messages ( 4)` holds the four axiom reports — so the same capture shows, in one place, that
the proofs are closed and that the axioms are the whitelisted three.

Captures: `infoview/<declaration>.txt`, summary in `infoview/infoview-summary.json`.

A note on flakiness, because it shaped the method: the pane does not always repaint immediately,
and the first passes read an empty Tactic state at the correct cursor positions. The capture now
polls up to 24 s for the text instead of sleeping a fixed interval; the run recorded here is one
pass in which all four were read.

## What this does and does not establish

It establishes, from observation rather than from the CLI: the four declarations elaborate in the
editor with zero errors and zero warnings, each proof leaves no goals, and the axiom reports shown
in the editor match the whitelist. It is still an observation record, not a certificate — the
`fact_tree_admitted` flag stays `false`.

