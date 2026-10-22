# Editor check attempt for T3 (and its dependency): result `PARTIAL`

The handoff left `editor_status: NOT_CHECKED`. This document records what an actual VS Code
attempt produced, including the attempts that failed, so that nothing here reads as a pass.

## What was done

VS Code 1.143.0 with extension `leanprover.lean4-0.0.240` was launched on the two Lake projects,
driven through Windows UI Automation (no screenshots, no image files: every claim below is
backed by a text capture of the accessibility tree).

| attempt | window | outcome |
|---|---|---|
| 1 | — | **invalid** — the folder path was passed unquoted to `code.cmd`, so VS Code split it on the space and opened `D:\Inter-universal` plus `…\Teichmüller`; the window was also in Restricted Mode, which disables the Lean extension. Its "没有问题" status line therefore says nothing about Lean. Kept as `vscode-observation-attempt1-INVALID.txt`. |
| 2 | `core-transport - Visual Studio Code` | trusted via the banner's own 管理 → 信任 flow (no user settings were edited); the Lean InfoView opened and the Lean 4 status item appeared; the file tab `DelegatedLogBridge.lean` is present, and the editor reports **1 problem**. |
| 2b | same | Problems panel: `错误: 行 1 和字符 1 处的 Imports are out of date and must be rebuilt; use the "Restart File" command in your editor.` |
| 3 | `core-log - Visual Studio Code` | same single diagnostic for `CoreLog/QpThree.lean`, both before and **after** `lake build` succeeded (3047 jobs, 21 s, exit 0) and after a full editor restart. |

## What is established

1. The editor really was opened, trusted, and running the Lean 4 extension: the accessibility
   tree shows the `Lean 4` status item, the `Lean InfoView` editor group, and the file's tab.
2. The single diagnostic is the extension's *stale-imports guard*, not a Lean elaboration error.
   It sits at line 1, character 1, and its text names its own remedy.
3. Its cause in `core-transport` is structurally demonstrable and independent of the editor:
   `lake build CoreTransport` fails with
   `no such file or directory … candidates/core-transport/CoreTransport.lean` — the lakefile
   declares `lean_lib CoreTransport` but the library root module does not exist. The extension
   cannot obtain a build plan, so it cannot check imports.
4. In `core-log` the library root **does** exist and `lake build` succeeds, yet the guard still
   fires. So the guard is not only about a failed build; whatever it compares is still
   considered stale, and clearing it from outside the editor was not achieved.

## What is therefore NOT claimed

- No claim of zero diagnostics in the editor. The count observed was **1 error, 0 warnings**.
- No InfoView `No goals` observation for the four T3 declarations. The InfoView pane is present
  in the tree as `ControlType.Document | Infoview` but exposes no text through this capture
  method, and cursor placement at each proof end was not driven to a state where that text
  appears.
- `editor_status` stays `PARTIAL`, not checked-and-passed; nothing is admitted to the fact-tree.

## What the main line should do (one concrete action)

Add the missing library root, i.e. a two-line `candidates/core-transport/CoreTransport.lean`
that imports `CoreTransport.Basic` and `CoreTransport.Completion`, then re-run this check. T3's
own rules forbid creating that file (the only permitted new Lean source was
`DelegatedLogBridge.lean`), which is why it is reported rather than fixed here. Whether the
`core-log` guard then clears is a separate question and should not be assumed.
