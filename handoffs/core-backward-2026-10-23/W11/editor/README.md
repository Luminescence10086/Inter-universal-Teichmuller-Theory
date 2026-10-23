# W11 editor evidence — what the editor plane actually certifies, and what it does not

R3 of `research/lana-link-acceptance-2026-10-23/fix-handoff.md` rejected the earlier W11 editor gate
because it rested on an **empty Problems panel**. An empty panel does not say *which* file was checked,
and it does not say that the file's own `#print axioms` report was ever displayed. This note records
four capture sessions that try to satisfy the stronger reading, and the outcome of each. Nothing here is
promoted to a pass that the capture did not produce.

## The instrument

`capture-axiom-report.ps1` (this directory) relaunches VS Code on `candidates/core-transport`, opens
`EtaComparison.lean`, opens the Problems panel **before** elaboration finishes, types the file name into
the panel's filter so that the visible rows are exactly this file's rows, polls for rows matching
`depends on axioms`, and dumps the accessibility tree. It refuses to report success on a partial
reading: exit 2 no window, 3 wrong folder, 4 restricted mode, 6 no axiom rows, 7 rows not attributable to
the file, 8 error/warning rows present.

## The four sessions

| # | Revision | Channel | Result |
|---|----------|---------|--------|
| 1 | searched `ControlType.Text` only | Problems panel | reported "not found" while 47 problem rows were on screen — the rows are `ControlType.TreeItem`, so the instrument was blind, not the editor silent |
| 2 | `Text` + `TreeItem`, panel filtered | Problems panel | instrument worked: filter typed, banner `在给定的筛选条件下，没有找到结果` — the file had **no rows of any severity**, but the panel had been opened minutes after the poll started |
| 3 | Lean InfoView, `--force-renderer-accessibility` | InfoView (webview) | InfoView group exists but its content is not exposed to UI Automation in either mode: 0 text nodes inside it |
| 4 | panel opened and filtered before elaboration, then `Lean 4: Restart File` after 120 s | Problems panel | filter `EtaComparison` typed; banner `在给定的筛选条件下，没有找到结果`; `axiomRows = 0`; `errorOrWarningRows = 0`; exit 6 |

Session 4 is the current evidence: `capture-axiom-report.json`, `capture-axiom-report.log`,
`vscode-observation-axioms.txt` (356 nodes; the Problems tab reads `问题 (Ctrl+Shift+M) - 总计 47 个问题`,
the filter box reads `筛选器问题`, the banner reads `在给定的筛选条件下，没有找到结果。`, and the editor
group carries the absolute path `D:\Inter-universal Teichmüller Theory\candidates\core-transport\EtaComparison.lean`).

## What the editor plane therefore certifies

1. The window is the one named `core-transport`, the open document is that absolute path, and the
   Problems panel is filtered to `EtaComparison`.
2. For that file the panel holds **zero rows of any severity** — no error, no warning, no information.
3. The channel itself works: the 47 rows it does hold belong to other files of the same package and are
   themselves `#print axioms` information rows, so this panel does publish that kind of row when a file
   has been elaborated.

## What it does not certify, and why the gate is now marked PENDING

Point 2 is *absence of rows*, and point 3 shows that other files in the same window did produce rows.
The file's own 43 `#print axioms` lines (see `../axioms.txt`, produced by the CLI) therefore did **not**
reach the panel: the extension did not elaborate this file in these sessions, so the editor plane never
displayed its axiom report and cannot be cited as having done so.

Consequences, applied in `../delivery.json`:

* `gates.editor.errors` / `gates.editor.warnings` become `not attested by the editor` rather than `0`:
  a file that was not elaborated produces no rows, and "no rows" is not a reading of zero diagnostics.
* `status` drops from `CLI_CHECKED_EDITOR_CHECKED` to `CLI_CHECKED_EDITOR_PENDING`, and `editor_run`
  becomes `false`, matching the label T3 already uses for the same situation.
* The axiom footprint of the file is carried by the CLI plane only: 43 declarations, 43 `#print axioms`
  lines, axioms `propext, Classical.choice, Quot.sound`, zero errors, zero warnings
  (`../check.json`, `--build-lib`, `-DwarningAsError=true`).

## Reproducing

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass `
  -File handoffs\core-backward-2026-10-23\W11\capture-axiom-report.ps1 `
  -Root "D:\Inter-universal Teichmüller Theory" -File EtaComparison.lean -WaitSeconds 240
```

Exit 0 would mean the file's own axiom rows were on screen with no error or warning row; that is the
only outcome that would restore the `EDITOR_CHECKED` label. It was not reached in four sessions, and the
label has been lowered accordingly rather than argued around.
