# capture-axiom-report.ps1 -- capture THIS file's own `#print axioms` report from the VS Code Problems
# view, filtered to the file, and refuse to report success unless the rows are really there.
#
# History of the three failed attempts, so the current shape is not a guess:
#   * rev 1 searched only ControlType.Text. The Problems rows are ControlType.TreeItem, so it reported
#     "not found" with a 47-problem panel on screen.
#   * rev 2 fixed the scope and filtered the panel to the file; that worked as an instrument and showed
#     the file had no diagnostics at that moment ("在给定的筛选条件下，没有找到结果"), because the panel
#     was opened only after the poll had already been running for minutes.
#   * rev 3 tried the Lean InfoView instead, with --force-renderer-accessibility: the InfoView group is
#     present but its webview content is not exposed through UI Automation in either mode, so nothing
#     is readable there.
#
# rev 4 therefore does the one thing the earlier revisions did not: it opens and filters the Problems
# panel *before* the file is elaborated, so the panel is already subscribed when Lean publishes the
# rows, and it polls the panel's own TreeItems. Exit codes: 2 no window, 3 wrong folder, 4 restricted,
# 6 no axiom rows, 7 rows not attributable to this file, 8 error/warning rows present.
#
# ASCII-only: PowerShell 5.1 decodes BOM-less UTF-8 as ANSI, so localised UI strings are \uXXXX.
param(
  [string]$Root = '',
  [string]$Folder = '',
  [string]$File = 'EtaComparison.lean',
  [string]$OutDir = '',
  [int]$WaitSeconds = 900
)

$bootstrap = Join-Path $env:TEMP 'capture-axiom-report.log'
function Trace([string]$m) { Add-Content -Path $bootstrap -Value ("{0} {1}" -f (Get-Date -Format 'HH:mm:ss'), $m) }
Set-Content -Path $bootstrap -Value "start $(Get-Date -Format o)"

$RE_RESTRICTED   = '\u53D7\u9650\u6A21\u5F0F|Restricted Mode'
$RE_AXIOM        = 'depends on axioms'
$RE_ERROR        = '^\u9519\u8BEF|^\u8B66\u544A|Error:|Warning:'
$RE_PROBLEMS_TAB = '\u95EE\u9898|\u9519\u8BEF|\u8B66\u544A|Problems'
$RE_FILTER       = '\u7B5B\u9009\u5668|filter'
$RE_NO_RESULTS   = '\u6CA1\u6709\u627E\u5230\u7ED3\u679C'

function Find-Window($AE, $TS) {
  $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ClassNameProperty, 'Chrome_WidgetWin_1')
  foreach ($w in $AE::RootElement.FindAll($TS::Children, $cond)) {
    try { if ($w.Current.Name -match 'Visual Studio Code') { return $w } } catch { }
  }
  return $null
}

function Get-Texts($root, $AE, $TS, [string]$pattern, [string[]]$types = @('Text', 'TreeItem')) {
  $out = @()
  foreach ($typeName in $types) {
    $type = [System.Windows.Automation.ControlType]::$typeName
    $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty, $type)
    foreach ($t in $root.FindAll($TS::Descendants, $cond)) {
      try { $n = $t.Current.Name; if ($n -match $pattern) { $out += $n } } catch { }
    }
  }
  return $out
}

function Find-Control($root, $AE, $TS, [string]$pattern, [string]$controlType) {
  $type = [System.Windows.Automation.ControlType]::$controlType
  $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty, $type)
  foreach ($el in $root.FindAll($TS::Descendants, $cond)) {
    try { if ($el.Current.Name -match $pattern) { return $el } } catch { }
  }
  return $null
}

function Dump($win, $AE, $TS, [string]$path, [string]$header) {
  $sb = New-Object System.Text.StringBuilder
  [void]$sb.AppendLine("### $header $(Get-Date -Format o)")
  [void]$sb.AppendLine("### window: $($win.Current.Name)")
  $count = 0; $stack = New-Object System.Collections.Stack; $stack.Push(@($win, 0))
  while ($stack.Count -gt 0 -and $count -lt 20000) {
    $item = $stack.Pop(); $el = $item[0]; $depth = $item[1]
    try {
      $c = $el.Current
      $nm = ($c.Name -replace '\s+', ' ').Trim()
      if ($nm.Length -gt 400) { $nm = $nm.Substring(0, 400) + '...' }
      [void]$sb.AppendLine(('{0}{1} | {2}' -f ('  ' * [Math]::Min($depth, 22)), $c.ControlType.ProgrammaticName, $nm))
      $count++
    } catch { }
    if ($depth -ge 22) { continue }
    try {
      $kids = $el.FindAll($TS::Children, [System.Windows.Automation.Condition]::TrueCondition)
      for ($i = $kids.Count - 1; $i -ge 0; $i--) { $stack.Push(@($kids[$i], $depth + 1)) }
    } catch { }
  }
  [void]$sb.AppendLine("### nodes: $count")
  $sb.ToString() | Set-Content -Path $path -Encoding utf8
  return $count
}

try {
  if (-not $Root)   { $Root = (Get-Location).Path }
  if (-not $Folder) { $Folder = Join-Path (Join-Path $Root 'candidates') 'core-transport' }
  if (-not $OutDir) { $OutDir = Join-Path (Join-Path (Join-Path $Root 'handoffs') 'core-backward-2026-10-23') 'W11/editor' }
  $filePath = Join-Path $Folder $File
  $tag = [IO.Path]::GetFileNameWithoutExtension($File)
  New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
  $log = Join-Path $OutDir 'capture-axiom-report.log'
  "=== capture $(Get-Date -Format o) ===" | Set-Content -Path $log -Encoding utf8
  "folder: $Folder"       | Add-Content $log
  "file:   $filePath"     | Add-Content $log
  "exists: $(Test-Path $filePath)" | Add-Content $log

  Add-Type -AssemblyName UIAutomationClient
  Add-Type -AssemblyName UIAutomationTypes
  Add-Type -AssemblyName Microsoft.VisualBasic
  Add-Type -AssemblyName System.Windows.Forms
  $AE = [System.Windows.Automation.AutomationElement]
  $TS = [System.Windows.Automation.TreeScope]

  $code = Join-Path (Join-Path $env:LOCALAPPDATA 'Programs\Microsoft VS Code\bin') 'code.cmd'
  $leaf = Split-Path $Folder -Leaf

  Get-Process Code -ErrorAction SilentlyContinue | Stop-Process -Force
  Start-Sleep -Seconds 3
  & $code --new-window --disable-telemetry $Folder | Out-Null
  Trace 'launched (plain window)'

  $deadline = (Get-Date).AddSeconds(180); $win = $null
  while ((Get-Date) -lt $deadline -and -not $win) {
    Start-Sleep -Seconds 2
    $w = Find-Window $AE $TS
    if ($w -and ($w.Current.Name -match [regex]::Escape($leaf))) { $win = $w }
  }
  if (-not $win) { Trace 'no window with the folder title'; exit 2 }
  Trace "window=$($win.Current.Name)"

  Start-Sleep -Seconds 5
  $restricted = @(Get-Texts $win $AE $TS $RE_RESTRICTED @('Text'))
  "restrictedBanners: $($restricted.Count)" | Add-Content $log
  if ($restricted.Count -gt 0) { Trace 'refused: restricted mode'; exit 4 }
  if ($win.Current.Name -notmatch [regex]::Escape($leaf)) { Trace 'refused: wrong folder'; exit 3 }

  & $code --reuse-window --goto ('{0}:1' -f $filePath) | Out-Null
  Start-Sleep -Seconds 6
  "opened: $filePath" | Add-Content $log

  # Open and filter the Problems panel BEFORE elaboration finishes, so the panel is subscribed when the
  # extension publishes the file's information diagnostics.
  try {
    [Microsoft.VisualBasic.Interaction]::AppActivate($win.Current.ProcessId) | Out-Null
    Start-Sleep -Milliseconds 800
    [System.Windows.Forms.SendKeys]::SendWait('^+m'); Start-Sleep -Seconds 2
    Trace 'sent Ctrl+Shift+M before elaboration'
  } catch { Trace "problems-panel route failed: $($_.Exception.Message)" }

  $filter = Find-Control $win $AE $TS $RE_FILTER 'Edit'
  if ($filter) {
    try {
      $filter.SetFocus(); Start-Sleep -Milliseconds 700
      [System.Windows.Forms.SendKeys]::SendWait('^a')
      [System.Windows.Forms.SendKeys]::SendWait($tag)
      Start-Sleep -Seconds 2
      Trace "typed Problems filter: $tag"
    } catch { Trace "filter route failed: $($_.Exception.Message)" }
  } else { Trace 'filter box not found' }

  # Poll the panel rows: TreeItems only, so the (unrelated) editor text never matches.
  $hits = @()
  $deadline = (Get-Date).AddSeconds($WaitSeconds)
  $noResults = $false
  $restarted = $false
  $startedAt = Get-Date
  while ((Get-Date) -lt $deadline) {
    $hits = @(Get-Texts $win $AE $TS $RE_AXIOM @('TreeItem'))
    $nr = @(Get-Texts $win $AE $TS $RE_NO_RESULTS @('Text'))
    if ($nr.Count -gt 0) { $noResults = $true }
    Trace ("poll: axiomTreeItems=" + $hits.Count + " noResults=" + $noResults)
    if ($hits.Count -gt 0) { break }
    # If nothing has been published after two minutes, ask the extension to restart the file: a server
    # that has finished its first pass without publishing will not publish later on its own.
    if (-not $restarted -and ((Get-Date) - $startedAt).TotalSeconds -gt 120) {
      $restarted = $true
      try {
        [Microsoft.VisualBasic.Interaction]::AppActivate($win.Current.ProcessId) | Out-Null
        Start-Sleep -Milliseconds 800
        [System.Windows.Forms.SendKeys]::SendWait('^+p'); Start-Sleep -Milliseconds 1200
        [System.Windows.Forms.SendKeys]::SendWait('Lean 4: Restart File'); Start-Sleep -Milliseconds 1500
        [System.Windows.Forms.SendKeys]::SendWait('~'); Start-Sleep -Seconds 3
        Trace 'sent Lean 4: Restart File'
        $f2 = Find-Control $win $AE $TS $RE_FILTER 'Edit'
        if ($f2) {
          $f2.SetFocus(); Start-Sleep -Milliseconds 600
          [System.Windows.Forms.SendKeys]::SendWait('^a'); [System.Windows.Forms.SendKeys]::SendWait($tag)
        }
      } catch { Trace "restart route failed: $($_.Exception.Message)" }
    }
    Start-Sleep -Seconds 5
  }
  $found = $hits.Count -gt 0
  $ownLines = @($hits | Where-Object { $_ -match [regex]::Escape($tag) })
  $errorRows = @(Get-Texts $win $AE $TS $RE_ERROR @('TreeItem'))
  $summary = @(Get-Texts $win $AE $TS '\u6709 \d+ \u4e2a\u95EE\u9898|\d+ \u4e2a\u95EE\u9898|No problems' @('Text', 'TreeItem'))

  $tree = Join-Path $OutDir 'vscode-observation-axioms.txt'
  $n = Dump $win $AE $TS $tree ("axiom-report capture for " + $File)
  Trace "dumped $n nodes"

  $evidence = [ordered]@{
    capturedAt            = (Get-Date -Format o)
    window                = $win.Current.Name
    absolutePath          = $filePath
    channel               = 'VS Code Problems panel, filtered to the file (TreeItem rows)'
    relaunchFlag          = 'none (plain window, as in the W10 capture that worked)'
    filterQuery           = $tag
    panelOpenedBeforeRun  = $true
    axiomRows             = $hits.Count
    axiomRowsMatchingFile = $ownLines.Count
    noResultsBannerSeen   = $noResults
    errorOrWarningRows    = $errorRows.Count
    problemSummaries      = $summary
    treeFile              = $tree
    treeNodes             = $n
  }
  ($evidence | ConvertTo-Json -Depth 4) | Set-Content -Path (Join-Path $OutDir 'capture-axiom-report.json') -Encoding utf8
  "foundAxiomRows: $($hits.Count)" | Add-Content $log
  "ownAxiomRows:   $($ownLines.Count)" | Add-Content $log
  "errorRows:      $($errorRows.Count)" | Add-Content $log
  "noResultsBanner: $noResults" | Add-Content $log
  ($summary -join ' || ') | Add-Content $log

  if (-not $found) { exit 6 }
  if ($ownLines.Count -eq 0) { exit 7 }
  if ($errorRows.Count -gt 0) { exit 8 }
  exit 0
} catch {
  Trace ("FAILED: " + $_.Exception.Message)
  exit 1
}
