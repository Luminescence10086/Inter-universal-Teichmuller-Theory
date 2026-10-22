# capture-infoview.ps1 -- try to read the Lean InfoView's goal state per declaration.
# The Infoview is an embedded webview; under plain UI Automation its text is not exposed.
# This script relaunches VS Code with --force-renderer-accessibility (which asks Chromium to
# build its accessibility tree) and, for each declaration, parks the cursor on the line AFTER
# the last tactic step, where the InfoView should say "No goals".
# It reports exactly what it found and never turns a missing reading into a pass.
param(
  [string]$Root = '',
  [string]$Folder = '',
  [string]$File = 'DelegatedLogBridge.lean',
  [string]$OutDir = '',
  [string[]]$Targets = @(
    'localLog_eq_padicLog:36',
    'summable_logTerm:42',
    'hasSum_logTerm_localLog:50',
    'logImage_Q3_eq_closedBall:64'
  )
)

function Trace([string]$m) { Add-Content -Path (Join-Path $env:TEMP 'capture-infoview.log') -Value ("{0} {1}" -f (Get-Date -Format 'HH:mm:ss'), $m) }
Set-Content -Path (Join-Path $env:TEMP 'capture-infoview.log') -Value "start $(Get-Date -Format o)"

function Dump($win, $AE, $TS, [string]$path, [string]$header, [int]$maxDepth = 18) {
  $sb = New-Object System.Text.StringBuilder
  [void]$sb.AppendLine("### $header $(Get-Date -Format o)")
  $count = 0; $stack = New-Object System.Collections.Stack; $stack.Push(@($win, 0))
  while ($stack.Count -gt 0 -and $count -lt 9000) {
    $item = $stack.Pop(); $el = $item[0]; $depth = $item[1]
    try {
      $c = $el.Current
      $nm = ($c.Name -replace '\s+', ' ').Trim()
      if ($nm.Length -gt 600) { $nm = $nm.Substring(0, 600) + '...' }
      [void]$sb.AppendLine(('{0}{1} | {2}' -f ('  ' * [Math]::Min($depth, 22)), $c.ControlType.ProgrammaticName, $nm))
      $count++
    } catch { }
    if ($depth -ge $maxDepth) { continue }
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
  if (-not $OutDir) { $OutDir = Join-Path (Join-Path (Join-Path $Root 'handoffs') 'core-support-2026-10-22') 'T3/infoview' }
  New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
  Add-Type -AssemblyName UIAutomationClient
  Add-Type -AssemblyName UIAutomationTypes
  $AE = [System.Windows.Automation.AutomationElement]
  $TS = [System.Windows.Automation.TreeScope]

  Get-Process Code -ErrorAction SilentlyContinue | Stop-Process -Force
  Start-Sleep -Seconds 3
  $code = Join-Path (Join-Path $env:LOCALAPPDATA 'Programs\Microsoft VS Code\bin') 'code.cmd'
  # --force-renderer-accessibility asks Chromium to expose its accessibility tree, which is the
  # only lever that can make an embedded webview readable through UI Automation here.
  & $code --new-window --disable-telemetry --force-renderer-accessibility $Folder | Out-Null
  Trace 'launched with --force-renderer-accessibility'

  $deadline = (Get-Date).AddSeconds(150); $win = $null
  while ((Get-Date) -lt $deadline -and -not $win) {
    Start-Sleep -Milliseconds 1500
    $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ClassNameProperty, 'Chrome_WidgetWin_1')
    foreach ($w in $AE::RootElement.FindAll($TS::Children, $cond)) {
      try { if ($w.Current.Name -match 'Visual Studio Code') { $win = $w; break } } catch { }
    }
  }
  if (-not $win) { Trace 'no window'; exit 2 }
  Trace "window=$($win.Current.Name)"
  $leaf = Split-Path $Folder -Leaf
  if ($win.Current.Name -notmatch [regex]::Escape($leaf)) { Trace 'refused: wrong folder'; exit 3 }

  Start-Sleep -Seconds 5
  $textCond = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty,
                [System.Windows.Automation.ControlType]::Text)
  $restricted = @()
  foreach ($t in $win.FindAll($TS::Descendants, $textCond)) { try { if ($t.Current.Name -match '受限模式|Restricted Mode') { $restricted += 1 } } catch { } }
  if ($restricted.Count -gt 0) { Trace 'still restricted; Lean would be inactive'; exit 4 }

  & $code --reuse-window --goto ('{0}:1' -f (Join-Path $Folder $File)) | Out-Null
  Start-Sleep -Seconds 8

  $summary = @()
  foreach ($target in $Targets) {
    $parts = $target.Split(':')
    $name = $parts[0]; $line = $parts[1]; $col = if ($parts.Count -ge 3) { $parts[2] } else { "1" }
    & $code --reuse-window --goto ('{0}:{1}:{2}' -f (Join-Path $Folder $File), $line, $col) | Out-Null
    $texts = @()
    for ($try = 0; $try -lt 12; $try++) {
      Start-Sleep -Seconds 2
      $texts = @()
      foreach ($t in $win.FindAll($TS::Descendants, $textCond)) {
        try { $v = $t.Current.Name; if ($v -match '(?i)no goals|goals accomplished|⊢|目标') { $texts += $v } } catch { }
      }
      if ($texts.Count -gt 0) { break }
    }
    $path = Join-Path $OutDir ("{0}.txt" -f $name)
    $n = Dump $win $AE $TS $path ("InfoView attempt at {0} (cursor line {1})" -f $name, $line)
    $hit = ($texts -join ' | ')
    Trace "$name line=$line nodes=$n hits=[$hit]"
    $summary += [pscustomobject]@{ name = $name; line = $line; nodes = $n; goal_text = $hit }
  }
  $summary | ConvertTo-Json -Depth 4 | Set-Content -Path (Join-Path $OutDir 'infoview-summary.json') -Encoding utf8
  Trace 'done'
  exit 0
} catch {
  Trace ("FAILED: " + $_.Exception.Message)
  exit 1
}
