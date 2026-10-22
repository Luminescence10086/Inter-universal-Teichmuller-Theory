# capture-vscode.ps1 (ASCII-only on purpose: PowerShell 5.1 decodes BOM-less UTF-8 as ANSI,
# so a non-ASCII literal in this file silently becomes a wrong path).
# Opens the core-transport Lake workspace, waits for the Lean 4 extension, then dumps the real
# accessibility tree of the VS Code main window. It refuses to invent a verdict.
param(
  [string]$Root    = '',
  [string]$Folder  = '',
  [string]$File    = 'DelegatedLogBridge.lean',
  [string]$OutDir  = '',
  [int]$SettleSeconds = 240,
  [int]$PollSeconds   = 5
)

$bootstrap = Join-Path $env:TEMP 'capture-vscode-bootstrap.log'
function Trace([string]$m) { Add-Content -Path $bootstrap -Value ("{0} {1}" -f (Get-Date -Format 'HH:mm:ss'), $m) }
Set-Content -Path $bootstrap -Value "start $(Get-Date -Format o)"

try {
  if (-not $Root)   { $Root = (Get-Location).Path }
  if (-not $Folder) { $Folder = Join-Path (Join-Path $Root 'candidates') 'core-transport' }
  if (-not $OutDir) { $OutDir = Join-Path (Join-Path (Join-Path $Root 'handoffs') 'core-support-2026-10-22') 'T3' }
  Trace "root=$Root"
  Trace "folder=$Folder"
  Trace "outdir=$OutDir"

  Add-Type -AssemblyName UIAutomationClient
  Add-Type -AssemblyName UIAutomationTypes
  Trace 'UIA loaded'

  $AE = [System.Windows.Automation.AutomationElement]
  $TS = [System.Windows.Automation.TreeScope]

  New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
  $log = Join-Path $OutDir 'vscode-capture.log'
  "=== capture start $(Get-Date -Format o) ===" | Set-Content -Path $log -Encoding utf8
  "folder: $Folder" | Add-Content $log
  "file:   $File (exists: $(Test-Path (Join-Path $Folder $File)))" | Add-Content $log

  $code = Join-Path (Join-Path $env:LOCALAPPDATA 'Programs\Microsoft VS Code\bin') 'code.cmd'
  Trace "code=$code exists=$(Test-Path $code)"

  Start-Process -FilePath $code -ArgumentList @('--new-window', '--disable-telemetry', $Folder) | Out-Null
  Trace 'launched'

  $deadline = (Get-Date).AddSeconds(120)
  $win = $null
  while ((Get-Date) -lt $deadline -and -not $win) {
    Start-Sleep -Milliseconds 1500
    $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ClassNameProperty, 'Chrome_WidgetWin_1')
    $wins = $AE::RootElement.FindAll($TS::Children, $cond)
    foreach ($w in $wins) { if ($w.Current.Name -match 'Visual Studio Code') { $win = $w; break } }
  }
  if (-not $win) { 'NO_WINDOW' | Add-Content $log; Trace 'no window'; exit 2 }
  $winName = $win.Current.Name
  "window: $winName" | Add-Content $log
  Trace "window=$winName"

  Start-Sleep -Seconds 4
  $btnCond = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty,
              [System.Windows.Automation.ControlType]::Button)
  $buttons = $win.FindAll($TS::Descendants, $btnCond)
  foreach ($b in $buttons) {
    if ($b.Current.Name -match 'trust the authors|^Trust') {
      try { $b.GetCurrentPattern([System.Windows.Automation.InvokePattern]::Pattern).Invoke()
            "trust prompt: $($b.Current.Name)" | Add-Content $log; Start-Sleep -Seconds 5 } catch { }
    }
  }

  Start-Process -FilePath $code -ArgumentList @('--reuse-window', '--goto', ('{0}:1' -f (Join-Path $Folder $File))) | Out-Null
  Start-Sleep -Seconds 8
  Trace 'file opened'

  $deadline = (Get-Date).AddSeconds($SettleSeconds)
  $last = ''; $stable = 0
  while ((Get-Date) -lt $deadline) {
    $hits = @()
    $textCond = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty,
                  [System.Windows.Automation.ControlType]::Text)
    foreach ($t in $win.FindAll($TS::Descendants, $textCond)) {
      try { if ($t.Current.Name -match '(?i)lean|error|warning|problem|checking|building') { $hits += $t.Current.Name } } catch { }
    }
    $cur = ($hits -join ' || ')
    if ($cur -eq $last) { $stable++ } else { $stable = 0; $last = $cur }
    "poll $((Get-Date).ToString('HH:mm:ss')) stable=$stable status=[$cur]" | Add-Content $log
    if ($stable -ge 3) { break }
    Start-Sleep -Seconds $PollSeconds
  }
  Trace "settled stable=$stable"

  $sb = New-Object System.Text.StringBuilder
  [void]$sb.AppendLine("### VS Code accessibility tree, captured $(Get-Date -Format o)")
  [void]$sb.AppendLine("### window: $winName")
  $count = 0
  $stack = New-Object System.Collections.Stack
  $stack.Push(@($win, 0))
  while ($stack.Count -gt 0 -and $count -lt 4000) {
    $item = $stack.Pop(); $el = $item[0]; $depth = $item[1]
    try {
      $cur2 = $el.Current
      $nm = ($cur2.Name -replace '\s+', ' ').Trim()
      if ($nm.Length -gt 220) { $nm = $nm.Substring(0, 220) + '...' }
      [void]$sb.AppendLine(('{0}{1} | {2}' -f ('  ' * [Math]::Min($depth, 20)), $cur2.ControlType.ProgrammaticName, $nm))
      $count++
    } catch { }
    if ($depth -ge 14) { continue }
    try {
      $kids = $el.FindAll($TS::Children, [System.Windows.Automation.Condition]::TrueCondition)
      for ($i = $kids.Count - 1; $i -ge 0; $i--) { $stack.Push(@($kids[$i], $depth + 1)) }
    } catch { }
  }
  [void]$sb.AppendLine("### nodes: $count")
  $sb.ToString() | Set-Content -Path (Join-Path $OutDir 'vscode-observation-tree.txt') -Encoding utf8
  "tree captured: $count nodes" | Add-Content $log
  "=== capture end $(Get-Date -Format o) ===" | Add-Content $log
  Trace "done nodes=$count"
  exit 0
} catch {
  Trace ("FAILED: " + $_.Exception.GetType().FullName + ': ' + $_.Exception.Message)
  Trace ("at: " + $_.InvocationInfo.PositionMessage)
  exit 1
}
