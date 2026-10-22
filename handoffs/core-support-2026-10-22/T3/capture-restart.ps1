# capture-restart.ps1 -- drive the Lean 4 extension's own "Restart File" command, then re-read
# the Problems panel. The diagnostic we captured says, in the editor's own words, that imports
# are out of date and that "Restart File" is the remedy; doing exactly that is the honest next
# step, and the re-capture decides whether the error was a stale-artifact guard or something real.
param(
  [string]$Root = '',
  [string]$OutDir = '',
  [int]$WaitSeconds = 90
)

function Trace([string]$m) { Add-Content -Path (Join-Path $env:TEMP 'capture-restart.log') -Value ("{0} {1}" -f (Get-Date -Format 'HH:mm:ss'), $m) }
Set-Content -Path (Join-Path $env:TEMP 'capture-restart.log') -Value "start $(Get-Date -Format o)"

function Dump-Window($win, $AE, $TS, [string]$path, [string]$header) {
  $sb = New-Object System.Text.StringBuilder
  [void]$sb.AppendLine("### $header $(Get-Date -Format o)")
  [void]$sb.AppendLine("### window: $($win.Current.Name)")
  $count = 0; $stack = New-Object System.Collections.Stack; $stack.Push(@($win, 0))
  while ($stack.Count -gt 0 -and $count -lt 9000) {
    $item = $stack.Pop(); $el = $item[0]; $depth = $item[1]
    try {
      $c = $el.Current
      $nm = ($c.Name -replace '\s+', ' ').Trim()
      if ($nm.Length -gt 400) { $nm = $nm.Substring(0, 400) + '...' }
      [void]$sb.AppendLine(('{0}{1} | {2}' -f ('  ' * [Math]::Min($depth, 20)), $c.ControlType.ProgrammaticName, $nm))
      $count++
    } catch { }
    if ($depth -ge 16) { continue }
    try {
      $kids = $el.FindAll($TS::Children, [System.Windows.Automation.Condition]::TrueCondition)
      for ($i = $kids.Count - 1; $i -ge 0; $i--) { $stack.Push(@($kids[$i], $depth + 1)) }
    } catch { }
  }
  [void]$sb.AppendLine("### nodes: $count")
  $sb.ToString() | Set-Content -Path $path -Encoding utf8
  return $count
}

function Invoke-Named($win, $AE, $TS, [string]$pattern, [string]$controlType) {
  $type = [System.Windows.Automation.ControlType]::$controlType
  $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty, $type)
  foreach ($el in $win.FindAll($TS::Descendants, $cond)) {
    try { if ($el.Current.Name -match $pattern) {
      $el.GetCurrentPattern([System.Windows.Automation.InvokePattern]::Pattern).Invoke(); return $el.Current.Name } } catch { }
  }
  return $null
}

try {
  if (-not $Root) { $Root = (Get-Location).Path }
  if (-not $OutDir) { $OutDir = Join-Path (Join-Path (Join-Path $Root 'handoffs') 'core-support-2026-10-22') 'T3' }
  Add-Type -AssemblyName UIAutomationClient
  Add-Type -AssemblyName UIAutomationTypes
  Add-Type -AssemblyName System.Windows.Forms
  Add-Type -AssemblyName Microsoft.VisualBasic
  $AE = [System.Windows.Automation.AutomationElement]
  $TS = [System.Windows.Automation.TreeScope]

  $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ClassNameProperty, 'Chrome_WidgetWin_1')
  $win = $null
  foreach ($w in $AE::RootElement.FindAll($TS::Children, $cond)) {
    try { if ($w.Current.Name -match 'Visual Studio Code') { $win = $w; break } } catch { }
  }
  if (-not $win) { Trace 'no window'; exit 2 }
  Trace "window=$($win.Current.Name)"

  # path 1: the Lean 4 status-bar item has a menu that contains Restart File
  $leanBtn = Invoke-Named $win $AE $TS '^Lean 4$' 'Button'
  Trace "lean status button=$leanBtn"
  Start-Sleep -Seconds 2
  $restart = Invoke-Named $win $AE $TS 'Restart File|重启文件|重新启动文件' 'ListItem'
  if (-not $restart) { $restart = Invoke-Named $win $AE $TS 'Restart File|重启文件' 'MenuItem' }
  Trace "restart via menu=$restart"

  if (-not $restart) {
    # path 2: command palette
    [Microsoft.VisualBasic.Interaction]::AppActivate($win.Current.ProcessId) | Out-Null
    Start-Sleep -Milliseconds 800
    [System.Windows.Forms.SendKeys]::SendWait('^+p')
    Start-Sleep -Milliseconds 1200
    [System.Windows.Forms.SendKeys]::SendWait('Lean 4: Restart File')
    Start-Sleep -Milliseconds 1500
    [System.Windows.Forms.SendKeys]::SendWait('~')
    Trace 'palette route sent'
    Start-Sleep -Seconds 2
  }

  Dump-Window $win $AE $TS (Join-Path $OutDir 'vscode-after-restart-action.txt') 'immediately after Restart File' | Out-Null

  # wait for the server to settle, then dump again
  $deadline = (Get-Date).AddSeconds($WaitSeconds); $last = ''; $stable = 0
  while ((Get-Date) -lt $deadline) {
    $cond2 = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty,
               [System.Windows.Automation.ControlType]::Text)
    $hits = @()
    foreach ($t in $win.FindAll($TS::Descendants, $cond2)) {
      try { if ($t.Current.Name -match '(?i)问题|个错误|Lean|Info') { $hits += $t.Current.Name } } catch { }
    }
    $cur = ($hits -join ' || ')
    if ($cur -eq $last) { $stable++ } else { $stable = 0; $last = $cur }
    Trace "poll stable=$stable [$cur]"
    if ($stable -ge 4) { break }
    Start-Sleep -Seconds 5
  }

  $n = Dump-Window $win $AE $TS (Join-Path $OutDir 'vscode-observation-after-restart.txt') 'after Restart File settled'
  Trace "final dump nodes=$n"
  exit 0
} catch {
  Trace ("FAILED: " + $_.Exception.Message)
  exit 1
}
