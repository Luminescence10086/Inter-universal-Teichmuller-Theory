# capture-problems.ps1 -- read the actual diagnostic text out of the running VS Code window.
# Attempt 2 proved the editor reports 1 problem for DelegatedLogBridge.lean while the CLI
# reports zero; this script opens the Problems panel and dumps the message verbatim.
param(
  [string]$Root = '',
  [string]$OutDir = ''
)

function Trace([string]$m) { Add-Content -Path (Join-Path $env:TEMP 'capture-problems.log') -Value ("{0} {1}" -f (Get-Date -Format 'HH:mm:ss'), $m) }
Set-Content -Path (Join-Path $env:TEMP 'capture-problems.log') -Value "start $(Get-Date -Format o)"

try {
  if (-not $Root) { $Root = (Get-Location).Path }
  if (-not $OutDir) { $OutDir = Join-Path (Join-Path (Join-Path $Root 'handoffs') 'core-support-2026-10-22') 'T3' }
  Add-Type -AssemblyName UIAutomationClient
  Add-Type -AssemblyName UIAutomationTypes
  Add-Type -AssemblyName System.Windows.Forms
  $AE = [System.Windows.Automation.AutomationElement]
  $TS = [System.Windows.Automation.TreeScope]

  $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ClassNameProperty, 'Chrome_WidgetWin_1')
  $win = $null
  foreach ($w in $AE::RootElement.FindAll($TS::Children, $cond)) {
    try { if ($w.Current.Name -match 'Visual Studio Code') { $win = $w; break } } catch { }
  }
  if (-not $win) { Trace 'no window'; exit 2 }
  Trace "window=$($win.Current.Name)"

  # Clicking the status-bar error count opens the Problems view; that needs no keyboard focus,
  # unlike SendKeys (the window element itself refuses SetFocus).
  $clicked = $null
  $btnCond = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty,
               [System.Windows.Automation.ControlType]::Button)
  foreach ($b in $win.FindAll($TS::Descendants, $btnCond)) {
    try {
      if ($b.Current.Name -match '错误|Errors?|警告') {
        $b.GetCurrentPattern([System.Windows.Automation.InvokePattern]::Pattern).Invoke()
        $clicked = $b.Current.Name; break
      }
    } catch { }
  }
  Trace "clicked=$clicked"
  if (-not $clicked) {
    Add-Type -AssemblyName Microsoft.VisualBasic
    try { [Microsoft.VisualBasic.Interaction]::AppActivate($win.Current.ProcessId) | Out-Null
          Start-Sleep -Seconds 1
          [System.Windows.Forms.SendKeys]::SendWait('^+m')
          Trace 'sent ctrl+shift+m after AppActivate' } catch { Trace "activate failed: $($_.Exception.Message)" }
  }
  Start-Sleep -Seconds 3

  $sb = New-Object System.Text.StringBuilder
  [void]$sb.AppendLine("### Problems view capture, $(Get-Date -Format o)")
  [void]$sb.AppendLine("### window: $($win.Current.Name)")
  $count = 0; $stack = New-Object System.Collections.Stack; $stack.Push(@($win, 0))
  while ($stack.Count -gt 0 -and $count -lt 8000) {
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
  $sb.ToString() | Set-Content -Path (Join-Path $OutDir 'vscode-problems-panel.txt') -Encoding utf8
  Trace "captured nodes=$count"
  exit 0
} catch {
  Trace ("FAILED: " + $_.Exception.Message)
  exit 1
}
