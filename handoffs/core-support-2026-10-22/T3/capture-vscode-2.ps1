# capture-vscode-2.ps1 -- open a Lake workspace, wait for the Lean 4 extension, dump the real
# accessibility tree of the VS Code main window.
#
# ASCII-only on purpose, twice over:
#   * PowerShell 5.1 decodes BOM-less UTF-8 as ANSI, so non-ASCII literals in this file would
#     become wrong paths/patterns;
#   * an earlier revision was patched through Get-Content/Set-Content and its Chinese patterns
#     were double-encoded into mojibake, which would have made the restricted-mode check silently
#     false. Localised UI strings are therefore written as \uXXXX regex escapes.
#
# It refuses to fabricate a verdict: wrong folder, restricted window, or missing tab all exit non-zero.
param(
  [string]$Root = '',
  [string]$Folder = '',
  [string]$File = 'DelegatedLogBridge.lean',
  [string]$OutDir = '',
  [int]$SettleSeconds = 240,
  [int]$PollSeconds = 5
)

$bootstrap = Join-Path $env:TEMP 'capture-vscode-2-bootstrap.log'
function Trace([string]$m) { Add-Content -Path $bootstrap -Value ("{0} {1}" -f (Get-Date -Format 'HH:mm:ss'), $m) }
Set-Content -Path $bootstrap -Value "start $(Get-Date -Format o)"

# UI strings, spelled as regex escapes: restricted mode, trust, manage, problems.
$RE_RESTRICTED = 'Restricted Mode|\u53D7\u9650\u6A21\u5F0F'
$RE_TRUST      = '\u4FE1\u4EFB|Trust'
$RE_MANAGE     = '^(\u7BA1\u7406|Manage)$'
$RE_PROBLEMS   = '\u95EE\u9898|\u9519\u8BEF|\u8B66\u544A|Problems|error|warning'

function Find-Window($AE, $TS) {
  $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ClassNameProperty, 'Chrome_WidgetWin_1')
  foreach ($w in $AE::RootElement.FindAll($TS::Children, $cond)) {
    try { if ($w.Current.Name -match 'Visual Studio Code') { return $w } } catch { }
  }
  return $null
}

function Invoke-ByName($root, $AE, $TS, [string]$pattern, [string]$controlType) {
  $type = [System.Windows.Automation.ControlType]::$controlType
  $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty, $type)
  foreach ($el in $root.FindAll($TS::Descendants, $cond)) {
    try { if ($el.Current.Name -match $pattern) {
      $el.GetCurrentPattern([System.Windows.Automation.InvokePattern]::Pattern).Invoke(); return $el.Current.Name } } catch { }
  }
  return $null
}

function Get-Texts($root, $AE, $TS, [string]$pattern) {
  $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty,
            [System.Windows.Automation.ControlType]::Text)
  $out = @()
  foreach ($t in $root.FindAll($TS::Descendants, $cond)) {
    try { if ($t.Current.Name -match $pattern) { $out += $t.Current.Name } } catch { }
  }
  return $out
}

try {
  if (-not $Root)   { $Root = (Get-Location).Path }
  if (-not $Folder) { $Folder = Join-Path (Join-Path $Root 'candidates') 'core-transport' }
  if (-not $OutDir) { $OutDir = Join-Path (Join-Path (Join-Path $Root 'handoffs') 'core-support-2026-10-22') 'T3' }
  $leaf = Split-Path $Folder -Leaf
  $filePath = Join-Path $Folder $File
  New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
  $log = Join-Path $OutDir 'vscode-capture-2.log'
  "=== attempt 2 start $(Get-Date -Format o) ===" | Set-Content -Path $log -Encoding utf8
  "folder: $Folder" | Add-Content $log
  "file:   $File (exists: $(Test-Path $filePath))" | Add-Content $log

  Add-Type -AssemblyName UIAutomationClient
  Add-Type -AssemblyName UIAutomationTypes
  $AE = [System.Windows.Automation.AutomationElement]
  $TS = [System.Windows.Automation.TreeScope]

  Get-Process Code -ErrorAction SilentlyContinue | Stop-Process -Force
  Start-Sleep -Seconds 3
  $code = Join-Path (Join-Path $env:LOCALAPPDATA 'Programs\Microsoft VS Code\bin') 'code.cmd'
  & $code --new-window --disable-telemetry $Folder | Out-Null
  Trace 'launched with quoted folder'

  $deadline = (Get-Date).AddSeconds(120); $win = $null
  while ((Get-Date) -lt $deadline -and -not $win) { Start-Sleep -Milliseconds 1500; $win = Find-Window $AE $TS }
  if (-not $win) { 'NO_WINDOW' | Add-Content $log; Trace 'no window'; exit 2 }

  # a freshly launched window is titled just "Visual Studio Code" until the folder loads
  $deadlineT = (Get-Date).AddSeconds(120)
  while ($win -and ($win.Current.Name -notmatch [regex]::Escape($leaf)) -and (Get-Date) -lt $deadlineT) {
    Start-Sleep -Seconds 2
    $win = Find-Window $AE $TS
  }
  if (-not $win) { 'NO_WINDOW' | Add-Content $log; exit 2 }
  $title = $win.Current.Name
  "window: $title" | Add-Content $log
  Trace "window=$title"
  if ($title -notmatch [regex]::Escape($leaf)) {
    "REFUSED: window title does not name the folder ($title, expected '$leaf')" | Add-Content $log
    Trace 'refused: wrong folder'
    exit 3
  }

  Start-Sleep -Seconds 5
  $trusted = $false
  for ($i = 0; $i -lt 6 -and -not $trusted; $i++) {
    $banner = Get-Texts $win $AE $TS $RE_RESTRICTED
    if (-not $banner) { $trusted = $true; break }
    $manage = Invoke-ByName $win $AE $TS $RE_MANAGE 'Button'
    "step $i manage=$manage banner=$($banner.Count)" | Add-Content $log
    Start-Sleep -Seconds 2
    $a = Invoke-ByName $win $AE $TS $RE_TRUST 'ListItem'
    if (-not $a) { $a = Invoke-ByName $win $AE $TS $RE_TRUST 'MenuItem' }
    if (-not $a) { $a = Invoke-ByName $win $AE $TS $RE_TRUST 'Button' }
    "step $i trustAction=$a" | Add-Content $log
    Start-Sleep -Seconds 3
  }
  $stillRestricted = (Get-Texts $win $AE $TS $RE_RESTRICTED).Count -gt 0
  "trusted=$trusted stillRestricted=$stillRestricted" | Add-Content $log
  if ($stillRestricted) {
    'REFUSED: window still in restricted mode; Lean extension inactive' | Add-Content $log
    Trace 'refused: restricted'
    exit 4
  }

  & $code --reuse-window --goto ('{0}:1' -f $filePath) | Out-Null
  Start-Sleep -Seconds 8
  $tabs = @()
  $cond = New-Object System.Windows.Automation.PropertyCondition($AE::ControlTypeProperty,
            [System.Windows.Automation.ControlType]::TabItem)
  foreach ($t in $win.FindAll($TS::Descendants, $cond)) { try { $tabs += $t.Current.Name } catch { } }
  "tabs: $($tabs -join ' | ')" | Add-Content $log
  $tabLeaf = [regex]::Escape((Split-Path $File -Leaf))
  if (-not ($tabs | Where-Object { $_ -match $tabLeaf })) {
    'REFUSED: the file tab is not present' | Add-Content $log; Trace 'refused: no tab'; exit 5
  }

  $deadline = (Get-Date).AddSeconds($SettleSeconds); $last = ''; $stable = 0
  while ((Get-Date) -lt $deadline) {
    $hits = Get-Texts $win $AE $TS $RE_PROBLEMS
    $cur = ($hits -join ' || ')
    if ($cur -eq $last) { $stable++ } else { $stable = 0; $last = $cur }
    "poll $((Get-Date).ToString('HH:mm:ss')) stable=$stable status=[$cur]" | Add-Content $log
    if ($stable -ge 4) { break }
    Start-Sleep -Seconds $PollSeconds
  }
  Trace "settled stable=$stable"

  $sb = New-Object System.Text.StringBuilder
  [void]$sb.AppendLine("### VS Code accessibility tree, captured $(Get-Date -Format o)")
  [void]$sb.AppendLine("### window: $title")
  $count = 0; $stack = New-Object System.Collections.Stack; $stack.Push(@($win, 0))
  while ($stack.Count -gt 0 -and $count -lt 6000) {
    $item = $stack.Pop(); $el = $item[0]; $depth = $item[1]
    try {
      $c = $el.Current
      $nm = ($c.Name -replace '\s+', ' ').Trim()
      if ($nm.Length -gt 240) { $nm = $nm.Substring(0, 240) + '...' }
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
  $sb.ToString() | Set-Content -Path (Join-Path $OutDir 'vscode-observation-tree-2.txt') -Encoding utf8
  "tree captured: $count nodes" | Add-Content $log
  Trace "done nodes=$count"
  exit 0
} catch {
  Trace ("FAILED: " + $_.Exception.Message)
  exit 1
}
