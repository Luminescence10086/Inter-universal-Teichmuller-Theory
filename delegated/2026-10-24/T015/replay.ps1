# T015 · narrow read-only replay
#
# Scope: ONLY re-verify that the remote branch research/backward-paths still equals the
# reviewed commit d3c5599..., and re-emit the raw git evidence into logs/.
#
# Guarantees / limits (read before running):
#   * read-only: no checkout, no reset, no merge, no branch switch, no worktree add
#   * the only network operations are `git ls-remote` and `git fetch --dry-run`
#     (contact only; --dry-run writes no refs and no objects)
#   * writes ONLY inside this task directory (logs/)
#   * does NOT rebuild Lean, does NOT run any model, does NOT touch main source,
#     Boundary files, fact-tree or other task directories
#   * exit code 0 = all assertions hold (branch still consistent with d3c5599)
#               1 = at least one assertion failed (remote moved or repo changed)
#
# Usage:  pwsh -NoProfile -File replay.ps1                  # if PowerShell 7+ is installed
#         powershell -NoProfile -File replay.ps1            # Windows PowerShell 5.1
#         <either> -SkipNetwork                             # offline; skips ls-remote/fetch
#
# Verified on this machine with: powershell.exe 5.1.26100.9711 -NoProfile -File replay.ps1
# This file is kept pure ASCII: PS 5.1 decodes a BOM-less .ps1 as ANSI, so a literal
# non-ASCII path spelled in the source would be mangled. The repo root is derived from
# this script's own location instead: delegated/2026-10-24/T015/replay.ps1 -> repo root.

[CmdletBinding()]
param(
    [string]$Root = '',
    [string]$ReviewedSha = 'd3c5599668aa57c5c00244117abd26787fcd559e',
    [string]$BaselineSha = '8d60456043e30a3da79cc838d03a19b80675dc98',
    [string]$BaselineJsonSha256 = 'e24e6801c2eac58f7d97cfe5f3f7a95deeaf05852231006a0085290eecd126cf',
    [string]$Branch = 'research/backward-paths',
    [string]$ReviewedTree = '731cdae8a42f46a13d38a47f3cd5be0d06bad580',
    [string]$Layer5Blob = 'adc280bef846ca1e49b3a7b7071caaa725221797',
    [switch]$SkipNetwork
)

$ErrorActionPreference = 'Continue'

if ([string]::IsNullOrWhiteSpace($Root)) {
    $Root = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..\..')).Path
}
$Root = (Resolve-Path -LiteralPath $Root).Path

$TaskDir = Join-Path $Root 'delegated\2026-10-24\T015'
$LogDir  = Join-Path $TaskDir 'logs'
New-Item -ItemType Directory -Force -Path $LogDir | Out-Null

$GitExe  = (Get-Command git -ErrorAction Stop).Source
$Trace   = Join-Path $LogDir '_replay.trace.log'
$script:Failed = @()

function Quote-Arg {
    param([string]$A)
    if ($A -match '[\s"]') { return '"' + ($A -replace '"', '\"') + '"' }
    return $A
}

# Run git with true stdout/stderr separation. Start-Process is used instead of `& git`
# because PS 5.1 turns any native stderr output into a terminating NativeCommandError
# under ErrorActionPreference=Stop, and `git fetch --dry-run` legitimately writes progress
# to stderr.
function Invoke-Git {
    param([string]$Name, [string[]]$GitArgs)
    $stdout = Join-Path $LogDir "$Name.stdout.log"
    $stderr = Join-Path $LogDir "$Name.stderr.log"
    $argList = @('-C', (Quote-Arg $Root)) + ($GitArgs | ForEach-Object { Quote-Arg $_ })
    $proc = Start-Process -FilePath $GitExe -ArgumentList $argList -Wait -PassThru `
                          -NoNewWindow -RedirectStandardOutput $stdout -RedirectStandardError $stderr
    $code = $proc.ExitCode
    "`$ git -C `"$Root`" $($GitArgs -join ' ')   # exit=$code" | Add-Content -LiteralPath $Trace -Encoding utf8
    $out = ''
    $err = ''
    if (Test-Path $stdout) { $out = (Get-Content -LiteralPath $stdout -Raw -Encoding UTF8) }
    if (Test-Path $stderr) { $err = (Get-Content -LiteralPath $stderr -Raw -Encoding UTF8) }
    if ([string]::IsNullOrEmpty($out)) { $out = '' }
    if ($null -eq $err) { $err = '' }
    return [pscustomobject]@{ Exit = $code; Out = $out.Trim(); Err = $err.Trim(); OutFile = $stdout; ErrFile = $stderr }
}

function Assert-Equal {
    param([string]$Label, [string]$Actual, [string]$Expected)
    if ($Actual -eq $Expected) { Write-Host "[ OK ] $Label = $Actual" }
    else {
        Write-Host "[FAIL] $Label = '$Actual' (expected '$Expected')"
        $script:Failed += "$Label : got '$Actual' expected '$Expected'"
    }
}

function Assert-Zero {
    param([string]$Label, $Result)
    if ($Result.Exit -eq 0) { Write-Host "[ OK ] $Label (git exit 0)" }
    else {
        Write-Host "[FAIL] $Label (git exit $($Result.Exit)) $($Result.Err)"
        $script:Failed += "$Label : git exit $($Result.Exit)"
    }
}

Set-Content -LiteralPath $Trace -Value '' -Encoding utf8
Write-Host '== T015 replay :: read-only consistency check =='
Write-Host "root=$Root"

# --- 0. baseline file identity ------------------------------------------------
$baselinePath = Join-Path $Root 'handoffs\agent-batch-2026-10-24\baseline.json'
$baselineHash = (Get-FileHash -LiteralPath $baselinePath -Algorithm SHA256).Hash.ToLower()
Set-Content -LiteralPath (Join-Path $LogDir 'baseline.sha256.log') -Value $baselineHash -Encoding utf8
Assert-Equal 'baseline.json sha256' $baselineHash $BaselineJsonSha256

# --- 1. repository identity and HEAD -----------------------------------------
$top = Invoke-Git 'git-toplevel' @('rev-parse', '--show-toplevel'); Assert-Zero 'rev-parse --show-toplevel' $top
Assert-Equal 'toplevel' ($top.Out -replace '/', '\') $Root
$head = Invoke-Git 'git-head' @('rev-parse', 'HEAD'); Assert-Zero 'rev-parse HEAD' $head
Assert-Equal 'HEAD' $head.Out $BaselineSha

# --- 2. reviewed commit still resolves to the same object --------------------
$revC = Invoke-Git 'git-reviewed-commit' @('rev-parse', "$ReviewedSha^{commit}"); Assert-Zero 'rev-parse reviewed' $revC
Assert-Equal 'reviewed commit' $revC.Out $ReviewedSha
$revT = Invoke-Git 'git-reviewed-tree' @('rev-parse', "$ReviewedSha^{tree}"); Assert-Zero 'rev-parse reviewed tree' $revT
Assert-Equal 'reviewed tree' $revT.Out $ReviewedTree
$size = Invoke-Git 'git-layer5-blob-size' @('cat-file', '-s', "${ReviewedSha}:research/core-backward-2026-10-23/backward-paths-layer5-2026-10-23.md")
Assert-Zero 'cat-file -s layer5' $size
Assert-Equal 'layer5 blob size (bytes)' $size.Out '9132'

# --- 3. remote head (network, read-only) ------------------------------------
if (-not $SkipNetwork) {
    $ls = Invoke-Git 'git-ls-remote' @('ls-remote', 'origin', "refs/heads/$Branch"); Assert-Zero 'ls-remote' $ls
    Assert-Equal 'remote ls-remote' $ls.Out "$ReviewedSha`trefs/heads/$Branch"
    $dry = Invoke-Git 'git-fetch-dry-run' @('fetch', 'origin', $Branch, '--dry-run')
    Assert-Zero 'fetch --dry-run' $dry
    Write-Host "[ OK ] fetch --dry-run made no ref update (dry run; stderr in logs/git-fetch-dry-run.stderr.log)"
} else {
    Write-Host '[SKIP] network checks (ls-remote / fetch --dry-run)'
}

# --- 4. local branch and remote-tracking branch agree ------------------------
$lb = Invoke-Git 'git-local-branch' @('rev-parse', "refs/heads/$Branch"); Assert-Zero 'rev-parse local branch' $lb
Assert-Equal "local refs/heads/$Branch" $lb.Out $ReviewedSha
$tb = Invoke-Git 'git-track-branch' @('rev-parse', "refs/remotes/origin/$Branch"); Assert-Zero 'rev-parse tracking' $tb
Assert-Equal "remote-tracking origin/$Branch" $tb.Out $ReviewedSha

# --- 5. zero commits each way, empty diff -----------------------------------
$log = Invoke-Git 'git-log-oneline' @('log', '--oneline', '-8', "refs/remotes/origin/$Branch"); Assert-Zero 'log --oneline -8' $log
$fw = Invoke-Git 'git-count-forward' @('rev-list', '--count', "refs/heads/$Branch..refs/remotes/origin/$Branch"); Assert-Zero 'rev-list count forward' $fw
$bw = Invoke-Git 'git-count-backward' @('rev-list', '--count', "refs/remotes/origin/$Branch..refs/heads/$Branch"); Assert-Zero 'rev-list count backward' $bw
Assert-Equal 'new commits remote-side (reviewed..origin)' $fw.Out '0'
Assert-Equal 'new commits reviewed-side (origin..reviewed)' $bw.Out '0'
$st = Invoke-Git 'git-diff-stat' @('diff', '--stat', "refs/remotes/origin/$Branch", "refs/heads/$Branch"); Assert-Zero 'diff --stat origin vs reviewed' $st
Assert-Equal 'diff --stat origin vs reviewed' $st.Out ''

# --- 6. the reviewed commit's own shape (its layer-5 delivery) ---------------
$ds = Invoke-Git 'git-diff-stat-reviewed-commit' @('diff', '--stat', "$ReviewedSha^", $ReviewedSha); Assert-Zero 'diff --stat reviewed commit' $ds
if ($ds.Out -match '1 file changed, 145 insertions\(\+\)') { Write-Host '[ OK ] reviewed commit = 1 file changed, 145 insertions(+)' }
else { Write-Host "[FAIL] reviewed commit stat: $($ds.Out)"; $script:Failed += "reviewed commit stat: $($ds.Out)" }
$dt = Invoke-Git 'git-difftree-reviewed-commit' @('diff-tree', '--no-commit-id', '--name-status', "$ReviewedSha^", $ReviewedSha); Assert-Zero 'diff-tree reviewed commit' $dt
Assert-Equal 'reviewed commit touches' $dt.Out 'M	research'
$rd = Invoke-Git 'git-diff-stat-reviewed-vs-baseline' @('diff', '--stat', $BaselineSha, $ReviewedSha)
Assert-Zero 'diff --stat baseline..reviewed' $rd

# --- 7. layer-5 blob identity ------------------------------------------------
$l5 = Invoke-Git 'git-layer5-blob' @('rev-parse', "${ReviewedSha}:research/core-backward-2026-10-23/backward-paths-layer5-2026-10-23.md")
Assert-Zero 'rev-parse layer5 blob' $l5
Assert-Equal 'layer5 blob oid' $l5.Out $Layer5Blob

# --- 8. main worktree still has exactly the four known tracked dirty files ---
$por = Invoke-Git 'git-status-porcelain' @('status', '--porcelain', '--untracked-files=no'); Assert-Zero 'status --porcelain' $por
$dirty = @($por.Out -split "`r?`n" | Where-Object { $_.Trim() -ne '' })
Assert-Equal 'tracked dirty file count' "$($dirty.Count)" '4'

# --- verdict ----------------------------------------------------------------
Write-Host ''
if ($script:Failed.Count -eq 0) {
    Write-Host "T015_REPLAY_PASS: remote $Branch == $ReviewedSha (0 new commits; empty diff)"
    exit 0
}
Write-Host "T015_REPLAY_FAIL: $($script:Failed.Count) assertion(s) failed"
$script:Failed | ForEach-Object { Write-Host "  - $_" }
exit 1
