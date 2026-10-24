# T097 — replay script (read-only, offline, idempotent)
#
# WHAT THIS DOES
#   Runs delegated/2026-10-24/T097/T097_audit.py, which re-checks every citation in
#   quantifiers.json against the bytes of the baseline-pinned sources, and writes the
#   actual stdout/stderr of that run into logs/.
#
# WHAT THIS DOES NOT DO
#   * no network access, no downloads, no package installs
#   * no `git fetch`, no branch switch, no checkout, no `git clean`, no reset
#   * no Lean / lake invocation (T097 is SOURCE_OR_ENGINEERING; see unresolved U5)
#   * no write anywhere except logs/ inside this task directory
#   * no modification of the main-line source, Boundary files, fact-tree, or any other
#     task directory
#
# READ THIS FIRST, THEN RUN.
#   Audit the script before executing it, per PROTOCOL.md ("接收方先读脚本，再决定运行").
#
# EXPECTED RESULT
#   exit code 0 and stdout containing "ALL_ANCHORS_VERIFIED".
#   That means the transcription matches the cited bytes. It is NOT evidence that
#   Wall (9-1) is true, and it is not a Lean or editor acceptance.

[CmdletBinding()]
param(
    # Defaults are resolved in the body: Windows PowerShell 5.1 does not populate
    # $PSScriptRoot while a param() default is being evaluated under -File.
    [string] $RepoRoot,
    [string] $Python = 'python'
)

$ErrorActionPreference = 'Stop'
$here = $PSScriptRoot
if (-not $here) { $here = Split-Path -Parent $MyInvocation.MyCommand.Definition }
if (-not $RepoRoot) { $RepoRoot = (Resolve-Path (Join-Path $here '..\..\..')).Path }
$logDir = Join-Path $here 'logs'
New-Item -ItemType Directory -Force -Path $logDir | Out-Null

$audit = Join-Path $here 'T097_audit.py'
$ledger = Join-Path $here 'quantifiers.json'

if (-not (Test-Path -LiteralPath $audit)) { throw "missing: $audit" }
if (-not (Test-Path -LiteralPath $ledger)) { throw "missing: $ledger" }

# Pin what we are about to replay, so the logs can be tied to these exact bytes.
$pinned = [ordered]@{}
foreach ($f in @($audit, $ledger)) {
    $pinned[(Split-Path $f -Leaf)] = (Get-FileHash -Algorithm SHA256 -LiteralPath $f).Hash.ToLower()
}
$pinned.GetEnumerator() | ForEach-Object { "PIN  $($_.Key)  $($_.Value)" } |
    Set-Content -LiteralPath (Join-Path $logDir 'replay.pins.log') -Encoding utf8

$argv = @($audit, '--root', $RepoRoot, '--ledger', $ledger)
"ARGV  $Python $($argv -join ' ')" | Set-Content -LiteralPath (Join-Path $logDir 'replay.argv.log') -Encoding utf8
"CWD   $RepoRoot"                 | Add-Content -LiteralPath (Join-Path $logDir 'replay.argv.log') -Encoding utf8

$sw = [System.Diagnostics.Stopwatch]::StartNew()
$out = Join-Path $logDir 'audit.stdout.log'
$err = Join-Path $logDir 'audit.stderr.log'

# The verifier prints maths and CJK quoted from the sources. Force UTF-8 for the child
# process so a non-UTF-8 console code page cannot turn a passing audit into a fake failure.
$env:PYTHONIOENCODING = 'utf-8'
$env:PYTHONUTF8 = '1'

Push-Location $RepoRoot
try {
    # The call operator is used (not Start-Process) because -ArgumentList re-splits on
    # spaces, and the repo path contains a space. Native stderr redirection to a file is
    # safe here: PS 5.1 does not promote a native child's stderr to a terminating error.
    & $Python @argv 1> $out 2> $err
    $code = $LASTEXITCODE
}
finally {
    $sw.Stop()
    Pop-Location
}

[ordered]@{
    argv             = @($Python) + $argv
    cwd              = $RepoRoot
    exit_code        = $code
    duration_seconds = [math]::Round($sw.Elapsed.TotalSeconds, 3)
    stdout           = 'logs/audit.stdout.log'
    stderr           = 'logs/audit.stderr.log'
} | ConvertTo-Json | Set-Content -LiteralPath (Join-Path $logDir 'audit.run.json') -Encoding utf8

Get-Content -LiteralPath $out
if ((Get-Item -LiteralPath $err).Length -gt 0) {
    Write-Host '--- stderr ---'
    Get-Content -LiteralPath $err
}
Write-Host "exit code: $code"
exit $code
