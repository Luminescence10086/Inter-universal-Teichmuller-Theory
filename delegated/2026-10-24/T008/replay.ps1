# T008 replay.ps1 - narrow replay of this task's explicit target ONLY.
#
# WHAT THIS DOES
#   Runs delegated/2026-10-24/T008/probe/T008Probe.lean through the already-built
#   `candidates/core-kummer` Lake workspace and prints the #check / #print axioms trace.
#
# WHAT THIS DOES NOT DO
#   - no `lake build` of anything (does not touch candidates/core-kummer/.lake)
#   - no download, no upgrade, no `git checkout`, no clean, no dependency change
#   - no edit of any file outside this task directory
#
# READ THIS BEFORE RUNNING. It only re-verifies a type ledger. It cannot and does not
# prove any new mathematics, and a PASS here is not a fact-tree admission.

[CmdletBinding()]
param(
    [string]$Root = '',
    [string]$LeanProject = ''
)

$ErrorActionPreference = 'Stop'

# Default root is derived from this script's own location: the task directory is
# <root>/delegated/2026-10-24/T008, so the repository root is three levels up.
# Pass -Root explicitly only when the tree was copied somewhere else. (The live root
# contains non-ASCII characters, so it is derived rather than hard-coded.)
if (-not $Root) {
    $Root = Split-Path -Parent (Split-Path -Parent (Split-Path -Parent $PSScriptRoot))
}
if (-not (Test-Path $Root)) { throw "Root not found: $Root" }

$TaskDir = Join-Path $Root 'delegated\2026-10-24\T008'
if (-not $LeanProject) { $LeanProject = Join-Path $Root 'candidates\core-kummer' }

$Probe    = Join-Path $TaskDir 'probe\T008Probe.lean'
$LogDir   = Join-Path $TaskDir 'logs'
$OutFile  = Join-Path $LogDir 'replay.stdout.log'
$ErrFile  = Join-Path $LogDir 'replay.stderr.log'

Write-Host "root      : $Root"
Write-Host "lean proj : $LeanProject"
Write-Host "probe     : $Probe"

foreach ($p in @($Probe, $LeanProject)) {
    if (-not (Test-Path $p)) { throw "missing required path: $p" }
}
New-Item -ItemType Directory -Force -Path $LogDir | Out-Null

# --- pinned input hashes this replay is meaningful against -------------------
$pinned = @{
    'candidates\core-kummer\ContinuousKummerTheory\Kummer\Decomposition.lean'           = 'b7a67da60e61998d631201b3053aadea387993c68984dd1e14a3f5d9d446b7a6'
    'candidates\core-kummer\ContinuousKummerTheory\Kummer\DecompositionSurjective.lean' = '88f59d79f06050aaa6a2838eb8c33fe5fd94b6426034f582259a934d9ec3e3f8'
    'candidates\core-kummer\ContinuousKummerTheory\ContH1\Basic.lean'                   = 'a0c0e0ada763df8c664bd5f11d548c30025e4a3855c8c7e9aa53eacb4e41a59c'
    'candidates\core-kummer\Boundary\ReducedComparison.lean'                            = '40b6c22138ffeff4b6c78b58a28ef54d90779b980c8f7e6735f5d9ae24219edf'
    'candidates\core-kummer\CohomologyReflection.lean'                                  = '0c5476c9993fcf960a7748c0b4643386bf9291640bd03582483b217f0b55d8a3'
    'probe\T008Probe.lean'                                                              = $null   # printed, not asserted
}
$drift = $false
foreach ($rel in $pinned.Keys | Sort-Object) {
    $full = if ($rel -like 'probe\*') { Join-Path $TaskDir $rel } else { Join-Path $Root $rel }
    if (-not (Test-Path $full)) { Write-Host "DRIFT   $rel  MISSING"; $drift = $true; continue }
    $h = (Get-FileHash -Algorithm SHA256 -Path $full).Hash.ToLower()
    if ($null -eq $pinned[$rel]) {
        Write-Host "probe   $rel  $h"
    } elseif ($h -eq $pinned[$rel]) {
        Write-Host "ok      $rel  $h"
    } else {
        Write-Host "DRIFT   $rel  $h  (expected $($pinned[$rel]))"
        $drift = $true
    }
}
if ($drift) {
    Write-Warning 'Input drift detected. The recorded PASS no longer applies to these bytes; results below are informational only.'
}

# --- the single command this task owns --------------------------------------
$sw = [System.Diagnostics.Stopwatch]::StartNew()
Push-Location $LeanProject
try {
    & lake env lean -DwarningAsError=true $Probe 1> $OutFile 2> $ErrFile
    $code = $LASTEXITCODE
} finally {
    Pop-Location
}
$sw.Stop()

Write-Host ''
Write-Host "exit      : $code"
Write-Host "seconds   : $([math]::Round($sw.Elapsed.TotalSeconds,2))"
Write-Host "stdout    : $OutFile"
Write-Host "stderr    : $ErrFile"

$errs = Select-String -Path $OutFile, $ErrFile -Pattern 'error' -ErrorAction SilentlyContinue
$sorry = Select-String -Path $OutFile, $ErrFile -Pattern ': sorry|sorryAx' -ErrorAction SilentlyContinue
Write-Host "errors    : $(@($errs).Count)"
Write-Host "sorry     : $(@($sorry).Count)"

Write-Host ''
Write-Host '--- axiom report ---'
Select-String -Path $OutFile -Pattern 'depends on axioms|does not depend on any axioms' |
    ForEach-Object { $_.Line }

if ($code -ne 0) { throw "probe failed with exit $code (see $OutFile)" }
if (@($errs).Count -gt 0) { throw "probe printed errors (see $OutFile)" }
if (@($sorry).Count -gt 0) { throw "probe mentions sorry (see $OutFile)" }

Write-Host ''
Write-Host 'PASS: type ledger re-checked. This is NOT a mathematical result and NOT a fact-tree admission.'
