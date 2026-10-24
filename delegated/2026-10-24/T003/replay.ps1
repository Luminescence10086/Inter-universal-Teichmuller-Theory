# T003 replay — read-only Mathlib PowerSeries substitution API retrieval.
#
# Reads:  <Mathlib>/Mathlib/RingTheory/PowerSeries/{Substitution,Basic,Inverse,Order,Evaluation,Expand}.lean
#         <Mathlib>/Mathlib/RingTheory/MvPowerSeries/Substitution.lean
# Writes: only inside this delivery directory (api-map.json, .tmp/, logs/).
#
# No download, no lake update/build, no `lake env lean`, no edit of the main project,
# no change to Boundary files or the central fact-tree. Nothing here needs the network.
#
# Run from anywhere; the script locates itself.
#   pwsh -File replay.ps1
#   pwsh -File replay.ps1 -MathlibRoot 'D:\path\to\mathlib'
#
# Expect: exit 0 and "REPLAY_OK". If Mathlib is absent or at a different commit the
# script fails loudly rather than silently reading a different version.

[CmdletBinding()]
param(
    [string]$MathlibRoot = 'C:\Users\18746\Desktop\数竞屠宰场\.lake\packages\mathlib',
    [string]$ExpectedCommit = '85e3a25e006c35636f0e53b0e9296caca2685bc0'
)

$ErrorActionPreference = 'Stop'
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $here

$logDir = Join-Path $here 'logs'
$tmpDir = Join-Path $here '.tmp'
New-Item -ItemType Directory -Force -Path $logDir, $tmpDir | Out-Null

function Assert-True([bool]$cond, [string]$msg) {
    if (-not $cond) { throw "ASSERT FAILED: $msg" }
    Write-Host "  ok: $msg"
}

Write-Host '== 1. toolchain =='
$py = (Get-Command python -ErrorAction SilentlyContinue)
Assert-True ($null -ne $py) 'python is on PATH'
Write-Host ("  python: " + (& python --version 2>&1))

Write-Host '== 2. Mathlib pin =='
Assert-True (Test-Path (Join-Path $MathlibRoot 'Mathlib')) "Mathlib root exists: $MathlibRoot"
$actual = (& git -C $MathlibRoot rev-parse HEAD 2>&1 | Out-String).Trim()
Write-Host ("  expected commit: " + $ExpectedCommit)
Write-Host ("  actual   commit: " + $actual)
Assert-True ($actual -eq $ExpectedCommit) 'Mathlib commit matches the baseline pin'

Write-Host '== 3. required source files exist =='
$required = @(
    'Mathlib/RingTheory/PowerSeries/Substitution.lean',
    'Mathlib/RingTheory/PowerSeries/Basic.lean',
    'Mathlib/RingTheory/PowerSeries/Inverse.lean',
    'Mathlib/RingTheory/PowerSeries/Order.lean',
    'Mathlib/RingTheory/PowerSeries/Evaluation.lean',
    'Mathlib/RingTheory/PowerSeries/Expand.lean',
    'Mathlib/RingTheory/MvPowerSeries/Substitution.lean'
)
foreach ($r in $required) {
    Assert-True (Test-Path (Join-Path $MathlibRoot ($r -replace '/', '\'))) $r
}

Write-Host '== 4. re-extract declarations verbatim =='
$sw = [System.Diagnostics.Stopwatch]::StartNew()
& python tools/extract.py tools/targets.json .tmp/decls_dump.txt 2>&1 |
    Tee-Object -FilePath (Join-Path $logDir 'replay_extract.stdout.log')
Assert-True ($LASTEXITCODE -eq 0) 'extract.py exit 0'

& python tools/sigs.py .tmp/decls_dump.txt .tmp/sigs.txt 2>&1 |
    Tee-Object -FilePath (Join-Path $logDir 'replay_sigs.stdout.log')
Assert-True ($LASTEXITCODE -eq 0) 'sigs.py exit 0'

Write-Host '== 5. rebuild api-map.json =='
& python tools/build_api_map.py .tmp/sigs.txt api-map.json 2>&1 |
    Tee-Object -FilePath (Join-Path $logDir 'replay_build_api_map.stdout.log')
Assert-True ($LASTEXITCODE -eq 0) 'build_api_map.py exit 0'
$sw.Stop()
Write-Host ("  rebuild seconds: " + [math]::Round($sw.Elapsed.TotalSeconds, 2))

Write-Host '== 6. verify the five gaps (negative searches) =='
& python tools/verify_gaps.py $MathlibRoot .tmp/gapcheck.json 2>&1 |
    Tee-Object -FilePath (Join-Path $logDir 'replay_verify_gaps.stdout.log')
Assert-True ($LASTEXITCODE -eq 0) 'no gap contradicted'

Write-Host '== 7. api-map.json is well formed =='
$map = Get-Content -Raw -Encoding UTF8 api-map.json | ConvertFrom-Json
Assert-True ($map.schema_version -eq 1) 'schema_version == 1'
Assert-True ($map.task_id -eq 'T003') 'task_id == T003'
Assert-True ($map.status -eq 'RESEARCH_ONLY') 'status == RESEARCH_ONLY'
$n = $map.entries.Count
Write-Host ("  entries: " + $n)
Assert-True ($n -ge 100) 'at least 100 retrieved declarations'
Assert-True ($map.entries.Count -eq $map.totals.entries) 'totals.entries consistent'
Assert-True ($map.gaps.Count -eq 5) '5 documented gaps'
foreach ($e in $map.entries) {
    foreach ($f in 'name', 'file', 'signature', 'category') {
        if (-not $e.$f) { throw "ASSERT FAILED: entry missing $f : $($e.name)" }
    }
    if ($e.signature -match 'REPLACE_WITH') { throw "ASSERT FAILED: placeholder in $($e.name)" }
}

Write-Host '== 8. recorded file hashes still match =='
foreach ($row in $map.mathlib_files) {
    $p = Join-Path $MathlibRoot ($row.path -replace '/', '\')
    $h = (Get-FileHash -Algorithm SHA256 -LiteralPath $p).Hash.ToLower()
    if ($h -ne $row.sha256) {
        throw "ASSERT FAILED: hash drift in $($row.path) (recorded $($row.sha256), actual $h)"
    }
}
Write-Host ("  ok: " + $map.mathlib_files.Count + " Mathlib files match their recorded SHA256")

Write-Host ''
Write-Host 'REPLAY_OK — retrieval reproduced; five gaps re-confirmed; no build performed.'
Write-Host 'NOTE: this is a RESEARCH_ONLY artifact. It proves nothing about Lean compilation,'
Write-Host '      axioms, or editor admission, and it does not advance the mainline fact-tree.'
